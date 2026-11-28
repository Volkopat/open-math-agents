import OMAReductions.R_Erdos78_erdos_78_variants_li_R1
import Mathlib

/-!
# Proof of `Erdos78.erdos_78.variants.li.R1.H2`

Given any polynomial-time `FinTM2` computing `f : List Bool × ℕ × ℕ → Bool` under
`BitstringEncoding`, we construct a wrapper `FinTM2` computing
`fun p => f (List.replicate (Nat.log 2 p.1.length + 1) true, min p.2.1 p.2.2, max p.2.1 p.2.2)`
in polynomial time.

Architecture:
1. `cmpLittleEndian` compares two little-endian `Computability.encodeNat` bitstrings from LSB to MSB
   using a 3-valued state `Cmp3 = {lt, eq, gt}`, proved equal to `decide (u < v)`.
2. Given `M : TM2ComputableInPolyTime bitEncode bitEncode f`, form a wrapper `FinTM2` with stack
   index type `Sum PreK M.tm.K`, label type `Sum PreΛ M.tm.Λ`, and internal state `Preσ × M.tm.σ`.
   Its input stack is `Sum.inl .inp` (`Bool`) and its output stack is `Sum.inr M.tm.k₁`.
3. Phase 1 (`readS`) scans `delimit (bitEncode s)` in 6-bit blocks, pushing one `true` onto `suR`
   per element of `s`.
4. Phase 2 (`logCheck`, `halve`, `moveCnt`) repeatedly halves the unary count on `suR` to push
   exactly `k = Nat.log 2 s.length + 1` copies of `true` onto `kStack`.
5. Phase 3 (`readU`, `readV`, `revU`, `revV`) extracts two reversed copies of `encodeNat u` and
   `encodeNat v`, reverses one copy of each for comparison, and preserves `suR2 = (encodeNat u).reverse`
   and `svR2 = (encodeNat v).reverse`.
6. Phase 4 (`cmpUV`, `clearSV_lt`, `clearSU_ge`) runs `cmpLittleEndian` and drains leftover bits.
7. Phase 5 (`emitMaxV`/`emitMinU` or `emitMaxU`/`emitMinV`, followed by `emitS`) writes
   `bitEncode (List.replicate k true, min u v, max u v)` onto `Sum.inr M.tm.k₀`, resets `Preσ`,
   and jumps to `Sum.inr M.tm.main`, where lifted statements simulate `M.tm` step-for-step.
-/

namespace Erdos78LiH2Proof

open Computability Turing Turing.TM2 StateTransition ComplexityTheory BitstringEncoding

/- ### Section 1: Encoding Helpers, Logarithm Bound, and Little-Endian Comparison -/

private def pairBits : List Bool → List Bool
  | [] => []
  | b :: l => true :: b :: pairBits l

private lemma pairBits_append (l₁ l₂ : List Bool) :
    pairBits (l₁ ++ l₂) = pairBits l₁ ++ pairBits l₂ := by
  induction l₁ with
  | nil => rfl
  | cons b l ih => simp [pairBits, ih]

private lemma delimit_eq_pairBits_append (l : List Bool) :
    delimit l = pairBits l ++ [false] := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [delimit, pairBits, ih]

private def repeatSix : ℕ → List Bool
  | 0 => []
  | k + 1 => [true, true, true, true, true, false] ++ repeatSix k

private lemma repeatSix_append_six (k : ℕ) :
    repeatSix k ++ [true, true, true, true, true, false] = repeatSix (k + 1) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [repeatSix, List.append_assoc]
    exact congrArg ([true, true, true, true, true, false] ++ ·) ih

private lemma replicate_append_cons (a : ℕ) (x : Bool) (ks : List Bool) :
    List.replicate a x ++ (x :: ks) = List.replicate (a + 1) x ++ ks := by
  induction a with
  | zero => rfl
  | succ a ih => simp only [List.replicate_succ, List.cons_append, ih]

private lemma bitEncode_list_bool_nil :
    bitEncode ([] : List Bool) = [] := rfl

private lemma bitEncode_list_bool_cons (b : Bool) (s : List Bool) :
    bitEncode (b :: s) = true :: b :: false :: bitEncode s := rfl

private lemma length_bitEncode_list_bool (s : List Bool) :
    (bitEncode s).length = 3 * s.length := by
  induction s with
  | nil => rfl
  | cons b s ih =>
    rw [bitEncode_list_bool_cons]
    simp [ih]
    omega

private lemma delimit_bitEncode_replicate_true (k : ℕ) :
    delimit (bitEncode (List.replicate k true)) = repeatSix k ++ [false] := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, bitEncode_list_bool_cons]
    simp only [delimit, ih, repeatSix, List.cons_append, List.nil_append]

private lemma nat_log2_le_self (n : ℕ) : Nat.log 2 n ≤ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have h1 : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (Nat.ne_of_gt hn)
    have h2 : Nat.log 2 n < 2 ^ Nat.log 2 n := Nat.lt_two_pow_self
    omega

private lemma poly_eval_mono (p : Polynomial ℕ) {a b : ℕ} (h : a ≤ b) :
    p.eval a ≤ p.eval b := by
  rw [Polynomial.eval_eq_sum, Polynomial.eval_eq_sum]
  exact Finset.sum_le_sum fun i _ => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h i)

private lemma posNum_one_le (m : PosNum) : 1 ≤ (m : ℕ) := by
  induction m with
  | one => simp
  | bit0 k ih => simp [PosNum.cast_bit0]; omega
  | bit1 k ih => simp [PosNum.cast_bit1]

private inductive Cmp3 : Type
  | lt
  | eq
  | gt
  deriving DecidableEq

private def cmp3Equiv : Cmp3 ≃ Fin 3 where
  toFun
    | .lt => 0
    | .eq => 1
    | .gt => 2
  invFun
    | ⟨0, _⟩ => .lt
    | ⟨1, _⟩ => .eq
    | ⟨2, _⟩ => .gt
  left_inv c := by cases c <;> rfl
  right_inv i := by fin_cases i <;> rfl

private instance : Fintype Cmp3 := Fintype.ofEquiv (Fin 3) cmp3Equiv.symm

private def updateCmp (c : Cmp3) (a b : Bool) : Cmp3 :=
  if a = b then c else if a = false then .lt else .gt

private def cmpLittleEndian : List Bool → List Bool → Cmp3 → Bool
  | [], [], c => decide (c = .lt)
  | [], _ :: _, _ => true
  | _ :: _, [], _ => false
  | a :: as, b :: bs, c => cmpLittleEndian as bs (updateCmp c a b)

private lemma cmpLittleEndian_nil_nonempty {bs : List Bool} (hb : bs ≠ []) (c : Cmp3) :
    cmpLittleEndian [] bs c = true := by
  cases bs with
  | nil => exact absurd rfl hb
  | cons _ _ => rfl

private lemma cmpLittleEndian_nonempty_nil {as : List Bool} (ha : as ≠ []) (c : Cmp3) :
    cmpLittleEndian as [] c = false := by
  cases as with
  | nil => exact absurd rfl ha
  | cons _ _ => rfl

private lemma cmpLittleEndian_encodePosNum (p : PosNum) :
    ∀ (q : PosNum) (c : Cmp3),
      cmpLittleEndian (Computability.encodePosNum p) (Computability.encodePosNum q) c =
        match compare (p : ℕ) (q : ℕ) with
        | .lt => true
        | .gt => false
        | .eq => decide (c = .lt) := by
  induction p with
  | one =>
    intro q c
    cases q with
    | one =>
      simp [Computability.encodePosNum, cmpLittleEndian, updateCmp]
    | bit0 m =>
      have hm := posNum_one_le m
      have hcmp : compare ((PosNum.one : PosNum) : ℕ) ((PosNum.bit0 m : PosNum) : ℕ) = .lt := by
        rw [Nat.compare_eq_lt]; simp [PosNum.cast_bit0]; omega
      rw [hcmp]
      simp only [Computability.encodePosNum, cmpLittleEndian]
      exact cmpLittleEndian_nil_nonempty (Computability.encodePosNum_nonempty m) _
    | bit1 m =>
      have hcmp : compare ((PosNum.one : PosNum) : ℕ) ((PosNum.bit1 m : PosNum) : ℕ) = .lt := by
        rw [Nat.compare_eq_lt]; simp [PosNum.cast_bit1]
      rw [hcmp]
      simp only [Computability.encodePosNum, cmpLittleEndian]
      exact cmpLittleEndian_nil_nonempty (Computability.encodePosNum_nonempty m) _
  | bit0 m ih =>
    intro q c
    cases q with
    | one =>
      have hm := posNum_one_le m
      have hcmp : compare ((PosNum.bit0 m : PosNum) : ℕ) ((PosNum.one : PosNum) : ℕ) = .gt := by
        rw [Nat.compare_eq_gt]; simp [PosNum.cast_bit0]; omega
      rw [hcmp]
      simp only [Computability.encodePosNum, cmpLittleEndian]
      exact cmpLittleEndian_nonempty_nil (Computability.encodePosNum_nonempty m) _
    | bit0 k =>
      simp only [Computability.encodePosNum, cmpLittleEndian, updateCmp, ↓reduceIte]
      rw [ih k c]
      rcases lt_trichotomy (m : ℕ) (k : ℕ) with hlt | heq | hgt
      · have h1 : compare (m : ℕ) (k : ℕ) = .lt := Nat.compare_eq_lt.mpr hlt
        have h2 : compare ((PosNum.bit0 m : PosNum) : ℕ) ((PosNum.bit0 k : PosNum) : ℕ) = .lt := by
          rw [Nat.compare_eq_lt]; simp [PosNum.cast_bit0]; omega
        rw [h1, h2]
      · have h1 : compare (m : ℕ) (k : ℕ) = .eq := Nat.compare_eq_eq.mpr heq
        have h2 : compare ((PosNum.bit0 m : PosNum) : ℕ) ((PosNum.bit0 k : PosNum) : ℕ) = .eq := by
          rw [Nat.compare_eq_eq]; simp [PosNum.cast_bit0]; omega
        rw [h1, h2]
      · have h1 : compare (m : ℕ) (k : ℕ) = .gt := Nat.compare_eq_gt.mpr hgt
        have h2 : compare ((PosNum.bit0 m : PosNum) : ℕ) ((PosNum.bit0 k : PosNum) : ℕ) = .gt := by
          rw [Nat.compare_eq_gt]; simp [PosNum.cast_bit0]; omega
        rw [h1, h2]
    | bit1 k =>
      simp only [Computability.encodePosNum, cmpLittleEndian, updateCmp, Bool.false_eq_true, ↓reduceIte]
      rw [ih k .lt]
      rcases lt_trichotomy (m : ℕ) (k : ℕ) with hlt | heq | hgt
      · have h1 : compare (m : ℕ) (k : ℕ) = .lt := Nat.compare_eq_lt.mpr hlt
        have h2 : compare ((PosNum.bit0 m : PosNum) : ℕ) ((PosNum.bit1 k : PosNum) : ℕ) = .lt := by
          rw [Nat.compare_eq_lt]; simp [PosNum.cast_bit0, PosNum.cast_bit1]; omega
        rw [h1, h2]
      · have h1 : compare (m : ℕ) (k : ℕ) = .eq := Nat.compare_eq_eq.mpr heq
        have h2 : compare ((PosNum.bit0 m : PosNum) : ℕ) ((PosNum.bit1 k : PosNum) : ℕ) = .lt := by
          rw [Nat.compare_eq_lt]; simp [PosNum.cast_bit0, PosNum.cast_bit1]; omega
        rw [h1, h2]; rfl
      · have h1 : compare (m : ℕ) (k : ℕ) = .gt := Nat.compare_eq_gt.mpr hgt
        have h2 : compare ((PosNum.bit0 m : PosNum) : ℕ) ((PosNum.bit1 k : PosNum) : ℕ) = .gt := by
          rw [Nat.compare_eq_gt]; simp [PosNum.cast_bit0, PosNum.cast_bit1]; omega
        rw [h1, h2]
  | bit1 m ih =>
    intro q c
    cases q with
    | one =>
      have hcmp : compare ((PosNum.bit1 m : PosNum) : ℕ) ((PosNum.one : PosNum) : ℕ) = .gt := by
        rw [Nat.compare_eq_gt]; simp [PosNum.cast_bit1]
      rw [hcmp]
      simp only [Computability.encodePosNum, cmpLittleEndian]
      exact cmpLittleEndian_nonempty_nil (Computability.encodePosNum_nonempty m) _
    | bit0 k =>
      simp only [Computability.encodePosNum, cmpLittleEndian, updateCmp, Bool.true_eq_false, ↓reduceIte]
      rw [ih k .gt]
      rcases lt_trichotomy (m : ℕ) (k : ℕ) with hlt | heq | hgt
      · have h1 : compare (m : ℕ) (k : ℕ) = .lt := Nat.compare_eq_lt.mpr hlt
        have h2 : compare ((PosNum.bit1 m : PosNum) : ℕ) ((PosNum.bit0 k : PosNum) : ℕ) = .lt := by
          rw [Nat.compare_eq_lt]; simp [PosNum.cast_bit0, PosNum.cast_bit1]; omega
        rw [h1, h2]
      · have h1 : compare (m : ℕ) (k : ℕ) = .eq := Nat.compare_eq_eq.mpr heq
        have h2 : compare ((PosNum.bit1 m : PosNum) : ℕ) ((PosNum.bit0 k : PosNum) : ℕ) = .gt := by
          rw [Nat.compare_eq_gt]; simp [PosNum.cast_bit0, PosNum.cast_bit1]; omega
        rw [h1, h2]; rfl
      · have h1 : compare (m : ℕ) (k : ℕ) = .gt := Nat.compare_eq_gt.mpr hgt
        have h2 : compare ((PosNum.bit1 m : PosNum) : ℕ) ((PosNum.bit0 k : PosNum) : ℕ) = .gt := by
          rw [Nat.compare_eq_gt]; simp [PosNum.cast_bit0, PosNum.cast_bit1]; omega
        rw [h1, h2]
    | bit1 k =>
      simp only [Computability.encodePosNum, cmpLittleEndian, updateCmp, ↓reduceIte]
      rw [ih k c]
      rcases lt_trichotomy (m : ℕ) (k : ℕ) with hlt | heq | hgt
      · have h1 : compare (m : ℕ) (k : ℕ) = .lt := Nat.compare_eq_lt.mpr hlt
        have h2 : compare ((PosNum.bit1 m : PosNum) : ℕ) ((PosNum.bit1 k : PosNum) : ℕ) = .lt := by
          rw [Nat.compare_eq_lt]; simp [PosNum.cast_bit1]; omega
        rw [h1, h2]
      · have h1 : compare (m : ℕ) (k : ℕ) = .eq := Nat.compare_eq_eq.mpr heq
        have h2 : compare ((PosNum.bit1 m : PosNum) : ℕ) ((PosNum.bit1 k : PosNum) : ℕ) = .eq := by
          rw [Nat.compare_eq_eq]; simp [PosNum.cast_bit1]; omega
        rw [h1, h2]
      · have h1 : compare (m : ℕ) (k : ℕ) = .gt := Nat.compare_eq_gt.mpr hgt
        have h2 : compare ((PosNum.bit1 m : PosNum) : ℕ) ((PosNum.bit1 k : PosNum) : ℕ) = .gt := by
          rw [Nat.compare_eq_gt]; simp [PosNum.cast_bit1]; omega
        rw [h1, h2]

private lemma cmpLittleEndian_encodeNat (u v : ℕ) :
    cmpLittleEndian (Computability.encodeNat u) (Computability.encodeNat v) .eq = decide (u < v) := by
  have hu : ((u : Num) : ℕ) = u := Num.to_of_nat u
  have hv : ((v : Num) : ℕ) = v := Num.to_of_nat v
  unfold Computability.encodeNat
  cases hnu : (u : Num) with
  | zero =>
    have hu0 : u = 0 := by rw [← hu, hnu]; rfl
    subst hu0
    cases hnv : (v : Num) with
    | zero =>
      have hv0 : v = 0 := by rw [← hv, hnv]; rfl
      subst hv0; rfl
    | pos q =>
      have hvq : v = (q : ℕ) := by rw [← hv, hnv]; rfl
      have hqpos : 0 < (q : ℕ) := by
        have := posNum_one_le q; omega
      simp only [Computability.encodeNum, hvq, decide_eq_true hqpos]
      exact cmpLittleEndian_nil_nonempty (Computability.encodePosNum_nonempty q) .eq
  | pos p =>
    have hup : u = (p : ℕ) := by rw [← hu, hnu]; rfl
    cases hnv : (v : Num) with
    | zero =>
      have hv0 : v = 0 := by rw [← hv, hnv]; rfl
      subst hv0
      simp only [Computability.encodeNum, Nat.not_lt_zero, decide_false]
      exact cmpLittleEndian_nonempty_nil (Computability.encodePosNum_nonempty p) .eq
    | pos q =>
      have hvq : v = (q : ℕ) := by rw [← hv, hnv]; rfl
      simp only [Computability.encodeNum, hup, hvq]
      rw [cmpLittleEndian_encodePosNum p q .eq]
      rcases lt_trichotomy (p : ℕ) (q : ℕ) with hlt | heq | hgt
      · rw [Nat.compare_eq_lt.mpr hlt, decide_eq_true hlt]
      · rw [Nat.compare_eq_eq.mpr heq, heq]
        simp
      · rw [Nat.compare_eq_gt.mpr hgt, decide_eq_false (not_lt_of_gt hgt)]

/- ### Section 2: Wrapper `FinTM2` Construction -/

private inductive PreK : Type
  | inp
  | kStack
  | suR
  | su
  | suR2
  | svR
  | sv
  | svR2
  deriving DecidableEq

private def preKEquiv : PreK ≃ Fin 8 where
  toFun
    | .inp => 0
    | .kStack => 1
    | .suR => 2
    | .su => 3
    | .suR2 => 4
    | .svR => 5
    | .sv => 6
    | .svR2 => 7
  invFun
    | ⟨0, _⟩ => .inp
    | ⟨1, _⟩ => .kStack
    | ⟨2, _⟩ => .suR
    | ⟨3, _⟩ => .su
    | ⟨4, _⟩ => .suR2
    | ⟨5, _⟩ => .svR
    | ⟨6, _⟩ => .sv
    | ⟨7, _⟩ => .svR2
  left_inv k := by cases k <;> rfl
  right_inv i := by fin_cases i <;> rfl

private instance : Fintype PreK := Fintype.ofEquiv (Fin 8) preKEquiv.symm

private inductive PreΛ : Type
  | readS
  | logCheck
  | halve
  | moveCnt
  | readU
  | readV
  | revU
  | revV
  | cmpUV
  | clearSV_lt
  | emitMaxV
  | emitMinU
  | clearSU_ge
  | emitMaxU
  | emitMinV
  | emitS
  deriving DecidableEq

private def preΛEquiv : PreΛ ≃ Fin 16 where
  toFun
    | .readS => 0
    | .logCheck => 1
    | .halve => 2
    | .moveCnt => 3
    | .readU => 4
    | .readV => 5
    | .revU => 6
    | .revV => 7
    | .cmpUV => 8
    | .clearSV_lt => 9
    | .emitMaxV => 10
    | .emitMinU => 11
    | .clearSU_ge => 12
    | .emitMaxU => 13
    | .emitMinV => 14
    | .emitS => 15
  invFun
    | ⟨0, _⟩ => .readS
    | ⟨1, _⟩ => .logCheck
    | ⟨2, _⟩ => .halve
    | ⟨3, _⟩ => .moveCnt
    | ⟨4, _⟩ => .readU
    | ⟨5, _⟩ => .readV
    | ⟨6, _⟩ => .revU
    | ⟨7, _⟩ => .revV
    | ⟨8, _⟩ => .cmpUV
    | ⟨9, _⟩ => .clearSV_lt
    | ⟨10, _⟩ => .emitMaxV
    | ⟨11, _⟩ => .emitMinU
    | ⟨12, _⟩ => .clearSU_ge
    | ⟨13, _⟩ => .emitMaxU
    | ⟨14, _⟩ => .emitMinV
    | ⟨15, _⟩ => .emitS
    | ⟨_ + 16, h⟩ => absurd h (by omega)
  left_inv l := by cases l <;> rfl
  right_inv i := by fin_cases i <;> rfl

private instance : Fintype PreΛ := Fintype.ofEquiv (Fin 16) preΛEquiv.symm

private abbrev Preσ : Type := Cmp3 × Option Bool × Option Bool

private def preσInit : Preσ := (.eq, none, none)

private lemma cfg_ext {K : Type*} {Γ : K → Type*} {Λ σ : Type*}
    {c₁ c₂ : TM2.Cfg Γ Λ σ}
    (hl : c₁.l = c₂.l) (hvar : c₁.var = c₂.var) (hstk : c₁.stk = c₂.stk) : c₁ = c₂ := by
  cases c₁; cases c₂; cases hl; cases hvar; cases hstk; rfl

section Wrapper

variable {f : List Bool × ℕ × ℕ → Bool}
variable (M : TM2ComputableInPolyTime
  (BitstringEncoding.toEncoding (α := List Bool × ℕ × ℕ)).encode
  (BitstringEncoding.toEncoding (α := Bool)).encode f)

private abbrev WK : Type := Sum PreK M.tm.K

private abbrev WΓ : WK M → Type
  | Sum.inl _ => Bool
  | Sum.inr k => M.tm.Γ k

private abbrev WΛ : Type := Sum PreΛ M.tm.Λ
private abbrev Wσ : Type := Preσ × M.tm.σ

private def liftStmt :
    TM2.Stmt M.tm.Γ M.tm.Λ M.tm.σ → TM2.Stmt (WΓ M) (WΛ M) (Wσ M)
  | .push k g q => .push (Sum.inr k) (fun v => g v.2) (liftStmt q)
  | .peek k g q => .peek (Sum.inr k) (fun v o => (v.1, g v.2 o)) (liftStmt q)
  | .pop k g q => .pop (Sum.inr k) (fun v o => (v.1, g v.2 o)) (liftStmt q)
  | .load g q => .load (fun v => (v.1, g v.2)) (liftStmt q)
  | .branch g q₁ q₂ => .branch (fun v => g v.2) (liftStmt q₁) (liftStmt q₂)
  | .goto g => .goto (fun v => Sum.inr (g v.2))
  | .halt => .halt

private def preProg : PreΛ → TM2.Stmt (WΓ M) (WΛ M) (Wσ M)
  | .readS =>
      .pop (Sum.inl .inp) (fun v o => ((v.1.1, o, none), v.2)) <|
      .branch (fun v => decide (v.1.2.1 = some true))
        (.pop (Sum.inl .inp) (fun v _ => v) <|
         .pop (Sum.inl .inp) (fun v _ => v) <|
         .pop (Sum.inl .inp) (fun v _ => v) <|
         .pop (Sum.inl .inp) (fun v _ => v) <|
         .pop (Sum.inl .inp) (fun v _ => v) <|
         .push (Sum.inl .suR) (fun _ => true) <|
         .goto (fun _ => Sum.inl .readS))
        (.goto (fun _ => Sum.inl .logCheck))
  | .logCheck =>
      .pop (Sum.inl .suR) (fun v o => ((v.1.1, o, none), v.2)) <|
      .pop (Sum.inl .suR) (fun v o => ((v.1.1, v.1.2.1, o), v.2)) <|
      .branch (fun v => v.1.2.2.isSome)
        (.push (Sum.inl .svR) (fun _ => true) <|
         .goto (fun _ => Sum.inl .halve))
        (.push (Sum.inl .kStack) (fun _ => true) <|
         .load (fun v => ((v.1.1, none, none), v.2)) <|
         .goto (fun _ => Sum.inl .readU))
  | .halve =>
      .pop (Sum.inl .suR) (fun v o => ((v.1.1, o, none), v.2)) <|
      .pop (Sum.inl .suR) (fun v o => ((v.1.1, v.1.2.1, o), v.2)) <|
      .branch (fun v => v.1.2.2.isSome)
        (.push (Sum.inl .svR) (fun _ => true) <|
         .goto (fun _ => Sum.inl .halve))
        (.push (Sum.inl .kStack) (fun _ => true) <|
         .load (fun v => ((v.1.1, none, none), v.2)) <|
         .goto (fun _ => Sum.inl .moveCnt))
  | .moveCnt =>
      .pop (Sum.inl .svR) (fun v o => ((v.1.1, o, none), v.2)) <|
      .branch (fun v => v.1.2.1.isSome)
        (.push (Sum.inl .suR) (fun _ => true) <|
         .goto (fun _ => Sum.inl .moveCnt))
        (.goto (fun _ => Sum.inl .logCheck))
  | .readU =>
      .pop (Sum.inl .inp) (fun v o => ((v.1.1, o, none), v.2)) <|
      .branch (fun v => decide (v.1.2.1 = some true))
        (.pop (Sum.inl .inp) (fun v o => ((v.1.1, o, none), v.2)) <|
         .push (Sum.inl .suR) (fun v => v.1.2.1.getD false) <|
         .push (Sum.inl .suR2) (fun v => v.1.2.1.getD false) <|
         .goto (fun _ => Sum.inl .readU))
        (.goto (fun _ => Sum.inl .readV))
  | .readV =>
      .pop (Sum.inl .inp) (fun v o => ((v.1.1, o, none), v.2)) <|
      .branch (fun v => v.1.2.1.isSome)
        (.push (Sum.inl .svR) (fun v => v.1.2.1.getD false) <|
         .push (Sum.inl .svR2) (fun v => v.1.2.1.getD false) <|
         .goto (fun _ => Sum.inl .readV))
        (.goto (fun _ => Sum.inl .revU))
  | .revU =>
      .pop (Sum.inl .suR) (fun v o => ((v.1.1, o, none), v.2)) <|
      .branch (fun v => v.1.2.1.isSome)
        (.push (Sum.inl .su) (fun v => v.1.2.1.getD false) <|
         .goto (fun _ => Sum.inl .revU))
        (.goto (fun _ => Sum.inl .revV))
  | .revV =>
      .pop (Sum.inl .svR) (fun v o => ((v.1.1, o, none), v.2)) <|
      .branch (fun v => v.1.2.1.isSome)
        (.push (Sum.inl .sv) (fun v => v.1.2.1.getD false) <|
         .goto (fun _ => Sum.inl .revV))
        (.load (fun v => ((.eq, none, none), v.2)) <|
         .goto (fun _ => Sum.inl .cmpUV))
  | .cmpUV =>
      .pop (Sum.inl .su) (fun v o => ((v.1.1, o, none), v.2)) <|
      .pop (Sum.inl .sv) (fun v o => ((v.1.1, v.1.2.1, o), v.2)) <|
      .branch (fun v => v.1.2.1.isSome)
        (.branch (fun v => v.1.2.2.isSome)
          (.load (fun v =>
              ((updateCmp v.1.1 (v.1.2.1.getD false) (v.1.2.2.getD false), none, none), v.2)) <|
           .goto (fun _ => Sum.inl .cmpUV))
          (.goto (fun _ => Sum.inl .clearSU_ge)))
        (.branch (fun v => v.1.2.2.isSome)
          (.goto (fun _ => Sum.inl .clearSV_lt))
          (.branch (fun v => decide (v.1.1 = .lt))
            (.goto (fun _ => Sum.inl .emitMaxV))
            (.goto (fun _ => Sum.inl .emitMaxU))))
  | .clearSV_lt =>
      .pop (Sum.inl .sv) (fun v o => ((v.1.1, o, none), v.2)) <|
      .branch (fun v => v.1.2.1.isSome)
        (.goto (fun _ => Sum.inl .clearSV_lt))
        (.goto (fun _ => Sum.inl .emitMaxV))
  | .emitMaxV =>
      .pop (Sum.inl .svR2) (fun v o => ((v.1.1, o, none), v.2)) <|
      .branch (fun v => v.1.2.1.isSome)
        (.push (Sum.inr M.tm.k₀) (fun v => M.inputAlphabet.symm (v.1.2.1.getD false)) <|
         .goto (fun _ => Sum.inl .emitMaxV))
        (.push (Sum.inr M.tm.k₀) (fun _ => M.inputAlphabet.symm false) <|
         .goto (fun _ => Sum.inl .emitMinU))
  | .emitMinU =>
      .pop (Sum.inl .suR2) (fun v o => ((v.1.1, o, none), v.2)) <|
      .branch (fun v => v.1.2.1.isSome)
        (.push (Sum.inr M.tm.k₀) (fun v => M.inputAlphabet.symm (v.1.2.1.getD false)) <|
         .push (Sum.inr M.tm.k₀) (fun _ => M.inputAlphabet.symm true) <|
         .goto (fun _ => Sum.inl .emitMinU))
        (.push (Sum.inr M.tm.k₀) (fun _ => M.inputAlphabet.symm false) <|
         .goto (fun _ => Sum.inl .emitS))
  | .clearSU_ge =>
      .pop (Sum.inl .su) (fun v o => ((v.1.1, o, none), v.2)) <|
      .branch (fun v => v.1.2.1.isSome)
        (.goto (fun _ => Sum.inl .clearSU_ge))
        (.goto (fun _ => Sum.inl .emitMaxU))
  | .emitMaxU =>
      .pop (Sum.inl .suR2) (fun v o => ((v.1.1, o, none), v.2)) <|
      .branch (fun v => v.1.2.1.isSome)
        (.push (Sum.inr M.tm.k₀) (fun v => M.inputAlphabet.symm (v.1.2.1.getD false)) <|
         .goto (fun _ => Sum.inl .emitMaxU))
        (.push (Sum.inr M.tm.k₀) (fun _ => M.inputAlphabet.symm false) <|
         .goto (fun _ => Sum.inl .emitMinV))
  | .emitMinV =>
      .pop (Sum.inl .svR2) (fun v o => ((v.1.1, o, none), v.2)) <|
      .branch (fun v => v.1.2.1.isSome)
        (.push (Sum.inr M.tm.k₀) (fun v => M.inputAlphabet.symm (v.1.2.1.getD false)) <|
         .push (Sum.inr M.tm.k₀) (fun _ => M.inputAlphabet.symm true) <|
         .goto (fun _ => Sum.inl .emitMinV))
        (.push (Sum.inr M.tm.k₀) (fun _ => M.inputAlphabet.symm false) <|
         .goto (fun _ => Sum.inl .emitS))
  | .emitS =>
      .pop (Sum.inl .kStack) (fun v o => ((v.1.1, o, none), v.2)) <|
      .branch (fun v => v.1.2.1.isSome)
        (.push (Sum.inr M.tm.k₀) (fun _ => M.inputAlphabet.symm false) <|
         .push (Sum.inr M.tm.k₀) (fun _ => M.inputAlphabet.symm true) <|
         .push (Sum.inr M.tm.k₀) (fun _ => M.inputAlphabet.symm true) <|
         .push (Sum.inr M.tm.k₀) (fun _ => M.inputAlphabet.symm true) <|
         .push (Sum.inr M.tm.k₀) (fun _ => M.inputAlphabet.symm true) <|
         .push (Sum.inr M.tm.k₀) (fun _ => M.inputAlphabet.symm true) <|
         .goto (fun _ => Sum.inl .emitS))
        (.load (fun v => (preσInit, v.2)) <|
         .goto (fun _ => Sum.inr M.tm.main))

private def wrapProg : WΛ M → TM2.Stmt (WΓ M) (WΛ M) (Wσ M)
  | Sum.inl l => preProg M l
  | Sum.inr l => liftStmt M (M.tm.m l)

private abbrev wrapTM : FinTM2 where
  K := WK M
  kDecidableEq := inferInstance
  kFin := @instFintypeSum PreK M.tm.K _ M.tm.kFin
  k₀ := Sum.inl .inp
  k₁ := Sum.inr M.tm.k₁
  Γ := WΓ M
  Λ := WΛ M
  main := Sum.inl .readS
  ΛFin := @instFintypeSum PreΛ M.tm.Λ _ M.tm.ΛFin
  σ := Wσ M
  initialState := (preσInit, M.tm.initialState)
  σFin := @instFintypeProd Preσ M.tm.σ _ M.tm.σFin
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := wrapProg M

/- ### Section 3: Stack Builder and Simulation Lemmas -/

private def mkPreStk (inp kStack suR su suR2 svR sv svR2 : List Bool)
    (rhs : ∀ k : M.tm.K, List (M.tm.Γ k)) :
    ∀ k : WK M, List (WΓ M k)
  | Sum.inl .inp => inp
  | Sum.inl .kStack => kStack
  | Sum.inl .suR => suR
  | Sum.inl .su => su
  | Sum.inl .suR2 => suR2
  | Sum.inl .svR => svR
  | Sum.inl .sv => sv
  | Sum.inl .svR2 => svR2
  | Sum.inr k => rhs k

private def emptyRhs : ∀ k : M.tm.K, List (M.tm.Γ k) := fun _ => []

private def mkInitRhs (s : List (M.tm.Γ M.tm.k₀)) : ∀ k : M.tm.K, List (M.tm.Γ k) :=
  fun k => @dite (List (M.tm.Γ k)) (k = M.tm.k₀) (M.tm.kDecidableEq k M.tm.k₀)
    (fun h => by rw [h]; exact s) (fun _ => [])

private lemma update_mkPreStk_inp (inp' inp kStack suR su suR2 svR sv svR2 : List Bool)
    (rhs : ∀ k, List (M.tm.Γ k)) :
    Function.update (mkPreStk M inp kStack suR su suR2 svR sv svR2 rhs) (Sum.inl .inp) inp' =
      mkPreStk M inp' kStack suR su suR2 svR sv svR2 rhs := by
  funext k; cases k with
  | inl pk => cases pk <;> simp [Function.update, mkPreStk]
  | inr rk => simp [Function.update, mkPreStk]

private lemma update_mkPreStk_kStack (kStack' inp kStack suR su suR2 svR sv svR2 : List Bool)
    (rhs : ∀ k, List (M.tm.Γ k)) :
    Function.update (mkPreStk M inp kStack suR su suR2 svR sv svR2 rhs) (Sum.inl .kStack) kStack' =
      mkPreStk M inp kStack' suR su suR2 svR sv svR2 rhs := by
  funext k; cases k with
  | inl pk => cases pk <;> simp [Function.update, mkPreStk]
  | inr rk => simp [Function.update, mkPreStk]

private lemma update_mkPreStk_suR (suR' inp kStack suR su suR2 svR sv svR2 : List Bool)
    (rhs : ∀ k, List (M.tm.Γ k)) :
    Function.update (mkPreStk M inp kStack suR su suR2 svR sv svR2 rhs) (Sum.inl .suR) suR' =
      mkPreStk M inp kStack suR' su suR2 svR sv svR2 rhs := by
  funext k; cases k with
  | inl pk => cases pk <;> simp [Function.update, mkPreStk]
  | inr rk => simp [Function.update, mkPreStk]

private lemma update_mkPreStk_su (su' inp kStack suR su suR2 svR sv svR2 : List Bool)
    (rhs : ∀ k, List (M.tm.Γ k)) :
    Function.update (mkPreStk M inp kStack suR su suR2 svR sv svR2 rhs) (Sum.inl .su) su' =
      mkPreStk M inp kStack suR su' suR2 svR sv svR2 rhs := by
  funext k; cases k with
  | inl pk => cases pk <;> simp [Function.update, mkPreStk]
  | inr rk => simp [Function.update, mkPreStk]

private lemma update_mkPreStk_suR2 (suR2' inp kStack suR su suR2 svR sv svR2 : List Bool)
    (rhs : ∀ k, List (M.tm.Γ k)) :
    Function.update (mkPreStk M inp kStack suR su suR2 svR sv svR2 rhs) (Sum.inl .suR2) suR2' =
      mkPreStk M inp kStack suR su suR2' svR sv svR2 rhs := by
  funext k; cases k with
  | inl pk => cases pk <;> simp [Function.update, mkPreStk]
  | inr rk => simp [Function.update, mkPreStk]

private lemma update_mkPreStk_svR (svR' inp kStack suR su suR2 svR sv svR2 : List Bool)
    (rhs : ∀ k, List (M.tm.Γ k)) :
    Function.update (mkPreStk M inp kStack suR su suR2 svR sv svR2 rhs) (Sum.inl .svR) svR' =
      mkPreStk M inp kStack suR su suR2 svR' sv svR2 rhs := by
  funext k; cases k with
  | inl pk => cases pk <;> simp [Function.update, mkPreStk]
  | inr rk => simp [Function.update, mkPreStk]

private lemma update_mkPreStk_sv (sv' inp kStack suR su suR2 svR sv svR2 : List Bool)
    (rhs : ∀ k, List (M.tm.Γ k)) :
    Function.update (mkPreStk M inp kStack suR su suR2 svR sv svR2 rhs) (Sum.inl .sv) sv' =
      mkPreStk M inp kStack suR su suR2 svR sv' svR2 rhs := by
  funext k; cases k with
  | inl pk => cases pk <;> simp [Function.update, mkPreStk]
  | inr rk => simp [Function.update, mkPreStk]

private lemma update_mkPreStk_svR2 (svR2' inp kStack suR su suR2 svR sv svR2 : List Bool)
    (rhs : ∀ k, List (M.tm.Γ k)) :
    Function.update (mkPreStk M inp kStack suR su suR2 svR sv svR2 rhs) (Sum.inl .svR2) svR2' =
      mkPreStk M inp kStack suR su suR2 svR sv svR2' rhs := by
  funext k; cases k with
  | inl pk => cases pk <;> simp [Function.update, mkPreStk]
  | inr rk => simp [Function.update, mkPreStk]

private lemma update_mkPreStk_inr (k₀ : M.tm.K) (v : List (M.tm.Γ k₀))
    (inp kStack suR su suR2 svR sv svR2 : List Bool) (rhs : ∀ k, List (M.tm.Γ k)) :
    Function.update (mkPreStk M inp kStack suR su suR2 svR sv svR2 rhs) (Sum.inr k₀) v =
      mkPreStk M inp kStack suR su suR2 svR sv svR2 (Function.update rhs k₀ v) := by
  funext k; cases k with
  | inl pk => cases pk <;> simp [Function.update, mkPreStk]
  | inr rk =>
    by_cases h : rk = k₀
    · subst h; simp [Function.update, mkPreStk]
    · simp [Function.update, mkPreStk, h]

private lemma update_mkInitRhs (a : M.tm.Γ M.tm.k₀) (acc : List (M.tm.Γ M.tm.k₀)) :
    Function.update (mkInitRhs M acc) M.tm.k₀ (a :: acc) = mkInitRhs M (a :: acc) := by
  funext k
  by_cases h : k = M.tm.k₀
  · subst h; simp [Function.update, mkInitRhs]
  · simp [Function.update, mkInitRhs, h]

private lemma stepAux_pop_inp (b : Bool) (inp kStack suR su suR2 svR sv svR2 : List Bool)
    (rhs : ∀ k, List (M.tm.Γ k)) (g : Wσ M → Option Bool → Wσ M)
    (q : TM2.Stmt (WΓ M) (WΛ M) (Wσ M)) (v : Wσ M) :
    TM2.stepAux (.pop (Sum.inl .inp) g q) v
      (mkPreStk M (b :: inp) kStack suR su suR2 svR sv svR2 rhs) =
    TM2.stepAux q (g v (some b))
      (mkPreStk M inp kStack suR su suR2 svR sv svR2 rhs) := by
  dsimp only [TM2.stepAux, mkPreStk, List.head?_cons, List.tail_cons]
  rw [update_mkPreStk_inp]

private lemma stepAux_push_k0 (g : Wσ M → M.tm.Γ M.tm.k₀)
    (q : TM2.Stmt (WΓ M) (WΛ M) (Wσ M)) (v : Wσ M)
    (inp kStack suR su suR2 svR sv svR2 : List Bool)
    (acc : List (M.tm.Γ M.tm.k₀)) :
    TM2.stepAux (.push (Sum.inr M.tm.k₀) g q) v
      (mkPreStk M inp kStack suR su suR2 svR sv svR2 (mkInitRhs M acc)) =
    TM2.stepAux q v
      (mkPreStk M inp kStack suR su suR2 svR sv svR2 (mkInitRhs M (g v :: acc))) := by
  dsimp only [TM2.stepAux, mkPreStk]
  rw [update_mkPreStk_inr]
  have hmk : mkInitRhs M acc M.tm.k₀ = acc := by simp [mkInitRhs]
  rw [hmk, update_mkInitRhs]

private lemma emptyRhs_eq_mkInitRhs_nil : emptyRhs M = mkInitRhs M [] := by
  funext k
  by_cases h : k = M.tm.k₀
  · subst h; simp [emptyRhs, mkInitRhs]
  · simp [emptyRhs, mkInitRhs, h]

private def evalsStep {α : Type*} (step : α → Option α) {a b : α} (h : step a = some b) :
    EvalsToInTime step a (some b) 1 where
  steps := 1
  evals_in_steps := by simpa [Function.iterate_one, flip] using h
  steps_le_m := le_refl 1

private def evalsTrans {α : Type*} {step : α → Option α} {a b : α} {c : Option α} {m₁ m₂ : ℕ}
    (h₁ : EvalsToInTime step a (some b) m₁) (h₂ : EvalsToInTime step b c m₂) :
    EvalsToInTime step a c (m₂ + m₁) :=
  EvalsToInTime.trans step m₁ m₂ a b c h₁ h₂

private def evalsMono {α : Type*} {step : α → Option α} {a : α} {b : Option α} {m₁ m₂ : ℕ}
    (h : EvalsToInTime step a b m₁) (hle : m₁ ≤ m₂) : EvalsToInTime step a b m₂ where
  steps := h.steps
  evals_in_steps := h.evals_in_steps
  steps_le_m := h.steps_le_m.trans hle

private def liftCfg (c : M.tm.Cfg) : (wrapTM M).Cfg where
  l := c.l.map Sum.inr
  var := (preσInit, c.var)
  stk := mkPreStk M [] [] [] [] [] [] [] [] c.stk

private lemma stepAux_liftStmt (q : TM2.Stmt M.tm.Γ M.tm.Λ M.tm.σ)
    (v : M.tm.σ) (S : ∀ k : M.tm.K, List (M.tm.Γ k)) :
    TM2.stepAux (liftStmt M q) (preσInit, v) (mkPreStk M [] [] [] [] [] [] [] [] S) =
      liftCfg M (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k g q ih =>
    dsimp only [liftStmt, TM2.stepAux, mkPreStk]
    rw [update_mkPreStk_inr]
    exact ih v (Function.update S k (g v :: S k))
  | peek k g q ih =>
    dsimp only [liftStmt, TM2.stepAux, mkPreStk]
    exact ih (g v (S k).head?) S
  | pop k g q ih =>
    dsimp only [liftStmt, TM2.stepAux, mkPreStk]
    rw [update_mkPreStk_inr]
    exact ih (g v (S k).head?) (Function.update S k (S k).tail)
  | load g q ih =>
    dsimp only [liftStmt, TM2.stepAux]
    exact ih (g v) S
  | branch g q₁ q₂ ih₁ ih₂ =>
    dsimp only [liftStmt, TM2.stepAux]
    cases g v
    · exact ih₂ v S
    · exact ih₁ v S
  | goto g => rfl
  | halt => rfl

private lemma step_liftCfg (c : M.tm.Cfg) :
    (wrapTM M).step (liftCfg M c) = (M.tm.step c).map (liftCfg M) := by
  rcases c with ⟨l, var, stk⟩
  cases l with
  | none => rfl
  | some l =>
    exact congrArg some (stepAux_liftStmt M (M.tm.m l) var stk)

private lemma iterate_step_liftCfg (n : ℕ) (c : M.tm.Cfg) :
    (flip Option.bind (wrapTM M).step)^[n] (some (liftCfg M c)) =
      ((flip Option.bind M.tm.step)^[n] (some c)).map (liftCfg M) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    simp only [flip, Option.bind_some, step_liftCfg]
    cases h : M.tm.step c with
    | none =>
      simp only [Option.map_none]
      clear ih h c
      induction n with
      | zero => rfl
      | succ k ihk =>
        rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
        simp only [flip, Option.bind_none]
        exact ihk
    | some c' =>
      simp only [Option.map_some]
      exact ih c'

private lemma liftCfg_initList (s : List (M.tm.Γ M.tm.k₀)) :
    liftCfg M (initList M.tm s) =
      ⟨some (Sum.inr M.tm.main), (preσInit, M.tm.initialState),
        mkPreStk M [] [] [] [] [] [] [] [] (mkInitRhs M s)⟩ := by
  rfl

private lemma liftCfg_haltList (s : List (M.tm.Γ M.tm.k₁)) :
    liftCfg M (haltList M.tm s) = haltList (wrapTM M) s := by
  apply cfg_ext
  · rfl
  · rfl
  · funext k
    cases k with
    | inl pk => cases pk <;> simp [liftCfg, haltList, wrapTM, mkPreStk]
    | inr rk =>
      simp only [liftCfg, haltList, wrapTM, mkPreStk]
      by_cases hrk : rk = M.tm.k₁
      · subst hrk; simp
      · simp [hrk]

private def simulateM {s : List (M.tm.Γ M.tm.k₀)} {out : List (M.tm.Γ M.tm.k₁)} {m : ℕ}
    (h : TM2OutputsInTime M.tm s (some out) m) :
    EvalsToInTime (wrapTM M).step
      ⟨some (Sum.inr M.tm.main), (preσInit, M.tm.initialState),
        mkPreStk M [] [] [] [] [] [] [] [] (mkInitRhs M s)⟩
      (some (haltList (wrapTM M) out)) m where
  steps := h.steps
  evals_in_steps := by
    rw [← liftCfg_initList]
    have hstep := iterate_step_liftCfg M h.steps (initList M.tm s)
    change (flip Option.bind (wrapTM M).step)^[h.steps] (some (liftCfg M (initList M.tm s))) = _
    rw [hstep]
    have hev := h.evals_in_steps
    change (flip Option.bind M.tm.step)^[h.steps] (some (initList M.tm s)) =
      some (haltList M.tm out) at hev
    rw [hev, Option.map_some, liftCfg_haltList]
  steps_le_m := h.steps_le_m

/- ### Section 4: Phase-by-Phase Execution Lemmas -/

private def runReadS (s rest : List Bool) (acc : ℕ) (p : Preσ) :
    EvalsToInTime (wrapTM M).step
      ⟨some (Sum.inl .readS), (p, M.tm.initialState),
        mkPreStk M (delimit (bitEncode s) ++ rest) [] (List.replicate acc true) [] [] [] [] []
          (emptyRhs M)⟩
      (some ⟨some (Sum.inl .logCheck), ((p.1, some false, none), M.tm.initialState),
        mkPreStk M rest [] (List.replicate (s.length + acc) true) [] [] [] [] []
          (emptyRhs M)⟩)
      (s.length + 1) := by
  induction s generalizing acc p with
  | nil =>
    refine evalsStep (wrapTM M).step ?_
    rw [bitEncode_list_bool_nil]
    dsimp only [FinTM2.step, wrapTM, wrapProg, preProg, delimit, TM2.step, List.cons_append,
      List.nil_append, List.length_nil]
    have hbf : decide ((some false : Option Bool) = some true) = false := by decide
    rw [Nat.zero_add, stepAux_pop_inp, TM2.stepAux]
    dsimp only
    rw [hbf]
    rfl
  | cons b s ih =>
    have h1 : (wrapTM M).step
        ⟨some (Sum.inl .readS), (p, M.tm.initialState),
          mkPreStk M (delimit (bitEncode (b :: s)) ++ rest) [] (List.replicate acc true)
            [] [] [] [] [] (emptyRhs M)⟩ =
        some ⟨some (Sum.inl .readS), ((p.1, some true, none), M.tm.initialState),
          mkPreStk M (delimit (bitEncode s) ++ rest) [] (List.replicate (acc + 1) true)
            [] [] [] [] [] (emptyRhs M)⟩ := by
      rw [bitEncode_list_bool_cons, List.replicate_succ]
      dsimp only [FinTM2.step, wrapTM, wrapProg, preProg, delimit, TM2.step, List.cons_append]
      rw [stepAux_pop_inp, TM2.stepAux]
      dsimp only [decide_true, Bool.cond_true]
      rw [stepAux_pop_inp, stepAux_pop_inp, stepAux_pop_inp, stepAux_pop_inp, stepAux_pop_inp,
        TM2.stepAux]
      dsimp only [mkPreStk]
      rw [update_mkPreStk_suR]
      rfl
    have h2 := ih (acc + 1) (p.1, some true, none)
    have hlen : s.length + (acc + 1) = (b :: s).length + acc := by simp; omega
    rw [hlen] at h2
    exact evalsMono (evalsTrans (evalsStep _ h1) h2) (by dsimp only [List.length_cons]; omega)

private def runHalve (n : ℕ) :
    ∀ (rest ks : List Bool) (acc : ℕ) (p : Preσ),
      EvalsToInTime (wrapTM M).step
        ⟨some (Sum.inl .halve), (p, M.tm.initialState),
          mkPreStk M rest ks (List.replicate n true) [] [] (List.replicate acc true) [] []
            (emptyRhs M)⟩
        (some ⟨some (Sum.inl .moveCnt), ((p.1, none, none), M.tm.initialState),
          mkPreStk M rest (true :: ks) [] [] [] (List.replicate (acc + n / 2) true) [] []
            (emptyRhs M)⟩)
        (n / 2 + 1) := by
  match n with
  | 0 =>
    intro rest ks acc p
    refine evalsStep (wrapTM M).step ?_
    simp [FinTM2.step, wrapTM, wrapProg, preProg, TM2.step, TM2.stepAux, mkPreStk,
      update_mkPreStk_suR, update_mkPreStk_kStack]; rfl
  | 1 =>
    intro rest ks acc p
    refine evalsStep (wrapTM M).step ?_
    simp [FinTM2.step, wrapTM, wrapProg, preProg, TM2.step, TM2.stepAux, mkPreStk,
      update_mkPreStk_suR, update_mkPreStk_kStack]; rfl
  | m + 2 =>
    intro rest ks acc p
    have h1 : (wrapTM M).step
        ⟨some (Sum.inl .halve), (p, M.tm.initialState),
          mkPreStk M rest ks (List.replicate (m + 2) true) [] [] (List.replicate acc true) [] []
            (emptyRhs M)⟩ =
        some ⟨some (Sum.inl .halve), ((p.1, some true, some true), M.tm.initialState),
          mkPreStk M rest ks (List.replicate m true) [] [] (List.replicate (acc + 1) true) [] []
            (emptyRhs M)⟩ := by
      rw [List.replicate_succ, List.replicate_succ, List.replicate_succ]
      simp [FinTM2.step, wrapTM, wrapProg, preProg, TM2.step, TM2.stepAux, mkPreStk,
        update_mkPreStk_suR, update_mkPreStk_svR]; rfl
    have h2 := runHalve m rest ks (acc + 1) (p.1, some true, some true)
    have hdiv : acc + 1 + m / 2 = acc + (m + 2) / 2 := by omega
    rw [hdiv] at h2
    exact evalsMono (evalsTrans (evalsStep _ h1) h2) (by omega)

private def runMoveCnt (r : ℕ) (rest ks : List Bool) (a : ℕ) (p : Preσ) :
    EvalsToInTime (wrapTM M).step
      ⟨some (Sum.inl .moveCnt), (p, M.tm.initialState),
        mkPreStk M rest ks (List.replicate a true) [] [] (List.replicate r true) [] []
          (emptyRhs M)⟩
      (some ⟨some (Sum.inl .logCheck), ((p.1, none, none), M.tm.initialState),
        mkPreStk M rest ks (List.replicate (r + a) true) [] [] [] [] []
          (emptyRhs M)⟩)
      (r + 1) := by
  induction r generalizing a p with
  | zero =>
    refine evalsStep (wrapTM M).step ?_
    simp [FinTM2.step, wrapTM, wrapProg, preProg, TM2.step, TM2.stepAux, mkPreStk,
      update_mkPreStk_svR]; rfl
  | succ r ih =>
    have h1 : (wrapTM M).step
        ⟨some (Sum.inl .moveCnt), (p, M.tm.initialState),
          mkPreStk M rest ks (List.replicate a true) [] [] (List.replicate (r + 1) true) [] []
            (emptyRhs M)⟩ =
        some ⟨some (Sum.inl .moveCnt), ((p.1, some true, none), M.tm.initialState),
          mkPreStk M rest ks (List.replicate (a + 1) true) [] [] (List.replicate r true) [] []
            (emptyRhs M)⟩ := by
      rw [List.replicate_succ, List.replicate_succ]
      simp [FinTM2.step, wrapTM, wrapProg, preProg, TM2.step, TM2.stepAux, mkPreStk,
        update_mkPreStk_svR, update_mkPreStk_suR]; rfl
    have h2 := ih (a + 1) (p.1, some true, none)
    have hsum : r + (a + 1) = r + 1 + a := by omega
    rw [hsum] at h2
    exact evalsMono (evalsTrans (evalsStep _ h1) h2) (by omega)

private def runLogLoop (n : ℕ) :
    ∀ (rest ks : List Bool) (p : Preσ),
      EvalsToInTime (wrapTM M).step
        ⟨some (Sum.inl .logCheck), (p, M.tm.initialState),
          mkPreStk M rest ks (List.replicate n true) [] [] [] [] [] (emptyRhs M)⟩
        (some ⟨some (Sum.inl .readU), ((p.1, none, none), M.tm.initialState),
          mkPreStk M rest (List.replicate (Nat.log 2 n + 1) true ++ ks) [] [] [] [] [] []
            (emptyRhs M)⟩)
        (4 * n + 1) := by
  match n with
  | 0 =>
    intro rest ks p
    refine evalsStep (wrapTM M).step ?_
    simp [FinTM2.step, wrapTM, wrapProg, preProg, TM2.step, TM2.stepAux, mkPreStk,
      update_mkPreStk_suR, update_mkPreStk_kStack]; rfl
  | 1 =>
    intro rest ks p
    refine evalsMono (evalsStep (wrapTM M).step ?_) (by omega)
    simp [FinTM2.step, wrapTM, wrapProg, preProg, TM2.step, TM2.stepAux, mkPreStk,
      update_mkPreStk_suR, update_mkPreStk_kStack]; rfl
  | m + 2 =>
    intro rest ks p
    have h1 : (wrapTM M).step
        ⟨some (Sum.inl .logCheck), (p, M.tm.initialState),
          mkPreStk M rest ks (List.replicate (m + 2) true) [] [] [] [] [] (emptyRhs M)⟩ =
        some ⟨some (Sum.inl .halve), ((p.1, some true, some true), M.tm.initialState),
          mkPreStk M rest ks (List.replicate m true) [] [] (List.replicate 1 true) [] []
            (emptyRhs M)⟩ := by
      rw [List.replicate_succ, List.replicate_succ, List.replicate_one]
      simp [FinTM2.step, wrapTM, wrapProg, preProg, TM2.step, TM2.stepAux, mkPreStk,
        update_mkPreStk_suR, update_mkPreStk_svR]; rfl
    have h2 := runHalve M m rest ks 1 (p.1, some true, some true)
    have h3 := runMoveCnt M (1 + m / 2) rest (true :: ks) 0 (p.1, none, none)
    have hdiv : 1 + m / 2 = (m + 2) / 2 := by omega
    rw [Nat.add_zero, hdiv] at h3
    rw [hdiv] at h2
    have : (m + 2) / 2 < m + 2 := by omega
    have h4 := runLogLoop ((m + 2) / 2) rest (true :: ks) (p.1, none, none)
    have hlog : Nat.log 2 ((m + 2) / 2) + 1 = Nat.log 2 (m + 2) := by
      symm
      exact Nat.log_of_one_lt_of_le (by decide : 1 < 2) (by omega : 2 ≤ m + 2)
    rw [replicate_append_cons, hlog] at h4
    have h12 := evalsTrans (evalsStep _ h1) h2
    have h123 := evalsTrans h12 h3
    have h1234 := evalsTrans h123 h4
    exact evalsMono h1234 (by omega)
termination_by n

private def runReadU (a rest ks suR suR2 : List Bool) (p : Preσ) :
    EvalsToInTime (wrapTM M).step
      ⟨some (Sum.inl .readU), (p, M.tm.initialState),
        mkPreStk M (delimit a ++ rest) ks suR [] suR2 [] [] [] (emptyRhs M)⟩
      (some ⟨some (Sum.inl .readV), ((p.1, some false, none), M.tm.initialState),
        mkPreStk M rest ks (a.reverse ++ suR) [] (a.reverse ++ suR2) [] [] [] (emptyRhs M)⟩)
      (a.length + 1) := by
  induction a generalizing suR suR2 p with
  | nil =>
    refine evalsStep (wrapTM M).step ?_
    simp [FinTM2.step, wrapTM, wrapProg, preProg, delimit, TM2.step, TM2.stepAux, mkPreStk,
      update_mkPreStk_inp]; rfl
  | cons b a ih =>
    have h1 : (wrapTM M).step
        ⟨some (Sum.inl .readU), (p, M.tm.initialState),
          mkPreStk M (delimit (b :: a) ++ rest) ks suR [] suR2 [] [] [] (emptyRhs M)⟩ =
        some ⟨some (Sum.inl .readU), ((p.1, some b, none), M.tm.initialState),
          mkPreStk M (delimit a ++ rest) ks (b :: suR) [] (b :: suR2) [] [] [] (emptyRhs M)⟩ := by
      simp [FinTM2.step, wrapTM, wrapProg, preProg, delimit, TM2.step, TM2.stepAux, mkPreStk,
        update_mkPreStk_inp, update_mkPreStk_suR, update_mkPreStk_suR2]; rfl
    have h2 := ih (b :: suR) (b :: suR2) (p.1, some b, none)
    have hcat1 : a.reverse ++ (b :: suR) = (b :: a).reverse ++ suR := by simp [List.append_assoc]
    have hcat2 : a.reverse ++ (b :: suR2) = (b :: a).reverse ++ suR2 := by simp [List.append_assoc]
    rw [hcat1, hcat2] at h2
    exact evalsMono (evalsTrans (evalsStep _ h1) h2) (by dsimp only [List.length_cons]; omega)

private def runReadV (v ks suR suR2 svR svR2 : List Bool) (p : Preσ) :
    EvalsToInTime (wrapTM M).step
      ⟨some (Sum.inl .readV), (p, M.tm.initialState),
        mkPreStk M v ks suR [] suR2 svR [] svR2 (emptyRhs M)⟩
      (some ⟨some (Sum.inl .revU), ((p.1, none, none), M.tm.initialState),
        mkPreStk M [] ks suR [] suR2 (v.reverse ++ svR) [] (v.reverse ++ svR2) (emptyRhs M)⟩)
      (v.length + 1) := by
  induction v generalizing svR svR2 p with
  | nil =>
    refine evalsStep (wrapTM M).step ?_
    simp [FinTM2.step, wrapTM, wrapProg, preProg, TM2.step, TM2.stepAux, mkPreStk,
      update_mkPreStk_inp]; rfl
  | cons b v ih =>
    have h1 : (wrapTM M).step
        ⟨some (Sum.inl .readV), (p, M.tm.initialState),
          mkPreStk M (b :: v) ks suR [] suR2 svR [] svR2 (emptyRhs M)⟩ =
        some ⟨some (Sum.inl .readV), ((p.1, some b, none), M.tm.initialState),
          mkPreStk M v ks suR [] suR2 (b :: svR) [] (b :: svR2) (emptyRhs M)⟩ := by
      simp [FinTM2.step, wrapTM, wrapProg, preProg, TM2.step, TM2.stepAux, mkPreStk,
        update_mkPreStk_inp, update_mkPreStk_svR, update_mkPreStk_svR2]; rfl
    have h2 := ih (b :: svR) (b :: svR2) (p.1, some b, none)
    have hcat1 : v.reverse ++ (b :: svR) = (b :: v).reverse ++ svR := by simp [List.append_assoc]
    have hcat2 : v.reverse ++ (b :: svR2) = (b :: v).reverse ++ svR2 := by simp [List.append_assoc]
    rw [hcat1, hcat2] at h2
    exact evalsMono (evalsTrans (evalsStep _ h1) h2) (by dsimp only [List.length_cons]; omega)

private def runRevU (suR su ks suR2 svR svR2 : List Bool) (p : Preσ) :
    EvalsToInTime (wrapTM M).step
      ⟨some (Sum.inl .revU), (p, M.tm.initialState),
        mkPreStk M [] ks suR su suR2 svR [] svR2 (emptyRhs M)⟩
      (some ⟨some (Sum.inl .revV), ((p.1, none, none), M.tm.initialState),
        mkPreStk M [] ks [] (suR.reverse ++ su) suR2 svR [] svR2 (emptyRhs M)⟩)
      (suR.length + 1) := by
  induction suR generalizing su p with
  | nil =>
    refine evalsStep (wrapTM M).step ?_
    simp [FinTM2.step, wrapTM, wrapProg, preProg, TM2.step, TM2.stepAux, mkPreStk,
      update_mkPreStk_suR]; rfl
  | cons b s ih =>
    have h1 : (wrapTM M).step
        ⟨some (Sum.inl .revU), (p, M.tm.initialState),
          mkPreStk M [] ks (b :: s) su suR2 svR [] svR2 (emptyRhs M)⟩ =
        some ⟨some (Sum.inl .revU), ((p.1, some b, none), M.tm.initialState),
          mkPreStk M [] ks s (b :: su) suR2 svR [] svR2 (emptyRhs M)⟩ := by
      simp [FinTM2.step, wrapTM, wrapProg, preProg, TM2.step, TM2.stepAux, mkPreStk,
        update_mkPreStk_suR, update_mkPreStk_su]; rfl
    have h2 := ih (b :: su) (p.1, some b, none)
    have hcat : s.reverse ++ (b :: su) = (b :: s).reverse ++ su := by simp [List.append_assoc]
    rw [hcat] at h2
    exact evalsMono (evalsTrans (evalsStep _ h1) h2) (by dsimp only [List.length_cons]; omega)

private def runRevV (svR sv ks su suR2 svR2 : List Bool) (p : Preσ) :
    EvalsToInTime (wrapTM M).step
      ⟨some (Sum.inl .revV), (p, M.tm.initialState),
        mkPreStk M [] ks [] su suR2 svR sv svR2 (emptyRhs M)⟩
      (some ⟨some (Sum.inl .cmpUV), ((.eq, none, none), M.tm.initialState),
        mkPreStk M [] ks [] su suR2 [] (svR.reverse ++ sv) svR2 (emptyRhs M)⟩)
      (svR.length + 1) := by
  induction svR generalizing sv p with
  | nil =>
    refine evalsStep (wrapTM M).step ?_
    simp [FinTM2.step, wrapTM, wrapProg, preProg, TM2.step, TM2.stepAux, mkPreStk,
      update_mkPreStk_svR]; rfl
  | cons b s ih =>
    have h1 : (wrapTM M).step
        ⟨some (Sum.inl .revV), (p, M.tm.initialState),
          mkPreStk M [] ks [] su suR2 (b :: s) sv svR2 (emptyRhs M)⟩ =
        some ⟨some (Sum.inl .revV), ((p.1, some b, none), M.tm.initialState),
          mkPreStk M [] ks [] su suR2 s (b :: sv) svR2 (emptyRhs M)⟩ := by
      simp [FinTM2.step, wrapTM, wrapProg, preProg, TM2.step, TM2.stepAux, mkPreStk,
        update_mkPreStk_svR, update_mkPreStk_sv]; rfl
    have h2 := ih (b :: sv) (p.1, some b, none)
    have hcat : s.reverse ++ (b :: sv) = (b :: s).reverse ++ sv := by simp [List.append_assoc]
    rw [hcat] at h2
    exact evalsMono (evalsTrans (evalsStep _ h1) h2) (by dsimp only [List.length_cons]; omega)

private def runClearSVLt (sv ks suR2 svR2 : List Bool) (p : Preσ) :
    EvalsToInTime (wrapTM M).step
      ⟨some (Sum.inl .clearSV_lt), (p, M.tm.initialState),
        mkPreStk M [] ks [] [] suR2 [] sv svR2 (emptyRhs M)⟩
      (some ⟨some (Sum.inl .emitMaxV), ((p.1, none, none), M.tm.initialState),
        mkPreStk M [] ks [] [] suR2 [] [] svR2 (emptyRhs M)⟩)
      (sv.length + 1) := by
  induction sv generalizing p with
  | nil =>
    refine evalsStep (wrapTM M).step ?_
    simp [FinTM2.step, wrapTM, wrapProg, preProg, TM2.step, TM2.stepAux, mkPreStk,
      update_mkPreStk_sv]; rfl
  | cons b s ih =>
    have h1 : (wrapTM M).step
        ⟨some (Sum.inl .clearSV_lt), (p, M.tm.initialState),
          mkPreStk M [] ks [] [] suR2 [] (b :: s) svR2 (emptyRhs M)⟩ =
        some ⟨some (Sum.inl .clearSV_lt), ((p.1, some b, none), M.tm.initialState),
          mkPreStk M [] ks [] [] suR2 [] s svR2 (emptyRhs M)⟩ := by
      simp [FinTM2.step, wrapTM, wrapProg, preProg, TM2.step, TM2.stepAux, mkPreStk,
        update_mkPreStk_sv]; rfl
    exact evalsMono (evalsTrans (evalsStep _ h1) (ih (p.1, some b, none)))
      (by dsimp only [List.length_cons]; omega)

private def runClearSUGe (su ks suR2 svR2 : List Bool) (p : Preσ) :
    EvalsToInTime (wrapTM M).step
      ⟨some (Sum.inl .clearSU_ge), (p, M.tm.initialState),
        mkPreStk M [] ks [] su suR2 [] [] svR2 (emptyRhs M)⟩
      (some ⟨some (Sum.inl .emitMaxU), ((p.1, none, none), M.tm.initialState),
        mkPreStk M [] ks [] [] suR2 [] [] svR2 (emptyRhs M)⟩)
      (su.length + 1) := by
  induction su generalizing p with
  | nil =>
    refine evalsStep (wrapTM M).step ?_
    simp [FinTM2.step, wrapTM, wrapProg, preProg, TM2.step, TM2.stepAux, mkPreStk,
      update_mkPreStk_su]; rfl
  | cons b s ih =>
    have h1 : (wrapTM M).step
        ⟨some (Sum.inl .clearSU_ge), (p, M.tm.initialState),
          mkPreStk M [] ks [] (b :: s) suR2 [] [] svR2 (emptyRhs M)⟩ =
        some ⟨some (Sum.inl .clearSU_ge), ((p.1, some b, none), M.tm.initialState),
          mkPreStk M [] ks [] s suR2 [] [] svR2 (emptyRhs M)⟩ := by
      simp [FinTM2.step, wrapTM, wrapProg, preProg, TM2.step, TM2.stepAux, mkPreStk,
        update_mkPreStk_su]; rfl
    exact evalsMono (evalsTrans (evalsStep _ h1) (ih (p.1, some b, none)))
      (by dsimp only [List.length_cons]; omega)

private def runEmitMaxV (svR2 ks suR2 : List Bool) (acc : List (M.tm.Γ M.tm.k₀)) (p : Preσ) :
    EvalsToInTime (wrapTM M).step
      ⟨some (Sum.inl .emitMaxV), (p, M.tm.initialState),
        mkPreStk M [] ks [] [] suR2 [] [] svR2 (mkInitRhs M acc)⟩
      (some ⟨some (Sum.inl .emitMinU), ((p.1, none, none), M.tm.initialState),
        mkPreStk M [] ks [] [] suR2 [] [] []
          (mkInitRhs M (M.inputAlphabet.symm false :: (List.map M.inputAlphabet.symm svR2.reverse ++ acc)))⟩)
      (svR2.length + 1) := by
  induction svR2 generalizing acc p with
  | nil =>
    refine evalsStep (wrapTM M).step ?_
    simp only [FinTM2.step, wrapTM, wrapProg, preProg, TM2.step, TM2.stepAux, mkPreStk,
      update_mkPreStk_svR2, List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_false]
    rw [update_mkPreStk_inr]
    have hmk : mkInitRhs M acc M.tm.k₀ = acc := by simp [mkInitRhs]
    rw [hmk, update_mkInitRhs]
    rfl
  | cons b s ih =>
    have h1 : (wrapTM M).step
        ⟨some (Sum.inl .emitMaxV), (p, M.tm.initialState),
          mkPreStk M [] ks [] [] suR2 [] [] (b :: s) (mkInitRhs M acc)⟩ =
        some ⟨some (Sum.inl .emitMaxV), ((p.1, some b, none), M.tm.initialState),
          mkPreStk M [] ks [] [] suR2 [] [] s (mkInitRhs M (M.inputAlphabet.symm b :: acc))⟩ := by
      dsimp only [FinTM2.step, wrapTM, wrapProg, preProg, TM2.step]
      rw [TM2.stepAux]
      dsimp only [mkPreStk, List.head?_cons, List.tail_cons]
      rw [update_mkPreStk_svR2, TM2.stepAux]
      dsimp only [Option.isSome_some, Bool.cond_true, Option.getD_some]
      rw [stepAux_push_k0]
      rfl
    have h2 := ih (M.inputAlphabet.symm b :: acc) (p.1, some b, none)
    have hcat : List.map M.inputAlphabet.symm s.reverse ++ (M.inputAlphabet.symm b :: acc) =
        List.map M.inputAlphabet.symm (b :: s).reverse ++ acc := by
      simp [List.append_assoc]
    rw [hcat] at h2
    exact evalsMono (evalsTrans (evalsStep _ h1) h2) (by dsimp only [List.length_cons]; omega)

private def runEmitMinU (suR2 ks : List Bool) (acc : List (M.tm.Γ M.tm.k₀)) (p : Preσ) :
    EvalsToInTime (wrapTM M).step
      ⟨some (Sum.inl .emitMinU), (p, M.tm.initialState),
        mkPreStk M [] ks [] [] suR2 [] [] [] (mkInitRhs M acc)⟩
      (some ⟨some (Sum.inl .emitS), ((p.1, none, none), M.tm.initialState),
        mkPreStk M [] ks [] [] [] [] [] []
          (mkInitRhs M (M.inputAlphabet.symm false ::
            (List.map M.inputAlphabet.symm (pairBits suR2.reverse) ++ acc)))⟩)
      (suR2.length + 1) := by
  induction suR2 generalizing acc p with
  | nil =>
    refine evalsStep (wrapTM M).step ?_
    simp only [FinTM2.step, wrapTM, wrapProg, preProg, TM2.step, TM2.stepAux, mkPreStk,
      update_mkPreStk_suR2, List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_false]
    rw [update_mkPreStk_inr]
    have hmk : mkInitRhs M acc M.tm.k₀ = acc := by simp [mkInitRhs]
    rw [hmk, update_mkInitRhs]
    rfl
  | cons b s ih =>
    have h1 : (wrapTM M).step
        ⟨some (Sum.inl .emitMinU), (p, M.tm.initialState),
          mkPreStk M [] ks [] [] (b :: s) [] [] [] (mkInitRhs M acc)⟩ =
        some ⟨some (Sum.inl .emitMinU), ((p.1, some b, none), M.tm.initialState),
          mkPreStk M [] ks [] [] s [] [] []
            (mkInitRhs M (M.inputAlphabet.symm true :: M.inputAlphabet.symm b :: acc))⟩ := by
      dsimp only [FinTM2.step, wrapTM, wrapProg, preProg, TM2.step]
      rw [TM2.stepAux]
      dsimp only [mkPreStk, List.head?_cons, List.tail_cons]
      rw [update_mkPreStk_suR2, TM2.stepAux]
      dsimp only [Option.isSome_some, Bool.cond_true, Option.getD_some]
      rw [stepAux_push_k0, stepAux_push_k0]
      rfl
    have h2 := ih (M.inputAlphabet.symm true :: M.inputAlphabet.symm b :: acc) (p.1, some b, none)
    have hcat : List.map M.inputAlphabet.symm (pairBits s.reverse) ++
          (M.inputAlphabet.symm true :: M.inputAlphabet.symm b :: acc) =
        List.map M.inputAlphabet.symm (pairBits (b :: s).reverse) ++ acc := by
      rw [List.reverse_cons, pairBits_append]
      simp [pairBits, List.append_assoc]
    rw [hcat] at h2
    exact evalsMono (evalsTrans (evalsStep _ h1) h2) (by dsimp only [List.length_cons]; omega)

private def runEmitMaxU (suR2 ks svR2 : List Bool) (acc : List (M.tm.Γ M.tm.k₀)) (p : Preσ) :
    EvalsToInTime (wrapTM M).step
      ⟨some (Sum.inl .emitMaxU), (p, M.tm.initialState),
        mkPreStk M [] ks [] [] suR2 [] [] svR2 (mkInitRhs M acc)⟩
      (some ⟨some (Sum.inl .emitMinV), ((p.1, none, none), M.tm.initialState),
        mkPreStk M [] ks [] [] [] [] [] svR2
          (mkInitRhs M (M.inputAlphabet.symm false :: (List.map M.inputAlphabet.symm suR2.reverse ++ acc)))⟩)
      (suR2.length + 1) := by
  induction suR2 generalizing acc p with
  | nil =>
    refine evalsStep (wrapTM M).step ?_
    simp only [FinTM2.step, wrapTM, wrapProg, preProg, TM2.step, TM2.stepAux, mkPreStk,
      update_mkPreStk_suR2, List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_false]
    rw [update_mkPreStk_inr]
    have hmk : mkInitRhs M acc M.tm.k₀ = acc := by simp [mkInitRhs]
    rw [hmk, update_mkInitRhs]
    rfl
  | cons b s ih =>
    have h1 : (wrapTM M).step
        ⟨some (Sum.inl .emitMaxU), (p, M.tm.initialState),
          mkPreStk M [] ks [] [] (b :: s) [] [] svR2 (mkInitRhs M acc)⟩ =
        some ⟨some (Sum.inl .emitMaxU), ((p.1, some b, none), M.tm.initialState),
          mkPreStk M [] ks [] [] s [] [] svR2 (mkInitRhs M (M.inputAlphabet.symm b :: acc))⟩ := by
      dsimp only [FinTM2.step, wrapTM, wrapProg, preProg, TM2.step]
      rw [TM2.stepAux]
      dsimp only [mkPreStk, List.head?_cons, List.tail_cons]
      rw [update_mkPreStk_suR2, TM2.stepAux]
      dsimp only [Option.isSome_some, Bool.cond_true, Option.getD_some]
      rw [stepAux_push_k0]
      rfl
    have h2 := ih (M.inputAlphabet.symm b :: acc) (p.1, some b, none)
    have hcat : List.map M.inputAlphabet.symm s.reverse ++ (M.inputAlphabet.symm b :: acc) =
        List.map M.inputAlphabet.symm (b :: s).reverse ++ acc := by
      simp [List.append_assoc]
    rw [hcat] at h2
    exact evalsMono (evalsTrans (evalsStep _ h1) h2) (by dsimp only [List.length_cons]; omega)

private def runEmitMinV (svR2 ks : List Bool) (acc : List (M.tm.Γ M.tm.k₀)) (p : Preσ) :
    EvalsToInTime (wrapTM M).step
      ⟨some (Sum.inl .emitMinV), (p, M.tm.initialState),
        mkPreStk M [] ks [] [] [] [] [] svR2 (mkInitRhs M acc)⟩
      (some ⟨some (Sum.inl .emitS), ((p.1, none, none), M.tm.initialState),
        mkPreStk M [] ks [] [] [] [] [] []
          (mkInitRhs M (M.inputAlphabet.symm false ::
            (List.map M.inputAlphabet.symm (pairBits svR2.reverse) ++ acc)))⟩)
      (svR2.length + 1) := by
  induction svR2 generalizing acc p with
  | nil =>
    refine evalsStep (wrapTM M).step ?_
    simp only [FinTM2.step, wrapTM, wrapProg, preProg, TM2.step, TM2.stepAux, mkPreStk,
      update_mkPreStk_svR2, List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_false]
    rw [update_mkPreStk_inr]
    have hmk : mkInitRhs M acc M.tm.k₀ = acc := by simp [mkInitRhs]
    rw [hmk, update_mkInitRhs]
    rfl
  | cons b s ih =>
    have h1 : (wrapTM M).step
        ⟨some (Sum.inl .emitMinV), (p, M.tm.initialState),
          mkPreStk M [] ks [] [] [] [] [] (b :: s) (mkInitRhs M acc)⟩ =
        some ⟨some (Sum.inl .emitMinV), ((p.1, some b, none), M.tm.initialState),
          mkPreStk M [] ks [] [] [] [] [] s
            (mkInitRhs M (M.inputAlphabet.symm true :: M.inputAlphabet.symm b :: acc))⟩ := by
      dsimp only [FinTM2.step, wrapTM, wrapProg, preProg, TM2.step]
      rw [TM2.stepAux]
      dsimp only [mkPreStk, List.head?_cons, List.tail_cons]
      rw [update_mkPreStk_svR2, TM2.stepAux]
      dsimp only [Option.isSome_some, Bool.cond_true, Option.getD_some]
      rw [stepAux_push_k0, stepAux_push_k0]
      rfl
    have h2 := ih (M.inputAlphabet.symm true :: M.inputAlphabet.symm b :: acc) (p.1, some b, none)
    have hcat : List.map M.inputAlphabet.symm (pairBits s.reverse) ++
          (M.inputAlphabet.symm true :: M.inputAlphabet.symm b :: acc) =
        List.map M.inputAlphabet.symm (pairBits (b :: s).reverse) ++ acc := by
      rw [List.reverse_cons, pairBits_append]
      simp [pairBits, List.append_assoc]
    rw [hcat] at h2
    exact evalsMono (evalsTrans (evalsStep _ h1) h2) (by dsimp only [List.length_cons]; omega)

private def runEmitS (k : ℕ) (acc : List (M.tm.Γ M.tm.k₀)) (p : Preσ) :
    EvalsToInTime (wrapTM M).step
      ⟨some (Sum.inl .emitS), (p, M.tm.initialState),
        mkPreStk M [] (List.replicate k true) [] [] [] [] [] [] (mkInitRhs M acc)⟩
      (some ⟨some (Sum.inr M.tm.main), (preσInit, M.tm.initialState),
        mkPreStk M [] [] [] [] [] [] [] []
          (mkInitRhs M (List.map M.inputAlphabet.symm (repeatSix k) ++ acc))⟩)
      (k + 1) := by
  induction k generalizing acc p with
  | zero =>
    refine evalsStep (wrapTM M).step ?_
    simp [FinTM2.step, wrapTM, wrapProg, preProg, repeatSix, TM2.step, TM2.stepAux, mkPreStk,
      update_mkPreStk_kStack]; rfl
  | succ k ih =>
    have h1 : (wrapTM M).step
        ⟨some (Sum.inl .emitS), (p, M.tm.initialState),
          mkPreStk M [] (List.replicate (k + 1) true) [] [] [] [] [] [] (mkInitRhs M acc)⟩ =
        some ⟨some (Sum.inl .emitS), ((p.1, some true, none), M.tm.initialState),
          mkPreStk M [] (List.replicate k true) [] [] [] [] [] []
            (mkInitRhs M (List.map M.inputAlphabet.symm [true, true, true, true, true, false] ++ acc))⟩ := by
      rw [List.replicate_succ]
      dsimp only [FinTM2.step, wrapTM, wrapProg, preProg, TM2.step]
      rw [TM2.stepAux]
      dsimp only [mkPreStk, List.head?_cons, List.tail_cons]
      rw [update_mkPreStk_kStack, TM2.stepAux]
      dsimp only [Option.isSome_some, Bool.cond_true]
      rw [stepAux_push_k0, stepAux_push_k0, stepAux_push_k0, stepAux_push_k0, stepAux_push_k0,
        stepAux_push_k0]
      rfl
    have h2 := ih (List.map M.inputAlphabet.symm [true, true, true, true, true, false] ++ acc)
      (p.1, some true, none)
    have hcat : List.map M.inputAlphabet.symm (repeatSix k) ++
          (List.map M.inputAlphabet.symm [true, true, true, true, true, false] ++ acc) =
        List.map M.inputAlphabet.symm (repeatSix (k + 1)) ++ acc := by
      rw [← List.append_assoc, ← List.map_append, repeatSix_append_six]
    rw [hcat] at h2
    exact evalsMono (evalsTrans (evalsStep _ h1) h2) (by omega)

private def runEmitLt (k : ℕ) (suR2 svR2 : List Bool) (p : Preσ) :
    EvalsToInTime (wrapTM M).step
      ⟨some (Sum.inl .emitMaxV), (p, M.tm.initialState),
        mkPreStk M [] (List.replicate k true) [] [] suR2 [] [] svR2 (emptyRhs M)⟩
      (some ⟨some (Sum.inr M.tm.main), (preσInit, M.tm.initialState),
        mkPreStk M [] [] [] [] [] [] [] []
          (mkInitRhs M (List.map M.inputAlphabet.symm
            (delimit (bitEncode (List.replicate k true)) ++
              (delimit suR2.reverse ++ svR2.reverse))))⟩)
      (svR2.length + suR2.length + k + 3) := by
  have h1 := runEmitMaxV M svR2 (List.replicate k true) suR2 [] p
  rw [← emptyRhs_eq_mkInitRhs_nil, List.append_nil] at h1
  have h2 := runEmitMinU M suR2 (List.replicate k true)
    (M.inputAlphabet.symm false :: List.map M.inputAlphabet.symm svR2.reverse) (p.1, none, none)
  have h3 := runEmitS M k
    (M.inputAlphabet.symm false ::
      (List.map M.inputAlphabet.symm (pairBits suR2.reverse) ++
        (M.inputAlphabet.symm false :: List.map M.inputAlphabet.symm svR2.reverse)))
    (p.1, none, none)
  have h12 := evalsTrans h1 h2
  have h123 := evalsTrans h12 h3
  have hpay :
      List.map M.inputAlphabet.symm (repeatSix k) ++
        (M.inputAlphabet.symm false ::
          (List.map M.inputAlphabet.symm (pairBits suR2.reverse) ++
            (M.inputAlphabet.symm false :: List.map M.inputAlphabet.symm svR2.reverse))) =
      List.map M.inputAlphabet.symm
        (delimit (bitEncode (List.replicate k true)) ++
          (delimit suR2.reverse ++ svR2.reverse)) := by
    rw [delimit_bitEncode_replicate_true, delimit_eq_pairBits_append]
    simp [List.append_assoc]
  rw [hpay] at h123
  exact evalsMono h123 (by omega)

private def runEmitGe (k : ℕ) (suR2 svR2 : List Bool) (p : Preσ) :
    EvalsToInTime (wrapTM M).step
      ⟨some (Sum.inl .emitMaxU), (p, M.tm.initialState),
        mkPreStk M [] (List.replicate k true) [] [] suR2 [] [] svR2 (emptyRhs M)⟩
      (some ⟨some (Sum.inr M.tm.main), (preσInit, M.tm.initialState),
        mkPreStk M [] [] [] [] [] [] [] []
          (mkInitRhs M (List.map M.inputAlphabet.symm
            (delimit (bitEncode (List.replicate k true)) ++
              (delimit svR2.reverse ++ suR2.reverse))))⟩)
      (suR2.length + svR2.length + k + 3) := by
  have h1 := runEmitMaxU M suR2 (List.replicate k true) svR2 [] p
  rw [← emptyRhs_eq_mkInitRhs_nil, List.append_nil] at h1
  have h2 := runEmitMinV M svR2 (List.replicate k true)
    (M.inputAlphabet.symm false :: List.map M.inputAlphabet.symm suR2.reverse) (p.1, none, none)
  have h3 := runEmitS M k
    (M.inputAlphabet.symm false ::
      (List.map M.inputAlphabet.symm (pairBits svR2.reverse) ++
        (M.inputAlphabet.symm false :: List.map M.inputAlphabet.symm suR2.reverse)))
    (p.1, none, none)
  have h12 := evalsTrans h1 h2
  have h123 := evalsTrans h12 h3
  have hpay :
      List.map M.inputAlphabet.symm (repeatSix k) ++
        (M.inputAlphabet.symm false ::
          (List.map M.inputAlphabet.symm (pairBits svR2.reverse) ++
            (M.inputAlphabet.symm false :: List.map M.inputAlphabet.symm suR2.reverse))) =
      List.map M.inputAlphabet.symm
        (delimit (bitEncode (List.replicate k true)) ++
          (delimit svR2.reverse ++ suR2.reverse)) := by
    rw [delimit_bitEncode_replicate_true, delimit_eq_pairBits_append]
    simp [List.append_assoc]
  rw [hpay] at h123
  exact evalsMono h123 (by omega)

private def runCmpAndFinish (su : List Bool) :
    ∀ (sv : List Bool) (k : ℕ) (suR2 svR2 : List Bool) (c : Cmp3) (ob₁ ob₂ : Option Bool),
      EvalsToInTime (wrapTM M).step
        ⟨some (Sum.inl .cmpUV), ((c, ob₁, ob₂), M.tm.initialState),
          mkPreStk M [] (List.replicate k true) [] su suR2 [] sv svR2 (emptyRhs M)⟩
        (some ⟨some (Sum.inr M.tm.main), (preσInit, M.tm.initialState),
          mkPreStk M [] [] [] [] [] [] [] []
            (mkInitRhs M (List.map M.inputAlphabet.symm
              (delimit (bitEncode (List.replicate k true)) ++
                if cmpLittleEndian su sv c then
                  delimit suR2.reverse ++ svR2.reverse
                else
                  delimit svR2.reverse ++ suR2.reverse)))⟩)
        (su.length + sv.length + suR2.length + svR2.length + k + 6) := by
  induction su with
  | nil =>
    intro sv k suR2 svR2 c ob₁ ob₂
    cases sv with
    | nil =>
      by_cases hc : c = .lt
      · subst hc
        have hstep : (wrapTM M).step
            ⟨some (Sum.inl .cmpUV), ((.lt, ob₁, ob₂), M.tm.initialState),
              mkPreStk M [] (List.replicate k true) [] [] suR2 [] [] svR2 (emptyRhs M)⟩ =
            some ⟨some (Sum.inl .emitMaxV), ((.lt, none, none), M.tm.initialState),
              mkPreStk M [] (List.replicate k true) [] [] suR2 [] [] svR2 (emptyRhs M)⟩ := by
          simp [FinTM2.step, wrapTM, wrapProg, preProg, TM2.step, TM2.stepAux, mkPreStk,
            update_mkPreStk_su, update_mkPreStk_sv]; rfl
        have h2 := runEmitLt M k suR2 svR2 (.lt, none, none)
        have htr := evalsTrans (evalsStep _ hstep) h2
        have hcmp : cmpLittleEndian [] [] .lt = true := rfl
        rw [hcmp, if_pos rfl]
        exact evalsMono htr (by omega)
      · have hstep : (wrapTM M).step
            ⟨some (Sum.inl .cmpUV), ((c, ob₁, ob₂), M.tm.initialState),
              mkPreStk M [] (List.replicate k true) [] [] suR2 [] [] svR2 (emptyRhs M)⟩ =
            some ⟨some (Sum.inl .emitMaxU), ((c, none, none), M.tm.initialState),
              mkPreStk M [] (List.replicate k true) [] [] suR2 [] [] svR2 (emptyRhs M)⟩ := by
          simp [FinTM2.step, wrapTM, wrapProg, preProg, TM2.step, TM2.stepAux, mkPreStk,
            update_mkPreStk_su, update_mkPreStk_sv, hc]; rfl
        have h2 := runEmitGe M k suR2 svR2 (c, none, none)
        have htr := evalsTrans (evalsStep _ hstep) h2
        have hcmp : cmpLittleEndian [] [] c = false := by simp [cmpLittleEndian, hc]
        rw [hcmp, if_neg Bool.false_ne_true]
        exact evalsMono htr (by omega)
    | cons b s =>
      have hstep : (wrapTM M).step
          ⟨some (Sum.inl .cmpUV), ((c, ob₁, ob₂), M.tm.initialState),
            mkPreStk M [] (List.replicate k true) [] [] suR2 [] (b :: s) svR2 (emptyRhs M)⟩ =
          some ⟨some (Sum.inl .clearSV_lt), ((c, none, some b), M.tm.initialState),
            mkPreStk M [] (List.replicate k true) [] [] suR2 [] s svR2 (emptyRhs M)⟩ := by
        simp [FinTM2.step, wrapTM, wrapProg, preProg, TM2.step, TM2.stepAux, mkPreStk,
          update_mkPreStk_su, update_mkPreStk_sv]; rfl
      have h2 := runClearSVLt M s (List.replicate k true) suR2 svR2 (c, none, some b)
      have h3 := runEmitLt M k suR2 svR2 (c, none, none)
      have h12 := evalsTrans (evalsStep _ hstep) h2
      have h123 := evalsTrans h12 h3
      have hcmp : cmpLittleEndian [] (b :: s) c = true := rfl
      rw [hcmp, if_pos rfl]
      exact evalsMono h123 (by dsimp only [List.length_nil, List.length_cons]; omega)
  | cons a sa ih =>
    intro sv k suR2 svR2 c ob₁ ob₂
    cases sv with
    | nil =>
      have hstep : (wrapTM M).step
          ⟨some (Sum.inl .cmpUV), ((c, ob₁, ob₂), M.tm.initialState),
            mkPreStk M [] (List.replicate k true) [] (a :: sa) suR2 [] [] svR2 (emptyRhs M)⟩ =
          some ⟨some (Sum.inl .clearSU_ge), ((c, some a, none), M.tm.initialState),
            mkPreStk M [] (List.replicate k true) [] sa suR2 [] [] svR2 (emptyRhs M)⟩ := by
        simp [FinTM2.step, wrapTM, wrapProg, preProg, TM2.step, TM2.stepAux, mkPreStk,
          update_mkPreStk_su, update_mkPreStk_sv]; rfl
      have h2 := runClearSUGe M sa (List.replicate k true) suR2 svR2 (c, some a, none)
      have h3 := runEmitGe M k suR2 svR2 (c, none, none)
      have h12 := evalsTrans (evalsStep _ hstep) h2
      have h123 := evalsTrans h12 h3
      have hcmp : cmpLittleEndian (a :: sa) [] c = false := rfl
      rw [hcmp, if_neg Bool.false_ne_true]
      exact evalsMono h123 (by dsimp only [List.length_nil, List.length_cons]; omega)
    | cons b sb =>
      let c' := updateCmp c a b
      have hstep : (wrapTM M).step
          ⟨some (Sum.inl .cmpUV), ((c, ob₁, ob₂), M.tm.initialState),
            mkPreStk M [] (List.replicate k true) [] (a :: sa) suR2 [] (b :: sb) svR2 (emptyRhs M)⟩ =
          some ⟨some (Sum.inl .cmpUV), ((c', none, none), M.tm.initialState),
            mkPreStk M [] (List.replicate k true) [] sa suR2 [] sb svR2 (emptyRhs M)⟩ := by
        simp [FinTM2.step, wrapTM, wrapProg, preProg, TM2.step, TM2.stepAux, mkPreStk,
          update_mkPreStk_su, update_mkPreStk_sv, c']; rfl
      have hrec := ih sb k suR2 svR2 c' none none
      have htr := evalsTrans (evalsStep _ hstep) hrec
      have hcmp : cmpLittleEndian (a :: sa) (b :: sb) c = cmpLittleEndian sa sb c' := rfl
      rw [hcmp]
      exact evalsMono htr (by dsimp only [List.length_cons]; omega)

private lemma initList_wrapTM (L : List Bool) :
    initList (wrapTM M) L =
      ⟨some (Sum.inl .readS), (preσInit, M.tm.initialState),
        mkPreStk M L [] [] [] [] [] [] [] (emptyRhs M)⟩ := by
  apply cfg_ext
  · rfl
  · rfl
  · funext k
    cases k with
    | inl pk => cases pk <;> simp [initList, wrapTM, mkPreStk]
    | inr rk => simp [initList, wrapTM, mkPreStk, emptyRhs]

private noncomputable def wrapComputable :
    TM2ComputableInPolyTime
      (BitstringEncoding.toEncoding (α := List Bool × ℕ × ℕ)).encode
      (BitstringEncoding.toEncoding (α := Bool)).encode
      (fun p : List Bool × ℕ × ℕ =>
        f (List.replicate (Nat.log 2 p.1.length + 1) true, min p.2.1 p.2.2, max p.2.1 p.2.2)) where
  tm := wrapTM M
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := M.outputAlphabet
  time := Polynomial.C 4 * Polynomial.X + Polynomial.C 15 +
    M.time.comp (Polynomial.C 2 * Polynomial.X + Polynomial.C 6)
  outputsFun x := by
    rcases x with ⟨s, u, v⟩
    let eu : List Bool := Computability.encodeNat u
    let ev : List Bool := Computability.encodeNat v
    let k : ℕ := Nat.log 2 s.length + 1
    let L : List Bool := delimit (bitEncode s) ++ (delimit eu ++ ev)
    let L' : List Bool := delimit (bitEncode (List.replicate k true)) ++
      (delimit (Computability.encodeNat (min u v)) ++ Computability.encodeNat (max u v))
    have hL_len : L.length = 6 * s.length + 2 * eu.length + ev.length + 2 := by
      simp [L, length_delimit, length_bitEncode_list_bool]
      omega
    have hk_le : k ≤ s.length + 1 := by
      have := nat_log2_le_self s.length
      omega
    have h1 := runReadS M s (delimit eu ++ ev) 0 preσInit
    rw [Nat.add_zero] at h1
    have h2 := runLogLoop M s.length (delimit eu ++ ev) [] (preσInit.1, some false, none)
    rw [List.append_nil] at h2
    have h3 := runReadU M eu ev (List.replicate k true) [] [] (preσInit.1, none, none)
    rw [List.append_nil] at h3
    have h4 := runReadV M ev (List.replicate k true) eu.reverse eu.reverse [] []
      (preσInit.1, some false, none)
    rw [List.append_nil] at h4
    have h5 := runRevU M eu.reverse [] (List.replicate k true) eu.reverse ev.reverse ev.reverse
      (preσInit.1, none, none)
    rw [List.reverse_reverse, List.append_nil] at h5
    have h6 := runRevV M ev.reverse [] (List.replicate k true) eu eu.reverse ev.reverse
      (preσInit.1, none, none)
    rw [List.reverse_reverse, List.append_nil] at h6
    have h7 := runCmpAndFinish M eu ev k eu.reverse ev.reverse .eq none none
    rw [List.reverse_reverse, List.reverse_reverse] at h7
    have h12 := evalsTrans h1 h2
    have h123 := evalsTrans h12 h3
    have h1234 := evalsTrans h123 h4
    have h12345 := evalsTrans h1234 h5
    have h123456 := evalsTrans h12345 h6
    have hpre := evalsTrans h123456 h7
    have hcmp_eq : cmpLittleEndian eu ev .eq = decide (u < v) := cmpLittleEndian_encodeNat u v
    have htarget :
        delimit (bitEncode (List.replicate k true)) ++
          (if cmpLittleEndian eu ev .eq then delimit eu ++ ev else delimit ev ++ eu) = L' := by
      rw [hcmp_eq]
      by_cases huv : u < v
      · have hle : u ≤ v := le_of_lt huv
        simp [L', eu, ev, huv, min_eq_left hle, max_eq_right hle]
      · have hle : v ≤ u := le_of_not_gt huv
        simp [L', eu, ev, huv, min_eq_right hle, max_eq_left hle]
    rw [htarget] at hpre
    have hL'_le : L'.length ≤ 2 * L.length + 6 := by
      by_cases huv : u < v
      · have hle : u ≤ v := le_of_lt huv
        have hlen' : L'.length = 6 * k + 2 * eu.length + ev.length + 2 := by
          simp [L', eu, ev, min_eq_left hle, max_eq_right hle, length_delimit,
            length_bitEncode_list_bool]
          omega
        omega
      · have hle : v ≤ u := le_of_not_gt huv
        have hlen' : L'.length = 6 * k + 2 * ev.length + eu.length + 2 := by
          simp [L', eu, ev, min_eq_right hle, max_eq_left hle, length_delimit,
            length_bitEncode_list_bool]
          omega
        omega
    have hpre_bound :
        (eu.length + ev.length + eu.reverse.length + ev.reverse.length + k + 6) +
          ((ev.reverse.length + 1) +
            ((eu.reverse.length + 1) +
              ((ev.length + 1) +
                ((eu.length + 1) +
                  ((4 * s.length + 1) + (s.length + 1)))))) ≤
        4 * L.length + 15 := by
      simp only [List.length_reverse]
      omega
    have hM_time : M.time.eval L'.length ≤
        (M.time.comp (Polynomial.C 2 * Polynomial.X + Polynomial.C 6)).eval L.length := by
      rw [Polynomial.eval_comp]
      have hlin : (Polynomial.C 2 * Polynomial.X + Polynomial.C 6).eval L.length =
          2 * L.length + 6 := by
        simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
      rw [hlin]
      exact poly_eval_mono M.time hL'_le
    have htime_eval :
        (Polynomial.C 4 * Polynomial.X + Polynomial.C 15 +
          M.time.comp (Polynomial.C 2 * Polynomial.X + Polynomial.C 6)).eval L.length =
        4 * L.length + 15 +
          (M.time.comp (Polynomial.C 2 * Polynomial.X + Polynomial.C 6)).eval L.length := by
      simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
    have hM : TM2OutputsInTime M.tm (List.map M.inputAlphabet.invFun L')
        (some (List.map M.outputAlphabet.invFun
          ((BitstringEncoding.toEncoding (α := Bool)).encode
            (f (List.replicate k true, min u v, max u v)))))
        (M.time.eval L'.length) := M.outputsFun (List.replicate k true, min u v, max u v)
    have hsim := simulateM M hM
    have hfull := evalsTrans hpre hsim
    change TM2OutputsInTime (wrapTM M) (List.map id L)
      (some (List.map M.outputAlphabet.invFun
        ((BitstringEncoding.toEncoding (α := Bool)).encode
          (f (List.replicate k true, min u v, max u v)))))
      ((Polynomial.C 4 * Polynomial.X + Polynomial.C 15 +
        M.time.comp (Polynomial.C 2 * Polynomial.X + Polynomial.C 6)).eval L.length)
    rw [List.map_id, htime_eval]
    unfold TM2OutputsInTime
    rw [initList_wrapTM]
    exact evalsMono hfull (by omega)

end Wrapper

private theorem main_H2 :
    OMA.R_Erdos78_erdos_78_variants_li_R1.H2 := by
  intro f hf
  rcases hf with ⟨M⟩
  exact ⟨fun p => f (List.replicate (Nat.log 2 p.1.length + 1) true, min p.2.1 p.2.2, max p.2.1 p.2.2),
    ⟨wrapComputable M⟩, fun _ _ _ => rfl⟩

end Erdos78LiH2Proof

theorem OMA.solution : OMA.R_Erdos78_erdos_78_variants_li_R1.H2 :=
  Erdos78LiH2Proof.main_H2
