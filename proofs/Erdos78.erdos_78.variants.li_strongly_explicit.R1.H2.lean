import OMAReductions.R_Erdos78_erdos_78_variants_li_strongly_explicit_R1
import Mathlib

/-!
# Proof of `Erdos78.erdos_78.variants.li_strongly_explicit.R1.H2`

Given any polynomial-time `FinTM2` computing `f : ℕ × ℕ × ℕ → Bool` under `BitstringEncoding`,
we construct a wrapper `FinTM2` computing `fun x => if x.2.1 < x.2.2 then f x else false` in
polynomial time.

Architecture:
1. `cmpLittleEndian` compares two little-endian `Computability.encodeNat` bitstrings from LSB to MSB
   using a 3-valued state `Cmp3 = {lt, eq, gt}`, proved equal to `decide (u < v)` via induction on
   `PosNum`.
2. Given `M : TM2ComputableInPolyTime bitEncode bitEncode f`, form a wrapper `FinTM2` with stack
   index type `Sum PreK M.tm.K`, label type `Sum PreΛ M.tm.Λ`, and internal state `Preσ × M.tm.σ`.
   Its input stack is `Sum.inl .inp` (`Bool`) and its output stack is `Sum.inr M.tm.k₁`.
3. In linear time (`≤ 5 * L.length + 10` steps), the preprocessing phase scans
   `L = delimit (encodeNat n) ++ delimit (encodeNat u) ++ encodeNat v`, saves `L.reverse` onto
   `bak`, extracts and reverses `encodeNat u` and `encodeNat v` onto `su` and `sv`, and runs
   `cmpLittleEndian`.
4. If `u < v` is false, the machine drains all auxiliary stacks, pushes `M.outputAlphabet.symm false`
   onto `Sum.inr M.tm.k₁`, resets the auxiliary state, and halts at `haltList`.
5. If `u < v` is true, the machine drains `sv`, transfers `bak` onto `Sum.inr M.tm.k₀` (restoring
   `List.map M.inputAlphabet.symm L`), resets the auxiliary state, and jumps to `Sum.inr M.tm.main`,
   where lifted statements of `M.tm` simulate `M.tm` step-for-step to `haltList`.
-/

namespace Erdos78LiStronglyExplicitH2Proof

open Computability Turing Turing.TM2 StateTransition ComplexityTheory BitstringEncoding

/- ### Section 1: Little-Endian Binary Comparison on `Computability.encodeNat` -/

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

private lemma posNum_one_le (m : PosNum) : 1 ≤ (m : ℕ) := by
  induction m with
  | one => exact le_rfl
  | bit0 k ih => simp [PosNum.cast_bit0]; omega
  | bit1 k ih => simp [PosNum.cast_bit1]

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
  | bak
  | suR
  | su
  | svR
  | sv
  deriving DecidableEq

private def preKEquiv : PreK ≃ Fin 6 where
  toFun
    | .inp => 0
    | .bak => 1
    | .suR => 2
    | .su => 3
    | .svR => 4
    | .sv => 5
  invFun
    | ⟨0, _⟩ => .inp
    | ⟨1, _⟩ => .bak
    | ⟨2, _⟩ => .suR
    | ⟨3, _⟩ => .su
    | ⟨4, _⟩ => .svR
    | ⟨5, _⟩ => .sv
  left_inv k := by cases k <;> rfl
  right_inv i := by fin_cases i <;> rfl

private instance : Fintype PreK := Fintype.ofEquiv (Fin 6) preKEquiv.symm

private inductive PreΛ : Type
  | skipN
  | readU
  | readV
  | revU
  | revV
  | cmpUV
  | clearSV_true
  | feedM
  | clearSU_false
  | clearBak_false
  deriving DecidableEq

private def preΛEquiv : PreΛ ≃ Fin 10 where
  toFun
    | .skipN => 0
    | .readU => 1
    | .readV => 2
    | .revU => 3
    | .revV => 4
    | .cmpUV => 5
    | .clearSV_true => 6
    | .feedM => 7
    | .clearSU_false => 8
    | .clearBak_false => 9
  invFun
    | ⟨0, _⟩ => .skipN
    | ⟨1, _⟩ => .readU
    | ⟨2, _⟩ => .readV
    | ⟨3, _⟩ => .revU
    | ⟨4, _⟩ => .revV
    | ⟨5, _⟩ => .cmpUV
    | ⟨6, _⟩ => .clearSV_true
    | ⟨7, _⟩ => .feedM
    | ⟨8, _⟩ => .clearSU_false
    | ⟨9, _⟩ => .clearBak_false
  left_inv l := by cases l <;> rfl
  right_inv i := by fin_cases i <;> rfl

private instance : Fintype PreΛ := Fintype.ofEquiv (Fin 10) preΛEquiv.symm

private abbrev Preσ : Type := Cmp3 × Option Bool × Option Bool

private def preσInit : Preσ := (.eq, none, none)

section Wrapper

variable {f : ℕ × ℕ × ℕ → Bool}
variable (M : TM2ComputableInPolyTime
  (BitstringEncoding.toEncoding (α := ℕ × ℕ × ℕ)).encode
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
  | .skipN =>
      .pop (Sum.inl .inp) (fun v o => ((v.1.1, o, none), v.2)) <|
      .branch (fun v => decide (v.1.2.1 = some true))
        (.push (Sum.inl .bak) (fun _ => true) <|
         .pop (Sum.inl .inp) (fun v o => ((v.1.1, o, none), v.2)) <|
         .push (Sum.inl .bak) (fun v => v.1.2.1.getD false) <|
         .goto (fun _ => Sum.inl .skipN))
        (.push (Sum.inl .bak) (fun _ => false) <|
         .goto (fun _ => Sum.inl .readU))
  | .readU =>
      .pop (Sum.inl .inp) (fun v o => ((v.1.1, o, none), v.2)) <|
      .branch (fun v => decide (v.1.2.1 = some true))
        (.push (Sum.inl .bak) (fun _ => true) <|
         .pop (Sum.inl .inp) (fun v o => ((v.1.1, o, none), v.2)) <|
         .push (Sum.inl .bak) (fun v => v.1.2.1.getD false) <|
         .push (Sum.inl .suR) (fun v => v.1.2.1.getD false) <|
         .goto (fun _ => Sum.inl .readU))
        (.push (Sum.inl .bak) (fun _ => false) <|
         .goto (fun _ => Sum.inl .readV))
  | .readV =>
      .pop (Sum.inl .inp) (fun v o => ((v.1.1, o, none), v.2)) <|
      .branch (fun v => v.1.2.1.isSome)
        (.push (Sum.inl .bak) (fun v => v.1.2.1.getD false) <|
         .push (Sum.inl .svR) (fun v => v.1.2.1.getD false) <|
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
          (.goto (fun _ => Sum.inl .clearSU_false)))
        (.branch (fun v => v.1.2.2.isSome)
          (.goto (fun _ => Sum.inl .clearSV_true))
          (.branch (fun v => decide (v.1.1 = .lt))
            (.goto (fun _ => Sum.inl .feedM))
            (.goto (fun _ => Sum.inl .clearBak_false))))
  | .clearSV_true =>
      .pop (Sum.inl .sv) (fun v o => ((v.1.1, o, none), v.2)) <|
      .branch (fun v => v.1.2.1.isSome)
        (.goto (fun _ => Sum.inl .clearSV_true))
        (.goto (fun _ => Sum.inl .feedM))
  | .feedM =>
      .pop (Sum.inl .bak) (fun v o => ((v.1.1, o, none), v.2)) <|
      .branch (fun v => v.1.2.1.isSome)
        (.push (Sum.inr M.tm.k₀) (fun v => M.inputAlphabet.symm (v.1.2.1.getD false)) <|
         .goto (fun _ => Sum.inl .feedM))
        (.load (fun v => (preσInit, v.2)) <|
         .goto (fun _ => Sum.inr M.tm.main))
  | .clearSU_false =>
      .pop (Sum.inl .su) (fun v o => ((v.1.1, o, none), v.2)) <|
      .branch (fun v => v.1.2.1.isSome)
        (.goto (fun _ => Sum.inl .clearSU_false))
        (.goto (fun _ => Sum.inl .clearBak_false))
  | .clearBak_false =>
      .pop (Sum.inl .bak) (fun v o => ((v.1.1, o, none), v.2)) <|
      .branch (fun v => v.1.2.1.isSome)
        (.goto (fun _ => Sum.inl .clearBak_false))
        (.push (Sum.inr M.tm.k₁) (fun _ => M.outputAlphabet.symm false) <|
         .load (fun v => (preσInit, v.2)) <|
         .halt)

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
  main := Sum.inl .skipN
  ΛFin := @instFintypeSum PreΛ M.tm.Λ _ M.tm.ΛFin
  σ := Wσ M
  initialState := (preσInit, M.tm.initialState)
  σFin := @instFintypeProd Preσ M.tm.σ _ M.tm.σFin
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := wrapProg M

/- ### Section 3: Helper Stack Builder and Step/Simulation Lemmas -/

private lemma cfg_ext {K : Type*} {Γ : K → Type*} {Λ σ : Type*}
    {c₁ c₂ : TM2.Cfg Γ Λ σ}
    (hl : c₁.l = c₂.l) (hvar : c₁.var = c₂.var) (hstk : c₁.stk = c₂.stk) : c₁ = c₂ := by
  cases c₁; cases c₂; cases hl; cases hvar; cases hstk; rfl

private def mkPreStk (inp bak suR su svR sv : List Bool) (rhs : ∀ k : M.tm.K, List (M.tm.Γ k)) :
    ∀ k : WK M, List (WΓ M k)
  | Sum.inl .inp => inp
  | Sum.inl .bak => bak
  | Sum.inl .suR => suR
  | Sum.inl .su => su
  | Sum.inl .svR => svR
  | Sum.inl .sv => sv
  | Sum.inr k => rhs k

private def emptyRhs : ∀ k : M.tm.K, List (M.tm.Γ k) := fun _ => []

private def mkInitRhs (s : List (M.tm.Γ M.tm.k₀)) : ∀ k : M.tm.K, List (M.tm.Γ k) :=
  fun k => @dite (List (M.tm.Γ k)) (k = M.tm.k₀) (M.tm.kDecidableEq k M.tm.k₀)
    (fun h => by rw [h]; exact s) (fun _ => [])

private lemma update_mkPreStk_inp (inp' inp bak suR su svR sv : List Bool) (rhs : ∀ k, List (M.tm.Γ k)) :
    Function.update (mkPreStk M inp bak suR su svR sv rhs) (Sum.inl .inp) inp' =
      mkPreStk M inp' bak suR su svR sv rhs := by
  funext k; cases k with
  | inl pk => cases pk <;> simp [Function.update, mkPreStk]
  | inr rk => simp [Function.update, mkPreStk]

private lemma update_mkPreStk_bak (bak' inp bak suR su svR sv : List Bool) (rhs : ∀ k, List (M.tm.Γ k)) :
    Function.update (mkPreStk M inp bak suR su svR sv rhs) (Sum.inl .bak) bak' =
      mkPreStk M inp bak' suR su svR sv rhs := by
  funext k; cases k with
  | inl pk => cases pk <;> simp [Function.update, mkPreStk]
  | inr rk => simp [Function.update, mkPreStk]

private lemma update_mkPreStk_suR (suR' inp bak suR su svR sv : List Bool) (rhs : ∀ k, List (M.tm.Γ k)) :
    Function.update (mkPreStk M inp bak suR su svR sv rhs) (Sum.inl .suR) suR' =
      mkPreStk M inp bak suR' su svR sv rhs := by
  funext k; cases k with
  | inl pk => cases pk <;> simp [Function.update, mkPreStk]
  | inr rk => simp [Function.update, mkPreStk]

private lemma update_mkPreStk_su (su' inp bak suR su svR sv : List Bool) (rhs : ∀ k, List (M.tm.Γ k)) :
    Function.update (mkPreStk M inp bak suR su svR sv rhs) (Sum.inl .su) su' =
      mkPreStk M inp bak suR su' svR sv rhs := by
  funext k; cases k with
  | inl pk => cases pk <;> simp [Function.update, mkPreStk]
  | inr rk => simp [Function.update, mkPreStk]

private lemma update_mkPreStk_svR (svR' inp bak suR su svR sv : List Bool) (rhs : ∀ k, List (M.tm.Γ k)) :
    Function.update (mkPreStk M inp bak suR su svR sv rhs) (Sum.inl .svR) svR' =
      mkPreStk M inp bak suR su svR' sv rhs := by
  funext k; cases k with
  | inl pk => cases pk <;> simp [Function.update, mkPreStk]
  | inr rk => simp [Function.update, mkPreStk]

private lemma update_mkPreStk_sv (sv' inp bak suR su svR sv : List Bool) (rhs : ∀ k, List (M.tm.Γ k)) :
    Function.update (mkPreStk M inp bak suR su svR sv rhs) (Sum.inl .sv) sv' =
      mkPreStk M inp bak suR su svR sv' rhs := by
  funext k; cases k with
  | inl pk => cases pk <;> simp [Function.update, mkPreStk]
  | inr rk => simp [Function.update, mkPreStk]

private lemma update_mkPreStk_inr (k₀ : M.tm.K) (v : List (M.tm.Γ k₀))
    (inp bak suR su svR sv : List Bool) (rhs : ∀ k, List (M.tm.Γ k)) :
    Function.update (mkPreStk M inp bak suR su svR sv rhs) (Sum.inr k₀) v =
      mkPreStk M inp bak suR su svR sv (Function.update rhs k₀ v) := by
  funext k; cases k with
  | inl pk => cases pk <;> simp [Function.update, mkPreStk]
  | inr rk =>
    by_cases h : rk = k₀
    · subst h; simp [Function.update, mkPreStk]
    · simp [Function.update, mkPreStk, h]

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
  stk := mkPreStk M [] [] [] [] [] [] c.stk

private lemma stepAux_liftStmt (q : TM2.Stmt M.tm.Γ M.tm.Λ M.tm.σ)
    (v : M.tm.σ) (S : ∀ k : M.tm.K, List (M.tm.Γ k)) :
    TM2.stepAux (liftStmt M q) (preσInit, v) (mkPreStk M [] [] [] [] [] [] S) =
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
        mkPreStk M [] [] [] [] [] [] (mkInitRhs M s)⟩ := by
  rfl

private lemma liftCfg_haltList (s : List (M.tm.Γ M.tm.k₁)) :
    liftCfg M (haltList M.tm s) = haltList (wrapTM M) s := by
  apply cfg_ext
  · rfl
  · rfl
  · funext k
    cases k with
    | inl pk => cases pk <;> simp [liftCfg, haltList, mkPreStk]
    | inr rk =>
      simp only [liftCfg, haltList, mkPreStk]
      by_cases hrk : rk = M.tm.k₁
      · subst hrk; simp
      · simp [hrk]

private def simulateM {s : List (M.tm.Γ M.tm.k₀)} {out : List (M.tm.Γ M.tm.k₁)} {m : ℕ}
    (h : TM2OutputsInTime M.tm s (some out) m) :
    EvalsToInTime (wrapTM M).step
      ⟨some (Sum.inr M.tm.main), (preσInit, M.tm.initialState),
        mkPreStk M [] [] [] [] [] [] (mkInitRhs M s)⟩
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

private def runSkipN (a rest bak : List Bool) (p : Preσ) :
    EvalsToInTime (wrapTM M).step
      ⟨some (Sum.inl .skipN), (p, M.tm.initialState),
        mkPreStk M (delimit a ++ rest) bak [] [] [] [] (emptyRhs M)⟩
      (some ⟨some (Sum.inl .readU), ((p.1, some false, none), M.tm.initialState),
        mkPreStk M rest ((delimit a).reverse ++ bak) [] [] [] [] (emptyRhs M)⟩)
      (a.length + 1) := by
  induction a generalizing bak p with
  | nil =>
    refine evalsStep (wrapTM M).step ?_
    simp [FinTM2.step, wrapProg, preProg, delimit, TM2.step, TM2.stepAux, mkPreStk,
      update_mkPreStk_inp, update_mkPreStk_bak]; rfl
  | cons b a ih =>
    have h1 : (wrapTM M).step
        ⟨some (Sum.inl .skipN), (p, M.tm.initialState),
          mkPreStk M (delimit (b :: a) ++ rest) bak [] [] [] [] (emptyRhs M)⟩ =
        some ⟨some (Sum.inl .skipN), ((p.1, some b, none), M.tm.initialState),
          mkPreStk M (delimit a ++ rest) (b :: true :: bak) [] [] [] [] (emptyRhs M)⟩ := by
      simp [FinTM2.step, wrapProg, preProg, delimit, TM2.step, TM2.stepAux, mkPreStk,
        update_mkPreStk_inp, update_mkPreStk_bak]; rfl
    have h2 := ih (b :: true :: bak) (p.1, some b, none)
    have hcat : (delimit a).reverse ++ (b :: true :: bak) = (delimit (b :: a)).reverse ++ bak := by
      simp [delimit, List.append_assoc]
    rw [hcat] at h2
    exact evalsMono (evalsTrans (evalsStep _ h1) h2) (by simp)

private def runReadU (a rest bak suR : List Bool) (p : Preσ) :
    EvalsToInTime (wrapTM M).step
      ⟨some (Sum.inl .readU), (p, M.tm.initialState),
        mkPreStk M (delimit a ++ rest) bak suR [] [] [] (emptyRhs M)⟩
      (some ⟨some (Sum.inl .readV), ((p.1, some false, none), M.tm.initialState),
        mkPreStk M rest ((delimit a).reverse ++ bak) (a.reverse ++ suR) [] [] [] (emptyRhs M)⟩)
      (a.length + 1) := by
  induction a generalizing bak suR p with
  | nil =>
    refine evalsStep (wrapTM M).step ?_
    simp [FinTM2.step, wrapProg, preProg, delimit, TM2.step, TM2.stepAux, mkPreStk,
      update_mkPreStk_inp, update_mkPreStk_bak]; rfl
  | cons b a ih =>
    have h1 : (wrapTM M).step
        ⟨some (Sum.inl .readU), (p, M.tm.initialState),
          mkPreStk M (delimit (b :: a) ++ rest) bak suR [] [] [] (emptyRhs M)⟩ =
        some ⟨some (Sum.inl .readU), ((p.1, some b, none), M.tm.initialState),
          mkPreStk M (delimit a ++ rest) (b :: true :: bak) (b :: suR) [] [] [] (emptyRhs M)⟩ := by
      simp [FinTM2.step, wrapProg, preProg, delimit, TM2.step, TM2.stepAux, mkPreStk,
        update_mkPreStk_inp, update_mkPreStk_bak, update_mkPreStk_suR]; rfl
    have h2 := ih (b :: true :: bak) (b :: suR) (p.1, some b, none)
    have hcat1 : (delimit a).reverse ++ (b :: true :: bak) = (delimit (b :: a)).reverse ++ bak := by
      simp [delimit, List.append_assoc]
    have hcat2 : a.reverse ++ (b :: suR) = (b :: a).reverse ++ suR := by
      simp [List.append_assoc]
    rw [hcat1, hcat2] at h2
    exact evalsMono (evalsTrans (evalsStep _ h1) h2) (by simp)

private def runReadV (v bak suR svR : List Bool) (p : Preσ) :
    EvalsToInTime (wrapTM M).step
      ⟨some (Sum.inl .readV), (p, M.tm.initialState),
        mkPreStk M v bak suR [] svR [] (emptyRhs M)⟩
      (some ⟨some (Sum.inl .revU), ((p.1, none, none), M.tm.initialState),
        mkPreStk M [] (v.reverse ++ bak) suR [] (v.reverse ++ svR) [] (emptyRhs M)⟩)
      (v.length + 1) := by
  induction v generalizing bak svR p with
  | nil =>
    refine evalsStep (wrapTM M).step ?_
    simp [FinTM2.step, wrapProg, preProg, TM2.step, TM2.stepAux, mkPreStk,
      update_mkPreStk_inp]; rfl
  | cons b v ih =>
    have h1 : (wrapTM M).step
        ⟨some (Sum.inl .readV), (p, M.tm.initialState),
          mkPreStk M (b :: v) bak suR [] svR [] (emptyRhs M)⟩ =
        some ⟨some (Sum.inl .readV), ((p.1, some b, none), M.tm.initialState),
          mkPreStk M v (b :: bak) suR [] (b :: svR) [] (emptyRhs M)⟩ := by
      simp [FinTM2.step, wrapProg, preProg, TM2.step, TM2.stepAux, mkPreStk,
        update_mkPreStk_inp, update_mkPreStk_bak, update_mkPreStk_svR]; rfl
    have h2 := ih (b :: bak) (b :: svR) (p.1, some b, none)
    have hcat1 : v.reverse ++ (b :: bak) = (b :: v).reverse ++ bak := by simp [List.append_assoc]
    have hcat2 : v.reverse ++ (b :: svR) = (b :: v).reverse ++ svR := by simp [List.append_assoc]
    rw [hcat1, hcat2] at h2
    exact evalsMono (evalsTrans (evalsStep _ h1) h2) (by simp)

private def runRevU (suR su bak svR : List Bool) (p : Preσ) :
    EvalsToInTime (wrapTM M).step
      ⟨some (Sum.inl .revU), (p, M.tm.initialState),
        mkPreStk M [] bak suR su svR [] (emptyRhs M)⟩
      (some ⟨some (Sum.inl .revV), ((p.1, none, none), M.tm.initialState),
        mkPreStk M [] bak [] (suR.reverse ++ su) svR [] (emptyRhs M)⟩)
      (suR.length + 1) := by
  induction suR generalizing su p with
  | nil =>
    refine evalsStep (wrapTM M).step ?_
    simp [FinTM2.step, wrapProg, preProg, TM2.step, TM2.stepAux, mkPreStk,
      update_mkPreStk_suR]; rfl
  | cons b s ih =>
    have h1 : (wrapTM M).step
        ⟨some (Sum.inl .revU), (p, M.tm.initialState),
          mkPreStk M [] bak (b :: s) su svR [] (emptyRhs M)⟩ =
        some ⟨some (Sum.inl .revU), ((p.1, some b, none), M.tm.initialState),
          mkPreStk M [] bak s (b :: su) svR [] (emptyRhs M)⟩ := by
      simp [FinTM2.step, wrapProg, preProg, TM2.step, TM2.stepAux, mkPreStk,
        update_mkPreStk_suR, update_mkPreStk_su]; rfl
    have h2 := ih (b :: su) (p.1, some b, none)
    have hcat : s.reverse ++ (b :: su) = (b :: s).reverse ++ su := by simp [List.append_assoc]
    rw [hcat] at h2
    exact evalsMono (evalsTrans (evalsStep _ h1) h2) (by simp)

private def runRevV (svR sv bak su : List Bool) (p : Preσ) :
    EvalsToInTime (wrapTM M).step
      ⟨some (Sum.inl .revV), (p, M.tm.initialState),
        mkPreStk M [] bak [] su svR sv (emptyRhs M)⟩
      (some ⟨some (Sum.inl .cmpUV), ((.eq, none, none), M.tm.initialState),
        mkPreStk M [] bak [] su [] (svR.reverse ++ sv) (emptyRhs M)⟩)
      (svR.length + 1) := by
  induction svR generalizing sv p with
  | nil =>
    refine evalsStep (wrapTM M).step ?_
    simp [FinTM2.step, wrapProg, preProg, TM2.step, TM2.stepAux, mkPreStk,
      update_mkPreStk_svR]; rfl
  | cons b s ih =>
    have h1 : (wrapTM M).step
        ⟨some (Sum.inl .revV), (p, M.tm.initialState),
          mkPreStk M [] bak [] su (b :: s) sv (emptyRhs M)⟩ =
        some ⟨some (Sum.inl .revV), ((p.1, some b, none), M.tm.initialState),
          mkPreStk M [] bak [] su s (b :: sv) (emptyRhs M)⟩ := by
      simp [FinTM2.step, wrapProg, preProg, TM2.step, TM2.stepAux, mkPreStk,
        update_mkPreStk_svR, update_mkPreStk_sv]; rfl
    have h2 := ih (b :: sv) (p.1, some b, none)
    have hcat : s.reverse ++ (b :: sv) = (b :: s).reverse ++ sv := by simp [List.append_assoc]
    rw [hcat] at h2
    exact evalsMono (evalsTrans (evalsStep _ h1) h2) (by simp)

private def runClearSVTrue (sv bak : List Bool) (p : Preσ) :
    EvalsToInTime (wrapTM M).step
      ⟨some (Sum.inl .clearSV_true), (p, M.tm.initialState),
        mkPreStk M [] bak [] [] [] sv (emptyRhs M)⟩
      (some ⟨some (Sum.inl .feedM), ((p.1, none, none), M.tm.initialState),
        mkPreStk M [] bak [] [] [] [] (emptyRhs M)⟩)
      (sv.length + 1) := by
  induction sv generalizing p with
  | nil =>
    refine evalsStep (wrapTM M).step ?_
    simp [FinTM2.step, wrapProg, preProg, TM2.step, TM2.stepAux, mkPreStk,
      update_mkPreStk_sv]; rfl
  | cons b s ih =>
    have h1 : (wrapTM M).step
        ⟨some (Sum.inl .clearSV_true), (p, M.tm.initialState),
          mkPreStk M [] bak [] [] [] (b :: s) (emptyRhs M)⟩ =
        some ⟨some (Sum.inl .clearSV_true), ((p.1, some b, none), M.tm.initialState),
          mkPreStk M [] bak [] [] [] s (emptyRhs M)⟩ := by
      simp [FinTM2.step, wrapProg, preProg, TM2.step, TM2.stepAux, mkPreStk,
        update_mkPreStk_sv]; rfl
    exact evalsMono (evalsTrans (evalsStep _ h1) (ih (p.1, some b, none))) (by simp)

private def runClearSUFalse (su bak : List Bool) (p : Preσ) :
    EvalsToInTime (wrapTM M).step
      ⟨some (Sum.inl .clearSU_false), (p, M.tm.initialState),
        mkPreStk M [] bak [] su [] [] (emptyRhs M)⟩
      (some ⟨some (Sum.inl .clearBak_false), ((p.1, none, none), M.tm.initialState),
        mkPreStk M [] bak [] [] [] [] (emptyRhs M)⟩)
      (su.length + 1) := by
  induction su generalizing p with
  | nil =>
    refine evalsStep (wrapTM M).step ?_
    simp [FinTM2.step, wrapProg, preProg, TM2.step, TM2.stepAux, mkPreStk,
      update_mkPreStk_su]; rfl
  | cons b s ih =>
    have h1 : (wrapTM M).step
        ⟨some (Sum.inl .clearSU_false), (p, M.tm.initialState),
          mkPreStk M [] bak [] (b :: s) [] [] (emptyRhs M)⟩ =
        some ⟨some (Sum.inl .clearSU_false), ((p.1, some b, none), M.tm.initialState),
          mkPreStk M [] bak [] s [] [] (emptyRhs M)⟩ := by
      simp [FinTM2.step, wrapProg, preProg, TM2.step, TM2.stepAux, mkPreStk,
        update_mkPreStk_su]; rfl
    exact evalsMono (evalsTrans (evalsStep _ h1) (ih (p.1, some b, none))) (by simp)

private def runClearBakFalse (bak : List Bool) (p : Preσ) :
    EvalsToInTime (wrapTM M).step
      ⟨some (Sum.inl .clearBak_false), (p, M.tm.initialState),
        mkPreStk M [] bak [] [] [] [] (emptyRhs M)⟩
      (some (haltList (wrapTM M) [M.outputAlphabet.symm false]))
      (bak.length + 1) := by
  induction bak generalizing p with
  | nil =>
    refine evalsStep (wrapTM M).step ?_
    simp only [FinTM2.step, wrapProg, preProg, TM2.step, TM2.stepAux, mkPreStk,
      update_mkPreStk_bak]
    rw [update_mkPreStk_inr]
    congr 1
    apply cfg_ext
    · rfl
    · rfl
    · funext k
      cases k with
      | inl pk => cases pk <;> simp [haltList, mkPreStk]
      | inr rk =>
        by_cases hrk : rk = M.tm.k₁
        · subst hrk; simp [haltList, mkPreStk, emptyRhs, Function.update]
        · simp [haltList, mkPreStk, emptyRhs, Function.update, hrk]
  | cons b s ih =>
    have h1 : (wrapTM M).step
        ⟨some (Sum.inl .clearBak_false), (p, M.tm.initialState),
          mkPreStk M [] (b :: s) [] [] [] [] (emptyRhs M)⟩ =
        some ⟨some (Sum.inl .clearBak_false), ((p.1, some b, none), M.tm.initialState),
          mkPreStk M [] s [] [] [] [] (emptyRhs M)⟩ := by
      simp [FinTM2.step, wrapProg, preProg, TM2.step, TM2.stepAux, mkPreStk,
        update_mkPreStk_bak]; rfl
    exact evalsMono (evalsTrans (evalsStep _ h1) (ih (p.1, some b, none))) (by simp)

private lemma update_mkInitRhs (a : M.tm.Γ M.tm.k₀) (acc : List (M.tm.Γ M.tm.k₀)) :
    Function.update (mkInitRhs M acc) M.tm.k₀ (a :: acc) = mkInitRhs M (a :: acc) := by
  funext k
  by_cases h : k = M.tm.k₀
  · subst h; simp [Function.update, mkInitRhs]
  · simp [Function.update, mkInitRhs, h]

private def runFeedM (bak : List Bool) (acc : List (M.tm.Γ M.tm.k₀)) (p : Preσ) :
    EvalsToInTime (wrapTM M).step
      ⟨some (Sum.inl .feedM), (p, M.tm.initialState),
        mkPreStk M [] bak [] [] [] [] (mkInitRhs M acc)⟩
      (some ⟨some (Sum.inr M.tm.main), (preσInit, M.tm.initialState),
        mkPreStk M [] [] [] [] [] [] (mkInitRhs M (List.map M.inputAlphabet.symm bak.reverse ++ acc))⟩)
      (bak.length + 1) := by
  induction bak generalizing acc p with
  | nil =>
    refine evalsStep (wrapTM M).step ?_
    simp [FinTM2.step, wrapProg, preProg, TM2.step, TM2.stepAux, mkPreStk,
      update_mkPreStk_bak]; rfl
  | cons b s ih =>
    have h1 : (wrapTM M).step
        ⟨some (Sum.inl .feedM), (p, M.tm.initialState),
          mkPreStk M [] (b :: s) [] [] [] [] (mkInitRhs M acc)⟩ =
        some ⟨some (Sum.inl .feedM), ((p.1, some b, none), M.tm.initialState),
          mkPreStk M [] s [] [] [] [] (mkInitRhs M (M.inputAlphabet.symm b :: acc))⟩ := by
      simp only [FinTM2.step, wrapProg, preProg, TM2.step, TM2.stepAux, mkPreStk,
        update_mkPreStk_bak, List.head?_cons, List.tail_cons, Option.isSome_some, Bool.cond_true,
        Option.getD_some]
      rw [update_mkPreStk_inr]
      have hmk : mkInitRhs M acc M.tm.k₀ = acc := by simp [mkInitRhs]
      rw [hmk, update_mkInitRhs]; rfl
    have h2 := ih (M.inputAlphabet.symm b :: acc) (p.1, some b, none)
    have hcat : List.map M.inputAlphabet.symm s.reverse ++ (M.inputAlphabet.symm b :: acc) =
        List.map M.inputAlphabet.symm (b :: s).reverse ++ acc := by
      simp [List.append_assoc]
    rw [hcat] at h2
    exact evalsMono (evalsTrans (evalsStep _ h1) h2) (by simp)

private lemma emptyRhs_eq_mkInitRhs_nil : emptyRhs M = mkInitRhs M [] := by
  funext k
  by_cases h : k = M.tm.k₀
  · subst h; simp [emptyRhs, mkInitRhs]
  · simp [emptyRhs, mkInitRhs, h]

private def runCmpAndFinish (su : List Bool) :
    ∀ (sv bak : List Bool) (c : Cmp3) (ob₁ ob₂ : Option Bool),
      EvalsToInTime (wrapTM M).step
        ⟨some (Sum.inl .cmpUV), ((c, ob₁, ob₂), M.tm.initialState),
          mkPreStk M [] bak [] su [] sv (emptyRhs M)⟩
        (if cmpLittleEndian su sv c then
          some ⟨some (Sum.inr M.tm.main), (preσInit, M.tm.initialState),
            mkPreStk M [] [] [] [] [] []
              (mkInitRhs M (List.map M.inputAlphabet.symm bak.reverse))⟩
        else
          some (haltList (wrapTM M) [M.outputAlphabet.symm false]))
        (su.length + sv.length + bak.length + 4) := by
  induction su with
  | nil =>
    intro sv bak c ob₁ ob₂
    cases sv with
    | nil =>
      by_cases hc : c = .lt
      · subst hc
        have hstep : (wrapTM M).step
            ⟨some (Sum.inl .cmpUV), ((.lt, ob₁, ob₂), M.tm.initialState),
              mkPreStk M [] bak [] [] [] [] (emptyRhs M)⟩ =
            some ⟨some (Sum.inl .feedM), ((.lt, none, none), M.tm.initialState),
              mkPreStk M [] bak [] [] [] [] (mkInitRhs M [])⟩ := by
          rw [← emptyRhs_eq_mkInitRhs_nil]
          simp [FinTM2.step, wrapProg, preProg, TM2.step, TM2.stepAux, mkPreStk,
            update_mkPreStk_su, update_mkPreStk_sv]; rfl
        have h2 := runFeedM M bak [] (.lt, none, none)
        rw [List.append_nil] at h2
        have htr := evalsTrans (evalsStep _ hstep) h2
        have hcmp : cmpLittleEndian [] [] .lt = true := rfl
        rw [hcmp, if_pos rfl]
        exact evalsMono htr (by omega)
      · have hstep : (wrapTM M).step
            ⟨some (Sum.inl .cmpUV), ((c, ob₁, ob₂), M.tm.initialState),
              mkPreStk M [] bak [] [] [] [] (emptyRhs M)⟩ =
            some ⟨some (Sum.inl .clearBak_false), ((c, none, none), M.tm.initialState),
              mkPreStk M [] bak [] [] [] [] (emptyRhs M)⟩ := by
          simp [FinTM2.step, wrapProg, preProg, TM2.step, TM2.stepAux, mkPreStk,
            update_mkPreStk_su, update_mkPreStk_sv, hc]; rfl
        have h2 := runClearBakFalse M bak (c, none, none)
        have htr := evalsTrans (evalsStep _ hstep) h2
        have hcmp : cmpLittleEndian [] [] c = false := by simp [cmpLittleEndian, hc]
        rw [hcmp, if_neg Bool.false_ne_true]
        exact evalsMono htr (by omega)
    | cons b s =>
      have hstep : (wrapTM M).step
          ⟨some (Sum.inl .cmpUV), ((c, ob₁, ob₂), M.tm.initialState),
            mkPreStk M [] bak [] [] [] (b :: s) (emptyRhs M)⟩ =
          some ⟨some (Sum.inl .clearSV_true), ((c, none, some b), M.tm.initialState),
            mkPreStk M [] bak [] [] [] s (emptyRhs M)⟩ := by
        simp [FinTM2.step, wrapProg, preProg, TM2.step, TM2.stepAux, mkPreStk,
          update_mkPreStk_su, update_mkPreStk_sv]; rfl
      have h2 := runClearSVTrue M s bak (c, none, some b)
      have h3 := runFeedM M bak [] (c, none, none)
      rw [← emptyRhs_eq_mkInitRhs_nil, List.append_nil] at h3
      have h12 := evalsTrans (evalsStep _ hstep) h2
      have h123 := evalsTrans h12 h3
      have hcmp : cmpLittleEndian [] (b :: s) c = true := rfl
      rw [hcmp, if_pos rfl]
      exact evalsMono h123 (by simp; omega)
  | cons a sa ih =>
    intro sv bak c ob₁ ob₂
    cases sv with
    | nil =>
      have hstep : (wrapTM M).step
          ⟨some (Sum.inl .cmpUV), ((c, ob₁, ob₂), M.tm.initialState),
            mkPreStk M [] bak [] (a :: sa) [] [] (emptyRhs M)⟩ =
          some ⟨some (Sum.inl .clearSU_false), ((c, some a, none), M.tm.initialState),
            mkPreStk M [] bak [] sa [] [] (emptyRhs M)⟩ := by
        simp [FinTM2.step, wrapProg, preProg, TM2.step, TM2.stepAux, mkPreStk,
          update_mkPreStk_su, update_mkPreStk_sv]; rfl
      have h2 := runClearSUFalse M sa bak (c, some a, none)
      have h3 := runClearBakFalse M bak (c, none, none)
      have h12 := evalsTrans (evalsStep _ hstep) h2
      have h123 := evalsTrans h12 h3
      have hcmp : cmpLittleEndian (a :: sa) [] c = false := rfl
      rw [hcmp, if_neg Bool.false_ne_true]
      exact evalsMono h123 (by simp; omega)
    | cons b sb =>
      let c' := updateCmp c a b
      have hstep : (wrapTM M).step
          ⟨some (Sum.inl .cmpUV), ((c, ob₁, ob₂), M.tm.initialState),
            mkPreStk M [] bak [] (a :: sa) [] (b :: sb) (emptyRhs M)⟩ =
          some ⟨some (Sum.inl .cmpUV), ((c', none, none), M.tm.initialState),
            mkPreStk M [] bak [] sa [] sb (emptyRhs M)⟩ := by
        simp [FinTM2.step, wrapProg, preProg, TM2.step, TM2.stepAux, mkPreStk,
          update_mkPreStk_su, update_mkPreStk_sv, c']; rfl
      have hrec := ih sb bak c' none none
      have htr := evalsTrans (evalsStep _ hstep) hrec
      have hcmp : cmpLittleEndian (a :: sa) (b :: sb) c = cmpLittleEndian sa sb c' := rfl
      rw [hcmp]
      exact evalsMono htr (by simp; omega)

private lemma initList_wrapTM (L : List Bool) :
    initList (wrapTM M) L =
      ⟨some (Sum.inl .skipN), (preσInit, M.tm.initialState),
        mkPreStk M L [] [] [] [] [] (emptyRhs M)⟩ := by
  apply cfg_ext
  · rfl
  · rfl
  · funext k
    cases k with
    | inl pk => cases pk <;> simp [initList, mkPreStk]
    | inr rk => simp [initList, mkPreStk, emptyRhs]

private noncomputable def wrapComputable :
    TM2ComputableInPolyTime
      (BitstringEncoding.toEncoding (α := ℕ × ℕ × ℕ)).encode
      (BitstringEncoding.toEncoding (α := Bool)).encode
      (fun x : ℕ × ℕ × ℕ => if x.2.1 < x.2.2 then f x else false) where
  tm := wrapTM M
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := M.outputAlphabet
  time := Polynomial.C 5 * Polynomial.X + Polynomial.C 12 + M.time
  outputsFun x := by
    rcases x with ⟨n, u, v⟩
    let en : List Bool := Computability.encodeNat n
    let eu : List Bool := Computability.encodeNat u
    let ev : List Bool := Computability.encodeNat v
    let L : List Bool := delimit en ++ (delimit eu ++ ev)
    have hL_eq : (BitstringEncoding.toEncoding (α := ℕ × ℕ × ℕ)).encode (n, u, v) = L := rfl
    have hL_len : L.length = (2 * en.length + 1) + (2 * eu.length + 1) + ev.length := by
      simp [L, length_delimit]; omega
    have h1 := runSkipN M en (delimit eu ++ ev) [] preσInit
    rw [List.append_nil] at h1
    have h2 := runReadU M eu ev (delimit en).reverse [] (preσInit.1, some false, none)
    rw [List.append_nil] at h2
    have h3 := runReadV M ev ((delimit eu).reverse ++ (delimit en).reverse) eu.reverse []
      (preσInit.1, some false, none)
    rw [List.append_nil] at h3
    have hbak_eq : ev.reverse ++ ((delimit eu).reverse ++ (delimit en).reverse) = L.reverse := by
      simp [L, List.reverse_append, List.append_assoc]
    rw [hbak_eq] at h3
    have h4 := runRevU M eu.reverse [] L.reverse ev.reverse (preσInit.1, none, none)
    rw [List.reverse_reverse, List.append_nil] at h4
    have h5 := runRevV M ev.reverse [] L.reverse eu (preσInit.1, none, none)
    rw [List.reverse_reverse, List.append_nil] at h5
    have h6 := runCmpAndFinish M eu ev L.reverse .eq none none
    rw [List.reverse_reverse] at h6
    have h12 := evalsTrans h1 h2
    have h123 := evalsTrans h12 h3
    have h1234 := evalsTrans h123 h4
    have h12345 := evalsTrans h1234 h5
    have hpre := evalsTrans h12345 h6
    have hpre_bound :
        (eu.length + ev.length + L.reverse.length + 4) +
          ((ev.reverse.length + 1) +
            ((eu.reverse.length + 1) +
              ((ev.length + 1) + ((eu.length + 1) + (en.length + 1))))) ≤
        5 * L.length + 12 := by
      simp only [List.length_reverse]
      omega
    have hcmp_eq : cmpLittleEndian eu ev .eq = decide (u < v) := cmpLittleEndian_encodeNat u v
    have htime_eval :
        (Polynomial.C 5 * Polynomial.X + Polynomial.C 12 + M.time).eval L.length =
          5 * L.length + 12 + M.time.eval L.length := by
      simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
    change TM2OutputsInTime (wrapTM M) (List.map id L)
      (some (List.map M.outputAlphabet.invFun
        ((BitstringEncoding.toEncoding (α := Bool)).encode (if u < v then f (n, u, v) else false))))
      ((Polynomial.C 5 * Polynomial.X + Polynomial.C 12 + M.time).eval L.length)
    rw [List.map_id, htime_eval]
    unfold TM2OutputsInTime
    rw [initList_wrapTM]
    by_cases huv : u < v
    · have hdec : cmpLittleEndian eu ev .eq = true := by rw [hcmp_eq, decide_eq_true huv]
      rw [if_pos hdec] at hpre
      have hM : TM2OutputsInTime M.tm (List.map M.inputAlphabet.invFun L)
          (some (List.map M.outputAlphabet.invFun
            ((BitstringEncoding.toEncoding (α := Bool)).encode (f (n, u, v)))))
          (M.time.eval L.length) := M.outputsFun (n, u, v)
      have hsim := simulateM M hM
      have hfull := evalsTrans hpre hsim
      rw [if_pos huv]
      exact evalsMono hfull (by omega)
    · have hdec : cmpLittleEndian eu ev .eq = false := by rw [hcmp_eq, decide_eq_false huv]
      rw [if_neg (by rw [hdec]; decide)] at hpre
      have hout : List.map M.outputAlphabet.invFun
          ((BitstringEncoding.toEncoding (α := Bool)).encode false) =
          [M.outputAlphabet.symm false] := rfl
      rw [if_neg huv, hout]
      exact evalsMono hpre (by omega)

end Wrapper

private theorem main_H2 :
    OMA.R_Erdos78_erdos_78_variants_li_strongly_explicit_R1.H2 := by
  intro f hf
  rcases hf with ⟨M⟩
  exact ⟨wrapComputable M⟩

end Erdos78LiStronglyExplicitH2Proof

theorem OMA.solution : OMA.R_Erdos78_erdos_78_variants_li_strongly_explicit_R1.H2 :=
  Erdos78LiStronglyExplicitH2Proof.main_H2
