import OMAReductions.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H1_R1
import Mathlib.Tactic

/-!
# Binomial columns 14, 15, 16, 17 for the exponents `3240*q + 2801` (OEIS A249609)

For `a = 3240*q + 2801`, the columns 14, 15, 16, 17 give an evil binomial coefficient
`C(2^a, k)` on all but 13 residue classes of `q` modulo 210. As in ZedingZhang's sibling
reduction for the class 2705, PanPapag's periodicity theorem from the parent reduction reduces each
column to one representative exponent per residue class of `a` modulo twice the order of 2 modulo
the odd part of `k!`, and the parity at each representative is certified by folding with bitwise xor.
Column 17 has period 680400 = 3240 * 210, so the case split runs over `q` modulo 210.
The 13 remaining classes are the hypotheses.
-/

namespace OMA.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H1_R1_H4_R1

open OMA.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H1_R1

def H1 : Prop :=
  ∀ q : ℕ, q % 210 ∈ ([4, 17, 31, 64, 66] : List ℕ) →
    ∃ k ∈ List.range' 1 (2 ^ (3240*q+2801)),
      OeisA249609.isEvil ((2 ^ (3240*q+2801)).choose k) = true

def H2 : Prop :=
  ∀ q : ℕ, q % 210 ∈ ([99, 129, 130, 134] : List ℕ) →
    ∃ k ∈ List.range' 1 (2 ^ (3240*q+2801)),
      OeisA249609.isEvil ((2 ^ (3240*q+2801)).choose k) = true

def H3 : Prop :=
  ∀ q : ℕ, q % 210 ∈ ([141, 157, 200, 206] : List ℕ) →
    ∃ k ∈ List.range' 1 (2 ^ (3240*q+2801)),
      OeisA249609.isEvil ((2 ^ (3240*q+2801)).choose k) = true

section Certificates

private theorem weight_half (n : ℕ) :
    (Nat.digits 2 n).count 1 = (Nat.digits 2 (n/2)).count 1 + n%2 := by
  have hh := count_ones_append (n/2) 1 (n%2) (by simpa using Nat.mod_lt n (by decide : 0 < 2))
  rw [pow_one, Nat.div_add_mod'] at hh
  change (Nat.digits 2 n).count 1 = (Nat.digits 2 (n / 2)).count 1 + (Nat.digits 2 (n % 2)).count 1 at hh
  rw [hh]
  have h : n%2 = 0 ∨ n%2 = 1 := by omega
  rcases h with h | h <;> rw [h] <;> rfl

private theorem xor_weight (a b : ℕ) : (Nat.digits 2 (a ^^^ b)).count 1 % 2 = ((Nat.digits 2 a).count 1 + (Nat.digits 2 b).count 1) % 2 := by
  induction h : a+b using Nat.strong_induction_on generalizing a b with
  | h n ih =>
    by_cases hzero : n = 0
    · have ha : a = 0 := by omega
      have hb : b = 0 := by omega
      subst a; subst b; rfl
    have half := ih (a/2+b/2) (by omega) (a/2) (b/2) rfl
    have ha := weight_half a
    have hb := weight_half b
    have hab := weight_half (a ^^^ b)
    rw [Nat.xor_div_two] at hab
    have hmod := Nat.xor_mod_two_eq (m := a) (n := b)
    omega

/-- Folding the two halves with xor preserves the parity and halves the bit width. -/
private theorem fold_certificate (i n : ℕ) (h :
    (Nat.rec (motive := fun _ => ℕ → ℕ) (fun v => (Nat.digits 2 v).count 1 % 2)
      (fun j f v => let base := 2^(8 * 2^j); f ((v / base) ^^^ (v % base))) i n) = 0) :
    (Nat.digits 2 n).count 1 % 2 = 0 := by
  let count := Nat.rec (motive := fun _ => ℕ → ℕ) (fun v => (Nat.digits 2 v).count 1 % 2)
      (fun j f v => let base := 2^(8 * 2^j); f ((v / base) ^^^ (v % base)))
  have spec (j v : ℕ) : count j v = (Nat.digits 2 v).count 1 % 2 := by
    induction j generalizing v with
    | zero => rfl
    | succ j ih =>
      let w := 8*2^j
      change count j ((v / 2^w) ^^^ (v % 2^w)) = _
      rw [ih,xor_weight]
      have hh := count_ones_append (v / 2^w) w (v%2^w) (Nat.mod_lt _ (by positivity))
      rw [Nat.div_add_mod'] at hh
      exact congrArg (· % 2) hh.symm
  exact (spec i n).symm.trans h


set_option maxHeartbeats 8000000 in
private theorem falling14 (x B : ℕ) (hx : 0 < x) (hB : B = 34359738368) :
    ([(false, 0), (true, 28132717568), (false, 19802759039), (true, 7763021312), (false, 20313753095), (true, 24402034612), (false, 3336118785), (true, 33568795215), (false, 135036472), (true, 34343068715), (false, 1474472), (true, 34359647277), (false, 3730), (true, 34359738277), (false, 0)] : List (Bool × ℕ)).foldr
      (fun s v => (v * x + (if s.1 then x-1 else 0)) * B + s.2) 0 =
      (x * B).descFactorial 14 := by
  let low (v c : ℕ) := (v * x + 0) * B + c
  let high (v c : ℕ) := (v * x + (x-1)) * B + c
  calc
    _ = (low (high (low (high (low (high (low (high (low (high (low (high (low (high (low 0 0) 34359738277) 3730) 34359647277) 1474472) 34343068715) 135036472) 33568795215) 3336118785) 24402034612) 20313753095) 7763021312) 19802759039) 28132717568) 0) := rfl
    _ = _ := by
      dsimp only [low, high]
      rw [hB]
      apply Int.ofNat_inj.mp
      norm_num [Nat.descFactorial]
      simp (disch := omega) only [Nat.cast_sub, Nat.cast_mul, Nat.cast_ofNat]
      ring

private theorem parity14_2801 :
    (Nat.digits 2 ((2^2801).descFactorial 14 / 42567525)).count 1 % 2 = 0 := by
  apply fold_certificate 13
  decide +kernel

private theorem parity14_9281 :
    (Nat.digits 2 ((2^9281).descFactorial 14 / 42567525)).count 1 % 2 = 0 := by
  apply fold_certificate 14
  decide +kernel

private theorem parity14_19001 :
    (Nat.digits 2 ((2^19001).descFactorial 14 / 42567525)).count 1 % 2 = 0 := by
  apply fold_certificate 16
  decide +kernel

private theorem parity14_22241 :
    (Nat.digits 2 ((2^22241).descFactorial 14 / 42567525)).count 1 % 2 = 0 := by
  apply fold_certificate 16
  decide +kernel

set_option maxHeartbeats 8000000 in
private theorem column14 (a : ℕ) (ha : 35 ≤ a)
    (hr : a % 22680 ∈ ([2801, 9281, 19001, 22241] : List ℕ)) :
    OeisA249609.isEvil ((2^a).choose 14) = true := by
  let ds : List (Bool × ℕ) := [(false, 0), (true, 28132717568), (false, 19802759039), (true, 7763021312), (false, 20313753095), (true, 24402034612), (false, 3336118785), (true, 33568795215), (false, 135036472), (true, 34343068715), (false, 1474472), (true, 34359647277), (false, 3730), (true, 34359738277), (false, 0)]
  refine (periodic_column (k := 14) (t := 35) (l := 11340) (d := 42567525) (z := 11)
    (ds := ds) ha (by decide) (by decide +kernel) ?_ ?_ (by decide)).2 ?_
  · dsimp only [ds]; decide
  · intro w
    rw [pow_add 2 w 35]
    exact falling14 (2^w) (2^35) (by positivity) (by decide)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with hr | hr | hr | hr
  · rw [show (a-35) % (11340+11340) + 35 = 2801 by omega]
    exact parity14_2801
  · rw [show (a-35) % (11340+11340) + 35 = 9281 by omega]
    exact parity14_9281
  · rw [show (a-35) % (11340+11340) + 35 = 19001 by omega]
    exact parity14_19001
  · rw [show (a-35) % (11340+11340) + 35 = 22241 by omega]
    exact parity14_22241

set_option maxHeartbeats 8000000 in
private theorem falling15 (x B : ℕ) (hx : 0 < x) (hB : B = 549755813888) :
    ([(false, 0), (false, 87178291200), (true, 266290166528), (false, 392156797823), (true, 238766553488), (false, 159721605679), (true, 493092447128), (false, 14409322927), (true, 547074360113), (false, 368411614), (true, 549718501613), (false, 2749746), (true, 549755670563), (false, 5004), (true, 549755813783), (false, 0)] : List (Bool × ℕ)).foldr
      (fun s v => (v * x + (if s.1 then x-1 else 0)) * B + s.2) 0 =
      (x * B).descFactorial 15 := by
  let low (v c : ℕ) := (v * x + 0) * B + c
  let high (v c : ℕ) := (v * x + (x-1)) * B + c
  calc
    _ = (low (low (high (low (high (low (high (low (high (low (high (low (high (low (high (low 0 0) 549755813783) 5004) 549755670563) 2749746) 549718501613) 368411614) 547074360113) 14409322927) 493092447128) 159721605679) 238766553488) 392156797823) 266290166528) 87178291200) 0) := rfl
    _ = _ := by
      dsimp only [low, high]
      rw [hB]
      apply Int.ofNat_inj.mp
      norm_num [Nat.descFactorial]
      simp (disch := omega) only [Nat.cast_sub, Nat.cast_mul, Nat.cast_ofNat]
      ring

private theorem parity15_28721 :
    (Nat.digits 2 ((2^28721).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 16
  decide +kernel

private theorem parity15_35201 :
    (Nat.digits 2 ((2^35201).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 17
  decide +kernel

private theorem parity15_51401 :
    (Nat.digits 2 ((2^51401).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 17
  decide +kernel

private theorem parity15_61121 :
    (Nat.digits 2 ((2^61121).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 17
  decide +kernel

private theorem parity15_74081 :
    (Nat.digits 2 ((2^74081).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 18
  decide +kernel

private theorem parity15_106481 :
    (Nat.digits 2 ((2^106481).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 18
  decide +kernel

private theorem parity15_129161 :
    (Nat.digits 2 ((2^129161).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 18
  decide +kernel

private theorem parity15_148601 :
    (Nat.digits 2 ((2^148601).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity15_151841 :
    (Nat.digits 2 ((2^151841).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity15_164801 :
    (Nat.digits 2 ((2^164801).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity15_174521 :
    (Nat.digits 2 ((2^174521).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity15_219881 :
    (Nat.digits 2 ((2^219881).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity15_239321 :
    (Nat.digits 2 ((2^239321).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity15_242561 :
    (Nat.digits 2 ((2^242561).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity15_255521 :
    (Nat.digits 2 ((2^255521).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity15_262001 :
    (Nat.digits 2 ((2^262001).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity15_265241 :
    (Nat.digits 2 ((2^265241).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity15_278201 :
    (Nat.digits 2 ((2^278201).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity15_284681 :
    (Nat.digits 2 ((2^284681).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 20
  decide +kernel

private theorem parity15_307361 :
    (Nat.digits 2 ((2^307361).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 20
  decide +kernel

private theorem parity15_333281 :
    (Nat.digits 2 ((2^333281).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 20
  decide +kernel

set_option maxHeartbeats 8000000 in
private theorem column15 (a : ℕ) (ha : 39 ≤ a)
    (hr : a % 340200 ∈ ([28721, 35201, 51401, 61121, 74081, 106481, 129161, 148601, 151841, 164801, 174521, 219881, 239321, 242561, 255521, 262001, 265241, 278201, 284681, 307361, 333281] : List ℕ)) :
    OeisA249609.isEvil ((2^a).choose 15) = true := by
  let ds : List (Bool × ℕ) := [(false, 0), (false, 87178291200), (true, 266290166528), (false, 392156797823), (true, 238766553488), (false, 159721605679), (true, 493092447128), (false, 14409322927), (true, 547074360113), (false, 368411614), (true, 549718501613), (false, 2749746), (true, 549755670563), (false, 5004), (true, 549755813783), (false, 0)]
  refine (periodic_column (k := 15) (t := 39) (l := 170100) (d := 638512875) (z := 11)
    (ds := ds) ha (by decide) (by decide +kernel) ?_ ?_ (by decide)).2 ?_
  · dsimp only [ds]; decide
  · intro w
    rw [pow_add 2 w 39]
    exact falling15 (2^w) (2^39) (by positivity) (by decide)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr
  · rw [show (a-39) % (170100+170100) + 39 = 28721 by omega]
    exact parity15_28721
  · rw [show (a-39) % (170100+170100) + 39 = 35201 by omega]
    exact parity15_35201
  · rw [show (a-39) % (170100+170100) + 39 = 51401 by omega]
    exact parity15_51401
  · rw [show (a-39) % (170100+170100) + 39 = 61121 by omega]
    exact parity15_61121
  · rw [show (a-39) % (170100+170100) + 39 = 74081 by omega]
    exact parity15_74081
  · rw [show (a-39) % (170100+170100) + 39 = 106481 by omega]
    exact parity15_106481
  · rw [show (a-39) % (170100+170100) + 39 = 129161 by omega]
    exact parity15_129161
  · rw [show (a-39) % (170100+170100) + 39 = 148601 by omega]
    exact parity15_148601
  · rw [show (a-39) % (170100+170100) + 39 = 151841 by omega]
    exact parity15_151841
  · rw [show (a-39) % (170100+170100) + 39 = 164801 by omega]
    exact parity15_164801
  · rw [show (a-39) % (170100+170100) + 39 = 174521 by omega]
    exact parity15_174521
  · rw [show (a-39) % (170100+170100) + 39 = 219881 by omega]
    exact parity15_219881
  · rw [show (a-39) % (170100+170100) + 39 = 239321 by omega]
    exact parity15_239321
  · rw [show (a-39) % (170100+170100) + 39 = 242561 by omega]
    exact parity15_242561
  · rw [show (a-39) % (170100+170100) + 39 = 255521 by omega]
    exact parity15_255521
  · rw [show (a-39) % (170100+170100) + 39 = 262001 by omega]
    exact parity15_262001
  · rw [show (a-39) % (170100+170100) + 39 = 265241 by omega]
    exact parity15_265241
  · rw [show (a-39) % (170100+170100) + 39 = 278201 by omega]
    exact parity15_278201
  · rw [show (a-39) % (170100+170100) + 39 = 284681 by omega]
    exact parity15_284681
  · rw [show (a-39) % (170100+170100) + 39 = 307361 by omega]
    exact parity15_307361
  · rw [show (a-39) % (170100+170100) + 39 = 333281 by omega]
    exact parity15_333281

set_option maxHeartbeats 8000000 in
private theorem falling16 (x B : ℕ) (hx : 0 < x) (hB : B = 8796093022208) :
    ([(false, 0), (true, 7488418654208), (false, 4339163001599), (true, 2630275407488), (false, 5056995703823), (true, 6089279676608), (false, 1009672107079), (true, 8523289811528), (false, 54631129552), (true, 8787885394208), (false, 928095739), (true, 8796014463728), (false, 4899621), (true, 8796092803808), (false, 6579), (true, 8796093022088), (false, 0)] : List (Bool × ℕ)).foldr
      (fun s v => (v * x + (if s.1 then x-1 else 0)) * B + s.2) 0 =
      (x * B).descFactorial 16 := by
  let low (v c : ℕ) := (v * x + 0) * B + c
  let high (v c : ℕ) := (v * x + (x-1)) * B + c
  calc
    _ = (low (high (low (high (low (high (low (high (low (high (low (high (low (high (low (high (low 0 0) 8796093022088) 6579) 8796092803808) 4899621) 8796014463728) 928095739) 8787885394208) 54631129552) 8523289811528) 1009672107079) 6089279676608) 5056995703823) 2630275407488) 4339163001599) 7488418654208) 0) := rfl
    _ = _ := by
      dsimp only [low, high]
      rw [hB]
      apply Int.ofNat_inj.mp
      norm_num [Nat.descFactorial]
      simp (disch := omega) only [Nat.cast_sub, Nat.cast_mul, Nat.cast_ofNat]
      ring

private theorem parity16_6041 :
    (Nat.digits 2 ((2^6041).descFactorial 16 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 14
  decide +kernel

private theorem parity16_12521 :
    (Nat.digits 2 ((2^12521).descFactorial 16 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 15
  decide +kernel

private theorem parity16_38441 :
    (Nat.digits 2 ((2^38441).descFactorial 16 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 17
  decide +kernel

private theorem parity16_125921 :
    (Nat.digits 2 ((2^125921).descFactorial 16 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 18
  decide +kernel

private theorem parity16_142121 :
    (Nat.digits 2 ((2^142121).descFactorial 16 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity16_187481 :
    (Nat.digits 2 ((2^187481).descFactorial 16 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity16_193961 :
    (Nat.digits 2 ((2^193961).descFactorial 16 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity16_197201 :
    (Nat.digits 2 ((2^197201).descFactorial 16 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity16_232841 :
    (Nat.digits 2 ((2^232841).descFactorial 16 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity16_287921 :
    (Nat.digits 2 ((2^287921).descFactorial 16 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 20
  decide +kernel

private theorem parity16_300881 :
    (Nat.digits 2 ((2^300881).descFactorial 16 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 20
  decide +kernel

set_option maxHeartbeats 8000000 in
private theorem column16 (a : ℕ) (ha : 43 ≤ a)
    (hr : a % 340200 ∈ ([6041, 12521, 38441, 125921, 142121, 187481, 193961, 197201, 232841, 287921, 300881] : List ℕ)) :
    OeisA249609.isEvil ((2^a).choose 16) = true := by
  let ds : List (Bool × ℕ) := [(false, 0), (true, 7488418654208), (false, 4339163001599), (true, 2630275407488), (false, 5056995703823), (true, 6089279676608), (false, 1009672107079), (true, 8523289811528), (false, 54631129552), (true, 8787885394208), (false, 928095739), (true, 8796014463728), (false, 4899621), (true, 8796092803808), (false, 6579), (true, 8796093022088), (false, 0)]
  refine (periodic_column (k := 16) (t := 43) (l := 170100) (d := 638512875) (z := 15)
    (ds := ds) ha (by decide) (by decide +kernel) ?_ ?_ (by decide)).2 ?_
  · dsimp only [ds]; decide
  · intro w
    rw [pow_add 2 w 43]
    exact falling16 (2^w) (2^43) (by positivity) (by decide)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr
  · rw [show (a-43) % (170100+170100) + 43 = 6041 by omega]
    exact parity16_6041
  · rw [show (a-43) % (170100+170100) + 43 = 12521 by omega]
    exact parity16_12521
  · rw [show (a-43) % (170100+170100) + 43 = 38441 by omega]
    exact parity16_38441
  · rw [show (a-43) % (170100+170100) + 43 = 125921 by omega]
    exact parity16_125921
  · rw [show (a-43) % (170100+170100) + 43 = 142121 by omega]
    exact parity16_142121
  · rw [show (a-43) % (170100+170100) + 43 = 187481 by omega]
    exact parity16_187481
  · rw [show (a-43) % (170100+170100) + 43 = 193961 by omega]
    exact parity16_193961
  · rw [show (a-43) % (170100+170100) + 43 = 197201 by omega]
    exact parity16_197201
  · rw [show (a-43) % (170100+170100) + 43 = 232841 by omega]
    exact parity16_232841
  · rw [show (a-43) % (170100+170100) + 43 = 287921 by omega]
    exact parity16_287921
  · rw [show (a-43) % (170100+170100) + 43 = 300881 by omega]
    exact parity16_300881

set_option maxHeartbeats 8000000 in
private theorem falling17 (x B : ℕ) (hx : 0 < x) (hB : B = 140737488355328) :
    ([(false, 0), (false, 20922789888000), (true, 70003205961728), (false, 102992244837119), (true, 53659739479424), (false, 48366009233423), (true, 121875921296448), (false, 5374523477959), (true, 139590587071800), (false, 185953177552), (true, 140714431195488), (false, 2185031419), (true, 140737331402896), (false, 8394021), (true, 140737488031648), (false, 8499), (true, 140737488355192), (false, 0)] : List (Bool × ℕ)).foldr
      (fun s v => (v * x + (if s.1 then x-1 else 0)) * B + s.2) 0 =
      (x * B).descFactorial 17 := by
  let low (v c : ℕ) := (v * x + 0) * B + c
  let high (v c : ℕ) := (v * x + (x-1)) * B + c
  calc
    _ = (low (low (high (low (high (low (high (low (high (low (high (low (high (low (high (low (high (low 0 0) 140737488355192) 8499) 140737488031648) 8394021) 140737331402896) 2185031419) 140714431195488) 185953177552) 139590587071800) 5374523477959) 121875921296448) 48366009233423) 53659739479424) 102992244837119) 70003205961728) 20922789888000) 0) := rfl
    _ = _ := by
      dsimp only [low, high]
      rw [hB]
      apply Int.ofNat_inj.mp
      norm_num [Nat.descFactorial]
      simp (disch := omega) only [Nat.cast_sub, Nat.cast_mul, Nat.cast_ofNat]
      ring

private theorem parity17_80561 :
    (Nat.digits 2 ((2^80561).descFactorial 17 / 10854718875)).count 1 % 2 = 0 := by
  apply fold_certificate 18
  decide +kernel

private theorem parity17_83801 :
    (Nat.digits 2 ((2^83801).descFactorial 17 / 10854718875)).count 1 % 2 = 0 := by
  apply fold_certificate 18
  decide +kernel

private theorem parity17_96761 :
    (Nat.digits 2 ((2^96761).descFactorial 17 / 10854718875)).count 1 % 2 = 0 := by
  apply fold_certificate 18
  decide +kernel

private theorem parity17_119441 :
    (Nat.digits 2 ((2^119441).descFactorial 17 / 10854718875)).count 1 % 2 = 0 := by
  apply fold_certificate 18
  decide +kernel

private theorem parity17_171281 :
    (Nat.digits 2 ((2^171281).descFactorial 17 / 10854718875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity17_310601 :
    (Nat.digits 2 ((2^310601).descFactorial 17 / 10854718875)).count 1 % 2 = 0 := by
  apply fold_certificate 20
  decide +kernel

private theorem parity17_330041 :
    (Nat.digits 2 ((2^330041).descFactorial 17 / 10854718875)).count 1 % 2 = 0 := by
  apply fold_certificate 20
  decide +kernel

private theorem parity17_355961 :
    (Nat.digits 2 ((2^355961).descFactorial 17 / 10854718875)).count 1 % 2 = 0 := by
  apply fold_certificate 20
  decide +kernel

private theorem parity17_398081 :
    (Nat.digits 2 ((2^398081).descFactorial 17 / 10854718875)).count 1 % 2 = 0 := by
  apply fold_certificate 20
  decide +kernel

private theorem parity17_443441 :
    (Nat.digits 2 ((2^443441).descFactorial 17 / 10854718875)).count 1 % 2 = 0 := by
  apply fold_certificate 20
  decide +kernel

private theorem parity17_550361 :
    (Nat.digits 2 ((2^550361).descFactorial 17 / 10854718875)).count 1 % 2 = 0 := by
  apply fold_certificate 21
  decide +kernel

private theorem parity17_556841 :
    (Nat.digits 2 ((2^556841).descFactorial 17 / 10854718875)).count 1 % 2 = 0 := by
  apply fold_certificate 21
  decide +kernel

private theorem parity17_663761 :
    (Nat.digits 2 ((2^663761).descFactorial 17 / 10854718875)).count 1 % 2 = 0 := by
  apply fold_certificate 21
  decide +kernel

set_option maxHeartbeats 8000000 in
private theorem column17 (a : ℕ) (ha : 47 ≤ a)
    (hr : a % 680400 ∈ ([80561, 83801, 96761, 119441, 171281, 310601, 330041, 355961, 398081, 443441, 550361, 556841, 663761] : List ℕ)) :
    OeisA249609.isEvil ((2^a).choose 17) = true := by
  let ds : List (Bool × ℕ) := [(false, 0), (false, 20922789888000), (true, 70003205961728), (false, 102992244837119), (true, 53659739479424), (false, 48366009233423), (true, 121875921296448), (false, 5374523477959), (true, 139590587071800), (false, 185953177552), (true, 140714431195488), (false, 2185031419), (true, 140737331402896), (false, 8394021), (true, 140737488031648), (false, 8499), (true, 140737488355192), (false, 0)]
  refine (periodic_column (k := 17) (t := 47) (l := 340200) (d := 10854718875) (z := 15)
    (ds := ds) ha (by decide) (by decide +kernel) ?_ ?_ (by decide)).2 ?_
  · dsimp only [ds]; decide
  · intro w
    rw [pow_add 2 w 47]
    exact falling17 (2^w) (2^47) (by positivity) (by decide)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr
  · rw [show (a-47) % (340200+340200) + 47 = 80561 by omega]
    exact parity17_80561
  · rw [show (a-47) % (340200+340200) + 47 = 83801 by omega]
    exact parity17_83801
  · rw [show (a-47) % (340200+340200) + 47 = 96761 by omega]
    exact parity17_96761
  · rw [show (a-47) % (340200+340200) + 47 = 119441 by omega]
    exact parity17_119441
  · rw [show (a-47) % (340200+340200) + 47 = 171281 by omega]
    exact parity17_171281
  · rw [show (a-47) % (340200+340200) + 47 = 310601 by omega]
    exact parity17_310601
  · rw [show (a-47) % (340200+340200) + 47 = 330041 by omega]
    exact parity17_330041
  · rw [show (a-47) % (340200+340200) + 47 = 355961 by omega]
    exact parity17_355961
  · rw [show (a-47) % (340200+340200) + 47 = 398081 by omega]
    exact parity17_398081
  · rw [show (a-47) % (340200+340200) + 47 = 443441 by omega]
    exact parity17_443441
  · rw [show (a-47) % (340200+340200) + 47 = 550361 by omega]
    exact parity17_550361
  · rw [show (a-47) % (340200+340200) + 47 = 556841 by omega]
    exact parity17_556841
  · rw [show (a-47) % (340200+340200) + 47 = 663761 by omega]
    exact parity17_663761

end Certificates

set_option maxRecDepth 100000 in
private theorem cover : ∀ q : Fin 210,
    (3240*q.val+2801) % 22680 ∈ ([2801, 9281, 19001, 22241] : List ℕ) ∨
    (3240*q.val+2801) % 340200 ∈ ([28721, 35201, 51401, 61121, 74081, 106481, 129161, 148601, 151841, 164801, 174521, 219881, 239321, 242561, 255521, 262001, 265241, 278201, 284681, 307361, 333281] : List ℕ) ∨
    (3240*q.val+2801) % 340200 ∈ ([6041, 12521, 38441, 125921, 142121, 187481, 193961, 197201, 232841, 287921, 300881] : List ℕ) ∨
    (3240*q.val+2801) % 680400 ∈ ([80561, 83801, 96761, 119441, 171281, 310601, 330041, 355961, 398081, 443441, 550361, 556841, 663761] : List ℕ) ∨
    q.val % 210 ∈ ([4, 17, 31, 64, 66] : List ℕ) ∨
    q.val % 210 ∈ ([99, 129, 130, 134] : List ℕ) ∨
    q.val % 210 ∈ ([141, 157, 200, 206] : List ℕ) := by decide +kernel

theorem main : H1 → H2 → H3 → OMA.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H1_R1.H4 := by
  intro h1 h2 h3 q
  have reduceMod (d : ℕ) (hd : d ∣ 680400) :
      (3240*(q%210)+2801)%d = (3240*q+2801)%d :=
    (((Nat.mod_modEq q 210).mul_left' 3240).of_dvd hd).add_right 2801
  have cases := cover ⟨q%210, Nat.mod_lt _ (by decide)⟩
  dsimp only at cases
  rw [reduceMod 22680 (by decide), reduceMod 340200 (by decide), reduceMod 680400 (by decide)] at cases
  rw [Nat.mod_mod_of_dvd q (by decide : 210 ∣ 210)] at cases
  have hbig : 32 ≤ 2^(3240*q+2801) :=
    le_trans (by decide : 32 ≤ 2^5) (Nat.pow_le_pow_right (by decide) (by omega))
  rcases cases with h | h | h | h | h | h | h
  · exact witness _ 14 (by decide) (by omega) (column14 _ (by omega) h)
  · exact witness _ 15 (by decide) (by omega) (column15 _ (by omega) h)
  · exact witness _ 16 (by decide) (by omega) (column16 _ (by omega) h)
  · exact witness _ 17 (by decide) (by omega) (column17 _ (by omega) h)
  · exact h1 q h
  · exact h2 q h
  · exact h3 q h

end OMA.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H1_R1_H4_R1
