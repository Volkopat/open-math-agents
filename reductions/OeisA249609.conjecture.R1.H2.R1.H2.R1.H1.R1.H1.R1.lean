import OMAReductions.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H1_R1
import Mathlib.Tactic

/-!
# Binomial columns 14, 15, 16, 17 for the exponents `3240*q + 209` (OEIS A249609)

For `a = 3240*q + 209`, the columns 14, 15, 16, 17 give an evil binomial coefficient
`C(2^a, k)` on all but 11 residue classes of `q` modulo 105. As in ZedingZhang's sibling
reduction for the class 2705, PanPapag's periodicity theorem from the parent reduction reduces each
column to one representative exponent per residue class of `a` modulo twice the order of 2 modulo
the odd part of `k!`, and the parity at each representative is certified by folding with bitwise xor.
Column 17 has period 680400 = 3240 * 210, so the case split runs over `q` modulo 210.
The 11 remaining classes are the hypotheses.
-/

namespace OMA.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H1_R1_H1_R1

open OMA.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H1_R1

def H1 : Prop :=
  ∀ q : ℕ, q % 105 ∈ ([0, 23, 30, 84] : List ℕ) →
    ∃ k ∈ List.range' 1 (2 ^ (3240*q+209)),
      OeisA249609.isEvil ((2 ^ (3240*q+209)).choose k) = true

def H2 : Prop :=
  ∀ q : ℕ, q % 105 ∈ ([5, 26, 40, 87] : List ℕ) →
    ∃ k ∈ List.range' 1 (2 ^ (3240*q+209)),
      OeisA249609.isEvil ((2 ^ (3240*q+209)).choose k) = true

def H3 : Prop :=
  ∀ q : ℕ, q % 105 ∈ ([29, 42, 52] : List ℕ) →
    ∃ k ∈ List.range' 1 (2 ^ (3240*q+209)),
      OeisA249609.isEvil ((2 ^ (3240*q+209)).choose k) = true

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

private theorem parity14_13169 :
    (Nat.digits 2 ((2^13169).descFactorial 14 / 42567525)).count 1 % 2 = 0 := by
  apply fold_certificate 15
  decide +kernel

private theorem parity14_19649 :
    (Nat.digits 2 ((2^19649).descFactorial 14 / 42567525)).count 1 % 2 = 0 := by
  apply fold_certificate 16
  decide +kernel

set_option maxHeartbeats 8000000 in
private theorem column14 (a : ℕ) (ha : 35 ≤ a)
    (hr : a % 22680 ∈ ([13169, 19649] : List ℕ)) :
    OeisA249609.isEvil ((2^a).choose 14) = true := by
  let ds : List (Bool × ℕ) := [(false, 0), (true, 28132717568), (false, 19802759039), (true, 7763021312), (false, 20313753095), (true, 24402034612), (false, 3336118785), (true, 33568795215), (false, 135036472), (true, 34343068715), (false, 1474472), (true, 34359647277), (false, 3730), (true, 34359738277), (false, 0)]
  refine (periodic_column (k := 14) (t := 35) (l := 11340) (d := 42567525) (z := 11)
    (ds := ds) ha (by decide) (by decide +kernel) ?_ ?_ (by decide)).2 ?_
  · dsimp only [ds]; decide
  · intro w
    rw [pow_add 2 w 35]
    exact falling14 (2^w) (2^35) (by positivity) (by decide)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with hr | hr
  · rw [show (a-35) % (11340+11340) + 35 = 13169 by omega]
    exact parity14_13169
  · rw [show (a-35) % (11340+11340) + 35 = 19649 by omega]
    exact parity14_19649

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

private theorem parity15_3449 :
    (Nat.digits 2 ((2^3449).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 13
  decide +kernel

private theorem parity15_6689 :
    (Nat.digits 2 ((2^6689).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 14
  decide +kernel

private theorem parity15_22889 :
    (Nat.digits 2 ((2^22889).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 16
  decide +kernel

private theorem parity15_32609 :
    (Nat.digits 2 ((2^32609).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 16
  decide +kernel

private theorem parity15_45569 :
    (Nat.digits 2 ((2^45569).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 17
  decide +kernel

private theorem parity15_55289 :
    (Nat.digits 2 ((2^55289).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 17
  decide +kernel

private theorem parity15_61769 :
    (Nat.digits 2 ((2^61769).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 17
  decide +kernel

private theorem parity15_68249 :
    (Nat.digits 2 ((2^68249).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 17
  decide +kernel

private theorem parity15_71489 :
    (Nat.digits 2 ((2^71489).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 18
  decide +kernel

private theorem parity15_77969 :
    (Nat.digits 2 ((2^77969).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 18
  decide +kernel

private theorem parity15_90929 :
    (Nat.digits 2 ((2^90929).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 18
  decide +kernel

private theorem parity15_100649 :
    (Nat.digits 2 ((2^100649).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 18
  decide +kernel

private theorem parity15_107129 :
    (Nat.digits 2 ((2^107129).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 18
  decide +kernel

private theorem parity15_116849 :
    (Nat.digits 2 ((2^116849).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 18
  decide +kernel

private theorem parity15_120089 :
    (Nat.digits 2 ((2^120089).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 18
  decide +kernel

private theorem parity15_139529 :
    (Nat.digits 2 ((2^139529).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 18
  decide +kernel

private theorem parity15_146009 :
    (Nat.digits 2 ((2^146009).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity15_152489 :
    (Nat.digits 2 ((2^152489).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity15_175169 :
    (Nat.digits 2 ((2^175169).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity15_184889 :
    (Nat.digits 2 ((2^184889).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity15_188129 :
    (Nat.digits 2 ((2^188129).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity15_191369 :
    (Nat.digits 2 ((2^191369).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity15_197849 :
    (Nat.digits 2 ((2^197849).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity15_210809 :
    (Nat.digits 2 ((2^210809).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity15_214049 :
    (Nat.digits 2 ((2^214049).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity15_220529 :
    (Nat.digits 2 ((2^220529).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity15_227009 :
    (Nat.digits 2 ((2^227009).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity15_233489 :
    (Nat.digits 2 ((2^233489).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity15_243209 :
    (Nat.digits 2 ((2^243209).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity15_252929 :
    (Nat.digits 2 ((2^252929).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity15_256169 :
    (Nat.digits 2 ((2^256169).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity15_259409 :
    (Nat.digits 2 ((2^259409).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity15_265889 :
    (Nat.digits 2 ((2^265889).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity15_275609 :
    (Nat.digits 2 ((2^275609).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity15_288569 :
    (Nat.digits 2 ((2^288569).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 20
  decide +kernel

private theorem parity15_295049 :
    (Nat.digits 2 ((2^295049).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 20
  decide +kernel

private theorem parity15_298289 :
    (Nat.digits 2 ((2^298289).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 20
  decide +kernel

private theorem parity15_304769 :
    (Nat.digits 2 ((2^304769).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 20
  decide +kernel

private theorem parity15_311249 :
    (Nat.digits 2 ((2^311249).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 20
  decide +kernel

private theorem parity15_327449 :
    (Nat.digits 2 ((2^327449).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 20
  decide +kernel

private theorem parity15_333929 :
    (Nat.digits 2 ((2^333929).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 20
  decide +kernel

set_option maxHeartbeats 8000000 in
private theorem column15 (a : ℕ) (ha : 39 ≤ a)
    (hr : a % 340200 ∈ ([3449, 6689, 22889, 32609, 45569, 55289, 61769, 68249, 71489, 77969, 90929, 100649, 107129, 116849, 120089, 139529, 146009, 152489, 175169, 184889, 188129, 191369, 197849, 210809, 214049, 220529, 227009, 233489, 243209, 252929, 256169, 259409, 265889, 275609, 288569, 295049, 298289, 304769, 311249, 327449, 333929] : List ℕ)) :
    OeisA249609.isEvil ((2^a).choose 15) = true := by
  let ds : List (Bool × ℕ) := [(false, 0), (false, 87178291200), (true, 266290166528), (false, 392156797823), (true, 238766553488), (false, 159721605679), (true, 493092447128), (false, 14409322927), (true, 547074360113), (false, 368411614), (true, 549718501613), (false, 2749746), (true, 549755670563), (false, 5004), (true, 549755813783), (false, 0)]
  refine (periodic_column (k := 15) (t := 39) (l := 170100) (d := 638512875) (z := 11)
    (ds := ds) ha (by decide) (by decide +kernel) ?_ ?_ (by decide)).2 ?_
  · dsimp only [ds]; decide
  · intro w
    rw [pow_add 2 w 39]
    exact falling15 (2^w) (2^39) (by positivity) (by decide)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr
  · rw [show (a-39) % (170100+170100) + 39 = 3449 by omega]
    exact parity15_3449
  · rw [show (a-39) % (170100+170100) + 39 = 6689 by omega]
    exact parity15_6689
  · rw [show (a-39) % (170100+170100) + 39 = 22889 by omega]
    exact parity15_22889
  · rw [show (a-39) % (170100+170100) + 39 = 32609 by omega]
    exact parity15_32609
  · rw [show (a-39) % (170100+170100) + 39 = 45569 by omega]
    exact parity15_45569
  · rw [show (a-39) % (170100+170100) + 39 = 55289 by omega]
    exact parity15_55289
  · rw [show (a-39) % (170100+170100) + 39 = 61769 by omega]
    exact parity15_61769
  · rw [show (a-39) % (170100+170100) + 39 = 68249 by omega]
    exact parity15_68249
  · rw [show (a-39) % (170100+170100) + 39 = 71489 by omega]
    exact parity15_71489
  · rw [show (a-39) % (170100+170100) + 39 = 77969 by omega]
    exact parity15_77969
  · rw [show (a-39) % (170100+170100) + 39 = 90929 by omega]
    exact parity15_90929
  · rw [show (a-39) % (170100+170100) + 39 = 100649 by omega]
    exact parity15_100649
  · rw [show (a-39) % (170100+170100) + 39 = 107129 by omega]
    exact parity15_107129
  · rw [show (a-39) % (170100+170100) + 39 = 116849 by omega]
    exact parity15_116849
  · rw [show (a-39) % (170100+170100) + 39 = 120089 by omega]
    exact parity15_120089
  · rw [show (a-39) % (170100+170100) + 39 = 139529 by omega]
    exact parity15_139529
  · rw [show (a-39) % (170100+170100) + 39 = 146009 by omega]
    exact parity15_146009
  · rw [show (a-39) % (170100+170100) + 39 = 152489 by omega]
    exact parity15_152489
  · rw [show (a-39) % (170100+170100) + 39 = 175169 by omega]
    exact parity15_175169
  · rw [show (a-39) % (170100+170100) + 39 = 184889 by omega]
    exact parity15_184889
  · rw [show (a-39) % (170100+170100) + 39 = 188129 by omega]
    exact parity15_188129
  · rw [show (a-39) % (170100+170100) + 39 = 191369 by omega]
    exact parity15_191369
  · rw [show (a-39) % (170100+170100) + 39 = 197849 by omega]
    exact parity15_197849
  · rw [show (a-39) % (170100+170100) + 39 = 210809 by omega]
    exact parity15_210809
  · rw [show (a-39) % (170100+170100) + 39 = 214049 by omega]
    exact parity15_214049
  · rw [show (a-39) % (170100+170100) + 39 = 220529 by omega]
    exact parity15_220529
  · rw [show (a-39) % (170100+170100) + 39 = 227009 by omega]
    exact parity15_227009
  · rw [show (a-39) % (170100+170100) + 39 = 233489 by omega]
    exact parity15_233489
  · rw [show (a-39) % (170100+170100) + 39 = 243209 by omega]
    exact parity15_243209
  · rw [show (a-39) % (170100+170100) + 39 = 252929 by omega]
    exact parity15_252929
  · rw [show (a-39) % (170100+170100) + 39 = 256169 by omega]
    exact parity15_256169
  · rw [show (a-39) % (170100+170100) + 39 = 259409 by omega]
    exact parity15_259409
  · rw [show (a-39) % (170100+170100) + 39 = 265889 by omega]
    exact parity15_265889
  · rw [show (a-39) % (170100+170100) + 39 = 275609 by omega]
    exact parity15_275609
  · rw [show (a-39) % (170100+170100) + 39 = 288569 by omega]
    exact parity15_288569
  · rw [show (a-39) % (170100+170100) + 39 = 295049 by omega]
    exact parity15_295049
  · rw [show (a-39) % (170100+170100) + 39 = 298289 by omega]
    exact parity15_298289
  · rw [show (a-39) % (170100+170100) + 39 = 304769 by omega]
    exact parity15_304769
  · rw [show (a-39) % (170100+170100) + 39 = 311249 by omega]
    exact parity15_311249
  · rw [show (a-39) % (170100+170100) + 39 = 327449 by omega]
    exact parity15_327449
  · rw [show (a-39) % (170100+170100) + 39 = 333929 by omega]
    exact parity15_333929

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

private theorem parity16_48809 :
    (Nat.digits 2 ((2^48809).descFactorial 16 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 17
  decide +kernel

private theorem parity16_142769 :
    (Nat.digits 2 ((2^142769).descFactorial 16 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity16_181649 :
    (Nat.digits 2 ((2^181649).descFactorial 16 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity16_204329 :
    (Nat.digits 2 ((2^204329).descFactorial 16 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity16_207569 :
    (Nat.digits 2 ((2^207569).descFactorial 16 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity16_230249 :
    (Nat.digits 2 ((2^230249).descFactorial 16 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity16_278849 :
    (Nat.digits 2 ((2^278849).descFactorial 16 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 20
  decide +kernel

private theorem parity16_301529 :
    (Nat.digits 2 ((2^301529).descFactorial 16 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 20
  decide +kernel

private theorem parity16_317729 :
    (Nat.digits 2 ((2^317729).descFactorial 16 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 20
  decide +kernel

private theorem parity16_320969 :
    (Nat.digits 2 ((2^320969).descFactorial 16 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 20
  decide +kernel

private theorem parity16_324209 :
    (Nat.digits 2 ((2^324209).descFactorial 16 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 20
  decide +kernel

set_option maxHeartbeats 8000000 in
private theorem column16 (a : ℕ) (ha : 43 ≤ a)
    (hr : a % 340200 ∈ ([48809, 142769, 181649, 204329, 207569, 230249, 278849, 301529, 317729, 320969, 324209] : List ℕ)) :
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
  · rw [show (a-43) % (170100+170100) + 43 = 48809 by omega]
    exact parity16_48809
  · rw [show (a-43) % (170100+170100) + 43 = 142769 by omega]
    exact parity16_142769
  · rw [show (a-43) % (170100+170100) + 43 = 181649 by omega]
    exact parity16_181649
  · rw [show (a-43) % (170100+170100) + 43 = 204329 by omega]
    exact parity16_204329
  · rw [show (a-43) % (170100+170100) + 43 = 207569 by omega]
    exact parity16_207569
  · rw [show (a-43) % (170100+170100) + 43 = 230249 by omega]
    exact parity16_230249
  · rw [show (a-43) % (170100+170100) + 43 = 278849 by omega]
    exact parity16_278849
  · rw [show (a-43) % (170100+170100) + 43 = 301529 by omega]
    exact parity16_301529
  · rw [show (a-43) % (170100+170100) + 43 = 317729 by omega]
    exact parity16_317729
  · rw [show (a-43) % (170100+170100) + 43 = 320969 by omega]
    exact parity16_320969
  · rw [show (a-43) % (170100+170100) + 43 = 324209 by omega]
    exact parity16_324209

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

private theorem parity17_9929 :
    (Nat.digits 2 ((2^9929).descFactorial 17 / 10854718875)).count 1 % 2 = 0 := by
  apply fold_certificate 15
  decide +kernel

private theorem parity17_26129 :
    (Nat.digits 2 ((2^26129).descFactorial 17 / 10854718875)).count 1 % 2 = 0 := by
  apply fold_certificate 16
  decide +kernel

private theorem parity17_29369 :
    (Nat.digits 2 ((2^29369).descFactorial 17 / 10854718875)).count 1 % 2 = 0 := by
  apply fold_certificate 16
  decide +kernel

private theorem parity17_39089 :
    (Nat.digits 2 ((2^39089).descFactorial 17 / 10854718875)).count 1 % 2 = 0 := by
  apply fold_certificate 17
  decide +kernel

private theorem parity17_52049 :
    (Nat.digits 2 ((2^52049).descFactorial 17 / 10854718875)).count 1 % 2 = 0 := by
  apply fold_certificate 17
  decide +kernel

private theorem parity17_113609 :
    (Nat.digits 2 ((2^113609).descFactorial 17 / 10854718875)).count 1 % 2 = 0 := by
  apply fold_certificate 18
  decide +kernel

private theorem parity17_123329 :
    (Nat.digits 2 ((2^123329).descFactorial 17 / 10854718875)).count 1 % 2 = 0 := by
  apply fold_certificate 18
  decide +kernel

private theorem parity17_158969 :
    (Nat.digits 2 ((2^158969).descFactorial 17 / 10854718875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity17_162209 :
    (Nat.digits 2 ((2^162209).descFactorial 17 / 10854718875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity17_165449 :
    (Nat.digits 2 ((2^165449).descFactorial 17 / 10854718875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity17_236729 :
    (Nat.digits 2 ((2^236729).descFactorial 17 / 10854718875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity17_249689 :
    (Nat.digits 2 ((2^249689).descFactorial 17 / 10854718875)).count 1 % 2 = 0 := by
  apply fold_certificate 20
  decide +kernel

private theorem parity17_350129 :
    (Nat.digits 2 ((2^350129).descFactorial 17 / 10854718875)).count 1 % 2 = 0 := by
  apply fold_certificate 20
  decide +kernel

private theorem parity17_366329 :
    (Nat.digits 2 ((2^366329).descFactorial 17 / 10854718875)).count 1 % 2 = 0 := by
  apply fold_certificate 20
  decide +kernel

private theorem parity17_369569 :
    (Nat.digits 2 ((2^369569).descFactorial 17 / 10854718875)).count 1 % 2 = 0 := by
  apply fold_certificate 20
  decide +kernel

private theorem parity17_379289 :
    (Nat.digits 2 ((2^379289).descFactorial 17 / 10854718875)).count 1 % 2 = 0 := by
  apply fold_certificate 20
  decide +kernel

private theorem parity17_392249 :
    (Nat.digits 2 ((2^392249).descFactorial 17 / 10854718875)).count 1 % 2 = 0 := by
  apply fold_certificate 20
  decide +kernel

private theorem parity17_453809 :
    (Nat.digits 2 ((2^453809).descFactorial 17 / 10854718875)).count 1 % 2 = 0 := by
  apply fold_certificate 20
  decide +kernel

private theorem parity17_463529 :
    (Nat.digits 2 ((2^463529).descFactorial 17 / 10854718875)).count 1 % 2 = 0 := by
  apply fold_certificate 20
  decide +kernel

private theorem parity17_499169 :
    (Nat.digits 2 ((2^499169).descFactorial 17 / 10854718875)).count 1 % 2 = 0 := by
  apply fold_certificate 21
  decide +kernel

private theorem parity17_502409 :
    (Nat.digits 2 ((2^502409).descFactorial 17 / 10854718875)).count 1 % 2 = 0 := by
  apply fold_certificate 21
  decide +kernel

private theorem parity17_505649 :
    (Nat.digits 2 ((2^505649).descFactorial 17 / 10854718875)).count 1 % 2 = 0 := by
  apply fold_certificate 21
  decide +kernel

private theorem parity17_576929 :
    (Nat.digits 2 ((2^576929).descFactorial 17 / 10854718875)).count 1 % 2 = 0 := by
  apply fold_certificate 21
  decide +kernel

private theorem parity17_589889 :
    (Nat.digits 2 ((2^589889).descFactorial 17 / 10854718875)).count 1 % 2 = 0 := by
  apply fold_certificate 21
  decide +kernel

set_option maxHeartbeats 8000000 in
private theorem column17 (a : ℕ) (ha : 47 ≤ a)
    (hr : a % 680400 ∈ ([9929, 26129, 29369, 39089, 52049, 113609, 123329, 158969, 162209, 165449, 236729, 249689, 350129, 366329, 369569, 379289, 392249, 453809, 463529, 499169, 502409, 505649, 576929, 589889] : List ℕ)) :
    OeisA249609.isEvil ((2^a).choose 17) = true := by
  let ds : List (Bool × ℕ) := [(false, 0), (false, 20922789888000), (true, 70003205961728), (false, 102992244837119), (true, 53659739479424), (false, 48366009233423), (true, 121875921296448), (false, 5374523477959), (true, 139590587071800), (false, 185953177552), (true, 140714431195488), (false, 2185031419), (true, 140737331402896), (false, 8394021), (true, 140737488031648), (false, 8499), (true, 140737488355192), (false, 0)]
  refine (periodic_column (k := 17) (t := 47) (l := 340200) (d := 10854718875) (z := 15)
    (ds := ds) ha (by decide) (by decide +kernel) ?_ ?_ (by decide)).2 ?_
  · dsimp only [ds]; decide
  · intro w
    rw [pow_add 2 w 47]
    exact falling17 (2^w) (2^47) (by positivity) (by decide)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr
  · rw [show (a-47) % (340200+340200) + 47 = 9929 by omega]
    exact parity17_9929
  · rw [show (a-47) % (340200+340200) + 47 = 26129 by omega]
    exact parity17_26129
  · rw [show (a-47) % (340200+340200) + 47 = 29369 by omega]
    exact parity17_29369
  · rw [show (a-47) % (340200+340200) + 47 = 39089 by omega]
    exact parity17_39089
  · rw [show (a-47) % (340200+340200) + 47 = 52049 by omega]
    exact parity17_52049
  · rw [show (a-47) % (340200+340200) + 47 = 113609 by omega]
    exact parity17_113609
  · rw [show (a-47) % (340200+340200) + 47 = 123329 by omega]
    exact parity17_123329
  · rw [show (a-47) % (340200+340200) + 47 = 158969 by omega]
    exact parity17_158969
  · rw [show (a-47) % (340200+340200) + 47 = 162209 by omega]
    exact parity17_162209
  · rw [show (a-47) % (340200+340200) + 47 = 165449 by omega]
    exact parity17_165449
  · rw [show (a-47) % (340200+340200) + 47 = 236729 by omega]
    exact parity17_236729
  · rw [show (a-47) % (340200+340200) + 47 = 249689 by omega]
    exact parity17_249689
  · rw [show (a-47) % (340200+340200) + 47 = 350129 by omega]
    exact parity17_350129
  · rw [show (a-47) % (340200+340200) + 47 = 366329 by omega]
    exact parity17_366329
  · rw [show (a-47) % (340200+340200) + 47 = 369569 by omega]
    exact parity17_369569
  · rw [show (a-47) % (340200+340200) + 47 = 379289 by omega]
    exact parity17_379289
  · rw [show (a-47) % (340200+340200) + 47 = 392249 by omega]
    exact parity17_392249
  · rw [show (a-47) % (340200+340200) + 47 = 453809 by omega]
    exact parity17_453809
  · rw [show (a-47) % (340200+340200) + 47 = 463529 by omega]
    exact parity17_463529
  · rw [show (a-47) % (340200+340200) + 47 = 499169 by omega]
    exact parity17_499169
  · rw [show (a-47) % (340200+340200) + 47 = 502409 by omega]
    exact parity17_502409
  · rw [show (a-47) % (340200+340200) + 47 = 505649 by omega]
    exact parity17_505649
  · rw [show (a-47) % (340200+340200) + 47 = 576929 by omega]
    exact parity17_576929
  · rw [show (a-47) % (340200+340200) + 47 = 589889 by omega]
    exact parity17_589889

end Certificates

set_option maxRecDepth 100000 in
private theorem cover : ∀ q : Fin 210,
    (3240*q.val+209) % 22680 ∈ ([13169, 19649] : List ℕ) ∨
    (3240*q.val+209) % 340200 ∈ ([3449, 6689, 22889, 32609, 45569, 55289, 61769, 68249, 71489, 77969, 90929, 100649, 107129, 116849, 120089, 139529, 146009, 152489, 175169, 184889, 188129, 191369, 197849, 210809, 214049, 220529, 227009, 233489, 243209, 252929, 256169, 259409, 265889, 275609, 288569, 295049, 298289, 304769, 311249, 327449, 333929] : List ℕ) ∨
    (3240*q.val+209) % 340200 ∈ ([48809, 142769, 181649, 204329, 207569, 230249, 278849, 301529, 317729, 320969, 324209] : List ℕ) ∨
    (3240*q.val+209) % 680400 ∈ ([9929, 26129, 29369, 39089, 52049, 113609, 123329, 158969, 162209, 165449, 236729, 249689, 350129, 366329, 369569, 379289, 392249, 453809, 463529, 499169, 502409, 505649, 576929, 589889] : List ℕ) ∨
    q.val % 105 ∈ ([0, 23, 30, 84] : List ℕ) ∨
    q.val % 105 ∈ ([5, 26, 40, 87] : List ℕ) ∨
    q.val % 105 ∈ ([29, 42, 52] : List ℕ) := by decide +kernel

theorem main : H1 → H2 → H3 → OMA.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H1_R1.H1 := by
  intro h1 h2 h3 q
  have reduceMod (d : ℕ) (hd : d ∣ 680400) :
      (3240*(q%210)+209)%d = (3240*q+209)%d :=
    (((Nat.mod_modEq q 210).mul_left' 3240).of_dvd hd).add_right 209
  have cases := cover ⟨q%210, Nat.mod_lt _ (by decide)⟩
  dsimp only at cases
  rw [reduceMod 22680 (by decide), reduceMod 340200 (by decide), reduceMod 680400 (by decide)] at cases
  rw [Nat.mod_mod_of_dvd q (by decide : 105 ∣ 210)] at cases
  have hbig : 32 ≤ 2^(3240*q+209) :=
    le_trans (by decide : 32 ≤ 2^5) (Nat.pow_le_pow_right (by decide) (by omega))
  rcases cases with h | h | h | h | h | h | h
  · exact witness _ 14 (by decide) (by omega) (column14 _ (by omega) h)
  · exact witness _ 15 (by decide) (by omega) (column15 _ (by omega) h)
  · exact witness _ 16 (by decide) (by omega) (column16 _ (by omega) h)
  · exact witness _ 17 (by decide) (by omega) (column17 _ (by omega) h)
  · exact h1 q h
  · exact h2 q h
  · exact h3 q h

end OMA.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H1_R1_H1_R1
