import OMAReductions.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H1_R1
import Mathlib.Tactic

/-!
# Binomial columns 14, 15, 16, 17 for the exponents `3240*q + 545` (OEIS A249609)

For `a = 3240*q + 545`, the columns 14, 15, 16, 17 give an evil binomial coefficient
`C(2^a, k)` on all but 5 residue classes of `q` modulo 105. As in ZedingZhang's sibling
reduction for the class 2705, PanPapag's periodicity theorem from the parent reduction reduces each
column to one representative exponent per residue class of `a` modulo twice the order of 2 modulo
the odd part of `k!`, and the parity at each representative is certified by folding with bitwise xor.
Column 17 has period 680400 = 3240 * 210, so the case split runs over `q` modulo 210.
The 5 remaining classes are the hypotheses.
-/

namespace OMA.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H1_R1_H2_R1

open OMA.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H1_R1

def H1 : Prop :=
  ∀ q : ℕ, q % 105 ∈ ([9, 10] : List ℕ) →
    ∃ k ∈ List.range' 1 (2 ^ (3240*q+545)),
      OeisA249609.isEvil ((2 ^ (3240*q+545)).choose k) = true

def H2 : Prop :=
  ∀ q : ℕ, q % 105 ∈ ([37, 38] : List ℕ) →
    ∃ k ∈ List.range' 1 (2 ^ (3240*q+545)),
      OeisA249609.isEvil ((2 ^ (3240*q+545)).choose k) = true

def H3 : Prop :=
  ∀ q : ℕ, q % 105 ∈ ([91] : List ℕ) →
    ∃ k ∈ List.range' 1 (2 ^ (3240*q+545)),
      OeisA249609.isEvil ((2 ^ (3240*q+545)).choose k) = true

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

private theorem parity14_13505 :
    (Nat.digits 2 ((2^13505).descFactorial 14 / 42567525)).count 1 % 2 = 0 := by
  apply fold_certificate 15
  decide +kernel

private theorem parity14_16745 :
    (Nat.digits 2 ((2^16745).descFactorial 14 / 42567525)).count 1 % 2 = 0 := by
  apply fold_certificate 15
  decide +kernel

private theorem parity14_19985 :
    (Nat.digits 2 ((2^19985).descFactorial 14 / 42567525)).count 1 % 2 = 0 := by
  apply fold_certificate 16
  decide +kernel

set_option maxHeartbeats 8000000 in
private theorem column14 (a : ℕ) (ha : 35 ≤ a)
    (hr : a % 22680 ∈ ([13505, 16745, 19985] : List ℕ)) :
    OeisA249609.isEvil ((2^a).choose 14) = true := by
  let ds : List (Bool × ℕ) := [(false, 0), (true, 28132717568), (false, 19802759039), (true, 7763021312), (false, 20313753095), (true, 24402034612), (false, 3336118785), (true, 33568795215), (false, 135036472), (true, 34343068715), (false, 1474472), (true, 34359647277), (false, 3730), (true, 34359738277), (false, 0)]
  refine (periodic_column (k := 14) (t := 35) (l := 11340) (d := 42567525) (z := 11)
    (ds := ds) ha (by decide) (by decide +kernel) ?_ ?_ (by decide)).2 ?_
  · dsimp only [ds]; decide
  · intro w
    rw [pow_add 2 w 35]
    exact falling14 (2^w) (2^35) (by positivity) (by decide)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with hr | hr | hr
  · rw [show (a-35) % (11340+11340) + 35 = 13505 by omega]
    exact parity14_13505
  · rw [show (a-35) % (11340+11340) + 35 = 16745 by omega]
    exact parity14_16745
  · rw [show (a-35) % (11340+11340) + 35 = 19985 by omega]
    exact parity14_19985

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

private theorem parity15_7025 :
    (Nat.digits 2 ((2^7025).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 14
  decide +kernel

private theorem parity15_23225 :
    (Nat.digits 2 ((2^23225).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 16
  decide +kernel

private theorem parity15_45905 :
    (Nat.digits 2 ((2^45905).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 17
  decide +kernel

private theorem parity15_52385 :
    (Nat.digits 2 ((2^52385).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 17
  decide +kernel

private theorem parity15_55625 :
    (Nat.digits 2 ((2^55625).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 17
  decide +kernel

private theorem parity15_68585 :
    (Nat.digits 2 ((2^68585).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 17
  decide +kernel

private theorem parity15_71825 :
    (Nat.digits 2 ((2^71825).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 18
  decide +kernel

private theorem parity15_78305 :
    (Nat.digits 2 ((2^78305).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 18
  decide +kernel

private theorem parity15_91265 :
    (Nat.digits 2 ((2^91265).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 18
  decide +kernel

private theorem parity15_100985 :
    (Nat.digits 2 ((2^100985).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 18
  decide +kernel

private theorem parity15_117185 :
    (Nat.digits 2 ((2^117185).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 18
  decide +kernel

private theorem parity15_136625 :
    (Nat.digits 2 ((2^136625).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 18
  decide +kernel

private theorem parity15_143105 :
    (Nat.digits 2 ((2^143105).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity15_159305 :
    (Nat.digits 2 ((2^159305).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity15_162545 :
    (Nat.digits 2 ((2^162545).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity15_181985 :
    (Nat.digits 2 ((2^181985).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity15_185225 :
    (Nat.digits 2 ((2^185225).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity15_188465 :
    (Nat.digits 2 ((2^188465).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity15_204665 :
    (Nat.digits 2 ((2^204665).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity15_207905 :
    (Nat.digits 2 ((2^207905).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity15_214385 :
    (Nat.digits 2 ((2^214385).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity15_227345 :
    (Nat.digits 2 ((2^227345).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity15_233825 :
    (Nat.digits 2 ((2^233825).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity15_237065 :
    (Nat.digits 2 ((2^237065).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity15_250025 :
    (Nat.digits 2 ((2^250025).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity15_253265 :
    (Nat.digits 2 ((2^253265).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity15_275945 :
    (Nat.digits 2 ((2^275945).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity15_279185 :
    (Nat.digits 2 ((2^279185).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity15_282425 :
    (Nat.digits 2 ((2^282425).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 20
  decide +kernel

private theorem parity15_298625 :
    (Nat.digits 2 ((2^298625).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 20
  decide +kernel

private theorem parity15_301865 :
    (Nat.digits 2 ((2^301865).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 20
  decide +kernel

private theorem parity15_305105 :
    (Nat.digits 2 ((2^305105).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 20
  decide +kernel

private theorem parity15_318065 :
    (Nat.digits 2 ((2^318065).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 20
  decide +kernel

private theorem parity15_324545 :
    (Nat.digits 2 ((2^324545).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 20
  decide +kernel

private theorem parity15_327785 :
    (Nat.digits 2 ((2^327785).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 20
  decide +kernel

set_option maxHeartbeats 8000000 in
private theorem column15 (a : ℕ) (ha : 39 ≤ a)
    (hr : a % 340200 ∈ ([7025, 23225, 45905, 52385, 55625, 68585, 71825, 78305, 91265, 100985, 117185, 136625, 143105, 159305, 162545, 181985, 185225, 188465, 204665, 207905, 214385, 227345, 233825, 237065, 250025, 253265, 275945, 279185, 282425, 298625, 301865, 305105, 318065, 324545, 327785] : List ℕ)) :
    OeisA249609.isEvil ((2^a).choose 15) = true := by
  let ds : List (Bool × ℕ) := [(false, 0), (false, 87178291200), (true, 266290166528), (false, 392156797823), (true, 238766553488), (false, 159721605679), (true, 493092447128), (false, 14409322927), (true, 547074360113), (false, 368411614), (true, 549718501613), (false, 2749746), (true, 549755670563), (false, 5004), (true, 549755813783), (false, 0)]
  refine (periodic_column (k := 15) (t := 39) (l := 170100) (d := 638512875) (z := 11)
    (ds := ds) ha (by decide) (by decide +kernel) ?_ ?_ (by decide)).2 ?_
  · dsimp only [ds]; decide
  · intro w
    rw [pow_add 2 w 39]
    exact falling15 (2^w) (2^39) (by positivity) (by decide)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr
  · rw [show (a-39) % (170100+170100) + 39 = 7025 by omega]
    exact parity15_7025
  · rw [show (a-39) % (170100+170100) + 39 = 23225 by omega]
    exact parity15_23225
  · rw [show (a-39) % (170100+170100) + 39 = 45905 by omega]
    exact parity15_45905
  · rw [show (a-39) % (170100+170100) + 39 = 52385 by omega]
    exact parity15_52385
  · rw [show (a-39) % (170100+170100) + 39 = 55625 by omega]
    exact parity15_55625
  · rw [show (a-39) % (170100+170100) + 39 = 68585 by omega]
    exact parity15_68585
  · rw [show (a-39) % (170100+170100) + 39 = 71825 by omega]
    exact parity15_71825
  · rw [show (a-39) % (170100+170100) + 39 = 78305 by omega]
    exact parity15_78305
  · rw [show (a-39) % (170100+170100) + 39 = 91265 by omega]
    exact parity15_91265
  · rw [show (a-39) % (170100+170100) + 39 = 100985 by omega]
    exact parity15_100985
  · rw [show (a-39) % (170100+170100) + 39 = 117185 by omega]
    exact parity15_117185
  · rw [show (a-39) % (170100+170100) + 39 = 136625 by omega]
    exact parity15_136625
  · rw [show (a-39) % (170100+170100) + 39 = 143105 by omega]
    exact parity15_143105
  · rw [show (a-39) % (170100+170100) + 39 = 159305 by omega]
    exact parity15_159305
  · rw [show (a-39) % (170100+170100) + 39 = 162545 by omega]
    exact parity15_162545
  · rw [show (a-39) % (170100+170100) + 39 = 181985 by omega]
    exact parity15_181985
  · rw [show (a-39) % (170100+170100) + 39 = 185225 by omega]
    exact parity15_185225
  · rw [show (a-39) % (170100+170100) + 39 = 188465 by omega]
    exact parity15_188465
  · rw [show (a-39) % (170100+170100) + 39 = 204665 by omega]
    exact parity15_204665
  · rw [show (a-39) % (170100+170100) + 39 = 207905 by omega]
    exact parity15_207905
  · rw [show (a-39) % (170100+170100) + 39 = 214385 by omega]
    exact parity15_214385
  · rw [show (a-39) % (170100+170100) + 39 = 227345 by omega]
    exact parity15_227345
  · rw [show (a-39) % (170100+170100) + 39 = 233825 by omega]
    exact parity15_233825
  · rw [show (a-39) % (170100+170100) + 39 = 237065 by omega]
    exact parity15_237065
  · rw [show (a-39) % (170100+170100) + 39 = 250025 by omega]
    exact parity15_250025
  · rw [show (a-39) % (170100+170100) + 39 = 253265 by omega]
    exact parity15_253265
  · rw [show (a-39) % (170100+170100) + 39 = 275945 by omega]
    exact parity15_275945
  · rw [show (a-39) % (170100+170100) + 39 = 279185 by omega]
    exact parity15_279185
  · rw [show (a-39) % (170100+170100) + 39 = 282425 by omega]
    exact parity15_282425
  · rw [show (a-39) % (170100+170100) + 39 = 298625 by omega]
    exact parity15_298625
  · rw [show (a-39) % (170100+170100) + 39 = 301865 by omega]
    exact parity15_301865
  · rw [show (a-39) % (170100+170100) + 39 = 305105 by omega]
    exact parity15_305105
  · rw [show (a-39) % (170100+170100) + 39 = 318065 by omega]
    exact parity15_318065
  · rw [show (a-39) % (170100+170100) + 39 = 324545 by omega]
    exact parity15_324545
  · rw [show (a-39) % (170100+170100) + 39 = 327785 by omega]
    exact parity15_327785

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

private theorem parity16_545 :
    (Nat.digits 2 ((2^545).descFactorial 16 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 11
  decide +kernel

private theorem parity16_3785 :
    (Nat.digits 2 ((2^3785).descFactorial 16 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 13
  decide +kernel

private theorem parity16_10265 :
    (Nat.digits 2 ((2^10265).descFactorial 16 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 15
  decide +kernel

private theorem parity16_75065 :
    (Nat.digits 2 ((2^75065).descFactorial 16 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 18
  decide +kernel

private theorem parity16_94505 :
    (Nat.digits 2 ((2^94505).descFactorial 16 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 18
  decide +kernel

private theorem parity16_113945 :
    (Nat.digits 2 ((2^113945).descFactorial 16 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 18
  decide +kernel

private theorem parity16_139865 :
    (Nat.digits 2 ((2^139865).descFactorial 16 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity16_146345 :
    (Nat.digits 2 ((2^146345).descFactorial 16 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity16_165785 :
    (Nat.digits 2 ((2^165785).descFactorial 16 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity16_169025 :
    (Nat.digits 2 ((2^169025).descFactorial 16 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity16_191705 :
    (Nat.digits 2 ((2^191705).descFactorial 16 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity16_230585 :
    (Nat.digits 2 ((2^230585).descFactorial 16 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity16_256505 :
    (Nat.digits 2 ((2^256505).descFactorial 16 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity16_272705 :
    (Nat.digits 2 ((2^272705).descFactorial 16 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 20
  decide +kernel

private theorem parity16_321305 :
    (Nat.digits 2 ((2^321305).descFactorial 16 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 20
  decide +kernel

set_option maxHeartbeats 8000000 in
private theorem column16 (a : ℕ) (ha : 43 ≤ a)
    (hr : a % 340200 ∈ ([545, 3785, 10265, 75065, 94505, 113945, 139865, 146345, 165785, 169025, 191705, 230585, 256505, 272705, 321305] : List ℕ)) :
    OeisA249609.isEvil ((2^a).choose 16) = true := by
  let ds : List (Bool × ℕ) := [(false, 0), (true, 7488418654208), (false, 4339163001599), (true, 2630275407488), (false, 5056995703823), (true, 6089279676608), (false, 1009672107079), (true, 8523289811528), (false, 54631129552), (true, 8787885394208), (false, 928095739), (true, 8796014463728), (false, 4899621), (true, 8796092803808), (false, 6579), (true, 8796093022088), (false, 0)]
  refine (periodic_column (k := 16) (t := 43) (l := 170100) (d := 638512875) (z := 15)
    (ds := ds) ha (by decide) (by decide +kernel) ?_ ?_ (by decide)).2 ?_
  · dsimp only [ds]; decide
  · intro w
    rw [pow_add 2 w 43]
    exact falling16 (2^w) (2^43) (by positivity) (by decide)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr
  · rw [show (a-43) % (170100+170100) + 43 = 545 by omega]
    exact parity16_545
  · rw [show (a-43) % (170100+170100) + 43 = 3785 by omega]
    exact parity16_3785
  · rw [show (a-43) % (170100+170100) + 43 = 10265 by omega]
    exact parity16_10265
  · rw [show (a-43) % (170100+170100) + 43 = 75065 by omega]
    exact parity16_75065
  · rw [show (a-43) % (170100+170100) + 43 = 94505 by omega]
    exact parity16_94505
  · rw [show (a-43) % (170100+170100) + 43 = 113945 by omega]
    exact parity16_113945
  · rw [show (a-43) % (170100+170100) + 43 = 139865 by omega]
    exact parity16_139865
  · rw [show (a-43) % (170100+170100) + 43 = 146345 by omega]
    exact parity16_146345
  · rw [show (a-43) % (170100+170100) + 43 = 165785 by omega]
    exact parity16_165785
  · rw [show (a-43) % (170100+170100) + 43 = 169025 by omega]
    exact parity16_169025
  · rw [show (a-43) % (170100+170100) + 43 = 191705 by omega]
    exact parity16_191705
  · rw [show (a-43) % (170100+170100) + 43 = 230585 by omega]
    exact parity16_230585
  · rw [show (a-43) % (170100+170100) + 43 = 256505 by omega]
    exact parity16_256505
  · rw [show (a-43) % (170100+170100) + 43 = 272705 by omega]
    exact parity16_272705
  · rw [show (a-43) % (170100+170100) + 43 = 321305 by omega]
    exact parity16_321305

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

private theorem parity17_26465 :
    (Nat.digits 2 ((2^26465).descFactorial 17 / 10854718875)).count 1 % 2 = 0 := by
  apply fold_certificate 16
  decide +kernel

private theorem parity17_49145 :
    (Nat.digits 2 ((2^49145).descFactorial 17 / 10854718875)).count 1 % 2 = 0 := by
  apply fold_certificate 17
  decide +kernel

private theorem parity17_97745 :
    (Nat.digits 2 ((2^97745).descFactorial 17 / 10854718875)).count 1 % 2 = 0 := by
  apply fold_certificate 18
  decide +kernel

private theorem parity17_211145 :
    (Nat.digits 2 ((2^211145).descFactorial 17 / 10854718875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity17_259745 :
    (Nat.digits 2 ((2^259745).descFactorial 17 / 10854718875)).count 1 % 2 = 0 := by
  apply fold_certificate 20
  decide +kernel

private theorem parity17_366665 :
    (Nat.digits 2 ((2^366665).descFactorial 17 / 10854718875)).count 1 % 2 = 0 := by
  apply fold_certificate 20
  decide +kernel

private theorem parity17_389345 :
    (Nat.digits 2 ((2^389345).descFactorial 17 / 10854718875)).count 1 % 2 = 0 := by
  apply fold_certificate 20
  decide +kernel

private theorem parity17_437945 :
    (Nat.digits 2 ((2^437945).descFactorial 17 / 10854718875)).count 1 % 2 = 0 := by
  apply fold_certificate 20
  decide +kernel

private theorem parity17_551345 :
    (Nat.digits 2 ((2^551345).descFactorial 17 / 10854718875)).count 1 % 2 = 0 := by
  apply fold_certificate 21
  decide +kernel

private theorem parity17_599945 :
    (Nat.digits 2 ((2^599945).descFactorial 17 / 10854718875)).count 1 % 2 = 0 := by
  apply fold_certificate 21
  decide +kernel

set_option maxHeartbeats 8000000 in
private theorem column17 (a : ℕ) (ha : 47 ≤ a)
    (hr : a % 680400 ∈ ([26465, 49145, 97745, 211145, 259745, 366665, 389345, 437945, 551345, 599945] : List ℕ)) :
    OeisA249609.isEvil ((2^a).choose 17) = true := by
  let ds : List (Bool × ℕ) := [(false, 0), (false, 20922789888000), (true, 70003205961728), (false, 102992244837119), (true, 53659739479424), (false, 48366009233423), (true, 121875921296448), (false, 5374523477959), (true, 139590587071800), (false, 185953177552), (true, 140714431195488), (false, 2185031419), (true, 140737331402896), (false, 8394021), (true, 140737488031648), (false, 8499), (true, 140737488355192), (false, 0)]
  refine (periodic_column (k := 17) (t := 47) (l := 340200) (d := 10854718875) (z := 15)
    (ds := ds) ha (by decide) (by decide +kernel) ?_ ?_ (by decide)).2 ?_
  · dsimp only [ds]; decide
  · intro w
    rw [pow_add 2 w 47]
    exact falling17 (2^w) (2^47) (by positivity) (by decide)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with hr | hr | hr | hr | hr | hr | hr | hr | hr | hr
  · rw [show (a-47) % (340200+340200) + 47 = 26465 by omega]
    exact parity17_26465
  · rw [show (a-47) % (340200+340200) + 47 = 49145 by omega]
    exact parity17_49145
  · rw [show (a-47) % (340200+340200) + 47 = 97745 by omega]
    exact parity17_97745
  · rw [show (a-47) % (340200+340200) + 47 = 211145 by omega]
    exact parity17_211145
  · rw [show (a-47) % (340200+340200) + 47 = 259745 by omega]
    exact parity17_259745
  · rw [show (a-47) % (340200+340200) + 47 = 366665 by omega]
    exact parity17_366665
  · rw [show (a-47) % (340200+340200) + 47 = 389345 by omega]
    exact parity17_389345
  · rw [show (a-47) % (340200+340200) + 47 = 437945 by omega]
    exact parity17_437945
  · rw [show (a-47) % (340200+340200) + 47 = 551345 by omega]
    exact parity17_551345
  · rw [show (a-47) % (340200+340200) + 47 = 599945 by omega]
    exact parity17_599945

end Certificates

set_option maxRecDepth 100000 in
private theorem cover : ∀ q : Fin 210,
    (3240*q.val+545) % 22680 ∈ ([13505, 16745, 19985] : List ℕ) ∨
    (3240*q.val+545) % 340200 ∈ ([7025, 23225, 45905, 52385, 55625, 68585, 71825, 78305, 91265, 100985, 117185, 136625, 143105, 159305, 162545, 181985, 185225, 188465, 204665, 207905, 214385, 227345, 233825, 237065, 250025, 253265, 275945, 279185, 282425, 298625, 301865, 305105, 318065, 324545, 327785] : List ℕ) ∨
    (3240*q.val+545) % 340200 ∈ ([545, 3785, 10265, 75065, 94505, 113945, 139865, 146345, 165785, 169025, 191705, 230585, 256505, 272705, 321305] : List ℕ) ∨
    (3240*q.val+545) % 680400 ∈ ([26465, 49145, 97745, 211145, 259745, 366665, 389345, 437945, 551345, 599945] : List ℕ) ∨
    q.val % 105 ∈ ([9, 10] : List ℕ) ∨
    q.val % 105 ∈ ([37, 38] : List ℕ) ∨
    q.val % 105 ∈ ([91] : List ℕ) := by decide +kernel

theorem main : H1 → H2 → H3 → OMA.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H1_R1.H2 := by
  intro h1 h2 h3 q
  have reduceMod (d : ℕ) (hd : d ∣ 680400) :
      (3240*(q%210)+545)%d = (3240*q+545)%d :=
    (((Nat.mod_modEq q 210).mul_left' 3240).of_dvd hd).add_right 545
  have cases := cover ⟨q%210, Nat.mod_lt _ (by decide)⟩
  dsimp only at cases
  rw [reduceMod 22680 (by decide), reduceMod 340200 (by decide), reduceMod 680400 (by decide)] at cases
  rw [Nat.mod_mod_of_dvd q (by decide : 105 ∣ 210)] at cases
  have hbig : 32 ≤ 2^(3240*q+545) :=
    le_trans (by decide : 32 ≤ 2^5) (Nat.pow_le_pow_right (by decide) (by omega))
  rcases cases with h | h | h | h | h | h | h
  · exact witness _ 14 (by decide) (by omega) (column14 _ (by omega) h)
  · exact witness _ 15 (by decide) (by omega) (column15 _ (by omega) h)
  · exact witness _ 16 (by decide) (by omega) (column16 _ (by omega) h)
  · exact witness _ 17 (by decide) (by omega) (column17 _ (by omega) h)
  · exact h1 q h
  · exact h2 q h
  · exact h3 q h

end OMA.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H1_R1_H2_R1
