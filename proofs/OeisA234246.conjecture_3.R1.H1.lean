import OMAReductions.R_OeisA234246_conjecture_3_R1
import Mathlib

/- The closest square of opposite parity leaves an odd gap d at most 4095.
For d ≥ 7 a table supplies distinct primes p + q = d + 1. Then p*q has
cototient d. Where p*q is too large, the short table below supplies a
different square and totient argument. All entries are checked in Lean. -/

namespace OMA.SunFinite

abbrev Good (n : ℕ) : Prop :=
  ∃ k, 0 < k ∧ k < n ∧ IsSquare (k + (n - k).totient)

lemma mul_phi {a b x y : ℕ} (h : a.Coprime b) (ha : a.totient = x) (hb : b.totient = y) :
    (a * b).totient = x * y := by rw [Nat.totient_mul h, ha, hb]

lemma phi10 : Nat.totient 10 = 4 :=
  (mul_phi (a := 2) (b := 5) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0) (Nat.totient_prime_pow_succ (p := 5) (by norm_num) 0))

lemma phi12 : Nat.totient 12 = 4 :=
  (mul_phi (a := 4) (b := 3) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 1) (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0))

lemma phi18 : Nat.totient 18 = 6 :=
  (mul_phi (a := 2) (b := 9) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0) (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 1))

lemma phi24 : Nat.totient 24 = 8 :=
  (mul_phi (a := 8) (b := 3) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 2) (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0))

lemma phi26 : Nat.totient 26 = 12 :=
  (mul_phi (a := 2) (b := 13) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0) (Nat.totient_prime_pow_succ (p := 13) (by norm_num) 0))

lemma phi30 : Nat.totient 30 = 8 :=
  (mul_phi (a := 2) (b := 15) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0) (mul_phi (a := 3) (b := 5) (by decide) (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0) (Nat.totient_prime_pow_succ (p := 5) (by norm_num) 0)))

lemma phi34 : Nat.totient 34 = 16 :=
  (mul_phi (a := 2) (b := 17) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0) (Nat.totient_prime_pow_succ (p := 17) (by norm_num) 0))

lemma phi36 : Nat.totient 36 = 12 :=
  (mul_phi (a := 4) (b := 9) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 1) (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 1))

lemma phi38 : Nat.totient 38 = 18 :=
  (mul_phi (a := 2) (b := 19) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0) (Nat.totient_prime_pow_succ (p := 19) (by norm_num) 0))

lemma phi42 : Nat.totient 42 = 12 :=
  (mul_phi (a := 2) (b := 21) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0) (mul_phi (a := 3) (b := 7) (by decide) (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0) (Nat.totient_prime_pow_succ (p := 7) (by norm_num) 0)))

lemma phi48 : Nat.totient 48 = 16 :=
  (mul_phi (a := 16) (b := 3) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 3) (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0))

lemma phi52 : Nat.totient 52 = 24 :=
  (mul_phi (a := 4) (b := 13) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 1) (Nat.totient_prime_pow_succ (p := 13) (by norm_num) 0))

lemma phi54 : Nat.totient 54 = 18 :=
  (mul_phi (a := 2) (b := 27) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0) (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 2))

lemma phi60 : Nat.totient 60 = 16 :=
  (mul_phi (a := 4) (b := 15) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 1) (mul_phi (a := 3) (b := 5) (by decide) (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0) (Nat.totient_prime_pow_succ (p := 5) (by norm_num) 0)))

lemma phi63 : Nat.totient 63 = 36 :=
  (mul_phi (a := 9) (b := 7) (by decide) (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 1) (Nat.totient_prime_pow_succ (p := 7) (by norm_num) 0))

lemma phi66 : Nat.totient 66 = 20 :=
  (mul_phi (a := 2) (b := 33) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0) (mul_phi (a := 3) (b := 11) (by decide) (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0) (Nat.totient_prime_pow_succ (p := 11) (by norm_num) 0)))

lemma phi72 : Nat.totient 72 = 24 :=
  (mul_phi (a := 8) (b := 9) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 2) (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 1))

lemma phi74 : Nat.totient 74 = 36 :=
  (mul_phi (a := 2) (b := 37) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0) (Nat.totient_prime_pow_succ (p := 37) (by norm_num) 0))

lemma phi76 : Nat.totient 76 = 36 :=
  (mul_phi (a := 4) (b := 19) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 1) (Nat.totient_prime_pow_succ (p := 19) (by norm_num) 0))

lemma phi78 : Nat.totient 78 = 24 :=
  (mul_phi (a := 2) (b := 39) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0) (mul_phi (a := 3) (b := 13) (by decide) (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0) (Nat.totient_prime_pow_succ (p := 13) (by norm_num) 0)))

lemma phi82 : Nat.totient 82 = 40 :=
  (mul_phi (a := 2) (b := 41) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0) (Nat.totient_prime_pow_succ (p := 41) (by norm_num) 0))

lemma phi84 : Nat.totient 84 = 24 :=
  (mul_phi (a := 4) (b := 21) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 1) (mul_phi (a := 3) (b := 7) (by decide) (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0) (Nat.totient_prime_pow_succ (p := 7) (by norm_num) 0)))

lemma phi96 : Nat.totient 96 = 32 :=
  (mul_phi (a := 32) (b := 3) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 4) (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0))

lemma phi98 : Nat.totient 98 = 42 :=
  (mul_phi (a := 2) (b := 49) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0) (Nat.totient_prime_pow_succ (p := 7) (by norm_num) 1))

lemma phi114 : Nat.totient 114 = 36 :=
  (mul_phi (a := 2) (b := 57) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0) (mul_phi (a := 3) (b := 19) (by decide) (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0) (Nat.totient_prime_pow_succ (p := 19) (by norm_num) 0)))

lemma phi120 : Nat.totient 120 = 32 :=
  (mul_phi (a := 8) (b := 15) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 2) (mul_phi (a := 3) (b := 5) (by decide) (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0) (Nat.totient_prime_pow_succ (p := 5) (by norm_num) 0)))

lemma phi122 : Nat.totient 122 = 60 :=
  (mul_phi (a := 2) (b := 61) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0) (Nat.totient_prime_pow_succ (p := 61) (by norm_num) 0))

lemma phi126 : Nat.totient 126 = 36 :=
  (mul_phi (a := 2) (b := 63) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0) (mul_phi (a := 9) (b := 7) (by decide) (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 1) (Nat.totient_prime_pow_succ (p := 7) (by norm_num) 0)))

lemma phi132 : Nat.totient 132 = 40 :=
  (mul_phi (a := 4) (b := 33) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 1) (mul_phi (a := 3) (b := 11) (by decide) (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0) (Nat.totient_prime_pow_succ (p := 11) (by norm_num) 0)))

lemma phi138 : Nat.totient 138 = 44 :=
  (mul_phi (a := 2) (b := 69) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0) (mul_phi (a := 3) (b := 23) (by decide) (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0) (Nat.totient_prime_pow_succ (p := 23) (by norm_num) 0)))

lemma phi144 : Nat.totient 144 = 48 :=
  (mul_phi (a := 16) (b := 9) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 3) (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 1))

lemma phi146 : Nat.totient 146 = 72 :=
  (mul_phi (a := 2) (b := 73) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0) (Nat.totient_prime_pow_succ (p := 73) (by norm_num) 0))

lemma phi150 : Nat.totient 150 = 40 :=
  (mul_phi (a := 2) (b := 75) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0) (mul_phi (a := 3) (b := 25) (by decide) (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0) (Nat.totient_prime_pow_succ (p := 5) (by norm_num) 1)))

lemma phi156 : Nat.totient 156 = 48 :=
  (mul_phi (a := 4) (b := 39) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 1) (mul_phi (a := 3) (b := 13) (by decide) (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0) (Nat.totient_prime_pow_succ (p := 13) (by norm_num) 0)))

lemma phi170 : Nat.totient 170 = 64 :=
  (mul_phi (a := 2) (b := 85) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0) (mul_phi (a := 5) (b := 17) (by decide) (Nat.totient_prime_pow_succ (p := 5) (by norm_num) 0) (Nat.totient_prime_pow_succ (p := 17) (by norm_num) 0)))

lemma phi180 : Nat.totient 180 = 48 :=
  (mul_phi (a := 4) (b := 45) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 1) (mul_phi (a := 9) (b := 5) (by decide) (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 1) (Nat.totient_prime_pow_succ (p := 5) (by norm_num) 0)))

lemma phi186 : Nat.totient 186 = 60 :=
  (mul_phi (a := 2) (b := 93) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0) (mul_phi (a := 3) (b := 31) (by decide) (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0) (Nat.totient_prime_pow_succ (p := 31) (by norm_num) 0)))

lemma phi192 : Nat.totient 192 = 64 :=
  (mul_phi (a := 64) (b := 3) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 5) (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0))

lemma phi194 : Nat.totient 194 = 96 :=
  (mul_phi (a := 2) (b := 97) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0) (Nat.totient_prime_pow_succ (p := 97) (by norm_num) 0))

lemma phi198 : Nat.totient 198 = 60 :=
  (mul_phi (a := 2) (b := 99) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0) (mul_phi (a := 9) (b := 11) (by decide) (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 1) (Nat.totient_prime_pow_succ (p := 11) (by norm_num) 0)))

lemma phi202 : Nat.totient 202 = 100 :=
  (mul_phi (a := 2) (b := 101) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0) (Nat.totient_prime_pow_succ (p := 101) (by norm_num) 0))

lemma phi204 : Nat.totient 204 = 64 :=
  (mul_phi (a := 4) (b := 51) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 1) (mul_phi (a := 3) (b := 17) (by decide) (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0) (Nat.totient_prime_pow_succ (p := 17) (by norm_num) 0)))

lemma phi206 : Nat.totient 206 = 102 :=
  (mul_phi (a := 2) (b := 103) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0) (Nat.totient_prime_pow_succ (p := 103) (by norm_num) 0))

lemma phi210 : Nat.totient 210 = 48 :=
  (mul_phi (a := 2) (b := 105) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0) (mul_phi (a := 3) (b := 35) (by decide) (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0) (mul_phi (a := 5) (b := 7) (by decide) (Nat.totient_prime_pow_succ (p := 5) (by norm_num) 0) (Nat.totient_prime_pow_succ (p := 7) (by norm_num) 0))))

lemma phi216 : Nat.totient 216 = 72 :=
  (mul_phi (a := 8) (b := 27) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 2) (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 2))

lemma phi222 : Nat.totient 222 = 72 :=
  (mul_phi (a := 2) (b := 111) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0) (mul_phi (a := 3) (b := 37) (by decide) (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0) (Nat.totient_prime_pow_succ (p := 37) (by norm_num) 0)))

lemma phi228 : Nat.totient 228 = 72 :=
  (mul_phi (a := 4) (b := 57) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 1) (mul_phi (a := 3) (b := 19) (by decide) (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0) (Nat.totient_prime_pow_succ (p := 19) (by norm_num) 0)))

lemma phi230 : Nat.totient 230 = 88 :=
  (mul_phi (a := 2) (b := 115) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0) (mul_phi (a := 5) (b := 23) (by decide) (Nat.totient_prime_pow_succ (p := 5) (by norm_num) 0) (Nat.totient_prime_pow_succ (p := 23) (by norm_num) 0)))

lemma phi246 : Nat.totient 246 = 80 :=
  (mul_phi (a := 2) (b := 123) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0) (mul_phi (a := 3) (b := 41) (by decide) (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0) (Nat.totient_prime_pow_succ (p := 41) (by norm_num) 0)))

lemma phi255 : Nat.totient 255 = 128 :=
  (mul_phi (a := 3) (b := 85) (by decide) (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0) (mul_phi (a := 5) (b := 17) (by decide) (Nat.totient_prime_pow_succ (p := 5) (by norm_num) 0) (Nat.totient_prime_pow_succ (p := 17) (by norm_num) 0)))

lemma phi260 : Nat.totient 260 = 96 :=
  (mul_phi (a := 4) (b := 65) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 1) (mul_phi (a := 5) (b := 13) (by decide) (Nat.totient_prime_pow_succ (p := 5) (by norm_num) 0) (Nat.totient_prime_pow_succ (p := 13) (by norm_num) 0)))

lemma phi266 : Nat.totient 266 = 108 :=
  (mul_phi (a := 2) (b := 133) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0) (mul_phi (a := 7) (b := 19) (by decide) (Nat.totient_prime_pow_succ (p := 7) (by norm_num) 0) (Nat.totient_prime_pow_succ (p := 19) (by norm_num) 0)))

lemma phi268 : Nat.totient 268 = 132 :=
  (mul_phi (a := 4) (b := 67) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 1) (Nat.totient_prime_pow_succ (p := 67) (by norm_num) 0))

lemma phi276 : Nat.totient 276 = 88 :=
  (mul_phi (a := 4) (b := 69) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 1) (mul_phi (a := 3) (b := 23) (by decide) (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0) (Nat.totient_prime_pow_succ (p := 23) (by norm_num) 0)))

lemma phi282 : Nat.totient 282 = 92 :=
  (mul_phi (a := 2) (b := 141) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0) (mul_phi (a := 3) (b := 47) (by decide) (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0) (Nat.totient_prime_pow_succ (p := 47) (by norm_num) 0)))

lemma phi292 : Nat.totient 292 = 144 :=
  (mul_phi (a := 4) (b := 73) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 1) (Nat.totient_prime_pow_succ (p := 73) (by norm_num) 0))

lemma phi296 : Nat.totient 296 = 144 :=
  (mul_phi (a := 8) (b := 37) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 2) (Nat.totient_prime_pow_succ (p := 37) (by norm_num) 0))

lemma phi304 : Nat.totient 304 = 144 :=
  (mul_phi (a := 16) (b := 19) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 3) (Nat.totient_prime_pow_succ (p := 19) (by norm_num) 0))

lemma phi328 : Nat.totient 328 = 160 :=
  (mul_phi (a := 8) (b := 41) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 2) (Nat.totient_prime_pow_succ (p := 41) (by norm_num) 0))

lemma phi330 : Nat.totient 330 = 80 :=
  (mul_phi (a := 2) (b := 165) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0) (mul_phi (a := 3) (b := 55) (by decide) (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0) (mul_phi (a := 5) (b := 11) (by decide) (Nat.totient_prime_pow_succ (p := 5) (by norm_num) 0) (Nat.totient_prime_pow_succ (p := 11) (by norm_num) 0))))

lemma phi338 : Nat.totient 338 = 156 :=
  (mul_phi (a := 2) (b := 169) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0) (Nat.totient_prime_pow_succ (p := 13) (by norm_num) 1))

lemma phi360 : Nat.totient 360 = 96 :=
  (mul_phi (a := 8) (b := 45) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 2) (mul_phi (a := 9) (b := 5) (by decide) (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 1) (Nat.totient_prime_pow_succ (p := 5) (by norm_num) 0)))

lemma phi372 : Nat.totient 372 = 120 :=
  (mul_phi (a := 4) (b := 93) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 1) (mul_phi (a := 3) (b := 31) (by decide) (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0) (Nat.totient_prime_pow_succ (p := 31) (by norm_num) 0)))

lemma phi378 : Nat.totient 378 = 108 :=
  (mul_phi (a := 2) (b := 189) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0) (mul_phi (a := 27) (b := 7) (by decide) (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 2) (Nat.totient_prime_pow_succ (p := 7) (by norm_num) 0)))

lemma phi384 : Nat.totient 384 = 128 :=
  (mul_phi (a := 128) (b := 3) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 6) (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0))

lemma phi388 : Nat.totient 388 = 192 :=
  (mul_phi (a := 4) (b := 97) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 1) (Nat.totient_prime_pow_succ (p := 97) (by norm_num) 0))

lemma phi396 : Nat.totient 396 = 120 :=
  (mul_phi (a := 4) (b := 99) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 1) (mul_phi (a := 9) (b := 11) (by decide) (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 1) (Nat.totient_prime_pow_succ (p := 11) (by norm_num) 0)))

lemma phi430 : Nat.totient 430 = 168 :=
  (mul_phi (a := 2) (b := 215) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0) (mul_phi (a := 5) (b := 43) (by decide) (Nat.totient_prime_pow_succ (p := 5) (by norm_num) 0) (Nat.totient_prime_pow_succ (p := 43) (by norm_num) 0)))

lemma phi434 : Nat.totient 434 = 180 :=
  (mul_phi (a := 2) (b := 217) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0) (mul_phi (a := 7) (b := 31) (by decide) (Nat.totient_prime_pow_succ (p := 7) (by norm_num) 0) (Nat.totient_prime_pow_succ (p := 31) (by norm_num) 0)))

lemma phi483 : Nat.totient 483 = 264 :=
  (mul_phi (a := 3) (b := 161) (by decide) (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0) (mul_phi (a := 7) (b := 23) (by decide) (Nat.totient_prime_pow_succ (p := 7) (by norm_num) 0) (Nat.totient_prime_pow_succ (p := 23) (by norm_num) 0)))

lemma phi494 : Nat.totient 494 = 216 :=
  (mul_phi (a := 2) (b := 247) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0) (mul_phi (a := 13) (b := 19) (by decide) (Nat.totient_prime_pow_succ (p := 13) (by norm_num) 0) (Nat.totient_prime_pow_succ (p := 19) (by norm_num) 0)))

lemma phi514 : Nat.totient 514 = 256 :=
  (mul_phi (a := 2) (b := 257) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0) (Nat.totient_prime_pow_succ (p := 257) (by norm_num) 0))

lemma phi536 : Nat.totient 536 = 264 :=
  (mul_phi (a := 8) (b := 67) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 2) (Nat.totient_prime_pow_succ (p := 67) (by norm_num) 0))

lemma phi578 : Nat.totient 578 = 272 :=
  (mul_phi (a := 2) (b := 289) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0) (Nat.totient_prime_pow_succ (p := 17) (by norm_num) 1))

lemma phi630 : Nat.totient 630 = 144 :=
  (mul_phi (a := 2) (b := 315) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0) (mul_phi (a := 9) (b := 35) (by decide) (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 1) (mul_phi (a := 5) (b := 7) (by decide) (Nat.totient_prime_pow_succ (p := 5) (by norm_num) 0) (Nat.totient_prime_pow_succ (p := 7) (by norm_num) 0))))

lemma phi672 : Nat.totient 672 = 192 :=
  (mul_phi (a := 32) (b := 21) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 4) (mul_phi (a := 3) (b := 7) (by decide) (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0) (Nat.totient_prime_pow_succ (p := 7) (by norm_num) 0)))

lemma phi708 : Nat.totient 708 = 232 :=
  (mul_phi (a := 4) (b := 177) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 1) (mul_phi (a := 3) (b := 59) (by decide) (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0) (Nat.totient_prime_pow_succ (p := 59) (by norm_num) 0)))

lemma phi732 : Nat.totient 732 = 240 :=
  (mul_phi (a := 4) (b := 183) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 1) (mul_phi (a := 3) (b := 61) (by decide) (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0) (Nat.totient_prime_pow_succ (p := 61) (by norm_num) 0)))

lemma phi777 : Nat.totient 777 = 432 :=
  (mul_phi (a := 3) (b := 259) (by decide) (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0) (mul_phi (a := 7) (b := 37) (by decide) (Nat.totient_prime_pow_succ (p := 7) (by norm_num) 0) (Nat.totient_prime_pow_succ (p := 37) (by norm_num) 0)))

lemma phi790 : Nat.totient 790 = 312 :=
  (mul_phi (a := 2) (b := 395) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0) (mul_phi (a := 5) (b := 79) (by decide) (Nat.totient_prime_pow_succ (p := 5) (by norm_num) 0) (Nat.totient_prime_pow_succ (p := 79) (by norm_num) 0)))

lemma phi854 : Nat.totient 854 = 360 :=
  (mul_phi (a := 2) (b := 427) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0) (mul_phi (a := 7) (b := 61) (by decide) (Nat.totient_prime_pow_succ (p := 7) (by norm_num) 0) (Nat.totient_prime_pow_succ (p := 61) (by norm_num) 0)))

lemma phi914 : Nat.totient 914 = 456 :=
  (mul_phi (a := 2) (b := 457) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0) (Nat.totient_prime_pow_succ (p := 457) (by norm_num) 0))

lemma phi964 : Nat.totient 964 = 480 :=
  (mul_phi (a := 4) (b := 241) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 1) (Nat.totient_prime_pow_succ (p := 241) (by norm_num) 0))

lemma phi974 : Nat.totient 974 = 486 :=
  (mul_phi (a := 2) (b := 487) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0) (Nat.totient_prime_pow_succ (p := 487) (by norm_num) 0))

lemma phi976 : Nat.totient 976 = 480 :=
  (mul_phi (a := 16) (b := 61) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 3) (Nat.totient_prime_pow_succ (p := 61) (by norm_num) 0))

lemma phi1176 : Nat.totient 1176 = 336 :=
  (mul_phi (a := 8) (b := 147) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 2) (mul_phi (a := 3) (b := 49) (by decide) (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0) (Nat.totient_prime_pow_succ (p := 7) (by norm_num) 1)))

lemma phi1360 : Nat.totient 1360 = 512 :=
  (mul_phi (a := 16) (b := 85) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 3) (mul_phi (a := 5) (b := 17) (by decide) (Nat.totient_prime_pow_succ (p := 5) (by norm_num) 0) (Nat.totient_prime_pow_succ (p := 17) (by norm_num) 0)))

lemma phi1370 : Nat.totient 1370 = 544 :=
  (mul_phi (a := 2) (b := 685) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0) (mul_phi (a := 5) (b := 137) (by decide) (Nat.totient_prime_pow_succ (p := 5) (by norm_num) 0) (Nat.totient_prime_pow_succ (p := 137) (by norm_num) 0)))

lemma phi1610 : Nat.totient 1610 = 528 :=
  (mul_phi (a := 2) (b := 805) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0) (mul_phi (a := 5) (b := 161) (by decide) (Nat.totient_prime_pow_succ (p := 5) (by norm_num) 0) (mul_phi (a := 7) (b := 23) (by decide) (Nat.totient_prime_pow_succ (p := 7) (by norm_num) 0) (Nat.totient_prime_pow_succ (p := 23) (by norm_num) 0))))

lemma phi2675 : Nat.totient 2675 = 2120 :=
  (mul_phi (a := 25) (b := 107) (by decide) (Nat.totient_prime_pow_succ (p := 5) (by norm_num) 1) (Nat.totient_prime_pow_succ (p := 107) (by norm_num) 0))

lemma phi2978 : Nat.totient 2978 = 1488 :=
  (mul_phi (a := 2) (b := 1489) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0) (Nat.totient_prime_pow_succ (p := 1489) (by norm_num) 0))

lemma phi7378 : Nat.totient 7378 = 2880 :=
  (mul_phi (a := 2) (b := 3689) (by decide) (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0) (mul_phi (a := 7) (b := 527) (by decide) (Nat.totient_prime_pow_succ (p := 7) (by norm_num) 0) (mul_phi (a := 17) (b := 31) (by decide) (Nat.totient_prime_pow_succ (p := 17) (by norm_num) 0) (Nat.totient_prime_pow_succ (p := 31) (by norm_num) 0))))

structure CertifiedCase where
  number : ℕ
  valid : Good number

def makeCase (n r m : ℕ) {t : ℕ} (hphi : m.totient = t)
    (h : 0 < m ∧ m < n ∧ n + t = r * r + m) : CertifiedCase :=
  ⟨n, OMA.R_OeisA234246_conjecture_3_R1.witness h.1 h.2.1 (r := r)
    (by rw [hphi]; exact h.2.2)⟩

/- Each entry supplies a square root, a totient argument and its checked factorization. -/
set_option maxRecDepth 4096 in
def exceptions : List CertifiedCase :=
  [makeCase 61 7 18 phi18 (by decide),
   makeCase 63 7 26 phi26 (by decide),
   makeCase 72 8 12 phi12 (by decide),
   makeCase 76 8 18 phi18 (by decide),
   makeCase 78 8 26 phi26 (by decide),
   makeCase 80 8 24 phi24 (by decide),
   makeCase 87 9 10 phi10 (by decide),
   makeCase 91 8 63 phi63 (by decide),
   makeCase 93 9 18 phi18 (by decide),
   makeCase 99 9 34 phi34 (by decide),
   makeCase 108 10 12 phi12 (by decide),
   makeCase 110 8 66 phi66 (by decide),
   makeCase 116 10 24 phi24 (by decide),
   makeCase 118 10 34 phi34 (by decide),
   makeCase 129 11 12 phi12 (by decide),
   makeCase 135 11 26 phi26 (by decide),
   makeCase 137 11 24 phi24 (by decide),
   makeCase 141 11 38 phi38 (by decide),
   makeCase 150 12 10 phi10 (by decide),
   makeCase 158 12 26 phi26 (by decide),
   makeCase 162 12 34 phi34 (by decide),
   makeCase 168 12 36 phi36 (by decide),
   makeCase 181 13 18 phi18 (by decide),
   makeCase 185 13 24 phi24 (by decide),
   makeCase 191 13 30 phi30 (by decide),
   makeCase 195 11 146 phi146 (by decide),
   makeCase 206 12 122 phi122 (by decide),
   makeCase 220 14 36 phi36 (by decide),
   makeCase 222 12 114 phi114 (by decide),
   makeCase 249 15 36 phi36 (by decide),
   makeCase 253 15 52 phi52 (by decide),
   makeCase 255 15 42 phi42 (by decide),
   makeCase 278 16 30 phi30 (by decide),
   makeCase 284 16 52 phi52 (by decide),
   makeCase 309 17 38 phi38 (by decide),
   makeCase 315 15 126 phi126 (by decide),
   makeCase 323 15 194 phi194 (by decide),
   makeCase 348 18 36 phi36 (by decide),
   makeCase 356 18 48 phi48 (by decide),
   makeCase 391 19 42 phi42 (by decide),
   makeCase 440 20 76 phi76 (by decide),
   makeCase 479 21 74 phi74 (by decide),
   makeCase 573 23 60 phi60 (by decide),
   makeCase 673 25 72 phi72 (by decide),
   makeCase 722 26 66 phi66 (by decide),
   makeCase 773 27 60 phi60 (by decide),
   makeCase 826 28 82 phi82 (by decide),
   makeCase 881 29 76 phi76 (by decide),
   makeCase 938 30 74 phi74 (by decide),
   makeCase 997 31 54 phi54 (by decide),
   makeCase 1021 31 84 phi84 (by decide),
   makeCase 1023 31 122 phi122 (by decide),
   makeCase 1058 30 266 phi266 (by decide),
   makeCase 1082 30 338 phi338 (by decide),
   makeCase 1084 32 84 phi84 (by decide),
   makeCase 1086 32 122 phi122 (by decide),
   makeCase 1088 32 96 phi96 (by decide),
   makeCase 1121 33 48 phi48 (by decide),
   makeCase 1145 33 98 phi98 (by decide),
   makeCase 1147 29 578 phi578 (by decide),
   makeCase 1149 33 84 phi84 (by decide),
   makeCase 1151 33 122 phi122 (by decide),
   makeCase 1186 34 42 phi42 (by decide),
   makeCase 1210 34 78 phi78 (by decide),
   makeCase 1212 34 98 phi98 (by decide),
   makeCase 1214 32 282 phi282 (by decide),
   makeCase 1216 34 84 phi84 (by decide),
   makeCase 1253 35 52 phi52 (by decide),
   makeCase 1277 33 276 phi276 (by decide),
   makeCase 1281 35 98 phi98 (by decide),
   makeCase 1283 34 255 phi255 (by decide),
   makeCase 1322 34 246 phi246 (by decide),
   makeCase 1346 34 282 phi282 (by decide),
   makeCase 1350 36 78 phi78 (by decide),
   makeCase 1352 36 98 phi98 (by decide),
   makeCase 1393 37 36 phi36 (by decide),
   makeCase 1417 37 72 phi72 (by decide),
   makeCase 1421 35 388 phi388 (by decide),
   makeCase 1423 37 78 phi78 (by decide),
   makeCase 1443 37 146 phi146 (by decide),
   makeCase 1466 38 30 phi30 (by decide),
   makeCase 1496 37 255 phi255 (by decide),
   makeCase 1518 38 146 phi146 (by decide),
   makeCase 1571 38 255 phi255 (by decide),
   makeCase 1648 40 72 phi72 (by decide),
   makeCase 1727 41 66 phi66 (by decide),
   makeCase 1808 42 60 phi60 (by decide),
   makeCase 1891 43 82 phi82 (by decide),
   makeCase 1976 44 76 phi76 (by decide),
   makeCase 2063 45 74 phi74 (by decide),
   makeCase 3135 55 150 phi150 (by decide),
   makeCase 3244 56 156 phi156 (by decide),
   makeCase 3355 57 170 phi170 (by decide),
   makeCase 3468 58 206 phi206 (by decide),
   makeCase 3583 59 202 phi202 (by decide),
   makeCase 3700 59 483 phi483 (by decide),
   makeCase 3819 61 194 phi194 (by decide),
   makeCase 3940 62 144 phi144 (by decide),
   makeCase 4063 63 138 phi138 (by decide),
   makeCase 4188 64 132 phi132 (by decide),
   makeCase 4315 65 126 phi126 (by decide),
   makeCase 4444 66 120 phi120 (by decide),
   makeCase 6083 75 914 phi914 (by decide),
   makeCase 6236 78 296 phi296 (by decide),
   makeCase 6391 79 222 phi222 (by decide),
   makeCase 6548 80 292 phi292 (by decide),
   makeCase 6707 75 1610 phi1610 (by decide),
   makeCase 6868 82 216 phi216 (by decide),
   makeCase 7031 83 230 phi230 (by decide),
   makeCase 7196 84 204 phi204 (by decide),
   makeCase 7363 85 198 phi198 (by decide),
   makeCase 7532 86 268 phi268 (by decide),
   makeCase 7703 85 790 phi790 (by decide),
   makeCase 7741 86 777 phi777 (by decide),
   makeCase 7876 88 180 phi180 (by decide),
   makeCase 7914 87 777 phi777 (by decide),
   makeCase 8051 85 1370 phi1370 (by decide),
   makeCase 8089 89 328 phi328 (by decide),
   makeCase 8228 90 192 phi192 (by decide),
   makeCase 8266 90 246 phi246 (by decide),
   makeCase 8407 91 186 phi186 (by decide),
   makeCase 8445 91 260 phi260 (by decide),
   makeCase 8626 92 210 phi210 (by decide),
   makeCase 8809 93 304 phi304 (by decide),
   makeCase 8994 94 266 phi266 (by decide),
   makeCase 9181 95 228 phi228 (by decide),
   makeCase 19599 139 494 phi494 (by decide),
   makeCase 19876 140 396 phi396 (by decide),
   makeCase 20155 140 2675 phi2675 (by decide),
   makeCase 20436 142 536 phi536 (by decide),
   makeCase 20719 143 378 phi378 (by decide),
   makeCase 21004 142 1176 phi1176 (by decide),
   makeCase 21291 144 2675 phi2675 (by decide),
   makeCase 21580 146 360 phi360 (by decide),
   makeCase 21871 147 430 phi430 (by decide),
   makeCase 22164 146 1360 phi1360 (by decide),
   makeCase 22459 149 514 phi514 (by decide),
   makeCase 22756 150 384 phi384 (by decide),
   makeCase 23055 151 434 phi434 (by decide),
   makeCase 23356 152 372 phi372 (by decide),
   makeCase 23659 153 330 phi330 (by decide),
   makeCase 62000 248 976 phi976 (by decide),
   makeCase 62495 249 854 phi854 (by decide),
   makeCase 62992 250 732 phi732 (by decide),
   makeCase 63491 249 2978 phi2978 (by decide),
   makeCase 63992 252 974 phi974 (by decide),
   makeCase 64495 253 630 phi630 (by decide),
   makeCase 65000 254 964 phi964 (by decide),
   makeCase 65507 247 7378 phi7378 (by decide),
   makeCase 66016 256 672 phi672 (by decide),
   makeCase 66527 257 790 phi790 (by decide),
   makeCase 67040 258 708 phi708 (by decide)]

def exceptionOK (n : ℕ) : Bool :=
  exceptions.any fun v => decide (v.number = n)

lemma exception_sound {n : ℕ} (h : exceptionOK n = true) : Good n := by
  unfold exceptionOK at h
  obtain ⟨v, _, hv⟩ := List.any_eq_true.mp h
  have he : v.number = n := of_decide_eq_true hv
  exact he ▸ v.valid

/-- Roots at least d/4+64 are handled by a single checked inequality. -/
def checkRoots (d m : ℕ) : Bool :=
  let b := d / 4
  decide (m < b * b + d) ||
    (decide (m < (b + 64) * (b + 64) + d) &&
      (List.range 64).all fun i =>
        let r := b + i
        let n := r * r + d
        decide (n < 60 ∨ m < n) || exceptionOK n)

lemma roots_sound {d m r : ℕ} (hc : checkRoots d m = true)
    (hd : d ≤ 4 * r + 3) (hn : 60 ≤ r * r + d) :
    m < r * r + d ∨ Good (r * r + d) := by
  let b := d / 4
  have hbr : b ≤ r := by dsimp [b]; omega
  unfold checkRoots at hc
  rcases Bool.or_eq_true_iff.mp hc with hlow | hrest
  · have hl : m < b * b + d := of_decide_eq_true hlow
    have hsq := Nat.mul_le_mul hbr hbr
    exact Or.inl (by omega)
  obtain ⟨hbound, hscan⟩ := Bool.and_eq_true_iff.mp hrest
  by_cases hr : b + 64 ≤ r
  · have hl : m < (b + 64) * (b + 64) + d := of_decide_eq_true hbound
    have hsq := Nat.mul_le_mul hr hr
    exact Or.inl (by omega)
  have hi : r - b ∈ List.range 64 := List.mem_range.mpr (by omega)
  have hw := List.all_eq_true.mp hscan _ hi
  change (decide ((b + (r - b)) * (b + (r - b)) + d < 60 ∨
    m < (b + (r - b)) * (b + (r - b)) + d) ||
    exceptionOK ((b + (r - b)) * (b + (r - b)) + d)) = true at hw
  rw [show b + (r - b) = r by omega] at hw
  rcases Bool.or_eq_true_iff.mp hw with hsmall | he
  · have hs := of_decide_eq_true hsmall
    exact Or.inl (by omega)
  · exact Or.inr (exception_sound he)

/-- Every prime used below is smaller than 65 squared. -/
def trialPrime (p : ℕ) : Bool :=
  decide (2 ≤ p ∧ p < 65 * 65) &&
    (List.range 63).all fun i => decide (p < (i + 2) * (i + 2) ∨ p % (i + 2) ≠ 0)

lemma trial_sound {p : ℕ} (hc : trialPrime p = true) : p.Prime := by
  unfold trialPrime at hc
  obtain ⟨ha, hdiv⟩ := Bool.and_eq_true_iff.mp hc
  obtain ⟨hp, hb⟩ := of_decide_eq_true ha
  refine Nat.prime_def_le_sqrt.mpr ⟨hp, ?_⟩
  intro m hm hs hmp
  have hsq : m * m ≤ p := Nat.le_sqrt.mp hs
  have h65 : m < 65 := by
    by_contra! h
    have hbig := Nat.mul_le_mul h h
    norm_num at hb hbig
    omega
  have hi : m - 2 ∈ List.range 63 := List.mem_range.mpr (by omega)
  have hw := List.all_eq_true.mp hdiv _ hi
  rw [show m - 2 + 2 = m by omega] at hw
  have hz := Nat.mod_eq_zero_of_dvd hmp
  have hh := of_decide_eq_true hw
  omega

def pairOK (d p : ℕ) : Bool :=
  let q := d + 1 - p
  (trialPrime p && trialPrime q && decide (p ≠ q ∧ p + q = d + 1)) && checkRoots d (p * q)

lemma pair_sound {d p r : ℕ} (hc : pairOK d p = true)
    (hd : d ≤ 4 * r + 3) (hn : 60 ≤ r * r + d) : Good (r * r + d) := by
  let q := d + 1 - p
  change ((trialPrime p && trialPrime q && decide (p ≠ q ∧ p + q = d + 1)) &&
    checkRoots d (p * q)) = true at hc
  obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp hc
  obtain ⟨hpr, heq⟩ := Bool.and_eq_true_iff.mp ha
  obtain ⟨hpcheck, hqcheck⟩ := Bool.and_eq_true_iff.mp hpr
  obtain ⟨hpq, he⟩ := of_decide_eq_true heq
  have hp := trial_sound hpcheck
  have hq := trial_sound hqcheck
  rcases roots_sound hb hd hn with hlt | doneCase
  · apply OMA.R_OeisA234246_conjecture_3_R1.witness (Nat.mul_pos hp.pos hq.pos) hlt (r := r)
    have hphi := OMA.R_OeisA234246_conjecture_3_R1.totient_product hp hq hpq
    omega
  · exact doneCase

/-- Consecutive entries correspond to consecutive odd gaps, starting at d. -/
def checkRow (d : ℕ) : List ℕ → Bool
  | [] => true
  | p :: ps => pairOK d p && checkRow (d + 2) ps

lemma row_sound {ps : List ℕ} {d i : ℕ}
    (hc : checkRow d ps = true) (hi : i < ps.length) :
    ∃ p, pairOK (d + 2 * i) p = true := by
  induction ps generalizing d i with
  | nil => simp at hi
  | cons p ps ih =>
    change (pairOK d p && checkRow (d + 2) ps) = true at hc
    obtain ⟨hfirst, htail⟩ := Bool.and_eq_true_iff.mp hc
    cases i with
    | zero => exact ⟨p, by simpa using hfirst⟩
    | succ i =>
      rw [show d + 2 * (i + 1) = (d + 2) + 2 * i by omega]
      exact ih htail (by simpa using hi)

def Block (lo hi : ℕ) : Prop :=
  ∀ d, lo ≤ d → d < hi → d % 2 = 1 → ∃ p, pairOK d p = true

lemma block_of_row (lo : ℕ) (ps : List ℕ) (ho : lo % 2 = 1)
    (hc : checkRow lo ps = true) : Block lo (lo + 2 * ps.length) := by
  intro d hlo hhi hodd
  let i := (d - lo) / 2
  have he : lo + 2 * i = d := by dsimp [i]; omega
  have hi : i < ps.length := by omega
  simpa only [he] using row_sound hc hi

lemma join_blocks {a b c : ℕ} (hab : Block a b) (hbc : Block b c) : Block a c := by
  intro d hlo hhi hodd
  by_cases h : d < b
  · exact hab d hlo h hodd
  · exact hbc d (by omega) hhi hodd

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
lemma block00 : Block 7 71 :=
  block_of_row 7 [3, 3, 5, 3, 3, 5, 3, 3, 5, 3, 5, 7, 3, 3, 5, 7,
   3, 5, 3, 3, 5, 3, 5, 7, 3, 5, 7, 3, 3, 5, 7, 3] (by decide) (by decide)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
lemma block01 : Block 71 135 :=
  block_of_row 71 [5, 3, 3, 5, 7, 3, 5, 3, 5, 7, 3, 5, 7, 19, 3, 5,
   3, 3, 5, 3, 3, 5, 3, 5, 7, 13, 11, 13, 19, 3, 5, 3] (by decide) (by decide)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
lemma block02 : Block 135 199 :=
  block_of_row 135 [5, 7, 3, 3, 5, 7, 11, 11, 3, 3, 5, 7, 3, 5, 7, 3,
   5, 3, 5, 7, 3, 5, 7, 3, 3, 5, 7, 11, 11, 3, 3, 5] (by decide) (by decide)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
lemma block03 : Block 199 263 :=
  block_of_row 199 [3, 3, 5, 7, 11, 11, 13, 3, 5, 7, 23, 11, 13, 3, 5, 3,
   3, 5, 3, 5, 7, 3, 3, 5, 7, 11, 11, 3, 5, 7, 3, 5] (by decide) (by decide)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
lemma block04 : Block 263 327 :=
  block_of_row 263 [7, 3, 5, 7, 3, 3, 5, 7, 3, 5, 3, 3, 5, 7, 11, 11,
   3, 5, 7, 19, 11, 13, 31, 3, 5, 3, 3, 5, 3, 5, 7, 13] (by decide) (by decide)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
lemma block05 : Block 327 391 :=
  block_of_row 327 [11, 13, 19, 3, 5, 7, 3, 5, 7, 29, 11, 3, 3, 5, 3, 5,
   7, 3, 5, 7, 19, 3, 5, 7, 3, 5, 7, 3, 5, 3, 5, 7] (by decide) (by decide)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
lemma block06 : Block 391 455 :=
  block_of_row 391 [3, 5, 7, 19, 3, 5, 3, 5, 7, 13, 3, 5, 7, 17, 11, 3,
   3, 5, 7, 11, 11, 3, 3, 5, 7, 3, 5, 3, 5, 7, 3, 5] (by decide) (by decide)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
lemma block07 : Block 455 519 :=
  block_of_row 455 [7, 19, 3, 5, 3, 3, 5, 3, 5, 7, 13, 11, 13, 3, 5, 7,
   31, 3, 5, 3, 5, 7, 13, 3, 5, 3, 5, 7, 3, 5, 7, 19] (by decide) (by decide)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
lemma block08 : Block 519 583 :=
  block_of_row 519 [11, 13, 3, 3, 5, 7, 11, 11, 13, 17, 17, 19, 3, 5, 7, 3,
   5, 7, 47, 11, 3, 5, 7, 3, 5, 7, 3, 3, 5, 7, 3, 5] (by decide) (by decide)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
lemma block09 : Block 583 647 :=
  block_of_row 583 [7, 17, 11, 3, 5, 7, 3, 5, 7, 3, 3, 5, 7, 3, 5, 7,
   3, 5, 3, 3, 5, 7, 11, 11, 13, 3, 5, 7, 23, 11, 3, 3] (by decide) (by decide)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
lemma block10 : Block 647 711 :=
  block_of_row 647 [5, 3, 5, 7, 3, 5, 7, 3, 3, 5, 7, 11, 11, 13, 3, 5,
   3, 5, 7, 3, 5, 7, 19, 3, 5, 7, 17, 11, 3, 5, 7, 19] (by decide) (by decide)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
lemma block11 : Block 711 775 :=
  block_of_row 711 [3, 5, 7, 17, 11, 3, 5, 7, 19, 3, 5, 7, 3, 5, 7, 3,
   5, 3, 5, 7, 13, 3, 5, 7, 3, 5, 3, 5, 7, 13, 3, 5] (by decide) (by decide)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
lemma block12 : Block 775 839 :=
  block_of_row 775 [3, 5, 7, 13, 11, 13, 19, 3, 5, 7, 23, 11, 3, 5, 7, 19,
   11, 13, 3, 3, 5, 7, 11, 11, 3, 3, 5, 3, 3, 5, 7, 11] (by decide) (by decide)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
lemma block13 : Block 839 903 :=
  block_of_row 839 [11, 3, 5, 7, 19, 11, 13, 31, 3, 5, 3, 3, 5, 3, 5, 7,
   13, 11, 13, 19, 3, 5, 3, 3, 5, 3, 5, 7, 13, 11, 13, 19] (by decide) (by decide)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
lemma block14 : Block 903 967 :=
  block_of_row 903 [17, 19, 31, 3, 5, 3, 5, 7, 13, 3, 5, 7, 17, 11, 3, 5,
   7, 19, 3, 5, 3, 5, 7, 3, 5, 7, 3, 5, 7, 43, 11, 13] (by decide) (by decide)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
lemma block15 : Block 967 1031 :=
  block_of_row 967 [31, 3, 5, 3, 5, 7, 3, 5, 7, 3, 5, 7, 73, 3, 5, 7,
   3, 5, 7, 23, 11, 13, 3, 5, 3, 5, 7, 3, 3, 5, 7, 11] (by decide) (by decide)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
lemma block16 : Block 1031 1095 :=
  block_of_row 1031 [11, 3, 3, 5, 7, 3, 5, 7, 17, 11, 3, 3, 5, 7, 11, 11,
   3, 3, 5, 7, 3, 5, 7, 17, 11, 13, 23, 17, 19, 3, 5, 3] (by decide) (by decide)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
lemma block17 : Block 1095 1159 :=
  block_of_row 1095 [3, 5, 3, 5, 7, 3, 5, 7, 3, 5, 7, 31, 3, 5, 7, 3,
   5, 7, 3, 5, 7, 29, 11, 13, 41, 17, 19, 41, 23, 3, 3, 5] (by decide) (by decide)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
lemma block18 : Block 1159 1223 :=
  block_of_row 1159 [7, 11, 11, 3, 5, 7, 19, 3, 5, 7, 17, 11, 3, 5, 7, 3,
   5, 7, 3, 5, 7, 31, 3, 5, 7, 17, 11, 13, 3, 5, 3, 5] (by decide) (by decide)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
lemma block19 : Block 1223 1287 :=
  block_of_row 1223 [7, 3, 5, 7, 3, 3, 5, 7, 3, 5, 7, 17, 11, 13, 3, 5,
   7, 29, 11, 3, 5, 7, 19, 11, 13, 37, 17, 19, 3, 3, 5, 3] (by decide) (by decide)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
lemma block20 : Block 1287 1351 :=
  block_of_row 1287 [5, 7, 3, 3, 5, 7, 3, 5, 3, 3, 5, 3, 5, 7, 13, 11,
   13, 3, 3, 5, 7, 3, 5, 7, 17, 11, 13, 23, 17, 19, 29, 23] (by decide) (by decide)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
lemma block21 : Block 1351 1415 :=
  block_of_row 1351 [31, 47, 29, 31, 41, 41, 3, 5, 7, 3, 5, 7, 3, 5, 7, 61,
   3, 5, 7, 17, 11, 13, 23, 17, 19, 3, 5, 7, 41, 11, 3, 5] (by decide) (by decide)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
lemma block22 : Block 1415 1479 :=
  block_of_row 1415 [7, 19, 11, 13, 43, 3, 5, 3, 3, 5, 3, 5, 7, 3, 5, 7,
   19, 3, 5, 3, 3, 5, 7, 3, 5, 7, 17, 11, 13, 3, 5, 7] (by decide) (by decide)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
lemma block23 : Block 1479 1543 :=
  block_of_row 1479 [29, 11, 3, 3, 5, 3, 3, 5, 3, 5, 7, 3, 5, 7, 19, 11,
   13, 3, 5, 7, 31, 11, 13, 3, 5, 7, 43, 3, 5, 7, 17, 11] (by decide) (by decide)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
lemma block24 : Block 1543 1607 :=
  block_of_row 1543 [13, 3, 5, 7, 3, 5, 3, 5, 7, 3, 5, 7, 19, 3, 5, 3,
   5, 7, 13, 3, 5, 3, 5, 7, 13, 11, 13, 19, 3, 5, 3, 5] (by decide) (by decide)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
lemma block25 : Block 1607 1671 :=
  block_of_row 1607 [7, 3, 3, 5, 3, 5, 7, 3, 3, 5, 7, 3, 5, 7, 17, 11,
   3, 5, 7, 19, 11, 13, 31, 17, 19, 31, 3, 5, 7, 3, 5, 3] (by decide) (by decide)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
lemma block26 : Block 1671 1735 :=
  block_of_row 1671 [3, 5, 7, 11, 11, 13, 17, 17, 19, 23, 23, 31, 3, 5, 3, 3,
   5, 7, 11, 11, 3, 5, 7, 19, 11, 13, 3, 3, 5, 7, 11, 11] (by decide) (by decide)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
lemma block27 : Block 1735 1799 :=
  block_of_row 1735 [3, 5, 7, 19, 3, 5, 7, 3, 5, 7, 3, 5, 7, 3, 5, 7,
   47, 11, 13, 41, 17, 19, 3, 5, 7, 3, 5, 3, 3, 5, 7, 11] (by decide) (by decide)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
lemma block28 : Block 1799 1863 :=
  block_of_row 1799 [11, 13, 3, 5, 7, 23, 11, 3, 5, 7, 19, 11, 13, 3, 5, 7,
   31, 3, 5, 7, 17, 11, 13, 23, 17, 3, 5, 7, 67, 11, 13, 31] (by decide) (by decide)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
lemma block29 : Block 1863 1927 :=
  block_of_row 1863 [3, 5, 7, 3, 5, 3, 3, 5, 3, 3, 5, 7, 11, 11, 3, 5,
   7, 19, 11, 13, 3, 5, 7, 3, 5, 7, 3, 5, 7, 43, 11, 13] (by decide) (by decide)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
lemma block30 : Block 1927 1991 :=
  block_of_row 1927 [61, 17, 19, 3, 3, 5, 7, 11, 11, 13, 17, 17, 3, 3, 5, 7,
   11, 11, 13, 17, 17, 19, 23, 23, 3, 5, 7, 3, 5, 7, 37, 3] (by decide) (by decide)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
lemma block31 : Block 1991 2055 :=
  block_of_row 1991 [5, 7, 3, 5, 3, 3, 5, 3, 5, 7, 13, 3, 5, 7, 3, 5,
   7, 23, 11, 3, 3, 5, 7, 11, 11, 3, 5, 7, 19, 11, 13, 37] (by decide) (by decide)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
lemma block32 : Block 2055 2119 :=
  block_of_row 2055 [3, 5, 7, 23, 11, 3, 5, 7, 3, 5, 7, 61, 11, 13, 3, 3,
   5, 3, 3, 5, 7, 11, 11, 3, 5, 7, 19, 11, 13, 3, 3, 5] (by decide) (by decide)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
lemma block33 : Block 2119 2183 :=
  block_of_row 2119 [7, 11, 11, 13, 17, 17, 3, 3, 5, 7, 3, 5, 3, 3, 5, 7,
   11, 11, 3, 5, 7, 19, 3, 5, 7, 17, 11, 13, 23, 17, 19, 3] (by decide) (by decide)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
lemma block34 : Block 2183 2247 :=
  block_of_row 2183 [5, 7, 47, 11, 13, 41, 17, 19, 47, 23, 43, 3, 5, 3, 5, 7,
   3, 5, 7, 19, 3, 5, 7, 17, 11, 13, 23, 17, 3, 3, 5, 3] (by decide) (by decide)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
lemma block35 : Block 2247 2311 :=
  block_of_row 2247 [5, 7, 13, 3, 5, 7, 17, 11, 13, 23, 17, 3, 3, 5, 3, 5,
   7, 13, 3, 5, 7, 3, 5, 7, 3, 5, 3, 5, 7, 13, 11, 13] (by decide) (by decide)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
lemma block36 : Block 2311 2375 :=
  block_of_row 2311 [3, 3, 5, 7, 11, 11, 13, 17, 17, 19, 23, 23, 3, 5, 7, 3,
   3, 5, 7, 3, 5, 3, 5, 7, 3, 5, 7, 19, 11, 13, 31, 3] (by decide) (by decide)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
lemma block37 : Block 2375 2439 :=
  block_of_row 2375 [5, 7, 3, 5, 3, 3, 5, 7, 3, 5, 3, 5, 7, 3, 5, 7,
   19, 11, 13, 3, 5, 7, 3, 5, 7, 3, 5, 7, 43, 11, 13, 61] (by decide) (by decide)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
lemma block38 : Block 2439 2503 :=
  block_of_row 2439 [3, 5, 3, 5, 7, 3, 5, 7, 19, 11, 13, 3, 5, 7, 31, 3,
   5, 7, 3, 5, 3, 5, 7, 13, 11, 13, 19, 17, 19, 31, 23, 29] (by decide) (by decide)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
lemma block39 : Block 2503 2567 :=
  block_of_row 2503 [31, 3, 5, 7, 53, 11, 13, 41, 17, 19, 3, 5, 7, 53, 11, 3,
   5, 7, 19, 3, 5, 3, 5, 7, 3, 3, 5, 7, 3, 5, 7, 17] (by decide) (by decide)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
lemma block40 : Block 2567 2631 :=
  block_of_row 2567 [11, 13, 23, 17, 19, 29, 23, 3, 5, 7, 31, 11, 13, 3, 3, 5,
   7, 11, 11, 13, 17, 17, 3, 5, 7, 61, 3, 5, 3, 5, 7, 13] (by decide) (by decide)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
lemma block41 : Block 2631 2695 :=
  block_of_row 2631 [11, 13, 3, 5, 7, 103, 11, 13, 31, 3, 5, 7, 23, 11, 3, 3,
   5, 3, 5, 7, 13, 3, 5, 7, 3, 5, 7, 3, 5, 3, 3, 5] (by decide) (by decide)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
lemma block42 : Block 2695 2759 :=
  block_of_row 2695 [3, 5, 7, 3, 5, 7, 19, 3, 5, 3, 3, 5, 7, 3, 5, 7,
   17, 11, 3, 3, 5, 7, 11, 11, 3, 5, 7, 19, 3, 5, 3, 5] (by decide) (by decide)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
lemma block43 : Block 2759 2823 :=
  block_of_row 2759 [7, 13, 11, 13, 19, 3, 5, 7, 23, 11, 3, 5, 7, 19, 11, 13,
   3, 3, 5, 7, 3, 5, 3, 3, 5, 7, 11, 11, 13, 17, 17, 3] (by decide) (by decide)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
lemma block44 : Block 2823 2887 :=
  block_of_row 2823 [5, 7, 31, 11, 13, 31, 3, 5, 3, 5, 7, 3, 5, 7, 19, 3,
   5, 7, 3, 5, 3, 5, 7, 13, 11, 13, 19, 17, 19, 3, 5, 7] (by decide) (by decide)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
lemma block45 : Block 2887 2951 :=
  block_of_row 2887 [31, 3, 5, 7, 17, 11, 3, 5, 7, 3, 5, 7, 3, 5, 7, 31,
   3, 5, 7, 17, 11, 3, 5, 7, 19, 11, 13, 3, 5, 7, 31, 11] (by decide) (by decide)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
lemma block46 : Block 2951 3015 :=
  block_of_row 2951 [13, 37, 3, 5, 3, 5, 7, 3, 5, 7, 3, 3, 5, 7, 11, 11,
   13, 17, 17, 19, 23, 23, 43, 29, 29, 3, 3, 5, 7, 11, 11, 3] (by decide) (by decide)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
lemma block47 : Block 3015 3079 :=
  block_of_row 3015 [5, 7, 19, 3, 5, 3, 5, 7, 13, 11, 13, 19, 3, 5, 3, 5,
   7, 13, 3, 5, 7, 17, 11, 13, 3, 5, 7, 3, 5, 7, 53, 11] (by decide) (by decide)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
lemma block48 : Block 3079 3143 :=
  block_of_row 3079 [13, 3, 5, 3, 5, 7, 3, 5, 7, 19, 11, 13, 37, 17, 19, 31,
   3, 5, 7, 29, 11, 3, 3, 5, 7, 11, 11, 13, 17, 17, 3, 5] (by decide) (by decide)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
lemma block49 : Block 3143 3207 :=
  block_of_row 3143 [7, 37, 11, 13, 31, 17, 19, 37, 23, 41, 43, 3, 5, 3, 3, 5,
   7, 11, 11, 13, 3, 5, 7, 3, 5, 3, 5, 7, 13, 11, 13, 3] (by decide) (by decide)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
lemma block50 : Block 3207 3271 :=
  block_of_row 3207 [5, 7, 3, 5, 7, 31, 3, 5, 3, 5, 7, 13, 3, 5, 7, 17,
   11, 13, 23, 17, 19, 29, 23, 3, 3, 5, 3, 3, 5, 7, 11, 11] (by decide) (by decide)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
lemma block51 : Block 3271 3335 :=
  block_of_row 3271 [13, 3, 5, 7, 23, 11, 13, 29, 17, 19, 41, 23, 37, 41, 29, 3,
   3, 5, 7, 3, 5, 7, 3, 5, 7, 3, 5, 3, 5, 7, 3, 3] (by decide) (by decide)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
lemma block52 : Block 3335 3399 :=
  block_of_row 3335 [5, 7, 11, 11, 13, 3, 5, 3, 5, 7, 13, 11, 13, 3, 3, 5,
   7, 11, 11, 3, 3, 5, 7, 11, 11, 13, 17, 17, 3, 3, 5, 7] (by decide) (by decide)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
lemma block53 : Block 3399 3463 :=
  block_of_row 3399 [11, 11, 13, 17, 17, 3, 5, 7, 3, 5, 7, 31, 11, 13, 37, 17,
   19, 43, 3, 5, 7, 29, 11, 13, 41, 17, 3, 5, 7, 67, 3, 5] (by decide) (by decide)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
lemma block54 : Block 3463 3527 :=
  block_of_row 3463 [3, 3, 5, 3, 3, 5, 7, 11, 11, 13, 17, 17, 19, 23, 23, 3,
   5, 7, 31, 3, 5, 7, 17, 11, 13, 3, 5, 7, 3, 5, 7, 59] (by decide) (by decide)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
lemma block55 : Block 3527 3591 :=
  block_of_row 3527 [11, 3, 3, 5, 3, 5, 7, 3, 3, 5, 7, 3, 5, 7, 17, 11,
   3, 3, 5, 7, 11, 11, 13, 3, 5, 7, 23, 11, 3, 3, 5, 7] (by decide) (by decide)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
lemma block56 : Block 3591 3655 :=
  block_of_row 3591 [11, 11, 3, 5, 7, 19, 11, 13, 37, 3, 5, 7, 3, 5, 3, 5,
   7, 3, 5, 7, 19, 3, 5, 7, 3, 5, 7, 3, 5, 7, 29, 11] (by decide) (by decide)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
lemma block57 : Block 3655 3719 :=
  block_of_row 3655 [13, 41, 17, 3, 5, 7, 31, 11, 13, 3, 3, 5, 3, 5, 7, 13,
   11, 13, 19, 3, 5, 7, 3, 5, 3, 5, 7, 13, 3, 5, 7, 17] (by decide) (by decide)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
lemma block58 : Block 3719 3783 :=
  block_of_row 3719 [11, 3, 5, 7, 19, 3, 5, 7, 3, 5, 7, 3, 5, 7, 29, 11,
   13, 53, 17, 19, 41, 23, 3, 5, 7, 3, 3, 5, 7, 11, 11, 3] (by decide) (by decide)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
lemma block59 : Block 3783 3847 :=
  block_of_row 3783 [5, 7, 19, 11, 13, 61, 3, 5, 3, 5, 7, 3, 5, 7, 19, 11,
   13, 79, 17, 19, 3, 3, 5, 7, 11, 11, 3, 5, 7, 19, 11, 13] (by decide) (by decide)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
lemma block60 : Block 3847 3911 :=
  block_of_row 3847 [79, 3, 5, 3, 3, 5, 7, 11, 11, 3, 5, 7, 19, 11, 13, 31,
   3, 5, 3, 5, 7, 13, 3, 5, 7, 17, 11, 13, 23, 17, 19, 3] (by decide) (by decide)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
lemma block61 : Block 3911 3975 :=
  block_of_row 3911 [5, 3, 5, 7, 3, 3, 5, 3, 5, 7, 3, 3, 5, 7, 11, 11,
   13, 3, 5, 3, 5, 7, 13, 11, 13, 19, 17, 19, 37, 3, 5, 7] (by decide) (by decide)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
lemma block62 : Block 3975 4039 :=
  block_of_row 3975 [29, 11, 13, 53, 17, 19, 41, 23, 3, 5, 7, 31, 11, 13, 3, 3,
   5, 3, 5, 7, 3, 5, 7, 3, 3, 5, 7, 3, 5, 7, 17, 11] (by decide) (by decide)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
lemma block63 : Block 4039 4097 :=
  block_of_row 4039 [13, 23, 17, 19, 29, 23, 3, 3, 5, 7, 3, 5, 7, 17, 11, 13,
   23, 17, 3, 5, 7, 3, 5, 7, 31, 11, 13, 3, 3] (by decide) (by decide)

lemma all_pairs : Block 7 4097 := (join_blocks (join_blocks (join_blocks (join_blocks (join_blocks (join_blocks block00 block01) (join_blocks block02 block03)) (join_blocks (join_blocks block04 block05) (join_blocks block06 block07))) (join_blocks (join_blocks (join_blocks block08 block09) (join_blocks block10 block11)) (join_blocks (join_blocks block12 block13) (join_blocks block14 block15)))) (join_blocks (join_blocks (join_blocks (join_blocks block16 block17) (join_blocks block18 block19)) (join_blocks (join_blocks block20 block21) (join_blocks block22 block23))) (join_blocks (join_blocks (join_blocks block24 block25) (join_blocks block26 block27)) (join_blocks (join_blocks block28 block29) (join_blocks block30 block31))))) (join_blocks (join_blocks (join_blocks (join_blocks (join_blocks block32 block33) (join_blocks block34 block35)) (join_blocks (join_blocks block36 block37) (join_blocks block38 block39))) (join_blocks (join_blocks (join_blocks block40 block41) (join_blocks block42 block43)) (join_blocks (join_blocks block44 block45) (join_blocks block46 block47)))) (join_blocks (join_blocks (join_blocks (join_blocks block48 block49) (join_blocks block50 block51)) (join_blocks (join_blocks block52 block53) (join_blocks block54 block55))) (join_blocks (join_blocks (join_blocks block56 block57) (join_blocks block58 block59)) (join_blocks (join_blocks block60 block61) (join_blocks block62 block63))))))

lemma bounded_gap {n : ℕ} (hn : 60 ≤ n) (hu : n < 2 ^ 20) :
    ∃ r d : ℕ, n = r * r + d ∧ d % 2 = 1 ∧ d ≤ 4 * r + 3 ∧ d < 4096 := by
  let s := n.sqrt
  have hlo : s * s ≤ n := Nat.sqrt_le n
  have hhi : n < (s + 1) * (s + 1) := Nat.lt_succ_sqrt n
  have hs : s ≤ 1023 := by
    by_contra! h
    have hb := Nat.mul_le_mul (show 1024 ≤ s by omega) (show 1024 ≤ s by omega)
    norm_num at hb hu
    omega
  have hp : s ≠ 0 := by intro hz; rw [hz] at hhi; omega
  obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero hp
  obtain ⟨d, hnd⟩ := Nat.exists_eq_add_of_le hlo
  by_cases ho : d % 2 = 1
  · have hd : d ≤ 4 * s + 3 := by nlinarith
    exact ⟨s, d, hnd, ho, hd, by omega⟩
  · have hd : d + 2 * r + 1 ≤ 4 * r + 3 := by rw [hr] at hnd hhi; nlinarith
    refine ⟨r, d + 2 * r + 1, ?_, by omega, hd, by omega⟩
    rw [hr] at hnd
    nlinarith

end OMA.SunFinite

theorem OMA.solution : OMA.R_OeisA234246_conjecture_3_R1.H1 := by
  intro n hn hu
  obtain ⟨r, d, hnd, hodd, hd, hb⟩ := OMA.SunFinite.bounded_gap hn hu
  by_cases h : d < 7
  · have hv : d = 1 ∨ d = 3 ∨ d = 5 := by omega
    rcases hv with h1 | h3 | h5
    · apply OMA.R_OeisA234246_conjecture_3_R1.witness (m := 2) (r := r) (by decide) (by omega)
      rw [show Nat.totient 2 = 1 by decide]
      omega
    · apply OMA.R_OeisA234246_conjecture_3_R1.witness (m := 9) (r := r) (by decide) (by omega)
      rw [show Nat.totient 9 = 6 by decide]
      omega
    · apply OMA.R_OeisA234246_conjecture_3_R1.witness (m := 25) (r := r) (by decide) (by omega)
      rw [show Nat.totient 25 = 20 by decide]
      omega
  obtain ⟨p, hp⟩ := OMA.SunFinite.all_pairs d (by omega) (by omega) hodd
  rw [hnd] at hn ⊢
  exact OMA.SunFinite.pair_sound hp hd hn
