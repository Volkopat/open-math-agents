import OMAReductions.R_OeisA249609_conjecture_R1_H2_R1
import Mathlib.Tactic

/-!
# Odd Pascal rows near a power of two

Write an odd row index as n = 2^(e+1) - c with 1 ≤ c ≤ 2^e.
Every Mersenne row with exponent at least four has a coefficient of
even binary digit sum in columns 1, 4, 6, 7 or 8. For each of these
columns the parity is periodic in the exponent, with period dividing
24 once the fixed binary blocks no longer overlap.

There is also a test uniform in the odd defect c. When c(c+1) < 2^(e+1),
double the second binomial coefficient and separate the two binary
blocks in n(n-1). If c(c+1) has even weight, the first and second
columns have opposite weight parity. The two remaining tasks address
large defects and the small defects escaping this test.

The generic long-division argument and the binary concatenation lemma
are adapted from PanPapag’s PR 5614 for rows indexed by powers of two.
The shifted falling factorials, the residue certificates, and the
near-power column-two identity below apply to different row indices.
-/

namespace OMA.R_OeisA249609_conjecture_R1_H2_R1_H1_R1

/-- Appending a padded binary word adds its number of one-bits. -/
lemma count_ones_append (x w c : ℕ) (hc : c < 2^w) :
    (Nat.digits 2 (x * 2^w + c)).count 1 =
      (Nat.digits 2 x).count 1 + (Nat.digits 2 c).count 1 := by
  let ones (n : ℕ) := (Nat.digits 2 n).count 1
  change ones (x * 2^w + c) = ones x + ones c
  have hlen : (Nat.digits 2 c).length ≤ w := (Nat.digits_length_le_iff (by decide : 1 < 2) _).mpr hc
  have h := Nat.digits_append_zeroes_append_digits (b := 2) (m := x) (n := c)
    (k := w - (Nat.digits 2 c).length) (by decide)
  by_cases hx : x = 0
  · simp [hx, ones]
  have e := h (Nat.pos_of_ne_zero hx)
  rw [show (Nat.digits 2 c).length + (w - (Nat.digits 2 c).length) = w by omega] at e
  unfold ones
  rw [show x * 2 ^ w + c = c + 2^w*x by ring, ← e]
  simp [List.count_replicate, Nat.add_comm]

set_option maxHeartbeats 2000000 in
lemma rowPeriodic (row : ℕ → ℕ) {a k t d z l : ℕ} {ds : List (Bool × ℕ)}
    (ht : t ≤ a) (hd : 0 < d) (hm : 2^l%d=1%d) (hc : ∀ s ∈ ds, s.2 < 2^t)
    (hw : ∀ w : ℕ, ds.foldr (fun s v => (v * 2^w + (if s.1 then 2^w-1 else 0)) * 2^t + s.2) 0 =
      (row (w+t)).descFactorial k) (hf : k.factorial = d * 2^z) :
    OeisA249609.isEvil ((row a).choose k) = true ↔
      (Nat.digits 2 ((row ((a-t)%(l+l)+t)).descFactorial k / d)).count 1 % 2 = 0 := by
  let ones (x : ℕ) : ℕ := (Nat.digits 2 x).count 1
  have ones_join (x w c : ℕ) (hc : c < 2^w) :
      ones (x * 2^w + c) = ones x + ones c := count_ones_append x w c hc

  let state (d x : ℕ) : ℕ × ℕ := (x%d, ones (x/d)%2)

  have state_join {d : ℕ} (hd : 0 < d) (x w c : ℕ) (hc : c < 2^w) :
      state d (x*2^w+c) =
        let v := x%d * 2^w+c
        (v%d, ((state d x).2 + ones (v/d))%2) := by
    have he : x*2^w+c = (x%d * 2^w+c) + (x/d * 2^w)*d := by
      calc
        x*2^w+c = (x%d+d*(x/d))*2^w+c := by rw [Nat.mod_add_div]
        _ = _ := by ring
    have hv : (x%d * 2^w+c)/d < 2^w := by
      apply (Nat.div_lt_iff_lt_mul hd).mpr
      have h := Nat.mul_le_mul_right (2^w) (Nat.succ_le_of_lt (Nat.mod_lt x hd))
      rw [Nat.succ_mul] at h
      nlinarith only [h,hc]
    unfold state
    rw [he, Nat.add_mul_mod_self_right, Nat.add_mul_div_right _ _ hd,
        Nat.add_comm ((x % d * 2 ^ w + c) / d), ones_join _ _ _ hv]
    simp [Nat.add_mod]

  have state_join_eq {d x y : ℕ} (hd : 0 < d) (he : state d x = state d y)
      (w c : ℕ) (hc : c < 2^w) : state d (x*2^w+c) = state d (y*2^w+c) := by
    have hr : x%d = y%d := congrArg Prod.fst he
    rw [state_join hd x w c hc, state_join hd y w c hc, he, hr]

  let fill (b : Bool) (w : ℕ) : ℕ := if b then 2^w-1 else 0

  have fill_lt (b : Bool) (w : ℕ) : fill b w < 2^w := by
    have : 0 < 2^w := by positivity
    cases b <;> simp [fill]

  have fill_add (b : Bool) (w u : ℕ) :
      fill b (w+u) = fill b w * 2^u + fill b u := by
    have hw : 0 < 2^w := by positivity
    have hu : 0 < 2^u := by positivity
    cases b
    · simp [fill]
    simp only [fill, if_true, pow_add]
    have e := Nat.sub_add_cancel (show 1 ≤ 2^w by omega)
    have e' := Nat.sub_add_cancel (show 1 ≤ 2^u by omega)
    have hh := congrArg (· * 2^u) e
    simp only [Nat.add_mul, Nat.one_mul] at hh
    omega

  have state_repeat {d l : ℕ} (hd : 0 < d) (hmod : 2^l % d = 1 % d)
      (x : ℕ) (b : Bool) : state d (x*2^(l+l) + fill b (l+l)) = state d x := by
    let c := fill b l
    have hc := fill_lt b l
    have hdiv : d ∣ 2^l-1 :=
      (Nat.modEq_iff_dvd' (show 1 ≤ 2^l by exact Nat.one_le_two_pow)).mp hmod.symm
    have hz : c%d = 0 := by cases b <;> simp [c, fill, Nat.mod_eq_zero_of_dvd hdiv]
    have hrem (y : ℕ) : (y*2^l+c)%d = y%d := by
      rw [Nat.add_mod, hz, Nat.add_zero, Nat.mod_mod, Nat.mul_mod, hmod, ← Nat.mul_mod, Nat.mul_one]
    rw [fill_add, pow_add]
    change state d (x*(2^l*2^l)+(c*2^l+c)) = _
    rw [show x*(2^l*2^l)+(c*2^l+c) = (x*2^l+c)*2^l+c by ring]
    rw [state_join hd _ _ _ hc, hrem x, state_join hd _ _ _ hc]
    dsimp only
    rw [hrem (x%d), Nat.mod_mod]
    unfold state
    congr 1
    omega


  let word (w t : ℕ) (ds : List (Bool × ℕ)) : ℕ :=
    ds.foldr (fun s v => (v * 2^w + fill s.1 w) * 2^t + s.2) 0

  have word_period {d l : ℕ} (hd : 0 < d) (hm : 2^l%d=1%d) (w t : ℕ)
      (ds : List (Bool × ℕ)) (hc : ∀ s ∈ ds, s.2 < 2^t) :
      state d (word (w+(l+l)) t ds) = state d (word w t ds) := by
    induction ds with
    | nil => rfl
    | cons s ds ih =>
      obtain ⟨b,c⟩ := s
      have hsmall : c < 2 ^ t := hc (b,c) (by simp)
      have he := ih (fun s hs => hc s (by simp [hs]))
      change state d ((word (w+(l+l)) t ds * 2^(w+(l+l))+fill b (w+(l+l)))*2^t+c) =
        state d ((word w t ds*2^w+fill b w)*2^t+c)
      apply state_join_eq hd _ t c hsmall
      rw [fill_add b w (l+l), pow_add]
      rw [show word (w+(l+l)) t ds*(2^w*2^(l+l))+
            (fill b w*2^(l+l)+fill b (l+l)) =
          (word (w+(l+l)) t ds * 2^w+fill b w)*2^(l+l)+fill b (l+l) by ring]
      rw [state_repeat hd hm]
      exact state_join_eq hd he w _ (fill_lt b w)

  have word_mod {d l : ℕ} (hd : 0 < d) (hm : 2^l%d=1%d) (w t : ℕ)
      (ds : List (Bool × ℕ)) (hc : ∀ s ∈ ds, s.2 < 2^t) :
      state d (word w t ds) = state d (word (w%(l+l)) t ds) := by
    have per (x q : ℕ) : state d (word (x+(l+l)*q) t ds) = state d (word x t ds) := by
      induction q with
      | zero => simp
      | succ q ih =>
        rw [Nat.mul_succ, ← Nat.add_assoc, word_period hd hm, ih]
        exact hc
    conv_lhs => rw [← Nat.mod_add_div w (l+l)]
    exact per _ _



  have ones_scaled (v n : ℕ) : ones (2^v * n) = ones n := by
    simpa only [Nat.mul_comm n, Nat.add_zero, show ones 0 = 0 by rfl] using
      ones_join n v 0 (by positivity)

  have column {a k t d z l : ℕ} {ds : List (Bool × ℕ)} (ht : t ≤ a)
      (hd : 0 < d) (hm : 2^l%d=1%d) (hc : ∀ s ∈ ds, s.2 < 2^t)
      (hword : ∀ w, word w t ds = (row (w+t)).descFactorial k)
      (hfac : k.factorial = d * 2^z) :
      OeisA249609.isEvil ((row a).choose k) = true ↔
        (state d (word ((a-t)%(l+l)) t ds)).2 = 0 := by
    rw [← word_mod hd hm (a-t) t ds hc, hword, Nat.sub_add_cancel ht,
        Nat.descFactorial_eq_factorial_mul_choose, hfac, Nat.mul_assoc]
    change (ones ((row a).choose k) % 2 == 0) = true ↔
      ones (d * (2^z * (row a).choose k) / d) % 2 = 0
    rw [Nat.mul_div_cancel_left _ hd, ones_scaled, beq_iff_eq]
  have he := column ht hd hm hc hw hf
  change _ ↔ ones ((row ((a-t)%(l+l)+t)).descFactorial k /d)%2 = 0
  rw [← hw]
  exact he


set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
lemma falling1 (x : ℕ) (hx : 0 < x) :
    ([(true, 3)] : List (Bool × ℕ)).foldr (fun s n => (n*x + (if s.1 then x-1 else 0))*4+s.2) 0 =
      (x*4-1).descFactorial 1 := by
  let low (n c : ℕ) := (n*x+0)*4+c
  let high (n c : ℕ) := (n*x+(x-1))*4+c
  calc
    _ = (high 0 3) := rfl
    _ = _ := by
      apply Int.ofNat_inj.mp
      dsimp only [low,high]
      norm_num [Nat.descFactorial]
      simp (disch := omega) only [Nat.cast_sub, Nat.cast_mul, Nat.cast_ofNat]
      ring

lemma column1 (a : ℕ) (ha : 24 ≤ a) (hr : a % 24 ∈ ([0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22] : List ℕ)) :
    OeisA249609.isEvil ((2^a-1).choose 1) = true := by
  apply (rowPeriodic (fun v => 2^v-1) (a:=a) (k:=1) (t:=2) (l:=12) (d:=1) (z:=0)
    (ds:=([(true, 3)] : List (Bool × ℕ))) (by omega) (by decide) (by decide) (by decide)
    (fun w => by rw [pow_add]; exact falling1 (2^w) (by positivity))
    (by decide)).2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with hr|hr|hr|hr|hr|hr|hr|hr|hr|hr|hr|hr
  · rw [show (a-2)%(12+12)+2 = 24 by omega]; decide +kernel
  · rw [show (a-2)%(12+12)+2 = 2 by omega]; decide +kernel
  · rw [show (a-2)%(12+12)+2 = 4 by omega]; decide +kernel
  · rw [show (a-2)%(12+12)+2 = 6 by omega]; decide +kernel
  · rw [show (a-2)%(12+12)+2 = 8 by omega]; decide +kernel
  · rw [show (a-2)%(12+12)+2 = 10 by omega]; decide +kernel
  · rw [show (a-2)%(12+12)+2 = 12 by omega]; decide +kernel
  · rw [show (a-2)%(12+12)+2 = 14 by omega]; decide +kernel
  · rw [show (a-2)%(12+12)+2 = 16 by omega]; decide +kernel
  · rw [show (a-2)%(12+12)+2 = 18 by omega]; decide +kernel
  · rw [show (a-2)%(12+12)+2 = 20 by omega]; decide +kernel
  · rw [show (a-2)%(12+12)+2 = 22 by omega]; decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
lemma falling4 (x : ℕ) (hx : 0 < x) :
    ([(false, 24), (true, 78), (false, 34), (true, 118)] : List (Bool × ℕ)).foldr (fun s n => (n*x + (if s.1 then x-1 else 0))*128+s.2) 0 =
      (x*128-1).descFactorial 4 := by
  let low (n c : ℕ) := (n*x+0)*128+c
  let high (n c : ℕ) := (n*x+(x-1))*128+c
  calc
    _ = (low (high (low (high 0 118) 34) 78) 24) := rfl
    _ = _ := by
      apply Int.ofNat_inj.mp
      dsimp only [low,high]
      norm_num [Nat.descFactorial]
      simp (disch := omega) only [Nat.cast_sub, Nat.cast_mul, Nat.cast_ofNat]
      ring

lemma column4 (a : ℕ) (ha : 24 ≤ a) (hr : a % 24 ∈ ([3, 7, 11, 15, 19, 23] : List ℕ)) :
    OeisA249609.isEvil ((2^a-1).choose 4) = true := by
  apply (rowPeriodic (fun v => 2^v-1) (a:=a) (k:=4) (t:=7) (l:=12) (d:=3) (z:=3)
    (ds:=([(false, 24), (true, 78), (false, 34), (true, 118)] : List (Bool × ℕ))) (by omega) (by decide) (by decide) (by decide)
    (fun w => by rw [pow_add]; exact falling4 (2^w) (by positivity))
    (by decide)).2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with hr|hr|hr|hr|hr|hr
  · rw [show (a-7)%(12+12)+7 = 27 by omega]; decide +kernel
  · rw [show (a-7)%(12+12)+7 = 7 by omega]; decide +kernel
  · rw [show (a-7)%(12+12)+7 = 11 by omega]; decide +kernel
  · rw [show (a-7)%(12+12)+7 = 15 by omega]; decide +kernel
  · rw [show (a-7)%(12+12)+7 = 19 by omega]; decide +kernel
  · rw [show (a-7)%(12+12)+7 = 23 by omega]; decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
lemma falling6 (x : ℕ) (hx : 0 < x) :
    ([(false, 720), (true, 2332), (false, 1623), (true, 3361), (false, 174), (true, 4075)] : List (Bool × ℕ)).foldr (fun s n => (n*x + (if s.1 then x-1 else 0))*4096+s.2) 0 =
      (x*4096-1).descFactorial 6 := by
  let low (n c : ℕ) := (n*x+0)*4096+c
  let high (n c : ℕ) := (n*x+(x-1))*4096+c
  calc
    _ = (low (high (low (high (low (high 0 4075) 174) 3361) 1623) 2332) 720) := rfl
    _ = _ := by
      apply Int.ofNat_inj.mp
      dsimp only [low,high]
      norm_num [Nat.descFactorial]
      simp (disch := omega) only [Nat.cast_sub, Nat.cast_mul, Nat.cast_ofNat]
      ring

lemma column6 (a : ℕ) (ha : 24 ≤ a) (hr : a % 24 ∈ ([1, 13] : List ℕ)) :
    OeisA249609.isEvil ((2^a-1).choose 6) = true := by
  apply (rowPeriodic (fun v => 2^v-1) (a:=a) (k:=6) (t:=12) (l:=12) (d:=45) (z:=4)
    (ds:=([(false, 720), (true, 2332), (false, 1623), (true, 3361), (false, 174), (true, 4075)] : List (Bool × ℕ))) (by omega) (by decide) (by decide) (by decide)
    (fun w => by rw [pow_add]; exact falling6 (2^w) (by positivity))
    (by decide)).2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with hr|hr
  · rw [show (a-12)%(12+12)+12 = 25 by omega]; decide +kernel
  · rw [show (a-12)%(12+12)+12 = 13 by omega]; decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
lemma falling7 (x : ℕ) (hx : 0 < x) :
    ([(true, 27728), (false, 13067), (true, 19636), (false, 6768), (true, 30808), (false, 321), (true, 32740)] : List (Bool × ℕ)).foldr (fun s n => (n*x + (if s.1 then x-1 else 0))*32768+s.2) 0 =
      (x*32768-1).descFactorial 7 := by
  let low (n c : ℕ) := (n*x+0)*32768+c
  let high (n c : ℕ) := (n*x+(x-1))*32768+c
  calc
    _ = (high (low (high (low (high (low (high 0 32740) 321) 30808) 6768) 19636) 13067) 27728) := rfl
    _ = _ := by
      apply Int.ofNat_inj.mp
      dsimp only [low,high]
      norm_num [Nat.descFactorial]
      simp (disch := omega) only [Nat.cast_sub, Nat.cast_mul, Nat.cast_ofNat]
      ring

lemma column7 (a : ℕ) (ha : 24 ≤ a) (hr : a % 24 ∈ ([9, 21] : List ℕ)) :
    OeisA249609.isEvil ((2^a-1).choose 7) = true := by
  apply (rowPeriodic (fun v => 2^v-1) (a:=a) (k:=7) (t:=15) (l:=12) (d:=315) (z:=4)
    (ds:=([(true, 27728), (false, 13067), (true, 19636), (false, 6768), (true, 30808), (false, 321), (true, 32740)] : List (Bool × ℕ))) (by omega) (by decide) (by decide) (by decide)
    (fun w => by rw [pow_add]; exact falling7 (2^w) (by positivity))
    (by decide)).2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with hr|hr
  · rw [show (a-15)%(12+12)+15 = 33 by omega]; decide +kernel
  · rw [show (a-15)%(12+12)+15 = 21 by omega]; decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
lemma falling8 (x : ℕ) (hx : 0 < x) :
    ([(false, 40320), (true, 152560), (false, 118123), (true, 194860), (false, 22448), (true, 257608), (false, 545), (true, 262108)] : List (Bool × ℕ)).foldr (fun s n => (n*x + (if s.1 then x-1 else 0))*262144+s.2) 0 =
      (x*262144-1).descFactorial 8 := by
  let low (n c : ℕ) := (n*x+0)*262144+c
  let high (n c : ℕ) := (n*x+(x-1))*262144+c
  calc
    _ = (low (high (low (high (low (high (low (high 0 262108) 545) 257608) 22448) 194860) 118123) 152560) 40320) := rfl
    _ = _ := by
      apply Int.ofNat_inj.mp
      dsimp only [low,high]
      norm_num [Nat.descFactorial]
      simp (disch := omega) only [Nat.cast_sub, Nat.cast_mul, Nat.cast_ofNat]
      ring

lemma column8 (a : ℕ) (ha : 24 ≤ a) (hr : a % 24 ∈ ([5, 17] : List ℕ)) :
    OeisA249609.isEvil ((2^a-1).choose 8) = true := by
  apply (rowPeriodic (fun v => 2^v-1) (a:=a) (k:=8) (t:=18) (l:=12) (d:=315) (z:=7)
    (ds:=([(false, 40320), (true, 152560), (false, 118123), (true, 194860), (false, 22448), (true, 257608), (false, 545), (true, 262108)] : List (Bool × ℕ))) (by omega) (by decide) (by decide) (by decide)
    (fun w => by rw [pow_add]; exact falling8 (2^w) (by positivity))
    (by decide)).2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with hr|hr
  · rw [show (a-18)%(12+12)+18 = 29 by omega]; decide +kernel
  · rw [show (a-18)%(12+12)+18 = 41 by omega]; decide +kernel

lemma witness (a : ℕ) (ha : 4 ≤ a) :
    ∃ k ∈ ([1, 4, 6, 7, 8] : List ℕ), OeisA249609.isEvil ((2^a-1).choose k) = true := by
  by_cases h : 24 ≤ a
  · have hcov : ∀ i : Fin 24, i.val ∈ ([0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22] : List ℕ) ∨
      i.val ∈ ([3, 7, 11, 15, 19, 23] : List ℕ) ∨
      i.val ∈ ([1, 13] : List ℕ) ∨
      i.val ∈ ([9, 21] : List ℕ) ∨
      i.val ∈ ([5, 17] : List ℕ) := by decide
    rcases hcov ⟨a%24, Nat.mod_lt _ (by decide)⟩ with h₁|h₁|h₁|h₁|h₁
    · exact ⟨1, by decide, column1 a h h₁⟩
    · exact ⟨4, by decide, column4 a h h₁⟩
    · exact ⟨6, by decide, column6 a h h₁⟩
    · exact ⟨7, by decide, column7 a h h₁⟩
    · exact ⟨8, by decide, column8 a h h₁⟩
  · have small : a ≤ 23 := by omega
    interval_cases a
    · refine ⟨1, by decide, ?_⟩; rw [Nat.choose_eq_descFactorial_div_factorial]; decide +kernel
    · refine ⟨4, by decide, ?_⟩; rw [Nat.choose_eq_descFactorial_div_factorial]; decide +kernel
    · refine ⟨1, by decide, ?_⟩; rw [Nat.choose_eq_descFactorial_div_factorial]; decide +kernel
    · refine ⟨4, by decide, ?_⟩; rw [Nat.choose_eq_descFactorial_div_factorial]; decide +kernel
    · refine ⟨1, by decide, ?_⟩; rw [Nat.choose_eq_descFactorial_div_factorial]; decide +kernel
    · refine ⟨7, by decide, ?_⟩; rw [Nat.choose_eq_descFactorial_div_factorial]; decide +kernel
    · refine ⟨1, by decide, ?_⟩; rw [Nat.choose_eq_descFactorial_div_factorial]; decide +kernel
    · refine ⟨4, by decide, ?_⟩; rw [Nat.choose_eq_descFactorial_div_factorial]; decide +kernel
    · refine ⟨1, by decide, ?_⟩; rw [Nat.choose_eq_descFactorial_div_factorial]; decide +kernel
    · refine ⟨6, by decide, ?_⟩; rw [Nat.choose_eq_descFactorial_div_factorial]; decide +kernel
    · refine ⟨1, by decide, ?_⟩; rw [Nat.choose_eq_descFactorial_div_factorial]; decide +kernel
    · refine ⟨4, by decide, ?_⟩; rw [Nat.choose_eq_descFactorial_div_factorial]; decide +kernel
    · refine ⟨1, by decide, ?_⟩; rw [Nat.choose_eq_descFactorial_div_factorial]; decide +kernel
    · refine ⟨8, by decide, ?_⟩; rw [Nat.choose_eq_descFactorial_div_factorial]; decide +kernel
    · refine ⟨1, by decide, ?_⟩; rw [Nat.choose_eq_descFactorial_div_factorial]; decide +kernel
    · refine ⟨4, by decide, ?_⟩; rw [Nat.choose_eq_descFactorial_div_factorial]; decide +kernel
    · refine ⟨1, by decide, ?_⟩; rw [Nat.choose_eq_descFactorial_div_factorial]; decide +kernel
    · refine ⟨7, by decide, ?_⟩; rw [Nat.choose_eq_descFactorial_div_factorial]; decide +kernel
    · refine ⟨1, by decide, ?_⟩; rw [Nat.choose_eq_descFactorial_div_factorial]; decide +kernel
    · refine ⟨4, by decide, ?_⟩; rw [Nat.choose_eq_descFactorial_div_factorial]; decide +kernel

lemma half (x : ℕ) :
    (Nat.digits 2 x).count 1 = (Nat.digits 2 (x/2)).count 1 + x%2 := by
  have h := count_ones_append (x/2) 1 (x%2) (by simpa using Nat.mod_lt x (by decide : 0 < 2))
  rw [pow_one, Nat.div_add_mod'] at h
  rcases (show x%2 = 0 ∨ x%2 = 1 by omega) with h₀|h₁
  · simpa [h₀] using h
  · simpa [h₁] using h

lemma complement (a u v : ℕ) (h : u+v+1 = 2^a) :
    (Nat.digits 2 u).count 1 + (Nat.digits 2 v).count 1 = a := by
  induction a generalizing u v with
  | zero =>
    have hu : u = 0 := by simpa using (show u = 0 by omega)
    have hv : v = 0 := by omega
    simp [hu,hv]
  | succ a ih =>
    rw [pow_succ] at h
    have hi := ih (u/2) (v/2) (by omega)
    rw [half u,half v]
    omega

lemma even_digits_double (u : ℕ) :
    (Nat.digits 2 (2*u)).count 1 = (Nat.digits 2 u).count 1 := by
  rw [half]
  simp

lemma columns_one_two (a c n : ℕ) (hc : Odd c) (hd : c*(c+1)<2^a)
    (hn : n+c=2^a) (hweight : OeisA249609.isEvil (c*(c+1)) = true) :
    OeisA249609.isEvil (n.choose 1) = true ∨
      OeisA249609.isEvil (n.choose 2) = true := by
  have hcmod := Nat.odd_iff.mp hc
  have hpos : 0 < c := by omega
  have hcc : c+c ≤ c*(c+1) := by nlinarith
  let z := 2^a-(2*c+1)
  have hz : z+2*c+1 = 2^a := by dsimp [z]; omega
  have hn' : n=z+c+1 := by omega
  have prod_eq : n*(n-1) = z*2^a + c*(c+1) := by
    rw [hn',← hz]
    simp
    ring
  have hc1 := complement a n (c-1) (by omega)
  have hc2 := complement a z (2*c) (by omega)
  rw [even_digits_double] at hc2
  have hc3 := count_ones_append z a (c*(c+1)) hd
  have c2 : 2*n.choose 2 = n*(n-1) := by
    have e := Nat.descFactorial_eq_factorial_mul_choose n 2
    simpa [Nat.descFactorial, mul_comm] using e.symm
  rw [← prod_eq, ← c2, even_digits_double] at hc3
  have hcp : (Nat.digits 2 c).count 1 = (Nat.digits 2 (c-1)).count 1 + 1 := by
    have h₁ := half c
    have h₂ := half (c-1)
    rw [show (c-1)/2 = c/2 by omega] at h₂
    omega
  simpa only [Nat.choose_one_right, OeisA249609.isEvil, beq_iff_eq] using (show
      (Nat.digits 2 n).count 1 % 2 = 0 ∨ (Nat.digits 2 (n.choose 2)).count 1 % 2 = 0 by
    have he : (Nat.digits 2 (c*(c+1))).count 1 % 2 = 0 := by
      simpa [OeisA249609.isEvil] using hweight
    omega)

/-- The large-defect range. -/
def H1 : Prop := ∀ e c : ℕ, 1 < c → c ≤ 2^e → Odd c →
  2^(e+1) ≤ c*(c+1) → OeisA249609.isEvil (2^(e+1)-c) = false →
  ∃ k ∈ List.range' 1 (2^(e+1)-c), OeisA249609.isEvil ((2^(e+1)-c).choose k) = true

/-- Small defects for which the first two columns do not give opposite parities. -/
def H2 : Prop := ∀ e c : ℕ, 1 < c → c ≤ 2^e → Odd c →
  c*(c+1) < 2^(e+1) → OeisA249609.isEvil (c*(c+1)) = false →
  OeisA249609.isEvil (2^(e+1)-c) = false →
  ∃ k ∈ List.range' 1 (2^(e+1)-c), OeisA249609.isEvil ((2^(e+1)-c).choose k) = true

theorem main : H1 → H2 → OMA.R_OeisA249609_conjecture_R1_H2_R1.H1 := by
  intro large small n hn hnodd hweight hne
  let e := Nat.log 2 n
  let c := 2^(e+1)-n
  have hlow : 2^e ≤ n := Nat.pow_log_le_self 2 hn.ne'
  have hupp : n < 2^(e+1) := Nat.lt_pow_succ_log_self (by decide) n
  have hsum : n+c = 2^(e+1) := by dsimp [c]; omega
  have hform : 2^(e+1)-c = n := by omega
  have hc : 0 < c := by omega
  have hcle : c ≤ 2^e := by rw [pow_succ] at hsum; omega
  have hcodd : Odd c := by
    apply Nat.odd_iff.mpr
    have hr := Nat.odd_iff.mp hnodd
    rw [pow_succ] at hsum
    omega
  by_cases one : c = 1
  · have he : 4 ≤ e+1 := by
      by_contra! h
      have cases : e=0 ∨ e=1 ∨ e=2 := by omega
      rcases cases with he|he|he <;> rw [he,one] at hsum <;> norm_num at hsum
      · apply hne; rw [show n=1 by omega]; decide
      · have bad : OeisA249609.isEvil 3 = false := (show n=3 by omega) ▸ hweight
        exact (by decide : ¬ OeisA249609.isEvil 3 = false) bad
      · apply hne; rw [show n=7 by omega]; decide
    have hrow : n = 2^(e+1)-1 := by omega
    obtain ⟨k,hk,hkGood⟩ := witness (e+1) he
    have hk8 : 1 ≤ k ∧ k ≤ 8 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      omega
    have hl := Nat.pow_le_pow_right (by decide : 0 < 2) he
    refine ⟨k,List.mem_range'_1.mpr ⟨hk8.1,by omega⟩, ?_⟩
    simpa only [hrow] using hkGood
  · have hc' : 1 < c := by omega
    by_cases hcut : c*(c+1)<2^(e+1)
    · by_cases hw : OeisA249609.isEvil (c*(c+1)) = true
      · rcases columns_one_two (e+1) c n hcodd hcut hsum hw with h|h
        · exact ⟨1,List.mem_range'_1.mpr ⟨by decide, by omega⟩, h⟩
        · exact ⟨2,List.mem_range'_1.mpr ⟨by decide, by omega⟩, h⟩
      · simpa only [hform] using small e c hc' hcle hcodd hcut (by simpa using hw)
          (by simpa only [hform] using hweight)
    · simpa only [hform] using large e c hc' hcle hcodd (by omega) (by simpa only [hform] using hweight)

end OMA.R_OeisA249609_conjecture_R1_H2_R1_H1_R1
