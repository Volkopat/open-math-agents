import OMAReductions.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H1_R1_H3_R1_H1_R1_H1_R1
import Mathlib.Tactic

-- Credit: @AlfredMelson. Uses the periodic_column lemma of @PanPapag and the
-- binary xor certificate from the merged column-18/19 reduction by @FransDevelopment.
namespace OMA.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H1_R1_H3_R1_H1_R1_H1_R1_H1_R1
open OMA.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H1_R1

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

private def parityFold : ℕ → ℕ → ℕ := Nat.rec (motive := fun _ => ℕ → ℕ) (fun v => (Nat.digits 2 v).count 1 % 2)
      (fun j f v => let base := (1 : ℕ) <<< (8 * 2^j); f ((v / base) ^^^ (v % base)))

private theorem parityFold_spec (j v : ℕ) : parityFold j v = (Nat.digits 2 v).count 1 % 2 := by
    induction j generalizing v with
    | zero => rfl
    | succ j ih =>
      let w := 8*2^j
      change parityFold j ((v / (1 <<< w)) ^^^ (v % (1 <<< w))) = _
      rw [Nat.shiftLeft_eq, Nat.one_mul]
      rw [ih,xor_weight]
      have hh := count_ones_append (v / 2^w) w (v%2^w) (Nat.mod_lt _ (by positivity))
      rw [Nat.div_add_mod'] at hh
      exact congrArg (· % 2) hh.symm

private def ones (x : ℕ) := (Nat.digits 2 x).count 1
private def state (d x : ℕ) := (x%d, ones (x/d)%2)
private def appendState (d : ℕ) (s : ℕ × ℕ) (w c : ℕ) : ℕ × ℕ :=
  let v := s.1 * 2^w + c
  (v%d, (s.2 + parityFold 20 (v/d))%2)
private theorem state_join {d : ℕ} (hd : 0 < d) (x w c : ℕ) (hc : c < 2^w) :
    state d (x*2^w+c) = appendState d (state d x) w c := by
  simp only [appendState, parityFold_spec, Nat.add_mod_mod]
  have ones_join (u w c : ℕ) (hc : c < 2^w) :
      ones (u*2^w+c) = ones u + ones c := count_ones_append u w c hc
  have he : x*2^w+c = (x%d * 2^w+c) + (x/d * 2^w)*d := by
    calc
      x*2^w+c = (x%d+d*(x/d))*2^w+c := by rw [Nat.mod_add_div]
      _ = _ := by ring
  have hv : (x%d * 2^w+c)/d < 2^w := by
    apply (Nat.div_lt_iff_lt_mul hd).mpr
    have h := Nat.mul_le_mul_right (2^w) (Nat.succ_le_of_lt (Nat.mod_lt x hd))
    rw [Nat.succ_mul] at h
    nlinarith only [h,hc]
  change state d (x*2^w+c) = ((x%d * 2^w+c)%d, ((state d x).2 + ones ((x%d * 2^w+c)/d))%2)
  unfold state
  rw [he, Nat.add_mul_mod_self_right, Nat.add_mul_div_right _ _ hd,
      Nat.add_comm ((x % d * 2 ^ w + c) / d), ones_join _ _ _ hv]
  simp [Nat.add_mod]

private def fill (b : Bool) (w : ℕ) : ℕ := if b then 2^w-1 else 0

private theorem fill_lt (b : Bool) (w : ℕ) : fill b w < 2^w := by
    have : 0 < 2^w := by positivity
    cases b <;> simp [fill]

private theorem fill_add (b : Bool) (w u : ℕ) :
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


private def fillState (d : ℕ) (b : Bool) : ℕ → ℕ × ℕ → ℕ → ℕ × ℕ
  | 0, s, w => appendState d s w (fill b w)
  | j+1, s, w =>
    let u := w/2
    fillState d b j (fillState d b j s u) (w-u)

private theorem fillState_spec {d : ℕ} (hd : 0 < d) (b : Bool) (j x w : ℕ) :
    fillState d b j (state d x) w = state d (x*2^w + fill b w) := by
  induction j generalizing x w with
  | zero => exact (state_join hd x w _ (fill_lt b w)).symm
  | succ j ih =>
    rw [fillState, ih, ih]
    have hw : w/2 + (w-w/2) = w := by omega
    congr 1
    conv_rhs => rw [← hw, fill_add, pow_add]
    ring

private def digitStates (d w : ℕ) (ds : List (Bool × ℕ)) :=
  ds.foldr (fun e s => appendState d (fillState d e.1 3 s w) 64 e.2) (0,0)
private theorem digitStates_spec {d : ℕ} (hd : 0 < d) (w : ℕ) (ds : List (Bool × ℕ))
    (hc : ∀ e ∈ ds, e.2 < 2^64) :
    digitStates d w ds = state d (ds.foldr
      (fun e n => (n*2^w + fill e.1 w)*2^64+e.2) 0) := by
  induction ds with
  | nil => simp [digitStates, state, ones]
  | cons e ds ih =>
    change appendState d (fillState d e.1 3 (digitStates d w ds) w) 64 e.2 = _
    rw [ih (fun v hv => hc v (by simp [hv])), fillState_spec hd, ← state_join hd _ _ _ (hc e (by simp))]
    rfl
set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
private theorem falling20 (x B : ℕ) (hx : 0 < x) (hB : B = 18446744073709551616) :
    ([(false, 0), (true, 18325098973300719616), (false, 431565146817638399), (true, 17778134343368398336), (false, 610116075740491775), (true, 18075359286364323616), (false, 161429736530118959), (true, 18394483170347038896), (false, 12953636989943895), (true, 18444240214954084066), (false, 381922055502194), (true, 18446697793061799706), (false, 4465226757380), (true, 18446743731457039716), (false, 20692933629), (true, 18446744072735609716), (false, 34916945), (true, 18446744073708631066), (false, 16814), (true, 18446744073709551426)] : List (Bool × ℕ)).foldr (fun s n => (n*x + (if s.1 then x-1 else 0))*B + s.2) 0 =
      (x*B).descFactorial 20 := by
  let low (n c : ℕ) := (n*x+0)*B+c
  let high (n c : ℕ) := (n*x+(x-1))*B+c
  calc
    _ = (low (high (low (high (low (high (low (high (low (high (low (high (low (high (low (high (low (high (low (high 0 18446744073709551426) 16814) 18446744073708631066) 34916945) 18446744072735609716) 20692933629) 18446743731457039716) 4465226757380) 18446697793061799706) 381922055502194) 18444240214954084066) 12953636989943895) 18394483170347038896) 161429736530118959) 18075359286364323616) 610116075740491775) 17778134343368398336) 431565146817638399) 18325098973300719616) 0) := rfl
    _ = _ := by
      dsimp only [low, high]
      rw [hB]
      apply Int.ofNat_inj.mp
      norm_num [Nat.descFactorial]
      simp (disch := omega) only [Nat.cast_sub, Nat.cast_mul, Nat.cast_ofNat]
      ring

private theorem compute20 (r : ℕ) (hr : 64 ≤ r)
    (cert : (digitStates 9280784638125 (r-64) [(false, 0), (true, 18325098973300719616), (false, 431565146817638399), (true, 17778134343368398336), (false, 610116075740491775), (true, 18075359286364323616), (false, 161429736530118959), (true, 18394483170347038896), (false, 12953636989943895), (true, 18444240214954084066), (false, 381922055502194), (true, 18446697793061799706), (false, 4465226757380), (true, 18446743731457039716), (false, 20692933629), (true, 18446744072735609716), (false, 34916945), (true, 18446744073708631066), (false, 16814), (true, 18446744073709551426)]).2 = 0) :
    (Nat.digits 2 ((2^r).descFactorial 20 / 9280784638125)).count 1 % 2 = 0 := by
  have h := digitStates_spec (d := 9280784638125) (by decide) (r-64) [(false, 0), (true, 18325098973300719616), (false, 431565146817638399), (true, 17778134343368398336), (false, 610116075740491775), (true, 18075359286364323616), (false, 161429736530118959), (true, 18394483170347038896), (false, 12953636989943895), (true, 18444240214954084066), (false, 381922055502194), (true, 18446697793061799706), (false, 4465226757380), (true, 18446743731457039716), (false, 20692933629), (true, 18446744072735609716), (false, 34916945), (true, 18446744073708631066), (false, 16814), (true, 18446744073709551426)] (by decide)
  have e := falling20 (2^(r-64)) (2^64) (by positivity) rfl
  change _ = (2^(r-64)*2^64).descFactorial 20 at e
  rw [← pow_add, Nat.sub_add_cancel hr] at e
  rw [h] at cert
  simpa only [fill, e, state, ones] using cert

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
private theorem hit20 (a : ℕ) (ha : 64 ≤ a)
    (hr : (a-64)%30618000+64 ∈ ([21457985, 27581585, 3767585, 9891185, 16014785, 22138385, 28261985, 5468585, 11592185, 17715785, 23839385, 29962985, 5808785, 24179585] : List ℕ)) :
    OeisA249609.isEvil ((2^a).choose 20) = true := by
  apply (periodic_column (a:=a) (k:=20) (t:=64) (l:=15309000) (d:=9280784638125) (z:=18)
    (ds:=([(false, 0), (true, 18325098973300719616), (false, 431565146817638399), (true, 17778134343368398336), (false, 610116075740491775), (true, 18075359286364323616), (false, 161429736530118959), (true, 18394483170347038896), (false, 12953636989943895), (true, 18444240214954084066), (false, 381922055502194), (true, 18446697793061799706), (false, 4465226757380), (true, 18446743731457039716), (false, 20692933629), (true, 18446744072735609716), (false, 34916945), (true, 18446744073708631066), (false, 16814), (true, 18446744073709551426)] : List (Bool × ℕ))) ha (by decide) (by decide +kernel) (by decide)
    (fun w => by rw [pow_add]; exact falling20 (2^w) (2^64) (by positivity) (by decide))
    (by decide)).2
  generalize (a-64)%30618000+64 = r at *
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> apply compute20 _ (by decide) <;> decide +kernel

def H1 : Prop := ∀ q : ℕ, q % 9450 ∈ ([952, 2842, 4732] : List ℕ) →
  ∃ k ∈ List.range' 1 (2 ^ (3240*q+2705)), OeisA249609.isEvil ((2 ^ (3240*q+2705)).choose k) = true

def H2 : Prop := ∀ q : ℕ, q % 9450 ∈ ([3682, 5572, 9352] : List ℕ) →
  ∃ k ∈ List.range' 1 (2 ^ (3240*q+2705)), OeisA249609.isEvil ((2 ^ (3240*q+2705)).choose k) = true

theorem main : H1 → H2 → OMA.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H1_R1_H3_R1_H1_R1_H1_R1.H1 := by
  intro h1 h2 q hq
  have hit (h : (3240*q+2705-64)%30618000+64 ∈ ([21457985, 27581585, 3767585, 9891185, 16014785, 22138385, 28261985, 5468585, 11592185, 17715785, 23839385, 29962985, 5808785, 24179585] : List ℕ)) : ∃ k ∈ List.range' 1 (2 ^ (3240*q+2705)), OeisA249609.isEvil ((2 ^ (3240*q+2705)).choose k) = true := by
    refine ⟨20, List.mem_range'_1.mpr ⟨by decide, ?_⟩, hit20 _ (by omega) h⟩
    have := Nat.pow_le_pow_right (by decide : 0 < 2) (show 5 ≤ 3240*q+2705 by omega)
    omega
  have he := Nat.mod_add_div q 1890
  have hf := Nat.mod_add_div (q/1890) 5
  have hg := Nat.mod_lt (q/1890) (by decide : 0 < 5)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with h|h|h|h <;> generalize hh : q / 1890 % 5 = j at hg <;> interval_cases j
  · apply h1 q
    rw [show q%9450 = 952 by omega]
    decide
  · apply h1 q
    rw [show q%9450 = 2842 by omega]
    decide
  · apply h1 q
    rw [show q%9450 = 4732 by omega]
    decide
  · apply hit
    rw [show (3240*q+2705-64)%30618000+64 = 21457985 by omega]
    decide
  · apply hit
    rw [show (3240*q+2705-64)%30618000+64 = 27581585 by omega]
    decide
  · apply hit
    rw [show (3240*q+2705-64)%30618000+64 = 3767585 by omega]
    decide
  · apply hit
    rw [show (3240*q+2705-64)%30618000+64 = 9891185 by omega]
    decide
  · apply hit
    rw [show (3240*q+2705-64)%30618000+64 = 16014785 by omega]
    decide
  · apply hit
    rw [show (3240*q+2705-64)%30618000+64 = 22138385 by omega]
    decide
  · apply hit
    rw [show (3240*q+2705-64)%30618000+64 = 28261985 by omega]
    decide
  · apply hit
    rw [show (3240*q+2705-64)%30618000+64 = 5468585 by omega]
    decide
  · apply hit
    rw [show (3240*q+2705-64)%30618000+64 = 11592185 by omega]
    decide
  · apply hit
    rw [show (3240*q+2705-64)%30618000+64 = 17715785 by omega]
    decide
  · apply hit
    rw [show (3240*q+2705-64)%30618000+64 = 23839385 by omega]
    decide
  · apply hit
    rw [show (3240*q+2705-64)%30618000+64 = 29962985 by omega]
    decide
  · apply hit
    rw [show (3240*q+2705-64)%30618000+64 = 5808785 by omega]
    decide
  · apply h2 q
    rw [show q%9450 = 3682 by omega]
    decide
  · apply h2 q
    rw [show q%9450 = 5572 by omega]
    decide
  · apply hit
    rw [show (3240*q+2705-64)%30618000+64 = 24179585 by omega]
    decide
  · apply h2 q
    rw [show q%9450 = 9352 by omega]
    decide

end OMA.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H1_R1_H3_R1_H1_R1_H1_R1_H1_R1
