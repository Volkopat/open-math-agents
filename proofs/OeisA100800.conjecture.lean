import FormalConjectures.OEIS.«100800»

-- Problem: Conjectures associated with A100800
-- Upstream: formal-conjectures FormalConjectures/OEIS/100800.lean:87 (declaration OeisA100800.conjecture)
-- Credit: @waspflannel (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

-- Proof found by the lemmata harness (Codex fork) with gpt-6.2-astra and verified by Lean.

namespace OeisA100800
open Nat Function

theorem iter_ge_seed (n j : ℕ) : n ≤ f^[j] n := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact ih.trans (Nat.le_add_right _ _)

theorem positive_return {n : ℕ} (hn : n ≠ 0) :
    a n ≠ 0 ↔ ∃ k : ℕ, n ∣ f^[k+1] n := by
  classical
  unfold a
  dsimp only
  split_ifs with h
  · exact iff_of_true (Nat.ne_of_gt ((Nat.pos_of_ne_zero hn).trans_le (iter_ge_seed _ _))) h
  · exact iff_of_false (fun he => he rfl) h

theorem f_mod9 (n : ℕ) : f n ≡ 2*n [MOD 9] := by
  simpa only [f, sumDigits, two_mul] using (Nat.modEq_nine_digits_sum n).symm.add_left n

theorem iter_mod9 (n j : ℕ) : f^[j] n ≡ 2^j*n [MOD 9] := by
  induction j with
  | zero => simp [Nat.ModEq]
  | succ j ih =>
    rw [Function.iterate_succ_apply', pow_succ']
    simpa only [mul_assoc] using (f_mod9 _).trans (ih.mul_left 2)
end OeisA100800

namespace OeisA100800

theorem sum_low_digit (d h : ℕ) (hd : d < 10) : sumDigits (d + 10*h) = d + sumDigits h := by
  by_cases H : d ≠ 0 ∨ h ≠ 0
  · rw [sumDigits, Nat.digits_add 10 (by decide) d h hd H]; rfl
  · push Not at H; simp [H.1,H.2]

theorem sum_block (e h r : ℕ) (hr : r < 10^e) :
    sumDigits (r + 10^e * h) = sumDigits r + sumDigits h := by
  induction e generalizing r with
  | zero => simp_all [sumDigits]
  | succ e ih =>
    have hr' : r / 10 < 10^e := (Nat.div_lt_iff_lt_mul (by decide : 0 < 10)).2 (by simpa [pow_succ] using hr)
    have hmod := Nat.mod_lt r (by decide : 0 < 10)
    have H := Nat.mod_add_div r 10
    have H' : r + 10^(e+1)*h = r%10 + 10*(r/10 + 10^e*h) := by rw [mul_add, pow_succ', mul_assoc]; omega
    rw [H', sum_low_digit _ _ hmod, ih _ hr', ← Nat.add_assoc, ← sum_low_digit _ _ hmod, H]

def nines (p : ℕ) : ℕ → ℕ
  | 0 => p
  | t+1 => 9 + 10*nines p t

theorem nines_sum (p t : ℕ) : sumDigits (nines p t) = sumDigits p + 9*t := by
  induction t with
  | zero => simp [nines]
  | succ t ih => rw [nines, sum_low_digit _ _ (by decide), ih]; omega

theorem nines_succ (p t : ℕ) : nines p t + 1 = 10^t*(p+1) := by
  induction t with
  | zero => simp [nines]
  | succ t ih => rw [nines, pow_succ', Nat.mul_assoc, ← ih]; omega
end OeisA100800

namespace OeisA100800
open Function

theorem sum_pos {x : ℕ} (hx : x ≠ 0) : 0 < sumDigits x := by
  have h := Nat.getLast_digit_ne_zero 10 hx
  exact (Nat.pos_of_ne_zero h).trans_le (List.single_le_sum (fun _ _ => Nat.zero_le _) _ (List.getLast_mem _))

theorem first_slice {n A E : ℕ} (hn : 0 < n) (hnA : n < A)
    (hE : ∀ x < A, sumDigits x ≤ E) :
    ∃ j r, f^[j+1] n = r+A ∧ r ≤ E := by
  have grow (j : ℕ) : n+j ≤ f^[j] n := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [iterate_succ_apply', f]
      have hp := sum_pos (Nat.ne_of_gt (hn.trans_le (iter_ge_seed n j)))
      omega
  have hex : ∃ j, A ≤ f^[j] n := ⟨A,by have := grow A; omega⟩
  have hhit := Nat.find_spec hex
  cases hi : Nat.find hex with
  | zero => simp [hi] at hhit; omega
  | succ j =>
    have hpre : f^[j] n < A := lt_of_not_ge (Nat.find_min hex (by omega : j < Nat.find hex))
    rw [hi] at hhit
    refine ⟨j, f^[j+1] n - A, (Nat.sub_add_cancel hhit).symm, ?_⟩
    rw [iterate_succ_apply', f]
    have := hE _ hpre; omega

inductive HitsEnd (b h : ℕ) : ℕ → Prop
  | endpt : HitsEnd b h (10^b)
  | from_step (r : ℕ) (hr : r < 10^b) (later : HitsEnd b h (r + h + sumDigits r)) : HitsEnd b h r

theorem lift_end {b p r : ℕ} (h : HitsEnd b (sumDigits p) r) :
    ∃ i, f^[i] (r+10^b*p) = 10^b+10^b*p := by
  induction h with
  | endpt => exact ⟨0,rfl⟩
  | from_step r hr h ih =>
    obtain ⟨i,hi⟩ := ih
    refine ⟨i+1,?_⟩
    rw [iterate_succ_apply, f, sum_block _ _ _ hr]
    convert hi using 2; ring

theorem catching_block {n p b E : ℕ} (hn : 0 < n) (hA : n < 10^b*p)
    (hd : n ∣ 10^b+10^b*p) (hE : ∀ x < 10^b*p, sumDigits x ≤ E)
    (catchAll : ∀ r ≤ E, (sumDigits p + r).gcd 9 = n.gcd 9 → HitsEnd b (sumDigits p) r) : a n ≠ 0 := by
  obtain ⟨j,r,he,hr⟩ := first_slice hn hA hE
  have h9 : 10^b ≡ 1 [MOD 9] := by simpa using (show 10 ≡ 1 [MOD 9] by decide).pow b
  have hm : r + 10^b*p ≡ sumDigits p + r [MOD 9] := by
    simpa [add_comm,sumDigits] using ((h9.mul (Nat.modEq_nine_digits_sum p)).add_left r)
  have hg := (hm.symm.trans ((he ▸ iter_mod9 n (j+1)) : r+10^b*p ≡ 2^(j+1)*n [MOD 9])).gcd_eq
  rw [Nat.Coprime.gcd_mul_left_cancel _ ((show Nat.Coprime 2 9 by decide).pow_left _)] at hg
  obtain ⟨i,hi⟩ := lift_end (catchAll r hr hg)
  apply (positive_return hn.ne').mpr
  refine ⟨i+j,?_⟩
  rwa [Nat.add_assoc, iterate_add_apply, he, hi]
end OeisA100800

namespace OeisA100800

def dsum : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k+1, x => x%10 + dsum k (x/10)

theorem dsum_correct (k x : ℕ) (hx : x < 10^k) : dsum k x = sumDigits x := by
  induction k generalizing x with
  | zero => simp_all [dsum,sumDigits]
  | succ k ih =>
    have hx' := (Nat.div_lt_iff_lt_mul (by decide : 0 < 10)).2 (show x < 10^k * 10 by simpa [pow_succ] using hx)
    rw [dsum, ih _ hx', ← sum_low_digit _ _ (Nat.mod_lt _ (by decide)), Nat.mod_add_div]

theorem dsum_upper (k x : ℕ) : dsum k x ≤ 9*k := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => rw [dsum]; have := ih (x/10); omega

inductive Flow (T h : ℕ) : ℕ → ℕ → Prop where
  | stay (r : ℕ) : Flow T h r r
  | step (r : ℕ) (hr : r < T) {y : ℕ} (tail : Flow T h (r+h+sumDigits r) y) : Flow T h r y

theorem Flow.trans {T h r z y : ℕ} (a : Flow T h r z) (b : Flow T h z y) : Flow T h r y := by
  induction a with
  | stay => exact b
  | step r hr _ ih => exact .step r hr (ih b)

theorem Flow.shift {d h j r y : ℕ} (a : Flow (10^d) (h+j) r y) (hj : j < 10) :
    Flow (10^(d+1)) h (r+10^d*j) (y+10^d*j) := by
  have hsj : sumDigits j = j := by simpa [sumDigits] using (sum_low_digit j 0 hj)
  induction a with
  | stay => exact .stay _
  | step r hr _ ih =>
    apply Flow.step
    · rw [pow_succ]; nlinarith only [hr, Nat.mul_le_mul_left (10^d) (show j+1 ≤ 10 by omega)]
    · rw [sum_block _ _ _ hr, hsj]; convert ih using 1; omega

def overshoot : ℕ → ℕ → ℕ → ℕ
  | 0,h,r => if r=0 then h-1 else r-1
  | d+1,h,r =>
    let B := 10^(d+1)
    if B ≤ r then r-B else if B ≤ r+h then r+h+dsum (d+1) r - B
    else Nat.rec r (fun j z => overshoot d (h+j) z) 10

theorem over_correct (d h r : ℕ) (hh : 0 < h) : Flow (10^d) h r (overshoot d h r + 10^d) := by
  induction d generalizing h r with
  | zero =>
    rw [pow_zero, overshoot]
    split_ifs with hz
    · subst r
      apply Flow.step _ (by decide)
      simp [sumDigits, Nat.sub_add_cancel (by omega : 1 ≤ h), Flow.stay]
    · rw [Nat.sub_add_cancel (by omega)]; exact .stay _
  | succ d ih =>
    rw [overshoot]
    split_ifs with h1 h2
    · rw [Nat.sub_add_cancel h1]; exact .stay _
    · apply Flow.step _ (by omega)
      rw [dsum_correct _ _ (by omega),Nat.sub_add_cancel (by omega)]
      exact .stay _
    · let z (i : ℕ) : ℕ := Nat.rec r (fun j w => overshoot d (h+j) w) i
      have H (j : ℕ) (hj : j ≤ 10) : Flow (10^(d+1)) h r (z j + 10^d*j) := by
        induction j with
        | zero => simpa [z] using Flow.stay (T:=10^(d+1)) (h:=h) r
        | succ j J =>
          have s := (ih (h+j) (z j) (by omega)).shift (by omega : j<10)
          apply (J (by omega)).trans
          convert s using 1
          change overshoot d (h+j) (z j) + 10^d*(j+1) = (overshoot d (h+j) (z j) + 10^d) + 10^d*j
          ring
      simpa only [z, pow_succ] using H 10 (by decide)

theorem Flow.exact_end {b h r y : ℕ} (a : Flow (10^b) h r y) (hy : HitsEnd b h y) : HitsEnd b h r := by
  induction a with
  | stay => exact hy
  | step r hr _ ih => exact .from_step r hr (ih hy)

theorem of_over_zero {b h r : ℕ} (hh : 0<h) (hz : overshoot b h r = 0) : HitsEnd b h r := by
  have H := over_correct b h r hh
  rw [hz,zero_add] at H
  exact H.exact_end .endpt
end OeisA100800

namespace OeisA100800

def catchesB (b h g E : ℕ) := (List.range (E+1)).all fun r => ((h+r).gcd 9 != g) || (overshoot b h r == 0)

theorem weight_transfer {n q K h b E : ℕ} (hn : 0 < n) (hq : 0 < q) (hsize : n*q ≤ 10^K)
    (hroom : 9*K < h) (hcon : n*q ≡ h+1 [MOD 9]) (hE : h+9*(b+K) ≤ E)
    (hc : catchesB b h (n.gcd 9) E = true) : a n ≠ 0 := by
  let z := n*q-1
  have hz : z+1=n*q := Nat.sub_add_cancel (Nat.mul_pos hn hq)
  have hzK : z < 10^K := by omega
  have hsd : sumDigits z ≤ 9*K := (dsum_correct K z hzK) ▸ dsum_upper K z
  have hs9 := (Nat.modEq_nine_digits_sum z).symm.add_right 1
  rw [hz] at hs9
  have hsh : sumDigits z ≡ h [MOD 9] := Nat.ModEq.add_right_cancel' 1 (hs9.trans hcon)
  obtain ⟨t,ht⟩ := (Nat.modEq_iff_exists_eq_add (by omega : sumDigits z ≤ h)).mp hsh
  let p := nines z t
  have hps : sumDigits p = h := (nines_sum z t).trans ht.symm
  have hp : p+1 = 10^t*(n*q) := by simpa only [p, hz] using nines_succ z t
  have ht1 : 1 ≤ t := by omega
  have ht10 : 10 ≤ 10^t := (show 10^1 ≤ 10^t from Nat.pow_le_pow_right (by decide) ht1)
  have hnq : n ≤ n*q := Nat.le_mul_of_pos_right _ hq
  have hnp : n < p := by have := Nat.mul_le_mul ht10 hnq; nlinarith
  have hb1 : 0 < 10^b := by positivity
  apply catching_block (p:=p) (b:=b) (E:=E) hn (hnp.trans_le (Nat.le_mul_of_pos_left _ hb1))
  · rw [show 10^b+10^b*p = 10^b*(p+1) by ring, hp]
    exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right (dvd_mul_right _ _) _) _
  · intro x hx
    have bound : x < 10^(b+t+K) := calc
      x < 10^b*p := hx
      _ ≤ 10^b*(p+1) := Nat.mul_le_mul_left _ (by omega)
      _ = 10^b*(10^t*(n*q)) := by rw [hp]
      _ ≤ 10^b*(10^t*10^K) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hsize)
      _ = 10^(b+t+K) := by rw [pow_add, pow_add, Nat.mul_assoc]
    have H := dsum_upper (b+t+K) x
    rw [dsum_correct _ _ bound] at H
    omega
  · intro r hr hg
    rw [hps] at hg ⊢
    have H := List.all_eq_true.mp hc r (List.mem_range.mpr (by omega))
    simp only [hg, bne_self_eq_false, Bool.false_or, beq_iff_eq] at H
    exact of_over_zero (by omega) H
end OeisA100800

namespace OeisA100800
open Function

theorem first_guard {n A E : ℕ} (hn : 0<n) (hnA : n<A) (guard : ∀ x < A, f x ≤ A+E) :
    ∃ j r, f^[j+1] n = r + A ∧ r ≤ E := by
  have grow (j : ℕ) : n+j ≤ f^[j] n := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [iterate_succ_apply', f]
      have hp := sum_pos (Nat.ne_of_gt (hn.trans_le (iter_ge_seed n j)))
      omega
  have hex : ∃ j, A ≤ f^[j] n := ⟨A, by have := grow A; omega⟩
  have hhit := Nat.find_spec hex
  cases hi : Nat.find hex with
  | zero => simp [hi] at hhit; omega
  | succ j =>
    have hpre : f^[j] n < A := lt_of_not_ge (Nat.find_min hex (by omega : j < Nat.find hex))
    rw [hi] at hhit
    refine ⟨j, f^[j+1] n - A, (Nat.sub_add_cancel hhit).symm, ?_⟩
    rw [iterate_succ_apply']; have := guard _ hpre; omega

theorem guard_capture {n p b E h : ℕ} (hn : 0<n) (hA : n<10^b*p) (hp : sumDigits p = h) (hh : 0<h)
    (hd : n ∣ 10^b+10^b*p) (guard : ∀ x < 10^b*p, f x ≤ 10^b*p + E)
    (cap : catchesB b h (n.gcd 9) E = true) : a n ≠ 0 := by
  obtain ⟨j,r,he,hr⟩ := first_guard hn hA guard
  have h9 : 10^b ≡ 1 [MOD 9] := by simpa using (show 10 ≡ 1 [MOD 9] by decide).pow b
  have hm : r + 10^b*p ≡ h + r [MOD 9] := by
    rw [← hp]
    simpa [add_comm,sumDigits] using ((h9.mul (Nat.modEq_nine_digits_sum p)).add_left r)
  have hg := (hm.symm.trans ((he ▸ iter_mod9 n (j+1)) : r+10^b*p ≡ 2^(j+1)*n [MOD 9])).gcd_eq
  rw [Nat.Coprime.gcd_mul_left_cancel _ ((show Nat.Coprime 2 9 by decide).pow_left _)] at hg
  have H := List.all_eq_true.mp cap r (List.mem_range.mpr (by omega))
  simp only [hg, bne_self_eq_false, Bool.false_or, beq_iff_eq] at H
  have HH : HitsEnd b (sumDigits p) r := hp ▸ of_over_zero hh H
  obtain ⟨i,hi⟩ := lift_end HH
  apply (positive_return hn.ne').mpr
  refine ⟨i+j,?_⟩
  rwa [Nat.add_assoc, iterate_add_apply, he, hi]
end OeisA100800

namespace OeisA100800
open Function

theorem Flow.activate {b p r y : ℕ} (H : Flow (10^b) (sumDigits p) r y) :
    ∃ i, f^[i] (r+10^b*p) = y+10^b*p := by
  induction H with
  | stay => exact ⟨0,rfl⟩
  | step r hr _ ih =>
    obtain ⟨i,hi⟩ := ih
    refine ⟨i+1,?_⟩
    rw [iterate_succ_apply,f,sum_block _ _ _ hr]
    convert hi using 2; ring

theorem common_landmark {n p b E h y : ℕ} (hn : 0<n) (hnA : n<10^b*p) (hp : sumDigits p=h)
    (hd : n ∣ y+10^b*p) (hg : ∀ x < 10^b*p, f x ≤ 10^b*p+E)
    (trace : ∀ r ≤ E, (h+r).gcd 9 = n.gcd 9 → Flow (10^b) h r y) : a n ≠ 0 := by
  obtain ⟨j,r,he,hr⟩ := first_guard hn hnA hg
  have h9 : 10^b ≡ 1 [MOD 9] := by simpa using (show 10 ≡ 1 [MOD 9] by decide).pow b
  have hm : r+10^b*p ≡ h+r [MOD 9] := by
    rw [←hp]; simpa [add_comm,sumDigits] using ((h9.mul (Nat.modEq_nine_digits_sum p)).add_left r)
  have he9 := (hm.symm.trans ((he ▸ iter_mod9 n (j+1)) : r+10^b*p ≡ 2^(j+1)*n [MOD 9])).gcd_eq
  rw [Nat.Coprime.gcd_mul_left_cancel _ ((show Nat.Coprime 2 9 by decide).pow_left _)] at he9
  have H : Flow (10^b) (sumDigits p) r y := hp ▸ trace r hr he9
  obtain ⟨i,hi⟩ := H.activate
  apply (positive_return hn.ne').mpr
  refine ⟨i+j,?_⟩
  rwa [Nat.add_assoc, iterate_add_apply, he, hi]
end OeisA100800

namespace OeisA100800.Carry
open OeisA100800

theorem pow_one9 (b : ℕ) : 10^b ≡ 1 [MOD 9] := by simpa using (show 10 ≡ 1 [MOD 9] by decide).pow b

theorem flow_bounds {b H r v g : ℕ} (F : Flow (10^b) (9*H) r v) (gg : g ∣ 9)
    (rd : g ∣ r) (hstart : r < 10^b + 9*(H+b)) : g ∣ v ∧ v < 10^b + 9*(H+b) := by
  induction F with
  | stay x => exact ⟨rd,hstart⟩
  | step x hx _ ih =>
    have sx : g ∣ sumDigits x := Nat.modEq_zero_iff_dvd.mp (((Nat.modEq_nine_digits_sum x).symm.of_dvd gg).trans (Nat.modEq_zero_iff_dvd.mpr rd))
    have hb := dsum_upper b x
    rw [dsum_correct b x hx] at hb
    exact ih (dvd_add (dvd_add rd (dvd_mul_of_dvd_left gg _)) sx) (by omega)

theorem phase_exists {n c u : ℕ} (hn : 0<n) (hc : n.gcd 9 ∣ c) (hu : n.gcd 9 ∣ u) : ∃ t<n, c ≡ u+9*t [MOD n] := by
  have h := (Nat.modEq_zero_iff_dvd.mpr hc).trans (Nat.modEq_zero_iff_dvd.mpr hu).symm
  obtain ⟨v,hnv,h9v⟩ := Nat.chineseRemainder' (n:=n) (m:=9) h
  let w := v + 9*n*u
  have w9 : w ≡ u [MOD 9] := by simpa [w, Nat.ModEq, Nat.add_mod, Nat.mul_assoc] using h9v
  have wn : w ≡ c [MOD n] := by simpa [w, Nat.ModEq, Nat.add_mod, mul_comm 9 n, Nat.mul_assoc] using hnv
  have lew : u ≤ w := by dsimp [w]; nlinarith
  obtain ⟨j,hj⟩ := (Nat.modEq_iff_exists_eq_add lew).mp w9.symm
  refine ⟨j%n,Nat.mod_lt _ hn,wn.symm.trans ?_⟩
  rw [hj]; exact ((Nat.mod_modEq j n).symm.mul_left 9).add_left u

theorem route_exit {n H b r u : ℕ} (hn : 0<n) (hh : 0<H) (hB : 9*(H+b)<10^b) (hr : r<10^b)
    (rd : n.gcd 9 ∣ r) (ud : n.gcd 9 ∣ u) : let z := overshoot b (9*H) r
    z < 10^b ∧ n.gcd 9 ∣ z+10^b ∧ ∃ t<n, z+10^b+sumDigits z+9*H+1 ≡ u+9*t [MOD n] := by
  dsimp only
  let z := overshoot b (9*H) r
  obtain ⟨hd,zb⟩ := flow_bounds (over_correct b (9*H) r (by omega)) (Nat.gcd_dvd_right n 9) rd (by omega)
  change n.gcd 9 ∣ z+10^b at hd
  change z+10^b < _ at zb
  refine ⟨by omega,hd,phase_exists hn ?_ ud⟩
  have hz : sumDigits z + 1 ≡ z+10^b [MOD 9] := (Nat.modEq_nine_digits_sum z).symm.add (pow_one9 b).symm
  have ha := Nat.modEq_zero_iff_dvd.mp ((hz.of_dvd (Nat.gcd_dvd_right n 9)).trans (Nat.modEq_zero_iff_dvd.mpr hd))
  have hsum := dvd_add (dvd_add hd ha) (dvd_mul_of_dvd_left (Nat.gcd_dvd_right n 9) H)
  have e : overshoot b (9*H) r + 10^b + sumDigits (overshoot b (9*H) r) + 9*H + 1 = z + 10^b + (sumDigits z + 1) + 9*H := by
    simp only [z]; ring
  rw [e]; exact hsum
end OeisA100800.Carry

namespace OeisA100800.Carry

def cap (n k s : ℕ) : ℕ := s + (s-n*k)*k

theorem capacity_step {n k s : ℕ} : ∃ d, cap n k (s+1) ≤ cap n k s + d + 1 ∧ d*n ≤ cap n k s := by
  by_cases hs : s<n*k
  · refine ⟨0,?_,by simp⟩
    simp [cap, Nat.sub_eq_zero_of_le (by omega : s+1 ≤ n*k), Nat.sub_eq_zero_of_le hs.le]
  · refine ⟨k,?_,?_⟩
    · rw [cap, cap, show s+1-n*k = (s-n*k)+1 by omega, Nat.add_mul]; omega
    · unfold cap; rw [mul_comm k n]; omega

theorem shrink {α : Type*} {S : Finset α} {n k s : ℕ} (hn : 0<n) (hc : S.card ≤ cap n k (s+1))
    (pick : α → ℕ) (hp : ∀ w∈S, pick w<n) : ∃ t<n, (S.filter (fun w => pick w ≠ t)).card ≤ cap n k s := by
  classical
  by_cases h : S.card ≤ cap n k s
  · exact ⟨0,hn,(Finset.card_filter_le ..).trans h⟩
  obtain ⟨d,hd,hprod⟩ := capacity_step (n:=n) (k:=k) (s:=s)
  by_contra! he
  have H := Finset.card_le_mul_card_image_of_maps_to (s:=S) (t:=Finset.range n) (f:=pick)
    (fun a ha => Finset.mem_range.mpr (hp a ha)) d (by
      intro j hj
      have bad := he j (Finset.mem_range.mp hj)
      have both := Finset.card_filter_add_card_filter_not (s:=S) (fun w => pick w = j)
      simp only [ne_eq] at bad
      omega)
  rw [Finset.card_range] at H
  omega
end OeisA100800.Carry

namespace OeisA100800.Carry
open OeisA100800

def lowGap (b t : ℕ) := 10^b * (10^t-1)
def prefixUp (t q : ℕ) := nines (10*q) t
theorem shift_sum (e m : ℕ) : sumDigits (10^e*m) = sumDigits m := by simpa [sumDigits] using sum_block e m 0 (by positivity)

theorem prefix_wt (t q : ℕ) : sumDigits (prefixUp t q) = sumDigits q + 9*t := by
  unfold prefixUp; rw [nines_sum]; congr 1; simpa using shift_sum 1 q

theorem prefix_after (t q : ℕ) : sumDigits (prefixUp t q+1) = sumDigits q + 1 := by
  unfold prefixUp; rw [nines_succ, shift_sum, Nat.add_comm (10*q) 1, sum_low_digit 1 q (by decide), Nat.add_comm]

theorem prefix_eq (t q : ℕ) : prefixUp t q = (10^t-1) + 10^(t+1)*q := by
  have hs := nines_succ (10*q) t
  change prefixUp t q + 1 = _ at hs
  rw [Nat.mul_add, mul_one] at hs
  rw [pow_succ]
  have hp : 0<10^t := by positivity
  nlinarith [Nat.sub_add_cancel (show 1 ≤ 10^t by omega)]

theorem origin_eq (b t q : ℕ) : 10^b * prefixUp t q = lowGap b t + 10^(b+(t+1))*q := by rw [prefix_eq,pow_add]; dsimp [lowGap]; ring

theorem gap_dvd (b t : ℕ) : 9 ∣ lowGap b t := by
  have he : 1 ≤ 10^t := Nat.one_le_pow _ _ (by decide)
  have h := (Nat.modEq_iff_exists_eq_add he).mp (pow_one9 t).symm
  obtain ⟨j,hj⟩ := h
  exact dvd_mul_of_dvd_right (show 9 ∣ 10^t-1 from ⟨j,by omega⟩) _

theorem next_room {b t H : ℕ} (hB : 9*(H+b)<10^b) (ht : t≤H) : 9*((H-t)+(b+(t+1)))<10^(b+(t+1)) := by
  have hb : 0<10^b := by positivity
  have hh : 0<10^t := by positivity
  rw [pow_add, pow_succ, ←Nat.mul_assoc]
  have he := Nat.le_mul_of_pos_right (10^b) hh
  omega

theorem next_offset {b t z : ℕ} (hz : z<10^b) : z+10^b+lowGap b t < 10^(b+(t+1)) := by
  have hh : 0<10^t := by positivity
  have he := Nat.le_mul_of_pos_right (10^b) hh
  dsimp [lowGap]; rw [Nat.mul_sub, mul_one, pow_add, pow_succ, ←Nat.mul_assoc]; omega

theorem prefix_short {q t H s : ℕ} (ht : t ≤ H) (hq : q < 10^(H-t+s)) : prefixUp t q < 10^(H+(s+1)) := by
  have he : H+(s+1) = (t+1)+(H-t+s) := by omega
  rw [he,pow_add, prefix_eq]
  have hx := Nat.mul_le_mul_left (10^(t+1)) (show q+1 ≤ 10^(H-t+s) by omega)
  rw [Nat.mul_add_one] at hx
  have hz : (10^t-1)<10^(t+1) := by
    rw [pow_succ]
    have : 0<10^t := by positivity
    omega
  omega

theorem routed_step {n H b t q z u : ℕ} (ht : t ≤ H) (hq : sumDigits q = 9*(H-t)) (hz : z<10^b)
    (he : z+10^b+sumDigits z+9*H+1 ≡ u+9*t [MOD n]) :
    f (z+10^b+10^b * prefixUp t q) ≡ u+10^b * prefixUp t q [MOD n] := by
  have hs : z+10^b+10^b * prefixUp t q = z+10^b*(prefixUp t q+1) := by ring
  have H1 : z+10^b+sumDigits z+(9*(H-t)+1) ≡ u [MOD n] := by
    apply Nat.ModEq.add_left_cancel (Nat.ModEq.refl (9*t))
    simpa only [show 9*t+(z+10^b+sumDigits z+(9*(H-t)+1)) = z+10^b+sumDigits z+9*H+1 by omega, Nat.add_comm (9*t) u] using he
  unfold f; rw [hs, sum_block b (prefixUp t q+1) z hz, prefix_after, hq, ←hs]
  convert H1.add_right (10^b * prefixUp t q) using 1; ring
end OeisA100800.Carry

namespace OeisA100800.Carry
open OeisA100800 Function

def Good (n b : ℕ) (w : ℕ × ℕ) : Prop := w.1 < 10^b ∧ n.gcd 9 ∣ w.1 ∧ n.gcd 9 ∣ w.2

theorem cover {n : ℕ} (hn : 0<n) (k s b H : ℕ) (S : Finset (ℕ × ℕ)) (hc : S.card ≤ cap n k s)
    (hh : n*s<H) (hB : 9*(H+b)<10^b) (hg : ∀ w∈S, Good n b w) :
    ∃ p, 0<p ∧ sumDigits p = 9*H ∧ p<10^(H+s) ∧
      ∀ w∈S, ∃ j, f^[j] (w.1+10^b*p) ≡ w.2+10^b*p [MOD n] := by
  classical
  induction s generalizing b H S with
  | zero =>
    have h0 : S = ∅ := Finset.card_eq_zero.mp (by simpa [cap] using hc)
    have hp := nines_succ 0 H
    simp only [zero_add, mul_one] at hp
    have hp' : 1<10^H := one_lt_pow₀ (by decide) (by simpa using Nat.ne_of_gt hh)
    exact ⟨nines 0 H,by omega,by rw [nines_sum]; simp [sumDigits],by simpa using (show nines 0 H < 10^H by omega),by simp [h0]⟩
  | succ s ih =>
    rw [Nat.mul_succ] at hh
    let z := fun w : ℕ×ℕ => overshoot b (9*H) w.1
    let fits := fun (w : ℕ×ℕ) (t : ℕ) => z w+10^b+sumDigits (z w)+9*H+1 ≡ w.2+9*t [MOD n]
    have exits (w) (hw : w∈S) : z w<10^b ∧ n.gcd 9 ∣ z w+10^b ∧ ∃ t<n, fits w t :=
      route_exit hn (by omega) hB (hg w hw).1 (hg w hw).2.1 (hg w hw).2.2
    let pick := fun w => if hw : w∈S then Nat.find (exits w hw).2.2 else 0
    have picked (w) (hw : w∈S) : pick w < n ∧ fits w (pick w) := by
      dsimp only [pick]; rw [dif_pos hw]; exact Nat.find_spec (exits w hw).2.2
    obtain ⟨t,ht,htc⟩ := shrink hn hc pick (fun w hw => (picked w hw).1)
    have htH : t≤H := by omega
    let move := fun w : ℕ×ℕ => (z w+10^b+lowGap b t, w.2+lowGap b t)
    let U := (S.filter (fun w => pick w ≠ t)).image move
    have hUc : U.card ≤ cap n k s := Finset.card_image_le.trans htc
    have hUg (w) (hw : w∈U) : Good n (b+(t+1)) w := by
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hw
      have hvS := (Finset.mem_filter.mp hv).1
      have eg := exits v hvS
      have gd := (Nat.gcd_dvd_right n 9).trans (gap_dvd b t)
      exact ⟨next_offset eg.1,dvd_add eg.2.1 gd,dvd_add (hg v hvS).2.2 gd⟩
    obtain ⟨q,hq,hqw,hql,allq⟩ := ih (b+(t+1)) (H-t) U hUc (by omega) (next_room hB htH) hUg
    have hpw : sumDigits (prefixUp t q) = 9*H := by rw [prefix_wt,hqw]; omega
    refine ⟨prefixUp t q,?_,hpw,prefix_short htH hql,?_⟩
    · rw [prefix_eq]; positivity
    intro w hw
    have F := over_correct b (9*H) w.1 (by omega)
    rw [←hpw] at F
    obtain ⟨j,hj⟩ := F.activate
    rw [hpw] at hj
    change f^[j] (w.1+10^b*prefixUp t q) = z w+10^b+10^b*prefixUp t q at hj
    by_cases hwin : pick w=t
    · have win := (picked w hw).2
      rw [hwin] at win
      refine ⟨j+1,?_⟩
      rw [iterate_succ_apply',hj]
      exact routed_step htH hqw (exits w hw).1 win
    · have hwU : move w ∈ U := Finset.mem_image_of_mem move (Finset.mem_filter.mpr ⟨hw,hwin⟩)
      obtain ⟨i,hi⟩ := allq _ hwU
      refine ⟨i+j,?_⟩
      rw [iterate_add_apply,hj,origin_eq]
      simpa only [move,Nat.add_assoc] using hi
end OeisA100800.Carry

namespace OeisA100800.Carry

theorem big_width {b : ℕ} (hb : 2≤b) : 20*b<10^b := by
  induction b, hb using Nat.le_induction with
  | base => decide
  | succ i hi ih => rw [pow_succ]; omega

theorem parameters (n : ℕ) (hn : 0<n) : ∃ k s b H E : ℕ, n*s<H ∧ n<10^b ∧ 9*(H+b)<10^b ∧ E<10^b ∧ 9*(b+(H+s))≤E ∧ (E+1)*(n+1) ≤ cap n k s := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  let n := m+1
  let k := 100*(n+1)^2
  let s := n*k + n*k
  let H := n*s+1
  let b := H+s+n+2
  let E := 9*(b+(H+s))
  have large := big_width (b:=b) (by dsimp [b]; omega)
  refine ⟨k,s,b,H,E,by dsimp [H,n]; omega,?_,?_,?_,le_rfl,?_⟩
  · dsimp [b,n] at large ⊢; omega
  · dsimp [b] at large ⊢; omega
  · dsimp [E,b] at large ⊢; omega
  · change (E+1)*(n+1) ≤ s+(s-n*k)*k
    rw [show s-n*k = n*k by dsimp [s]; omega]
    dsimp [E,b,H,s,k,n]
    nlinarith [Nat.zero_le (m^2), Nat.zero_le (m^3), Nat.zero_le (m^4), Nat.zero_le (m^5)]
end OeisA100800.Carry

namespace OeisA100800.Carry
open OeisA100800 Function

theorem returns (n : ℕ) (hn : 0<n) : a n ≠ 0 := by
  classical
  obtain ⟨k,s,b,H,E,hh,hnB,hB,hEB,hE,hc⟩ := parameters n hn
  let box := (Finset.range (E+1)) ×ˢ (Finset.range (n+1))
  let S := box.filter (fun w => n.gcd 9 ∣ w.1 ∧ n.gcd 9 ∣ w.2)
  have Hcard : S.card ≤ cap n k s := (Finset.card_filter_le ..).trans (by simpa [box] using hc)
  have Hgood (w) (hw : w∈S) : Good n b w := by
    obtain ⟨hb,hd⟩ := Finset.mem_filter.mp hw
    exact ⟨lt_of_le_of_lt (Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_product.mp hb).1)) hEB,hd⟩
  obtain ⟨p,hp,hpw,hpl,allp⟩ := cover hn k s b H S Hcard hh hB Hgood
  let A := 10^b*p
  have hnA : n<A := hnB.trans_le (Nat.le_mul_of_pos_right _ hp)
  have before (x) (hx : x<A) : sumDigits x ≤ E := by
    have hx' : x<10^(b+(H+s)) := by rw [pow_add]; exact hx.trans (Nat.mul_lt_mul_of_pos_left hpl (by positivity))
    rw [←dsum_correct _ _ hx']; exact (dsum_upper ..).trans hE
  obtain ⟨j,r,hj,hr⟩ := first_slice hn hnA before
  have g9 := Nat.gcd_dvd_right n 9
  have gn := Nat.gcd_dvd_left n 9
  have gp : n.gcd 9 ∣ p := Nat.modEq_zero_iff_dvd.mp (((Nat.modEq_nine_digits_sum p).of_dvd g9).trans (Nat.modEq_zero_iff_dvd.mpr (show n.gcd 9 ∣ sumDigits p by rw [hpw]; exact dvd_mul_of_dvd_left g9 _)))
  have gA : n.gcd 9 ∣ A := dvd_mul_of_dvd_right gp _
  have gr : n.gcd 9 ∣ r := by
    apply (Nat.dvd_add_iff_left gA).mpr
    rw [←hj]
    exact Nat.modEq_zero_iff_dvd.mp (((iter_mod9 n (j+1)).of_dvd g9).trans (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_right gn _)))
  let u := n-A%n
  have gu : n.gcd 9 ∣ u := Nat.dvd_sub gn ((Nat.dvd_mod_iff gn).mpr gA)
  have hu : n ∣ u+A := by
    use A/n+1
    have Hmod := Nat.mod_add_div A n
    have Hlt := Nat.mod_lt A hn
    dsimp [u]; rw [Nat.mul_succ]; omega
  have hru : (r,u) ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),Finset.mem_range.mpr (by dsimp [u]; omega)⟩,gr,gu⟩
  obtain ⟨i,hi⟩ := allp (r,u) hru
  apply (positive_return hn.ne').mpr
  use i+j
  rw [Nat.add_assoc, iterate_add_apply, hj]
  exact Nat.modEq_zero_iff_dvd.mp (hi.trans (Nat.modEq_zero_iff_dvd.mpr hu))
end OeisA100800.Carry

theorem OMA.solution : type_of% @OeisA100800.conjecture := by
  intro n hn
  exact OeisA100800.Carry.returns n (Nat.pos_of_ne_zero hn)
