import OMAStatements.S_oeis_a084044
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

/-! Construct palindromic multiples by repeating a palindromic block. -/

namespace A084044

open Nat

private theorem split_base_part (n : ℕ) (hn : 0 < n) :
    ∃ e q k : ℕ, 0 < e ∧ n = e * q ∧ e ∣ 10 ^ k ∧ (10 : ℕ).Coprime q := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hcop : (10 : ℕ).Coprime n
    · exact ⟨1, n, 0, by decide, by simp, by simp, hcop⟩
    obtain ⟨p, hp, hpbase, hpn⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
    obtain ⟨m, hm⟩ := hpn
    have hmpos : 0 < m := by
      by_contra! hm'
      have : m = 0 := by omega
      simp_all
    have hlt : m < n := by
      rw [hm]
      nlinarith [Nat.mul_le_mul_right m hp.two_le]
    obtain ⟨e, q, k, he, hmq, hpow, hc⟩ := ih m hlt hmpos
    refine ⟨p * e, q, k + 1, Nat.mul_pos hp.pos he, ?_, ?_, hc⟩
    · rw [hm, hmq, mul_assoc]
    · rw [_root_.pow_succ']
      exact Nat.mul_dvd_mul hpbase hpow

private def copies (w : List ℕ) (k : ℕ) :=
  (List.replicate k w).flatten

private theorem copies_succ (w : List ℕ) (k : ℕ) :
    copies w (k + 1) = w ++ copies w k := by
  simp [copies, List.replicate_succ]

private theorem copies_length (w : List ℕ) (k : ℕ) :
    (copies w k).length = w.length * k := by
  induction k with
  | zero => simp [copies]
  | succ k ih => rw [copies_succ, List.length_append, ih, Nat.mul_succ, add_comm]

private theorem copies_palindrome {w : List ℕ} (hw : w.reverse = w) (k : ℕ) :
    (copies w k).reverse = copies w k := by
  simp [copies, List.reverse_flatten, List.map_replicate, hw]

private theorem copies_digits {w : List ℕ} (hw : ∀ x ∈ w, x < 10) (k : ℕ) :
    ∀ x ∈ copies w k, x < 10 := by
  induction k with
  | zero => simp [copies]
  | succ k ih =>
    intro x hx
    rw [copies_succ, List.mem_append] at hx
    exact hx.elim (hw x) (ih x)

private theorem copies_dvd {e : ℕ} {w : List ℕ} (h : e ∣ ofDigits 10 w) (k : ℕ) :
    e ∣ ofDigits 10 (copies w k) := by
  induction k with
  | zero => simp [copies]
  | succ k ih => rw [copies_succ, ofDigits_append]; exact dvd_add h (dvd_mul_of_dvd_right ih _)

private theorem copies_zmod (q : ℕ) (w : List ℕ) (i : ℕ)
    (h : (10 : ZMod q) ^ w.length = 1) :
    ((ofDigits 10 (copies w i) : ℕ) : ZMod q) =
      (i : ZMod q) * ((ofDigits 10 w : ℕ) : ZMod q) := by
  induction i with
  | zero => simp [copies]
  | succ i ih =>
    rw [copies_succ, ofDigits_append, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, h,
      one_mul, ih, Nat.cast_succ, add_mul, one_mul, add_comm]

private theorem positive_period {q : ℕ} (hq : 0 < q) (hc : (10 : ℕ).Coprime q) (k : ℕ) :
    ∃ t : ℕ, 0 < t ∧ (10 : ZMod q) ^ (k * t) = 1 := by
  let : NeZero q := ⟨hq.ne'⟩
  let u := ZMod.unitOfCoprime (10 ^ k) (hc.pow_left k)
  refine ⟨orderOf u, orderOf_pos u, ?_⟩
  have eq := congrArg (fun x : (ZMod q)ˣ => (x : ZMod q)) (pow_orderOf_eq_one u)
  simp only [Units.val_pow_eq_pow_val, Units.val_one] at eq
  have hu : (u : ZMod q) = (10 : ZMod q) ^ k := by
    simp only [u, ZMod.coe_unitOfCoprime, Nat.cast_pow, Nat.cast_ofNat]
  rw [hu] at eq
  rwa [pow_mul]

private theorem copies_prefix (w : List ℕ) {i : ℕ} (hi : 0 < i) :
    ∃ rest, copies w i = w ++ rest := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi.ne'
  exact ⟨copies w j, copies_succ w j⟩

private theorem copies_last (w : List ℕ) {i : ℕ} (hi : 0 < i) :
    (copies w i).getLast? = w.getLast? :=
  List.getLast?_flatten_replicate hi.ne' w

private theorem exists_palindrome (n : ℕ) (hn : 0 < n) (hnTen : ¬10 ∣ n) :
    ∃ m, OMA.S_oeis_a084044.admissible n m := by
  obtain ⟨e,q,k,he,heq,hed,hc⟩ := split_base_part n hn
  have hq : 0 < q := by
    by_contra! h
    have : q = 0 := by omega
    simp_all
  have heTen : ¬10 ∣ e := fun h => hnTen (heq ▸ dvd_mul_of_dvd_left h q)
  have heRem : e % 10 ≠ 0 := fun h => heTen (Nat.dvd_of_mod_eq_zero h)
  let low := digits 10 e ++ List.replicate k 0
  let half := low ++ digits 10 n
  let w := half ++ half.reverse
  have hlowHead : low.head? = some (e%10) := by
    simp [low, digits_def' (by decide : 1 < 10) he]
  have hpal : w.reverse = w := by simp [w]
  have hlast : w.getLast? = some (e%10) := by
    rw [← List.head?_reverse, hpal]
    simp [w, half, hlowHead]
  have hlowDigits : ∀ x ∈ low, x < 10 := by
    intro x hx
    simp only [low, List.mem_append, List.mem_replicate] at hx
    exact hx.elim (digits_lt_base (by decide)) (fun h => h.2 ▸ by decide)
  have hhalfDigits : ∀ x ∈ half, x < 10 := by
    intro x hx
    rw [show half = low ++ digits 10 n by rfl, List.mem_append] at hx
    exact hx.elim (hlowDigits x) (digits_lt_base (by decide))
  have hwDigits : ∀ x ∈ w, x < 10 := by
    intro x hx
    rw [show w = half ++ half.reverse by rfl, List.mem_append, List.mem_reverse] at hx
    exact hx.elim (hhalfDigits x) (hhalfDigits x)
  have hwDiv : e ∣ ofDigits 10 w := by
    have hd : e ∣ (10 : ℕ)^low.length := by
      refine hed.trans (pow_dvd_pow _ ?_)
      simp [low]
    rw [show w = low ++ (digits 10 n ++ half.reverse) by simp [w, half, List.append_assoc],
      ofDigits_append]
    have hval : ofDigits 10 low = e := by
      rw [show low = digits 10 e ++ List.replicate k 0 by rfl,
        ofDigits_append_replicate_zero, ofDigits_digits]
    exact dvd_add (hval ▸ dvd_refl e) (dvd_mul_of_dvd_left hd _)
  obtain ⟨t,ht,hperiod⟩ := positive_period hq hc w.length
  let u := copies w t
  let v := copies u q
  let m := ofDigits 10 v
  have hperiodU : (10 : ZMod q) ^ u.length = 1 := by
    simpa only [u, copies_length] using hperiod
  have hqDiv : q ∣ m := by
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    rw [show m = ofDigits 10 (copies u q) by rfl, copies_zmod q u q hperiodU,
      ZMod.natCast_self, zero_mul]
  have heDiv : e ∣ m := copies_dvd (copies_dvd hwDiv t) q
  have hndvd : n ∣ m := by
    rw [heq]
    exact ((hc.pow_left k).of_dvd_left hed).mul_dvd_of_dvd_of_dvd heDiv hqDiv
  have hvlast : v.getLast? = some (e%10) := by
    rw [show v = copies u q by rfl, copies_last u hq, show u = copies w t by rfl,
      copies_last w ht, hlast]
  have hvne : v ≠ [] := by
    intro h
    simp [h] at hvlast
  have hdigit : digits 10 m = v := by
    refine digits_ofDigits 10 (by decide) v (copies_digits (copies_digits hwDigits t) q) ?_
    intro hv
    exact (List.getLast_of_getLast?_eq_some hvlast).trans_ne heRem
  have hm : 0 < m := by
    apply Nat.pos_of_ne_zero
    intro hz
    rw [hz, digits_zero] at hdigit
    exact hvne hdigit.symm
  refine ⟨m,hm,hndvd,?_,?_⟩
  · rw [hdigit]
    exact copies_palindrome (copies_palindrome hpal t) q
  · obtain ⟨r,hr⟩ := copies_prefix w ht
    obtain ⟨s,hs⟩ := copies_prefix u hq
    refine ⟨low,half.reverse ++ r ++ s,?_⟩
    rw [hdigit]
    change copies u q = _
    rw [hs, show u = copies w t by rfl, hr]
    simp [w, half, List.append_assoc]

private theorem palindrome_not_ten {n m : ℕ} (hm : OMA.S_oeis_a084044.admissible n m) :
    ¬ 10 ∣ n := by
  intro hTen
  have hmTen := hTen.trans hm.2.1
  have hmod : m % 10 = 0 := Nat.mod_eq_zero_of_dvd hmTen
  have hhead : (digits 10 m).head? = some 0 := by
    simp [digits_def' (by decide : 1 < 10) hm.1, hmod]
  have hlast : (digits 10 m).getLast? = some 0 := by
    rw [← List.head?_reverse, hm.2.2.1, hhead]
  have lastNe := getLast_digit_ne_zero 10 hm.1.ne'
  exact lastNe (List.getLast_of_getLast?_eq_some hlast)

end A084044

theorem OMA.solution : type_of% @OMA.S_oeis_a084044.main := by
  classical
  intro n hn
  by_cases hex : ∃ m, OMA.S_oeis_a084044.admissible n m
  · have hs := Nat.find_spec hex
    rw [OMA.S_oeis_a084044.a, dif_pos hex]
    exact iff_of_false hs.1.ne' (A084044.palindrome_not_ten hs)
  · have hdvd : 10 ∣ n := by
      by_contra h
      exact hex (A084044.exists_palindrome n hn h)
    simp [OMA.S_oeis_a084044.a, hex, hdvd]
