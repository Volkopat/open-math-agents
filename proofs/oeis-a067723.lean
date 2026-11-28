import OMAStatements.S_oeis_a067723
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace OMA.P_oeis_a067723

open OMA.S_oeis_a067723

/-- Evaluate a list of base-10 digits as an element of `ZMod 11` using `10 = -1`. -/
private def altSum : List ℕ → ZMod 11
  | [] => 0
  | d :: tl => (d : ZMod 11) - altSum tl

private lemma ofDigits_cast_zmod11 (l : List ℕ) :
    ((Nat.ofDigits 10 l : ℕ) : ZMod 11) = altSum l := by
  induction l with
  | nil => simp [altSum]
  | cons d tl ih =>
    simp only [Nat.ofDigits_cons, altSum, Nat.cast_add, Nat.cast_mul, ih]
    have h10 : ((10 : ℕ) : ZMod 11) = -1 := by decide
    rw [h10]
    ring

private lemma altSum_append (l1 l2 : List ℕ) :
    altSum (l1 ++ l2) = altSum l1 + (-1 : ZMod 11) ^ l1.length * altSum l2 := by
  induction l1 with
  | nil => simp [altSum]
  | cons d tl ih =>
    simp only [List.cons_append, altSum, List.length_cons, pow_succ]
    rw [ih]
    ring

private lemma altSum_reverse (l : List ℕ) :
    altSum l.reverse = -((-1 : ZMod 11) ^ l.length) * altSum l := by
  induction l with
  | nil => simp [altSum]
  | cons d tl ih =>
    simp only [List.reverse_cons, altSum_append, ih, List.length_reverse, List.length_cons]
    have hsingle : altSum [d] = (d : ZMod 11) := by simp [altSum]
    rw [hsingle]
    simp only [altSum, pow_succ]
    ring

private lemma eleven_dvd_of_even_palindrome {k : ℕ}
    (hpal : IsPalindrome k) (heven : Even (Nat.digits 10 k).length) : 11 ∣ k := by
  set l := Nat.digits 10 k
  have h1 : altSum l.reverse = -altSum l := by
    rw [altSum_reverse, heven.neg_one_pow]; ring
  rw [show l.reverse = l from hpal] at h1
  have h2 : (2 : ZMod 11) * altSum l = 0 := by linear_combination h1
  have h2_ne : (2 : ZMod 11) ≠ 0 := by decide
  have : Fact (Nat.Prime 11) := ⟨by decide⟩
  have h0 : altSum l = 0 := (mul_eq_zero.mp h2).resolve_left h2_ne
  rw [← ZMod.natCast_eq_zero_iff]
  have hof : Nat.ofDigits 10 l = k := Nat.ofDigits_digits 10 k
  rw [← hof, ofDigits_cast_zmod11, h0]

private lemma not_palindrome_of_ten_dvd {m : ℕ} (hm : 0 < m) (h10 : 10 ∣ m) :
    ¬ IsPalindrome m := by
  intro hpal
  have hne : Nat.digits 10 m ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr (by omega)
  have hhead : (Nat.digits 10 m).head hne = 0 := by
    have hcons : Nat.digits 10 m = (m % 10) :: Nat.digits 10 (m / 10) :=
      Nat.digits_def' (by norm_num) hm
    have hmod : m % 10 = 0 := Nat.mod_eq_zero_of_dvd h10
    rw [hmod] at hcons
    revert hne
    rw [hcons]
    intro _
    rfl
  have hlast : (Nat.digits 10 m).getLast hne ≠ 0 :=
    Nat.getLast_digit_ne_zero 10 (by omega)
  have hrev_head : (Nat.digits 10 m).reverse.head (List.reverse_ne_nil_iff.mpr hne) =
      (Nat.digits 10 m).getLast hne := List.head_reverse _
  have heq : (Nat.digits 10 m).head hne = (Nat.digits 10 m).getLast hne := by
    rw [← hrev_head]
    congr 1
    exact hpal.symm
  exact hlast (heq.symm.trans hhead)

private theorem prove_main : type_of% @OMA.S_oeis_a067723.main := by
  intro k ⟨hk10, hpal_k, hpal_phi⟩ heven
  have h11 : 11 ∣ k := eleven_dvd_of_even_palindrome hpal_k heven
  have h10 : 10 ∣ Nat.totient k := by
    have hd := Nat.totient_dvd_of_dvd h11
    have hphi11 : Nat.totient 11 = 10 := by decide
    rwa [hphi11] at hd
  have hpos : 0 < Nat.totient k := Nat.totient_pos.mpr (by omega)
  exact not_palindrome_of_ten_dvd hpos h10 hpal_phi

end OMA.P_oeis_a067723

theorem OMA.solution : type_of% @OMA.S_oeis_a067723.main :=
  OMA.P_oeis_a067723.prove_main
