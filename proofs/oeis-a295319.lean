import OMAStatements.S_oeis_a295319

/-!
Credit: @bnb9001 (proof; statement #22940 by @Harsha0912)

Build fixed-length palindromic decimal words by adding equal outer digits.
With leading zeroes allowed, their count is 10^ceil(n/2), and their sum S
satisfies 2*S + count = count*10^n. Restricting the outer digit to 1..9
gives a(n+2)=495*10^(n+ceil(n/2)). The digits/ofDigits correspondence
identifies this sum with the exact finite set in the imported statement.
The exponents obtained are precisely the residues 0 and 2 modulo 3.
-/

namespace A295319Proof
open Finset OMA.S_oeis_a295319

def wrap (d : ℕ) (w : List ℕ) : List ℕ := d :: (w ++ [d])

def words : ℕ → Finset (List ℕ)
  | 0 => {[]}
  | 1 => (range 10).image (fun d => [d])
  | n+2 => ((range 10).product (words n)).image (fun p => wrap p.1 p.2)

def proper (n : ℕ) : Finset (List ℕ) :=
  ((Icc 1 9).product (words n)).image (fun p => wrap p.1 p.2)

def Digits (w : List ℕ) : Prop := ∀ d ∈ w, d < 10

lemma wrap_injective : Function.Injective (fun p : ℕ × List ℕ => wrap p.1 p.2) := by
  rintro ⟨a,u⟩ ⟨b,v⟩ h
  simp only [wrap, List.cons.injEq] at h
  obtain ⟨rfl,h⟩ := h
  have := List.append_cancel_right h
  subst v
  rfl

lemma wrap_length (d : ℕ) (w : List ℕ) : (wrap d w).length = w.length+2 := by simp [wrap]

lemma wrap_digits (d : ℕ) (w : List ℕ) : Digits (wrap d w) ↔ d < 10 ∧ Digits w := by
  constructor
  · intro h
    exact ⟨h d (by simp [wrap]), fun x hx => h x (by simp [wrap,hx])⟩
  · rintro ⟨hd,hw⟩ x hx
    simp only [wrap,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | hx | rfl
    · exact hd
    · exact hw x hx
    · exact hd

lemma wrap_palindrome (d : ℕ) (w : List ℕ) :
    (wrap d w).reverse = wrap d w ↔ w.reverse = w := by
  simp [wrap, List.reverse_cons, List.reverse_append, List.cons_append]

lemma split_palindrome {n : ℕ} {w : List ℕ} (hlen : w.length = n+2) (hp : w.reverse = w) :
    ∃ d v, v.length = n ∧ w = wrap d v := by
  obtain ⟨a,t,rfl⟩ := List.exists_cons_of_length_pos (by omega : 0 < w.length)
  rcases List.eq_nil_or_concat' t with rfl | ⟨v,b,rfl⟩
  · simp at hlen
  have heq : b = a := by
    simp only [List.reverse_cons, List.reverse_append, List.reverse_nil,
      List.nil_append, List.cons_append, List.cons.injEq] at hp
    exact hp.1
  subst b
  exact ⟨a,v,by simpa using hlen,rfl⟩

lemma mem_words (n : ℕ) (w : List ℕ) :
    w ∈ words n ↔ w.length = n ∧ Digits w ∧ w.reverse = w := by
  induction n using Nat.twoStepInduction generalizing w with
  | zero => cases w <;> simp [words, Digits]
  | one =>
    constructor
    · intro h
      obtain ⟨d,hd,rfl⟩ := mem_image.mp h
      simp only [mem_range] at hd
      simp [Digits,hd]
    · rintro ⟨hl,hd,_⟩
      obtain ⟨d,rfl⟩ := List.length_eq_one_iff.mp hl
      exact mem_image.mpr ⟨d,mem_range.mpr (hd d (by simp)),rfl⟩
  | more n ih _ =>
    constructor
    · intro h
      obtain ⟨⟨d,v⟩,hp,rfl⟩ := mem_image.mp h
      obtain ⟨hd,hv⟩ := Finset.mem_product.mp hp
      obtain ⟨hl,hv,hpal⟩ := (ih v).mp hv
      exact ⟨by simpa [wrap_length] using hl,
        (wrap_digits d v).mpr ⟨mem_range.mp hd,hv⟩, (wrap_palindrome d v).mpr hpal⟩
    · rintro ⟨hl,hd,hp⟩
      obtain ⟨d,v,hv,rfl⟩ := split_palindrome hl hp
      obtain ⟨hd,hv'⟩ := (wrap_digits d v).mp hd
      exact mem_image.mpr ⟨(d,v), Finset.mem_product.mpr ⟨mem_range.mpr hd,
        (ih v).mpr ⟨hv,hv',(wrap_palindrome d v).mp hp⟩⟩, rfl⟩

lemma wrap_value (d : ℕ) (w : List ℕ) :
    Nat.ofDigits 10 (wrap d w) = d*(10^(w.length+1)+1) + 10*Nat.ofDigits 10 w := by
  simp only [wrap, Nat.ofDigits_cons, Nat.ofDigits_append, Nat.ofDigits_nil, pow_succ]
  ring

lemma wrap_getLast (d : ℕ) (w : List ℕ) (h : wrap d w ≠ []) : (wrap d w).getLast h = d := by
  simp [wrap, List.getLast_cons] 

lemma digits_wrap {n d : ℕ} {w : List ℕ} (hd : d ∈ Icc 1 9) (hw : w ∈ words n) :
    Nat.digits 10 (Nat.ofDigits 10 (wrap d w)) = wrap d w := by
  have hd' := mem_Icc.mp hd
  have hw' := (mem_words n w).mp hw
  apply Nat.digits_ofDigits 10 (by decide)
  · exact (wrap_digits d w).mpr ⟨by omega,hw'.2.1⟩
  · intro h
    rw [wrap_getLast]
    omega

lemma card_wraps (D : Finset ℕ) (n : ℕ) :
    (((D.product (words n)).image (fun p => wrap p.1 p.2))).card = D.card*(words n).card := by
  rw [card_image_of_injOn wrap_injective.injOn]
  exact card_product D (words n)

lemma sum_wraps (D : Finset ℕ) (n : ℕ) :
    (∑ w ∈ (D.product (words n)).image (fun p => wrap p.1 p.2), Nat.ofDigits 10 w) =
      (∑ d ∈ D, d) * (words n).card * (10^(n+1)+1) +
        D.card * 10 * ∑ w ∈ words n, Nat.ofDigits 10 w := by
  rw [sum_image wrap_injective.injOn]
  calc
    _ = ∑ d ∈ D, ∑ w ∈ words n, Nat.ofDigits 10 (wrap d w) := Finset.sum_product ..
    _ = ∑ d ∈ D, ∑ w ∈ words n, (d*(10^(n+1)+1) + 10*Nat.ofDigits 10 w) := by
      apply sum_congr rfl
      intro d hd
      apply sum_congr rfl
      intro w hw
      rw [wrap_value, (mem_words n w).mp hw |>.1]
    _ = _ := by
      simp only [sum_add_distrib, sum_const, smul_eq_mul, ← mul_sum, ← sum_mul]
      ring

lemma words_card (n : ℕ) : (words n).card = 10^((n+1)/2) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [words]
  | one => decide
  | more n ih _ =>
    rw [words, card_wraps, card_range, ih]
    have he : (n+2+1)/2 = (n+1)/2+1 := by omega
    rw [he,pow_succ]
    omega

lemma words_sum (n : ℕ) :
    2*(∑ w ∈ words n, Nat.ofDigits 10 w) + (words n).card = (words n).card*10^n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [words, Nat.ofDigits]
  | one => decide
  | more n ih _ =>
    rw [words, card_wraps, sum_wraps]
    have hs : ∑ d ∈ range 10, d = 45 := by decide
    rw [hs,card_range]
    simp only [pow_succ]
    nlinarith

lemma proper_sum (n : ℕ) :
    (∑ w ∈ proper n, Nat.ofDigits 10 w) = 495*10^(n+(n+1)/2) := by
  rw [proper, sum_wraps]
  have hs : ∑ d ∈ Icc 1 9, d = 45 := by decide
  have hc : (Icc 1 9).card = 9 := by decide
  rw [hs,hc,pow_add 10 n ((n+1)/2),pow_succ,← words_card]
  have hi := words_sum n
  nlinarith

lemma proper_injective (n : ℕ) : Set.InjOn (Nat.ofDigits 10) (proper n) := by
  intro u hu v hv he
  obtain ⟨⟨d,w⟩,hp,rfl⟩ := mem_image.mp hu
  obtain ⟨hd,hw⟩ := Finset.mem_product.mp hp
  obtain ⟨⟨e,z⟩,hq,rfl⟩ := mem_image.mp hv
  obtain ⟨he',hz⟩ := Finset.mem_product.mp hq
  have h := congrArg (Nat.digits 10) he
  simpa only [digits_wrap hd hw, digits_wrap he' hz] using h

lemma number_set (n : ℕ) :
    (Ico (10^(n+1)) (10^(n+2))).filter IsPal = (proper n).image (Nat.ofDigits 10) := by
  ext m
  constructor
  · intro hm
    obtain ⟨hm,hpal⟩ := mem_filter.mp hm
    change (Nat.digits 10 m).reverse = Nat.digits 10 m at hpal
    obtain ⟨hlo,hhi⟩ := mem_Ico.mp hm
    have hlen : (Nat.digits 10 m).length = n+2 := by
      have hu := (Nat.digits_length_le_iff (by decide : 1 < 10) m).mpr hhi
      have hl := (Nat.lt_digits_length_iff (by decide : 1 < 10) m).mpr hlo
      omega
    obtain ⟨d,w,hwlen,heq⟩ := split_palindrome hlen hpal
    have hd : d < 10 := Nat.digits_lt_base (by decide) (by rw [heq]; simp [wrap])
    have hm0 : m ≠ 0 := by
      have : 0 < 10^(n+1) := Nat.pow_pos (by decide)
      omega
    have hdn : d ≠ 0 := by
      have hn := Nat.getLast_digit_ne_zero 10 hm0
      simpa only [heq,wrap_getLast] using hn
    have hw : w ∈ words n := by
      apply (mem_words n w).mpr
      refine ⟨hwlen,?_,?_⟩
      · intro x hx
        exact Nat.digits_lt_base (by decide) (by rw [heq]; simp [wrap,hx])
      · apply (wrap_palindrome d w).mp
        simpa only [← heq] using hpal
    apply mem_image.mpr
    refine ⟨wrap d w,?_,?_⟩
    · exact mem_image.mpr ⟨(d,w),Finset.mem_product.mpr ⟨mem_Icc.mpr (by omega),hw⟩,rfl⟩
    · rw [← heq,Nat.ofDigits_digits]
  · intro hm
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hm
    obtain ⟨⟨d,w⟩,hp,rfl⟩ := mem_image.mp hu
    obtain ⟨hd,hw⟩ := Finset.mem_product.mp hp
    dsimp only [Prod.fst,Prod.snd]
    have hw' := (mem_words n w).mp hw
    have hlen : (Nat.digits 10 (Nat.ofDigits 10 (wrap d w))).length = n+2 := by
      rw [digits_wrap hd hw,wrap_length,hw'.1]
    apply mem_filter.mpr
    refine ⟨mem_Ico.mpr ⟨?_,?_⟩,?_⟩
    · apply (Nat.lt_digits_length_iff (by decide : 1 < 10) _).mp
      omega
    · apply (Nat.digits_length_le_iff (by decide : 1 < 10) _).mp
      omega
    · unfold IsPal
      rw [digits_wrap hd hw]
      exact (wrap_palindrome d w).mpr hw'.2.2

lemma a_formula (n : ℕ) : a (n+2) = 495*10^(n+(n+1)/2) := by
  unfold a
  have he : n+2-1 = n+1 := by omega
  rw [he,number_set,sum_image (proper_injective n),proper_sum]

end A295319Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a295319.main := by
  ext x
  constructor
  · rintro ⟨n,hn,hx⟩
    obtain ⟨t,rfl⟩ : ∃ t, n = t+2 := ⟨n-2,by omega⟩
    rw [A295319Proof.a_formula] at hx
    exact ⟨t+(t+1)/2,by omega,hx.symm⟩
  · rintro ⟨k,hk,rfl⟩
    refine ⟨2*k/3+2,by omega,?_⟩
    rw [A295319Proof.a_formula]
    congr 2
    omega

