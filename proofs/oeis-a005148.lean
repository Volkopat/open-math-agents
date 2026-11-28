import OMAStatements.S_oeis_a005148
import Mathlib.Tactic

/-!
Formalizes the known valuation result recorded in A005148. Legendre's
factorial formula gives the exact power of two in each central binomial
coefficient. In the convolution step, terms with opposite indices have
the same exact valuation, and a middle term has strictly higher valuation.
The convolution remainder therefore vanishes modulo the next power of two.
The scaled sequence is also divisible by three, so division by 24 removes
exactly three factors of two.
-/

namespace A005148
open OMA.S_oeis_a005148

private lemma factorial_weight (n : ℕ) : n.factorial.factorization 2 + weight n = n := by
  have h := Nat.sub_one_mul_factorization_factorial (n := n) Nat.prime_two
  have hle := Nat.digit_sum_le 2 n
  simp only [Nat.reduceSub, one_mul] at h
  unfold weight
  omega

private lemma choose_weight (m n : ℕ) :
    ((m + n).choose n).factorization 2 + weight (m + n) = weight m + weight n := by
  have hchoose := Nat.choose_ne_zero (Nat.le_add_left n m)
  have h := congrArg (fun x : ℕ => x.factorization 2)
    (Nat.add_choose_mul_factorial_mul_factorial m n)
  rw [Nat.factorization_mul (Nat.mul_ne_zero hchoose m.factorial_ne_zero) n.factorial_ne_zero,
    Finsupp.add_apply, Nat.factorization_mul hchoose m.factorial_ne_zero,
    Finsupp.add_apply] at h
  have hm := factorial_weight m
  have hn := factorial_weight n
  have hmn := factorial_weight (m+n)
  omega

private lemma weight_double (n : ℕ) : weight (2 * n) = weight n := by
  by_cases hn : n = 0
  · simp [hn]
  unfold weight
  have hd := Nat.digits_add 2 (by decide) 0 n (by decide) (Or.inr hn)
  simpa using congrArg List.sum hd

private lemma weight_pos {n : ℕ} (hn : 0 < n) : 0 < weight n := by
  have hd := Nat.getLast_digit_ne_zero 2 (Nat.ne_of_gt hn)
  have hm := List.getLast_mem (l := Nat.digits 2 n) (Nat.digits_ne_nil_iff_ne_zero.mpr hn.ne')
  exact Nat.pos_of_ne_zero (fun h => hd (List.sum_eq_zero_iff.mp h _ hm))

private lemma central_factorization (n : ℕ) :
    ((2*n).choose n).factorization 2 = weight n := by
  have h := choose_weight n n
  rw [← two_mul, weight_double] at h
  omega

private def OddQuotient (e : ℕ) (x : ℤ) : Prop :=
  ∃ q : ℤ, Odd q ∧ x = 2 ^ e * q

private lemma central_oddQuotient (n : ℕ) : OddQuotient (weight n) (central n) := by
  have hpos : 0 < (2*n).choose n := Nat.choose_pos (by omega)
  obtain ⟨q,hq⟩ := Nat.ordProj_dvd ((2*n).choose n) 2
  rw [central_factorization] at hq
  have hodd : Odd q := by
    by_contra h
    obtain ⟨k,hk⟩ := (even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp h))
    have hdvd : 2 ^ (weight n + 1) ∣ (2*n).choose n := by
      refine ⟨k, ?_⟩
      rw [hq, hk, pow_succ, mul_assoc]
    have hh := (Nat.prime_two.pow_dvd_iff_le_factorization hpos.ne').mp hdvd
    rw [central_factorization] at hh
    omega
  refine ⟨q, ?_, ?_⟩
  · exact_mod_cast hodd
  · unfold central
    exact_mod_cast hq


private lemma oddQuotient_mul {e f : ℕ} {x y : ℤ}
    (hx : OddQuotient e x) (hy : OddQuotient f y) : OddQuotient (e + f) (x * y) := by
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨v, hv, rfl⟩ := hy
  refine ⟨u * v, hu.mul hv, ?_⟩
  rw [pow_add]
  ring

private lemma oddQuotient_cube {e : ℕ} {x : ℤ}
    (hx : OddQuotient e x) : OddQuotient (3 * e) (x ^ 3) := by
  obtain ⟨u, hu, rfl⟩ := hx
  refine ⟨u ^ 3, hu.pow, ?_⟩
  rw [mul_comm 3 e, pow_mul, mul_pow]

private lemma oddQuotient_sub_dvd {e : ℕ} {x y : ℤ}
    (hx : OddQuotient e x) (hy : (2 : ℤ) ^ (e + 1) ∣ y) :
    OddQuotient e (x - y) := by
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨v, rfl⟩ := hy
  refine ⟨u - 2*v, ?_, ?_⟩
  · obtain ⟨q,hq⟩ := hu
    exact ⟨q-v, by omega⟩
  · rw [pow_succ]
    ring

private lemma lead_oddQuotient {n : ℕ} (hn : 0 < n) :
    OddQuotient (3 * weight n) (central n * (16 ^ n - central n ^ 2)) := by
  obtain ⟨u, hu, heq⟩ := central_oddQuotient n
  have hw := Nat.digit_sum_le 2 n
  change weight n ≤ n at hw
  let k := 4*n - (2*weight n+1)
  have hk : 4*n = 2*weight n+1 + k := by dsimp [k]; omega
  have he : (16 : ℤ)^n = 2^(2*weight n+1) * 2^k := by
    calc
      (16 : ℤ)^n = (2^4)^n := by norm_num
      _ = 2^(4*n) := by rw [pow_mul]
      _ = _ := by rw [hk, pow_add]
  have hfactor : OddQuotient (2 * weight n) (16 ^ n - central n ^ 2) := by
    refine ⟨2 * 2^k - u^2, ?_, ?_⟩
    · obtain ⟨v,hv⟩ := hu.pow (n := 2)
      exact ⟨2^k-v-1, by omega⟩
    · rw [he, heq, pow_succ, mul_pow, mul_comm 2 (weight n), pow_mul]
      ring
  simpa [show weight n + 2 * weight n = 3 * weight n by omega] using
    oddQuotient_mul (central_oddQuotient n) hfactor


private lemma oddQuotient_add_dvd {e : ℕ} {x y : ℤ}
    (hx : OddQuotient e x) (hy : OddQuotient e y) :
    (2 : ℤ) ^ (e + 1) ∣ x + y := by
  obtain ⟨u, ⟨a, ha⟩, rfl⟩ := hx
  obtain ⟨v, ⟨b, hb⟩, rfl⟩ := hy
  refine ⟨a + b + 1, ?_⟩
  rw [ha, hb, pow_succ]
  ring

private lemma oddQuotient_dvd_of_le {e f : ℕ} {x : ℤ}
    (hx : OddQuotient f x) (h : e ≤ f) : (2 : ℤ) ^ e ∣ x := by
  obtain ⟨u, _, rfl⟩ := hx
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  refine ⟨2 ^ k * u, ?_⟩
  rw [pow_add, mul_assoc]

private lemma rev_indices {n : ℕ} (i : Fin n) :
    (i : ℕ) + 1 + ((i.rev : Fin n) : ℕ) + 1 = n + 1 := by
  have hi := i.isLt
  rw [Fin.val_rev]
  omega

private lemma convolution_dvd (n : ℕ)
    (ih : ∀ i < n + 1, 0 < i → OddQuotient (3 * weight i) (scaled i)) :
    (2 : ℤ) ^ (3 * weight (n + 1) + 1) ∣
      ∑ i : Fin n, central (n - (i : ℕ)) ^ 3 * scaled ((i : ℕ) + 1) := by
  let e := 3 * weight (n + 1) + 1
  let exponent (i : Fin n) := 3 * (weight ((i : ℕ) + 1) + weight ((i.rev : ℕ) + 1))
  let term (i : Fin n) := central (n - (i : ℕ)) ^ 3 * scaled ((i : ℕ) + 1)
  have hquot (i : Fin n) : OddQuotient (exponent i) (term i) := by
    have hi := i.isLt
    have hidx := rev_indices i
    have heq : n - (i : ℕ) = ((i.rev : Fin n) : ℕ) + 1 := by omega
    have hc := oddQuotient_cube (central_oddQuotient (n - (i : ℕ)))
    have ha := ih ((i : ℕ) + 1) (by omega) (by omega)
    have h := oddQuotient_mul hc ha
    unfold exponent term
    rw [heq] at h ⊢
    convert h using 1
    omega
  have hexprev (i : Fin n) : exponent i.rev = exponent i := by
    unfold exponent
    rw [Fin.rev_rev]
    ac_rfl
  have hge (i : Fin n) : 3 * weight (n + 1) ≤ exponent i := by
    have hi := choose_weight ((i : ℕ) + 1) ((i.rev : ℕ) + 1)
    have hidx : (i : ℕ) + 1 + ((i.rev : ℕ) + 1) = n + 1 := by
      have h := rev_indices i
      omega
    rw [hidx] at hi
    unfold exponent
    omega
  let f (i : Fin n) : ZMod (2 ^ e) := (term i : ℤ)
  have vanish {x : ℤ} (h : (2 : ℤ)^e ∣ x) : (x : ZMod (2 ^ e)) = 0 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd x (2 ^ e)).2
    exact_mod_cast h
  have hsum : ∑ i : Fin n, f i = 0 := by
    apply Finset.sum_ninvolution Fin.rev
    · intro i
      change (term i : ZMod (2^e)) + (term i.rev : ZMod (2^e)) = 0
      rw [← Int.cast_add]
      apply vanish
      have hi := hge i
      by_cases h : e ≤ exponent i
      · exact dvd_add (oddQuotient_dvd_of_le (hquot i) h)
          (oddQuotient_dvd_of_le (hquot i.rev) (by rwa [hexprev]))
      · have he : exponent i = 3 * weight (n + 1) := by dsimp [e] at h; omega
        have hrev := hquot i.rev
        rw [hexprev, he] at hrev
        exact oddQuotient_add_dvd (he ▸ hquot i) hrev
    · intro i hnonzero heq
      have hi := weight_pos (n := (i : ℕ) + 1) (by omega)
      have hnd : n + 1 = 2 * ((i : ℕ) + 1) := by
        have h := rev_indices i
        rw [heq] at h
        omega
      have h : e ≤ exponent i := by
        unfold exponent e
        rw [heq, hnd, weight_double]
        omega
      exact hnonzero (vanish (oddQuotient_dvd_of_le (hquot i) h))
    · exact fun _ => Finset.mem_univ _
    · exact Fin.rev_rev
  change (2 : ℤ) ^ e ∣ ∑ i : Fin n, term i
  have hsum' : ((∑ i : Fin n, term i : ℤ) : ZMod (2 ^ e)) = 0 := by
    simpa only [Int.cast_sum] using hsum
  exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ (2 ^ e)).1 hsum'

private lemma scaled_oddQuotient (n : ℕ) (hn : 0 < n) :
    OddQuotient (3 * weight n) (scaled n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => omega
    | succ n =>
      rw [scaled]
      exact oddQuotient_sub_dvd (lead_oddQuotient hn) (convolution_dvd n ih)

private lemma scaled_three_dvd (n : ℕ) : (3 : ℤ) ∣ scaled n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [scaled]
    | succ n =>
      rw [scaled]
      apply dvd_sub
      · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).1
        push_cast
        have h16 : (16 : ZMod 3) = 1 := by decide
        rw [h16, one_pow]
        generalize (central (n + 1) : ZMod 3) = u
        fin_cases u <;> decide
      · apply Finset.dvd_sum
        intro i _
        exact Dvd.dvd.mul_left (ih ((i : ℕ) + 1) (Nat.succ_lt_succ i.isLt)) _

private theorem proof : ∀ n : ℕ, 0 < n →
    ∃ u : ℤ, Odd u ∧ a n = 2 ^ (3 * (weight n - 1)) * u := by
  intro n hn
  obtain ⟨q, hq, hs⟩ := scaled_oddQuotient n hn
  have hthree := scaled_three_dvd n
  rw [hs] at hthree
  have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).2 hthree
  push_cast at hz
  have htwo : (2 : ZMod 3) ≠ 0 := by decide
  have hq3 := (ZMod.intCast_zmod_eq_zero_iff_dvd q 3).1
    ((mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ htwo))
  obtain ⟨u, hu⟩ := hq3
  have hodd : Odd u := by
    obtain ⟨v, hv⟩ := hq
    exact ⟨v - u, by omega⟩
  have hw := weight_pos hn
  have he : 3 * weight n = 3 * (weight n - 1) + 3 := by omega
  have hscale : scaled n = (2 ^ (3 * (weight n - 1)) * u) * 24 := by
    rw [hs, hu, he, pow_add]
    ring
  refine ⟨u, hodd, ?_⟩
  rw [a, hscale, Int.mul_ediv_cancel _ (by decide : (24 : ℤ) ≠ 0)]

end A005148

theorem OMA.solution : type_of% @OMA.S_oeis_a005148.main :=
  A005148.proof
