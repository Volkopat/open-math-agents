import OMAStatements.S_oeis_a138217

/-!
Credit: @bnb9001 (proof; statement #17016 by @romechenko)

Cubing gives 2^(2*3^k)=1+3^(k+1)*u with u congruent to 1 modulo 3.
Reduction between successive moduli then proves order(2 mod 3^(k+1))=2*3^k.
Every totient/order quotient in the prime-power divisor sum is 1, giving
the required exact formula and the infinite composite family 3^(k+2).
For the counterexample, modular-power certificates show order 364 modulo
both 1093 and 1093^2. The resulting excess is 1194648, which is not
divisible by totient(1093^2)=1193556.
-/

namespace A138217Proof
open Finset OMA.S_oeis_a138217

lemma lift_three (k : ℕ) :
    ∃ u : ℕ, 2^(2*3^k) = 1+3^(k+1)*u ∧ u % 3 = 1 := by
  induction k with
  | zero => exact ⟨1,by decide,by decide⟩
  | succ k ih =>
    obtain ⟨u,hu,hm⟩ := ih
    refine ⟨u+3*3^k*u^2+3*(3^k)^2*u^3,?_,?_⟩
    · have he : 2*3^(k+1) = (2*3^k)*3 := by rw [pow_succ]; ring
      rw [he,pow_mul,hu]
      simp only [pow_succ]
      ring
    · simp [Nat.add_mod, Nat.mul_mod, hm]

lemma power_three_eq (k : ℕ) : (2 : ZMod (3^(k+1)))^(2*3^k) = 1 := by
  obtain ⟨u,hu,_⟩ := lift_three k
  have h : ((2^(2*3^k) : ℕ) : ZMod (3^(k+1))) = 1 := by
    rw [hu,Nat.cast_add,Nat.cast_mul,ZMod.natCast_self]
    simp
  simpa only [Nat.cast_pow,Nat.cast_ofNat] using h

lemma power_three_ne (k : ℕ) : (2 : ZMod (3^(k+2)))^(2*3^k) ≠ 1 := by
  obtain ⟨u,hu,hm⟩ := lift_three k
  intro he
  have he' : (2^(2*3^k)) ≡ 1 [MOD 3^(k+2)] :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mp (by simpa only [Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one] using he)
  have hpos : 1 ≤ 2^(2*3^k) := Nat.one_le_pow _ _ (by decide)
  have hd := (Nat.modEq_iff_dvd' hpos).mp he'.symm
  rw [hu,Nat.add_sub_cancel_left,pow_succ] at hd
  obtain ⟨v,hv⟩ := hd
  have hp : 0 < 3^(k+1) := Nat.pow_pos (by decide)
  have huv : u = 3*v := by nlinarith [hv]
  rw [huv] at hm
  omega

lemma order_three_succ (k : ℕ) : ordTwo (3^(k+1)) = 2*3^k := by
  induction k with
  | zero =>
    change orderOf (2 : ZMod 3) = 2
    exact orderOf_eq_prime (by decide) (by decide)
  | succ k ih =>
    have hs : 3^(k+1) ∣ 3^(k+2) := by exact pow_dvd_pow 3 (by omega)
    have hmap := orderOf_map_dvd (ZMod.castHom hs (ZMod (3^(k+1)))).toMonoidHom
      (2 : ZMod (3^(k+2)))
    have hdiv : 2*3^k ∣ ordTwo (3^(k+2)) := by
      have hmap' : ordTwo (3^(k+1)) ∣ ordTwo (3^(k+2)) := by
        change orderOf ((ZMod.castHom hs (ZMod (3^(k+1)))) (2 : ZMod (3^(k+2)))) ∣
          orderOf (2 : ZMod (3^(k+2))) at hmap
        rw [map_ofNat] at hmap
        exact hmap
      rwa [ih] at hmap'
    obtain ⟨v,hv⟩ := hdiv
    have hd : ordTwo (3^(k+2)) ∣ 2*3^(k+1) := orderOf_dvd_of_pow_eq_one (power_three_eq (k+1))
    have hp : 0 < 2*3^k := by positivity
    have hvdiv : v ∣ 3 := by
      rw [hv,pow_succ] at hd
      obtain ⟨t,ht⟩ := hd
      exact ⟨t,by nlinarith [ht]⟩
    rcases (show Nat.Prime 3 by decide).eq_one_or_self_of_dvd v hvdiv with hv1 | hv3
    · have horder : ordTwo (3^(k+2)) = 2*3^k := by simpa only [hv1,mul_one] using hv
      have he := pow_orderOf_eq_one (2 : ZMod (3^(k+2)))
      change (2 : ZMod (3^(k+2)))^ordTwo (3^(k+2)) = 1 at he
      rw [horder] at he
      exact False.elim (power_three_ne k he)
    · rw [hv,hv3,pow_succ]
      ring

lemma order_one : ordTwo 1 = 1 := by
  have he : (2 : ZMod 1) = 1 := Subsingleton.elim _ _
  rw [ordTwo,he,orderOf_one]

lemma order_three_totient (k : ℕ) : ordTwo (3^k) = (3^k).totient := by
  cases k with
  | zero => simpa using order_one
  | succ k =>
    rw [order_three_succ,Nat.totient_prime_pow_succ (by decide)]
    omega

lemma excess_three (k : ℕ) : excess (3^k) = k*(3^k).totient := by
  unfold excess
  rw [Nat.sum_divisors_prime_pow (by decide : Nat.Prime 3)]
  have hs : (∑ x ∈ range (k+1), (3^x).totient / ordTwo (3^x)) = k+1 := by
    calc
      _ = ∑ x ∈ range (k+1), 1 := by
        apply sum_congr rfl
        intro x hx
        rw [order_three_totient]
        exact Nat.div_self (Nat.totient_pos.mpr (by positivity))
      _ = _ := by simp
  rw [hs,order_three_totient]
  simp [mul_comm]

lemma infinitely_many : {n : ℕ | 1 < n ∧ ¬ n.Prime ∧ IsMember n}.Infinite := by
  apply Set.infinite_of_injective_forall_mem (f := fun k : ℕ => 3^(k+2))
  · intro i j hij
    have := Nat.pow_right_injective (by decide : 1 < 3) hij
    omega
  · intro k
    refine ⟨?_,?_,?_,?_⟩
    · exact Nat.one_lt_pow (by omega) (by decide)
    · exact Nat.Prime.not_prime_pow (by omega)
    · exact Odd.pow (by decide : Odd 3)
    · rw [excess_three]
      exact dvd_mul_left _ _

lemma order_certificate {N : ℕ}
    (h : (2 : ZMod N)^364 = 1)
    (h2 : (2 : ZMod N)^182 ≠ 1)
    (h7 : (2 : ZMod N)^52 ≠ 1)
    (h13 : (2 : ZMod N)^28 ≠ 1) : ordTwo N = 364 := by
  apply orderOf_eq_of_pow_and_pow_div_prime (by decide) h
  intro p hp hd
  have hd' : p ∣ 2^2*7*13 := by norm_num at hd ⊢; exact hd
  have hm : p = 2 ∨ p = 7 ∨ p = 13 := by
    rcases hp.dvd_mul.mp hd' with h | h
    · rcases hp.dvd_mul.mp h with h | h
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp (hp.dvd_of_dvd_pow h))
      · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h))
    · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h))
  rcases hm with rfl | rfl | rfl
  · exact h2
  · exact h7
  · exact h13

lemma pow_mod_iff (N e : ℕ) : (2 : ZMod N)^e = 1 ↔ 2^e % N = 1 % N := by
  simpa only [Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one] using
    ZMod.natCast_eq_natCast_iff' (2^e) 1 N

lemma order_1093 : ordTwo 1093 = 364 := by
  apply order_certificate
  · rw [pow_mod_iff,show 364 = 2*182 by decide,pow_mul]
    decide
  all_goals simp only [ne_eq,pow_mod_iff]; decide

lemma order_1093_sq : ordTwo (1093^2) = 364 := by
  apply order_certificate
  · rw [pow_mod_iff,show 364 = 2*182 by decide,pow_mul]
    decide
  all_goals simp only [ne_eq,pow_mod_iff]; decide

lemma wieferich_counterexample : ¬ IsMember (1093^2) := by
  intro h
  have hp : Nat.Prime 1093 := by norm_num
  have hsum : (∑ d ∈ (1093^2).divisors, d.totient / ordTwo d) = 3283 := by
    rw [Nat.sum_divisors_prime_pow hp]
    simp only [sum_range_succ,sum_range_zero,pow_zero,pow_one,order_one,order_1093,
      order_1093_sq,Nat.totient_one]
    rw [Nat.totient_prime_pow hp (by decide),Nat.totient_prime hp]
    norm_num
  have he : excess (1093^2) = 1194648 := by
    rw [excess,hsum,order_1093_sq]
  have ht : (1093^2).totient = 1193556 := by
    rw [Nat.totient_prime_pow hp (by decide)]
    norm_num
  have hd := h.2
  rw [he,ht] at hd
  norm_num at hd

end A138217Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a138217.main :=
  ⟨A138217Proof.infinitely_many,A138217Proof.excess_three,A138217Proof.wieferich_counterexample⟩

