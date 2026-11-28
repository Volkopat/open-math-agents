import OMAStatements.S_mse_4756846
import Mathlib

/-!
The reverse implication is the factorization in the original question
(https://math.stackexchange.com/questions/4756846). For an odd factorization
of the exponent, divide the sum of powers in two stages. Both quotients
are integers greater than one.
For the forward implication, index two gives the Jacobsthal quotient.
Lucas certificates verify this case at fourteen prime exponents.
-/

namespace OMA.R_mse_4756846_R1

private theorem sum_lt_sum_pow {x y k : ℕ} (hx : 0 < x) (hy : 1 < y) (hk : 1 < k) :
    x + y < x ^ k + y ^ k := by
  have hxk : x ^ 1 ≤ x ^ k := pow_le_pow_right₀ (by omega : 1 ≤ x) (by omega)
  have hyk : y ^ 1 < y ^ k := pow_lt_pow_right₀ hy hk
  simpa only [pow_one] using Nat.add_lt_add_of_le_of_lt hxk hyk

private theorem quotient_not_prime {x y r s : ℕ} (hx : 0 < x) (hy : 1 < y)
    (hr : 1 < r) (hs : 1 < s) (hro : Odd r) (hso : Odd s) :
    ¬ ((x ^ (r * s) + y ^ (r * s)) / (x + y)).Prime := by
  obtain ⟨a, ha⟩ := hro.nat_add_dvd_pow_add_pow x y
  obtain ⟨b, hb⟩ := hso.nat_add_dvd_pow_add_pow (x ^ r) (y ^ r)
  have h₁ := sum_lt_sum_pow hx hy hr
  have hyp : y < y ^ r := by simpa only [pow_one] using pow_lt_pow_right₀ hy hr
  have h₂ := sum_lt_sum_pow (x := x ^ r) (by positivity) (hy.trans hyp) hs
  have ha1 : a ≠ 1 := by
    intro h
    rw [h, mul_one] at ha
    omega
  have hb1 : b ≠ 1 := by
    intro h
    rw [h, mul_one] at hb
    omega
  rw [pow_mul, pow_mul, hb, ha, Nat.mul_assoc, Nat.mul_div_cancel_left _ (by omega : 0 < x + y)]
  exact Nat.not_prime_mul ha1 hb1

-- Repeated squaring follows the A078680 Proth certificate verifier.
private def modPower (a n m : ℕ) : ℕ :=
  Nat.binaryRec (motive := fun _ => ℕ) (1 % m)
    (fun b _ t => (if b then a * (t * t) else t * t) % m) n

private theorem cast_modPower (a n m : ℕ) :
    (modPower a n m : ZMod m) = (a : ZMod m) ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [modPower, ZMod.natCast_mod]
  | bit b n ih =>
    unfold modPower
    rw [Nat.binaryRec_eq b n (Or.inl (by
      change ((1 % m) * (1 % m)) % m = 1 % m
      simpa only [one_mul] using (Nat.mul_mod 1 1 m).symm))]
    change (((if b then a * (modPower a n m * modPower a n m)
      else modPower a n m * modPower a n m) % m : ℕ) : ZMod m) =
      (a : ZMod m) ^ (n.bit b)
    rw [ZMod.natCast_mod]
    cases b
    · simp [Nat.bit, two_mul, pow_add, ih]
    · simp [Nat.bit, pow_add, ih, mul_comm, pow_mul, pow_two]

private theorem modPower_lt (a n m : ℕ) (hm : 0 < m) : modPower a n m < m := by
  induction n using Nat.binaryRec with
  | zero => exact Nat.mod_lt _ hm
  | bit b n _ =>
    unfold modPower
    rw [Nat.binaryRec_eq b n (Or.inl (by
      change ((1 % m) * (1 % m)) % m = 1 % m
      simpa only [one_mul] using (Nat.mul_mod 1 1 m).symm))]
    exact Nat.mod_lt _ hm

private theorem mem_prime_factors {q : ℕ} (hq : q.Prime) (factors : List ℕ)
    (hf : ∀ d ∈ factors, Nat.Prime d) (h : q ∣ factors.prod) : q ∈ factors := by
  induction factors with
  | nil => exact (hq.not_dvd_one h).elim
  | cons d ds ih =>
    rcases hq.dvd_mul.mp (show q ∣ d * ds.prod from h) with hd | hd
    · exact List.mem_cons.mpr (Or.inl
        ((Nat.prime_dvd_prime_iff_eq hq (hf d (by simp))).mp hd))
    · exact List.mem_cons.mpr (Or.inr (ih (fun x hx => hf x (by simp [hx])) hd))

private theorem prime_from_factors (N a : ℕ) (factors : List ℕ) (hN : 1 < N)
    (hprod : factors.prod = N - 1) (hf : ∀ d ∈ factors, Nat.Prime d)
    (hfirst : modPower a (N - 1) N = 1)
    (hrest : ∀ d ∈ factors, modPower a ((N - 1) / d) N ≠ 1) : N.Prime := by
  apply lucas_primality N (a : ZMod N)
  · simpa only [hfirst, Nat.cast_one] using (cast_modPower a (N - 1) N).symm
  · intro q hq hd hpow
    have hmem := mem_prime_factors hq factors hf (hprod.symm ▸ hd)
    have hcast : (modPower a ((N - 1) / q) N : ZMod N) = (1 : ℕ) := by
      rw [cast_modPower, Nat.cast_one, hpow]
    have hcong := (ZMod.natCast_eq_natCast_iff _ _ _).mp hcast
    have hlt : modPower a ((N - 1) / q) N < N := modPower_lt a _ N (by omega)
    exact hrest q hmem (by
      simpa only [Nat.ModEq, Nat.mod_eq_of_lt hlt,
        Nat.mod_eq_of_lt hN] using hcong)


set_option maxRecDepth 12000 in
set_option maxHeartbeats 1000000 in
private theorem prime_43691 : Nat.Prime 43691 := by
  refine prime_from_factors 43691 6 [2, 5, 17, 257]
    (by decide) (by decide) ?_ (by decide) ?_
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl <;> decide

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1000000 in
private theorem prime_174763 : Nat.Prime 174763 := by
  refine prime_from_factors 174763 17 [2, 3, 3, 7, 19, 73]
    (by decide) (by decide) ?_ (by decide) ?_
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1000000 in
private theorem prime_2796203 : Nat.Prime 2796203 := by
  refine prime_from_factors 2796203 5 [2, 23, 89, 683]
    (by decide) (by decide) ?_ (by decide) ?_
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl <;> decide

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1000000 in
private theorem prime_715827883 : Nat.Prime 715827883 := by
  refine prime_from_factors 715827883 5 [2, 3, 7, 11, 31, 151, 331]
    (by decide) (by decide) ?_ (by decide) ?_
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1000000 in
private theorem prime_2932031007403 : Nat.Prime 2932031007403 := by
  refine prime_from_factors 2932031007403 3 [2, 3, 7, 7, 43, 127, 337, 5419]
    (by decide) (by decide) ?_ (by decide) ?_
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1000000 in
private theorem prime_768614336404564651 : Nat.Prime 768614336404564651 := by
  refine prime_from_factors 768614336404564651 3 [2, 3, 5, 5, 7, 11, 13, 31, 41, 61, 151, 331, 1321]
    (by decide) (by decide) ?_ (by decide) ?_
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1000000 in
private theorem prime_121369 : Nat.Prime 121369 := by
  refine prime_from_factors 121369 7 [2, 2, 2, 3, 13, 389]
    (by decide) (by decide) ?_ (by decide) ?_
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1000000 in
private theorem prime_22366891 : Nat.Prime 22366891 := by
  refine prime_from_factors 22366891 3 [2, 3, 3, 5, 7, 13, 2731]
    (by decide) (by decide) ?_ (by decide) ?_
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1000000 in
private theorem prime_201487636602438195784363 : Nat.Prime 201487636602438195784363 := by
  refine prime_from_factors 201487636602438195784363 3 [2, 3, 7, 79, 2731, 8191, 121369, 22366891]
    (by decide) (by decide) ?_ (by decide) ?_
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact prime_121369
    · exact prime_22366891
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1000000 in
private theorem prime_268501 : Nat.Prime 268501 := by
  refine prime_from_factors 268501 6 [2, 2, 3, 5, 5, 5, 179]
    (by decide) (by decide) ?_ (by decide) ?_
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1000000 in
private theorem prime_845100400152152934331135470251 : Nat.Prime 845100400152152934331135470251 := by
  refine prime_from_factors 845100400152152934331135470251 6 [2, 5, 5, 5, 11, 31, 41, 101, 251, 601, 1801, 4051, 8101, 268501]
    (by decide) (by decide) ?_ (by decide) ?_
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact prime_268501
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1000000 in
private theorem prime_649657 : Nat.Prime 649657 := by
  refine prime_from_factors 649657 5 [2, 2, 2, 3, 3, 7, 1289]
    (by decide) (by decide) ?_ (by decide) ?_
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1000000 in
private theorem prime_92737 : Nat.Prime 92737 := by
  refine prime_from_factors 92737 5 [2, 2, 2, 2, 2, 2, 3, 3, 7, 23]
    (by decide) (by decide) ?_ (by decide) ?_
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1000000 in
private theorem prime_699053 : Nat.Prime 699053 := by
  refine prime_from_factors 699053 2 [2, 2, 174763]
    (by decide) (by decide) ?_ (by decide) ?_
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact prime_174763
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl <;> decide

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1000000 in
private theorem prime_77158673929 : Nat.Prime 77158673929 := by
  refine prime_from_factors 77158673929 11 [2, 2, 2, 3, 3, 3, 7, 73, 699053]
    (by decide) (by decide) ?_ (by decide) ?_
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact prime_699053
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1000000 in
private theorem prime_56713727820156410577229101238628035243 : Nat.Prime 56713727820156410577229101238628035243 := by
  refine prime_from_factors 56713727820156410577229101238628035243 3 [2, 3, 3, 7, 7, 19, 43, 73, 127, 337, 5419, 649657, 92737, 77158673929]
    (by decide) (by decide) ?_ (by decide) ?_
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact prime_649657
    · exact prime_92737
    · exact prime_77158673929
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- These exponents have a prime Jacobsthal quotient at base two. -/
theorem base_two_cases {p : ℕ} (hp : p ∈ ([3, 5, 7, 11, 13, 17, 19, 23, 31, 43, 61, 79, 101, 127] : List ℕ)) :
    ((2 ^ p + 1) / 3).Prime := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact prime_43691
  · exact prime_174763
  · exact prime_2796203
  · exact prime_715827883
  · exact prime_2932031007403
  · exact prime_768614336404564651
  · exact prime_201487636602438195784363
  · exact prime_845100400152152934331135470251
  · exact prime_56713727820156410577229101238628035243

/-- A base-two Jacobsthal prime provides the Fibonacci witness at index two. -/
theorem fibonacci_witness {p : ℕ} (hp : ((2 ^ p + 1) / 3).Prime) :
    ∃ n : ℕ, 1 < n ∧ ((Nat.fib n ^ p + Nat.fib (n + 1) ^ p) /
      (Nat.fib n + Nat.fib (n + 1))).Prime := by
  refine ⟨2, by decide, ?_⟩
  change ((1 ^ p + 2 ^ p) / 3).Prime
  simpa only [one_pow, add_comm] using hp

/-- Primality of the quotient forces primality of the exponent. -/
def H1 : Prop := ∀ m n : ℕ, 1 ≤ m → 1 < n →
  ((Nat.fib n ^ (2 * m + 1) + Nat.fib (n + 1) ^ (2 * m + 1)) /
    (Nat.fib n + Nat.fib (n + 1))).Prime → (2 * m + 1).Prime

/-- The remaining prime exponents, for which the witness at index two fails. -/
def H2 : Prop := ∀ m : ℕ, 1 ≤ m → (2 * m + 1).Prime →
  ¬ ((2 ^ (2 * m + 1) + 1) / 3).Prime → ∃ n : ℕ, 1 < n ∧
  ((Nat.fib n ^ (2 * m + 1) + Nat.fib (n + 1) ^ (2 * m + 1)) /
    (Nat.fib n + Nat.fib (n + 1))).Prime

theorem prime_of_prime_quotient : H1 := by
  intro m n hm hn hq
  by_contra hp
  obtain ⟨r, s, hrlt, hslt, hfactor⟩ : ∃ r s : ℕ,
      r < 2 * m + 1 ∧ s < 2 * m + 1 ∧ r * s = 2 * m + 1 := by
    by_contra h
    exact hp (Nat.prime_iff_not_exists_mul_eq.mpr ⟨by omega, h⟩)
  have hr : 1 < r := by
    by_contra! h
    interval_cases r <;> simp_all
  have hs : 1 < s := by
    by_contra! h
    interval_cases s <;> simp_all
  have hord : Odd (r * s) := ⟨m, hfactor⟩
  have hodd := Nat.odd_mul.mp hord
  have hx : 0 < Nat.fib n := Nat.fib_pos.mpr (by omega)
  have hxy := Nat.fib_lt_fib_succ (show 2 ≤ n from hn)
  have hy : 1 < Nat.fib (n + 1) := by omega
  exact quotient_not_prime hx hy hr hs hodd.1 hodd.2 (hfactor.symm ▸ hq)

theorem main : H1 → H2 → type_of% @OMA.S_mse_4756846.main := by
  intro reverse forward m hm
  constructor
  · intro hp
    by_cases hbase : ((2 ^ (2 * m + 1) + 1) / 3).Prime
    · exact fibonacci_witness hbase
    · exact forward m hm hp hbase
  · rintro ⟨n, hn, hq⟩
    exact reverse m n hm hn hq

end OMA.R_mse_4756846_R1
