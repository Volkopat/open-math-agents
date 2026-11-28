import OMAReductions.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R2

/-!
Odd primitive abundant multiples of nine with at most five distinct prime divisors.
When both five and seven are absent, ratio bounds leave only the support 3, 11, 13, 17, 19.
Splitting its exponents either contradicts abundance or produces one of four explicit
pseudoperfect divisors. When both five and seven divide n, remove the pseudoperfect divisors
945, 1575, 2205 and 315p for each prime from 11 through 103. Every remaining n has
five prime factors, its valuations at 3, 5 and 7 are fixed, and every prime factor is below 5565.
The mixed cases have the additional support restrictions recorded below.

Reference for the primitive abundant enumeration: Jacob Liddy, An algorithm to determine
all odd primitive abundant numbers with d prime divisors (2018), supervised by Jeffrey Riedl.
https://ideaexchange.uakron.edu/honors_research_projects/728/
The divisor-sum lifting argument also appears in the parent reduction by LoopsGod.
-/
open Finset
namespace OMA.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R2_H2_R1

lemma pseudoperfect_multiple {d n : ℕ} (hd : d ∣ n) (hn : 0 < n)
    (h : d.Pseudoperfect) : n.Pseudoperfect := by
  obtain ⟨k, rfl⟩ := hd
  obtain ⟨_, s, hsub, hsum⟩ := h
  have hk : 0 < k := Nat.pos_of_mul_pos_left hn
  let scale : ℕ ↪ ℕ := ⟨(· * k), fun _ _ h => Nat.eq_of_mul_eq_mul_right hk h⟩
  refine ⟨hn, s.map scale, ?_, ?_⟩
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := mem_map.mp hx
    obtain ⟨had, halt⟩ := Nat.mem_properDivisors.mp (hsub ha)
    exact Nat.mem_properDivisors.mpr
      ⟨Nat.mul_dvd_mul_right had k, Nat.mul_lt_mul_of_pos_right halt hk⟩
  · rw [sum_map]
    change (∑ a ∈ s, a * k) = d * k
    rw [← sum_mul, hsum]

lemma local_ratio (p a : ℕ) (hp : p.Prime) :
    (p^a).abundancyIndex = (∑ j ∈ range (a+1), (p : ℚ)^j) / (p : ℚ)^a := by
  rw [Nat.abundancyIndex, ← ArithmeticFunction.sigma_one_apply,
    ArithmeticFunction.sigma_one_apply_prime_pow hp]
  push_cast
  rfl

lemma local_ratio_le (p a : ℕ) (hp : p.Prime) (B : ℚ) (h : (p : ℚ) ≤ B*(p-1)) :
    (p^a).abundancyIndex ≤ B := by
  rw [local_ratio p a hp, div_le_iff₀ (pow_pos (by exact_mod_cast hp.pos) a)]
  have h1 : (1 : ℚ) < p := by exact_mod_cast hp.one_lt
  apply (mul_le_mul_iff_left₀ (sub_pos.mpr h1)).mp
  rw [geom_sum_mul, pow_succ]
  have aux := mul_le_mul_of_nonneg_right h (show 0 ≤ (p : ℚ)^a by positivity)
  linarith only [aux]

lemma ratio_factors (n : ℕ) (hn : 0 < n) :
    n.abundancyIndex = ∏ p ∈ n.primeFactors, (p^(n.factorization p)).abundancyIndex := by
  have hs : (∑ d ∈ n.divisors, (d : ℚ)) =
      ∏ p ∈ n.primeFactors, ∑ j ∈ range (n.factorization p + 1), (p : ℚ)^j := by
    simpa only [Nat.cast_sum, Nat.cast_prod, Nat.cast_pow] using
      congrArg (fun k : ℕ => (k : ℚ)) (Nat.sum_divisors hn.ne')
  have hprod : (n : ℚ) = ∏ p ∈ n.primeFactors, (p : ℚ)^n.factorization p := by
    exact_mod_cast Nat.prod_primeFactors_pow_factorization hn.ne'
  calc
    _ = (∑ d ∈ n.divisors, (d : ℚ)) / n := by simp [Nat.abundancyIndex]
    _ = _ := by
      rw [hs,hprod,← prod_div_distrib]
      exact Finset.prod_congr rfl (fun p hp => (local_ratio p _ (Nat.prime_of_mem_primeFactors hp)).symm)

lemma supported_upper {K : ℕ} (n : ℕ) (hn : 0 < n) (card : n.primeFactors.card ≤ K)
    (S : Finset ℕ) (sub : S ⊆ n.primeFactors) (A B : ℚ) (one : 1 ≤ B)
    (fixed : (∏ p ∈ S, (p^(n.factorization p)).abundancyIndex) ≤ A)
    (outside : ∀ p ∈ n.primeFactors, p ∉ S → (p^(n.factorization p)).abundancyIndex ≤ B) :
    n.abundancyIndex ≤ B^(K-S.card)*A := by
  rw [ratio_factors _ hn, ← prod_sdiff sub]
  let R := n.primeFactors \ S
  have nonnegative (p : ℕ) : 0 ≤ (p^(n.factorization p)).abundancyIndex := by
    simp only [Nat.abundancyIndex]; positivity
  have hR : (∏ p ∈ R, (p^(n.factorization p)).abundancyIndex) ≤ B^R.card := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod (fun p _ => nonnegative p)
      (fun p h => outside p (mem_sdiff.mp h).1 (mem_sdiff.mp h).2)
  have count : R.card ≤ K - S.card := by
    dsimp [R]; rw [Finset.card_sdiff_of_subset sub]; omega
  exact mul_le_mul ((hR.trans (pow_le_pow_right₀ one count))) fixed
    (prod_nonneg fun p _ => nonnegative p) (by positivity)

lemma new_prime {K : ℕ} (n : ℕ) (hn : 0 < n) (ab : n.Abundant) (card : n.primeFactors.card ≤ K)
    (S : Finset ℕ) (sub : S ⊆ n.primeFactors) (P : ℕ) (hP : 1 < P) (A : ℚ)
    (fixed : (∏ p ∈ S, (p^(n.factorization p)).abundancyIndex) ≤ A)
    (limit : ((P : ℚ)/(P-1))^(K-S.card)*A ≤ 2) :
    ∃ p ∈ n.primeFactors, p ∉ S ∧ p < P := by
  by_contra! missing
  have Ppos : (1 : ℚ) < P := by exact_mod_cast hP
  let B : ℚ := (P : ℚ)/(P-1)
  have one : 1 ≤ B := by dsimp [B]; apply (le_div_iff₀ (by linarith)).mpr; linarith
  have eq : B*(P-1) = P := div_mul_cancel₀ _ (by linarith)
  have outside (p : ℕ) (hp : p ∈ n.primeFactors) (no : p ∉ S) : (p ^ n.factorization p).abundancyIndex ≤ B := by
    have lb : (P : ℚ) ≤ p := by exact_mod_cast missing p hp no
    apply local_ratio_le _ _ (Nat.prime_of_mem_primeFactors hp)
    nlinarith [mul_nonneg (sub_nonneg.mpr one) (sub_nonneg.mpr lb)]
  exact (not_lt_of_ge ((supported_upper n hn card S sub A B one fixed outside).trans limit))
    (Nat.abundant_iff_two_lt_abundancyIndex.mp ab)
lemma ratio_to_cap (p k n : ℕ) (hp : p.Prime) (le : n.factorization p ≤ k) (v : ℚ)
    (h : (∑ i ∈ range (k+1), (p : ℚ)^i)/(p : ℚ)^k ≤ v) :
    (p^(n.factorization p)).abundancyIndex ≤ v := by
  apply (Nat.abundancyIndex_le_of_dvd (pow_ne_zero _ hp.ne_zero) (pow_dvd_pow p le)).trans
  rwa [local_ratio p k hp]

lemma ratio_nonneg (x a : ℕ) : 0 ≤ (x^a).abundancyIndex := by
  unfold Nat.abundancyIndex
  positivity

lemma list_ratio_upper (n : ℕ) (l : List ℕ) (w : List ℚ)
    (h : List.Forall₂ (fun p c => (p^(n.factorization p)).abundancyIndex ≤ c) l w) :
    (l.map (fun p => (p^(n.factorization p)).abundancyIndex)).prod ≤ w.prod := by
  induction h with
  | nil => simp
  | @cons p c ps cs first _ ih =>
    simp only [List.map_cons, List.prod_cons]
    apply mul_le_mul first ih _ ((ratio_nonneg _ _).trans first)
    exact List.prod_nonneg (fun x hx => by obtain ⟨q,_,rfl⟩ := List.mem_map.mp hx; exact ratio_nonneg _ _)

lemma next_from_bounds {K : ℕ} (n : ℕ) (npos : 0 < n) (ab : n.Abundant) (hc : n.primeFactors.card ≤ K)
    (l : List ℕ) (w : List ℚ) (P : ℕ) (hP : 1 < P) (nd : l.Nodup)
    (sub : ∀ x ∈ l, x ∈ n.primeFactors)
    (bounds : List.Forall₂ (fun p c => (p^(n.factorization p)).abundancyIndex ≤ c) l w)
    (limit : ((P : ℚ)/(P-1))^(K-l.length)*w.prod ≤ 2) :
    ∃ p ∈ n.primeFactors, p ∉ l ∧ p < P := by
  have sub' : l.toFinset ⊆ n.primeFactors := fun x hx => sub x (List.mem_toFinset.mp hx)
  have fixed : (∏ p ∈ l.toFinset, (p^(n.factorization p)).abundancyIndex) ≤ w.prod := by
    rw [List.prod_toFinset _ nd]; exact list_ratio_upper n l w bounds
  have size := List.toFinset_card_of_nodup nd
  obtain ⟨p,hp,hs,lt⟩ := new_prime n npos ab hc l.toFinset sub' P hP w.prod fixed (by rwa [size])
  exact ⟨p,hp,fun x => hs (List.mem_toFinset.mpr x),lt⟩

lemma at_most_exponent (p e n : ℕ) (hp : p.Prime) (hn : 0 < n) (h : ¬p^(e+1) ∣ n) :
    n.factorization p ≤ e := by
  have := (hp.pow_dvd_iff_le_factorization hn.ne' (k:=e+1)).not.mp h
  omega

lemma at_least_one {n p : ℕ} (h : p ∈ n.primeFactors) : 1 ≤ n.factorization p :=
  (Nat.Prime.pow_dvd_iff_le_factorization (Nat.prime_of_mem_primeFactors h)
    (Nat.mem_primeFactors.mp h).2.2 (k:=1)).mp (by simpa using Nat.dvd_of_mem_primeFactors h)

lemma exclude_full (n : ℕ) (npos : 0 < n) (ab : n.Abundant) (l : List ℕ)
    (nd : l.Nodup) (size : n.primeFactors.card ≤ l.length)
    (sub : ∀ x ∈ l, x ∈ n.primeFactors) (w : List ℚ)
    (bounds : List.Forall₂ (fun p c => (p^(n.factorization p)).abundancyIndex ≤ c) l w)
    (limit : w.prod ≤ 2) : False := by
  have sub' : l.toFinset ⊆ n.primeFactors := fun x hx => sub x (List.mem_toFinset.mp hx)
  have eq : l.toFinset = n.primeFactors := Finset.eq_of_subset_of_card_le sub' (by rwa [List.toFinset_card_of_nodup nd])
  have lt := Nat.abundant_iff_two_lt_abundancyIndex.mp ab
  rw [ratio_factors n npos, ← eq, List.prod_toFinset _ nd] at lt
  exact (not_lt_of_ge ((list_ratio_upper n l w bounds).trans limit)) lt

lemma combine_dvd {m a b : ℕ} (ha : a ∣ m) (hb : b ∣ m) (c : a.Coprime b) : a*b ∣ m :=
  c.mul_dvd_of_dvd_of_dvd ha hb

lemma complement_total (n V : ℕ) (l : List ℕ) (total : (∑ d ∈ n.divisors, d) = V)
    (pos : 0<n) (nd : l.Nodup) (test : l.all (fun d => decide (d ∣ n ∧ d<n)) = true)
    (excess : l.sum+2*n=V) : n.Pseudoperfect := by
  have sub : l.toFinset ⊆ n.properDivisors := fun d hd => Nat.mem_properDivisors.mpr
    (of_decide_eq_true (List.all_eq_true.mp test d (List.mem_toFinset.mp hd)))
  have sumL : ∑ d ∈ l.toFinset, d = l.sum := by
    calc
      _ = (l.map id).sum := List.sum_toFinset id nd
      _ = l.sum := by simp
  rw [Nat.sum_divisors_eq_sum_properDivisors_add_self] at total
  have split := Finset.sum_sdiff sub (f:=id)
  change (∑ d ∈ n.properDivisors \ l.toFinset, d) + (∑ d ∈ l.toFinset, d) = ∑ d ∈ n.properDivisors, d at split
  refine ⟨pos,n.properDivisors \ l.toFinset,Finset.sdiff_subset,?_⟩
  omega
lemma power_sum (p e : ℕ) (prime : p.Prime) :
    (∑ d ∈ (p^e).divisors,d) = ∑ i ∈ range (e+1),p^i := by
  rw [← ArithmeticFunction.sigma_one_apply,ArithmeticFunction.sigma_one_apply_prime_pow prime]
lemma factored_pair (a b x y : ℕ) (cop : a.Coprime b)
    (left : (∑ d ∈ a.divisors,d) = x) (right : (∑ d ∈ b.divisors,d) = y) :
    (∑ d ∈ (a*b).divisors,d) = x*y := by rw [cop.sum_divisors_mul,left,right]

lemma factored_power (p k V : ℕ) (prime : p.Prime) (w : (∑ i ∈ range (k+1),p^i) = V) :
    (∑ d ∈ (p^k).divisors,d) = V := (power_sum p k prime).trans w
set_option maxRecDepth 12000 in
lemma base_945 : (945 : ℕ).Pseudoperfect :=
  complement_total 945 1920 [27, 3]
    (factored_pair 27 35 40 48 (by decide)
    (factored_power 3 3 40 (by decide) (by decide)) (factored_pair 5 7 6 8 (by decide)
    (factored_power 5 1 6 (by decide) (by decide)) (factored_power 7 1 8 (by decide) (by decide)))) (by decide) (by decide) (by decide) (by decide)
set_option maxRecDepth 12000 in
lemma base_1575 : (1575 : ℕ).Pseudoperfect :=
  complement_total 1575 3224 [63, 7, 3, 1]
    (factored_pair 9 175 13 248 (by decide)
    (factored_power 3 2 13 (by decide) (by decide)) (factored_pair 25 7 31 8 (by decide)
    (factored_power 5 2 31 (by decide) (by decide)) (factored_power 7 1 8 (by decide) (by decide)))) (by decide) (by decide) (by decide) (by decide)
set_option maxRecDepth 12000 in
lemma base_2205 : (2205 : ℕ).Pseudoperfect :=
  complement_total 2205 4446 [35, 1]
    (factored_pair 9 245 13 342 (by decide)
    (factored_power 3 2 13 (by decide) (by decide)) (factored_pair 5 49 6 57 (by decide)
    (factored_power 5 1 6 (by decide) (by decide)) (factored_power 7 2 57 (by decide) (by decide)))) (by decide) (by decide) (by decide) (by decide)
set_option maxRecDepth 12000 in
lemma base_3465 : (3465 : ℕ).Pseudoperfect :=
  complement_total 3465 7488 [495, 63]
    (factored_pair 9 385 13 576 (by decide)
    (factored_power 3 2 13 (by decide) (by decide)) (factored_pair 5 77 6 96 (by decide)
    (factored_power 5 1 6 (by decide) (by decide)) (factored_pair 7 11 8 12 (by decide)
    (factored_power 7 1 8 (by decide) (by decide)) (factored_power 11 1 12 (by decide) (by decide))))) (by decide) (by decide) (by decide) (by decide)
set_option maxRecDepth 12000 in
lemma base_4095 : (4095 : ℕ).Pseudoperfect :=
  complement_total 4095 8736 [455, 91]
    (factored_pair 9 455 13 672 (by decide)
    (factored_power 3 2 13 (by decide) (by decide)) (factored_pair 5 91 6 112 (by decide)
    (factored_power 5 1 6 (by decide) (by decide)) (factored_pair 7 13 8 14 (by decide)
    (factored_power 7 1 8 (by decide) (by decide)) (factored_power 13 1 14 (by decide) (by decide))))) (by decide) (by decide) (by decide) (by decide)
set_option maxRecDepth 12000 in
lemma base_5355 : (5355 : ℕ).Pseudoperfect :=
  complement_total 5355 11232 [357, 153, 9, 3]
    (factored_pair 9 595 13 864 (by decide)
    (factored_power 3 2 13 (by decide) (by decide)) (factored_pair 5 119 6 144 (by decide)
    (factored_power 5 1 6 (by decide) (by decide)) (factored_pair 7 17 8 18 (by decide)
    (factored_power 7 1 8 (by decide) (by decide)) (factored_power 17 1 18 (by decide) (by decide))))) (by decide) (by decide) (by decide) (by decide)
set_option maxRecDepth 12000 in
lemma base_5985 : (5985 : ℕ).Pseudoperfect :=
  complement_total 5985 12480 [399, 105, 5, 1]
    (factored_pair 9 665 13 960 (by decide)
    (factored_power 3 2 13 (by decide) (by decide)) (factored_pair 5 133 6 160 (by decide)
    (factored_power 5 1 6 (by decide) (by decide)) (factored_pair 7 19 8 20 (by decide)
    (factored_power 7 1 8 (by decide) (by decide)) (factored_power 19 1 20 (by decide) (by decide))))) (by decide) (by decide) (by decide) (by decide)
set_option maxRecDepth 12000 in
lemma base_7245 : (7245 : ℕ).Pseudoperfect :=
  complement_total 7245 14976 [483, 3]
    (factored_pair 9 805 13 1152 (by decide)
    (factored_power 3 2 13 (by decide) (by decide)) (factored_pair 5 161 6 192 (by decide)
    (factored_power 5 1 6 (by decide) (by decide)) (factored_pair 7 23 8 24 (by decide)
    (factored_power 7 1 8 (by decide) (by decide)) (factored_power 23 1 24 (by decide) (by decide))))) (by decide) (by decide) (by decide) (by decide)
set_option maxRecDepth 12000 in
lemma base_9135 : (9135 : ℕ).Pseudoperfect :=
  complement_total 9135 18720 [435, 15]
    (factored_pair 9 1015 13 1440 (by decide)
    (factored_power 3 2 13 (by decide) (by decide)) (factored_pair 5 203 6 240 (by decide)
    (factored_power 5 1 6 (by decide) (by decide)) (factored_pair 7 29 8 30 (by decide)
    (factored_power 7 1 8 (by decide) (by decide)) (factored_power 29 1 30 (by decide) (by decide))))) (by decide) (by decide) (by decide) (by decide)
set_option maxRecDepth 12000 in
lemma base_9765 : (9765 : ℕ).Pseudoperfect :=
  complement_total 9765 19968 [315, 105, 15, 3]
    (factored_pair 9 1085 13 1536 (by decide)
    (factored_power 3 2 13 (by decide) (by decide)) (factored_pair 5 217 6 256 (by decide)
    (factored_power 5 1 6 (by decide) (by decide)) (factored_pair 7 31 8 32 (by decide)
    (factored_power 7 1 8 (by decide) (by decide)) (factored_power 31 1 32 (by decide) (by decide))))) (by decide) (by decide) (by decide) (by decide)
set_option maxRecDepth 12000 in
lemma base_11655 : (11655 : ℕ).Pseudoperfect :=
  complement_total 11655 23712 [333, 63, 5, 1]
    (factored_pair 9 1295 13 1824 (by decide)
    (factored_power 3 2 13 (by decide) (by decide)) (factored_pair 5 259 6 304 (by decide)
    (factored_power 5 1 6 (by decide) (by decide)) (factored_pair 7 37 8 38 (by decide)
    (factored_power 7 1 8 (by decide) (by decide)) (factored_power 37 1 38 (by decide) (by decide))))) (by decide) (by decide) (by decide) (by decide)
set_option maxRecDepth 12000 in
lemma base_12915 : (12915 : ℕ).Pseudoperfect :=
  complement_total 12915 26208 [369, 9]
    (factored_pair 9 1435 13 2016 (by decide)
    (factored_power 3 2 13 (by decide) (by decide)) (factored_pair 5 287 6 336 (by decide)
    (factored_power 5 1 6 (by decide) (by decide)) (factored_pair 7 41 8 42 (by decide)
    (factored_power 7 1 8 (by decide) (by decide)) (factored_power 41 1 42 (by decide) (by decide))))) (by decide) (by decide) (by decide) (by decide)
set_option maxRecDepth 12000 in
lemma base_13545 : (13545 : ℕ).Pseudoperfect :=
  complement_total 13545 27456 [315, 45, 5, 1]
    (factored_pair 9 1505 13 2112 (by decide)
    (factored_power 3 2 13 (by decide) (by decide)) (factored_pair 5 301 6 352 (by decide)
    (factored_power 5 1 6 (by decide) (by decide)) (factored_pair 7 43 8 44 (by decide)
    (factored_power 7 1 8 (by decide) (by decide)) (factored_power 43 1 44 (by decide) (by decide))))) (by decide) (by decide) (by decide) (by decide)
set_option maxRecDepth 12000 in
lemma base_14805 : (14805 : ℕ).Pseudoperfect :=
  complement_total 14805 29952 [329, 9, 3, 1]
    (factored_pair 9 1645 13 2304 (by decide)
    (factored_power 3 2 13 (by decide) (by decide)) (factored_pair 5 329 6 384 (by decide)
    (factored_power 5 1 6 (by decide) (by decide)) (factored_pair 7 47 8 48 (by decide)
    (factored_power 7 1 8 (by decide) (by decide)) (factored_power 47 1 48 (by decide) (by decide))))) (by decide) (by decide) (by decide) (by decide)
set_option maxRecDepth 12000 in
lemma base_16695 : (16695 : ℕ).Pseudoperfect :=
  complement_total 16695 33696 [265, 35, 5, 1]
    (factored_pair 9 1855 13 2592 (by decide)
    (factored_power 3 2 13 (by decide) (by decide)) (factored_pair 5 371 6 432 (by decide)
    (factored_power 5 1 6 (by decide) (by decide)) (factored_pair 7 53 8 54 (by decide)
    (factored_power 7 1 8 (by decide) (by decide)) (factored_power 53 1 54 (by decide) (by decide))))) (by decide) (by decide) (by decide) (by decide)
set_option maxRecDepth 12000 in
lemma base_18585 : (18585 : ℕ).Pseudoperfect :=
  complement_total 18585 37440 [177, 63, 21, 9]
    (factored_pair 9 2065 13 2880 (by decide)
    (factored_power 3 2 13 (by decide) (by decide)) (factored_pair 5 413 6 480 (by decide)
    (factored_power 5 1 6 (by decide) (by decide)) (factored_pair 7 59 8 60 (by decide)
    (factored_power 7 1 8 (by decide) (by decide)) (factored_power 59 1 60 (by decide) (by decide))))) (by decide) (by decide) (by decide) (by decide)
set_option maxRecDepth 12000 in
lemma base_19215 : (19215 : ℕ).Pseudoperfect :=
  complement_total 19215 38688 [183, 63, 9, 3]
    (factored_pair 9 2135 13 2976 (by decide)
    (factored_power 3 2 13 (by decide) (by decide)) (factored_pair 5 427 6 496 (by decide)
    (factored_power 5 1 6 (by decide) (by decide)) (factored_pair 7 61 8 62 (by decide)
    (factored_power 7 1 8 (by decide) (by decide)) (factored_power 61 1 62 (by decide) (by decide))))) (by decide) (by decide) (by decide) (by decide)
set_option maxRecDepth 12000 in
lemma base_21105 : (21105 : ℕ).Pseudoperfect :=
  complement_total 21105 42432 [201, 21]
    (factored_pair 9 2345 13 3264 (by decide)
    (factored_power 3 2 13 (by decide) (by decide)) (factored_pair 5 469 6 544 (by decide)
    (factored_power 5 1 6 (by decide) (by decide)) (factored_pair 7 67 8 68 (by decide)
    (factored_power 7 1 8 (by decide) (by decide)) (factored_power 67 1 68 (by decide) (by decide))))) (by decide) (by decide) (by decide) (by decide)
set_option maxRecDepth 12000 in
lemma base_22365 : (22365 : ℕ).Pseudoperfect :=
  complement_total 22365 44928 [105, 71, 21, 1]
    (factored_pair 9 2485 13 3456 (by decide)
    (factored_power 3 2 13 (by decide) (by decide)) (factored_pair 5 497 6 576 (by decide)
    (factored_power 5 1 6 (by decide) (by decide)) (factored_pair 7 71 8 72 (by decide)
    (factored_power 7 1 8 (by decide) (by decide)) (factored_power 71 1 72 (by decide) (by decide))))) (by decide) (by decide) (by decide) (by decide)
set_option maxRecDepth 12000 in
lemma base_22995 : (22995 : ℕ).Pseudoperfect :=
  complement_total 22995 46176 [105, 73, 7, 1]
    (factored_pair 9 2555 13 3552 (by decide)
    (factored_power 3 2 13 (by decide) (by decide)) (factored_pair 5 511 6 592 (by decide)
    (factored_power 5 1 6 (by decide) (by decide)) (factored_pair 7 73 8 74 (by decide)
    (factored_power 7 1 8 (by decide) (by decide)) (factored_power 73 1 74 (by decide) (by decide))))) (by decide) (by decide) (by decide) (by decide)
set_option maxRecDepth 12000 in
lemma base_24885 : (24885 : ℕ).Pseudoperfect :=
  complement_total 24885 49920 [105, 45]
    (factored_pair 9 2765 13 3840 (by decide)
    (factored_power 3 2 13 (by decide) (by decide)) (factored_pair 5 553 6 640 (by decide)
    (factored_power 5 1 6 (by decide) (by decide)) (factored_pair 7 79 8 80 (by decide)
    (factored_power 7 1 8 (by decide) (by decide)) (factored_power 79 1 80 (by decide) (by decide))))) (by decide) (by decide) (by decide) (by decide)
set_option maxRecDepth 12000 in
lemma base_26145 : (26145 : ℕ).Pseudoperfect :=
  complement_total 26145 52416 [105, 21]
    (factored_pair 9 2905 13 4032 (by decide)
    (factored_power 3 2 13 (by decide) (by decide)) (factored_pair 5 581 6 672 (by decide)
    (factored_power 5 1 6 (by decide) (by decide)) (factored_pair 7 83 8 84 (by decide)
    (factored_power 7 1 8 (by decide) (by decide)) (factored_power 83 1 84 (by decide) (by decide))))) (by decide) (by decide) (by decide) (by decide)
set_option maxRecDepth 12000 in
lemma base_28035 : (28035 : ℕ).Pseudoperfect :=
  complement_total 28035 56160 [89, 1]
    (factored_pair 9 3115 13 4320 (by decide)
    (factored_power 3 2 13 (by decide) (by decide)) (factored_pair 5 623 6 720 (by decide)
    (factored_power 5 1 6 (by decide) (by decide)) (factored_pair 7 89 8 90 (by decide)
    (factored_power 7 1 8 (by decide) (by decide)) (factored_power 89 1 90 (by decide) (by decide))))) (by decide) (by decide) (by decide) (by decide)
set_option maxRecDepth 12000 in
lemma base_30555 : (30555 : ℕ).Pseudoperfect :=
  complement_total 30555 61152 [35, 7]
    (factored_pair 9 3395 13 4704 (by decide)
    (factored_power 3 2 13 (by decide) (by decide)) (factored_pair 5 679 6 784 (by decide)
    (factored_power 5 1 6 (by decide) (by decide)) (factored_pair 7 97 8 98 (by decide)
    (factored_power 7 1 8 (by decide) (by decide)) (factored_power 97 1 98 (by decide) (by decide))))) (by decide) (by decide) (by decide) (by decide)
set_option maxRecDepth 12000 in
lemma base_31815 : (31815 : ℕ).Pseudoperfect :=
  complement_total 31815 63648 [15, 3]
    (factored_pair 9 3535 13 4896 (by decide)
    (factored_power 3 2 13 (by decide) (by decide)) (factored_pair 5 707 6 816 (by decide)
    (factored_power 5 1 6 (by decide) (by decide)) (factored_pair 7 101 8 102 (by decide)
    (factored_power 7 1 8 (by decide) (by decide)) (factored_power 101 1 102 (by decide) (by decide))))) (by decide) (by decide) (by decide) (by decide)
set_option maxRecDepth 12000 in
lemma base_32445 : (32445 : ℕ).Pseudoperfect :=
  complement_total 32445 64896 [5, 1]
    (factored_pair 9 3605 13 4992 (by decide)
    (factored_power 3 2 13 (by decide) (by decide)) (factored_pair 5 721 6 832 (by decide)
    (factored_power 5 1 6 (by decide) (by decide)) (factored_pair 7 103 8 104 (by decide)
    (factored_power 7 1 8 (by decide) (by decide)) (factored_power 103 1 104 (by decide) (by decide))))) (by decide) (by decide) (by decide) (by decide)
set_option maxRecDepth 12000 in
lemma base_1555265892609 : (1555265892609 : ℕ).Pseudoperfect :=
  complement_total 1555265892609 3111617775609 [867, 11, 1, 146523, 3165723, 60148737, 1022528529]
    (factored_pair 729 2133423721 1093 2846859813 (by decide)
    (factored_power 3 6 1093 (by decide) (by decide)) (factored_pair 121 17631601 133 21404961 (by decide)
    (factored_power 11 2 133 (by decide) (by decide)) (factored_pair 169 104329 183 116967 (by decide)
    (factored_power 13 2 183 (by decide) (by decide)) (factored_pair 289 361 307 381 (by decide)
    (factored_power 17 2 307 (by decide) (by decide)) (factored_power 19 2 381 (by decide) (by decide)))))) (by decide) (by decide) (by decide) (by decide)
set_option maxRecDepth 12000 in
lemma base_5702641606233 : (5702641606233 : ℕ).Pseudoperfect :=
  complement_total 5702641606233 11406618097056 [9801, 429, 3, 642447, 84474819, 1249757091]
    (factored_pair 243 23467660931 364 31336862904 (by decide)
    (factored_power 3 5 364 (by decide) (by decide)) (factored_pair 1331 17631601 1464 21404961 (by decide)
    (factored_power 11 3 1464 (by decide) (by decide)) (factored_pair 169 104329 183 116967 (by decide)
    (factored_power 13 2 183 (by decide) (by decide)) (factored_pair 289 361 307 381 (by decide)
    (factored_power 17 2 307 (by decide) (by decide)) (factored_power 19 2 381 (by decide) (by decide)))))) (by decide) (by decide) (by decide) (by decide)
set_option maxRecDepth 12000 in
lemma base_114571254088863 : (114571254088863 : ℕ).Pseudoperfect :=
  complement_total 114571254088863 229152954139200 [26163, 1927341, 278871417, 10165136553]
    (factored_pair 243 471486642341 364 629541082800 (by decide)
    (factored_power 3 5 364 (by decide) (by decide)) (factored_pair 121 3896583821 133 4733391600 (by decide)
    (factored_power 11 2 133 (by decide) (by decide)) (factored_pair 2197 1773593 2380 1988820 (by decide)
    (factored_power 13 3 2380 (by decide) (by decide)) (factored_pair 4913 361 5220 381 (by decide)
    (factored_power 17 3 5220 (by decide) (by decide)) (factored_power 19 2 381 (by decide) (by decide)))))) (by decide) (by decide) (by decide) (by decide)
set_option maxRecDepth 12000 in
lemma base_1664652927055833 : (1664652927055833 : ℕ).Pseudoperfect :=
  complement_total 1664652927055833 3329387250294560 [2223, 17, 9, 177957, 497284359, 80898718329]
    (factored_pair 243 6850423568131 364 9146668270040 (by decide)
    (factored_power 3 5 364 (by decide) (by decide)) (factored_pair 121 56615070811 133 68771941880 (by decide)
    (factored_power 11 2 133 (by decide) (by decide)) (factored_pair 28561 1982251 30941 2222680 (by decide)
    (factored_power 13 4 30941 (by decide) (by decide)) (factored_pair 289 6859 307 7240 (by decide)
    (factored_power 17 2 307 (by decide) (by decide)) (factored_power 19 3 7240 (by decide) (by decide)))))) (by decide) (by decide) (by decide) (by decide)

set_option maxHeartbeats 3500000 in
lemma shape_3_11_13_17_19 (n : ℕ) (npos : 0 < n) (ab : n.Abundant) (hc : n.primeFactors.card ≤ 5)
    (m3 : 3 ∈ n.primeFactors) (m11 : 11 ∈ n.primeFactors) (m13 : 13 ∈ n.primeFactors) (m17 : 17 ∈ n.primeFactors) (m19 : 19 ∈ n.primeFactors)
    (lower3 : 2 ≤ n.factorization 3) : n.Pseudoperfect := by
  have sub : ∀ x ∈ ([3, 11, 13, 17, 19] : List ℕ), x ∈ n.primeFactors := by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption
  have exc := exclude_full n npos ab [3, 11, 13, 17, 19] (by decide) hc sub
  have c3 := local_ratio_le 3 (n.factorization 3) (by decide) (3/2) (by norm_num)
  have c11 := local_ratio_le 11 (n.factorization 11) (by decide) (11/10) (by norm_num)
  have c13 := local_ratio_le 13 (n.factorization 13) (by decide) (13/12) (by norm_num)
  have c17 := local_ratio_le 17 (n.factorization 17) (by decide) (17/16) (by norm_num)
  have c19 := local_ratio_le 19 (n.factorization 19) (by decide) (19/18) (by norm_num)
  by_cases d3_3 : 3 ≤ n.factorization 3
  ·
    by_cases d3_4 : 4 ≤ n.factorization 3
    ·
      by_cases d11_2 : 2 ≤ n.factorization 11
      ·
        by_cases d13_2 : 2 ≤ n.factorization 13
        ·
          by_cases d3_5 : 5 ≤ n.factorization 3
          ·
            by_cases d17_2 : 2 ≤ n.factorization 17
            ·
              by_cases d19_2 : 2 ≤ n.factorization 19
              ·
                by_cases d3_6 : 6 ≤ n.factorization 3
                ·
                  exact pseudoperfect_multiple (combine_dvd (combine_dvd (combine_dvd (combine_dvd ((Nat.Prime.pow_dvd_iff_le_factorization (by decide : Nat.Prime 3) npos.ne' (k:=6)).mpr (by omega)) ((Nat.Prime.pow_dvd_iff_le_factorization (by decide : Nat.Prime 11) npos.ne' (k:=2)).mpr (by omega)) (by decide)) ((Nat.Prime.pow_dvd_iff_le_factorization (by decide : Nat.Prime 13) npos.ne' (k:=2)).mpr (by omega)) (by decide)) ((Nat.Prime.pow_dvd_iff_le_factorization (by decide : Nat.Prime 17) npos.ne' (k:=2)).mpr (by omega)) (by decide)) ((Nat.Prime.pow_dvd_iff_le_factorization (by decide : Nat.Prime 19) npos.ne' (k:=2)).mpr (by omega)) (by decide)) npos base_1555265892609
                ·
                  have c3 := ratio_to_cap 3 5 n (by decide) (by omega) (364/243) (by norm_num [Finset.sum_range_succ])
                  by_cases d11_3 : 3 ≤ n.factorization 11
                  ·
                    exact pseudoperfect_multiple (combine_dvd (combine_dvd (combine_dvd (combine_dvd ((Nat.Prime.pow_dvd_iff_le_factorization (by decide : Nat.Prime 3) npos.ne' (k:=5)).mpr (by omega)) ((Nat.Prime.pow_dvd_iff_le_factorization (by decide : Nat.Prime 11) npos.ne' (k:=3)).mpr (by omega)) (by decide)) ((Nat.Prime.pow_dvd_iff_le_factorization (by decide : Nat.Prime 13) npos.ne' (k:=2)).mpr (by omega)) (by decide)) ((Nat.Prime.pow_dvd_iff_le_factorization (by decide : Nat.Prime 17) npos.ne' (k:=2)).mpr (by omega)) (by decide)) ((Nat.Prime.pow_dvd_iff_le_factorization (by decide : Nat.Prime 19) npos.ne' (k:=2)).mpr (by omega)) (by decide)) npos base_5702641606233
                  ·
                    have c11 := ratio_to_cap 11 2 n (by decide) (by omega) (133/121) (by norm_num [Finset.sum_range_succ])
                    by_cases d13_3 : 3 ≤ n.factorization 13
                    ·
                      by_cases d17_3 : 3 ≤ n.factorization 17
                      ·
                        exact pseudoperfect_multiple (combine_dvd (combine_dvd (combine_dvd (combine_dvd ((Nat.Prime.pow_dvd_iff_le_factorization (by decide : Nat.Prime 3) npos.ne' (k:=5)).mpr (by omega)) ((Nat.Prime.pow_dvd_iff_le_factorization (by decide : Nat.Prime 11) npos.ne' (k:=2)).mpr (by omega)) (by decide)) ((Nat.Prime.pow_dvd_iff_le_factorization (by decide : Nat.Prime 13) npos.ne' (k:=3)).mpr (by omega)) (by decide)) ((Nat.Prime.pow_dvd_iff_le_factorization (by decide : Nat.Prime 17) npos.ne' (k:=3)).mpr (by omega)) (by decide)) ((Nat.Prime.pow_dvd_iff_le_factorization (by decide : Nat.Prime 19) npos.ne' (k:=2)).mpr (by omega)) (by decide)) npos base_114571254088863
                      ·
                        have c17 := ratio_to_cap 17 2 n (by decide) (by omega) (307/289) (by norm_num [Finset.sum_range_succ])
                        by_cases d19_3 : 3 ≤ n.factorization 19
                        ·
                          by_cases d13_4 : 4 ≤ n.factorization 13
                          ·
                            exact pseudoperfect_multiple (combine_dvd (combine_dvd (combine_dvd (combine_dvd ((Nat.Prime.pow_dvd_iff_le_factorization (by decide : Nat.Prime 3) npos.ne' (k:=5)).mpr (by omega)) ((Nat.Prime.pow_dvd_iff_le_factorization (by decide : Nat.Prime 11) npos.ne' (k:=2)).mpr (by omega)) (by decide)) ((Nat.Prime.pow_dvd_iff_le_factorization (by decide : Nat.Prime 13) npos.ne' (k:=4)).mpr (by omega)) (by decide)) ((Nat.Prime.pow_dvd_iff_le_factorization (by decide : Nat.Prime 17) npos.ne' (k:=2)).mpr (by omega)) (by decide)) ((Nat.Prime.pow_dvd_iff_le_factorization (by decide : Nat.Prime 19) npos.ne' (k:=3)).mpr (by omega)) (by decide)) npos base_1664652927055833
                          ·
                            have c13 := ratio_to_cap 13 3 n (by decide) (by omega) (2380/2197) (by norm_num [Finset.sum_range_succ])
                            exact (exc [(364/243), (133/121), (2380/2197), (307/289), (19/18)] (.cons c3 (.cons c11 (.cons c13 (.cons c17 (.cons c19 .nil))))) (by norm_num [List.prod_cons])).elim
                        ·
                          have c19 := ratio_to_cap 19 2 n (by decide) (by omega) (381/361) (by norm_num [Finset.sum_range_succ])
                          exact (exc [(364/243), (133/121), (13/12), (307/289), (381/361)] (.cons c3 (.cons c11 (.cons c13 (.cons c17 (.cons c19 .nil))))) (by norm_num [List.prod_cons])).elim
                    ·
                      have c13 := ratio_to_cap 13 2 n (by decide) (by omega) (183/169) (by norm_num [Finset.sum_range_succ])
                      exact (exc [(364/243), (133/121), (183/169), (17/16), (19/18)] (.cons c3 (.cons c11 (.cons c13 (.cons c17 (.cons c19 .nil))))) (by norm_num [List.prod_cons])).elim
              ·
                have c19 := ratio_to_cap 19 1 n (by decide) (by omega) (20/19) (by norm_num [Finset.sum_range_succ])
                exact (exc [(3/2), (11/10), (13/12), (17/16), (20/19)] (.cons c3 (.cons c11 (.cons c13 (.cons c17 (.cons c19 .nil))))) (by norm_num [List.prod_cons])).elim
            ·
              have c17 := ratio_to_cap 17 1 n (by decide) (by omega) (18/17) (by norm_num [Finset.sum_range_succ])
              exact (exc [(3/2), (11/10), (13/12), (18/17), (19/18)] (.cons c3 (.cons c11 (.cons c13 (.cons c17 (.cons c19 .nil))))) (by norm_num [List.prod_cons])).elim
          ·
            have c3 := ratio_to_cap 3 4 n (by decide) (by omega) (121/81) (by norm_num [Finset.sum_range_succ])
            exact (exc [(121/81), (11/10), (13/12), (17/16), (19/18)] (.cons c3 (.cons c11 (.cons c13 (.cons c17 (.cons c19 .nil))))) (by norm_num [List.prod_cons])).elim
        ·
          have c13 := ratio_to_cap 13 1 n (by decide) (by omega) (14/13) (by norm_num [Finset.sum_range_succ])
          exact (exc [(3/2), (11/10), (14/13), (17/16), (19/18)] (.cons c3 (.cons c11 (.cons c13 (.cons c17 (.cons c19 .nil))))) (by norm_num [List.prod_cons])).elim
      ·
        have c11 := ratio_to_cap 11 1 n (by decide) (by omega) (12/11) (by norm_num [Finset.sum_range_succ])
        exact (exc [(3/2), (12/11), (13/12), (17/16), (19/18)] (.cons c3 (.cons c11 (.cons c13 (.cons c17 (.cons c19 .nil))))) (by norm_num [List.prod_cons])).elim
    ·
      have c3 := ratio_to_cap 3 3 n (by decide) (by omega) (40/27) (by norm_num [Finset.sum_range_succ])
      exact (exc [(40/27), (11/10), (13/12), (17/16), (19/18)] (.cons c3 (.cons c11 (.cons c13 (.cons c17 (.cons c19 .nil))))) (by norm_num [List.prod_cons])).elim
  ·
    have c3 := ratio_to_cap 3 2 n (by decide) (by omega) (13/9) (by norm_num [Finset.sum_range_succ])
    exact (exc [(13/9), (11/10), (13/12), (17/16), (19/18)] (.cons c3 (.cons c11 (.cons c13 (.cons c17 (.cons c19 .nil))))) (by norm_num [List.prod_cons])).elim

lemma missing57_3_11_13_17 (n : ℕ) (odd : Odd n) (ab : n.Abundant) (hc : n.primeFactors.card ≤ 5)
    (no5 : 5 ∉ n.primeFactors) (no7 : 7 ∉ n.primeFactors) (e3 : 2 ≤ n.factorization 3)
    (m3 : 3 ∈ n.primeFactors) (m11 : 11 ∈ n.primeFactors) (m13 : 13 ∈ n.primeFactors) (m17 : 17 ∈ n.primeFactors) : n.Pseudoperfect := by
  have sub : ∀ x ∈ ([3,11,13,17] : List ℕ), x ∈ n.primeFactors := by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl <;> assumption
  have c3 := local_ratio_le 3 (n.factorization 3) (by decide) (3/2) (by norm_num)
  have c11 := local_ratio_le 11 (n.factorization 11) (by decide) (11/10) (by norm_num)
  have c13 := local_ratio_le 13 (n.factorization 13) (by decide) (13/12) (by norm_num)
  have c17 := local_ratio_le 17 (n.factorization 17) (by decide) (17/16) (by norm_num)
  obtain ⟨p,mem,out,small⟩ := next_from_bounds n odd.pos ab hc [3,11,13,17] [3/2,11/10,13/12,17/16] 20 (by decide) (by decide) sub (.cons c3 (.cons c11 (.cons c13 (.cons c17 .nil)))) (by norm_num [List.prod_cons])
  have n2 : p ≠ 2 := fun h => odd.not_two_dvd_nat (h ▸ Nat.dvd_of_mem_primeFactors mem)
  have n5 : p ≠ 5 := fun h => no5 (h ▸ mem)
  have n7 : p ≠ 7 := fun h => no7 (h ▸ mem)
  have check : ∀ i : Fin 20, i.val.Prime → i.val ∉ ([3,11,13,17] : List ℕ) → i.val ≠ 2 → i.val ≠ 5 → i.val ≠ 7 → i.val ∈ ([19] : List ℕ) := by decide
  have h := check ⟨p,small⟩ (Nat.prime_of_mem_primeFactors mem) out n2 n5 n7
  change p ∈ ([19] : List ℕ) at h
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl
  · exact shape_3_11_13_17_19 n odd.pos ab hc m3 m11 m13 m17 mem e3
lemma missing57_3_11_13 (n : ℕ) (odd : Odd n) (ab : n.Abundant) (hc : n.primeFactors.card ≤ 5)
    (no5 : 5 ∉ n.primeFactors) (no7 : 7 ∉ n.primeFactors) (e3 : 2 ≤ n.factorization 3)
    (m3 : 3 ∈ n.primeFactors) (m11 : 11 ∈ n.primeFactors) (m13 : 13 ∈ n.primeFactors) : n.Pseudoperfect := by
  have sub : ∀ x ∈ ([3,11,13] : List ℕ), x ∈ n.primeFactors := by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl <;> assumption
  have c3 := local_ratio_le 3 (n.factorization 3) (by decide) (3/2) (by norm_num)
  have c11 := local_ratio_le 11 (n.factorization 11) (by decide) (11/10) (by norm_num)
  have c13 := local_ratio_le 13 (n.factorization 13) (by decide) (13/12) (by norm_num)
  obtain ⟨p,mem,out,small⟩ := next_from_bounds n odd.pos ab hc [3,11,13] [3/2,11/10,13/12] 19 (by decide) (by decide) sub (.cons c3 (.cons c11 (.cons c13 .nil))) (by norm_num [List.prod_cons])
  have n2 : p ≠ 2 := fun h => odd.not_two_dvd_nat (h ▸ Nat.dvd_of_mem_primeFactors mem)
  have n5 : p ≠ 5 := fun h => no5 (h ▸ mem)
  have n7 : p ≠ 7 := fun h => no7 (h ▸ mem)
  have check : ∀ i : Fin 19, i.val.Prime → i.val ∉ ([3,11,13] : List ℕ) → i.val ≠ 2 → i.val ≠ 5 → i.val ≠ 7 → i.val ∈ ([17] : List ℕ) := by decide
  have h := check ⟨p,small⟩ (Nat.prime_of_mem_primeFactors mem) out n2 n5 n7
  change p ∈ ([17] : List ℕ) at h
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl
  · exact missing57_3_11_13_17 n odd ab hc no5 no7 e3 m3 m11 m13 mem
lemma missing57_3_11 (n : ℕ) (odd : Odd n) (ab : n.Abundant) (hc : n.primeFactors.card ≤ 5)
    (no5 : 5 ∉ n.primeFactors) (no7 : 7 ∉ n.primeFactors) (e3 : 2 ≤ n.factorization 3)
    (m3 : 3 ∈ n.primeFactors) (m11 : 11 ∈ n.primeFactors) : n.Pseudoperfect := by
  have sub : ∀ x ∈ ([3,11] : List ℕ), x ∈ n.primeFactors := by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl <;> assumption
  have c3 := local_ratio_le 3 (n.factorization 3) (by decide) (3/2) (by norm_num)
  have c11 := local_ratio_le 11 (n.factorization 11) (by decide) (11/10) (by norm_num)
  obtain ⟨p,mem,out,small⟩ := next_from_bounds n odd.pos ab hc [3,11] [3/2,11/10] 17 (by decide) (by decide) sub (.cons c3 (.cons c11 .nil)) (by norm_num [List.prod_cons])
  have n2 : p ≠ 2 := fun h => odd.not_two_dvd_nat (h ▸ Nat.dvd_of_mem_primeFactors mem)
  have n5 : p ≠ 5 := fun h => no5 (h ▸ mem)
  have n7 : p ≠ 7 := fun h => no7 (h ▸ mem)
  have check : ∀ i : Fin 17, i.val.Prime → i.val ∉ ([3,11] : List ℕ) → i.val ≠ 2 → i.val ≠ 5 → i.val ≠ 7 → i.val ∈ ([13] : List ℕ) := by decide
  have h := check ⟨p,small⟩ (Nat.prime_of_mem_primeFactors mem) out n2 n5 n7
  change p ∈ ([13] : List ℕ) at h
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl
  · exact missing57_3_11_13 n odd ab hc no5 no7 e3 m3 m11 mem
lemma missing57_3_13 (n : ℕ) (odd : Odd n) (ab : n.Abundant) (hc : n.primeFactors.card ≤ 5)
    (no5 : 5 ∉ n.primeFactors) (no7 : 7 ∉ n.primeFactors) (e3 : 2 ≤ n.factorization 3)
    (m3 : 3 ∈ n.primeFactors) (m13 : 13 ∈ n.primeFactors) : n.Pseudoperfect := by
  have sub : ∀ x ∈ ([3,13] : List ℕ), x ∈ n.primeFactors := by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl <;> assumption
  have c3 := local_ratio_le 3 (n.factorization 3) (by decide) (3/2) (by norm_num)
  have c13 := local_ratio_le 13 (n.factorization 13) (by decide) (13/12) (by norm_num)
  obtain ⟨p,mem,out,small⟩ := next_from_bounds n odd.pos ab hc [3,13] [3/2,13/12] 15 (by decide) (by decide) sub (.cons c3 (.cons c13 .nil)) (by norm_num [List.prod_cons])
  have n2 : p ≠ 2 := fun h => odd.not_two_dvd_nat (h ▸ Nat.dvd_of_mem_primeFactors mem)
  have n5 : p ≠ 5 := fun h => no5 (h ▸ mem)
  have n7 : p ≠ 7 := fun h => no7 (h ▸ mem)
  have check : ∀ i : Fin 15, i.val.Prime → i.val ∉ ([3,13] : List ℕ) → i.val ≠ 2 → i.val ≠ 5 → i.val ≠ 7 → i.val ∈ ([11] : List ℕ) := by decide
  have h := check ⟨p,small⟩ (Nat.prime_of_mem_primeFactors mem) out n2 n5 n7
  change p ∈ ([11] : List ℕ) at h
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl
  · exact missing57_3_11_13 n odd ab hc no5 no7 e3 m3 mem m13
lemma missing57_3 (n : ℕ) (odd : Odd n) (ab : n.Abundant) (hc : n.primeFactors.card ≤ 5)
    (no5 : 5 ∉ n.primeFactors) (no7 : 7 ∉ n.primeFactors) (e3 : 2 ≤ n.factorization 3)
    (m3 : 3 ∈ n.primeFactors) : n.Pseudoperfect := by
  have sub : ∀ x ∈ ([3] : List ℕ), x ∈ n.primeFactors := by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl <;> assumption
  have c3 := local_ratio_le 3 (n.factorization 3) (by decide) (3/2) (by norm_num)
  obtain ⟨p,mem,out,small⟩ := next_from_bounds n odd.pos ab hc [3] [3/2] 15 (by decide) (by decide) sub (.cons c3 .nil) (by norm_num [List.prod_cons])
  have n2 : p ≠ 2 := fun h => odd.not_two_dvd_nat (h ▸ Nat.dvd_of_mem_primeFactors mem)
  have n5 : p ≠ 5 := fun h => no5 (h ▸ mem)
  have n7 : p ≠ 7 := fun h => no7 (h ▸ mem)
  have check : ∀ i : Fin 15, i.val.Prime → i.val ∉ ([3] : List ℕ) → i.val ≠ 2 → i.val ≠ 5 → i.val ≠ 7 → i.val ∈ ([11,13] : List ℕ) := by decide
  have h := check ⟨p,small⟩ (Nat.prime_of_mem_primeFactors mem) out n2 n5 n7
  change p ∈ ([11,13] : List ℕ) at h
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl
  · exact missing57_3_11 n odd ab hc no5 no7 e3 m3 mem
  · exact missing57_3_13 n odd ab hc no5 no7 e3 m3 mem

lemma both_from_large
    (small : ∀ p : ℕ, p.Prime → 7 < p → p < 107 → (315*p).Pseudoperfect)
    (large : ∀ n p : ℕ, Odd n → 0 < n → n.Abundant → n.primeFactors.card ≤ 5 →
      3 ∈ n.primeFactors → 5 ∈ n.primeFactors → 7 ∈ n.primeFactors → p ∈ n.primeFactors →
      107 ≤ p → p < 210 → (∀ q ∈ n.primeFactors, q ∉ ([3,5,7] : List ℕ) → p ≤ q) →
      n.factorization 3 = 2 → n.factorization 5 = 1 → n.factorization 7 = 1 → n.Pseudoperfect)
    (w945 : (945:ℕ).Pseudoperfect) (w1575 : (1575:ℕ).Pseudoperfect)
    (w2205 : (2205:ℕ).Pseudoperfect)
    (n : ℕ) (odd : Odd n) (ab : n.Abundant) (hc : n.primeFactors.card ≤ 5)
    (d9 : 9 ∣ n) (d5 : 5 ∣ n) (d7 : 7 ∣ n) : n.Pseudoperfect := by
  have d3 := dvd_trans (by decide : 3 ∣ 9) d9
  have m3 := Nat.mem_primeFactors.mpr ⟨(by decide : Nat.Prime 3),d3,odd.pos.ne'⟩
  have m5 := Nat.mem_primeFactors.mpr ⟨(by decide : Nat.Prime 5),d5,odd.pos.ne'⟩
  have m7 := Nat.mem_primeFactors.mpr ⟨(by decide : Nat.Prime 7),d7,odd.pos.ne'⟩
  have b315 : 315 ∣ n := combine_dvd (combine_dvd d9 d5 (by decide)) d7 (by decide)
  by_cases a : 945 ∣ n
  · exact pseudoperfect_multiple a odd.pos w945
  by_cases b : 1575 ∣ n
  · exact pseudoperfect_multiple b odd.pos w1575
  by_cases c : 2205 ∣ n
  · exact pseudoperfect_multiple c odd.pos w2205
  have e3 : n.factorization 3 = 2 := by
    apply Nat.le_antisymm
    · apply at_most_exponent 3 2 n (by decide) odd.pos
      intro h
      exact a (combine_dvd (combine_dvd h d5 (by decide)) d7 (by decide))
    · exact (Nat.Prime.pow_dvd_iff_le_factorization (by decide : Nat.Prime 3) odd.pos.ne' (k:=2)).mp d9
  have e5 : n.factorization 5 = 1 := by
    apply Nat.le_antisymm _ (at_least_one m5)
    apply at_most_exponent 5 1 n (by decide) odd.pos
    intro h
    exact b (combine_dvd (combine_dvd d9 h (by decide)) d7 (by decide))
  have e7 : n.factorization 7 = 1 := by
    apply Nat.le_antisymm _ (at_least_one m7)
    apply at_most_exponent 7 1 n (by decide) odd.pos
    intro h
    exact c (combine_dvd (combine_dvd d9 d5 (by decide)) h (by decide))
  have c3 := ratio_to_cap 3 2 n (by decide) e3.le (13/9) (by norm_num [Finset.sum_range_succ])
  have c5 := ratio_to_cap 5 1 n (by decide) e5.le (6/5) (by norm_num [Finset.sum_range_succ])
  have c7 := ratio_to_cap 7 1 n (by decide) e7.le (8/7) (by norm_num [Finset.sum_range_succ])
  have sub : ∀ x ∈ ([3,5,7] : List ℕ), x ∈ n.primeFactors := by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl <;> assumption
  obtain ⟨r,hr,out,lt⟩ := next_from_bounds n odd.pos ab hc [3,5,7] [13/9,6/5,8/7] 210
    (by decide) (by decide) sub (.cons c3 (.cons c5 (.cons c7 .nil))) (by norm_num [List.prod_cons])
  let R := n.primeFactors \ {3,5,7}
  have inR {x : ℕ} (hx : x ∈ n.primeFactors) (away : x ∉ ([3,5,7] : List ℕ)) : x ∈ R := by
    exact mem_sdiff.mpr ⟨hx,by simpa using away⟩
  have rR := inR hr out
  have ne : R.Nonempty := ⟨r,rR⟩
  let p := R.min' ne
  obtain ⟨mp,outside⟩ := mem_sdiff.mp (R.min'_mem ne)
  change p ∈ n.primeFactors at mp
  change p ∉ ({3,5,7} : Finset ℕ) at outside
  have pp := Nat.prime_of_mem_primeFactors mp
  have lo : 7 < p := by
    by_contra! le
    have cert : ∀ j : Fin 8, j.val.Prime → j.val ∈ ([2,3,5,7] : List ℕ) := by decide
    have vals : p ∈ ([2,3,5,7] : List ℕ) := cert ⟨p,by omega⟩ pp
    have n2 : p ≠ 2 := fun eq => odd.not_two_dvd_nat (eq ▸ Nat.dvd_of_mem_primeFactors mp)
    simp only [mem_insert,mem_singleton,not_or] at outside
    simp only [List.mem_cons,List.not_mem_nil,or_false] at vals
    omega
  have least (q : ℕ) (mq : q ∈ n.primeFactors) (out : q ∉ ([3,5,7] : List ℕ)) : p ≤ q :=
    R.min'_le _ (inR mq out)
  have hi := (least _ hr out).trans_lt lt
  by_cases smallP : p < 107
  · have cop : (315:ℕ).Coprime p := by
      rw [Nat.coprime_comm,pp.coprime_iff_not_dvd]
      intro dv
      have h1 : p ∣ 3 ∨ p ∣ 3 ∨ p ∣ 5 ∨ p ∣ 7 := by
        change p ∣ 3*(3*(5*7)) at dv
        simpa only [pp.dvd_mul] using dv
      rcases h1 with h|h|h|h <;> have := Nat.le_of_dvd (by decide) h <;> omega
    exact pseudoperfect_multiple (combine_dvd b315 (Nat.dvd_of_mem_primeFactors mp) cop) odd.pos (small p pp lo smallP)
  · exact large n p odd odd.pos ab hc m3 m5 m7 mp (by omega) hi least e3 e5 e7
set_option maxRecDepth 12000 in
lemma small_multiple (p : ℕ) (pr : p.Prime) (gt : 7<p) (lt : p<107) : (315*p).Pseudoperfect := by
  have test : ∀ i : Fin 107, i.val.Prime → 7 < i.val → i.val ∈ ([11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103] : List ℕ) := by decide
  have h : p ∈ ([11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103] : List ℕ) := test ⟨p,lt⟩ pr gt
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact base_3465
  · exact base_4095
  · exact base_5355
  · exact base_5985
  · exact base_7245
  · exact base_9135
  · exact base_9765
  · exact base_11655
  · exact base_12915
  · exact base_13545
  · exact base_14805
  · exact base_16695
  · exact base_18585
  · exact base_19215
  · exact base_21105
  · exact base_22365
  · exact base_22995
  · exact base_24885
  · exact base_26145
  · exact base_28035
  · exact base_30555
  · exact base_31815
  · exact base_32445
lemma bounded_large {n p : ℕ} (pos : 0<n) (ab : n.Abundant) (hc : n.primeFactors.card ≤ 5)
    (m3 : 3 ∈ n.primeFactors) (m5 : 5 ∈ n.primeFactors) (m7 : 7 ∈ n.primeFactors)
    (mp : p ∈ n.primeFactors) (lo : 107≤p) (hi : p<210)
    (e3 : n.factorization 3=2) (e5 : n.factorization 5=1) (e7 : n.factorization 7=1) :
    n.primeFactors.card=5 ∧ ∀ r ∈ n.primeFactors, r<5565 := by
  let l : List ℕ := [3,5,7,p]
  have nd : l.Nodup := by simp [l,ne_comm,show p≠3 by omega,show p≠5 by omega,show p≠7 by omega]
  have sub : ∀ x ∈ l, x ∈ n.primeFactors := by
    intro x hx
    simp only [l,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl <;> assumption
  have c3 := ratio_to_cap 3 2 n (by decide) e3.le (13/9) (by norm_num [Finset.sum_range_succ])
  have c5 := ratio_to_cap 5 1 n (by decide) e5.le (6/5) (by norm_num [Finset.sum_range_succ])
  have c7 := ratio_to_cap 7 1 n (by decide) e7.le (8/7) (by norm_num [Finset.sum_range_succ])
  have lb : (107:ℚ)≤p := by exact_mod_cast lo
  have cp := local_ratio_le p (n.factorization p) (Nat.prime_of_mem_primeFactors mp) (107/106) (by linarith)
  obtain ⟨q,mq,out,qt⟩ := next_from_bounds n pos ab hc l [13/9,6/5,8/7,107/106] 5565
    (by decide) nd sub (.cons c3 (.cons c5 (.cons c7 (.cons cp .nil)))) (by norm_num [l,List.prod_cons])
  have notin : q ∉ l.toFinset := by simpa using out
  have five : (insert q l.toFinset).card=5 := by rw [card_insert_of_notMem notin,List.toFinset_card_of_nodup nd]; rfl
  have same : insert q l.toFinset=n.primeFactors := Finset.eq_of_subset_of_card_le
    (Finset.insert_subset mq (fun x hx => sub x (List.mem_toFinset.mp hx))) (by omega)
  refine ⟨same ▸ five,?_⟩
  intro r hr
  rw [←same] at hr
  rcases mem_insert.mp hr with rfl|h
  · exact qt
  · have h := List.mem_toFinset.mp h
    simp only [l,List.mem_cons,List.not_mem_nil,or_false] at h
    omega
lemma next_with_5 (n : ℕ) (odd : Odd n) (ab : n.Abundant) (hc : n.primeFactors.card ≤ 5)
    (m3 : 3 ∈ n.primeFactors) (m5 : 5 ∈ n.primeFactors) (no : ¬7 ∣ n) :
    ∃ r ∈ ([11, 13, 17, 19, 23, 29, 31, 37, 41, 43] : List ℕ), r ∣ n := by
  have sub : ∀ x ∈ ([3,5] : List ℕ), x ∈ n.primeFactors := by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl <;> assumption
  have c3 := local_ratio_le 3 (n.factorization 3) (by decide) (3/2) (by norm_num)
  have cp := local_ratio_le 5 (n.factorization 5) (by decide) (5/4) (by norm_num)
  obtain ⟨r,mr,out,lt⟩ := next_from_bounds n odd.pos ab hc [3,5] [3/2,5/4] 47
    (by decide) (by decide) sub (.cons c3 (.cons cp .nil)) (by norm_num [List.prod_cons])
  have dv := Nat.dvd_of_mem_primeFactors mr
  have t : ∀ i : Fin 47, i.val.Prime → i.val ∉ ([3,5] : List ℕ) → i.val ≠ 2 → i.val ≠ 7 → i.val ∈ ([11, 13, 17, 19, 23, 29, 31, 37, 41, 43] : List ℕ) := by decide
  exact ⟨r,t ⟨r,lt⟩ (Nat.prime_of_mem_primeFactors mr) out (fun e => odd.not_two_dvd_nat (e ▸ dv)) (fun e => no (e ▸ dv)),dv⟩
lemma next_with_7 (n : ℕ) (odd : Odd n) (ab : n.Abundant) (hc : n.primeFactors.card ≤ 5)
    (m3 : 3 ∈ n.primeFactors) (m7 : 7 ∈ n.primeFactors) (no : ¬5 ∣ n) :
    ∃ r ∈ ([11, 13, 17, 19] : List ℕ), r ∣ n := by
  have sub : ∀ x ∈ ([3,7] : List ℕ), x ∈ n.primeFactors := by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl <;> assumption
  have c3 := local_ratio_le 3 (n.factorization 3) (by decide) (3/2) (by norm_num)
  have cp := local_ratio_le 7 (n.factorization 7) (by decide) (7/6) (by norm_num)
  obtain ⟨r,mr,out,lt⟩ := next_from_bounds n odd.pos ab hc [3,7] [3/2,7/6] 23
    (by decide) (by decide) sub (.cons c3 (.cons cp .nil)) (by norm_num [List.prod_cons])
  have dv := Nat.dvd_of_mem_primeFactors mr
  have t : ∀ i : Fin 23, i.val.Prime → i.val ∉ ([3,7] : List ℕ) → i.val ≠ 2 → i.val ≠ 5 → i.val ∈ ([11, 13, 17, 19] : List ℕ) := by decide
  exact ⟨r,t ⟨r,lt⟩ (Nat.prime_of_mem_primeFactors mr) out (fun e => odd.not_two_dvd_nat (e ▸ dv)) (fun e => no (e ▸ dv)),dv⟩
lemma four_with_5 (n : ℕ) (odd : Odd n) (ab : n.Abundant)
    (m3 : 3 ∈ n.primeFactors) (mp : 5 ∈ n.primeFactors) (no : ¬7 ∣ n) (a : ¬11 ∣ n) (b : ¬13 ∣ n) : 4 ≤ n.primeFactors.card := by
  by_contra! small
  have sub : ∀ x ∈ ([3,5] : List ℕ), x ∈ n.primeFactors := by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl <;> assumption
  have c3 := local_ratio_le 3 (n.factorization 3) (by decide) (3/2) (by norm_num)
  have cp := local_ratio_le 5 (n.factorization 5) (by decide) (5/4) (by norm_num)
  obtain ⟨r,mr,out,lt⟩ := next_from_bounds n odd.pos ab (show n.primeFactors.card ≤ 3 by omega) [3,5] [3/2,5/4] 16
    (by decide) (by decide) sub (.cons c3 (.cons cp .nil)) (by norm_num [List.prod_cons])
  have dv := Nat.dvd_of_mem_primeFactors mr
  have t : ∀ i : Fin 16, i.val.Prime → i.val ∉ ([3,5] : List ℕ) → i.val ≠ 2 → i.val ≠ 7 → i.val ≠ 11 → i.val ≠ 13 → False := by decide
  exact t ⟨r,lt⟩ (Nat.prime_of_mem_primeFactors mr) out (fun e => odd.not_two_dvd_nat (e ▸ dv)) (fun e => no (e ▸ dv)) (fun e => a (e ▸ dv)) (fun e => b (e ▸ dv))
lemma four_with_7 (n : ℕ) (odd : Odd n) (ab : n.Abundant)
    (m3 : 3 ∈ n.primeFactors) (mp : 7 ∈ n.primeFactors) (no : ¬5 ∣ n) : 4 ≤ n.primeFactors.card := by
  by_contra! small
  have sub : ∀ x ∈ ([3,7] : List ℕ), x ∈ n.primeFactors := by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl <;> assumption
  have c3 := local_ratio_le 3 (n.factorization 3) (by decide) (3/2) (by norm_num)
  have cp := local_ratio_le 7 (n.factorization 7) (by decide) (7/6) (by norm_num)
  obtain ⟨r,mr,out,lt⟩ := next_from_bounds n odd.pos ab (show n.primeFactors.card ≤ 3 by omega) [3,7] [3/2,7/6] 8
    (by decide) (by decide) sub (.cons c3 (.cons cp .nil)) (by norm_num [List.prod_cons])
  have dv := Nat.dvd_of_mem_primeFactors mr
  have t : ∀ i : Fin 8, i.val.Prime → i.val ∉ ([3,7] : List ℕ) → i.val ≠ 2 → i.val ≠ 5 → False := by decide
  exact t ⟨r,lt⟩ (Nat.prime_of_mem_primeFactors mr) out (fun e => odd.not_two_dvd_nat (e ▸ dv)) (fun e => no (e ▸ dv))



/-- Multiples of 315 that remain after removing the three small pseudoperfect divisors. -/
def H1 : Prop :=
  ∀ n : ℕ, Odd n → n.Abundant → n.primeFactors.card = 5 →
    n.factorization 3 = 2 → n.factorization 5 = 1 → n.factorization 7 = 1 →
    (∃ p : ℕ, p.Prime ∧ 107 ≤ p ∧ p < 210 ∧ p ∣ n) →
    (∀ r ∈ n.primeFactors, r < 5565) → n.Pseudoperfect

/-- Multiples of 63 coprime to five must acquire one of four further small primes. -/
def H2 : Prop :=
  ∀ n : ℕ, Odd n → n.Abundant → 4 ≤ n.primeFactors.card → n.primeFactors.card ≤ 5 →
    (∀ d ∈ n.properDivisors, d.Deficient) → 63 ∣ n → ¬5 ∣ n →
    (∃ r ∈ ([11,13,17,19] : List ℕ), r ∣ n) → n.Pseudoperfect

/-- Multiples of 45 coprime to seven with one of the two smallest possible extra primes. -/
def H3 : Prop :=
  ∀ n : ℕ, Odd n → n.Abundant → n.primeFactors.card ≤ 5 →
    (∀ d ∈ n.properDivisors, d.Deficient) → 45 ∣ n → ¬7 ∣ n →
    (11 ∣ n ∨ 13 ∣ n) → n.Pseudoperfect

/-- The remaining multiples of 45 have four or five distinct primes. -/
def H4 : Prop :=
  ∀ n : ℕ, Odd n → n.Abundant → 4 ≤ n.primeFactors.card → n.primeFactors.card ≤ 5 →
    (∀ d ∈ n.properDivisors, d.Deficient) → 45 ∣ n → ¬7 ∣ n → ¬11 ∣ n → ¬13 ∣ n →
    (∃ r ∈ ([17,19,23,29,31,37,41,43] : List ℕ), r ∣ n) → n.Pseudoperfect

theorem main : H1 → H2 → H3 → H4 → OMA.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R2.H2 := by
  intro both seven small other n odd ab hc prim d9
  have d3 := dvd_trans (by decide : 3 ∣ 9) d9
  have m3 := Nat.mem_primeFactors.mpr ⟨(by decide : Nat.Prime 3),d3,odd.pos.ne'⟩
  by_cases d5 : 5 ∣ n
  · have m5 := Nat.mem_primeFactors.mpr ⟨(by decide : Nat.Prime 5),d5,odd.pos.ne'⟩
    by_cases d7 : 7 ∣ n
    · apply both_from_large small_multiple _ base_945 base_1575 base_2205 n odd ab hc d9 d5 d7
      intro m p parity pos ma card a b c mp lo hi _ e3 e5 e7
      obtain ⟨five,bound⟩ := bounded_large pos ma card a b c mp lo hi e3 e5 e7
      exact both m parity ma five e3 e5 e7
        ⟨p,Nat.prime_of_mem_primeFactors mp,lo,hi,Nat.dvd_of_mem_primeFactors mp⟩ bound
    · have d45 : 45 ∣ n := combine_dvd d9 d5 (by decide)
      by_cases short : 11 ∣ n ∨ 13 ∣ n
      · exact small n odd ab hc prim d45 d7 short
      · obtain ⟨no11,no13⟩ := not_or.mp short
        apply other n odd ab (four_with_5 n odd ab m3 m5 d7 no11 no13) hc prim d45 d7 no11 no13
        obtain ⟨r,inlist,dv⟩ := next_with_5 n odd ab hc m3 m5 d7
        refine ⟨r,?_,dv⟩
        simp only [List.mem_cons,List.not_mem_nil,or_false] at inlist ⊢
        rcases inlist with rfl|rfl|tail
        · exact (no11 dv).elim
        · exact (no13 dv).elim
        · exact tail
  · by_cases d7 : 7 ∣ n
    · have m7 := Nat.mem_primeFactors.mpr ⟨(by decide : Nat.Prime 7),d7,odd.pos.ne'⟩
      exact seven n odd ab (four_with_7 n odd ab m3 m7 d5) hc prim (combine_dvd d9 d7 (by decide)) d5
        (next_with_7 n odd ab hc m3 m7 d5)
    · exact missing57_3 n odd ab hc (fun h => d5 (Nat.dvd_of_mem_primeFactors h))
        (fun h => d7 (Nat.dvd_of_mem_primeFactors h))
        ((Nat.Prime.pow_dvd_iff_le_factorization (by decide : Nat.Prime 3) odd.pos.ne' (k:=2)).mp d9) m3
end OMA.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R2_H2_R1
