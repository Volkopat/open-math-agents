import OMAReductions.R_oeis_a000215_R1

-- Reduction oeis-a000215.R1.H3.R1 of step oeis-a000215.R1.H3
-- Credit: @thepigeonslastflight

namespace OMA.R_oeis_a000215_R1_H3_R1
open OMA.R_oeis_a000215_R1

/-- The case x = 4t with t odd (x ≡ 4 mod 8), using only the factor x² + 1 = 16t² + 1.
    Python finds no odd t > 1 with 16t² + 1 ∣ 2^(4t) - 1 for 4t < 10^8. -/
def H1 : Prop := ∀ t : ℕ, Odd t → 1 < t → ¬ (16 * t ^ 2 + 1 ∣ 2 ^ (4 * t) - 1)

/-- The case 8 ∣ x. The hypotheses of H3 about 4p^k, 12p^k, 4p^a r, 36·11^k, 36·71^k and
    x % 8 = 4 are automatic or vacuous here. The family x = 8 p^k is now fully excluded:
    R1 left p = 3, k = 3 mod 4 open, and `eight_three_fails` below closes it modulo 9.
    In the family x = 16 p^k, `sixteen_prime_power` leaves six primes, each in one or two
    classes of k. In the family x = 24 p^k, `twentyfour_fails` leaves only p ∈ {3, 5, 7, 19}
    (and p = 3 is already excluded as 8·3^(k+1)). In the family x = 32 p^k,
    `thirtytwo_prime_power` leaves six primes, each in at most four classes of k. -/
def H2 : Prop := ∀ x : ℕ, 4 < x → 8 ∣ x → ¬ (x - 1).Prime →
    (¬ ∃ s : ℕ, x = 2 ^ s) →
    (∀ p k : ℕ, p.Prime → p ≠ 2 → k ≠ 0 → x ≠ 8 * p ^ k) →
    (∀ p k : ℕ, p.Prime → p ≠ 2 → k ≠ 0 → x = 16 * p ^ k →
      (p = 3 ∧ (k % 4 = 0 ∨ k % 16 = 8 ∨ k % 256 = 64)) ∨ (p = 13 ∧ k % 4 = 2) ∨
      (p = 43 ∧ (k % 8 = 4 ∨ k % 256 = 192)) ∨ (p = 193 ∧ k % 8 = 2) ∨
      (p = 241 ∧ k % 4 = 1) ∨ (p = 643 ∧ k % 16 = 4)) →
    (∀ p k : ℕ, p.Prime → p ≠ 2 → k ≠ 0 → x = 24 * p ^ k →
      p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 19) →
    (∀ p k : ℕ, p.Prime → p ≠ 2 → k ≠ 0 → x = 32 * p ^ k →
      (p = 3 ∧ (k % 4 = 1 ∨ k % 16 = 10 ∨ k % 256 = 16 ∨ k % 65536 = 51200)) ∨ (p = 11 ∧ k % 65536 = 14336) ∨
      (p = 43 ∧ (k % 8 = 5 ∨ k % 256 = 240)) ∨ (p = 331 ∧ k % 65536 = 14336) ∨
      (p = 643 ∧ k % 16 = 5) ∨ (p = 715827883 ∧ k % 32 = 5)) →
    (∀ m : ℕ, m ∣ x ^ 2 + 1 → m < 2 ^ (m.primeFactors.lcm fun q => x.gcd (q - 1))) →
    ¬ (x ^ 4 - 1 ∣ 2 ^ x - 1)

lemma sq_dvd_of_order (o t p k : ℕ) (hp : p.Prime)
    (h1 : o ∣ t * p * p ^ k) (h2 : ¬ o ∣ t * p) : p ^ 2 ∣ o := by
  by_contra hno
  have ho : o ≠ 0 := by
    rintro rfl
    apply h2
    have h := zero_dvd_iff.mp h1
    exact zero_dvd_iff.mpr ((mul_eq_zero.mp h).resolve_right (pow_ne_zero _ hp.ne_zero))
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd ho p hp.ne_one
  have ha : a ≤ 1 := by
    by_contra! ha
    exact hno (dvd_mul_of_dvd_left (pow_dvd_pow p ha) m)
  have cop : m.Coprime (p ^ (k + 1)) :=
    Nat.Coprime.pow_right (k + 1) (Nat.Coprime.symm ((hp.coprime_iff_not_dvd).mpr hm))
  have h1' : m ∣ t * p ^ (k + 1) := (dvd_mul_left m (p ^ a)).trans (by
    rw [pow_succ, mul_comm (p ^ k) p, ← mul_assoc]; exact h1)
  have mt : m ∣ t := cop.dvd_of_dvd_mul_right h1'
  apply h2
  rw [mul_comm t p]
  exact mul_dvd_mul ((pow_dvd_pow p ha).trans (by simp)) mt

/-- Prime divisors of the geometric sum, other than p, are 1 modulo p^2. -/
lemma geom_prime_sq (t p k q : ℕ) (ht : 0 < t) (hp : p.Prime) (hq : q.Prime)
    (hne : q ≠ p) (hd : q ∣ ∑ i ∈ Finset.range (p ^ k), (2 ^ (t * p)) ^ i) :
    q ≡ 1 [MOD p ^ 2] := by
  let _ : Fact q.Prime := ⟨hq⟩
  have hsum := (ZMod.natCast_eq_zero_iff _ _).mpr hd
  push_cast at hsum
  by_cases hb : (2 : ZMod q) ^ (t * p) = 1
  · simp [hb] at hsum
    have hqp : q ∣ p ^ k := (ZMod.natCast_eq_zero_iff _ _).mp (by simpa using hsum)
    exact (hne ((Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hqp))).elim
  have hbpow : ((2 : ZMod q) ^ (t * p)) ^ (p ^ k) = 1 := by
    have h := geom_sum_mul ((2 : ZMod q) ^ (t * p)) (p ^ k)
    rw [hsum, zero_mul] at h
    exact sub_eq_zero.mp h.symm
  rw [← pow_mul] at hbpow
  have two0 : (2 : ZMod q) ≠ 0 := by
    intro h
    rw [h, zero_pow (Nat.pos_iff_ne_zero.mp (Nat.mul_pos (Nat.mul_pos ht hp.pos)
      (Nat.pow_pos hp.pos)))] at hbpow
    exact zero_ne_one hbpow
  have od := orderOf_dvd_of_pow_eq_one hbpow
  have nd : ¬ orderOf (2 : ZMod q) ∣ t * p := fun h => hb (orderOf_dvd_iff_pow_eq_one.mp h)
  have sq := sq_dvd_of_order _ t p k hp od nd
  have card := ZMod.orderOf_dvd_card_sub_one two0
  exact ((Nat.modEq_iff_dvd' hq.one_le).mpr (sq.trans card)).symm

lemma geom_divisor_sq (t p k v : ℕ) (ht : 0 < t) (hp : p.Prime) (hn : ¬ p ∣ v)
    (hd : v ∣ ∑ i ∈ Finset.range (p ^ k), (2 ^ (t * p)) ^ i) : v ≡ 1 [MOD p ^ 2] := by
  induction v using Nat.recOnMul with
  | zero => simp at hn
  | one => rfl
  | prime q hq => exact geom_prime_sq t p k q ht hp hq (by rintro rfl; exact hn dvd_rfl) hd
  | mul a b' ia ib =>
    have da : a ∣ a * b' := dvd_mul_right _ _
    have db : b' ∣ a * b' := dvd_mul_left _ _
    simpa using (ia (fun h => hn (h.trans da)) (da.trans hd)).mul
      (ib (fun h => hn (h.trans db)) (db.trans hd))

/-- A divisor of 2^(t p^(k+1)) - 1 prime to p is, modulo p^2, a divisor of 2^(t p) - 1. -/
lemma small_divisor_sq (t p k v : ℕ) (ht : 0 < t) (hp : p.Prime) (hn : ¬ p ∣ v)
    (hd : v ∣ 2 ^ (t * p * p ^ k) - 1) :
    ∃ d : ℕ, d ∣ 2 ^ (t * p) - 1 ∧ d ∣ v ∧ v ≡ d [MOD p ^ 2] := by
  let G := ∑ i ∈ Finset.range (p ^ k), (2 ^ (t * p)) ^ i
  have hG : G * (2 ^ (t * p) - 1) = 2 ^ (t * p * p ^ k) - 1 := by
    rw [pow_mul 2 (t * p) (p ^ k)]
    exact geom_sum_mul_of_one_le Nat.one_le_two_pow _
  obtain ⟨r, d, hr, hdBase, h⟩ :=
    exists_dvd_and_dvd_of_dvd_mul (hG.symm ▸ hd : v ∣ G * (2 ^ (t * p) - 1))
  have dr : r ∣ v := ⟨d, h⟩
  refine ⟨d, hdBase, ⟨r, by rw [h, Nat.mul_comm]⟩, ?_⟩
  have h1 := geom_divisor_sq t p k r ht hp (fun h => hn (h.trans dr)) hr
  simpa only [h, one_mul] using h1.mul_right d

lemma pow_period (a n P q : ℕ) (h : a ^ P ≡ 1 [MOD q]) : a ^ n ≡ a ^ (n % P) [MOD q] := by
  have e : a ^ n = (a ^ P) ^ (n / P) * a ^ (n % P) := by
    rw [← pow_mul, ← pow_add, Nat.div_add_mod]
  rw [e]
  simpa using (h.pow (n / P)).mul_right (a ^ (n % P))

/-- The class k = 3 mod 4 that R1 left open also fails the test. Modulo 9, x - 1 = 8 * 3^k - 1
    must agree with a divisor of 2^24 - 1 that divides x - 1. Every such divisor that is 8 mod 9
    contains 7, 17 or 241, and none of these divides 8 * 3^k - 1 when k = 3 mod 4. -/
theorem eight_three_fails (k : ℕ) (hk : k ≠ 0) :
    ¬ ((8 * 3 ^ k) ^ 4 - 1 ∣ 2 ^ (8 * 3 ^ k) - 1) := by
  intro test
  have k4 := eight_three_exponent k hk test
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  let x := 8 * 3 ^ (j + 1)
  have hx : x = 8 * 3 * 3 ^ j := by dsimp [x]; ring
  have xpos : 0 < x := by positivity
  have x1 : x - 1 ∣ 2 ^ x - 1 := (Nat.sub_one_dvd_pow_sub_one x 4).trans test
  have x1' : x - 1 ∣ 2 ^ (8 * 3 * 3 ^ j) - 1 := by rw [← hx]; exact x1
  have x3 : 3 ∣ x := dvd_mul_of_dvd_right (dvd_pow_self 3 (by omega)) 8
  have x9 : 9 ∣ x := by
    have : 9 ∣ 3 ^ (j + 1) := by
      rw [show (9 : ℕ) = 3 ^ 2 by norm_num]; exact pow_dvd_pow 3 (by omega)
    exact dvd_mul_of_dvd_right this 8
  have n3 : ¬ 3 ∣ x - 1 := by omega
  obtain ⟨d, hd, dx, cong⟩ :=
    small_divisor_sq 8 3 j (x - 1) (by decide) Nat.prime_three n3 x1'
  have d9 : d % 9 = 8 := by
    have c : (x - 1) % 9 = d % 9 := cong
    omega
  have hd' : d ∣ 7 * (17 * (241 * 585)) := by
    have e : 2 ^ (8 * 3) - 1 = 7 * (17 * (241 * 585)) := by norm_num
    rwa [e] at hd
  have key : 7 ∣ d ∨ 17 ∣ d ∨ 241 ∣ d := by
    by_contra! h
    have c7 : d.Coprime 7 := ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr h.1).symm
    have c17 : d.Coprime 17 := ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr h.2.1).symm
    have c241 : d.Coprime 241 := ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr h.2.2).symm
    have d585 : d ∣ 585 :=
      c241.dvd_of_dvd_mul_left (c17.dvd_of_dvd_mul_left (c7.dvd_of_dvd_mul_left hd'))
    have dle := Nat.le_of_dvd (by norm_num) d585
    have cert : ∀ e : Fin 586, e.val ∣ 585 → e.val % 9 ≠ 8 := by decide +kernel
    exact cert ⟨d, by omega⟩ d585 d9
  have cert : ∀ r : Fin 240, r.val % 4 = 3 → ¬ (1 ≡ 8 * 3 ^ r.val [MOD 7]) ∧
      ¬ (1 ≡ 8 * 3 ^ r.val [MOD 17]) ∧ ¬ (1 ≡ 8 * 3 ^ r.val [MOD 241]) := by decide +kernel
  have c := cert ⟨(j + 1) % 240, Nat.mod_lt _ (by norm_num)⟩ (by show (j + 1) % 240 % 4 = 3; omega)
  have bad : ∀ l : ℕ, 3 ^ 240 ≡ 1 [MOD l] → l ∣ x - 1 → 1 ≡ 8 * 3 ^ ((j + 1) % 240) [MOD l] := by
    intro l hper hdiv
    have m1 : 1 ≡ x [MOD l] := (Nat.modEq_iff_dvd' (by omega)).mpr hdiv
    exact m1.trans ((pow_period 3 (j + 1) 240 l hper).mul_left 8)
  rcases key with h | h | h
  · exact c.1 (bad 7 (by decide) (h.trans dx))
  · exact c.2.1 (bad 17 (by decide) (h.trans dx))
  · exact c.2.2 (bad 241 (by decide) (h.trans dx))

/-- A prime dividing a product of primes is one of them. -/
lemma prime_mem_of_dvd {p : ℕ} (hp : p.Prime) :
    ∀ l : List ℕ, (∀ q ∈ l, q.Prime) → p ∣ l.prod → p ∈ l
  | [], _, h => absurd (Nat.dvd_one.mp (by simpa using h)) hp.ne_one
  | q :: l, hl, h => by
    rw [List.prod_cons] at h
    rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · exact List.mem_cons.mpr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (hl q (by simp))).mp h))
    · exact List.mem_cons_of_mem _
        (prime_mem_of_dvd hp l (fun r hr => hl r (List.mem_cons_of_mem _ hr)) h)

/-- If d ∣ t p^k - 1 and p^L = 1 mod d, then only k mod L matters. -/
lemma residue_of (t p k d L : ℕ) (hper : p ^ L ≡ 1 [MOD d]) (hpos : 0 < t * p ^ k)
    (h : d ∣ t * p ^ k - 1) : t * p ^ (k % L) ≡ 1 [MOD d] := by
  have m1 : 1 ≡ t * p ^ k [MOD d] := (Nat.modEq_iff_dvd' hpos).mpr h
  exact (m1.trans ((pow_period p k L d hper).mul_left t)).symm

lemma class_of (t p k d L a : ℕ) (hL : 0 < L) (hpos : 0 < t * p ^ k)
    (h : d ∣ t * p ^ k - 1) (hper : p ^ L ≡ 1 [MOD d])
    (cert : ∀ r : Fin L, t * p ^ r.val ≡ 1 [MOD d] → r.val = a) : k % L = a :=
  cert ⟨k % L, Nat.mod_lt _ hL⟩ (residue_of t p k d L hper hpos h)

lemma no_class (t p k d L : ℕ) (hL : 0 < L) (hpos : 0 < t * p ^ k)
    (h : d ∣ t * p ^ k - 1) (hper : p ^ L ≡ 1 [MOD d])
    (cert : ∀ r : Fin L, ¬ t * p ^ r.val ≡ 1 [MOD d]) : False :=
  cert ⟨k % L, Nat.mod_lt _ hL⟩ (residue_of t p k d L hper hpos h)

set_option maxHeartbeats 1000000 in
/-- In the family x = 16 p^k only six odd primes survive the predecessor test, each in one
    or two classes of k. -/
theorem sixteen_prime_power (p k : ℕ) (hp : p.Prime) (odd : p ≠ 2) (hk : k ≠ 0)
    (test : (16 * p ^ k) ^ 4 - 1 ∣ 2 ^ (16 * p ^ k) - 1) :
    (p = 3 ∧ (k % 4 = 0 ∨ k % 16 = 8 ∨ k % 256 = 64)) ∨ (p = 13 ∧ k % 4 = 2) ∨
    (p = 43 ∧ (k % 8 = 4 ∨ k % 256 = 192)) ∨ (p = 193 ∧ k % 8 = 2) ∨
    (p = 241 ∧ k % 4 = 1) ∨ (p = 643 ∧ k % 16 = 4) := by
  obtain ⟨d, hd, dh, plus⟩ := divisor_before 16 p k (by decide) hp hk test
  clear test
  have hpos : 0 < 16 * p ^ k := Nat.mul_pos (by norm_num) (Nat.pow_pos hp.pos)
  have hd' : d ∣ 65535 := by simpa using hd
  have hdle := Nat.le_of_dvd (by norm_num) hd'
  have dmem : ∀ a b : Fin 256, 256 * a.val + b.val ∣ 65535 → 256 * a.val + b.val ∈ [1, 3, 5,
      15, 17, 51, 85, 255, 257, 771, 1285, 3855, 4369, 13107, 21845, 65535] := by decide +kernel
  have hm : d ∈ [1, 3, 5, 15, 17, 51, 85, 255, 257, 771, 1285, 3855, 4369, 13107, 21845,
      65535] := by
    have e := dmem ⟨d / 256, by omega⟩ ⟨d % 256, Nat.mod_lt _ (by norm_num)⟩
    simp only [Nat.div_add_mod] at e
    exact e hd'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  have two : p ≠ 2 := odd
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl
  · have := prime_mem_of_dvd hp [2] (by norm_num) (by simpa using plus)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact (two rfl).elim
  · have := prime_mem_of_dvd hp [2, 2] (by norm_num) (by simpa using plus)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact (two rfl).elim
  · have := prime_mem_of_dvd hp [2, 3] (by norm_num) (by simpa using plus)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl
    · exact (two rfl).elim
    · exact Or.inl ⟨rfl, Or.inl (class_of 16 3 k 5 4 0 (by norm_num) hpos dh (by decide +kernel)
        (by decide +kernel))⟩
  · have := prime_mem_of_dvd hp [2, 2, 2, 2] (by norm_num) (by simpa using plus)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact (two rfl).elim
  · have := prime_mem_of_dvd hp [2, 3, 3] (by norm_num) (by simpa using plus)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl | rfl
    · exact (two rfl).elim
    all_goals exact Or.inl ⟨rfl, Or.inr (Or.inl (class_of 16 3 k 17 16 8 (by norm_num) hpos dh
        (by decide +kernel) (by decide +kernel)))⟩
  · have := prime_mem_of_dvd hp [2, 2, 13] (by norm_num) (by simpa using plus)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl | rfl
    · exact (two rfl).elim
    · exact (two rfl).elim
    · exact Or.inr (Or.inl ⟨rfl, class_of 16 13 k 51 4 2 (by norm_num) hpos dh (by decide +kernel)
        (by decide +kernel)⟩)
  · have := prime_mem_of_dvd hp [2, 43] (by norm_num) (by simpa using plus)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl
    · exact (two rfl).elim
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, Or.inl (class_of 16 43 k 85 8 4 (by norm_num) hpos dh
        (by decide +kernel) (by decide +kernel))⟩))
  · have := prime_mem_of_dvd hp [2, 2, 2, 2, 2, 2, 2, 2] (by norm_num) (by simpa using plus)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact (two rfl).elim
  · have := prime_mem_of_dvd hp [2, 3, 43] (by norm_num) (by simpa using plus)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl | rfl
    · exact (two rfl).elim
    · exact Or.inl ⟨rfl, Or.inr (Or.inr (class_of 16 3 k 257 256 64 (by norm_num) hpos dh
        (by decide +kernel) (by decide +kernel)))⟩
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr (class_of 16 43 k 257 256 192 (by norm_num) hpos
        dh (by decide +kernel) (by decide +kernel))⟩))
  · have := prime_mem_of_dvd hp [2, 2, 193] (by norm_num) (by simpa using plus)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl | rfl
    · exact (two rfl).elim
    · exact (two rfl).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, class_of 16 193 k 771 8 2 (by norm_num) hpos dh
        (by decide +kernel) (by decide +kernel)⟩)))
  · have := prime_mem_of_dvd hp [2, 643] (by norm_num) (by simpa using plus)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl
    · exact (two rfl).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, class_of 16 643 k 1285 16 4 (by norm_num)
        hpos dh (by decide +kernel) (by decide +kernel)⟩))))
  · have := prime_mem_of_dvd hp [2, 2, 2, 2, 241] (by norm_num) (by simpa using plus)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl | rfl | rfl | rfl
    any_goals exact (two rfl).elim
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, class_of 16 241 k 3855 4 1 (by norm_num)
      hpos dh (by decide +kernel) (by decide +kernel)⟩))))
  · have := prime_mem_of_dvd hp [2, 5, 19, 23] (by norm_num) (by simpa using plus)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl | rfl | rfl
    · exact (two rfl).elim
    · exact (no_class 16 5 k 4369 256 (by norm_num) hpos dh (by decide +kernel) (by decide +kernel)).elim
    · exact (no_class 16 19 k 4369 256 (by norm_num) hpos dh (by decide +kernel) (by decide +kernel)).elim
    · exact (no_class 16 23 k 4369 64 (by norm_num) hpos dh (by decide +kernel) (by decide +kernel)).elim
  · have := prime_mem_of_dvd hp [2, 2, 29, 113] (by norm_num) (by simpa using plus)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl | rfl | rfl
    · exact (two rfl).elim
    · exact (two rfl).elim
    · exact (no_class 16 29 k 13107 128 (by norm_num) hpos dh (by decide +kernel) (by decide +kernel)).elim
    · exact (no_class 16 113 k 13107 128 (by norm_num) hpos dh (by decide +kernel)
        (by decide +kernel)).elim
  · have := prime_mem_of_dvd hp [2, 3, 11, 331] (by norm_num) (by simpa using plus)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl | rfl | rfl
    · exact (two rfl).elim
    · exact (no_class 16 3 k 21845 256 (by norm_num) hpos dh (by decide +kernel) (by decide +kernel)).elim
    · exact (no_class 16 11 k 21845 64 (by norm_num) hpos dh (by decide +kernel) (by decide +kernel)).elim
    · exact (no_class 16 331 k 21845 256 (by norm_num) hpos dh (by decide +kernel)
        (by decide +kernel)).elim
  · have := prime_mem_of_dvd hp (List.replicate 16 2)
      (fun q hq => by rw [List.eq_of_mem_replicate hq]; exact Nat.prime_two) (by simpa using plus)
    simp at this
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact (two rfl).elim

-- The x = 32 p^k family.

/-- If q has order exactly 2^(n+1) modulo r, the solutions k of t q^k = 1 mod r form one class. -/
lemma pow2_class (t q k r n a : ℕ) (h1 : q ^ 2 ^ (n + 1) ≡ 1 [MOD r])
    (h2 : ¬ q ^ 2 ^ n ≡ 1 [MOD r]) (ha : t * q ^ a ≡ 1 [MOD r]) (hlt : a < 2 ^ (n + 1))
    (hpos : 0 < t * q ^ k) (hk : r ∣ t * q ^ k - 1) : k % 2 ^ (n + 1) = a := by
  have _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have e1 : ((q : ZMod r)) ^ 2 ^ (n + 1) = 1 := by
    have := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h1
    push_cast at this
    exact this
  have e2 : ¬ ((q : ZMod r)) ^ 2 ^ n = 1 := by
    intro h
    apply h2
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    push_cast
    exact h
  have ea : (t : ZMod r) * (q : ZMod r) ^ a = 1 := by
    have := (ZMod.natCast_eq_natCast_iff _ _ _).mpr ha
    push_cast at this
    exact this
  have ek : (t : ZMod r) * (q : ZMod r) ^ k = 1 := by
    have := (ZMod.natCast_eq_natCast_iff _ _ _).mpr ((Nat.modEq_iff_dvd' hpos).mpr hk).symm
    push_cast at this
    exact this
  have ord : orderOf (q : ZMod r) = 2 ^ (n + 1) := orderOf_eq_prime_pow e2 e1
  have key : (q : ZMod r) ^ (k + (2 ^ (n + 1) - a)) = 1 := by
    calc (q : ZMod r) ^ (k + (2 ^ (n + 1) - a))
        = (q : ZMod r) ^ k * (q : ZMod r) ^ (2 ^ (n + 1) - a) * ((t : ZMod r) * (q : ZMod r) ^ a) := by
          rw [ea, mul_one, pow_add]
      _ = ((t : ZMod r) * (q : ZMod r) ^ k) * (q : ZMod r) ^ (2 ^ (n + 1) - a + a) := by ring
      _ = 1 := by rw [ek, Nat.sub_add_cancel hlt.le, e1, one_mul]
  have hdvd : 2 ^ (n + 1) ∣ k + (2 ^ (n + 1) - a) := by
    have := orderOf_dvd_of_pow_eq_one key
    rwa [ord] at this
  have m : k + (2 ^ (n + 1) - a) ≡ a + (2 ^ (n + 1) - a) [MOD 2 ^ (n + 1)] := by
    rw [Nat.add_sub_cancel' hlt.le]
    exact (Nat.modEq_zero_iff_dvd.mpr hdvd).trans (Nat.modEq_zero_iff_dvd.mpr dvd_rfl).symm
  have := Nat.ModEq.add_right_cancel' _ m
  rw [Nat.ModEq, Nat.mod_eq_of_lt hlt] at this
  exact this

/-- If q^M = 1 but t^M ≠ 1 modulo r, then t q^k is never 1 modulo r. -/
lemma pow_no_class (t q k r M : ℕ) (h1 : q ^ M ≡ 1 [MOD r]) (h2 : ¬ t ^ M ≡ 1 [MOD r])
    (hpos : 0 < t * q ^ k) (hk : r ∣ t * q ^ k - 1) : False := by
  have m : 1 ≡ t * q ^ k [MOD r] := (Nat.modEq_iff_dvd' hpos).mpr hk
  have m2 := m.pow M
  rw [one_pow, mul_pow, ← pow_mul, mul_comm k M, pow_mul] at m2
  have m3 : t ^ M * (q ^ M) ^ k ≡ t ^ M * 1 ^ k [MOD r] := (h1.pow k).mul_left _
  rw [one_pow, mul_one] at m3
  exact h2 (m2.trans m3).symm

set_option maxRecDepth 100000 in
lemma t32_leaf_0 (p k : ℕ) (hp : p.Prime) (two : p ≠ 2) (hpos : 0 < 32 * p ^ k)
    (dh : 1 * (1 * (1 * (1 * 1))) ∣ 32 * p ^ k - 1) (plus : p ∣ 1 * (1 * (1 * (1 * 1))) + 1) :
    (p = 3 ∧ (k % 4 = 1 ∨ k % 16 = 10 ∨ k % 256 = 16 ∨ k % 65536 = 51200)) ∨ (p = 11 ∧ k % 65536 = 14336) ∨ (p = 43 ∧ (k % 8 = 5 ∨ k % 256 = 240)) ∨ (p = 331 ∧ k % 65536 = 14336) ∨ (p = 643 ∧ k % 16 = 5) ∨ (p = 715827883 ∧ k % 32 = 5) := by
  have := prime_mem_of_dvd hp (List.replicate 1 2)
    (fun q hq => by rw [List.eq_of_mem_replicate hq]; exact Nat.prime_two) (by simpa using plus)
  exact (two (List.eq_of_mem_replicate this)).elim

set_option maxRecDepth 100000 in
lemma t32_leaf_1 (p k : ℕ) (hp : p.Prime) (two : p ≠ 2) (hpos : 0 < 32 * p ^ k)
    (dh : 1 * (1 * (1 * (1 * 65537))) ∣ 32 * p ^ k - 1) (plus : p ∣ 1 * (1 * (1 * (1 * 65537))) + 1) :
    (p = 3 ∧ (k % 4 = 1 ∨ k % 16 = 10 ∨ k % 256 = 16 ∨ k % 65536 = 51200)) ∨ (p = 11 ∧ k % 65536 = 14336) ∨ (p = 43 ∧ (k % 8 = 5 ∨ k % 256 = 240)) ∨ (p = 331 ∧ k % 65536 = 14336) ∨ (p = 643 ∧ k % 16 = 5) ∨ (p = 715827883 ∧ k % 32 = 5) := by
  have := prime_mem_of_dvd hp [2, 3, 3, 11, 331] (by norm_num) (by simpa using plus)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at this
  rcases this with rfl | rfl | rfl | rfl | rfl
  · exact (two rfl).elim
  · clear plus
    have c0 := pow2_class 32 3 k 65537 15 51200 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) hpos (dvd_trans (by norm_num) dh)
    norm_num at c0
    omega
  · clear plus
    have c0 := pow2_class 32 3 k 65537 15 51200 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) hpos (dvd_trans (by norm_num) dh)
    norm_num at c0
    omega
  · clear plus
    have c0 := pow2_class 32 11 k 65537 15 14336 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) hpos (dvd_trans (by norm_num) dh)
    norm_num at c0
    omega
  · clear plus
    have c0 := pow2_class 32 331 k 65537 15 14336 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) hpos (dvd_trans (by norm_num) dh)
    norm_num at c0
    omega

set_option maxRecDepth 100000 in
lemma t32_leaf_2 (p k : ℕ) (hp : p.Prime) (two : p ≠ 2) (hpos : 0 < 32 * p ^ k)
    (dh : 1 * (1 * (1 * (257 * 1))) ∣ 32 * p ^ k - 1) (plus : p ∣ 1 * (1 * (1 * (257 * 1))) + 1) :
    (p = 3 ∧ (k % 4 = 1 ∨ k % 16 = 10 ∨ k % 256 = 16 ∨ k % 65536 = 51200)) ∨ (p = 11 ∧ k % 65536 = 14336) ∨ (p = 43 ∧ (k % 8 = 5 ∨ k % 256 = 240)) ∨ (p = 331 ∧ k % 65536 = 14336) ∨ (p = 643 ∧ k % 16 = 5) ∨ (p = 715827883 ∧ k % 32 = 5) := by
  have := prime_mem_of_dvd hp [2, 3, 43] (by norm_num) (by simpa using plus)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at this
  rcases this with rfl | rfl | rfl
  · exact (two rfl).elim
  · clear plus
    have c0 := pow2_class 32 3 k 257 7 16 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) hpos (dvd_trans (by norm_num) dh)
    norm_num at c0
    omega
  · clear plus
    have c0 := pow2_class 32 43 k 257 7 240 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) hpos (dvd_trans (by norm_num) dh)
    norm_num at c0
    omega

set_option maxRecDepth 100000 in
lemma t32_leaf_3 (p k : ℕ) (hp : p.Prime) (two : p ≠ 2) (hpos : 0 < 32 * p ^ k)
    (dh : 1 * (1 * (1 * (257 * 65537))) ∣ 32 * p ^ k - 1) (plus : p ∣ 1 * (1 * (1 * (257 * 65537))) + 1) :
    (p = 3 ∧ (k % 4 = 1 ∨ k % 16 = 10 ∨ k % 256 = 16 ∨ k % 65536 = 51200)) ∨ (p = 11 ∧ k % 65536 = 14336) ∨ (p = 43 ∧ (k % 8 = 5 ∨ k % 256 = 240)) ∨ (p = 331 ∧ k % 65536 = 14336) ∨ (p = 643 ∧ k % 16 = 5) ∨ (p = 715827883 ∧ k % 32 = 5) := by
  have := prime_mem_of_dvd hp [2, 5, 1684301] (by norm_num) (by simpa using plus)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at this
  rcases this with rfl | rfl | rfl
  · exact (two rfl).elim
  · clear plus
    have c0 := pow2_class 32 5 k 257 7 112 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) hpos (dvd_trans (by norm_num) dh)
    have c1 := pow2_class 32 5 k 65537 15 38912 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) hpos (dvd_trans (by norm_num) dh)
    norm_num at c0 c1
    omega
  · clear plus
    have c0 := pow2_class 32 1684301 k 257 7 144 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) hpos (dvd_trans (by norm_num) dh)
    have c1 := pow2_class 32 1684301 k 65537 15 26624 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) hpos (dvd_trans (by norm_num) dh)
    norm_num at c0 c1
    omega

set_option maxRecDepth 100000 in
lemma t32_leaf_4 (p k : ℕ) (hp : p.Prime) (two : p ≠ 2) (hpos : 0 < 32 * p ^ k)
    (dh : 1 * (1 * (17 * (1 * 1))) ∣ 32 * p ^ k - 1) (plus : p ∣ 1 * (1 * (17 * (1 * 1))) + 1) :
    (p = 3 ∧ (k % 4 = 1 ∨ k % 16 = 10 ∨ k % 256 = 16 ∨ k % 65536 = 51200)) ∨ (p = 11 ∧ k % 65536 = 14336) ∨ (p = 43 ∧ (k % 8 = 5 ∨ k % 256 = 240)) ∨ (p = 331 ∧ k % 65536 = 14336) ∨ (p = 643 ∧ k % 16 = 5) ∨ (p = 715827883 ∧ k % 32 = 5) := by
  have := prime_mem_of_dvd hp [2, 3, 3] (by norm_num) (by simpa using plus)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at this
  rcases this with rfl | rfl | rfl
  · exact (two rfl).elim
  · clear plus
    have c0 := pow2_class 32 3 k 17 3 10 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) hpos (dvd_trans (by norm_num) dh)
    norm_num at c0
    omega
  · clear plus
    have c0 := pow2_class 32 3 k 17 3 10 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) hpos (dvd_trans (by norm_num) dh)
    norm_num at c0
    omega

set_option maxRecDepth 100000 in
lemma t32_leaf_5 (p k : ℕ) (hp : p.Prime) (two : p ≠ 2) (hpos : 0 < 32 * p ^ k)
    (dh : 1 * (1 * (17 * (1 * 65537))) ∣ 32 * p ^ k - 1) (plus : p ∣ 1 * (1 * (17 * (1 * 65537))) + 1) :
    (p = 3 ∧ (k % 4 = 1 ∨ k % 16 = 10 ∨ k % 256 = 16 ∨ k % 65536 = 51200)) ∨ (p = 11 ∧ k % 65536 = 14336) ∨ (p = 43 ∧ (k % 8 = 5 ∨ k % 256 = 240)) ∨ (p = 331 ∧ k % 65536 = 14336) ∨ (p = 643 ∧ k % 16 = 5) ∨ (p = 715827883 ∧ k % 32 = 5) := by
  have := prime_mem_of_dvd hp [2, 5, 43, 2591] (by norm_num) (by simpa using plus)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at this
  rcases this with rfl | rfl | rfl | rfl
  · exact (two rfl).elim
  · clear plus
    have c0 := pow2_class 32 5 k 17 3 2 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) hpos (dvd_trans (by norm_num) dh)
    have c1 := pow2_class 32 5 k 65537 15 38912 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) hpos (dvd_trans (by norm_num) dh)
    norm_num at c0 c1
    omega
  · clear plus
    have c0 := pow2_class 32 43 k 17 2 5 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) hpos (dvd_trans (by norm_num) dh)
    have c1 := pow2_class 32 43 k 65537 15 2048 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) hpos (dvd_trans (by norm_num) dh)
    norm_num at c0 c1
    omega
  · clear plus
    have c0 := pow2_class 32 2591 k 17 3 14 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) hpos (dvd_trans (by norm_num) dh)
    have c1 := pow2_class 32 2591 k 65537 13 4608 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) hpos (dvd_trans (by norm_num) dh)
    norm_num at c0 c1
    omega

set_option maxRecDepth 100000 in
lemma t32_leaf_6 (p k : ℕ) (hp : p.Prime) (two : p ≠ 2) (hpos : 0 < 32 * p ^ k)
    (dh : 1 * (1 * (17 * (257 * 1))) ∣ 32 * p ^ k - 1) (plus : p ∣ 1 * (1 * (17 * (257 * 1))) + 1) :
    (p = 3 ∧ (k % 4 = 1 ∨ k % 16 = 10 ∨ k % 256 = 16 ∨ k % 65536 = 51200)) ∨ (p = 11 ∧ k % 65536 = 14336) ∨ (p = 43 ∧ (k % 8 = 5 ∨ k % 256 = 240)) ∨ (p = 331 ∧ k % 65536 = 14336) ∨ (p = 643 ∧ k % 16 = 5) ∨ (p = 715827883 ∧ k % 32 = 5) := by
  have := prime_mem_of_dvd hp [2, 5, 19, 23] (by norm_num) (by simpa using plus)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at this
  rcases this with rfl | rfl | rfl | rfl
  · exact (two rfl).elim
  · clear plus
    have c0 := pow2_class 32 5 k 17 3 2 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) hpos (dvd_trans (by norm_num) dh)
    have c1 := pow2_class 32 5 k 257 7 112 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) hpos (dvd_trans (by norm_num) dh)
    norm_num at c0 c1
    omega
  · clear plus
    have c0 := pow2_class 32 19 k 17 2 3 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) hpos (dvd_trans (by norm_num) dh)
    have c1 := pow2_class 32 19 k 257 7 80 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) hpos (dvd_trans (by norm_num) dh)
    norm_num at c0 c1
    omega
  · clear plus
    have c0 := pow2_class 32 23 k 17 3 6 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) hpos (dvd_trans (by norm_num) dh)
    have c1 := pow2_class 32 23 k 257 5 28 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) hpos (dvd_trans (by norm_num) dh)
    norm_num at c0 c1
    omega

set_option maxRecDepth 100000 in
lemma t32_leaf_7 (p k : ℕ) (hp : p.Prime) (two : p ≠ 2) (hpos : 0 < 32 * p ^ k)
    (dh : 1 * (1 * (17 * (257 * 65537))) ∣ 32 * p ^ k - 1) (plus : p ∣ 1 * (1 * (17 * (257 * 65537))) + 1) :
    (p = 3 ∧ (k % 4 = 1 ∨ k % 16 = 10 ∨ k % 256 = 16 ∨ k % 65536 = 51200)) ∨ (p = 11 ∧ k % 65536 = 14336) ∨ (p = 43 ∧ (k % 8 = 5 ∨ k % 256 = 240)) ∨ (p = 331 ∧ k % 65536 = 14336) ∨ (p = 643 ∧ k % 16 = 5) ∨ (p = 715827883 ∧ k % 32 = 5) := by
  have := prime_mem_of_dvd hp [2, 3, 131, 364289] (by norm_num) (by simpa using plus)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at this
  rcases this with rfl | rfl | rfl | rfl
  · exact (two rfl).elim
  · clear plus
    have c0 := pow2_class 32 3 k 257 7 16 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) hpos (dvd_trans (by norm_num) dh)
    have c1 := pow2_class 32 3 k 65537 15 51200 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) hpos (dvd_trans (by norm_num) dh)
    norm_num at c0 c1
    omega
  · clear plus
    have c0 := pow2_class 32 131 k 257 7 112 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) hpos (dvd_trans (by norm_num) dh)
    have c1 := pow2_class 32 131 k 65537 15 18432 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) hpos (dvd_trans (by norm_num) dh)
    norm_num at c0 c1
    omega
  · exact (pow_no_class 32 364289 k 17 4 (by decide +kernel) (by decide +kernel) hpos
      (dvd_trans (by norm_num) dh)).elim

set_option maxRecDepth 100000 in
lemma t32_leaf_8 (p k : ℕ) (hp : p.Prime) (two : p ≠ 2) (hpos : 0 < 32 * p ^ k)
    (dh : 1 * (5 * (1 * (1 * 1))) ∣ 32 * p ^ k - 1) (plus : p ∣ 1 * (5 * (1 * (1 * 1))) + 1) :
    (p = 3 ∧ (k % 4 = 1 ∨ k % 16 = 10 ∨ k % 256 = 16 ∨ k % 65536 = 51200)) ∨ (p = 11 ∧ k % 65536 = 14336) ∨ (p = 43 ∧ (k % 8 = 5 ∨ k % 256 = 240)) ∨ (p = 331 ∧ k % 65536 = 14336) ∨ (p = 643 ∧ k % 16 = 5) ∨ (p = 715827883 ∧ k % 32 = 5) := by
  have := prime_mem_of_dvd hp [2, 3] (by norm_num) (by simpa using plus)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at this
  rcases this with rfl | rfl
  · exact (two rfl).elim
  · clear plus
    have c0 := pow2_class 32 3 k 5 1 1 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) hpos (dvd_trans (by norm_num) dh)
    norm_num at c0
    omega

set_option maxRecDepth 100000 in
lemma t32_leaf_9 (p k : ℕ) (hp : p.Prime) (two : p ≠ 2) (hpos : 0 < 32 * p ^ k)
    (dh : 1 * (5 * (1 * (1 * 65537))) ∣ 32 * p ^ k - 1) (plus : p ∣ 1 * (5 * (1 * (1 * 65537))) + 1) :
    (p = 3 ∧ (k % 4 = 1 ∨ k % 16 = 10 ∨ k % 256 = 16 ∨ k % 65536 = 51200)) ∨ (p = 11 ∧ k % 65536 = 14336) ∨ (p = 43 ∧ (k % 8 = 5 ∨ k % 256 = 240)) ∨ (p = 331 ∧ k % 65536 = 14336) ∨ (p = 643 ∧ k % 16 = 5) ∨ (p = 715827883 ∧ k % 32 = 5) := by
  have := prime_mem_of_dvd hp [2, 59, 2777] (by norm_num) (by simpa using plus)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at this
  rcases this with rfl | rfl | rfl
  · exact (two rfl).elim
  · exact (pow_no_class 32 59 k 5 2 (by decide +kernel) (by decide +kernel) hpos
      (dvd_trans (by norm_num) dh)).elim
  · clear plus
    have c0 := pow2_class 32 2777 k 5 1 3 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) hpos (dvd_trans (by norm_num) dh)
    have c1 := pow2_class 32 2777 k 65537 15 14336 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) hpos (dvd_trans (by norm_num) dh)
    norm_num at c0 c1
    omega

set_option maxRecDepth 100000 in
lemma t32_leaf_10 (p k : ℕ) (hp : p.Prime) (two : p ≠ 2) (hpos : 0 < 32 * p ^ k)
    (dh : 1 * (5 * (1 * (257 * 1))) ∣ 32 * p ^ k - 1) (plus : p ∣ 1 * (5 * (1 * (257 * 1))) + 1) :
    (p = 3 ∧ (k % 4 = 1 ∨ k % 16 = 10 ∨ k % 256 = 16 ∨ k % 65536 = 51200)) ∨ (p = 11 ∧ k % 65536 = 14336) ∨ (p = 43 ∧ (k % 8 = 5 ∨ k % 256 = 240)) ∨ (p = 331 ∧ k % 65536 = 14336) ∨ (p = 643 ∧ k % 16 = 5) ∨ (p = 715827883 ∧ k % 32 = 5) := by
  have := prime_mem_of_dvd hp [2, 643] (by norm_num) (by simpa using plus)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at this
  rcases this with rfl | rfl
  · exact (two rfl).elim
  · clear plus
    have c0 := pow2_class 32 643 k 257 3 5 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) hpos (dvd_trans (by norm_num) dh)
    norm_num at c0
    omega

set_option maxRecDepth 100000 in
lemma t32_leaf_11 (p k : ℕ) (hp : p.Prime) (two : p ≠ 2) (hpos : 0 < 32 * p ^ k)
    (dh : 1 * (5 * (1 * (257 * 65537))) ∣ 32 * p ^ k - 1) (plus : p ∣ 1 * (5 * (1 * (257 * 65537))) + 1) :
    (p = 3 ∧ (k % 4 = 1 ∨ k % 16 = 10 ∨ k % 256 = 16 ∨ k % 65536 = 51200)) ∨ (p = 11 ∧ k % 65536 = 14336) ∨ (p = 43 ∧ (k % 8 = 5 ∨ k % 256 = 240)) ∨ (p = 331 ∧ k % 65536 = 14336) ∨ (p = 643 ∧ k % 16 = 5) ∨ (p = 715827883 ∧ k % 32 = 5) := by
  have := prime_mem_of_dvd hp [2, 3, 457, 30713] (by norm_num) (by simpa using plus)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at this
  rcases this with rfl | rfl | rfl | rfl
  · exact (two rfl).elim
  · clear plus
    have c0 := pow2_class 32 3 k 257 7 16 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) hpos (dvd_trans (by norm_num) dh)
    have c1 := pow2_class 32 3 k 65537 15 51200 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) hpos (dvd_trans (by norm_num) dh)
    norm_num at c0 c1
    omega
  · clear plus
    have c0 := pow2_class 32 457 k 257 6 120 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) hpos (dvd_trans (by norm_num) dh)
    have c1 := pow2_class 32 457 k 65537 15 10240 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) hpos (dvd_trans (by norm_num) dh)
    norm_num at c0 c1
    omega
  · clear plus
    have c0 := pow2_class 32 30713 k 257 7 16 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) hpos (dvd_trans (by norm_num) dh)
    have c1 := pow2_class 32 30713 k 65537 14 29696 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) hpos (dvd_trans (by norm_num) dh)
    norm_num at c0 c1
    omega

set_option maxRecDepth 100000 in
lemma t32_leaf_12 (p k : ℕ) (hp : p.Prime) (two : p ≠ 2) (hpos : 0 < 32 * p ^ k)
    (dh : 1 * (5 * (17 * (1 * 1))) ∣ 32 * p ^ k - 1) (plus : p ∣ 1 * (5 * (17 * (1 * 1))) + 1) :
    (p = 3 ∧ (k % 4 = 1 ∨ k % 16 = 10 ∨ k % 256 = 16 ∨ k % 65536 = 51200)) ∨ (p = 11 ∧ k % 65536 = 14336) ∨ (p = 43 ∧ (k % 8 = 5 ∨ k % 256 = 240)) ∨ (p = 331 ∧ k % 65536 = 14336) ∨ (p = 643 ∧ k % 16 = 5) ∨ (p = 715827883 ∧ k % 32 = 5) := by
  have := prime_mem_of_dvd hp [2, 43] (by norm_num) (by simpa using plus)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at this
  rcases this with rfl | rfl
  · exact (two rfl).elim
  · clear plus
    have c0 := pow2_class 32 43 k 17 2 5 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) hpos (dvd_trans (by norm_num) dh)
    norm_num at c0
    omega

set_option maxRecDepth 100000 in
lemma t32_leaf_13 (p k : ℕ) (hp : p.Prime) (two : p ≠ 2) (hpos : 0 < 32 * p ^ k)
    (dh : 1 * (5 * (17 * (1 * 65537))) ∣ 32 * p ^ k - 1) (plus : p ∣ 1 * (5 * (17 * (1 * 65537))) + 1) :
    (p = 3 ∧ (k % 4 = 1 ∨ k % 16 = 10 ∨ k % 256 = 16 ∨ k % 65536 = 51200)) ∨ (p = 11 ∧ k % 65536 = 14336) ∨ (p = 43 ∧ (k % 8 = 5 ∨ k % 256 = 240)) ∨ (p = 331 ∧ k % 65536 = 14336) ∨ (p = 643 ∧ k % 16 = 5) ∨ (p = 715827883 ∧ k % 32 = 5) := by
  have := prime_mem_of_dvd hp [2, 3, 23, 37, 1091] (by norm_num) (by simpa using plus)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at this
  rcases this with rfl | rfl | rfl | rfl | rfl
  · exact (two rfl).elim
  · clear plus
    have c0 := pow2_class 32 3 k 17 3 10 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) hpos (dvd_trans (by norm_num) dh)
    have c1 := pow2_class 32 3 k 65537 15 51200 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) hpos (dvd_trans (by norm_num) dh)
    norm_num at c0 c1
    omega
  · clear plus
    have c0 := pow2_class 32 23 k 17 3 6 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) hpos (dvd_trans (by norm_num) dh)
    have c1 := pow2_class 32 23 k 65537 15 55296 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) hpos (dvd_trans (by norm_num) dh)
    norm_num at c0 c1
    omega
  · clear plus
    have c0 := pow2_class 32 37 k 17 3 10 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) hpos (dvd_trans (by norm_num) dh)
    have c1 := pow2_class 32 37 k 65537 14 29696 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) hpos (dvd_trans (by norm_num) dh)
    norm_num at c0 c1
    omega
  · exact (pow_no_class 32 1091 k 5 1 (by decide +kernel) (by decide +kernel) hpos
      (dvd_trans (by norm_num) dh)).elim

set_option maxRecDepth 100000 in
lemma t32_leaf_14 (p k : ℕ) (hp : p.Prime) (two : p ≠ 2) (hpos : 0 < 32 * p ^ k)
    (dh : 1 * (5 * (17 * (257 * 1))) ∣ 32 * p ^ k - 1) (plus : p ∣ 1 * (5 * (17 * (257 * 1))) + 1) :
    (p = 3 ∧ (k % 4 = 1 ∨ k % 16 = 10 ∨ k % 256 = 16 ∨ k % 65536 = 51200)) ∨ (p = 11 ∧ k % 65536 = 14336) ∨ (p = 43 ∧ (k % 8 = 5 ∨ k % 256 = 240)) ∨ (p = 331 ∧ k % 65536 = 14336) ∨ (p = 643 ∧ k % 16 = 5) ∨ (p = 715827883 ∧ k % 32 = 5) := by
  have := prime_mem_of_dvd hp [2, 3, 11, 331] (by norm_num) (by simpa using plus)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at this
  rcases this with rfl | rfl | rfl | rfl
  · exact (two rfl).elim
  · clear plus
    have c0 := pow2_class 32 3 k 17 3 10 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) hpos (dvd_trans (by norm_num) dh)
    have c1 := pow2_class 32 3 k 257 7 16 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) hpos (dvd_trans (by norm_num) dh)
    norm_num at c0 c1
    omega
  · exact (pow_no_class 32 11 k 5 1 (by decide +kernel) (by decide +kernel) hpos
      (dvd_trans (by norm_num) dh)).elim
  · exact (pow_no_class 32 331 k 5 1 (by decide +kernel) (by decide +kernel) hpos
      (dvd_trans (by norm_num) dh)).elim

set_option maxRecDepth 100000 in
lemma t32_leaf_15 (p k : ℕ) (hp : p.Prime) (two : p ≠ 2) (hpos : 0 < 32 * p ^ k)
    (dh : 1 * (5 * (17 * (257 * 65537))) ∣ 32 * p ^ k - 1) (plus : p ∣ 1 * (5 * (17 * (257 * 65537))) + 1) :
    (p = 3 ∧ (k % 4 = 1 ∨ k % 16 = 10 ∨ k % 256 = 16 ∨ k % 65536 = 51200)) ∨ (p = 11 ∧ k % 65536 = 14336) ∨ (p = 43 ∧ (k % 8 = 5 ∨ k % 256 = 240)) ∨ (p = 331 ∧ k % 65536 = 14336) ∨ (p = 643 ∧ k % 16 = 5) ∨ (p = 715827883 ∧ k % 32 = 5) := by
  have := prime_mem_of_dvd hp [2, 715827883] (by norm_num) (by simpa using plus)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at this
  rcases this with rfl | rfl
  · exact (two rfl).elim
  · clear plus
    have c0 := pow2_class 32 715827883 k 65537 4 5 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) hpos (dvd_trans (by norm_num) dh)
    norm_num at c0
    omega

set_option maxRecDepth 100000 in
lemma t32_leaf_16 (p k : ℕ) (hp : p.Prime) (two : p ≠ 2) (hpos : 0 < 32 * p ^ k)
    (dh : 3 * (1 * (1 * (1 * 1))) ∣ 32 * p ^ k - 1) (plus : p ∣ 3 * (1 * (1 * (1 * 1))) + 1) :
    (p = 3 ∧ (k % 4 = 1 ∨ k % 16 = 10 ∨ k % 256 = 16 ∨ k % 65536 = 51200)) ∨ (p = 11 ∧ k % 65536 = 14336) ∨ (p = 43 ∧ (k % 8 = 5 ∨ k % 256 = 240)) ∨ (p = 331 ∧ k % 65536 = 14336) ∨ (p = 643 ∧ k % 16 = 5) ∨ (p = 715827883 ∧ k % 32 = 5) := by
  have := prime_mem_of_dvd hp (List.replicate 2 2)
    (fun q hq => by rw [List.eq_of_mem_replicate hq]; exact Nat.prime_two) (by simpa using plus)
  exact (two (List.eq_of_mem_replicate this)).elim

set_option maxRecDepth 100000 in
lemma t32_leaf_17 (p k : ℕ) (hp : p.Prime) (two : p ≠ 2) (hpos : 0 < 32 * p ^ k)
    (dh : 3 * (1 * (1 * (1 * 65537))) ∣ 32 * p ^ k - 1) (plus : p ∣ 3 * (1 * (1 * (1 * 65537))) + 1) :
    (p = 3 ∧ (k % 4 = 1 ∨ k % 16 = 10 ∨ k % 256 = 16 ∨ k % 65536 = 51200)) ∨ (p = 11 ∧ k % 65536 = 14336) ∨ (p = 43 ∧ (k % 8 = 5 ∨ k % 256 = 240)) ∨ (p = 331 ∧ k % 65536 = 14336) ∨ (p = 643 ∧ k % 16 = 5) ∨ (p = 715827883 ∧ k % 32 = 5) := by
  have := prime_mem_of_dvd hp [2, 2, 13, 19, 199] (by norm_num) (by simpa using plus)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at this
  rcases this with rfl | rfl | rfl | rfl | rfl
  · exact (two rfl).elim
  · exact (two rfl).elim
  · exact (pow_no_class 32 13 k 3 1 (by decide +kernel) (by decide +kernel) hpos
      (dvd_trans (by norm_num) dh)).elim
  · exact (pow_no_class 32 19 k 3 1 (by decide +kernel) (by decide +kernel) hpos
      (dvd_trans (by norm_num) dh)).elim
  · exact (pow_no_class 32 199 k 3 1 (by decide +kernel) (by decide +kernel) hpos
      (dvd_trans (by norm_num) dh)).elim

set_option maxRecDepth 100000 in
lemma t32_leaf_18 (p k : ℕ) (hp : p.Prime) (two : p ≠ 2) (hpos : 0 < 32 * p ^ k)
    (dh : 3 * (1 * (1 * (257 * 1))) ∣ 32 * p ^ k - 1) (plus : p ∣ 3 * (1 * (1 * (257 * 1))) + 1) :
    (p = 3 ∧ (k % 4 = 1 ∨ k % 16 = 10 ∨ k % 256 = 16 ∨ k % 65536 = 51200)) ∨ (p = 11 ∧ k % 65536 = 14336) ∨ (p = 43 ∧ (k % 8 = 5 ∨ k % 256 = 240)) ∨ (p = 331 ∧ k % 65536 = 14336) ∨ (p = 643 ∧ k % 16 = 5) ∨ (p = 715827883 ∧ k % 32 = 5) := by
  have := prime_mem_of_dvd hp [2, 2, 193] (by norm_num) (by simpa using plus)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at this
  rcases this with rfl | rfl | rfl
  · exact (two rfl).elim
  · exact (two rfl).elim
  · exact (pow_no_class 32 193 k 3 1 (by decide +kernel) (by decide +kernel) hpos
      (dvd_trans (by norm_num) dh)).elim

set_option maxRecDepth 100000 in
lemma t32_leaf_19 (p k : ℕ) (hp : p.Prime) (two : p ≠ 2) (hpos : 0 < 32 * p ^ k)
    (dh : 3 * (1 * (1 * (257 * 65537))) ∣ 32 * p ^ k - 1) (plus : p ∣ 3 * (1 * (1 * (257 * 65537))) + 1) :
    (p = 3 ∧ (k % 4 = 1 ∨ k % 16 = 10 ∨ k % 256 = 16 ∨ k % 65536 = 51200)) ∨ (p = 11 ∧ k % 65536 = 14336) ∨ (p = 43 ∧ (k % 8 = 5 ∨ k % 256 = 240)) ∨ (p = 331 ∧ k % 65536 = 14336) ∨ (p = 643 ∧ k % 16 = 5) ∨ (p = 715827883 ∧ k % 32 = 5) := by
  have := prime_mem_of_dvd hp [2, 2, 11, 1148387] (by norm_num) (by simpa using plus)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at this
  rcases this with rfl | rfl | rfl | rfl
  · exact (two rfl).elim
  · exact (two rfl).elim
  · clear plus
    have c0 := pow2_class 32 11 k 257 5 4 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) hpos (dvd_trans (by norm_num) dh)
    have c1 := pow2_class 32 11 k 65537 15 14336 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) hpos (dvd_trans (by norm_num) dh)
    norm_num at c0 c1
    omega
  · clear plus
    have c0 := pow2_class 32 1148387 k 257 5 28 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) hpos (dvd_trans (by norm_num) dh)
    have c1 := pow2_class 32 1148387 k 65537 15 51200 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) hpos (dvd_trans (by norm_num) dh)
    norm_num at c0 c1
    omega

set_option maxRecDepth 100000 in
lemma t32_leaf_20 (p k : ℕ) (hp : p.Prime) (two : p ≠ 2) (hpos : 0 < 32 * p ^ k)
    (dh : 3 * (1 * (17 * (1 * 1))) ∣ 32 * p ^ k - 1) (plus : p ∣ 3 * (1 * (17 * (1 * 1))) + 1) :
    (p = 3 ∧ (k % 4 = 1 ∨ k % 16 = 10 ∨ k % 256 = 16 ∨ k % 65536 = 51200)) ∨ (p = 11 ∧ k % 65536 = 14336) ∨ (p = 43 ∧ (k % 8 = 5 ∨ k % 256 = 240)) ∨ (p = 331 ∧ k % 65536 = 14336) ∨ (p = 643 ∧ k % 16 = 5) ∨ (p = 715827883 ∧ k % 32 = 5) := by
  have := prime_mem_of_dvd hp [2, 2, 13] (by norm_num) (by simpa using plus)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at this
  rcases this with rfl | rfl | rfl
  · exact (two rfl).elim
  · exact (two rfl).elim
  · exact (pow_no_class 32 13 k 3 1 (by decide +kernel) (by decide +kernel) hpos
      (dvd_trans (by norm_num) dh)).elim

set_option maxRecDepth 100000 in
lemma t32_leaf_21 (p k : ℕ) (hp : p.Prime) (two : p ≠ 2) (hpos : 0 < 32 * p ^ k)
    (dh : 3 * (1 * (17 * (1 * 65537))) ∣ 32 * p ^ k - 1) (plus : p ∣ 3 * (1 * (17 * (1 * 65537))) + 1) :
    (p = 3 ∧ (k % 4 = 1 ∨ k % 16 = 10 ∨ k % 256 = 16 ∨ k % 65536 = 51200)) ∨ (p = 11 ∧ k % 65536 = 14336) ∨ (p = 43 ∧ (k % 8 = 5 ∨ k % 256 = 240)) ∨ (p = 331 ∧ k % 65536 = 14336) ∨ (p = 643 ∧ k % 16 = 5) ∨ (p = 715827883 ∧ k % 32 = 5) := by
  have := prime_mem_of_dvd hp [2, 2, 7, 7, 17053] (by norm_num) (by simpa using plus)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at this
  rcases this with rfl | rfl | rfl | rfl | rfl
  · exact (two rfl).elim
  · exact (two rfl).elim
  · exact (pow_no_class 32 7 k 3 1 (by decide +kernel) (by decide +kernel) hpos
      (dvd_trans (by norm_num) dh)).elim
  · exact (pow_no_class 32 7 k 3 1 (by decide +kernel) (by decide +kernel) hpos
      (dvd_trans (by norm_num) dh)).elim
  · exact (pow_no_class 32 17053 k 3 1 (by decide +kernel) (by decide +kernel) hpos
      (dvd_trans (by norm_num) dh)).elim

set_option maxRecDepth 100000 in
lemma t32_leaf_22 (p k : ℕ) (hp : p.Prime) (two : p ≠ 2) (hpos : 0 < 32 * p ^ k)
    (dh : 3 * (1 * (17 * (257 * 1))) ∣ 32 * p ^ k - 1) (plus : p ∣ 3 * (1 * (17 * (257 * 1))) + 1) :
    (p = 3 ∧ (k % 4 = 1 ∨ k % 16 = 10 ∨ k % 256 = 16 ∨ k % 65536 = 51200)) ∨ (p = 11 ∧ k % 65536 = 14336) ∨ (p = 43 ∧ (k % 8 = 5 ∨ k % 256 = 240)) ∨ (p = 331 ∧ k % 65536 = 14336) ∨ (p = 643 ∧ k % 16 = 5) ∨ (p = 715827883 ∧ k % 32 = 5) := by
  have := prime_mem_of_dvd hp [2, 2, 29, 113] (by norm_num) (by simpa using plus)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at this
  rcases this with rfl | rfl | rfl | rfl
  · exact (two rfl).elim
  · exact (two rfl).elim
  · clear plus
    have c0 := pow2_class 32 29 k 17 3 2 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) hpos (dvd_trans (by norm_num) dh)
    have c1 := pow2_class 32 29 k 257 6 120 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) hpos (dvd_trans (by norm_num) dh)
    norm_num at c0 c1
    omega
  · clear plus
    have c0 := pow2_class 32 113 k 17 3 6 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) hpos (dvd_trans (by norm_num) dh)
    have c1 := pow2_class 32 113 k 257 6 8 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) hpos (dvd_trans (by norm_num) dh)
    norm_num at c0 c1
    omega

set_option maxRecDepth 100000 in
lemma t32_leaf_23 (p k : ℕ) (hp : p.Prime) (two : p ≠ 2) (hpos : 0 < 32 * p ^ k)
    (dh : 3 * (1 * (17 * (257 * 65537))) ∣ 32 * p ^ k - 1) (plus : p ∣ 3 * (1 * (17 * (257 * 65537))) + 1) :
    (p = 3 ∧ (k % 4 = 1 ∨ k % 16 = 10 ∨ k % 256 = 16 ∨ k % 65536 = 51200)) ∨ (p = 11 ∧ k % 65536 = 14336) ∨ (p = 43 ∧ (k % 8 = 5 ∨ k % 256 = 240)) ∨ (p = 331 ∧ k % 65536 = 14336) ∨ (p = 643 ∧ k % 16 = 5) ∨ (p = 715827883 ∧ k % 32 = 5) := by
  have := prime_mem_of_dvd hp [2, 2, 5, 13, 41, 61, 1321] (by norm_num) (by simpa using plus)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at this
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (two rfl).elim
  · exact (two rfl).elim
  · clear plus
    have c0 := pow2_class 32 5 k 257 7 112 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) hpos (dvd_trans (by norm_num) dh)
    have c1 := pow2_class 32 5 k 65537 15 38912 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) hpos (dvd_trans (by norm_num) dh)
    norm_num at c0 c1
    omega
  · exact (pow_no_class 32 13 k 3 1 (by decide +kernel) (by decide +kernel) hpos
      (dvd_trans (by norm_num) dh)).elim
  · clear plus
    have c0 := pow2_class 32 41 k 257 7 176 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) hpos (dvd_trans (by norm_num) dh)
    have c1 := pow2_class 32 41 k 65537 15 22528 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) hpos (dvd_trans (by norm_num) dh)
    norm_num at c0 c1
    omega
  · exact (pow_no_class 32 61 k 3 1 (by decide +kernel) (by decide +kernel) hpos
      (dvd_trans (by norm_num) dh)).elim
  · exact (pow_no_class 32 1321 k 3 1 (by decide +kernel) (by decide +kernel) hpos
      (dvd_trans (by norm_num) dh)).elim

set_option maxRecDepth 100000 in
lemma t32_leaf_24 (p k : ℕ) (hp : p.Prime) (two : p ≠ 2) (hpos : 0 < 32 * p ^ k)
    (dh : 3 * (5 * (1 * (1 * 1))) ∣ 32 * p ^ k - 1) (plus : p ∣ 3 * (5 * (1 * (1 * 1))) + 1) :
    (p = 3 ∧ (k % 4 = 1 ∨ k % 16 = 10 ∨ k % 256 = 16 ∨ k % 65536 = 51200)) ∨ (p = 11 ∧ k % 65536 = 14336) ∨ (p = 43 ∧ (k % 8 = 5 ∨ k % 256 = 240)) ∨ (p = 331 ∧ k % 65536 = 14336) ∨ (p = 643 ∧ k % 16 = 5) ∨ (p = 715827883 ∧ k % 32 = 5) := by
  have := prime_mem_of_dvd hp (List.replicate 4 2)
    (fun q hq => by rw [List.eq_of_mem_replicate hq]; exact Nat.prime_two) (by simpa using plus)
  exact (two (List.eq_of_mem_replicate this)).elim

set_option maxRecDepth 100000 in
lemma t32_leaf_25 (p k : ℕ) (hp : p.Prime) (two : p ≠ 2) (hpos : 0 < 32 * p ^ k)
    (dh : 3 * (5 * (1 * (1 * 65537))) ∣ 32 * p ^ k - 1) (plus : p ∣ 3 * (5 * (1 * (1 * 65537))) + 1) :
    (p = 3 ∧ (k % 4 = 1 ∨ k % 16 = 10 ∨ k % 256 = 16 ∨ k % 65536 = 51200)) ∨ (p = 11 ∧ k % 65536 = 14336) ∨ (p = 43 ∧ (k % 8 = 5 ∨ k % 256 = 240)) ∨ (p = 331 ∧ k % 65536 = 14336) ∨ (p = 643 ∧ k % 16 = 5) ∨ (p = 715827883 ∧ k % 32 = 5) := by
  have := prime_mem_of_dvd hp [2, 2, 2, 2, 61441] (by norm_num) (by simpa using plus)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at this
  rcases this with rfl | rfl | rfl | rfl | rfl
  · exact (two rfl).elim
  · exact (two rfl).elim
  · exact (two rfl).elim
  · exact (two rfl).elim
  · exact (pow_no_class 32 61441 k 3 1 (by decide +kernel) (by decide +kernel) hpos
      (dvd_trans (by norm_num) dh)).elim

set_option maxRecDepth 100000 in
lemma t32_leaf_26 (p k : ℕ) (hp : p.Prime) (two : p ≠ 2) (hpos : 0 < 32 * p ^ k)
    (dh : 3 * (5 * (1 * (257 * 1))) ∣ 32 * p ^ k - 1) (plus : p ∣ 3 * (5 * (1 * (257 * 1))) + 1) :
    (p = 3 ∧ (k % 4 = 1 ∨ k % 16 = 10 ∨ k % 256 = 16 ∨ k % 65536 = 51200)) ∨ (p = 11 ∧ k % 65536 = 14336) ∨ (p = 43 ∧ (k % 8 = 5 ∨ k % 256 = 240)) ∨ (p = 331 ∧ k % 65536 = 14336) ∨ (p = 643 ∧ k % 16 = 5) ∨ (p = 715827883 ∧ k % 32 = 5) := by
  have := prime_mem_of_dvd hp [2, 2, 2, 2, 241] (by norm_num) (by simpa using plus)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at this
  rcases this with rfl | rfl | rfl | rfl | rfl
  · exact (two rfl).elim
  · exact (two rfl).elim
  · exact (two rfl).elim
  · exact (two rfl).elim
  · exact (pow_no_class 32 241 k 3 1 (by decide +kernel) (by decide +kernel) hpos
      (dvd_trans (by norm_num) dh)).elim

set_option maxRecDepth 100000 in
lemma t32_leaf_27 (p k : ℕ) (hp : p.Prime) (two : p ≠ 2) (hpos : 0 < 32 * p ^ k)
    (dh : 3 * (5 * (1 * (257 * 65537))) ∣ 32 * p ^ k - 1) (plus : p ∣ 3 * (5 * (1 * (257 * 65537))) + 1) :
    (p = 3 ∧ (k % 4 = 1 ∨ k % 16 = 10 ∨ k % 256 = 16 ∨ k % 65536 = 51200)) ∨ (p = 11 ∧ k % 65536 = 14336) ∨ (p = 43 ∧ (k % 8 = 5 ∨ k % 256 = 240)) ∨ (p = 331 ∧ k % 65536 = 14336) ∨ (p = 643 ∧ k % 16 = 5) ∨ (p = 715827883 ∧ k % 32 = 5) := by
  have := prime_mem_of_dvd hp [2, 2, 2, 2, 15790321] (by norm_num) (by simpa using plus)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at this
  rcases this with rfl | rfl | rfl | rfl | rfl
  · exact (two rfl).elim
  · exact (two rfl).elim
  · exact (two rfl).elim
  · exact (two rfl).elim
  · exact (pow_no_class 32 15790321 k 3 1 (by decide +kernel) (by decide +kernel) hpos
      (dvd_trans (by norm_num) dh)).elim

set_option maxRecDepth 100000 in
lemma t32_leaf_28 (p k : ℕ) (hp : p.Prime) (two : p ≠ 2) (hpos : 0 < 32 * p ^ k)
    (dh : 3 * (5 * (17 * (1 * 1))) ∣ 32 * p ^ k - 1) (plus : p ∣ 3 * (5 * (17 * (1 * 1))) + 1) :
    (p = 3 ∧ (k % 4 = 1 ∨ k % 16 = 10 ∨ k % 256 = 16 ∨ k % 65536 = 51200)) ∨ (p = 11 ∧ k % 65536 = 14336) ∨ (p = 43 ∧ (k % 8 = 5 ∨ k % 256 = 240)) ∨ (p = 331 ∧ k % 65536 = 14336) ∨ (p = 643 ∧ k % 16 = 5) ∨ (p = 715827883 ∧ k % 32 = 5) := by
  have := prime_mem_of_dvd hp (List.replicate 8 2)
    (fun q hq => by rw [List.eq_of_mem_replicate hq]; exact Nat.prime_two) (by simpa using plus)
  exact (two (List.eq_of_mem_replicate this)).elim

set_option maxRecDepth 100000 in
lemma t32_leaf_29 (p k : ℕ) (hp : p.Prime) (two : p ≠ 2) (hpos : 0 < 32 * p ^ k)
    (dh : 3 * (5 * (17 * (1 * 65537))) ∣ 32 * p ^ k - 1) (plus : p ∣ 3 * (5 * (17 * (1 * 65537))) + 1) :
    (p = 3 ∧ (k % 4 = 1 ∨ k % 16 = 10 ∨ k % 256 = 16 ∨ k % 65536 = 51200)) ∨ (p = 11 ∧ k % 65536 = 14336) ∨ (p = 43 ∧ (k % 8 = 5 ∨ k % 256 = 240)) ∨ (p = 331 ∧ k % 65536 = 14336) ∨ (p = 643 ∧ k % 16 = 5) ∨ (p = 715827883 ∧ k % 32 = 5) := by
  have := prime_mem_of_dvd hp [2, 2, 2, 2, 2, 2, 2, 2, 97, 673] (by norm_num) (by simpa using plus)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at this
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (two rfl).elim
  · exact (two rfl).elim
  · exact (two rfl).elim
  · exact (two rfl).elim
  · exact (two rfl).elim
  · exact (two rfl).elim
  · exact (two rfl).elim
  · exact (two rfl).elim
  · exact (pow_no_class 32 97 k 3 1 (by decide +kernel) (by decide +kernel) hpos
      (dvd_trans (by norm_num) dh)).elim
  · exact (pow_no_class 32 673 k 3 1 (by decide +kernel) (by decide +kernel) hpos
      (dvd_trans (by norm_num) dh)).elim

set_option maxRecDepth 100000 in
lemma t32_leaf_30 (p k : ℕ) (hp : p.Prime) (two : p ≠ 2) (hpos : 0 < 32 * p ^ k)
    (dh : 3 * (5 * (17 * (257 * 1))) ∣ 32 * p ^ k - 1) (plus : p ∣ 3 * (5 * (17 * (257 * 1))) + 1) :
    (p = 3 ∧ (k % 4 = 1 ∨ k % 16 = 10 ∨ k % 256 = 16 ∨ k % 65536 = 51200)) ∨ (p = 11 ∧ k % 65536 = 14336) ∨ (p = 43 ∧ (k % 8 = 5 ∨ k % 256 = 240)) ∨ (p = 331 ∧ k % 65536 = 14336) ∨ (p = 643 ∧ k % 16 = 5) ∨ (p = 715827883 ∧ k % 32 = 5) := by
  have := prime_mem_of_dvd hp (List.replicate 16 2)
    (fun q hq => by rw [List.eq_of_mem_replicate hq]; exact Nat.prime_two) (by simpa using plus)
  exact (two (List.eq_of_mem_replicate this)).elim

set_option maxRecDepth 100000 in
lemma t32_leaf_31 (p k : ℕ) (hp : p.Prime) (two : p ≠ 2) (hpos : 0 < 32 * p ^ k)
    (dh : 3 * (5 * (17 * (257 * 65537))) ∣ 32 * p ^ k - 1) (plus : p ∣ 3 * (5 * (17 * (257 * 65537))) + 1) :
    (p = 3 ∧ (k % 4 = 1 ∨ k % 16 = 10 ∨ k % 256 = 16 ∨ k % 65536 = 51200)) ∨ (p = 11 ∧ k % 65536 = 14336) ∨ (p = 43 ∧ (k % 8 = 5 ∨ k % 256 = 240)) ∨ (p = 331 ∧ k % 65536 = 14336) ∨ (p = 643 ∧ k % 16 = 5) ∨ (p = 715827883 ∧ k % 32 = 5) := by
  have := prime_mem_of_dvd hp (List.replicate 32 2)
    (fun q hq => by rw [List.eq_of_mem_replicate hq]; exact Nat.prime_two) (by simpa using plus)
  exact (two (List.eq_of_mem_replicate this)).elim

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- In the family x = 32 p^k only six odd primes survive the predecessor test, each in at most
    four classes of k. Modulo each prime r ∣ 2^32 - 1 the order of p is a power of 2, so
    `pow_no_class` or `pow2_class` applies, and two incompatible classes give a contradiction. -/
theorem thirtytwo_prime_power (p k : ℕ) (hp : p.Prime) (odd : p ≠ 2) (hk : k ≠ 0)
    (test : (32 * p ^ k) ^ 4 - 1 ∣ 2 ^ (32 * p ^ k) - 1) :
    (p = 3 ∧ (k % 4 = 1 ∨ k % 16 = 10 ∨ k % 256 = 16 ∨ k % 65536 = 51200)) ∨ (p = 11 ∧ k % 65536 = 14336) ∨ (p = 43 ∧ (k % 8 = 5 ∨ k % 256 = 240)) ∨ (p = 331 ∧ k % 65536 = 14336) ∨ (p = 643 ∧ k % 16 = 5) ∨ (p = 715827883 ∧ k % 32 = 5) := by
  obtain ⟨d, hd, dh, plus⟩ := divisor_before 32 p k (by decide) hp hk test
  clear test
  have hpos : 0 < 32 * p ^ k := Nat.mul_pos (by norm_num) (Nat.pow_pos hp.pos)
  have two : p ≠ 2 := odd
  have h32 : 2 ^ 32 - 1 = 3 * (5 * (17 * (257 * 65537))) := by norm_num
  rw [h32] at hd
  obtain ⟨a, d1, ha, hd1, rfl⟩ := Nat.dvd_mul.mp hd
  obtain ⟨b, d2, hb, hd2, rfl⟩ := Nat.dvd_mul.mp hd1
  obtain ⟨c, d3, hc, hd3, rfl⟩ := Nat.dvd_mul.mp hd2
  obtain ⟨e, f, he, hf, rfl⟩ := Nat.dvd_mul.mp hd3
  have h0 := (Nat.dvd_prime (by norm_num)).mp ha
  have h1 := (Nat.dvd_prime (by norm_num)).mp hb
  have h2 := (Nat.dvd_prime (by norm_num)).mp hc
  have h3 := (Nat.dvd_prime (by norm_num)).mp he
  have h4 := (Nat.dvd_prime (by norm_num)).mp hf
  clear ha hb hc he hf hd hd1 hd2 hd3
  rcases h0 with rfl | rfl
  · rcases h1 with rfl | rfl
    · rcases h2 with rfl | rfl
      · rcases h3 with rfl | rfl
        · rcases h4 with rfl | rfl
          · exact t32_leaf_0 p k hp two hpos dh plus
          · exact t32_leaf_1 p k hp two hpos dh plus
        · rcases h4 with rfl | rfl
          · exact t32_leaf_2 p k hp two hpos dh plus
          · exact t32_leaf_3 p k hp two hpos dh plus
      · rcases h3 with rfl | rfl
        · rcases h4 with rfl | rfl
          · exact t32_leaf_4 p k hp two hpos dh plus
          · exact t32_leaf_5 p k hp two hpos dh plus
        · rcases h4 with rfl | rfl
          · exact t32_leaf_6 p k hp two hpos dh plus
          · exact t32_leaf_7 p k hp two hpos dh plus
    · rcases h2 with rfl | rfl
      · rcases h3 with rfl | rfl
        · rcases h4 with rfl | rfl
          · exact t32_leaf_8 p k hp two hpos dh plus
          · exact t32_leaf_9 p k hp two hpos dh plus
        · rcases h4 with rfl | rfl
          · exact t32_leaf_10 p k hp two hpos dh plus
          · exact t32_leaf_11 p k hp two hpos dh plus
      · rcases h3 with rfl | rfl
        · rcases h4 with rfl | rfl
          · exact t32_leaf_12 p k hp two hpos dh plus
          · exact t32_leaf_13 p k hp two hpos dh plus
        · rcases h4 with rfl | rfl
          · exact t32_leaf_14 p k hp two hpos dh plus
          · exact t32_leaf_15 p k hp two hpos dh plus
  · rcases h1 with rfl | rfl
    · rcases h2 with rfl | rfl
      · rcases h3 with rfl | rfl
        · rcases h4 with rfl | rfl
          · exact t32_leaf_16 p k hp two hpos dh plus
          · exact t32_leaf_17 p k hp two hpos dh plus
        · rcases h4 with rfl | rfl
          · exact t32_leaf_18 p k hp two hpos dh plus
          · exact t32_leaf_19 p k hp two hpos dh plus
      · rcases h3 with rfl | rfl
        · rcases h4 with rfl | rfl
          · exact t32_leaf_20 p k hp two hpos dh plus
          · exact t32_leaf_21 p k hp two hpos dh plus
        · rcases h4 with rfl | rfl
          · exact t32_leaf_22 p k hp two hpos dh plus
          · exact t32_leaf_23 p k hp two hpos dh plus
    · rcases h2 with rfl | rfl
      · rcases h3 with rfl | rfl
        · rcases h4 with rfl | rfl
          · exact t32_leaf_24 p k hp two hpos dh plus
          · exact t32_leaf_25 p k hp two hpos dh plus
        · rcases h4 with rfl | rfl
          · exact t32_leaf_26 p k hp two hpos dh plus
          · exact t32_leaf_27 p k hp two hpos dh plus
      · rcases h3 with rfl | rfl
        · rcases h4 with rfl | rfl
          · exact t32_leaf_28 p k hp two hpos dh plus
          · exact t32_leaf_29 p k hp two hpos dh plus
        · rcases h4 with rfl | rfl
          · exact t32_leaf_30 p k hp two hpos dh plus
          · exact t32_leaf_31 p k hp two hpos dh plus

-- The x = 24 p^k family: lemmas by fleet-2 (desk notes #122389-#122392).

lemma p_dvd_order (o c p k : ℕ) (hp : p.Prime) (h1 : o ∣ c * p ^ k) (h2 : ¬ o ∣ c) : p ∣ o := by
  by_contra hno
  have cop : o.Coprime (p ^ k) := Nat.Coprime.pow_right k ((Nat.coprime_comm).mp ((hp.coprime_iff_not_dvd).mpr hno))
  exact h2 (cop.dvd_of_dvd_mul_right h1)

lemma geom_prime_modp (c p k q : ℕ) (hc : 0 < c) (hp : p.Prime) (hq : q.Prime)
    (hne : q ≠ p) (hd : q ∣ ∑ i ∈ Finset.range (p ^ k), (2 ^ c) ^ i) :
    q ≡ 1 [MOD p] := by
  let _ : Fact q.Prime := ⟨hq⟩
  have hsum := (ZMod.natCast_eq_zero_iff _ _).mpr hd
  push_cast at hsum
  by_cases hb : (2 : ZMod q) ^ c = 1
  · simp [hb] at hsum
    have hqp : q ∣ p ^ k := (ZMod.natCast_eq_zero_iff _ _).mp (by simpa using hsum)
    exact (hne ((Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hqp))).elim
  have hbpow : ((2 : ZMod q) ^ c) ^ (p ^ k) = 1 := by
    have h := geom_sum_mul ((2 : ZMod q) ^ c) (p ^ k)
    rw [hsum, zero_mul] at h
    exact sub_eq_zero.mp h.symm
  rw [← pow_mul] at hbpow
  have two0 : (2 : ZMod q) ≠ 0 := by
    intro h
    rw [h, zero_pow (Nat.pos_iff_ne_zero.mp (Nat.mul_pos hc (Nat.pow_pos hp.pos)))] at hbpow
    exact zero_ne_one hbpow
  have od := orderOf_dvd_of_pow_eq_one hbpow
  have nd : ¬ orderOf (2 : ZMod q) ∣ c := fun h => hb (orderOf_dvd_iff_pow_eq_one.mp h)
  have pd := p_dvd_order _ c p k hp od nd
  have card := ZMod.orderOf_dvd_card_sub_one two0
  exact ((Nat.modEq_iff_dvd' hq.one_le).mpr (pd.trans card)).symm

lemma geom_divisor_modp (c p k v : ℕ) (hc : 0 < c) (hp : p.Prime) (hn : ¬ p ∣ v)
    (hd : v ∣ ∑ i ∈ Finset.range (p ^ k), (2 ^ c) ^ i) : v ≡ 1 [MOD p] := by
  induction v using Nat.recOnMul with
  | zero => simp at hn
  | one => rfl
  | prime q hq => exact geom_prime_modp c p k q hc hp hq (by rintro rfl; exact hn dvd_rfl) hd
  | mul a b' ia ib =>
    have da : a ∣ a * b' := dvd_mul_right _ _
    have db : b' ∣ a * b' := dvd_mul_left _ _
    simpa using (ia (fun h => hn (h.trans da)) (da.trans hd)).mul
      (ib (fun h => hn (h.trans db)) (db.trans hd))

/-- A divisor of 2^(c p^k) - 1 prime to p is, modulo p, a divisor of 2^c - 1. -/
lemma small_divisor_modp (c p k v : ℕ) (hc : 0 < c) (hp : p.Prime) (hn : ¬ p ∣ v)
    (hd : v ∣ 2 ^ (c * p ^ k) - 1) :
    ∃ d : ℕ, d ∣ 2 ^ c - 1 ∧ d ∣ v ∧ v ≡ d [MOD p] := by
  let G := ∑ i ∈ Finset.range (p ^ k), (2 ^ c) ^ i
  have hG : G * (2 ^ c - 1) = 2 ^ (c * p ^ k) - 1 := by
    rw [pow_mul 2 c (p ^ k)]
    exact geom_sum_mul_of_one_le Nat.one_le_two_pow _
  obtain ⟨r, d, hr, hdBase, h⟩ :=
    exists_dvd_and_dvd_of_dvd_mul (hG.symm ▸ hd : v ∣ G * (2 ^ c - 1))
  have dr : r ∣ v := ⟨d, h⟩
  refine ⟨d, hdBase, ⟨r, by rw [h, Nat.mul_comm]⟩, ?_⟩
  have h1 := geom_divisor_modp c p k r hc hp (fun h => hn (h.trans dr)) hr
  simpa only [h, one_mul] using h1.mul_right d

-- The 96 divisors d of 2^24 - 1, each with the prime factors of d + 1, are listed inline below.

lemma PL24_prime : ∀ q ∈ ([2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 67, 71, 73, 79, 83, 103, 109, 113, 137, 139, 149, 157, 167, 179, 181, 199, 211, 229, 239, 269, 283, 293, 373, 379, 383, 397, 439, 449, 491, 613, 683, 787, 829, 967, 1013, 1523, 1567, 2113, 2531, 3259, 4973, 5419, 5483, 7079, 7417, 9587, 10243, 12653, 16981, 18979, 19973, 31069, 43019, 61681, 108943, 133153, 199729, 2796203] : List ℕ), q.Prime := by
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

lemma T24_prod : ∀ e ∈ ([
  (1, [2]),
  (3, [2, 2]),
  (5, [2, 3]),
  (7, [2, 2, 2]),
  (9, [2, 5]),
  (13, [2, 7]),
  (15, [2, 2, 2, 2]),
  (17, [2, 3, 3]),
  (21, [2, 11]),
  (35, [2, 2, 3, 3]),
  (39, [2, 2, 2, 5]),
  (45, [2, 23]),
  (51, [2, 2, 13]),
  (63, [2, 2, 2, 2, 2, 2]),
  (65, [2, 3, 11]),
  (85, [2, 43]),
  (91, [2, 2, 23]),
  (105, [2, 53]),
  (117, [2, 59]),
  (119, [2, 2, 2, 3, 5]),
  (153, [2, 7, 11]),
  (195, [2, 2, 7, 7]),
  (221, [2, 3, 37]),
  (241, [2, 11, 11]),
  (255, [2, 2, 2, 2, 2, 2, 2, 2]),
  (273, [2, 137]),
  (315, [2, 2, 79]),
  (357, [2, 179]),
  (455, [2, 2, 2, 3, 19]),
  (585, [2, 293]),
  (595, [2, 2, 149]),
  (663, [2, 2, 2, 83]),
  (723, [2, 2, 181]),
  (765, [2, 383]),
  (819, [2, 2, 5, 41]),
  (1071, [2, 2, 2, 2, 67]),
  (1105, [2, 7, 79]),
  (1205, [2, 3, 3, 67]),
  (1365, [2, 683]),
  (1547, [2, 2, 3, 3, 43]),
  (1687, [2, 2, 2, 211]),
  (1785, [2, 19, 47]),
  (1989, [2, 5, 199]),
  (2169, [2, 5, 7, 31]),
  (3133, [2, 1567]),
  (3315, [2, 2, 829]),
  (3615, [2, 2, 2, 2, 2, 113]),
  (4095, [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]),
  (4097, [2, 3, 683]),
  (4641, [2, 11, 211]),
  (5061, [2, 2531]),
  (5355, [2, 2, 13, 103]),
  (7735, [2, 2, 2, 967]),
  (8435, [2, 2, 3, 19, 37]),
  (9399, [2, 2, 2, 5, 5, 47]),
  (9945, [2, 4973]),
  (10845, [2, 11, 17, 29]),
  (12291, [2, 2, 7, 439]),
  (13923, [2, 2, 59, 59]),
  (15183, [2, 2, 2, 2, 13, 73]),
  (15665, [2, 3, 7, 373]),
  (20485, [2, 10243]),
  (21931, [2, 2, 5483]),
  (23205, [2, 41, 283]),
  (25305, [2, 12653]),
  (28197, [2, 23, 613]),
  (28679, [2, 2, 2, 3, 5, 239]),
  (36873, [2, 103, 179]),
  (46995, [2, 2, 31, 379]),
  (53261, [2, 3, 3, 11, 269]),
  (61455, [2, 2, 2, 2, 23, 167]),
  (65793, [2, 67, 491]),
  (69615, [2, 2, 2, 2, 19, 229]),
  (75915, [2, 2, 18979]),
  (86037, [2, 43019]),
  (109655, [2, 2, 2, 3, 3, 1523]),
  (140985, [2, 157, 449]),
  (143395, [2, 2, 11, 3259]),
  (159783, [2, 2, 2, 19973]),
  (184365, [2, 7, 13, 1013]),
  (197379, [2, 2, 5, 71, 139]),
  (258111, [2, 2, 2, 2, 2, 2, 37, 109]),
  (266305, [2, 133153]),
  (328965, [2, 11, 19, 787]),
  (372827, [2, 2, 3, 31069]),
  (430185, [2, 29, 7417]),
  (479349, [2, 5, 5, 9587]),
  (798915, [2, 2, 199729]),
  (986895, [2, 2, 2, 2, 61681]),
  (1118481, [2, 79, 7079]),
  (1290555, [2, 2, 19, 16981]),
  (1864135, [2, 2, 2, 43, 5419]),
  (2396745, [2, 11, 108943]),
  (3355443, [2, 2, 397, 2113]),
  (5592405, [2, 2796203]),
  (16777215, [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2])
] : List (ℕ × List ℕ)), e.1 + 1 = e.2.prod := by decide +kernel

lemma T24_sub : ∀ e ∈ ([
  (1, [2]),
  (3, [2, 2]),
  (5, [2, 3]),
  (7, [2, 2, 2]),
  (9, [2, 5]),
  (13, [2, 7]),
  (15, [2, 2, 2, 2]),
  (17, [2, 3, 3]),
  (21, [2, 11]),
  (35, [2, 2, 3, 3]),
  (39, [2, 2, 2, 5]),
  (45, [2, 23]),
  (51, [2, 2, 13]),
  (63, [2, 2, 2, 2, 2, 2]),
  (65, [2, 3, 11]),
  (85, [2, 43]),
  (91, [2, 2, 23]),
  (105, [2, 53]),
  (117, [2, 59]),
  (119, [2, 2, 2, 3, 5]),
  (153, [2, 7, 11]),
  (195, [2, 2, 7, 7]),
  (221, [2, 3, 37]),
  (241, [2, 11, 11]),
  (255, [2, 2, 2, 2, 2, 2, 2, 2]),
  (273, [2, 137]),
  (315, [2, 2, 79]),
  (357, [2, 179]),
  (455, [2, 2, 2, 3, 19]),
  (585, [2, 293]),
  (595, [2, 2, 149]),
  (663, [2, 2, 2, 83]),
  (723, [2, 2, 181]),
  (765, [2, 383]),
  (819, [2, 2, 5, 41]),
  (1071, [2, 2, 2, 2, 67]),
  (1105, [2, 7, 79]),
  (1205, [2, 3, 3, 67]),
  (1365, [2, 683]),
  (1547, [2, 2, 3, 3, 43]),
  (1687, [2, 2, 2, 211]),
  (1785, [2, 19, 47]),
  (1989, [2, 5, 199]),
  (2169, [2, 5, 7, 31]),
  (3133, [2, 1567]),
  (3315, [2, 2, 829]),
  (3615, [2, 2, 2, 2, 2, 113]),
  (4095, [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]),
  (4097, [2, 3, 683]),
  (4641, [2, 11, 211]),
  (5061, [2, 2531]),
  (5355, [2, 2, 13, 103]),
  (7735, [2, 2, 2, 967]),
  (8435, [2, 2, 3, 19, 37]),
  (9399, [2, 2, 2, 5, 5, 47]),
  (9945, [2, 4973]),
  (10845, [2, 11, 17, 29]),
  (12291, [2, 2, 7, 439]),
  (13923, [2, 2, 59, 59]),
  (15183, [2, 2, 2, 2, 13, 73]),
  (15665, [2, 3, 7, 373]),
  (20485, [2, 10243]),
  (21931, [2, 2, 5483]),
  (23205, [2, 41, 283]),
  (25305, [2, 12653]),
  (28197, [2, 23, 613]),
  (28679, [2, 2, 2, 3, 5, 239]),
  (36873, [2, 103, 179]),
  (46995, [2, 2, 31, 379]),
  (53261, [2, 3, 3, 11, 269]),
  (61455, [2, 2, 2, 2, 23, 167]),
  (65793, [2, 67, 491]),
  (69615, [2, 2, 2, 2, 19, 229]),
  (75915, [2, 2, 18979]),
  (86037, [2, 43019]),
  (109655, [2, 2, 2, 3, 3, 1523]),
  (140985, [2, 157, 449]),
  (143395, [2, 2, 11, 3259]),
  (159783, [2, 2, 2, 19973]),
  (184365, [2, 7, 13, 1013]),
  (197379, [2, 2, 5, 71, 139]),
  (258111, [2, 2, 2, 2, 2, 2, 37, 109]),
  (266305, [2, 133153]),
  (328965, [2, 11, 19, 787]),
  (372827, [2, 2, 3, 31069]),
  (430185, [2, 29, 7417]),
  (479349, [2, 5, 5, 9587]),
  (798915, [2, 2, 199729]),
  (986895, [2, 2, 2, 2, 61681]),
  (1118481, [2, 79, 7079]),
  (1290555, [2, 2, 19, 16981]),
  (1864135, [2, 2, 2, 43, 5419]),
  (2396745, [2, 11, 108943]),
  (3355443, [2, 2, 397, 2113]),
  (5592405, [2, 2796203]),
  (16777215, [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2])
] : List (ℕ × List ℕ)), ∀ q ∈ e.2, q ∈ ([2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 67, 71, 73, 79, 83, 103, 109, 113, 137, 139, 149, 157, 167, 179, 181, 199, 211, 229, 239, 269, 283, 293, 373, 379, 383, 397, 439, 449, 491, 613, 683, 787, 829, 967, 1013, 1523, 1567, 2113, 2531, 3259, 4973, 5419, 5483, 7079, 7417, 9587, 10243, 12653, 16981, 18979, 19973, 31069, 43019, 61681, 108943, 133153, 199729, 2796203] : List ℕ) := by decide +kernel

lemma T24_cover : ∀ a ∈ Nat.divisors 9, ∀ b ∈ Nat.divisors 5, ∀ c ∈ Nat.divisors 7,
    ∀ e ∈ Nat.divisors 13, ∀ f ∈ Nat.divisors 17, ∀ g ∈ Nat.divisors 241,
    ∃ t ∈ ([
  (1, [2]),
  (3, [2, 2]),
  (5, [2, 3]),
  (7, [2, 2, 2]),
  (9, [2, 5]),
  (13, [2, 7]),
  (15, [2, 2, 2, 2]),
  (17, [2, 3, 3]),
  (21, [2, 11]),
  (35, [2, 2, 3, 3]),
  (39, [2, 2, 2, 5]),
  (45, [2, 23]),
  (51, [2, 2, 13]),
  (63, [2, 2, 2, 2, 2, 2]),
  (65, [2, 3, 11]),
  (85, [2, 43]),
  (91, [2, 2, 23]),
  (105, [2, 53]),
  (117, [2, 59]),
  (119, [2, 2, 2, 3, 5]),
  (153, [2, 7, 11]),
  (195, [2, 2, 7, 7]),
  (221, [2, 3, 37]),
  (241, [2, 11, 11]),
  (255, [2, 2, 2, 2, 2, 2, 2, 2]),
  (273, [2, 137]),
  (315, [2, 2, 79]),
  (357, [2, 179]),
  (455, [2, 2, 2, 3, 19]),
  (585, [2, 293]),
  (595, [2, 2, 149]),
  (663, [2, 2, 2, 83]),
  (723, [2, 2, 181]),
  (765, [2, 383]),
  (819, [2, 2, 5, 41]),
  (1071, [2, 2, 2, 2, 67]),
  (1105, [2, 7, 79]),
  (1205, [2, 3, 3, 67]),
  (1365, [2, 683]),
  (1547, [2, 2, 3, 3, 43]),
  (1687, [2, 2, 2, 211]),
  (1785, [2, 19, 47]),
  (1989, [2, 5, 199]),
  (2169, [2, 5, 7, 31]),
  (3133, [2, 1567]),
  (3315, [2, 2, 829]),
  (3615, [2, 2, 2, 2, 2, 113]),
  (4095, [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]),
  (4097, [2, 3, 683]),
  (4641, [2, 11, 211]),
  (5061, [2, 2531]),
  (5355, [2, 2, 13, 103]),
  (7735, [2, 2, 2, 967]),
  (8435, [2, 2, 3, 19, 37]),
  (9399, [2, 2, 2, 5, 5, 47]),
  (9945, [2, 4973]),
  (10845, [2, 11, 17, 29]),
  (12291, [2, 2, 7, 439]),
  (13923, [2, 2, 59, 59]),
  (15183, [2, 2, 2, 2, 13, 73]),
  (15665, [2, 3, 7, 373]),
  (20485, [2, 10243]),
  (21931, [2, 2, 5483]),
  (23205, [2, 41, 283]),
  (25305, [2, 12653]),
  (28197, [2, 23, 613]),
  (28679, [2, 2, 2, 3, 5, 239]),
  (36873, [2, 103, 179]),
  (46995, [2, 2, 31, 379]),
  (53261, [2, 3, 3, 11, 269]),
  (61455, [2, 2, 2, 2, 23, 167]),
  (65793, [2, 67, 491]),
  (69615, [2, 2, 2, 2, 19, 229]),
  (75915, [2, 2, 18979]),
  (86037, [2, 43019]),
  (109655, [2, 2, 2, 3, 3, 1523]),
  (140985, [2, 157, 449]),
  (143395, [2, 2, 11, 3259]),
  (159783, [2, 2, 2, 19973]),
  (184365, [2, 7, 13, 1013]),
  (197379, [2, 2, 5, 71, 139]),
  (258111, [2, 2, 2, 2, 2, 2, 37, 109]),
  (266305, [2, 133153]),
  (328965, [2, 11, 19, 787]),
  (372827, [2, 2, 3, 31069]),
  (430185, [2, 29, 7417]),
  (479349, [2, 5, 5, 9587]),
  (798915, [2, 2, 199729]),
  (986895, [2, 2, 2, 2, 61681]),
  (1118481, [2, 79, 7079]),
  (1290555, [2, 2, 19, 16981]),
  (1864135, [2, 2, 2, 43, 5419]),
  (2396745, [2, 11, 108943]),
  (3355443, [2, 2, 397, 2113]),
  (5592405, [2, 2796203]),
  (16777215, [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2])
] : List (ℕ × List ℕ)), t.1 = a * (b * (c * (e * (f * g)))) := by decide +kernel

/-- For each divisor d of 2^24 - 1 prime to 3 and each prime q | d + 1 outside {2,3,5,7,19}:
    q^240 ≡ 1 mod d, and 24 q^r is never 1 mod d. -/
lemma T24_cert : ∀ e ∈ ([
  (1, [2]),
  (3, [2, 2]),
  (5, [2, 3]),
  (7, [2, 2, 2]),
  (9, [2, 5]),
  (13, [2, 7]),
  (15, [2, 2, 2, 2]),
  (17, [2, 3, 3]),
  (21, [2, 11]),
  (35, [2, 2, 3, 3]),
  (39, [2, 2, 2, 5]),
  (45, [2, 23]),
  (51, [2, 2, 13]),
  (63, [2, 2, 2, 2, 2, 2]),
  (65, [2, 3, 11]),
  (85, [2, 43]),
  (91, [2, 2, 23]),
  (105, [2, 53]),
  (117, [2, 59]),
  (119, [2, 2, 2, 3, 5]),
  (153, [2, 7, 11]),
  (195, [2, 2, 7, 7]),
  (221, [2, 3, 37]),
  (241, [2, 11, 11]),
  (255, [2, 2, 2, 2, 2, 2, 2, 2]),
  (273, [2, 137]),
  (315, [2, 2, 79]),
  (357, [2, 179]),
  (455, [2, 2, 2, 3, 19]),
  (585, [2, 293]),
  (595, [2, 2, 149]),
  (663, [2, 2, 2, 83]),
  (723, [2, 2, 181]),
  (765, [2, 383]),
  (819, [2, 2, 5, 41]),
  (1071, [2, 2, 2, 2, 67]),
  (1105, [2, 7, 79]),
  (1205, [2, 3, 3, 67]),
  (1365, [2, 683]),
  (1547, [2, 2, 3, 3, 43]),
  (1687, [2, 2, 2, 211]),
  (1785, [2, 19, 47]),
  (1989, [2, 5, 199]),
  (2169, [2, 5, 7, 31]),
  (3133, [2, 1567]),
  (3315, [2, 2, 829]),
  (3615, [2, 2, 2, 2, 2, 113]),
  (4095, [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]),
  (4097, [2, 3, 683]),
  (4641, [2, 11, 211]),
  (5061, [2, 2531]),
  (5355, [2, 2, 13, 103]),
  (7735, [2, 2, 2, 967]),
  (8435, [2, 2, 3, 19, 37]),
  (9399, [2, 2, 2, 5, 5, 47]),
  (9945, [2, 4973]),
  (10845, [2, 11, 17, 29]),
  (12291, [2, 2, 7, 439]),
  (13923, [2, 2, 59, 59]),
  (15183, [2, 2, 2, 2, 13, 73]),
  (15665, [2, 3, 7, 373]),
  (20485, [2, 10243]),
  (21931, [2, 2, 5483]),
  (23205, [2, 41, 283]),
  (25305, [2, 12653]),
  (28197, [2, 23, 613]),
  (28679, [2, 2, 2, 3, 5, 239]),
  (36873, [2, 103, 179]),
  (46995, [2, 2, 31, 379]),
  (53261, [2, 3, 3, 11, 269]),
  (61455, [2, 2, 2, 2, 23, 167]),
  (65793, [2, 67, 491]),
  (69615, [2, 2, 2, 2, 19, 229]),
  (75915, [2, 2, 18979]),
  (86037, [2, 43019]),
  (109655, [2, 2, 2, 3, 3, 1523]),
  (140985, [2, 157, 449]),
  (143395, [2, 2, 11, 3259]),
  (159783, [2, 2, 2, 19973]),
  (184365, [2, 7, 13, 1013]),
  (197379, [2, 2, 5, 71, 139]),
  (258111, [2, 2, 2, 2, 2, 2, 37, 109]),
  (266305, [2, 133153]),
  (328965, [2, 11, 19, 787]),
  (372827, [2, 2, 3, 31069]),
  (430185, [2, 29, 7417]),
  (479349, [2, 5, 5, 9587]),
  (798915, [2, 2, 199729]),
  (986895, [2, 2, 2, 2, 61681]),
  (1118481, [2, 79, 7079]),
  (1290555, [2, 2, 19, 16981]),
  (1864135, [2, 2, 2, 43, 5419]),
  (2396745, [2, 11, 108943]),
  (3355443, [2, 2, 397, 2113]),
  (5592405, [2, 2796203]),
  (16777215, [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2])
] : List (ℕ × List ℕ)), e.1 % 3 ≠ 0 → ∀ q ∈ e.2, q ≠ 2 → q ≠ 3 → q ≠ 5 → q ≠ 7 → q ≠ 19 →
    q ^ 240 % e.1 = 1 % e.1 ∧ ∀ r < 240, (24 * q ^ r) % e.1 ≠ 1 % e.1 := by decide +kernel

lemma prime_mem_of_dvd_prod (p : ℕ) (hp : p.Prime) :
    ∀ L : List ℕ, (∀ q ∈ L, q.Prime) → p ∣ L.prod → p ∈ L
  | [], _, h => by
    simp only [List.prod_nil, Nat.dvd_one] at h
    exact (hp.ne_one h).elim
  | q :: L, hL, h => by
    rw [List.prod_cons] at h
    rcases (Nat.Prime.dvd_mul hp).mp h with h1 | h1
    · exact List.mem_cons.mpr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (hL q (by simp))).mp h1))
    · exact List.mem_cons_of_mem _
        (prime_mem_of_dvd_prod p hp L (fun r hr => hL r (List.mem_cons_of_mem _ hr)) h1)

lemma divisor_decomp (d : ℕ) (h : d ∣ 2 ^ 24 - 1) : ∃ t ∈ ([
  (1, [2]),
  (3, [2, 2]),
  (5, [2, 3]),
  (7, [2, 2, 2]),
  (9, [2, 5]),
  (13, [2, 7]),
  (15, [2, 2, 2, 2]),
  (17, [2, 3, 3]),
  (21, [2, 11]),
  (35, [2, 2, 3, 3]),
  (39, [2, 2, 2, 5]),
  (45, [2, 23]),
  (51, [2, 2, 13]),
  (63, [2, 2, 2, 2, 2, 2]),
  (65, [2, 3, 11]),
  (85, [2, 43]),
  (91, [2, 2, 23]),
  (105, [2, 53]),
  (117, [2, 59]),
  (119, [2, 2, 2, 3, 5]),
  (153, [2, 7, 11]),
  (195, [2, 2, 7, 7]),
  (221, [2, 3, 37]),
  (241, [2, 11, 11]),
  (255, [2, 2, 2, 2, 2, 2, 2, 2]),
  (273, [2, 137]),
  (315, [2, 2, 79]),
  (357, [2, 179]),
  (455, [2, 2, 2, 3, 19]),
  (585, [2, 293]),
  (595, [2, 2, 149]),
  (663, [2, 2, 2, 83]),
  (723, [2, 2, 181]),
  (765, [2, 383]),
  (819, [2, 2, 5, 41]),
  (1071, [2, 2, 2, 2, 67]),
  (1105, [2, 7, 79]),
  (1205, [2, 3, 3, 67]),
  (1365, [2, 683]),
  (1547, [2, 2, 3, 3, 43]),
  (1687, [2, 2, 2, 211]),
  (1785, [2, 19, 47]),
  (1989, [2, 5, 199]),
  (2169, [2, 5, 7, 31]),
  (3133, [2, 1567]),
  (3315, [2, 2, 829]),
  (3615, [2, 2, 2, 2, 2, 113]),
  (4095, [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]),
  (4097, [2, 3, 683]),
  (4641, [2, 11, 211]),
  (5061, [2, 2531]),
  (5355, [2, 2, 13, 103]),
  (7735, [2, 2, 2, 967]),
  (8435, [2, 2, 3, 19, 37]),
  (9399, [2, 2, 2, 5, 5, 47]),
  (9945, [2, 4973]),
  (10845, [2, 11, 17, 29]),
  (12291, [2, 2, 7, 439]),
  (13923, [2, 2, 59, 59]),
  (15183, [2, 2, 2, 2, 13, 73]),
  (15665, [2, 3, 7, 373]),
  (20485, [2, 10243]),
  (21931, [2, 2, 5483]),
  (23205, [2, 41, 283]),
  (25305, [2, 12653]),
  (28197, [2, 23, 613]),
  (28679, [2, 2, 2, 3, 5, 239]),
  (36873, [2, 103, 179]),
  (46995, [2, 2, 31, 379]),
  (53261, [2, 3, 3, 11, 269]),
  (61455, [2, 2, 2, 2, 23, 167]),
  (65793, [2, 67, 491]),
  (69615, [2, 2, 2, 2, 19, 229]),
  (75915, [2, 2, 18979]),
  (86037, [2, 43019]),
  (109655, [2, 2, 2, 3, 3, 1523]),
  (140985, [2, 157, 449]),
  (143395, [2, 2, 11, 3259]),
  (159783, [2, 2, 2, 19973]),
  (184365, [2, 7, 13, 1013]),
  (197379, [2, 2, 5, 71, 139]),
  (258111, [2, 2, 2, 2, 2, 2, 37, 109]),
  (266305, [2, 133153]),
  (328965, [2, 11, 19, 787]),
  (372827, [2, 2, 3, 31069]),
  (430185, [2, 29, 7417]),
  (479349, [2, 5, 5, 9587]),
  (798915, [2, 2, 199729]),
  (986895, [2, 2, 2, 2, 61681]),
  (1118481, [2, 79, 7079]),
  (1290555, [2, 2, 19, 16981]),
  (1864135, [2, 2, 2, 43, 5419]),
  (2396745, [2, 11, 108943]),
  (3355443, [2, 2, 397, 2113]),
  (5592405, [2, 2796203]),
  (16777215, [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2])
] : List (ℕ × List ℕ)), t.1 = d := by
  have e : 2 ^ 24 - 1 = 9 * (5 * (7 * (13 * (17 * 241)))) := by norm_num
  rw [e] at h
  obtain ⟨a, d1, ha, h1, rfl⟩ := Nat.dvd_mul.mp h
  obtain ⟨b, d2, hb, h2, rfl⟩ := Nat.dvd_mul.mp h1
  obtain ⟨c, d3, hc, h3, rfl⟩ := Nat.dvd_mul.mp h2
  obtain ⟨e', d4, he, h4, rfl⟩ := Nat.dvd_mul.mp h3
  obtain ⟨f, g, hf, hg, rfl⟩ := Nat.dvd_mul.mp h4
  exact T24_cover a (Nat.mem_divisors.mpr ⟨ha, by norm_num⟩) b (Nat.mem_divisors.mpr ⟨hb, by norm_num⟩)
    c (Nat.mem_divisors.mpr ⟨hc, by norm_num⟩) e' (Nat.mem_divisors.mpr ⟨he, by norm_num⟩)
    f (Nat.mem_divisors.mpr ⟨hf, by norm_num⟩) g (Nat.mem_divisors.mpr ⟨hg, by norm_num⟩)

/-- No x = 24 p^k with p a prime outside {2, 3, 5, 7, 19} passes Hasler's test. -/
theorem twentyfour_fails (p k : ℕ) (hp : p.Prime) (hk : k ≠ 0) (h2 : p ≠ 2) (h3 : p ≠ 3)
    (h5 : p ≠ 5) (h7 : p ≠ 7) (h19 : p ≠ 19) :
    ¬ ((24 * p ^ k) ^ 4 - 1 ∣ 2 ^ (24 * p ^ k) - 1) := by
  intro test
  have xpos : 0 < 24 * p ^ k := Nat.mul_pos (by norm_num) (Nat.pow_pos hp.pos)
  have px : p ∣ 24 * p ^ k := dvd_mul_of_dvd_right (dvd_pow_self p hk) 24
  have np : ¬ p ∣ 24 * p ^ k - 1 := by
    intro h
    have h1 : p ∣ (24 * p ^ k - 1) + 1 := by rwa [Nat.sub_add_cancel xpos]
    exact hp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right h).mp h1))
  have x1 : 24 * p ^ k - 1 ∣ 2 ^ (24 * p ^ k) - 1 :=
    (Nat.sub_one_dvd_pow_sub_one _ 4).trans test
  obtain ⟨d, hd, dx, cong⟩ := small_divisor_modp 24 p k _ (by norm_num) hp np x1
  have dp : p ∣ d + 1 := by
    have c2 : d + 1 ≡ 24 * p ^ k [MOD p] := by
      have := cong.symm.add_right 1
      rwa [Nat.sub_add_cancel xpos] at this
    exact Nat.modEq_zero_iff_dvd.mp (c2.trans (Nat.modEq_zero_iff_dvd.mpr px))
  obtain ⟨t, ht, rfl⟩ := divisor_decomp d hd
  have pmem : p ∈ t.2 :=
    prime_mem_of_dvd_prod p hp t.2 (fun q hq => PL24_prime q (T24_sub t ht q hq))
      (T24_prod t ht ▸ dp)
  have d3 : t.1 % 3 ≠ 0 := by
    intro h0
    have h3d : 3 ∣ 24 * p ^ k - 1 := (Nat.dvd_of_mod_eq_zero h0).trans dx
    generalize p ^ k = y at h3d xpos
    omega
  obtain ⟨per, hr⟩ := T24_cert t ht d3 p pmem h2 h3 h5 h7 h19
  apply hr (k % 240) (Nat.mod_lt _ (by norm_num))
  have m1 : 1 ≡ 24 * p ^ k [MOD t.1] := (Nat.modEq_iff_dvd' (by omega)).mpr dx
  have m2 : 24 * p ^ k ≡ 24 * p ^ (k % 240) [MOD t.1] := (pow_period p k 240 t.1 per).mul_left 24
  exact (m1.trans m2).symm

/-- No x = 8 p^k with p an odd prime passes Hasler's test. -/
theorem eight_prime_power_fails (p k : ℕ) (hp : p.Prime) (odd : p ≠ 2) (hk : k ≠ 0) :
    ¬ ((8 * p ^ k) ^ 4 - 1 ∣ 2 ^ (8 * p ^ k) - 1) := by
  intro test
  obtain rfl := eight_prime_power p k hp odd hk test
  exact eight_three_fails k hk test

theorem main : H1 → H2 → OMA.R_oeis_a000215_R1.H3 := by
  intro h1 h2 x big four np npow _ _ _ _ mbound _ test
  have hmod : x % 8 = 0 ∨ x % 8 = 4 := by omega
  rcases hmod with h0 | h4
  · refine h2 x big (by omega) np npow ?_ ?_ ?_ ?_ mbound test
    · rintro p k hp hp2 hk rfl
      exact eight_prime_power_fails p k hp hp2 hk test
    · rintro p k hp hp2 hk rfl
      exact sixteen_prime_power p k hp hp2 hk test
    · rintro p k hp hp2 hk rfl
      by_contra hne
      simp only [not_or] at hne
      exact twentyfour_fails p k hp hk hp2 hne.1 hne.2.1 hne.2.2.1 hne.2.2.2 test
    · rintro p k hp hp2 hk rfl
      exact thirtytwo_prime_power p k hp hp2 hk test
  · obtain ⟨t, rfl⟩ : ∃ t, x = 4 * t := ⟨x / 4, by omega⟩
    have todd : Odd t := ⟨t / 2, by omega⟩
    apply h1 t todd (by omega)
    have hsq : 16 * t ^ 2 + 1 = (4 * t) ^ 2 + 1 := by ring
    rw [hsq]
    exact dvd_trans (square_add_one_dvd (4 * t) (by omega)) test

end OMA.R_oeis_a000215_R1_H3_R1
