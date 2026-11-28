import OMAStatements.S_oeis_a378444
import Mathlib

-- Problem: OEIS A378444, a(n) = number of divisors d of n such that A083345(d) is even, where
-- A083345(d) is the numerator of r(d) = Sum(e/p : d = Product p^e).
-- Conjecture of Antti Karttunen: a(n) = ceiling(A174273(n)/2).
-- Statement: statements/oeis-a378444.lean (declaration OMA.S_oeis_a378444.main)
-- Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)
--
-- Proof. Let sg be the multiplicative function with sg(2^v) = (-1)^(v/2) for even v,
-- sg(2^v) = 0 for odd v, and sg(p^v) = (-1)^v for odd primes p. By induction on the
-- factorization (lemma Q_all), for each d >= 1 one of these two cases holds:
-- * the 2-adic valuation of d is even, r(d) = A/B with B odd, and sg(d) = (-1)^A;
-- * the 2-adic valuation of d is odd, sg(d) = 0, and r(d) = T/(2B) with T and B odd.
-- In the first case the numerator of r(d) has the parity of A, and in the second case it is
-- odd. Thus 2 [A083345(d) even] = A035263(d) + sg(d) (lemma pointwise), and the sum over the
-- divisors of n gives 2 a(n) = A174273(n) + S(n), where S(n) is the sum of sg(d) over d | n.
-- S is multiplicative, and S(p^v) is 0 or 1 (the partial sums of 1, -1, 1, -1, ... and of
-- 1, 0, -1, 0, 1, 0, ...). Thus S(n) is 0 or 1, and a(n) = ceiling(A174273(n)/2).

namespace OMA.A378444

open OMA.S_oeis_a378444

/-- The local factor of the sign function. -/
def w (p v : ℕ) : ℤ := if p = 2 then (if Even v then (-1) ^ (v / 2) else 0) else (-1) ^ v

/-- The sign function: multiplicative, `sg (p ^ v) = w p v`. -/
def sg (d : ℕ) : ℤ := if d = 0 then 0 else d.factorization.prod w

/-- `par A` is 1 for even `A` and -1 for odd `A`. -/
def par (A : ℤ) : ℤ := if Even A then 1 else -1

lemma w_zero (p : ℕ) : w p 0 = 1 := by
  unfold w
  simp

lemma sg_one : sg 1 = 1 := by simp [sg]

lemma sg_mul (x y : ℕ) (h : Nat.Coprime x y) (hx : x ≠ 0) (hy : y ≠ 0) :
    sg (x * y) = sg x * sg y := by
  unfold sg
  rw [if_neg (Nat.mul_ne_zero hx hy), if_neg hx, if_neg hy, Nat.factorization_mul_of_coprime h,
    Finsupp.prod_add_index_of_disjoint]
  rw [Nat.support_factorization, Nat.support_factorization]
  exact h.disjoint_primeFactors

lemma sg_prime_pow (p v : ℕ) (hp : p.Prime) : sg (p ^ v) = w p v := by
  unfold sg
  rw [if_neg (pow_ne_zero v hp.ne_zero), hp.factorization_pow, Finsupp.prod_single_index (w_zero p)]

lemma f_one : f 1 = 0 := by simp [f]

lemma f_mul (x y : ℕ) (hx : x ≠ 0) (hy : y ≠ 0) : f (x * y) = f x + f y := by
  unfold f
  rw [Nat.factorization_mul hx hy, Finsupp.sum_add_index']
  · intro p
    simp
  · intro p e1 e2
    push_cast
    ring

lemma f_prime_pow (p v : ℕ) (hp : p.Prime) : f (p ^ v) = (v : ℚ) / p := by
  unfold f
  rw [hp.factorization_pow, Finsupp.sum_single_index]
  simp

lemma par_natCast (c : ℕ) : par (c : ℤ) = (-1) ^ c := by
  unfold par
  rcases Nat.even_or_odd c with h | h
  · rw [if_pos (by exact_mod_cast h), h.neg_one_pow]
  · rw [if_neg (by rw [Int.not_even_iff_odd]; exact_mod_cast h), h.neg_one_pow]

lemma par_add (A1 A2 : ℤ) (B1 B2 : ℕ) (h1 : Odd B1) (h2 : Odd B2) :
    par (A1 * B2 + A2 * B1) = par A1 * par A2 := by
  have h1' : ¬ Even (B1 : ℤ) := by rw [Int.not_even_iff_odd]; exact_mod_cast h1
  have h2' : ¬ Even (B2 : ℤ) := by rw [Int.not_even_iff_odd]; exact_mod_cast h2
  unfold par
  by_cases e1 : Even A1 <;> by_cases e2 : Even A2 <;>
    simp [Int.even_add, Int.even_mul, e1, e2, h1', h2']

/-- The invariant that connects `f`, `sg` and the 2-adic valuation. -/
def Q (d : ℕ) : Prop :=
  (Even (padicValNat 2 d) ∧ ∃ A : ℤ, ∃ B : ℕ, Odd B ∧ f d = (A : ℚ) / (B : ℚ) ∧ sg d = par A) ∨
  (¬ Even (padicValNat 2 d) ∧ sg d = 0 ∧
    ∃ T : ℤ, ∃ B : ℕ, Odd T ∧ Odd B ∧ f d = (T : ℚ) / (2 * (B : ℚ)))

lemma Q_mul (x y : ℕ) (hc : Nat.Coprime x y) (hx : x ≠ 0) (hy : y ≠ 0) (qx : Q x) (qy : Q y) :
    Q (x * y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hv : padicValNat 2 (x * y) = padicValNat 2 x + padicValNat 2 y := padicValNat.mul hx hy
  rcases qx with ⟨ex, A1, B1, hB1, hf1, hs1⟩ | ⟨ex, hs1, T1, B1, hT1, hB1, hf1⟩
  · rcases qy with ⟨ey, A2, B2, hB2, hf2, hs2⟩ | ⟨ey, hs2, T2, B2, hT2, hB2, hf2⟩
    · left
      refine ⟨by rw [hv]; exact ex.add ey, A1 * B2 + A2 * B1, B1 * B2, hB1.mul hB2, ?_, ?_⟩
      · have h1 : (B1 : ℚ) ≠ 0 := by exact_mod_cast hB1.pos.ne'
        have h2 : (B2 : ℚ) ≠ 0 := by exact_mod_cast hB2.pos.ne'
        rw [f_mul x y hx hy, hf1, hf2, div_add_div _ _ h1 h2]
        push_cast
        ring
      · rw [sg_mul x y hc hx hy, hs1, hs2, par_add A1 A2 B1 B2 hB1 hB2]
    · right
      refine ⟨by rw [hv, Nat.even_add]; tauto, by rw [sg_mul x y hc hx hy, hs2, mul_zero],
        2 * A1 * B2 + T2 * B1, B1 * B2, ?_, hB1.mul hB2, ?_⟩
      · have : Odd (T2 * (B1 : ℤ)) := hT2.mul (by exact_mod_cast hB1)
        have he : Even (2 * A1 * (B2 : ℤ)) := ⟨A1 * B2, by ring⟩
        exact he.add_odd this
      · have h1 : (B1 : ℚ) ≠ 0 := by exact_mod_cast hB1.pos.ne'
        have h2 : (B2 : ℚ) ≠ 0 := by exact_mod_cast hB2.pos.ne'
        rw [f_mul x y hx hy, hf1, hf2]
        push_cast
        field_simp
  · rcases qy with ⟨ey, A2, B2, hB2, hf2, hs2⟩ | ⟨ey, hs2, T2, B2, hT2, hB2, hf2⟩
    · right
      refine ⟨by rw [hv, Nat.even_add]; tauto, by rw [sg_mul x y hc hx hy, hs1, zero_mul],
        T1 * B2 + 2 * A2 * B1, B1 * B2, ?_, hB1.mul hB2, ?_⟩
      · have : Odd (T1 * (B2 : ℤ)) := hT1.mul (by exact_mod_cast hB2)
        have he : Even (2 * A2 * (B1 : ℤ)) := ⟨A2 * B1, by ring⟩
        exact this.add_even he
      · have h1 : (B1 : ℚ) ≠ 0 := by exact_mod_cast hB1.pos.ne'
        have h2 : (B2 : ℚ) ≠ 0 := by exact_mod_cast hB2.pos.ne'
        rw [f_mul x y hx hy, hf1, hf2]
        push_cast
        field_simp
    · exfalso
      have hx2 : 2 ∣ x := dvd_of_one_le_padicValNat (by
        rcases Nat.eq_zero_or_pos (padicValNat 2 x) with h | h
        · rw [h] at ex; exact absurd Even.zero ex
        · exact h)
      have hy2 : 2 ∣ y := dvd_of_one_le_padicValNat (by
        rcases Nat.eq_zero_or_pos (padicValNat 2 y) with h | h
        · rw [h] at ey; exact absurd Even.zero ey
        · exact h)
      exact Nat.not_coprime_of_dvd_of_dvd (by norm_num) hx2 hy2 hc

lemma Q_prime_pow (p v : ℕ) (hp : p.Prime) : Q (p ^ v) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases h2 : p = 2
  · subst h2
    have hv : padicValNat 2 (2 ^ v) = v := padicValNat.prime_pow v
    rcases Nat.even_or_odd v with he | ho
    · left
      obtain ⟨c, hc⟩ := he
      refine ⟨by rw [hv]; exact ⟨c, hc⟩, (c : ℤ), 1, odd_one, ?_, ?_⟩
      · rw [f_prime_pow 2 v hp, hc]
        push_cast
        ring
      · rw [sg_prime_pow 2 v hp, par_natCast]
        unfold w
        rw [if_pos rfl, if_pos ⟨c, hc⟩]
        congr 1
        omega
    · right
      refine ⟨by rw [hv]; exact Nat.not_even_iff_odd.mpr ho, ?_, (v : ℤ), 1, by exact_mod_cast ho,
        odd_one, ?_⟩
      · rw [sg_prime_pow 2 v hp]
        unfold w
        rw [if_pos rfl, if_neg (Nat.not_even_iff_odd.mpr ho)]
      · rw [f_prime_pow 2 v hp]
        push_cast
        ring
  · left
    have hodd : Odd p := hp.odd_of_ne_two h2
    have hnd : ¬ 2 ∣ p ^ v := by
      intro h
      have := Nat.prime_two.dvd_of_dvd_pow h
      rw [Nat.prime_dvd_prime_iff_eq Nat.prime_two hp] at this
      exact h2 this.symm
    refine ⟨by rw [padicValNat.eq_zero_of_not_dvd hnd]; exact Even.zero, (v : ℤ), p, hodd, ?_, ?_⟩
    · rw [f_prime_pow p v hp]
      push_cast
      ring
    · rw [sg_prime_pow p v hp, par_natCast]
      unfold w
      rw [if_neg h2]

lemma Q_all (d : ℕ) : d ≠ 0 → Q d := by
  induction d using Nat.recOnPosPrimePosCoprime with
  | prime_pow p v hp hv => exact fun _ => Q_prime_pow p v hp
  | zero => exact fun h => absurd rfl h
  | one =>
    intro _
    left
    refine ⟨by simp, 0, 1, odd_one, by simp [f_one], ?_⟩
    rw [sg_one]
    simp [par]
  | coprime x y hx hy hc ihx ihy =>
    intro _
    exact Q_mul x y hc (by omega) (by omega) (ihx (by omega)) (ihy (by omega))

lemma cross (q : ℚ) (A : ℤ) (B : ℚ) (hB : B ≠ 0) (h : q = (A : ℚ) / B) :
    (q.num : ℚ) * B = (A : ℚ) * (q.den : ℚ) := by
  have hden : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
  have h1 : (q.num : ℚ) / (q.den : ℚ) = (A : ℚ) / B := by rw [Rat.num_div_den, h]
  rwa [div_eq_div_iff hden hB] at h1

lemma not_both_even (q : ℚ) (h1 : Even q.num) (h2 : Even (q.den : ℤ)) : False := by
  have hcop := q.reduced
  have e1 : 2 ∣ q.num.natAbs := by
    obtain ⟨c, hc⟩ := h1
    exact Int.natCast_dvd_natCast.mp (by rw [Int.natCast_natAbs]; exact (dvd_abs 2 q.num).mpr ⟨c, by rw [hc]; ring⟩)
  have e2 : 2 ∣ q.den := by
    obtain ⟨c, hc⟩ := h2
    exact Int.natCast_dvd_natCast.mp ⟨c, by rw [hc]; ring⟩
  exact Nat.not_coprime_of_dvd_of_dvd (by norm_num) e1 e2 hcop

lemma numL (q : ℚ) (A : ℤ) (B : ℕ) (hB : Odd B) (h : q = (A : ℚ) / (B : ℚ)) :
    Even q.num ↔ Even A := by
  have hB0 : (B : ℚ) ≠ 0 := by exact_mod_cast hB.pos.ne'
  have hc : q.num * (B : ℤ) = A * (q.den : ℤ) := by exact_mod_cast cross q A B hB0 h
  have hBo : ¬ Even (B : ℤ) := by rw [Int.not_even_iff_odd]; exact_mod_cast hB
  have hdo : ¬ Even (q.den : ℤ) := by
    intro hd
    have h1 : Even (q.num * (B : ℤ)) := by rw [hc]; exact hd.mul_left A
    rw [Int.even_mul] at h1
    rcases h1 with h1 | h1
    · exact not_both_even q h1 hd
    · exact hBo h1
  have e1 : Even (q.num * (B : ℤ)) ↔ Even q.num := by rw [Int.even_mul]; tauto
  have e2 : Even (A * (q.den : ℤ)) ↔ Even A := by rw [Int.even_mul]; tauto
  rw [← e1, hc, e2]

lemma numR (q : ℚ) (T : ℤ) (B : ℕ) (hT : Odd T) (hB : Odd B) (h : q = (T : ℚ) / (2 * (B : ℚ))) :
    ¬ Even q.num := by
  intro hn
  have hB0 : (2 * (B : ℚ)) ≠ 0 := by
    have : (B : ℚ) ≠ 0 := by exact_mod_cast hB.pos.ne'
    positivity
  have hc : q.num * (2 * (B : ℤ)) = T * (q.den : ℤ) := by exact_mod_cast cross q T _ hB0 h
  have h1 : Even (T * (q.den : ℤ)) := by rw [← hc]; exact ⟨q.num * B, by ring⟩
  rw [Int.even_mul] at h1
  rcases h1 with h1 | h1
  · exact (Int.not_even_iff_odd.mpr hT) h1
  · exact not_both_even q hn h1

/-- The pointwise identity: twice the indicator of an even numerator is the indicator of an
even 2-adic valuation plus the sign. -/
lemma pointwise (d : ℕ) (hd : d ≠ 0) :
    2 * (if Even (f d).num then (1 : ℤ) else 0)
      = (if Even (padicValNat 2 d) then (1 : ℤ) else 0) + sg d := by
  rcases Q_all d hd with ⟨ev, A, B, hB, hf, hs⟩ | ⟨ev, hs, T, B, hT, hB, hf⟩
  · rw [if_pos ev, hs]
    have := numL (f d) A B hB hf
    unfold par
    by_cases hA : Even A
    · rw [if_pos (this.mpr hA), if_pos hA]
      norm_num
    · rw [if_neg (fun h => hA (this.mp h)), if_neg hA]
      norm_num
  · rw [if_neg ev, hs, if_neg (numR (f d) T B hT hB hf)]
    norm_num

lemma wsum_odd (v : ℕ) :
    ∑ i ∈ Finset.range (v + 1), ((-1 : ℤ)) ^ i = if Even v then 1 else 0 := by
  induction v with
  | zero => simp
  | succ v ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases h : Even v
    · have ho : Odd (v + 1) := h.add_one
      rw [if_pos h, if_neg (Nat.not_even_iff_odd.mpr ho), ho.neg_one_pow]
      norm_num
    · have he : Even (v + 1) := (Nat.not_even_iff_odd.mp h).add_one
      rw [if_neg h, if_pos he, he.neg_one_pow]
      norm_num

lemma wsum_two (v : ℕ) :
    ∑ i ∈ Finset.range (v + 1), w 2 i = if v % 4 < 2 then 1 else 0 := by
  induction v with
  | zero => simp [w]
  | succ v ih =>
    rw [Finset.sum_range_succ, ih]
    unfold w
    rw [if_pos rfl]
    have h4 : v % 4 = 0 ∨ v % 4 = 1 ∨ v % 4 = 2 ∨ v % 4 = 3 := by omega
    rcases h4 with h | h | h | h
    · rw [if_pos (by omega), if_neg (by rw [Nat.even_iff]; omega), if_pos (by omega)]
      norm_num
    · have he : Odd ((v + 1) / 2) := by rw [Nat.odd_iff]; omega
      rw [if_pos (by omega), if_pos (by rw [Nat.even_iff]; omega), if_neg (by omega),
        he.neg_one_pow]
      norm_num
    · rw [if_neg (by omega), if_neg (by rw [Nat.even_iff]; omega), if_neg (by omega)]
      norm_num
    · have he : Even ((v + 1) / 2) := by rw [Nat.even_iff]; omega
      rw [if_neg (by omega), if_pos (by rw [Nat.even_iff]; omega), if_pos (by omega),
        he.neg_one_pow]
      norm_num

/-- The sign function as an arithmetic function. -/
def sgA : ArithmeticFunction ℤ := ⟨sg, by simp [sg]⟩

lemma sgA_mult : ArithmeticFunction.IsMultiplicative sgA := by
  refine ⟨sg_one, ?_⟩
  intro m n h
  show sg (m * n) = sg m * sg n
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [sg]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [sg]
  exact sg_mul m n h hm.ne' hn.ne'

/-- The sum of the signs of the divisors. -/
def S (n : ℕ) : ℤ := ∑ d ∈ n.divisors, sg d

lemma S_eq (n : ℕ) : S n = (sgA * (ArithmeticFunction.zeta : ArithmeticFunction ℤ)) n := by
  rw [ArithmeticFunction.coe_mul_zeta_apply]
  rfl

lemma S_01 (n : ℕ) : n ≠ 0 → (S n = 0 ∨ S n = 1) := by
  have hmult : ArithmeticFunction.IsMultiplicative
      (sgA * (ArithmeticFunction.zeta : ArithmeticFunction ℤ)) :=
    sgA_mult.mul ArithmeticFunction.isMultiplicative_zeta.natCast
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p v hp hv =>
    intro _
    have e : S (p ^ v) = ∑ i ∈ Finset.range (v + 1), w p i := by
      unfold S
      rw [Nat.sum_divisors_prime_pow hp]
      exact Finset.sum_congr rfl (fun i _ => sg_prime_pow p i hp)
    rw [e]
    by_cases h2 : p = 2
    · subst h2
      rw [wsum_two]
      split_ifs <;> simp
    · have e2 : ∑ i ∈ Finset.range (v + 1), w p i = ∑ i ∈ Finset.range (v + 1), ((-1 : ℤ)) ^ i :=
        Finset.sum_congr rfl (fun i _ => by unfold w; rw [if_neg h2])
      rw [e2, wsum_odd]
      split_ifs <;> simp
  | zero => exact fun h => absurd rfl h
  | one =>
    intro _
    right
    simp [S, sg_one]
  | coprime x y hx hy hc ihx ihy =>
    intro _
    have e : S (x * y) = S x * S y := by
      rw [S_eq, S_eq, S_eq]
      exact hmult.map_mul_of_coprime hc
    rw [e]
    rcases ihx (by omega) with h1 | h1 <;> rcases ihy (by omega) with h2 | h2 <;> simp [h1, h2]

theorem result (n : ℕ) (hn : 1 ≤ n) : a n = (b n + 1) / 2 := by
  have ha : (a n : ℤ) = ∑ d ∈ n.divisors, (if Even (f d).num then (1 : ℤ) else 0) := by
    unfold a
    rw [Finset.card_filter]
    push_cast
    exact Finset.sum_congr rfl (fun d _ => by split_ifs <;> rfl)
  have hb : (b n : ℤ) = ∑ d ∈ n.divisors, (if Even (padicValNat 2 d) then (1 : ℤ) else 0) := by
    unfold b
    push_cast
    rfl
  have hmain : 2 * (a n : ℤ) = (b n : ℤ) + S n := by
    rw [ha, hb, S, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    exact pointwise d (Nat.pos_of_mem_divisors hd).ne'
  rcases S_01 n (by omega) with h | h <;> rw [h] at hmain <;> omega

end OMA.A378444

theorem OMA.solution : type_of% @OMA.S_oeis_a378444.main :=
  fun n hn => OMA.A378444.result n hn
