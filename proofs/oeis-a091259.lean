import OMAStatements.S_oeis_a091259
import Mathlib

-- Problem: OEIS A091259, conjecture of Michel Marcus: the numerator a(n) of sigma_3(n)/sigma(n)
-- satisfies a(n) mod 3 = A353816(n), the indicator of the numbers x^2 + xy + y^2.
-- Statement: statements/oeis-a091259.lean (declaration OMA.S_oeis_a091259.main)
-- Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)
--
-- Proof. Let Cond(n) say: each prime p == 2 (mod 3) occurs to an even power in n.
-- Part 1 (n = x^2 + xy + y^2 if and only if Cond(n)). The form is multiplicative. A prime
-- p == 1 (mod 3) is represented (Thue: take s with s^2 + s + 1 == 0, and by the pigeonhole
-- principle a pair (a, b) with |a|, |b| <= sqrt(p) and a == s b; then a^2 + ab + b^2 is p or
-- 2p, and 2p is not possible by parity). 3 = 1 + 1 + 1 and p^2 = p^2 + 0 + 0. If p == 2
-- (mod 3) divides x^2 + xy + y^2, then p divides x and y, because t^2 + t + 1 has no root
-- modulo p; induction gives an even exponent.
-- Part 2. f(n) = sigma_3(n)/sigma(n) is the product over p^e || n of
-- (q^2 + q + 1)/(p^2 + p + 1) with q = p^(e+1). The 3-adic valuation of x^2 + x + 1 is 1 if
-- x == 1 (mod 3) and 0 otherwise. Thus the 3-adic valuation of f(n) is the number of primes
-- p == 2 (mod 3) with an odd exponent. If Cond(n) is false, 3 divides the numerator. If
-- Cond(n) is true, 3 does not divide the numerator; the numerator divides the product of the
-- numbers q^2 + q + 1, and each prime divisor r of x^2 + x + 1 is 3 or == 1 (mod 3) (x has
-- order 3 modulo r), thus the numerator is == 1 (mod 3).

namespace OMA.A091259

open Finset OMA.S_oeis_a091259

/-- n = x^2 + xy + y^2 with natural numbers x, y. -/
def Loe (n : ℕ) : Prop := ∃ x y : ℕ, n = x ^ 2 + x * y + y ^ 2

/-- n = x^2 + xy + y^2 with integers x, y. -/
def LoeZ (n : ℕ) : Prop := ∃ x y : ℤ, (n : ℤ) = x ^ 2 + x * y + y ^ 2

lemma loe_of_nonneg (n : ℕ) (x y : ℤ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : (n : ℤ) = x ^ 2 + x * y + y ^ 2) : Loe n := by
  lift x to ℕ using hx
  lift y to ℕ using hy
  exact ⟨x, y, by exact_mod_cast h⟩

lemma loe_of_loeZ (n : ℕ) (h : LoeZ n) : Loe n := by
  obtain ⟨x, y, h⟩ := h
  rcases le_total 0 x with hx | hx <;> rcases le_total 0 y with hy | hy
  · exact loe_of_nonneg n x y hx hy h
  · rcases le_total 0 (x + y) with hs | hs
    · exact loe_of_nonneg n (x + y) (-y) hs (by linarith) (by rw [h]; ring)
    · exact loe_of_nonneg n (-x - y) x (by linarith) hx (by rw [h]; ring)
  · rcases le_total 0 (x + y) with hs | hs
    · exact loe_of_nonneg n (-x) (x + y) (by linarith) hs (by rw [h]; ring)
    · exact loe_of_nonneg n y (-x - y) hy (by linarith) (by rw [h]; ring)
  · exact loe_of_nonneg n (-x) (-y) (by linarith) (by linarith) (by rw [h]; ring)

lemma loeZ_mul (m n : ℕ) (hm : LoeZ m) (hn : LoeZ n) : LoeZ (m * n) := by
  obtain ⟨a, b, hab⟩ := hm
  obtain ⟨c, d, hcd⟩ := hn
  refine ⟨a * c - b * d, a * d + b * c + b * d, ?_⟩
  push_cast
  rw [hab, hcd]; ring

lemma no_root (p : ℕ) [Fact p.Prime] (h : p % 3 = 2) (s : ZMod p) : s ^ 2 + s + 1 ≠ 0 := by
  have hp : p.Prime := Fact.out
  intro hs
  have h3 : s ^ 3 = 1 := by linear_combination (s - 1) * hs
  have h1 : s ≠ 1 := by
    rintro rfl
    have h30 : ((3 : ℕ) : ZMod p) = 0 := by push_cast; linear_combination hs
    rw [ZMod.natCast_eq_zero_iff] at h30
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h30
    omega
  have h0 : s ≠ 0 := by
    rintro rfl
    simp at h3
  have hord : orderOf s = 3 := orderOf_eq_prime h3 h1
  have hd := ZMod.orderOf_dvd_card_sub_one h0
  rw [hord] at hd
  have := hp.two_le
  omega

lemma root_of_prime (p : ℕ) [Fact p.Prime] (h : p % 3 = 1) : ∃ s : ZMod p, s ^ 2 + s + 1 = 0 := by
  have hp : p.Prime := Fact.out
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hord : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units]
  obtain ⟨t, ht⟩ : ∃ t, p - 1 = 3 * t := ⟨(p - 1) / 3, by omega⟩
  have ht0 : 0 < t := by have := hp.two_le; omega
  have h3 : ((g ^ t : (ZMod p)ˣ) : ZMod p) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← pow_mul, mul_comm, ← ht, ← hord, pow_orderOf_eq_one]; rfl
  have h1 : ((g ^ t : (ZMod p)ˣ) : ZMod p) ≠ 1 := by
    intro h1
    have h1' : g ^ t = 1 := Units.ext h1
    have hd := orderOf_dvd_of_pow_eq_one h1'
    rw [hord, ht] at hd
    have := Nat.le_of_dvd ht0 hd
    omega
  refine ⟨((g ^ t : (ZMod p)ˣ) : ZMod p), ?_⟩
  generalize ((g ^ t : (ZMod p)ˣ) : ZMod p) = s at h3 h1
  have hmul : (s - 1) * (s ^ 2 + s + 1) = 0 := by linear_combination h3
  rcases mul_eq_zero.1 hmul with h' | h'
  · exact absurd (sub_eq_zero.1 h') h1
  · exact h'

lemma thue_pair (p k : ℕ) [Fact p.Prime] (hk1 : p < (k + 1) * (k + 1)) (s : ZMod p) :
    ∃ a b : ℤ, ¬ (a = 0 ∧ b = 0) ∧ (-(k : ℤ) ≤ a ∧ a ≤ k) ∧ (-(k : ℤ) ≤ b ∧ b ≤ k) ∧
      ((a : ℤ) : ZMod p) = s * ((b : ℤ) : ZMod p) := by
  have hcard : (Finset.univ : Finset (ZMod p)).card
      < ((range (k + 1)) ×ˢ (range (k + 1))).card := by
    rw [Finset.card_univ, ZMod.card, card_product, card_range]; exact hk1
  obtain ⟨u, hu, v, hv, huv, hf⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard
    (f := fun w : ℕ × ℕ => ((w.1 : ZMod p)) - s * (w.2 : ZMod p)) (fun w _ => Finset.mem_univ _)
  rw [mem_product, mem_range, mem_range] at hu hv
  have hf' : (u.1 : ZMod p) - s * (u.2 : ZMod p) = (v.1 : ZMod p) - s * (v.2 : ZMod p) := hf
  refine ⟨(u.1 : ℤ) - v.1, (u.2 : ℤ) - v.2, ?_, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ?_⟩
  · rintro ⟨h1, h2⟩
    apply huv
    have e1 : u.1 = v.1 := by omega
    have e2 : u.2 = v.2 := by omega
    exact Prod.ext e1 e2
  · push_cast
    linear_combination hf'

lemma form_pos (a b : ℤ) (h : ¬ (a = 0 ∧ b = 0)) : 0 < a ^ 2 + a * b + b ^ 2 := by
  by_contra hneg
  apply h
  have h4 : (2 * a + b) ^ 2 + 3 * b ^ 2 = 4 * (a ^ 2 + a * b + b ^ 2) := by ring
  have hb2 : b ^ 2 ≤ 0 := by linarith [sq_nonneg (2 * a + b)]
  have hb0 : b = 0 := (pow_eq_zero_iff two_ne_zero).1 (le_antisymm hb2 (sq_nonneg b))
  have ha2 : (2 * a + b) ^ 2 ≤ 0 := by linarith [sq_nonneg b]
  have ha0 : 2 * a + b = 0 := (pow_eq_zero_iff two_ne_zero).1 (le_antisymm ha2 (sq_nonneg _))
  exact ⟨by omega, hb0⟩

lemma form_parity (a b P : ℤ) (h : a ^ 2 + a * b + b ^ 2 = P * 2) : ∃ Y : ℤ, P = 2 * Y := by
  obtain ⟨a', ha' | ha'⟩ := Int.even_or_odd' a <;> obtain ⟨b', hb' | hb'⟩ := Int.even_or_odd' b
  · exact ⟨a' ^ 2 + a' * b' + b' ^ 2, by rw [ha', hb'] at h; linarith⟩
  · exfalso
    have e : 2 * (2 * a' ^ 2 + 2 * a' * b' + a' + 2 * b' ^ 2 + 2 * b') + 1 = P * 2 := by
      rw [ha', hb'] at h; linarith
    omega
  · exfalso
    have e : 2 * (2 * a' ^ 2 + 2 * a' + 2 * a' * b' + b' + 2 * b' ^ 2) + 1 = P * 2 := by
      rw [ha', hb'] at h; linarith
    omega
  · exfalso
    have e : 2 * (2 * a' ^ 2 + 3 * a' + 2 * a' * b' + 3 * b' + 2 * b' ^ 2 + 1) + 1 = P * 2 := by
      rw [ha', hb'] at h; linarith
    omega

lemma form_bound (a b K : ℤ) (ha : -K ≤ a ∧ a ≤ K) (hb : -K ≤ b ∧ b ≤ K) :
    a ^ 2 + a * b + b ^ 2 ≤ 3 * (K * K) := by
  have h1 : a ^ 2 ≤ K * K := by nlinarith
  have h2 : b ^ 2 ≤ K * K := by nlinarith
  have h3 : a * b ≤ K * K := by nlinarith
  linarith

/-- Thue's argument: a prime p ≡ 1 (mod 3) is of the form x^2 + xy + y^2. -/
lemma prime_loeZ (p : ℕ) [Fact p.Prime] (h : p % 3 = 1) : LoeZ p := by
  have hp : p.Prime := Fact.out
  obtain ⟨s, hs⟩ := root_of_prime p h
  have hk1 : p < (Nat.sqrt p + 1) * (Nat.sqrt p + 1) := Nat.lt_succ_sqrt p
  have hk2 : Nat.sqrt p * Nat.sqrt p ≤ p := Nat.sqrt_le p
  generalize Nat.sqrt p = k at hk1 hk2
  have hk3 : k * k < p := by
    rcases Nat.lt_or_ge (k * k) p with h' | h'
    · exact h'
    · exfalso
      have e : p = k * k := le_antisymm h' hk2
      have hdv : k ∣ p := ⟨k, e⟩
      rcases (Nat.dvd_prime hp).1 hdv with h1 | h1
      · rw [h1] at e; have := hp.two_le; omega
      · rw [h1] at e; have := hp.two_le; nlinarith
  obtain ⟨a, b, hab0, habs_a, habs_b, hcong⟩ := thue_pair p k hk1 s
  have hdiv : (p : ℤ) ∣ a ^ 2 + a * b + b ^ 2 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1
    push_cast
    rw [hcong]
    linear_combination ((b : ZMod p)) ^ 2 * hs
  have hkz : (k : ℤ) * k < p := by exact_mod_cast hk3
  have hpos := form_pos a b hab0
  have hup := form_bound a b k habs_a habs_b
  obtain ⟨m, hm⟩ := hdiv
  have hpz : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have hm1 : 0 < m := by
    by_contra hneg
    have : (p : ℤ) * m ≤ 0 := by nlinarith
    linarith
  have hm3 : m < 3 := by
    by_contra hge
    have : (p : ℤ) * 3 ≤ p * m := by nlinarith
    linarith
  have hm12 : m = 1 ∨ m = 2 := by omega
  rcases hm12 with rfl | rfl
  · exact ⟨a, b, by rw [hm]; ring⟩
  · exfalso
    obtain ⟨Y, hY⟩ := form_parity a b p hm
    have hpe : p % 2 = 0 := by omega
    rcases hp.eq_two_or_odd with h2 | h2 <;> omega

/-- Each prime p ≡ 2 (mod 3) occurs to an even power in n. -/
def Cond (n : ℕ) : Prop := ∀ p : ℕ, p.Prime → p % 3 = 2 → Even (n.factorization p)

lemma cond_mul_of_ne (p m : ℕ) (hp : p.Prime) (hm : m ≠ 0) (hp3 : p % 3 ≠ 2)
    (h : Cond (p * m)) : Cond m := by
  intro q hq hq3
  have h1 := h q hq hq3
  rw [Nat.factorization_mul hp.ne_zero hm] at h1
  have hne : p ≠ q := by rintro rfl; exact hp3 hq3
  have h0 : p.factorization q = 0 := by
    rw [hp.factorization, Finsupp.single_apply, if_neg hne]
  rw [Finsupp.add_apply, h0, zero_add] at h1
  exact h1

lemma cond_sq (p m : ℕ) (hp : p.Prime) (hm : m ≠ 0) (h : Cond (p ^ 2 * m)) : Cond m := by
  intro q hq hq3
  have h1 := h q hq hq3
  rw [Nat.factorization_mul (pow_ne_zero 2 hp.ne_zero) hm, Nat.factorization_pow,
    Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at h1
  exact (Nat.even_add.1 h1).1 (even_two_mul _)

lemma loeZ_of_cond : ∀ n : ℕ, 1 ≤ n → Cond n → LoeZ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn hc
    by_cases h1 : n = 1
    · subst h1; exact ⟨1, 0, by norm_num⟩
    · have hp : n.minFac.Prime := Nat.minFac_prime h1
      have hpn : n.minFac ∣ n := Nat.minFac_dvd n
      generalize n.minFac = p at hp hpn
      have hfact : Fact p.Prime := ⟨hp⟩
      by_cases hp3 : p % 3 = 2
      · have hev := hc p hp hp3
        have hpos : 0 < n.factorization p := hp.factorization_pos_of_dvd (by omega) hpn
        have h2 : 2 ≤ n.factorization p := by obtain ⟨t, ht⟩ := hev; omega
        obtain ⟨m, rfl⟩ : p ^ 2 ∣ n := (hp.pow_dvd_iff_le_factorization (by omega)).2 h2
        have hm0 : m ≠ 0 := by rintro rfl; simp at hn
        have hlt : m < p ^ 2 * m := by
          have h4 : 4 ≤ p ^ 2 := by have := hp.two_le; nlinarith
          have hmp := Nat.pos_of_ne_zero hm0
          exact Nat.lt_of_lt_of_le (by omega : m < 4 * m) (Nat.mul_le_mul_right m h4)
        have hLm := ih m hlt (Nat.pos_of_ne_zero hm0) (cond_sq p m hp hm0 hc)
        exact loeZ_mul _ _ ⟨p, 0, by push_cast; ring⟩ hLm
      · obtain ⟨m, rfl⟩ := hpn
        have hm0 : m ≠ 0 := by rintro rfl; simp at hn
        have hlt : m < p * m := by
          have := hp.two_le
          nlinarith [Nat.pos_of_ne_zero hm0]
        have hLm := ih m hlt (Nat.pos_of_ne_zero hm0) (cond_mul_of_ne p m hp hm0 hp3 hc)
        have hLp : LoeZ p := by
          by_cases h31 : p % 3 = 1
          · exact prime_loeZ p h31
          · have h3 : 3 = p :=
              (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 (Nat.dvd_of_mod_eq_zero (by omega))
            subst h3
            exact ⟨1, 1, by norm_num⟩
        exact loeZ_mul _ _ hLp hLm

lemma dvd_both (p x y : ℕ) [Fact p.Prime] (hp3 : p % 3 = 2) (h : p ∣ x ^ 2 + x * y + y ^ 2) :
    p ∣ x ∧ p ∣ y := by
  have h0 : ((x : ZMod p)) ^ 2 + (x : ZMod p) * (y : ZMod p) + (y : ZMod p) ^ 2 = 0 := by
    have := (ZMod.natCast_eq_zero_iff _ p).2 h
    push_cast at this
    exact this
  have hy : (y : ZMod p) = 0 := by
    by_contra hy
    apply no_root p hp3 ((x : ZMod p) * (y : ZMod p)⁻¹)
    field_simp
    linear_combination h0
  have hx : (x : ZMod p) = 0 := by
    rw [hy] at h0
    have : (x : ZMod p) ^ 2 = 0 := by linear_combination h0
    exact (pow_eq_zero_iff two_ne_zero).1 this
  exact ⟨(ZMod.natCast_eq_zero_iff x p).1 hx, (ZMod.natCast_eq_zero_iff y p).1 hy⟩

lemma cond_of_loe : ∀ n : ℕ, 1 ≤ n → Loe n → Cond n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rintro hn ⟨x, y, hxy⟩ p hp hp3
    by_cases hpn : p ∣ n
    · have hfact : Fact p.Prime := ⟨hp⟩
      obtain ⟨⟨x', rfl⟩, ⟨y', rfl⟩⟩ := dvd_both p x y hp3 (hxy ▸ hpn)
      have e : n = p ^ 2 * (x' ^ 2 + x' * y' + y' ^ 2) := by rw [hxy]; ring
      have hn0 : x' ^ 2 + x' * y' + y' ^ 2 ≠ 0 := by
        intro h0; rw [h0] at e; omega
      have hlt : x' ^ 2 + x' * y' + y' ^ 2 < n := by
        rw [e]
        have h4 : 4 ≤ p ^ 2 := by have := hp.two_le; nlinarith
        have hmp := Nat.pos_of_ne_zero hn0
        exact Nat.lt_of_lt_of_le (by omega) (Nat.mul_le_mul_right _ h4)
      have hc := ih _ hlt (Nat.pos_of_ne_zero hn0) ⟨x', y', rfl⟩ p hp hp3
      rw [e, Nat.factorization_mul (pow_ne_zero 2 hp.ne_zero) hn0, Nat.factorization_pow,
        Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
      exact Even.add (even_two_mul _) hc
    · rw [Nat.factorization_eq_zero_of_not_dvd hpn]; exact ⟨0, rfl⟩

/-- The ratio sigma_3(n)/sigma(n). -/
def f (n : ℕ) : ℚ :=
  (ArithmeticFunction.sigma 3 n : ℚ) / (ArithmeticFunction.sigma 1 n : ℚ)

lemma f_one : f 1 = 1 := by
  unfold f
  simp

lemma f_mul (x y : ℕ) (h : Nat.Coprime x y) : f (x * y) = f x * f y := by
  unfold f
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime h,
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime h]
  push_cast
  rw [mul_div_mul_comm]

lemma f_pos (n : ℕ) (hn : n ≠ 0) : 0 < f n := by
  unfold f
  have h3 := ArithmeticFunction.sigma_pos 3 n hn
  have h1 := ArithmeticFunction.sigma_pos 1 n hn
  positivity

lemma f_prime_pow (p e : ℕ) (hp : p.Prime) :
    f (p ^ e) = (((p ^ (e + 1)) ^ 2 + p ^ (e + 1) + 1 : ℕ) : ℚ) / ((p ^ 2 + p + 1 : ℕ) : ℚ) := by
  unfold f
  rw [ArithmeticFunction.sigma_apply_prime_pow hp, ArithmeticFunction.sigma_apply_prime_pow hp]
  have hp1 : (p : ℚ) - 1 ≠ 0 := by
    have : (1 : ℚ) < p := by exact_mod_cast hp.one_lt
    linarith
  have g1 : (∑ j ∈ range (e + 1), (p : ℚ) ^ j) * ((p : ℚ) - 1) = (p : ℚ) ^ (e + 1) - 1 :=
    geom_sum_mul _ _
  have g3 : (∑ j ∈ range (e + 1), ((p : ℚ) ^ 3) ^ j) * ((p : ℚ) ^ 3 - 1)
      = ((p : ℚ) ^ 3) ^ (e + 1) - 1 := geom_sum_mul _ _
  have e3 : ((p : ℚ) ^ 3) ^ (e + 1) = ((p : ℚ) ^ (e + 1)) ^ 3 := by
    rw [← pow_mul, ← pow_mul, mul_comm]
  have c1 : ((∑ j ∈ range (e + 1), p ^ (j * 1) : ℕ) : ℚ) = ∑ j ∈ range (e + 1), (p : ℚ) ^ j := by
    push_cast
    apply sum_congr rfl
    intro j _
    rw [mul_one]
  have c3 : ((∑ j ∈ range (e + 1), p ^ (j * 3) : ℕ) : ℚ)
      = ∑ j ∈ range (e + 1), ((p : ℚ) ^ 3) ^ j := by
    push_cast
    apply sum_congr rfl
    intro j _
    rw [← pow_mul, mul_comm]
  rw [c1, c3]
  have hB : ((p ^ 2 + p + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have hG1 : (∑ j ∈ range (e + 1), (p : ℚ) ^ j) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at g1
    have : (1 : ℚ) < (p : ℚ) ^ (e + 1) := one_lt_pow₀ (by exact_mod_cast hp.one_lt) (by omega)
    linarith
  rw [div_eq_div_iff hG1 hB]
  push_cast
  apply mul_right_cancel₀ hp1
  rw [e3] at g3
  generalize (∑ j ∈ range (e + 1), (p : ℚ) ^ j) = G1 at g1 ⊢
  generalize (∑ j ∈ range (e + 1), ((p : ℚ) ^ 3) ^ j) = G3 at g3 ⊢
  generalize (p : ℚ) ^ (e + 1) = q at g1 g3 ⊢
  linear_combination g3 - (q ^ 2 + q + 1) * g1

lemma f_factorization (n : ℕ) (hn : n ≠ 0) :
    f n = ∏ p ∈ n.primeFactors, f (p ^ n.factorization p) := by
  have h := Nat.multiplicative_factorization f f_mul f_one hn
  rw [h, Finsupp.prod, Nat.support_factorization]

lemma val3 (x : ℕ) : padicValNat 3 (x ^ 2 + x + 1) = if x % 3 = 1 then 1 else 0 := by
  have hm : (x ^ 2 + x + 1) % 3 = ((x % 3) ^ 2 + x % 3 + 1) % 3 := by
    simp [Nat.add_mod, Nat.pow_mod]
  have hlt : x % 3 < 3 := Nat.mod_lt _ (by norm_num)
  by_cases h1 : x % 3 = 1
  · rw [if_pos h1]
    obtain ⟨t, rfl⟩ : ∃ t, x = 3 * t + 1 := ⟨x / 3, by omega⟩
    have e : (3 * t + 1) ^ 2 + (3 * t + 1) + 1 = 3 * (3 * t ^ 2 + 3 * t + 1) := by ring
    rw [e, padicValNat.mul (by norm_num) (by omega), padicValNat_self,
      padicValNat.eq_zero_of_not_dvd (by omega)]
  · rw [if_neg h1]
    apply padicValNat.eq_zero_of_not_dvd
    intro hd
    have h0 := Nat.mod_eq_zero_of_dvd hd
    rw [hm] at h0
    interval_cases (x % 3) <;> simp_all

lemma two_pow_mod (k : ℕ) : 2 ^ k % 3 = if Even k then 1 else 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Nat.mul_mod, ih]
    by_cases hk : Even k
    · rw [if_pos hk, if_neg (by rw [Nat.even_add_one]; exact not_not.2 hk)]
    · rw [if_neg hk, if_pos (by rw [Nat.even_add_one]; exact hk)]

lemma val_f (p e : ℕ) (hp : p.Prime) :
    padicValRat 3 (f (p ^ e)) = if p % 3 = 2 ∧ Odd e then 1 else 0 := by
  rw [f_prime_pow p e hp, padicValRat.div (by positivity) (by positivity), padicValRat.of_nat,
    padicValRat.of_nat, val3, val3]
  have hq : p ^ (e + 1) % 3 = (p % 3) ^ (e + 1) % 3 := Nat.pow_mod _ _ _
  have hlt : p % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have h2 := two_pow_mod (e + 1)
  rw [hq]
  interval_cases hp3 : (p % 3)
  · simp
  · simp
  · rw [h2]
    by_cases he : Odd e
    · have he1 : Even (e + 1) := by rw [Nat.even_add_one, Nat.not_even_iff_odd]; exact he
      simp [he, he1]
    · have he1 : ¬ Even (e + 1) := by
        rw [Nat.even_add_one, not_not, ← Nat.not_odd_iff_even]; exact he
      simp [he, he1]

lemma padic_prod (s : Finset ℕ) (g : ℕ → ℚ) (hg : ∀ p ∈ s, g p ≠ 0) :
    padicValRat 3 (∏ p ∈ s, g p) = ∑ p ∈ s, padicValRat 3 (g p) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha, sum_insert ha,
      padicValRat.mul (hg a (mem_insert_self a s))
        (prod_ne_zero_iff.2 (fun p hp => hg p (mem_insert_of_mem hp))),
      ih (fun p hp => hg p (mem_insert_of_mem hp))]

lemma val_sum (n : ℕ) (hn : n ≠ 0) :
    padicValRat 3 (f n)
      = ∑ p ∈ n.primeFactors, (if p % 3 = 2 ∧ Odd (n.factorization p) then (1 : ℤ) else 0) := by
  rw [f_factorization n hn, padic_prod]
  · apply sum_congr rfl
    intro p hp
    exact val_f p _ (Nat.prime_of_mem_primeFactors hp)
  · intro p hp
    exact (f_pos _ (pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero)).ne'

lemma prime_dvd_form (r x : ℕ) (hr : r.Prime) (h : r ∣ x ^ 2 + x + 1) : r = 3 ∨ r % 3 = 1 := by
  have hlt : r % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have hcases : r % 3 = 0 ∨ r % 3 = 1 ∨ r % 3 = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · left
    exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hr).1 (Nat.dvd_of_mod_eq_zero h0)).symm
  · right; exact h1
  · exfalso
    have hfact : Fact r.Prime := ⟨hr⟩
    apply no_root r h2 (x : ZMod r)
    have := (ZMod.natCast_eq_zero_iff _ r).2 h
    push_cast at this
    exact this

lemma num_dvd_prod (n : ℕ) (hn : n ≠ 0) :
    (f n).num ∣ ((∏ p ∈ n.primeFactors,
      ((p ^ (n.factorization p + 1)) ^ 2 + p ^ (n.factorization p + 1) + 1) : ℕ) : ℤ) := by
  have h : f n = Rat.divInt ((∏ p ∈ n.primeFactors,
      ((p ^ (n.factorization p + 1)) ^ 2 + p ^ (n.factorization p + 1) + 1) : ℕ) : ℤ)
      ((∏ p ∈ n.primeFactors, (p ^ 2 + p + 1) : ℕ) : ℤ) := by
    rw [Rat.divInt_eq_div, f_factorization n hn]
    push_cast
    rw [← prod_div_distrib]
    apply prod_congr rfl
    intro p hp
    rw [f_prime_pow p _ (Nat.prime_of_mem_primeFactors hp)]
    push_cast
    rfl
  rw [h]
  apply Rat.num_dvd
  have : 0 < ∏ p ∈ n.primeFactors, (p ^ 2 + p + 1) := prod_pos (fun p _ => by positivity)
  exact_mod_cast this.ne'

lemma mod3_one : ∀ m : ℕ, 0 < m → (∀ r : ℕ, r.Prime → r ∣ m → r % 3 = 1) → m % 3 = 1 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm h
    by_cases h1 : m = 1
    · subst h1; rfl
    · have hp : m.minFac.Prime := Nat.minFac_prime h1
      have hr := h _ hp (Nat.minFac_dvd m)
      obtain ⟨m', hm'⟩ := Nat.minFac_dvd m
      generalize m.minFac = p at hp hr hm'
      have hm'0 : 0 < m' := by
        rcases Nat.eq_zero_or_pos m' with h0 | h0
        · rw [h0] at hm'; omega
        · exact h0
      have hlt : m' < m := by
        have := hp.two_le
        rw [hm']; nlinarith
      have ih' := ih m' hlt hm'0
        (fun r hr' hd => h r hr' (Dvd.dvd.trans hd (Dvd.intro_left p hm'.symm)))
      rw [hm', Nat.mul_mod, hr, ih']

theorem main' (n : ℕ) (hn : 1 ≤ n) : a n % 3 = c n := by
  have hn0 : n ≠ 0 := by omega
  have hfact3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have haN : a n = (f n).num := rfl
  have hNpos : 0 < (f n).num := Rat.num_pos.2 (f_pos n hn0)
  have hval := val_sum n hn0
  have hred := (f n).reduced
  have hvdef : padicValRat 3 (f n)
      = (padicValNat 3 (f n).num.natAbs : ℤ) - (padicValNat 3 (f n).den : ℤ) := rfl
  by_cases hc : Cond n
  · -- all terms of the sum are zero
    have hzero : padicValRat 3 (f n) = 0 := by
      rw [hval]
      apply sum_eq_zero
      intro p hp
      rw [if_neg]
      rintro ⟨h2, hodd⟩
      exact (Nat.not_even_iff_odd.2 hodd) (hc p (Nat.prime_of_mem_primeFactors hp) h2)
    have h3 : ¬ 3 ∣ (f n).num.natAbs := by
      intro hd
      have h1 : 1 ≤ padicValNat 3 (f n).num.natAbs :=
        one_le_padicValNat_of_dvd (by omega) hd
      have h2 : padicValNat 3 (f n).den = 0 := by
        apply padicValNat.eq_zero_of_not_dvd
        intro hd2
        have := Nat.dvd_gcd hd hd2
        rw [Nat.Coprime] at hred
        rw [hred] at this
        omega
      rw [hvdef, h2] at hzero
      omega
    have hmod : (f n).num.natAbs % 3 = 1 := by
      apply mod3_one _ (by omega)
      intro r hr hd
      have hdz : (r : ℤ) ∣ (f n).num := Int.natCast_dvd.2 hd
      have hd2 := Dvd.dvd.trans hdz (num_dvd_prod n hn0)
      have hd3 : r ∣ ∏ p ∈ n.primeFactors,
          ((p ^ (n.factorization p + 1)) ^ 2 + p ^ (n.factorization p + 1) + 1) :=
        Int.natCast_dvd_natCast.1 hd2
      obtain ⟨p, _, hp⟩ := (Prime.dvd_finsetProd_iff (Nat.prime_iff.1 hr) _).1 hd3
      rcases prime_dvd_form r _ hr hp with h | h
      · exfalso; rw [h] at hd; exact h3 hd
      · exact h
    have hL : ∃ x y : ℕ, n = x ^ 2 + x * y + y ^ 2 := loe_of_loeZ n (loeZ_of_cond n hn hc)
    unfold c
    rw [if_pos hL, haN]
    omega
  · -- one term of the sum is one
    have hex : ∃ p : ℕ, p.Prime ∧ p % 3 = 2 ∧ ¬ Even (n.factorization p) := by
      by_contra hne
      apply hc
      intro p hp h2
      by_contra hev
      exact hne ⟨p, hp, h2, hev⟩
    obtain ⟨p, hp, h2, hev⟩ := hex
    have hpm : p ∈ n.primeFactors := by
      rw [Nat.mem_primeFactors]
      refine ⟨hp, Nat.dvd_of_factorization_pos ?_, hn0⟩
      intro h0; rw [h0] at hev; exact hev ⟨0, rfl⟩
    have hge : (1 : ℤ) ≤ padicValRat 3 (f n) := by
      rw [hval]
      have hs := single_le_sum
        (f := fun p => if p % 3 = 2 ∧ Odd (n.factorization p) then (1 : ℤ) else 0)
        (fun q _ => by positivity) hpm
      rw [if_pos ⟨h2, Nat.not_even_iff_odd.1 hev⟩] at hs
      exact hs
    have h3 : 3 ∣ (f n).num.natAbs := by
      by_contra hnd
      have h0 : padicValNat 3 (f n).num.natAbs = 0 := padicValNat.eq_zero_of_not_dvd hnd
      rw [hvdef, h0] at hge
      omega
    have hL : ¬ ∃ x y : ℕ, n = x ^ 2 + x * y + y ^ 2 := fun hL => hc (cond_of_loe n hn hL)
    unfold c
    rw [if_neg hL, haN]
    omega

end OMA.A091259

theorem OMA.solution : type_of% @OMA.S_oeis_a091259.main :=
  fun n hn => OMA.A091259.main' n hn
