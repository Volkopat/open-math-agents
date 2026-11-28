import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H3_R1

-- Reduction Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H3.R1.H4.R1
-- Credit: @adammcarter
-- Splits step H4 of Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H3.R1 (3 does not divide n, at least two
-- repeated odd primes, S not admissible) by the 2-adic valuation of a, with a lower bound on a
-- built in.  Proving the three H proves the step.
--
-- Notation: n unitary perfect, a = padicValNat 2 n, e(q) = n.factorization q, S = the repeated odd
-- primes.  The parent gives: a even, every simple odd prime is 1 mod 3, every prime 2 mod 3 of n
-- has even exponent (so it is repeated), some z in S with z = 2 mod 3 divides 2^a + 1, and the
-- Fermat primes 5, 17, 257, 65537 are in S when a = 2 mod 4, 4 mod 8, 8 mod 16, 16 mod 32.
--
-- PROVED BELOW, no hypothesis needed (lower_bound): if 3 does not divide n then a >= 125
-- (so a >= 126, a being even).  This is a weaker form of a theorem of H. A. M. Frei (Elem. Math.
-- 33 (1978), as quoted by OEIS A002827: a unitary perfect number prime to 3 has a >= 144).
-- Proof (a counting and weight argument):
--   (W) the product over the odd primes q of n of (1 + 1/q^e(q)) is 2 / (1 + 1/2^a);
--   every odd q of n is 1 mod 3 (factor at most 1 + 1/q) or 2 mod 3 with exponent >= 2
--   (factor at most 1 + 1/q^2);
--   the 2 mod 3 part is at most C = prod over u = 5 mod 6, u < 300, of (1 + 1/u^2), times
--   1 + 1/600 for the tail (telescoping: 1 + 1/u^2 <= (1 + 1/(2u)) / (1 + 1/(2u + 12)));
--   the 1 mod 3 part is at most the product of (1 + 1/p) over the first k primes p = 1 mod 3,
--   k = their number, and k <= a because n has at most a + 1 odd primes and z is one of them;
--   the product over the first 124 primes p = 1 mod 3 (up to 1669) times C is below 2048/1025,
--   and over the first 8 below 8/5; so (W) fails for 2 <= a <= 124.
--
-- ALSO PROVED (source_of_repeated, any n): every repeated odd prime z gets its factors of z from
-- the balance product, so z^2 divides 2^a + 1 or some odd prime q of n other than z has
-- z | 1 + q^e(q).  For the Fermat prime f of the class (5 when a = 2 mod 4, 17 when a = 4 mod 8)
-- this reads: f divides a (v_f(2^a + 1) = 1 + v_f(a)) or f has a second source.
--
-- H1 (OPEN): a = 2 mod 4 (then 5 is a repeated prime), a >= 125, with the parent conditions.
-- H2 (OPEN): a = 4 mod 8 (then 17 is a repeated prime), a >= 125, with the parent conditions.
-- H3 (OPEN): 8 | a, a >= 125, with the parent conditions (257 in S if a = 8 mod 16, 65537 in S
--    if a = 16 mod 32).
-- No known unitary perfect number has two repeated odd primes or is prime to 3.

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H3_R1_H4_R1

open OMA.R_Erdos1052_erdos_1052_R1 (card_odd_primeFactors_le)
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1 (prod_eq_two_mul prod_primeFactors_pow_self
  two_dvd_of_isUnitaryPerfect)
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H3_R1 (branch_none fact2_eq fact_pos)

-- H1: 3 does not divide n, a = 2 mod 4 (5 is repeated), a >= 125.
def H1 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    ∀ S : Finset ℕ, (∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) → 2 ≤ S.card →
    ¬ ((∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z) ∧
      ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097) →
    ¬ 3 ∣ n → padicValNat 2 n % 2 = 0 → 125 ≤ padicValNat 2 n →
    (∀ p ∈ n.primeFactors, p ≠ 2 → n.factorization p = 1 → p % 3 = 1) →
    (∀ q ∈ n.primeFactors, q % 3 = 2 → n.factorization q % 2 = 0) →
    (∃ z ∈ S, z % 3 = 2 ∧ z ∣ 2 ^ padicValNat 2 n + 1) →
    n.primeFactors.card % 2 = 1 →
    (∀ z ∈ S, z ^ 2 ∣ 2 ^ padicValNat 2 n + 1 ∨
      ∃ q ∈ n.primeFactors, q ≠ 2 ∧ q ≠ z ∧ z ∣ 1 + q ^ n.factorization q) →
    padicValNat 2 n % 4 = 2 → 5 ∈ S →
    padicValNat 2 n ≤ A

-- H2: 3 does not divide n, a = 4 mod 8 (17 is repeated), a >= 125.
def H2 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    ∀ S : Finset ℕ, (∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) → 2 ≤ S.card →
    ¬ ((∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z) ∧
      ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097) →
    ¬ 3 ∣ n → padicValNat 2 n % 2 = 0 → 125 ≤ padicValNat 2 n →
    (∀ p ∈ n.primeFactors, p ≠ 2 → n.factorization p = 1 → p % 3 = 1) →
    (∀ q ∈ n.primeFactors, q % 3 = 2 → n.factorization q % 2 = 0) →
    (∃ z ∈ S, z % 3 = 2 ∧ z ∣ 2 ^ padicValNat 2 n + 1) →
    n.primeFactors.card % 2 = 1 →
    (∀ z ∈ S, z ^ 2 ∣ 2 ^ padicValNat 2 n + 1 ∨
      ∃ q ∈ n.primeFactors, q ≠ 2 ∧ q ≠ z ∧ z ∣ 1 + q ^ n.factorization q) →
    padicValNat 2 n % 8 = 4 → 17 ∈ S →
    padicValNat 2 n ≤ A

-- H3: 3 does not divide n, 8 divides a, a >= 125.
def H3 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    ∀ S : Finset ℕ, (∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) → 2 ≤ S.card →
    ¬ ((∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z) ∧
      ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097) →
    ¬ 3 ∣ n → padicValNat 2 n % 2 = 0 → 125 ≤ padicValNat 2 n →
    (∀ p ∈ n.primeFactors, p ≠ 2 → n.factorization p = 1 → p % 3 = 1) →
    (∀ q ∈ n.primeFactors, q % 3 = 2 → n.factorization q % 2 = 0) →
    (∃ z ∈ S, z % 3 = 2 ∧ z ∣ 2 ^ padicValNat 2 n + 1) →
    n.primeFactors.card % 2 = 1 →
    (∀ z ∈ S, z ^ 2 ∣ 2 ^ padicValNat 2 n + 1 ∨
      ∃ q ∈ n.primeFactors, q ≠ 2 ∧ q ≠ z ∧ z ∣ 1 + q ^ n.factorization q) →
    padicValNat 2 n % 8 = 0 → (padicValNat 2 n % 16 = 8 → 257 ∈ S) →
    (padicValNat 2 n % 32 = 16 → 65537 ∈ S) →
    padicValNat 2 n ≤ A

-- Section 1. The weight identity.

theorem weight_eq {n : ℕ} (h : Erdos1052.IsUnitaryPerfect n) :
    (1 + 1 / (2 : ℚ) ^ n.factorization 2) *
      ∏ q ∈ n.primeFactors.erase 2, (1 + 1 / (q : ℚ) ^ n.factorization q) = 2 := by
  have hn : n ≠ 0 := h.2.ne'
  have h2pf : 2 ∈ n.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_two, two_dvd_of_isUnitaryPerfect h, hn⟩
  have hE : ((∏ p ∈ n.primeFactors, (1 + p ^ n.factorization p) : ℕ) : ℚ) = 2 * (n : ℚ) := by
    exact_mod_cast prod_eq_two_mul h
  have hN : ((∏ p ∈ n.primeFactors, p ^ n.factorization p : ℕ) : ℚ) = (n : ℚ) := by
    exact_mod_cast prod_primeFactors_pow_self hn
  push_cast at hE hN
  have hpos : ∀ p ∈ n.primeFactors, ((p : ℚ) ^ n.factorization p) ≠ 0 := fun p hp =>
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero)
  have hn' : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have key : ∏ p ∈ n.primeFactors, (1 + 1 / (p : ℚ) ^ n.factorization p) = 2 := by
    calc ∏ p ∈ n.primeFactors, (1 + 1 / (p : ℚ) ^ n.factorization p)
        = ∏ p ∈ n.primeFactors, ((1 + (p : ℚ) ^ n.factorization p) / (p : ℚ) ^ n.factorization p) :=
          Finset.prod_congr rfl fun p hp => by rw [add_div, div_self (hpos p hp), add_comm]
      _ = (∏ p ∈ n.primeFactors, (1 + (p : ℚ) ^ n.factorization p)) /
            ∏ p ∈ n.primeFactors, (p : ℚ) ^ n.factorization p := by rw [Finset.prod_div_distrib]
      _ = 2 := by rw [hE, hN, mul_div_assoc, div_self hn', mul_one]
  rwa [← Finset.mul_prod_erase _ _ h2pf] at key

theorem factor_le_one {q e : ℕ} (hq : 1 ≤ q) (he : 1 ≤ e) :
    1 + 1 / (q : ℚ) ^ e ≤ 1 + 1 / (q : ℚ) := by
  have h1 : (q : ℚ) ≤ (q : ℚ) ^ e := by
    have : q ≤ q ^ e := Nat.le_self_pow (by omega) q
    exact_mod_cast this
  have h0 : (0 : ℚ) < q := by exact_mod_cast hq
  have := one_div_le_one_div_of_le h0 h1
  linarith

theorem factor_le_two {q e : ℕ} (hq : 1 ≤ q) (he : 2 ≤ e) :
    1 + 1 / (q : ℚ) ^ e ≤ 1 + 1 / (q : ℚ) ^ 2 := by
  have h1 : (q : ℚ) ^ 2 ≤ (q : ℚ) ^ e := by
    have : q ^ 2 ≤ q ^ e := Nat.pow_le_pow_right (by omega) he
    exact_mod_cast this
  have h0 : (0 : ℚ) < (q : ℚ) ^ 2 := pow_pos (by exact_mod_cast hq) 2
  have := one_div_le_one_div_of_le h0 h1
  linarith

-- Section 2. Products of 1 + 1/u^2 over u = 5 mod 6.

theorem one_le_prod_rat (s : Finset ℕ) (f : ℕ → ℚ) (hf : ∀ i ∈ s, 1 ≤ f i) : 1 ≤ ∏ i ∈ s, f i := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has ih =>
    rw [Finset.prod_insert has]
    exact one_le_mul_of_one_le_of_one_le (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem prod_le_of_subset_rat {s t : Finset ℕ} (f : ℕ → ℚ) (hst : s ⊆ t) (hf : ∀ i ∈ t, 1 ≤ f i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ t, f i := by
  rw [← Finset.prod_sdiff hst]
  have h0 : 0 ≤ ∏ i ∈ s, f i :=
    le_trans zero_le_one (one_le_prod_rat s f fun i hi => hf i (hst hi))
  have h1 := one_le_prod_rat (t \ s) f fun i hi => hf i (Finset.mem_sdiff.mp hi).1
  nlinarith

theorem tele_step {x : ℚ} (hx : 5 ≤ x) :
    (1 + 1 / x ^ 2) * (1 + 1 / (2 * (x + 6))) ≤ 1 + 1 / (2 * x) := by
  have hx0 : 0 < x := by linarith
  have e : (1 + 1 / x ^ 2) * (1 + 1 / (2 * (x + 6))) =
      1 + 1 / (2 * x) - (4 * x - 13) / (x ^ 2 * (2 * x + 12)) := by
    field_simp
    ring
  rw [e]
  have : 0 ≤ (4 * x - 13) / (x ^ 2 * (2 * x + 12)) := div_nonneg (by linarith) (by positivity)
  linarith

theorem tele (T : Finset ℕ) : ∀ Y : ℕ, 5 ≤ Y → (∀ u ∈ T, u % 6 = 5 ∧ Y ≤ u) →
    ∏ u ∈ T, (1 + 1 / (u : ℚ) ^ 2) ≤ 1 + 1 / (2 * (Y : ℚ)) := by
  induction T using Finset.induction_on_min with
  | empty =>
    intro Y _ _
    rw [Finset.prod_empty]
    have : (0 : ℚ) ≤ 1 / (2 * (Y : ℚ)) := by positivity
    linarith
  | insert a s hmin ih =>
    intro Y hY hT
    have ha := hT a (Finset.mem_insert_self a s)
    have has : a ∉ s := fun h => lt_irrefl a (hmin a h)
    rw [Finset.prod_insert has]
    have hs : ∀ u ∈ s, u % 6 = 5 ∧ a + 6 ≤ u := fun u hu => by
      have h1 := hT u (Finset.mem_insert_of_mem hu)
      have h2 := hmin u hu
      omega
    have h1 := ih (a + 6) (by omega) hs
    have ha5 : (5 : ℚ) ≤ a := by exact_mod_cast (by omega : 5 ≤ a)
    have hYa : (Y : ℚ) ≤ a := by exact_mod_cast ha.2
    have hY0 : (5 : ℚ) ≤ Y := by exact_mod_cast hY
    have hstep := tele_step ha5
    have h2 : 1 / (2 * (a : ℚ)) ≤ 1 / (2 * (Y : ℚ)) :=
      one_div_le_one_div_of_le (by linarith) (by linarith)
    have h3 : (1 + 1 / (a : ℚ) ^ 2) * ∏ u ∈ s, (1 + 1 / (u : ℚ) ^ 2) ≤
        (1 + 1 / (a : ℚ) ^ 2) * (1 + 1 / (2 * ((a : ℚ) + 6))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have : ((a + 6 : ℕ) : ℚ) = (a : ℚ) + 6 := by push_cast; ring
      rw [← this]
      exact h1
    linarith

theorem c2_low (T : Finset ℕ) (hT : ∀ u ∈ T, u % 6 = 5) :
    ∏ u ∈ T.filter (fun u => u < 300), (1 + 1 / (u : ℚ) ^ 2) ≤
      ∏ i ∈ Finset.range 50, (1 + 1 / ((6 * i + 5 : ℕ) : ℚ) ^ 2) := by
  have hone : ∀ u : ℕ, (1 : ℚ) ≤ 1 + 1 / (u : ℚ) ^ 2 := fun u => by
    have : (0 : ℚ) ≤ 1 / (u : ℚ) ^ 2 := by positivity
    linarith
  have hsub : T.filter (fun u => u < 300) ⊆ (Finset.range 50).image (fun i => 6 * i + 5) := by
    intro u hu
    obtain ⟨hu1, hu2⟩ := Finset.mem_filter.mp hu
    have h5 := hT u hu1
    refine Finset.mem_image.mpr ⟨u / 6, Finset.mem_range.mpr (by omega), ?_⟩
    show 6 * (u / 6) + 5 = u
    omega
  have h1 := prod_le_of_subset_rat (fun u : ℕ => 1 + 1 / (u : ℚ) ^ 2) hsub fun u _ => hone u
  have hinj : Set.InjOn (fun i : ℕ => 6 * i + 5) (Finset.range 50 : Set ℕ) := by
    intro i _ j _ hij
    have : 6 * i + 5 = 6 * j + 5 := hij
    omega
  rw [Finset.prod_image hinj] at h1
  exact h1

theorem c2_bound (T : Finset ℕ) (hT : ∀ u ∈ T, u % 6 = 5) :
    ∏ u ∈ T, (1 + 1 / (u : ℚ) ^ 2) ≤ ((∏ i ∈ Finset.range 50, (1 + 1 / ((6 * i + 5 : ℕ) : ℚ) ^ 2)) * (1 + 1 / (2 * (300 : ℚ)))) := by
  rw [← Finset.prod_filter_mul_prod_filter_not T (fun u => u < 300)]
  have hlow := c2_low T hT
  have hhigh := tele (T.filter (fun u => ¬ u < 300)) 300 (by norm_num) (fun u hu => by
    obtain ⟨hu1, hu2⟩ := Finset.mem_filter.mp hu
    exact ⟨hT u hu1, by omega⟩)
  have hp1 : (0 : ℚ) ≤ ∏ u ∈ T.filter (fun u => ¬ u < 300), (1 + 1 / (u : ℚ) ^ 2) :=
    Finset.prod_nonneg fun u _ => by positivity
  have hp2 : (0 : ℚ) ≤ ∏ i ∈ Finset.range 50, (1 + 1 / ((6 * i + 5 : ℕ) : ℚ) ^ 2) :=
    Finset.prod_nonneg fun i _ => by positivity
  exact mul_le_mul hlow hhigh hp1 hp2

-- Section 3. Products of 1 + 1/p over sets of primes p = 1 mod 3.

theorem one_le_list (l : List ℕ) (hl : ∀ h ∈ l, 0 < h) : 1 ≤ (l.map (fun h : ℕ => 1 + 1 / (h : ℚ))).prod := by
  induction l with
  | nil => simp
  | cons x t ih =>
    rw [List.map_cons, List.prod_cons]
    have hx : (1 : ℚ) ≤ 1 + 1 / (x : ℚ) := by
      have : (0 : ℚ) ≤ 1 / (x : ℚ) := by positivity
      linarith
    exact one_le_mul_of_one_le_of_one_le hx (ih fun h hh => hl h (List.mem_cons_of_mem x hh))

theorem take_mono (l : List ℕ) (hl : ∀ h ∈ l, 0 < h) {k m : ℕ} (hkm : k ≤ m) :
    ((l.take k).map (fun h : ℕ => 1 + 1 / (h : ℚ))).prod ≤ ((l.take m).map (fun h : ℕ => 1 + 1 / (h : ℚ))).prod := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkm
  rw [List.take_add, List.map_append, List.prod_append]
  have h0 : (0 : ℚ) ≤ ((l.take k).map (fun h : ℕ => 1 + 1 / (h : ℚ))).prod :=
    le_trans zero_le_one (one_le_list _ fun h hh => hl h (List.mem_of_mem_take hh))
  have h1 := one_le_list ((l.drop k).take d) fun h hh => hl h (List.mem_of_mem_drop (List.mem_of_mem_take hh))
  exact le_mul_of_one_le_right h0 h1

theorem list_bound (X : ℕ) (hX : 0 < X) (good : ℕ → Prop) :
    ∀ (hs : List ℕ), hs.Pairwise (· < ·) → (∀ h ∈ hs, 0 < h ∧ h < X) → ∀ lb : ℕ,
    (∀ u, good u → lb ≤ u → u < X → u ∈ hs) → ∀ T : Finset ℕ, (∀ t ∈ T, good t ∧ lb ≤ t) →
    ∏ t ∈ T, (1 + 1 / (t : ℚ)) ≤
      ((hs.take T.card).map (fun h : ℕ => 1 + 1 / (h : ℚ))).prod * (1 + 1 / (X : ℚ)) ^ (T.card - hs.length) := by
  intro hs
  induction hs with
  | nil =>
    intro _ _ lb hc T hT
    simp only [List.take_nil, List.map_nil, List.prod_nil, one_mul, List.length_nil, Nat.sub_zero]
    rw [← Finset.prod_const]
    apply Finset.prod_le_prod
    · intro t _
      positivity
    · intro t ht
      have htX : X ≤ t := by
        by_contra hlt
        have := hc t (hT t ht).1 (hT t ht).2 (by omega)
        simp at this
      have : (1 : ℚ) / t ≤ 1 / X :=
        one_div_le_one_div_of_le (by exact_mod_cast hX) (by exact_mod_cast htX)
      linarith
  | cons h t ih =>
    intro hpw hpos lb hc T hT
    rcases T.eq_empty_or_nonempty with hT0 | hne
    · subst hT0
      simp
    · have hmT : T.min' hne ∈ T := T.min'_mem hne
      have hcard : T.card = (T.erase (T.min' hne)).card + 1 := (Finset.card_erase_add_one hmT).symm
      rw [← Finset.mul_prod_erase T (fun t : ℕ => 1 + 1 / (t : ℚ)) hmT, hcard, List.take_succ_cons,
        List.map_cons, List.prod_cons, List.length_cons, Nat.add_sub_add_right, mul_assoc]
      have hpw' := List.pairwise_cons.mp hpw
      have hh := hpos h (List.mem_cons.mpr (Or.inl rfl))
      have hhm : h ≤ T.min' hne := by
        by_cases hmX : T.min' hne < X
        · have := hc _ (hT _ hmT).1 (hT _ hmT).2 hmX
          rcases List.mem_cons.mp this with e | e
          · omega
          · exact (hpw'.1 _ e).le
        · omega
      have hih := ih hpw'.2 (fun x hx => hpos x (List.mem_cons_of_mem h hx)) (max lb (h + 1))
        (fun u hu hlb hux => by
          rcases List.mem_cons.mp (hc u hu (by omega) hux) with e | e
          · omega
          · exact e)
        (T.erase (T.min' hne)) (fun x hx => by
          have hxT := Finset.mem_of_mem_erase hx
          have hle : T.min' hne ≤ x := T.min'_le x hxT
          have hne' : x ≠ T.min' hne := Finset.ne_of_mem_erase hx
          have hlbm := (hT _ hmT).2
          exact ⟨(hT x hxT).1, by omega⟩)
      have h1 : 1 + 1 / ((T.min' hne : ℕ) : ℚ) ≤ 1 + 1 / (h : ℚ) := by
        have := one_div_le_one_div_of_le (by exact_mod_cast hh.1 : (0 : ℚ) < h)
          (by exact_mod_cast hhm : (h : ℚ) ≤ (T.min' hne : ℕ))
        linarith
      exact mul_le_mul h1 hih (Finset.prod_nonneg fun x _ => by positivity) (by positivity)

set_option maxRecDepth 100000 in
theorem hs_pairwise : (
    7 :: 13 :: 19 :: 31 :: 37 :: 43 :: 61 :: 67 :: 73 :: 79 :: 97 :: 103 :: 109 :: 127 ::
    139 :: 151 :: 157 :: 163 :: 181 :: 193 :: 199 :: 211 :: 223 :: 229 :: 241 :: 271 :: 277 ::
    283 :: 307 :: 313 :: 331 :: 337 :: 349 :: 367 :: 373 :: 379 :: 397 :: 409 :: 421 :: 433 ::
    439 :: 457 :: 463 :: 487 :: 499 :: 523 :: 541 :: 547 :: 571 :: 577 :: 601 :: 607 :: 613 ::
    619 :: 631 :: 643 :: 661 :: 673 :: 691 :: 709 :: 727 :: 733 :: 739 :: 751 :: 757 :: 769 ::
    787 :: 811 :: 823 :: 829 :: 853 :: 859 :: 877 :: 883 :: 907 :: 919 :: 937 :: 967 :: 991 ::
    997 :: 1009 :: 1021 :: 1033 :: 1039 :: 1051 :: 1063 :: 1069 :: 1087 :: 1093 :: 1117 ::
    1123 :: 1129 :: 1153 :: 1171 :: 1201 :: 1213 :: 1231 :: 1237 :: 1249 :: 1279 :: 1291 ::
    1297 :: 1303 :: 1321 :: 1327 :: 1381 :: 1399 :: 1423 :: 1429 :: 1447 :: 1453 :: 1459 ::
    1471 :: 1483 :: 1489 :: 1531 :: 1543 :: 1549 :: 1567 :: 1579 :: 1597 :: 1609 :: 1621 ::
    1627 :: 1657 :: 1663 :: 1669 :: 1693 :: 1699 :: 1723 :: 1741 :: 1747 :: 1753 :: 1759 ::
    1777 :: 1783 :: 1789 :: 1801 :: 1831 :: []).Pairwise (· < ·) := by decide

set_option maxRecDepth 100000 in
theorem hs_complete : ∀ u, u < 1849 → (u % 6 == 1 && 7 ≤ u && (u % 5 != 0 || u == 5) && (u % 7 != 0 || u == 7) && (u % 11 != 0 || u == 11) &&
      (u % 13 != 0 || u == 13) && (u % 17 != 0 || u == 17) && (u % 19 != 0 || u == 19) &&
      (u % 23 != 0 || u == 23) && (u % 29 != 0 || u == 29) && (u % 31 != 0 || u == 31) &&
      (u % 37 != 0 || u == 37) && (u % 41 != 0 || u == 41)) = true →
    u ∈ (
    7 :: 13 :: 19 :: 31 :: 37 :: 43 :: 61 :: 67 :: 73 :: 79 :: 97 :: 103 :: 109 :: 127 ::
    139 :: 151 :: 157 :: 163 :: 181 :: 193 :: 199 :: 211 :: 223 :: 229 :: 241 :: 271 :: 277 ::
    283 :: 307 :: 313 :: 331 :: 337 :: 349 :: 367 :: 373 :: 379 :: 397 :: 409 :: 421 :: 433 ::
    439 :: 457 :: 463 :: 487 :: 499 :: 523 :: 541 :: 547 :: 571 :: 577 :: 601 :: 607 :: 613 ::
    619 :: 631 :: 643 :: 661 :: 673 :: 691 :: 709 :: 727 :: 733 :: 739 :: 751 :: 757 :: 769 ::
    787 :: 811 :: 823 :: 829 :: 853 :: 859 :: 877 :: 883 :: 907 :: 919 :: 937 :: 967 :: 991 ::
    997 :: 1009 :: 1021 :: 1033 :: 1039 :: 1051 :: 1063 :: 1069 :: 1087 :: 1093 :: 1117 ::
    1123 :: 1129 :: 1153 :: 1171 :: 1201 :: 1213 :: 1231 :: 1237 :: 1249 :: 1279 :: 1291 ::
    1297 :: 1303 :: 1321 :: 1327 :: 1381 :: 1399 :: 1423 :: 1429 :: 1447 :: 1453 :: 1459 ::
    1471 :: 1483 :: 1489 :: 1531 :: 1543 :: 1549 :: 1567 :: 1579 :: 1597 :: 1609 :: 1621 ::
    1627 :: 1657 :: 1663 :: 1669 :: 1693 :: 1699 :: 1723 :: 1741 :: 1747 :: 1753 :: 1759 ::
    1777 :: 1783 :: 1789 :: 1801 :: 1831 :: []) := by decide

set_option maxRecDepth 100000 in
theorem hs_pos : ∀ h ∈ (
    7 :: 13 :: 19 :: 31 :: 37 :: 43 :: 61 :: 67 :: 73 :: 79 :: 97 :: 103 :: 109 :: 127 ::
    139 :: 151 :: 157 :: 163 :: 181 :: 193 :: 199 :: 211 :: 223 :: 229 :: 241 :: 271 :: 277 ::
    283 :: 307 :: 313 :: 331 :: 337 :: 349 :: 367 :: 373 :: 379 :: 397 :: 409 :: 421 :: 433 ::
    439 :: 457 :: 463 :: 487 :: 499 :: 523 :: 541 :: 547 :: 571 :: 577 :: 601 :: 607 :: 613 ::
    619 :: 631 :: 643 :: 661 :: 673 :: 691 :: 709 :: 727 :: 733 :: 739 :: 751 :: 757 :: 769 ::
    787 :: 811 :: 823 :: 829 :: 853 :: 859 :: 877 :: 883 :: 907 :: 919 :: 937 :: 967 :: 991 ::
    997 :: 1009 :: 1021 :: 1033 :: 1039 :: 1051 :: 1063 :: 1069 :: 1087 :: 1093 :: 1117 ::
    1123 :: 1129 :: 1153 :: 1171 :: 1201 :: 1213 :: 1231 :: 1237 :: 1249 :: 1279 :: 1291 ::
    1297 :: 1303 :: 1321 :: 1327 :: 1381 :: 1399 :: 1423 :: 1429 :: 1447 :: 1453 :: 1459 ::
    1471 :: 1483 :: 1489 :: 1531 :: 1543 :: 1549 :: 1567 :: 1579 :: 1597 :: 1609 :: 1621 ::
    1627 :: 1657 :: 1663 :: 1669 :: 1693 :: 1699 :: 1723 :: 1741 :: 1747 :: 1753 :: 1759 ::
    1777 :: 1783 :: 1789 :: 1801 :: 1831 :: []), 0 < h ∧ h < 1849 := by decide

set_option maxRecDepth 100000 in
theorem hs_length : (
    7 :: 13 :: 19 :: 31 :: 37 :: 43 :: 61 :: 67 :: 73 :: 79 :: 97 :: 103 :: 109 :: 127 ::
    139 :: 151 :: 157 :: 163 :: 181 :: 193 :: 199 :: 211 :: 223 :: 229 :: 241 :: 271 :: 277 ::
    283 :: 307 :: 313 :: 331 :: 337 :: 349 :: 367 :: 373 :: 379 :: 397 :: 409 :: 421 :: 433 ::
    439 :: 457 :: 463 :: 487 :: 499 :: 523 :: 541 :: 547 :: 571 :: 577 :: 601 :: 607 :: 613 ::
    619 :: 631 :: 643 :: 661 :: 673 :: 691 :: 709 :: 727 :: 733 :: 739 :: 751 :: 757 :: 769 ::
    787 :: 811 :: 823 :: 829 :: 853 :: 859 :: 877 :: 883 :: 907 :: 919 :: 937 :: 967 :: 991 ::
    997 :: 1009 :: 1021 :: 1033 :: 1039 :: 1051 :: 1063 :: 1069 :: 1087 :: 1093 :: 1117 ::
    1123 :: 1129 :: 1153 :: 1171 :: 1201 :: 1213 :: 1231 :: 1237 :: 1249 :: 1279 :: 1291 ::
    1297 :: 1303 :: 1321 :: 1327 :: 1381 :: 1399 :: 1423 :: 1429 :: 1447 :: 1453 :: 1459 ::
    1471 :: 1483 :: 1489 :: 1531 :: 1543 :: 1549 :: 1567 :: 1579 :: 1597 :: 1609 :: 1621 ::
    1627 :: 1657 :: 1663 :: 1669 :: 1693 :: 1699 :: 1723 :: 1741 :: 1747 :: 1753 :: 1759 ::
    1777 :: 1783 :: 1789 :: 1801 :: 1831 :: []).length = 139 := by decide

theorem good_mem {u : ℕ} (hu : u.Prime) (h3 : u % 3 = 1) (hX : u < 1849) :
    u ∈ (
    7 :: 13 :: 19 :: 31 :: 37 :: 43 :: 61 :: 67 :: 73 :: 79 :: 97 :: 103 :: 109 :: 127 ::
    139 :: 151 :: 157 :: 163 :: 181 :: 193 :: 199 :: 211 :: 223 :: 229 :: 241 :: 271 :: 277 ::
    283 :: 307 :: 313 :: 331 :: 337 :: 349 :: 367 :: 373 :: 379 :: 397 :: 409 :: 421 :: 433 ::
    439 :: 457 :: 463 :: 487 :: 499 :: 523 :: 541 :: 547 :: 571 :: 577 :: 601 :: 607 :: 613 ::
    619 :: 631 :: 643 :: 661 :: 673 :: 691 :: 709 :: 727 :: 733 :: 739 :: 751 :: 757 :: 769 ::
    787 :: 811 :: 823 :: 829 :: 853 :: 859 :: 877 :: 883 :: 907 :: 919 :: 937 :: 967 :: 991 ::
    997 :: 1009 :: 1021 :: 1033 :: 1039 :: 1051 :: 1063 :: 1069 :: 1087 :: 1093 :: 1117 ::
    1123 :: 1129 :: 1153 :: 1171 :: 1201 :: 1213 :: 1231 :: 1237 :: 1249 :: 1279 :: 1291 ::
    1297 :: 1303 :: 1321 :: 1327 :: 1381 :: 1399 :: 1423 :: 1429 :: 1447 :: 1453 :: 1459 ::
    1471 :: 1483 :: 1489 :: 1531 :: 1543 :: 1549 :: 1567 :: 1579 :: 1597 :: 1609 :: 1621 ::
    1627 :: 1657 :: 1663 :: 1669 :: 1693 :: 1699 :: 1723 :: 1741 :: 1747 :: 1753 :: 1759 ::
    1777 :: 1783 :: 1789 :: 1801 :: 1831 :: []) := by
  apply hs_complete u hX
  have key : ∀ s : ℕ, s.Prime → (u % s != 0 || u == s) = true := by
    intro s hs
    by_cases h : u % s = 0
    · have := (Nat.prime_dvd_prime_iff_eq hs hu).mp (Nat.dvd_of_mod_eq_zero h)
      simp [this]
    · simp [h]
  have h2 := hu.two_le
  have hodd : u % 2 = 1 := by
    rcases hu.eq_two_or_odd with e | e
    · omega
    · exact e
  have h6 : u % 6 = 1 := by omega
  have h7 : 7 ≤ u := by omega
  simp [key 5 (by norm_num), key 7 (by norm_num), key 11 (by norm_num), key 13 (by norm_num),
    key 17 (by norm_num), key 19 (by norm_num), key 23 (by norm_num), key 29 (by norm_num),
    key 31 (by norm_num), key 37 (by norm_num), key 41 (by norm_num), h6, h7]

theorem num_big : (((
    7 :: 13 :: 19 :: 31 :: 37 :: 43 :: 61 :: 67 :: 73 :: 79 :: 97 :: 103 :: 109 :: 127 ::
    139 :: 151 :: 157 :: 163 :: 181 :: 193 :: 199 :: 211 :: 223 :: 229 :: 241 :: 271 :: 277 ::
    283 :: 307 :: 313 :: 331 :: 337 :: 349 :: 367 :: 373 :: 379 :: 397 :: 409 :: 421 :: 433 ::
    439 :: 457 :: 463 :: 487 :: 499 :: 523 :: 541 :: 547 :: 571 :: 577 :: 601 :: 607 :: 613 ::
    619 :: 631 :: 643 :: 661 :: 673 :: 691 :: 709 :: 727 :: 733 :: 739 :: 751 :: 757 :: 769 ::
    787 :: 811 :: 823 :: 829 :: 853 :: 859 :: 877 :: 883 :: 907 :: 919 :: 937 :: 967 :: 991 ::
    997 :: 1009 :: 1021 :: 1033 :: 1039 :: 1051 :: 1063 :: 1069 :: 1087 :: 1093 :: 1117 ::
    1123 :: 1129 :: 1153 :: 1171 :: 1201 :: 1213 :: 1231 :: 1237 :: 1249 :: 1279 :: 1291 ::
    1297 :: 1303 :: 1321 :: 1327 :: 1381 :: 1399 :: 1423 :: 1429 :: 1447 :: 1453 :: 1459 ::
    1471 :: 1483 :: 1489 :: 1531 :: 1543 :: 1549 :: 1567 :: 1579 :: 1597 :: 1609 :: 1621 ::
    1627 :: 1657 :: 1663 :: 1669 :: 1693 :: 1699 :: 1723 :: 1741 :: 1747 :: 1753 :: 1759 ::
    1777 :: 1783 :: 1789 :: 1801 :: 1831 :: []).take 124).map (fun h : ℕ => 1 + 1 / (h : ℚ))).prod * ((∏ i ∈ Finset.range 50, (1 + 1 / ((6 * i + 5 : ℕ) : ℚ) ^ 2)) * (1 + 1 / (2 * (300 : ℚ)))) < 2048 / 1025 := by
  simp only [List.take, List.map, List.prod_cons, List.prod_nil, Finset.prod_range_succ,
    Finset.prod_range_zero]
  norm_num

theorem num_small : (((
    7 :: 13 :: 19 :: 31 :: 37 :: 43 :: 61 :: 67 :: 73 :: 79 :: 97 :: 103 :: 109 :: 127 ::
    139 :: 151 :: 157 :: 163 :: 181 :: 193 :: 199 :: 211 :: 223 :: 229 :: 241 :: 271 :: 277 ::
    283 :: 307 :: 313 :: 331 :: 337 :: 349 :: 367 :: 373 :: 379 :: 397 :: 409 :: 421 :: 433 ::
    439 :: 457 :: 463 :: 487 :: 499 :: 523 :: 541 :: 547 :: 571 :: 577 :: 601 :: 607 :: 613 ::
    619 :: 631 :: 643 :: 661 :: 673 :: 691 :: 709 :: 727 :: 733 :: 739 :: 751 :: 757 :: 769 ::
    787 :: 811 :: 823 :: 829 :: 853 :: 859 :: 877 :: 883 :: 907 :: 919 :: 937 :: 967 :: 991 ::
    997 :: 1009 :: 1021 :: 1033 :: 1039 :: 1051 :: 1063 :: 1069 :: 1087 :: 1093 :: 1117 ::
    1123 :: 1129 :: 1153 :: 1171 :: 1201 :: 1213 :: 1231 :: 1237 :: 1249 :: 1279 :: 1291 ::
    1297 :: 1303 :: 1321 :: 1327 :: 1381 :: 1399 :: 1423 :: 1429 :: 1447 :: 1453 :: 1459 ::
    1471 :: 1483 :: 1489 :: 1531 :: 1543 :: 1549 :: 1567 :: 1579 :: 1597 :: 1609 :: 1621 ::
    1627 :: 1657 :: 1663 :: 1669 :: 1693 :: 1699 :: 1723 :: 1741 :: 1747 :: 1753 :: 1759 ::
    1777 :: 1783 :: 1789 :: 1801 :: 1831 :: []).take 8).map (fun h : ℕ => 1 + 1 / (h : ℚ))).prod * ((∏ i ∈ Finset.range 50, (1 + 1 / ((6 * i + 5 : ℕ) : ℚ) ^ 2)) * (1 + 1 / (2 * (300 : ℚ)))) < 8 / 5 := by
  simp only [List.take, List.map, List.prod_cons, List.prod_nil, Finset.prod_range_succ,
    Finset.prod_range_zero]
  norm_num

-- Section 4. The lower bound.

theorem lower_bound {n : ℕ} {S : Finset ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (hS : ∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) (h3 : ¬ 3 ∣ n) :
    125 ≤ padicValNat 2 n := by
  have hn : n ≠ 0 := h.2.ne'
  obtain ⟨c1, c2, -, c4, c5, -⟩ := branch_none h hS h3
  have hW := weight_eq h
  rw [fact2_eq n] at hW
  set T := n.primeFactors.erase 2 with hTdef
  have hTmem : ∀ q ∈ T, q.Prime ∧ q ≠ 2 ∧ q ≠ 3 ∧ q ∈ n.primeFactors := by
    intro q hq
    have hq1 := Finset.mem_of_mem_erase hq
    refine ⟨Nat.prime_of_mem_primeFactors hq1, Finset.ne_of_mem_erase hq, ?_, hq1⟩
    rintro rfl
    exact h3 (Nat.dvd_of_mem_primeFactors hq1)
  -- split the weight
  have hsplit : ∏ q ∈ T, (1 + 1 / (q : ℚ) ^ n.factorization q) ≤
      (∏ q ∈ T.filter (fun q => q % 3 = 1), (1 + 1 / (q : ℚ))) *
        ∏ q ∈ T.filter (fun q => ¬ q % 3 = 1), (1 + 1 / (q : ℚ) ^ 2) := by
    rw [← Finset.prod_filter_mul_prod_filter_not T (fun q => q % 3 = 1)]
    apply mul_le_mul _ _ (Finset.prod_nonneg fun q _ => by positivity)
      (Finset.prod_nonneg fun q _ => by positivity)
    · apply Finset.prod_le_prod (fun q _ => by positivity)
      intro q hq
      obtain ⟨hqT, _⟩ := Finset.mem_filter.mp hq
      obtain ⟨hp, _, _, hpf⟩ := hTmem q hqT
      exact factor_le_one hp.one_lt.le (fact_pos hpf)
    · apply Finset.prod_le_prod (fun q _ => by positivity)
      intro q hq
      obtain ⟨hqT, hq1⟩ := Finset.mem_filter.mp hq
      obtain ⟨hp, hp2, hp3, hpf⟩ := hTmem q hqT
      have hq2 : q % 3 = 2 := by
        have : q % 3 ≠ 0 := fun h0 =>
          hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp (Nat.dvd_of_mod_eq_zero h0)).symm
        omega
      have he := c4 q hpf hq2
      have he1 := fact_pos hpf
      exact factor_le_two hp.one_lt.le (by omega)
  have hT2 : ∏ q ∈ T.filter (fun q => ¬ q % 3 = 1), (1 + 1 / (q : ℚ) ^ 2) ≤ ((∏ i ∈ Finset.range 50, (1 + 1 / ((6 * i + 5 : ℕ) : ℚ) ^ 2)) * (1 + 1 / (2 * (300 : ℚ)))) := by
    apply c2_bound
    intro q hq
    obtain ⟨hqT, hq1⟩ := Finset.mem_filter.mp hq
    obtain ⟨hp, hp2, hp3, _⟩ := hTmem q hqT
    have hodd : q % 2 = 1 := by
      rcases hp.eq_two_or_odd with e | e
      · exact absurd e hp2
      · exact e
    have : q % 3 ≠ 0 := fun h0 =>
      hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp (Nat.dvd_of_mod_eq_zero h0)).symm
    omega
  have hT1 := list_bound 1849 (by norm_num) (fun u => u.Prime ∧ u % 3 = 1) _ hs_pairwise hs_pos 0
    (fun u hu _ hux => good_mem hu.1 hu.2 hux) (T.filter (fun q => q % 3 = 1)) (fun t ht => by
      obtain ⟨htT, ht1⟩ := Finset.mem_filter.mp ht
      exact ⟨⟨(hTmem t htT).1, ht1⟩, Nat.zero_le t⟩)
  -- counting
  have hcardT : T.card ≤ padicValNat 2 n + 1 := by
    have := card_odd_primeFactors_le h
    rwa [Finset.filter_ne'] at this
  obtain ⟨z, hzS, hz3, -⟩ := c5
  have hzT2 : z ∈ T.filter (fun q => ¬ q % 3 = 1) := by
    obtain ⟨hzp, hz2, hzsq⟩ := (hS z).mp hzS
    refine Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hz2, ?_⟩, by omega⟩
    exact Nat.mem_primeFactors.mpr ⟨hzp, (dvd_pow_self z (by norm_num)).trans hzsq, hn⟩
  have hc12 := Finset.card_filter_add_card_filter_not (s := T) (fun q => q % 3 = 1)
  have hc2pos : 0 < (T.filter (fun q => ¬ q % 3 = 1)).card := Finset.card_pos.mpr ⟨z, hzT2⟩
  have hk : (T.filter (fun q => q % 3 = 1)).card ≤ padicValNat 2 n := by omega
  by_contra hlt
  have hlt : padicValNat 2 n ≤ 124 := by omega
  set k := (T.filter (fun q => q % 3 = 1)).card with hkdef
  rw [hs_length, show k - 139 = 0 by omega, pow_zero, mul_one] at hT1
  have hpos := hs_pos
  have hpos' : ∀ x ∈ (
    7 :: 13 :: 19 :: 31 :: 37 :: 43 :: 61 :: 67 :: 73 :: 79 :: 97 :: 103 :: 109 :: 127 ::
    139 :: 151 :: 157 :: 163 :: 181 :: 193 :: 199 :: 211 :: 223 :: 229 :: 241 :: 271 :: 277 ::
    283 :: 307 :: 313 :: 331 :: 337 :: 349 :: 367 :: 373 :: 379 :: 397 :: 409 :: 421 :: 433 ::
    439 :: 457 :: 463 :: 487 :: 499 :: 523 :: 541 :: 547 :: 571 :: 577 :: 601 :: 607 :: 613 ::
    619 :: 631 :: 643 :: 661 :: 673 :: 691 :: 709 :: 727 :: 733 :: 739 :: 751 :: 757 :: 769 ::
    787 :: 811 :: 823 :: 829 :: 853 :: 859 :: 877 :: 883 :: 907 :: 919 :: 937 :: 967 :: 991 ::
    997 :: 1009 :: 1021 :: 1033 :: 1039 :: 1051 :: 1063 :: 1069 :: 1087 :: 1093 :: 1117 ::
    1123 :: 1129 :: 1153 :: 1171 :: 1201 :: 1213 :: 1231 :: 1237 :: 1249 :: 1279 :: 1291 ::
    1297 :: 1303 :: 1321 :: 1327 :: 1381 :: 1399 :: 1423 :: 1429 :: 1447 :: 1453 :: 1459 ::
    1471 :: 1483 :: 1489 :: 1531 :: 1543 :: 1549 :: 1567 :: 1579 :: 1597 :: 1609 :: 1621 ::
    1627 :: 1657 :: 1663 :: 1669 :: 1693 :: 1699 :: 1723 :: 1741 :: 1747 :: 1753 :: 1759 ::
    1777 :: 1783 :: 1789 :: 1801 :: 1831 :: []), 0 < x := fun x hx => (hs_pos x hx).1
  have hP1 : 0 ≤ ∏ q ∈ T.filter (fun q => q % 3 = 1), (1 + 1 / (q : ℚ)) :=
    Finset.prod_nonneg fun q _ => by positivity
  have hP2 : 0 ≤ ∏ q ∈ T.filter (fun q => ¬ q % 3 = 1), (1 + 1 / (q : ℚ) ^ 2) :=
    Finset.prod_nonneg fun q _ => by positivity
  have hCpos : 0 ≤ ((∏ i ∈ Finset.range 50, (1 + 1 / ((6 * i + 5 : ℕ) : ℚ) ^ 2)) * (1 + 1 / (2 * (300 : ℚ)))) := by positivity
  have hw0 : 0 ≤ 1 + 1 / (2 : ℚ) ^ padicValNat 2 n := by positivity
  rcases Nat.lt_or_ge (padicValNat 2 n) 10 with hsm | hbig
  · have hk8 : k ≤ 8 := by omega
    have hH := take_mono _ hpos' hk8
    have h2a : (4 : ℚ) ≤ 2 ^ padicValNat 2 n := by
      have : 2 ^ 2 ≤ 2 ^ padicValNat 2 n := Nat.pow_le_pow_right (by norm_num) c2
      exact_mod_cast this
    have hw : 1 + 1 / (2 : ℚ) ^ padicValNat 2 n ≤ 5 / 4 := by
      have := one_div_le_one_div_of_le (by norm_num : (0 : ℚ) < 4) h2a
      linarith
    have hprod : ∏ q ∈ T, (1 + 1 / (q : ℚ) ^ n.factorization q) < 8 / 5 := by
      calc ∏ q ∈ T, (1 + 1 / (q : ℚ) ^ n.factorization q)
          ≤ (∏ q ∈ T.filter (fun q => q % 3 = 1), (1 + 1 / (q : ℚ))) *
              ∏ q ∈ T.filter (fun q => ¬ q % 3 = 1), (1 + 1 / (q : ℚ) ^ 2) := hsplit
        _ ≤ (((
    7 :: 13 :: 19 :: 31 :: 37 :: 43 :: 61 :: 67 :: 73 :: 79 :: 97 :: 103 :: 109 :: 127 ::
    139 :: 151 :: 157 :: 163 :: 181 :: 193 :: 199 :: 211 :: 223 :: 229 :: 241 :: 271 :: 277 ::
    283 :: 307 :: 313 :: 331 :: 337 :: 349 :: 367 :: 373 :: 379 :: 397 :: 409 :: 421 :: 433 ::
    439 :: 457 :: 463 :: 487 :: 499 :: 523 :: 541 :: 547 :: 571 :: 577 :: 601 :: 607 :: 613 ::
    619 :: 631 :: 643 :: 661 :: 673 :: 691 :: 709 :: 727 :: 733 :: 739 :: 751 :: 757 :: 769 ::
    787 :: 811 :: 823 :: 829 :: 853 :: 859 :: 877 :: 883 :: 907 :: 919 :: 937 :: 967 :: 991 ::
    997 :: 1009 :: 1021 :: 1033 :: 1039 :: 1051 :: 1063 :: 1069 :: 1087 :: 1093 :: 1117 ::
    1123 :: 1129 :: 1153 :: 1171 :: 1201 :: 1213 :: 1231 :: 1237 :: 1249 :: 1279 :: 1291 ::
    1297 :: 1303 :: 1321 :: 1327 :: 1381 :: 1399 :: 1423 :: 1429 :: 1447 :: 1453 :: 1459 ::
    1471 :: 1483 :: 1489 :: 1531 :: 1543 :: 1549 :: 1567 :: 1579 :: 1597 :: 1609 :: 1621 ::
    1627 :: 1657 :: 1663 :: 1669 :: 1693 :: 1699 :: 1723 :: 1741 :: 1747 :: 1753 :: 1759 ::
    1777 :: 1783 :: 1789 :: 1801 :: 1831 :: []).take 8).map (fun h : ℕ => 1 + 1 / (h : ℚ))).prod * ((∏ i ∈ Finset.range 50, (1 + 1 / ((6 * i + 5 : ℕ) : ℚ) ^ 2)) * (1 + 1 / (2 * (300 : ℚ)))) :=
            mul_le_mul (hT1.trans hH) hT2 hP2 (le_trans zero_le_one (one_le_list _ fun x hx =>
              hpos' x (List.mem_of_mem_take hx)))
        _ < 8 / 5 := num_small
    have hT0 : 0 ≤ ∏ q ∈ T, (1 + 1 / (q : ℚ) ^ n.factorization q) :=
      Finset.prod_nonneg fun q _ => by positivity
    nlinarith
  · have hk124 : k ≤ 124 := by omega
    have hH := take_mono _ hpos' hk124
    have h2a : (1024 : ℚ) ≤ 2 ^ padicValNat 2 n := by
      have : 2 ^ 10 ≤ 2 ^ padicValNat 2 n := Nat.pow_le_pow_right (by norm_num) hbig
      exact_mod_cast this
    have hw : 1 + 1 / (2 : ℚ) ^ padicValNat 2 n ≤ 1025 / 1024 := by
      have := one_div_le_one_div_of_le (by norm_num : (0 : ℚ) < 1024) h2a
      linarith
    have hprod : ∏ q ∈ T, (1 + 1 / (q : ℚ) ^ n.factorization q) < 2048 / 1025 := by
      calc ∏ q ∈ T, (1 + 1 / (q : ℚ) ^ n.factorization q)
          ≤ (∏ q ∈ T.filter (fun q => q % 3 = 1), (1 + 1 / (q : ℚ))) *
              ∏ q ∈ T.filter (fun q => ¬ q % 3 = 1), (1 + 1 / (q : ℚ) ^ 2) := hsplit
        _ ≤ (((
    7 :: 13 :: 19 :: 31 :: 37 :: 43 :: 61 :: 67 :: 73 :: 79 :: 97 :: 103 :: 109 :: 127 ::
    139 :: 151 :: 157 :: 163 :: 181 :: 193 :: 199 :: 211 :: 223 :: 229 :: 241 :: 271 :: 277 ::
    283 :: 307 :: 313 :: 331 :: 337 :: 349 :: 367 :: 373 :: 379 :: 397 :: 409 :: 421 :: 433 ::
    439 :: 457 :: 463 :: 487 :: 499 :: 523 :: 541 :: 547 :: 571 :: 577 :: 601 :: 607 :: 613 ::
    619 :: 631 :: 643 :: 661 :: 673 :: 691 :: 709 :: 727 :: 733 :: 739 :: 751 :: 757 :: 769 ::
    787 :: 811 :: 823 :: 829 :: 853 :: 859 :: 877 :: 883 :: 907 :: 919 :: 937 :: 967 :: 991 ::
    997 :: 1009 :: 1021 :: 1033 :: 1039 :: 1051 :: 1063 :: 1069 :: 1087 :: 1093 :: 1117 ::
    1123 :: 1129 :: 1153 :: 1171 :: 1201 :: 1213 :: 1231 :: 1237 :: 1249 :: 1279 :: 1291 ::
    1297 :: 1303 :: 1321 :: 1327 :: 1381 :: 1399 :: 1423 :: 1429 :: 1447 :: 1453 :: 1459 ::
    1471 :: 1483 :: 1489 :: 1531 :: 1543 :: 1549 :: 1567 :: 1579 :: 1597 :: 1609 :: 1621 ::
    1627 :: 1657 :: 1663 :: 1669 :: 1693 :: 1699 :: 1723 :: 1741 :: 1747 :: 1753 :: 1759 ::
    1777 :: 1783 :: 1789 :: 1801 :: 1831 :: []).take 124).map (fun h : ℕ => 1 + 1 / (h : ℚ))).prod * ((∏ i ∈ Finset.range 50, (1 + 1 / ((6 * i + 5 : ℕ) : ℚ) ^ 2)) * (1 + 1 / (2 * (300 : ℚ)))) :=
            mul_le_mul (hT1.trans hH) hT2 hP2 (le_trans zero_le_one (one_le_list _ fun x hx =>
              hpos' x (List.mem_of_mem_take hx)))
        _ < 2048 / 1025 := num_big
    have hT0 : 0 ≤ ∏ q ∈ T, (1 + 1 / (q : ℚ) ^ n.factorization q) :=
      Finset.prod_nonneg fun q _ => by positivity
    nlinarith

-- Section 4b. Every repeated odd prime has a source.

theorem source_of_repeated {n z : ℕ} (h : Erdos1052.IsUnitaryPerfect n) (hz : z.Prime) (hz2 : z ≠ 2)
    (hzz : z ^ 2 ∣ n) :
    z ^ 2 ∣ 2 ^ padicValNat 2 n + 1 ∨
      ∃ q ∈ n.primeFactors, q ≠ 2 ∧ q ≠ z ∧ z ∣ 1 + q ^ n.factorization q := by
  have hn : n ≠ 0 := h.2.ne'
  have h2pf : 2 ∈ n.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_two, two_dvd_of_isUnitaryPerfect h, hn⟩
  have E := prod_eq_two_mul h
  rw [← Finset.mul_prod_erase _ _ h2pf] at E
  by_cases hex : ∃ q ∈ n.primeFactors, q ≠ 2 ∧ q ≠ z ∧ z ∣ 1 + q ^ n.factorization q
  · exact Or.inr hex
  · left
    have hR : ¬ z ∣ ∏ q ∈ n.primeFactors.erase 2, (1 + q ^ n.factorization q) := by
      intro hd
      obtain ⟨q, hq, hzq⟩ := (Prime.dvd_finsetProd_iff hz.prime _).mp hd
      have hq1 := Finset.mem_of_mem_erase hq
      by_cases hqz : q = z
      · subst hqz
        have he := fact_pos hq1
        have h1 : q ∣ q ^ n.factorization q := dvd_pow_self q (by omega)
        have : q ∣ 1 := (Nat.dvd_add_right h1).mp (by rw [add_comm]; exact hzq)
        exact hz.one_lt.ne' (Nat.dvd_one.mp this)
      · exact hex ⟨q, hq1, Finset.ne_of_mem_erase hq, hqz, hzq⟩
    have hcop : Nat.Coprime (z ^ 2) (∏ q ∈ n.primeFactors.erase 2, (1 + q ^ n.factorization q)) :=
      Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd hz).mpr hR)
    have hd : z ^ 2 ∣ (1 + 2 ^ n.factorization 2) *
        ∏ q ∈ n.primeFactors.erase 2, (1 + q ^ n.factorization q) := by
      rw [E]
      exact Dvd.dvd.mul_left hzz 2
    have := hcop.dvd_of_dvd_mul_right hd
    rwa [add_comm, fact2_eq n] at this

-- Section 5. The step.

theorem main : H1 → H2 → H3 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H3_R1.H4 := by
  rintro ⟨A1, h1⟩ ⟨A2, h2⟩ ⟨A3, h3⟩
  refine ⟨A1 + A2 + A3, fun n h S hS hc hna h3n he _ hsimp hq2 hz h5 h17 h257 h65537 hcard => ?_⟩
  have hlow := lower_bound h hS h3n
  have hsrc : ∀ z ∈ S, z ^ 2 ∣ 2 ^ padicValNat 2 n + 1 ∨
      ∃ q ∈ n.primeFactors, q ≠ 2 ∧ q ≠ z ∧ z ∣ 1 + q ^ n.factorization q := fun z hz => by
    obtain ⟨hzp, hz2, hzz⟩ := (hS z).mp hz
    exact source_of_repeated h hzp hz2 hzz
  rcases (by omega : padicValNat 2 n % 4 = 2 ∨ padicValNat 2 n % 8 = 4 ∨ padicValNat 2 n % 8 = 0)
    with c | c | c
  · have := h1 n h S hS hc hna h3n he hlow hsimp hq2 hz hcard hsrc c (h5 c)
    omega
  · have := h2 n h S hS hc hna h3n he hlow hsimp hq2 hz hcard hsrc c (h17 c)
    omega
  · have := h3 n h S hS hc hna h3n he hlow hsimp hq2 hz hcard hsrc c h257 h65537
    omega

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H3_R1_H4_R1
