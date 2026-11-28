import OMAReductions.R_Erdos820_erdos_820_variants_log_log_exponent_R1

-- Step H2 of the reduction Erdos820.erdos_820.variants.log_log_exponent.R1
-- Credit: @LordMike

/-!
# An upper bound for `K n` (Erdős Problem 820)

`K n` is the least `k ≥ 2` with `gcd (k ^ n - 1) (2 ^ n - 1) = 1`. We prove that
`K n < exp (n ^ ((c + ε) / log (log n)))` for large `n`.

The proof has three parts.

* `sieve_aux`: Brun's pure sieve for a finite set of primes `p`, each with a set `B p` of
  forbidden residues.
* `K_bound`: `K n ≤ exp (90 * d(n) * (log n) ^ 3)` for `n ≥ 3`, where `d(n)` is the number of
  divisors of `n`. The sieve runs over the primes `p ∣ 2 ^ n - 1`, with `B p` the residues `r`
  with `r ^ n ≡ 1 (mod p)`. There are at most `gcd n (p - 1)` such residues, and
  `∑ gcd n (p - 1) / (p - 1) ≤ d(n) * (2 + log n)`.
* `divisor_bound` and `main_of`: `d(n) ≤ n ^ (34 / log (log n))` for large `n`, and the final
  asymptotic comparison.
-/

open Finset

namespace OpenB820

lemma box_count (X a q : ℕ) (hq : 0 < q) :
    (X : ℝ) / q - 1 ≤ (#{k ∈ range X | k ≡ a [MOD q]} : ℝ) ∧
      (#{k ∈ range X | k ≡ a [MOD q]} : ℝ) ≤ (X : ℝ) / q + 1 := by
  have h := Nat.count_modEq_card (b := X) hq a
  rw [Nat.count_eq_card_filter_range] at h
  rw [h]
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have h1 : ((X / q : ℕ) : ℝ) ≤ (X : ℝ) / q := Nat.cast_div_le
  have h2 : (X : ℝ) / q < ((X / q : ℕ) : ℝ) + 1 := by
    rw [div_lt_iff₀ hq']
    have h3 : X < (X / q + 1) * q := by
      have h4 := Nat.div_add_mod X q
      have h5 := Nat.mod_lt X hq
      nlinarith
    exact_mod_cast h3
  push_cast
  constructor <;> split_ifs <;> linarith

lemma pow_step (u b : ℝ) (hu : 0 ≤ u) (hb : 0 ≤ b) (s : ℕ) :
    (u + b) * u ^ s ≤ (u + b) ^ (s + 1) := by
  rw [pow_succ']
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hu (by linarith) s) (by linarith)

lemma step_arith (A x V t bb u us Gn S G1 : ℝ) (hGS : Gn + S = G1)
    (h1L : A * (V - t / 3) - u * us ≤ G1) (h1U : G1 ≤ A * (V + t / 3) + u * us)
    (hSU : S ≤ A * x * (V + t) + bb * us) (hSL : A * x * (V - t) - bb * us ≤ S) :
    A * ((1 - x) * V - (1 + 3 * x) * (t / 3)) - (u + bb) * us ≤ Gn ∧
      Gn ≤ A * ((1 - x) * V + (1 + 3 * x) * (t / 3)) + (u + bb) * us := by
  constructor <;> linarith

/-- Brun's pure sieve on a residue class, with explicit error terms. -/
theorem sieve_aux (X : ℕ) (B : ℕ → Finset ℕ) (s : ℕ) :
    ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ B p ⊆ range p) → ∀ q a : ℕ, 0 < q →
      (∀ p ∈ P, Nat.Coprime q p) →
      (X : ℝ) / q * (∏ p ∈ P, (1 - (#(B p) : ℝ) / p) -
          (∏ p ∈ P, (1 + 3 * ((#(B p) : ℝ) / p))) / 3 ^ s) -
          (1 + ∑ p ∈ P, (#(B p) : ℝ)) ^ s ≤
        (#{k ∈ range X | k ≡ a [MOD q] ∧ ∀ p ∈ P, k % p ∉ B p} : ℝ) ∧
      (#{k ∈ range X | k ≡ a [MOD q] ∧ ∀ p ∈ P, k % p ∉ B p} : ℝ) ≤
        (X : ℝ) / q * (∏ p ∈ P, (1 - (#(B p) : ℝ) / p) +
          (∏ p ∈ P, (1 + 3 * ((#(B p) : ℝ) / p))) / 3 ^ s) +
          (1 + ∑ p ∈ P, (#(B p) : ℝ)) ^ s := by
  induction s with
  | zero =>
    intro P hP q a hq _
    have hx : ∀ p ∈ P, 0 ≤ (#(B p) : ℝ) / p ∧ (#(B p) : ℝ) / p ≤ 1 := by
      intro p hp
      have hp0 : (0 : ℝ) < p := by exact_mod_cast (hP p hp).1.pos
      have hc : (#(B p) : ℝ) ≤ p := by
        have h := Finset.card_le_card (hP p hp).2
        rw [Finset.card_range] at h
        exact_mod_cast h
      exact ⟨by positivity, (div_le_one hp0).2 hc⟩
    have hV0 : 0 ≤ ∏ p ∈ P, (1 - (#(B p) : ℝ) / p) :=
      Finset.prod_nonneg fun p hp => by linarith [(hx p hp).2]
    have hV1 : ∏ p ∈ P, (1 - (#(B p) : ℝ) / p) ≤ 1 :=
      Finset.prod_le_one (fun p hp => by linarith [(hx p hp).2])
        (fun p hp => by linarith [(hx p hp).1])
    have hW : 1 ≤ ∏ p ∈ P, (1 + 3 * ((#(B p) : ℝ) / p)) := by
      calc (1 : ℝ) = ∏ p ∈ P, (1 : ℝ) := by simp
        _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one)
          (fun p hp => by linarith [(hx p hp).1])
    have hA : (0 : ℝ) ≤ (X : ℝ) / q := by positivity
    have hbox := box_count X a q hq
    have hle : (#{k ∈ range X | k ≡ a [MOD q] ∧ ∀ p ∈ P, k % p ∉ B p} : ℝ) ≤
        (#{k ∈ range X | k ≡ a [MOD q]} : ℝ) := by
      exact_mod_cast Finset.card_le_card (fun k hk => by
        simp only [mem_filter] at hk ⊢
        exact ⟨hk.1, hk.2.1⟩)
    have hG0 : (0 : ℝ) ≤ (#{k ∈ range X | k ≡ a [MOD q] ∧ ∀ p ∈ P, k % p ∉ B p} : ℝ) :=
      Nat.cast_nonneg _
    rw [pow_zero, pow_zero, div_one]
    generalize (∏ p ∈ P, (1 - (#(B p) : ℝ) / p)) = V at *
    generalize (∏ p ∈ P, (1 + 3 * ((#(B p) : ℝ) / p))) = W at *
    generalize (X : ℝ) / q = A at *
    constructor
    · nlinarith [mul_nonneg hA (sub_nonneg.2 (hV1.trans hW))]
    · nlinarith [mul_nonneg hA (by linarith : (0 : ℝ) ≤ V + W - 1), hbox.2]
  | succ s ihs =>
    intro P
    induction P using Finset.induction_on with
    | empty =>
      intro _ q a hq _
      have hbox := box_count X a q hq
      have hA : (0 : ℝ) ≤ (X : ℝ) / q := by positivity
      have h3 : (0 : ℝ) ≤ 1 / 3 ^ (s + 1) := by positivity
      have hset : {k ∈ range X | k ≡ a [MOD q] ∧ ∀ p ∈ (∅ : Finset ℕ), k % p ∉ B p} =
          {k ∈ range X | k ≡ a [MOD q]} := by
        ext k
        simp
      rw [hset, Finset.prod_empty, Finset.prod_empty, Finset.sum_empty, add_zero, one_pow]
      generalize (X : ℝ) / q = A at *
      generalize (1 : ℝ) / 3 ^ (s + 1) = e at *
      constructor
      · nlinarith [mul_nonneg hA h3, hbox.1]
      · nlinarith [mul_nonneg hA h3, hbox.2]
    | insert p P hpP ihP =>
      intro hP q a hq hcop
      have hPp := hP p (Finset.mem_insert_self p P)
      have hP' : ∀ p' ∈ P, p'.Prime ∧ B p' ⊆ range p' :=
        fun p' hp' => hP p' (Finset.mem_insert_of_mem hp')
      have hcop' : ∀ p' ∈ P, Nat.Coprime q p' :=
        fun p' hp' => hcop p' (Finset.mem_insert_of_mem hp')
      have hqp : Nat.Coprime q p := hcop p (Finset.mem_insert_self p P)
      have hp0 : 0 < p := hPp.1.pos
      have hcop2 : ∀ p' ∈ P, Nat.Coprime (q * p) p' := by
        intro p' hp'
        refine Nat.Coprime.mul_left (hcop' p' hp') ?_
        exact (Nat.coprime_primes hPp.1 (hP' p' hp').1).2 (fun h => hpP (h ▸ hp'))
      have I1 := ihP hP' q a hq hcop'
      have I0 := fun b : ℕ => ihs P hP' (q * p) (Nat.chineseRemainder hqp a b)
        (Nat.mul_pos hq hp0) hcop2
      have hGa : #{k ∈ range X | k ≡ a [MOD q] ∧ ∀ p' ∈ insert p P, k % p' ∉ B p'} =
          #({k ∈ range X | k ≡ a [MOD q] ∧ ∀ p' ∈ P, k % p' ∉ B p'}.filter
            (fun k => ¬ k % p ∈ B p)) := by
        congr 1
        ext k
        simp only [mem_filter, mem_range, Finset.forall_mem_insert]
        tauto
      have hGb : ∑ b ∈ B p, #{k ∈ range X | k ≡ (Nat.chineseRemainder hqp a b : ℕ) [MOD q * p] ∧
            ∀ p' ∈ P, k % p' ∉ B p'} =
          #({k ∈ range X | k ≡ a [MOD q] ∧ ∀ p' ∈ P, k % p' ∉ B p'}.filter
            (fun k => k % p ∈ B p)) := by
        rw [Finset.card_eq_sum_card_fiberwise (f := fun k => k % p) (t := B p)
          (fun k hk => Finset.mem_coe.2 (Finset.mem_filter.1 (Finset.mem_coe.1 hk)).2)]
        refine Finset.sum_congr rfl fun b hb => ?_
        congr 1
        ext k
        simp only [mem_filter, mem_range]
        have hb' : b < p := Finset.mem_range.1 (hPp.2 hb)
        have hc := (Nat.chineseRemainder hqp a b).2
        constructor
        · rintro ⟨hkX, hkc, hgood⟩
          obtain ⟨h1, h2⟩ := (Nat.modEq_and_modEq_iff_modEq_mul hqp).2 hkc
          have hkb : k % p = b := by
            have h3 : k % p = b % p := h2.trans hc.2
            rwa [Nat.mod_eq_of_lt hb'] at h3
          exact ⟨⟨⟨hkX, h1.trans hc.1, hgood⟩, hkb ▸ hb⟩, hkb⟩
        · rintro ⟨⟨⟨hkX, hka, hgood⟩, -⟩, hkb⟩
          have hkp : k ≡ b [MOD p] := by
            show k % p = b % p
            rw [Nat.mod_eq_of_lt hb']
            exact hkb
          exact ⟨hkX, (Nat.modEq_and_modEq_iff_modEq_mul hqp).1
            ⟨hka.trans hc.1.symm, hkp.trans hc.2.symm⟩, hgood⟩
      have hG : #{k ∈ range X | k ≡ a [MOD q] ∧ ∀ p' ∈ insert p P, k % p' ∉ B p'} +
          ∑ b ∈ B p, #{k ∈ range X | k ≡ (Nat.chineseRemainder hqp a b : ℕ) [MOD q * p] ∧
            ∀ p' ∈ P, k % p' ∉ B p'} =
          #{k ∈ range X | k ≡ a [MOD q] ∧ ∀ p' ∈ P, k % p' ∉ B p'} := by
        rw [hGa, hGb, add_comm]
        exact Finset.card_filter_add_card_filter_not _
      have hGr : (#{k ∈ range X | k ≡ a [MOD q] ∧ ∀ p' ∈ insert p P, k % p' ∉ B p'} : ℝ) +
          ∑ b ∈ B p, (#{k ∈ range X | k ≡ (Nat.chineseRemainder hqp a b : ℕ) [MOD q * p] ∧
            ∀ p' ∈ P, k % p' ∉ B p'} : ℝ) =
          (#{k ∈ range X | k ≡ a [MOD q] ∧ ∀ p' ∈ P, k % p' ∉ B p'} : ℝ) := by
        exact_mod_cast hG
      have hXqp : (X : ℝ) / ((q * p : ℕ) : ℝ) = (X : ℝ) / q / p := by
        push_cast
        rw [div_div]
      rw [hXqp] at I0
      have hsumU := Finset.sum_le_sum (s := B p) fun b _ => (I0 b).2
      have hsumL := Finset.sum_le_sum (s := B p) fun b _ => (I0 b).1
      rw [Finset.sum_const, nsmul_eq_mul] at hsumU hsumL
      have hβ : (0 : ℝ) ≤ ∑ p' ∈ P, (#(B p') : ℝ) := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
      have hbb : (0 : ℝ) ≤ (#(B p) : ℝ) := Nat.cast_nonneg _
      have hpow := pow_step (1 + ∑ p' ∈ P, (#(B p') : ℝ)) (#(B p) : ℝ) (by linarith) hbb s
      rw [Finset.prod_insert hpP, Finset.prod_insert hpP, Finset.sum_insert hpP]
      generalize (#{k ∈ range X | k ≡ a [MOD q] ∧ ∀ p' ∈ insert p P, k % p' ∉ B p'} : ℝ) = Gn at *
      generalize (#{k ∈ range X | k ≡ a [MOD q] ∧ ∀ p' ∈ P, k % p' ∉ B p'} : ℝ) = G1 at *
      generalize (∑ b ∈ B p, (#{k ∈ range X | k ≡ (Nat.chineseRemainder hqp a b : ℕ) [MOD q * p] ∧
            ∀ p' ∈ P, k % p' ∉ B p'} : ℝ)) = S at *
      generalize (∏ p' ∈ P, (1 - (#(B p') : ℝ) / p')) = V at *
      generalize (∏ p' ∈ P, (1 + 3 * ((#(B p') : ℝ) / p'))) = W at *
      generalize (∑ p' ∈ P, (#(B p') : ℝ)) = β at *
      generalize (#(B p) : ℝ) = bb at *
      generalize (X : ℝ) / q = A at *
      have key := step_arith A (bb / p) V (W / 3 ^ s) bb (1 + β) ((1 + β) ^ s) Gn S G1 hGr
        (by rw [show W / 3 ^ s / 3 = W / 3 ^ (s + 1) by ring,
              show (1 + β) * (1 + β) ^ s = (1 + β) ^ (s + 1) by ring]; exact I1.1)
        (by rw [show W / 3 ^ s / 3 = W / 3 ^ (s + 1) by ring,
              show (1 + β) * (1 + β) ^ s = (1 + β) ^ (s + 1) by ring]; exact I1.2)
        (by rw [show A * (bb / p) * (V + W / 3 ^ s) + bb * (1 + β) ^ s =
              bb * (A / p * (V + W / 3 ^ s) + (1 + β) ^ s) by ring]; exact hsumU)
        (by rw [show A * (bb / p) * (V - W / 3 ^ s) - bb * (1 + β) ^ s =
              bb * (A / p * (V - W / 3 ^ s) - (1 + β) ^ s) by ring]; exact hsumL)
      rw [show (1 + 3 * (bb / p)) * W / 3 ^ (s + 1) = (1 + 3 * (bb / p)) * (W / 3 ^ s / 3) by ring,
        show 1 + (bb + β) = 1 + β + bb by ring]
      constructor
      · linarith [key.1]
      · linarith [key.2]


/-- The residues `r` modulo `p` with `r ^ n ≡ 1`. -/
def Bad (n p : ℕ) : Finset ℕ := {r ∈ range p | r ^ n % p = 1}

lemma mem_bad {n p r : ℕ} : r ∈ Bad n p ↔ r < p ∧ r ^ n % p = 1 := by
  simp [Bad]

lemma zmod_pow_gcd (n p : ℕ) [Fact p.Prime] (hn : 0 < n) (x : ZMod p) (h : x ^ n = 1) :
    x ^ Nat.gcd n (p - 1) = 1 := by
  have h0 : x ≠ 0 := by
    intro h0
    rw [h0, zero_pow hn.ne'] at h
    exact zero_ne_one h
  exact pow_gcd_eq_one.2 ⟨h, ZMod.pow_card_sub_one_eq_one h0⟩

lemma bad_card_le (n p : ℕ) (hp : p.Prime) (hn : 0 < n) :
    #(Bad n p) ≤ Nat.gcd n (p - 1) := by
  have : Fact p.Prime := ⟨hp⟩
  have hg : 0 < Nat.gcd n (p - 1) := Nat.gcd_pos_of_pos_left _ hn
  calc #(Bad n p) ≤ #(Polynomial.nthRootsFinset (Nat.gcd n (p - 1)) (1 : ZMod p)) := by
        refine Finset.card_le_card_of_injOn (fun r : ℕ => (r : ZMod p)) ?_ ?_
        · intro r hr
          have hr' := mem_bad.1 (Finset.mem_coe.1 hr)
          rw [Finset.mem_coe, Polynomial.mem_nthRootsFinset hg]
          refine zmod_pow_gcd n p hn _ ?_
          have h1 : ((r ^ n : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
            rw [ZMod.natCast_eq_natCast_iff', hr'.2, Nat.mod_eq_of_lt hp.one_lt]
          simpa using h1
        · intro r hr r' hr' h
          have h1 := (mem_bad.1 (Finset.mem_coe.1 hr)).1
          have h2 := (mem_bad.1 (Finset.mem_coe.1 hr')).1
          have h3 := (ZMod.natCast_eq_natCast_iff' r r' p).1 h
          rwa [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at h3
    _ ≤ Multiset.card (Polynomial.nthRoots (Nat.gcd n (p - 1)) (1 : ZMod p)) := by
        rw [Polynomial.nthRootsFinset_def]
        exact Multiset.toFinset_card_le _
    _ ≤ Nat.gcd n (p - 1) := Polynomial.card_nthRoots _ _

lemma card_primeFactors_lt (N g : ℕ) (hN : 0 < N) (h : N < 2 ^ g) : #N.primeFactors < g := by
  have h1 : 2 ^ #N.primeFactors ≤ ∏ p ∈ N.primeFactors, p :=
    Finset.pow_card_le_prod _ _ _ fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
  have h2 : ∏ p ∈ N.primeFactors, p ≤ N := Nat.le_of_dvd hN (Nat.prod_primeFactors_dvd N)
  exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 (lt_of_le_of_lt (h1.trans h2) h)

lemma dvd_two_pow_gcd (n p : ℕ) (hn : 0 < n) (hp : p.Prime) (hd : p ∣ 2 ^ n - 1) :
    p ∣ 2 ^ Nat.gcd n (p - 1) - 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have h1 : (2 : ZMod p) ^ n = 1 := by
    have h := (ZMod.natCast_eq_zero_iff (2 ^ n - 1) p).2 hd
    rw [Nat.cast_sub Nat.one_le_two_pow] at h
    push_cast at h
    exact sub_eq_zero.1 h
  have h2 := zmod_pow_gcd n p hn 2 h1
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub Nat.one_le_two_pow]
  push_cast
  exact sub_eq_zero.2 h2

lemma sum_inv_Icc_le (g : ℕ) : ∑ m ∈ Icc 1 g, ((m : ℝ))⁻¹ ≤ 1 + Real.log g := by
  have h := harmonic_le_one_add_log g
  rw [harmonic_eq_sum_Icc] at h
  push_cast at h
  exact h

lemma fiber_sum_le (n g : ℕ) (hn : 0 < n) (hg : 0 < g) :
    ∑ p ∈ (2 ^ n - 1).primeFactors with Nat.gcd n (p - 1) = g, (g : ℝ) / ((p - 1 : ℕ) : ℝ) ≤
      2 + Real.log g := by
  obtain ⟨T, hT⟩ : ∃ T : Finset ℕ,
      T = (Nat.primeFactors (2 ^ n - 1)).filter (fun p => Nat.gcd n (p - 1) = g) := ⟨_, rfl⟩
  rw [← hT]
  have h2g := Nat.one_lt_two_pow hg.ne'
  have hmem : ∀ p ∈ T,
      p.Prime ∧ g ∣ p - 1 ∧ 0 < p - 1 ∧ p ∣ 2 ^ g - 1 := by
    intro p hp
    rw [hT, Finset.mem_filter] at hp
    have hpp := Nat.prime_of_mem_primeFactors hp.1
    refine ⟨hpp, hp.2 ▸ Nat.gcd_dvd_right _ _, Nat.sub_pos_of_lt hpp.one_lt, ?_⟩
    have := dvd_two_pow_gcd n p hn hpp (Nat.dvd_of_mem_primeFactors hp.1)
    rwa [hp.2] at this
  have hcard : #T ≤ g := by
    have hsub : T ⊆
        (2 ^ g - 1).primeFactors := by
      intro p hp
      have h := hmem p hp
      exact Nat.mem_primeFactors.2 ⟨h.1, h.2.2.2, by omega⟩
    have h2 : #(2 ^ g - 1).primeFactors < g :=
      card_primeFactors_lt _ _ (by omega) (by omega)
    exact (Finset.card_le_card hsub).trans h2.le
  have hg' : (0 : ℝ) < g := by exact_mod_cast hg
  have hterm : ∀ p ∈ T,
      (g : ℝ) / ((p - 1 : ℕ) : ℝ) ≤
      (if (p - 1) / g ≤ g then (((p - 1) / g : ℕ) : ℝ)⁻¹ else 0) + (g : ℝ)⁻¹ := by
    intro p hp
    obtain ⟨-, hd, hpos, -⟩ := hmem p hp
    obtain ⟨m, hm⟩ := hd
    have hm0 : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · rw [h, mul_zero] at hm
        omega
      · exact h
    have hdiv : (p - 1) / g = m := by rw [hm, Nat.mul_div_cancel_left _ hg]
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm0
    rw [hdiv, hm]
    push_cast
    have e : (g : ℝ) / (g * m) = (m : ℝ)⁻¹ := by field_simp
    rw [e]
    split_ifs with h
    · linarith [inv_pos.2 hg']
    · have h1 : (g : ℝ) ≤ m := by exact_mod_cast (not_le.1 h).le
      have h2 := inv_anti₀ hg' h1
      linarith
  have hinj : Set.InjOn (fun p : ℕ => (p - 1) / g)
      (T : Set ℕ) := by
    intro p hp p' hp' h
    obtain ⟨-, hd, hpos, -⟩ := hmem p (Finset.mem_coe.1 hp)
    obtain ⟨-, hd', hpos', -⟩ := hmem p' (Finset.mem_coe.1 hp')
    have h1 := Nat.div_mul_cancel hd
    have h2 := Nat.div_mul_cancel hd'
    have h3 : (p - 1) / g = (p' - 1) / g := h
    rw [h3] at h1
    have h4 : p - 1 = p' - 1 := h1.symm.trans h2
    omega
  have himg : ∑ p ∈ T,
      (if (p - 1) / g ≤ g then (((p - 1) / g : ℕ) : ℝ)⁻¹ else 0) =
      ∑ m ∈ T.image
        (fun p : ℕ => (p - 1) / g), (if m ≤ g then ((m : ℝ))⁻¹ else 0) :=
    (Finset.sum_image (f := fun m : ℕ => if m ≤ g then ((m : ℝ))⁻¹ else 0) hinj).symm
  calc ∑ p ∈ T, (g : ℝ) / ((p - 1 : ℕ) : ℝ)
      ≤ ∑ p ∈ T,
          ((if (p - 1) / g ≤ g then (((p - 1) / g : ℕ) : ℝ)⁻¹ else 0) + (g : ℝ)⁻¹) :=
        Finset.sum_le_sum hterm
    _ = ∑ p ∈ T,
          (if (p - 1) / g ≤ g then (((p - 1) / g : ℕ) : ℝ)⁻¹ else 0) +
          #T * (g : ℝ)⁻¹ := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    _ ≤ (1 + Real.log g) + 1 := by
        refine add_le_add ?_ ?_
        · rw [himg, ← Finset.sum_filter]
          refine (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_).trans (sum_inv_Icc_le g)
          · intro m hm
            rw [Finset.mem_filter, Finset.mem_image] at hm
            obtain ⟨⟨p, hp, rfl⟩, hle⟩ := hm
            obtain ⟨-, hd, hpos, -⟩ := hmem p hp
            rw [Finset.mem_Icc]
            exact ⟨Nat.div_pos (Nat.le_of_dvd hpos hd) hg, hle⟩
          · intro m _ _
            positivity
        · have h1 : (#T : ℝ) ≤ g := by
            exact_mod_cast hcard
          calc (#T : ℝ) * (g : ℝ)⁻¹
              ≤ g * (g : ℝ)⁻¹ := mul_le_mul_of_nonneg_right h1 (inv_pos.2 hg').le
            _ = 1 := mul_inv_cancel₀ hg'.ne'
    _ = 2 + Real.log g := by ring

lemma sum_gcd_le (n : ℕ) (hn : 0 < n) :
    ∑ p ∈ (2 ^ n - 1).primeFactors, (Nat.gcd n (p - 1) : ℝ) / ((p - 1 : ℕ) : ℝ) ≤
      #n.divisors * (2 + Real.log n) := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun p : ℕ => Nat.gcd n (p - 1)) (t := n.divisors)
    (fun p _ => Nat.mem_divisors.2 ⟨Nat.gcd_dvd_left _ _, hn.ne'⟩)]
  calc _ ≤ ∑ g ∈ n.divisors, (2 + Real.log n) := by
        refine Finset.sum_le_sum fun g hg => ?_
        have hgd := Nat.mem_divisors.1 hg
        have hg0 : 0 < g := Nat.pos_of_dvd_of_pos hgd.1 hn
        have h1 : ∑ p ∈ (2 ^ n - 1).primeFactors with Nat.gcd n (p - 1) = g,
            (Nat.gcd n (p - 1) : ℝ) / ((p - 1 : ℕ) : ℝ) =
            ∑ p ∈ (2 ^ n - 1).primeFactors with Nat.gcd n (p - 1) = g,
            (g : ℝ) / ((p - 1 : ℕ) : ℝ) :=
          Finset.sum_congr rfl fun p hp => by rw [(Finset.mem_filter.1 hp).2]
        rw [h1]
        refine (fiber_sum_le n g hn hg0).trans ?_
        have h2 : Real.log g ≤ Real.log n :=
          Real.log_le_log (by exact_mod_cast hg0) (by exact_mod_cast Nat.le_of_dvd hn hgd.1)
        linarith
    _ = #n.divisors * (2 + Real.log n) := by rw [Finset.sum_const, nsmul_eq_mul]

lemma exp_neg_two_mul_le (y : ℝ) (h0 : 0 ≤ y) (h1 : y ≤ 1 / 2) :
    Real.exp (-(2 * y)) ≤ 1 - y := by
  have h2 : 1 + 2 * y ≤ Real.exp (2 * y) := by linarith [Real.add_one_le_exp (2 * y)]
  have h3 : (0 : ℝ) < 1 + 2 * y := by linarith
  rw [Real.exp_neg]
  calc (Real.exp (2 * y))⁻¹ ≤ (1 + 2 * y)⁻¹ := inv_anti₀ h3 h2
    _ ≤ 1 - y := by
      rw [inv_eq_one_div, div_le_iff₀ h3]
      nlinarith

lemma prime_terms (n p : ℕ) (hn : 0 < n) (hp : p.Prime) :
    Real.exp (-(Real.log ((n : ℝ) + 1) + 2) *
        ((Nat.gcd n (p - 1) : ℝ) / ((p - 1 : ℕ) : ℝ))) ≤ 1 - (#(Bad n p) : ℝ) / p ∧
      1 + 3 * ((#(Bad n p) : ℝ) / p) ≤
        Real.exp (3 * ((Nat.gcd n (p - 1) : ℝ) / ((p - 1 : ℕ) : ℝ))) := by
  have hb := bad_card_le n p hp hn
  have hgd : Nat.gcd n (p - 1) ∣ p - 1 := Nat.gcd_dvd_right _ _
  have hgn : Nat.gcd n (p - 1) ≤ n := Nat.le_of_dvd hn (Nat.gcd_dvd_left _ _)
  have hP1 : 0 < p - 1 := Nat.sub_pos_of_lt hp.one_lt
  have hg0 : 0 < Nat.gcd n (p - 1) := Nat.gcd_pos_of_pos_left _ hn
  have hgle : Nat.gcd n (p - 1) ≤ p - 1 := Nat.le_of_dvd hP1 hgd
  have hpc : (p : ℝ) = ((p - 1 : ℕ) : ℝ) + 1 := by
    rw [Nat.cast_sub hp.one_lt.le]
    simp
  generalize Nat.gcd n (p - 1) = gg at *
  generalize #(Bad n p) = b at *
  generalize p - 1 = P1 at *
  have hbR : (b : ℝ) ≤ gg := by exact_mod_cast hb
  have hgR : (gg : ℝ) ≤ P1 := by exact_mod_cast hgle
  have hP1R : (0 : ℝ) < P1 := by exact_mod_cast hP1
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg _
  have hg0R : (0 : ℝ) < gg := by exact_mod_cast hg0
  have hp0 : (0 : ℝ) < p := by
    rw [hpc]
    linarith
  have hy0 : 0 ≤ (gg : ℝ) / P1 := by positivity
  have hxy : (b : ℝ) / p ≤ (gg : ℝ) / P1 := by
    rw [div_le_div_iff₀ hp0 hP1R, hpc]
    nlinarith
  have hx0 : 0 ≤ (b : ℝ) / p := by positivity
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hL : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg (by linarith)
  refine ⟨?_, ?_⟩
  · rcases hgle.eq_or_lt with heq | hlt
    · have hy1 : (gg : ℝ) / P1 = 1 := by
        rw [heq]
        exact div_self hP1R.ne'
      rw [hy1, mul_one]
      have hpn : (p : ℝ) ≤ n + 1 := by
        rw [hpc]
        have h1 : (P1 : ℝ) ≤ n := by
          rw [← heq]
          exact_mod_cast hgn
        linarith
      have h1 : Real.exp (-(Real.log ((n : ℝ) + 1) + 2)) ≤ 1 / ((n : ℝ) + 1) := by
        rw [neg_add, Real.exp_add, Real.exp_neg, Real.exp_log (by linarith), one_div]
        have h2 : Real.exp (-2) ≤ 1 := Real.exp_le_one_iff.2 (by norm_num)
        have hpos : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := inv_pos.2 (by linarith)
        nlinarith
      have h2 : 1 / ((n : ℝ) + 1) ≤ 1 / p := one_div_le_one_div_of_le hp0 hpn
      have h3 : 1 / (p : ℝ) ≤ 1 - b / p := by
        rw [le_sub_iff_add_le, ← add_div, div_le_one hp0, hpc]
        linarith
      exact h1.trans (h2.trans h3)
    · obtain ⟨m, hm⟩ := hgd
      have hm2 : 2 ≤ m := by
        rcases m with _ | _ | m
        · omega
        · omega
        · omega
      have h2g : 2 * gg ≤ P1 := by
        calc 2 * gg = gg * 2 := by ring
          _ ≤ gg * m := Nat.mul_le_mul_left _ hm2
          _ = P1 := hm.symm
      have hy : (gg : ℝ) / P1 ≤ 1 / 2 := by
        rw [div_le_div_iff₀ hP1R (by norm_num)]
        have h1 : ((2 * gg : ℕ) : ℝ) ≤ P1 := by exact_mod_cast h2g
        push_cast at h1
        linarith
      have h1 := exp_neg_two_mul_le _ hy0 hy
      have h2 : Real.exp (-(Real.log ((n : ℝ) + 1) + 2) * ((gg : ℝ) / P1)) ≤
          Real.exp (-(2 * ((gg : ℝ) / P1))) := by
        apply Real.exp_le_exp.2
        nlinarith
      linarith
  · have h1 := Real.add_one_le_exp (3 * ((gg : ℝ) / P1))
    linarith

lemma prod_bounds (n : ℕ) (hn : 0 < n) :
    Real.exp (-(Real.log ((n : ℝ) + 1) + 2) * ((#n.divisors : ℝ) * (2 + Real.log (n : ℝ)))) ≤
        ∏ p ∈ (2 ^ n - 1).primeFactors, (1 - (#(Bad n p) : ℝ) / p) ∧
      ∏ p ∈ (2 ^ n - 1).primeFactors, (1 + 3 * ((#(Bad n p) : ℝ) / p)) ≤
        Real.exp (3 * ((#n.divisors : ℝ) * (2 + Real.log (n : ℝ)))) := by
  have hsum := sum_gcd_le n hn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hL : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg (by linarith)
  constructor
  · refine le_trans ?_ (Finset.prod_le_prod (fun _ _ => (Real.exp_pos _).le)
      fun p hp => (prime_terms n p hn (Nat.prime_of_mem_primeFactors hp)).1)
    rw [← Real.exp_sum, ← Finset.mul_sum]
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonpos_left hsum (by linarith))
  · calc ∏ p ∈ (2 ^ n - 1).primeFactors, (1 + 3 * ((#(Bad n p) : ℝ) / p))
        ≤ ∏ p ∈ (2 ^ n - 1).primeFactors,
            Real.exp (3 * ((Nat.gcd n (p - 1) : ℝ) / ((p - 1 : ℕ) : ℝ))) :=
          Finset.prod_le_prod (fun p _ => by positivity)
            fun p hp => (prime_terms n p hn (Nat.prime_of_mem_primeFactors hp)).2
      _ = Real.exp (3 * ∑ p ∈ (2 ^ n - 1).primeFactors,
            (Nat.gcd n (p - 1) : ℝ) / ((p - 1 : ℕ) : ℝ)) := by
          rw [Finset.mul_sum, Real.exp_sum]
      _ ≤ Real.exp (3 * ((#n.divisors : ℝ) * (2 + Real.log (n : ℝ)))) :=
          Real.exp_le_exp.2 (by linarith)

lemma sum_bad_le (n : ℕ) (hn : 0 < n) :
    ∑ p ∈ (2 ^ n - 1).primeFactors, (#(Bad n p) : ℝ) ≤ (n : ℝ) ^ 2 := by
  have h2n := Nat.one_lt_two_pow hn.ne'
  have h1 : #(2 ^ n - 1).primeFactors ≤ n :=
    (card_primeFactors_lt _ _ (by omega) (by omega)).le
  calc ∑ p ∈ (2 ^ n - 1).primeFactors, (#(Bad n p) : ℝ)
      ≤ ∑ _p ∈ (2 ^ n - 1).primeFactors, (n : ℝ) := by
        refine Finset.sum_le_sum fun p hp => ?_
        have h := (bad_card_le n p (Nat.prime_of_mem_primeFactors hp) hn).trans
          (Nat.le_of_dvd hn (Nat.gcd_dvd_left _ _))
        exact_mod_cast h
    _ = #(2 ^ n - 1).primeFactors * (n : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ n * n := mul_le_mul_of_nonneg_right (by exact_mod_cast h1) (Nat.cast_nonneg n)
    _ = (n : ℝ) ^ 2 := by ring

lemma K_lt (n X : ℕ) (hn : 2 ≤ n)
    (hG : 2 ≤ #{k ∈ range X | ∀ p ∈ (2 ^ n - 1).primeFactors, k % p ∉ Bad n p}) :
    Erdos820.K n < X := by
  have h4 : 4 ≤ 2 ^ n :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨k, hk, hk2⟩ : ∃ k : ℕ, k ∈ (range X).filter
      (fun k : ℕ => ∀ p ∈ Nat.primeFactors (2 ^ n - 1), k % p ∉ Bad n p) ∧ 2 ≤ k := by
    by_contra hcon0
    have hcon : ∀ k : ℕ, k ∈ (range X).filter
        (fun k : ℕ => ∀ p ∈ Nat.primeFactors (2 ^ n - 1), k % p ∉ Bad n p) → k < 2 :=
      fun k hk => lt_of_not_ge fun h => hcon0 ⟨k, hk, h⟩
    have hsub : (range X).filter
        (fun k : ℕ => ∀ p ∈ Nat.primeFactors (2 ^ n - 1), k % p ∉ Bad n p) ⊆ {0} := by
      intro k hk
      have hk2 := hcon k hk
      rw [Finset.mem_singleton]
      by_contra hk0
      have hk1 : k = 1 := by omega
      subst hk1
      obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (show 2 ^ n - 1 ≠ 1 by omega)
      have hpm : p ∈ (2 ^ n - 1).primeFactors := Nat.mem_primeFactors.2 ⟨hp, hpd, by omega⟩
      refine (Finset.mem_filter.1 hk).2 p hpm ?_
      rw [mem_bad, Nat.mod_eq_of_lt hp.one_lt, one_pow, Nat.mod_eq_of_lt hp.one_lt]
      exact ⟨hp.one_lt, rfl⟩
    have hc := Finset.card_le_card hsub
    rw [Finset.card_singleton] at hc
    omega
  rw [Finset.mem_filter, Finset.mem_range] at hk
  have hcop : Nat.Coprime (k ^ n - 1) (2 ^ n - 1) := by
    refine Nat.coprime_of_dvd fun p hp hpk hp2 => ?_
    have hpm : p ∈ (2 ^ n - 1).primeFactors := Nat.mem_primeFactors.2 ⟨hp, hp2, by omega⟩
    refine hk.2 p hpm ?_
    rw [mem_bad]
    refine ⟨Nat.mod_lt _ hp.pos, ?_⟩
    have hk1 : 1 ≤ k ^ n := Nat.one_le_pow _ _ (by omega)
    have hmod : 1 ≡ k ^ n [MOD p] := (Nat.modEq_iff_dvd' hk1).2 hpk
    have hmod' : k ^ n % p = 1 % p := hmod.symm
    rw [← Nat.pow_mod, hmod', Nat.mod_eq_of_lt hp.one_lt]
  have hK : Erdos820.K n ≤ k := by
    unfold Erdos820.K
    exact Nat.sInf_le ⟨hk2, hcop⟩
  exact lt_of_le_of_lt hK hk.1

lemma K_lt_of (n s X : ℕ) (hn : 2 ≤ n) (Λ T : ℝ) (hΛ : Λ = Real.log ((n : ℝ) + 1) + 2)
    (hT : T = (#n.divisors : ℝ) * (2 + Real.log (n : ℝ)))
    (hs : 2 * Real.exp ((Λ + 3) * T) ≤ 3 ^ s)
    (hX : 2 * ((1 + (n : ℝ) ^ 2) ^ s + 2) * Real.exp (Λ * T) ≤ X) :
    Erdos820.K n < X := by
  have hn0 : 0 < n := by omega
  apply K_lt n X hn
  obtain ⟨hV, hW⟩ := prod_bounds n hn0
  have hβ := sum_bad_le n hn0
  have hβ0 : (0 : ℝ) ≤ ∑ p ∈ (2 ^ n - 1).primeFactors, (#(Bad n p) : ℝ) :=
    Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  have hsv := (sieve_aux X (Bad n) s (2 ^ n - 1).primeFactors
    (fun p hp => ⟨Nat.prime_of_mem_primeFactors hp,
      fun r hr => Finset.mem_range.2 (mem_bad.1 hr).1⟩)
    1 0 one_pos (fun p _ => Nat.coprime_one_left p)).1
  have hset : {k ∈ range X | k ≡ 0 [MOD 1] ∧ ∀ p ∈ (2 ^ n - 1).primeFactors, k % p ∉ Bad n p} =
      {k ∈ range X | ∀ p ∈ (2 ^ n - 1).primeFactors, k % p ∉ Bad n p} := by
    ext k
    simp [Nat.modEq_one]
  rw [hset] at hsv
  simp only [Nat.cast_one, div_one] at hsv
  rw [← hΛ, ← hT] at hV
  rw [← hT] at hW
  generalize (∏ p ∈ (2 ^ n - 1).primeFactors, (1 - (#(Bad n p) : ℝ) / p)) = V at *
  generalize (∏ p ∈ (2 ^ n - 1).primeFactors, (1 + 3 * ((#(Bad n p) : ℝ) / p))) = W at *
  generalize (∑ p ∈ (2 ^ n - 1).primeFactors, (#(Bad n p) : ℝ)) = β at *
  have hE : 0 < Real.exp (Λ * T) := Real.exp_pos _
  have hE3 : 0 < Real.exp (3 * T) := Real.exp_pos _
  have hV' : (Real.exp (Λ * T))⁻¹ ≤ V := by
    rw [← Real.exp_neg]
    rwa [neg_mul] at hV
  have hs' : 2 * (Real.exp (Λ * T) * Real.exp (3 * T)) ≤ 3 ^ s := by
    rw [← Real.exp_add, show Λ * T + 3 * T = (Λ + 3) * T by ring]
    exact hs
  have h3s : (0 : ℝ) < 3 ^ s := by positivity
  have hWs : W / 3 ^ s ≤ (Real.exp (Λ * T))⁻¹ / 2 := by
    rw [div_le_iff₀ h3s]
    calc W ≤ Real.exp (3 * T) := hW
      _ = (Real.exp (Λ * T))⁻¹ / 2 * (2 * (Real.exp (Λ * T) * Real.exp (3 * T))) := by
        field_simp
      _ ≤ (Real.exp (Λ * T))⁻¹ / 2 * 3 ^ s :=
        mul_le_mul_of_nonneg_left hs' (by positivity)
  have hpow : (1 + β) ^ s ≤ (1 + (n : ℝ) ^ 2) ^ s :=
    pow_le_pow_left₀ (by linarith) (by linarith) s
  have hX0 : (0 : ℝ) ≤ X := Nat.cast_nonneg _
  have hmain : (1 + (n : ℝ) ^ 2) ^ s + 2 ≤ X * (V - W / 3 ^ s) := by
    calc (1 + (n : ℝ) ^ 2) ^ s + 2
        = 2 * ((1 + (n : ℝ) ^ 2) ^ s + 2) * Real.exp (Λ * T) *
            ((Real.exp (Λ * T))⁻¹ / 2) := by
          field_simp
      _ ≤ X * ((Real.exp (Λ * T))⁻¹ / 2) := mul_le_mul_of_nonneg_right hX (by positivity)
      _ ≤ X * (V - W / 3 ^ s) := mul_le_mul_of_nonneg_left (by linarith) hX0
  have hfin : (2 : ℝ) ≤
      (#{k ∈ range X | ∀ p ∈ (2 ^ n - 1).primeFactors, k % p ∉ Bad n p} : ℝ) := by
    linarith
  exact_mod_cast hfin

/-- An explicit bound: `K n ≤ exp (90 d(n) (log n)^3)` for `n ≥ 3`. -/
theorem K_bound : ∃ C : ℝ, ∀ᶠ n : ℕ in Filter.atTop,
    (Erdos820.K n : ℝ) ≤ Real.exp (C * (n.divisors.card : ℝ) * Real.log (n : ℝ) ^ 3) := by
  refine ⟨90, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop 3] with n hn
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  obtain ⟨L, hL⟩ : ∃ L, L = Real.log (n : ℝ) := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = (n.divisors.card : ℝ) := ⟨_, rfl⟩
  rw [← hD, ← hL]
  have hL1 : 1 ≤ L := by
    rw [hL, Real.le_log_iff_exp_le hn0]
    linarith [Real.exp_one_lt_d9]
  have hD1 : 1 ≤ D := by
    rw [hD]
    exact_mod_cast Finset.card_pos.2 ⟨1, Nat.one_mem_divisors.2 (by omega)⟩
  have hΛ0 : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg (by linarith)
  obtain ⟨Λ, hΛdef⟩ : ∃ Λ, Λ = Real.log ((n : ℝ) + 1) + 2 := ⟨_, rfl⟩
  obtain ⟨T, hTdef⟩ : ∃ T, T = D * (2 + L) := ⟨_, rfl⟩
  have hΛ4 : Λ ≤ 4 * L := by
    have h1 : Real.log ((n : ℝ) + 1) ≤ Real.log ((n : ℝ) ^ 2) :=
      Real.log_le_log (by linarith) (by nlinarith)
    rw [Real.log_pow] at h1
    push_cast at h1
    rw [← hL] at h1
    rw [hΛdef]
    linarith
  have hΛ2 : 2 ≤ Λ := by
    rw [hΛdef]
    linarith
  have hT0 : 0 ≤ T := by
    rw [hTdef]
    exact mul_nonneg (by linarith) (by linarith)
  have hT : T ≤ 3 * (D * L) := by
    rw [hTdef]
    nlinarith
  have hDL0 : 0 ≤ 3 * (D * L) := by
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ D) (by linarith : (0 : ℝ) ≤ L)
    linarith
  have hDL2 : 1 ≤ D * L ^ 2 := one_le_mul_of_one_le_of_one_le hD1 (one_le_pow₀ hL1)
  have hu : D * L ^ 2 ≤ D * L ^ 3 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL1 (by norm_num)) (by linarith)
  have hA : (Λ + 3) * T ≤ 21 * (D * L ^ 2) := by
    calc (Λ + 3) * T ≤ (7 * L) * (3 * (D * L)) := mul_le_mul (by linarith) hT hT0 (by linarith)
      _ = 21 * (D * L ^ 2) := by ring
  have hΛT : Λ * T ≤ 12 * (D * L ^ 2) := by
    calc Λ * T ≤ (4 * L) * (3 * (D * L)) := mul_le_mul hΛ4 hT hT0 (by linarith)
      _ = 12 * (D * L ^ 2) := by ring
  have hA0 : 0 ≤ (Λ + 3) * T := mul_nonneg (by linarith) hT0
  obtain ⟨s, hsdef⟩ : ∃ s, s = ⌈(Λ + 3) * T⌉₊ + 1 := ⟨_, rfl⟩
  have hs1 : (Λ + 3) * T + 1 ≤ s := by
    rw [hsdef]
    push_cast
    linarith [Nat.le_ceil ((Λ + 3) * T)]
  have hs2 : (s : ℝ) ≤ (Λ + 3) * T + 2 := by
    rw [hsdef]
    push_cast
    linarith [Nat.ceil_lt_add_one hA0]
  have hs : 2 * Real.exp ((Λ + 3) * T) ≤ 3 ^ s := by
    calc 2 * Real.exp ((Λ + 3) * T) ≤ Real.exp 1 * Real.exp ((Λ + 3) * T) :=
          mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp 1]) (Real.exp_pos _).le
      _ = Real.exp ((Λ + 3) * T + 1) := by rw [← Real.exp_add, add_comm]
      _ ≤ Real.exp (s : ℝ) := Real.exp_le_exp.2 hs1
      _ = Real.exp 1 ^ s := by rw [← Real.exp_nat_mul, mul_one]
      _ ≤ 3 ^ s := pow_le_pow_left₀ (Real.exp_pos 1).le (by linarith [Real.exp_one_lt_d9]) s
  obtain ⟨Z, hZdef⟩ : ∃ Z, Z = 2 * ((1 + (n : ℝ) ^ 2) ^ s + 2) * Real.exp (Λ * T) := ⟨_, rfl⟩
  have hZ0 : 0 ≤ Z := by
    rw [hZdef]
    positivity
  have hK : Erdos820.K n < ⌈Z⌉₊ :=
    K_lt_of n s ⌈Z⌉₊ (by omega) Λ T hΛdef (by rw [hTdef, hD, hL]) hs
      (by rw [← hZdef]; exact Nat.le_ceil Z)
  have hKZ : (Erdos820.K n : ℝ) ≤ Z := by
    have h1 : (Erdos820.K n : ℝ) + 1 ≤ ⌈Z⌉₊ := by exact_mod_cast hK
    linarith [Nat.ceil_lt_add_one hZ0]
  refine hKZ.trans ?_
  have hu1 : 1 ≤ D * L ^ 3 := hDL2.trans hu
  have hpow : (1 + (n : ℝ) ^ 2) ^ s ≤ Real.exp (69 * (D * L ^ 3)) := by
    have h1 : 1 + (n : ℝ) ^ 2 ≤ Real.exp (3 * L) := by
      have h2 : Real.exp (3 * L) = (n : ℝ) ^ 3 := by
        rw [show (3 : ℝ) * L = (3 : ℕ) * L by norm_num, Real.exp_nat_mul, hL, Real.exp_log hn0]
      rw [h2]
      nlinarith [mul_le_mul_of_nonneg_right hn3 (sq_nonneg (n : ℝ))]
    calc (1 + (n : ℝ) ^ 2) ^ s ≤ Real.exp (3 * L) ^ s := pow_le_pow_left₀ (by positivity) h1 s
      _ = Real.exp (s * (3 * L)) := (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp (69 * (D * L ^ 3)) := by
        apply Real.exp_le_exp.2
        have h2 : (s : ℝ) ≤ 23 * (D * L ^ 2) := by linarith
        calc (s : ℝ) * (3 * L) ≤ 23 * (D * L ^ 2) * (3 * L) :=
              mul_le_mul_of_nonneg_right h2 (by linarith)
          _ = 69 * (D * L ^ 3) := by ring
  have hE : Real.exp (Λ * T) ≤ Real.exp (12 * (D * L ^ 3)) := Real.exp_le_exp.2 (by linarith)
  have h69 : 1 ≤ Real.exp (69 * (D * L ^ 3)) := Real.one_le_exp (by linarith)
  rw [hZdef]
  calc 2 * ((1 + (n : ℝ) ^ 2) ^ s + 2) * Real.exp (Λ * T)
      ≤ 2 * (3 * Real.exp (69 * (D * L ^ 3))) * Real.exp (12 * (D * L ^ 3)) :=
        mul_le_mul (by linarith) hE (Real.exp_pos _).le (by positivity)
    _ = 6 * Real.exp (81 * (D * L ^ 3)) := by
        rw [show 81 * (D * L ^ 3) = 69 * (D * L ^ 3) + 12 * (D * L ^ 3) by ring, Real.exp_add]
        ring
    _ ≤ Real.exp 5 * Real.exp (81 * (D * L ^ 3)) :=
        mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp 5]) (Real.exp_pos _).le
    _ = Real.exp (5 + 81 * (D * L ^ 3)) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (90 * D * L ^ 3) := Real.exp_le_exp.2 (by nlinarith)

lemma div_log_eq_sum (n : ℕ) (hn : n ≠ 0) :
    Real.log n = ∑ p ∈ n.primeFactors, (n.factorization p : ℝ) * Real.log p := by
  have h : (n : ℝ) = ∏ p ∈ n.primeFactors, (p : ℝ) ^ n.factorization p := by
    exact_mod_cast Nat.prod_primeFactors_pow_factorization hn
  conv_lhs => rw [h]
  rw [Real.log_prod]
  · exact Finset.sum_congr rfl fun p _ => Real.log_pow _ _
  · intro p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
    positivity

lemma div_term_le (n : ℕ) (hn : n ≠ 0) (Y : ℕ) (hY : 0 < Real.log Y) (p : ℕ) (hp : p.Prime) :
    Real.log ((n.factorization p : ℝ) + 1) ≤
      (if p < Y then Real.log (1 + Real.log n / Real.log 2) else 0) +
        (n.factorization p : ℝ) * Real.log p * (Real.log 2 / Real.log Y) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hlp : Real.log 2 ≤ Real.log p := Real.log_le_log (by norm_num) hp2
  have ha0 : (0 : ℝ) ≤ n.factorization p := Nat.cast_nonneg _
  have hY0 : (0 : ℝ) < Y := by
    rcases Nat.eq_zero_or_pos Y with h | h
    · rw [h] at hY
      simp at hY
    · exact_mod_cast h
  split_ifs with h
  · have h1 : (n.factorization p : ℝ) * Real.log p ≤ Real.log n := by
      have h2 : ((p : ℝ) ^ n.factorization p) ≤ n := by exact_mod_cast Nat.ordProj_le p hn
      have h3 := Real.log_le_log (by positivity) h2
      rwa [Real.log_pow] at h3
    have h4 : (n.factorization p : ℝ) ≤ Real.log n / Real.log 2 := by
      rw [le_div_iff₀ hl2]
      nlinarith
    have h5 : Real.log ((n.factorization p : ℝ) + 1) ≤ Real.log (1 + Real.log n / Real.log 2) :=
      Real.log_le_log (by positivity) (by linarith)
    have h6 : 0 ≤ (n.factorization p : ℝ) * Real.log p * (Real.log 2 / Real.log Y) :=
      mul_nonneg (mul_nonneg ha0 (hl2.le.trans hlp)) (div_nonneg hl2.le hY.le)
    linarith
  · have hYp : (Y : ℝ) ≤ p := by exact_mod_cast not_lt.1 h
    have h1 : Real.log Y ≤ Real.log p := Real.log_le_log hY0 hYp
    have h2 : (n.factorization p : ℝ) + 1 ≤ 2 ^ n.factorization p := by
      exact_mod_cast Nat.succ_le_of_lt (n.factorization p).lt_two_pow_self
    have h3 : Real.log ((n.factorization p : ℝ) + 1) ≤ n.factorization p * Real.log 2 := by
      have h := Real.log_le_log (by positivity) h2
      rwa [Real.log_pow] at h
    have h4 : (n.factorization p : ℝ) * Real.log 2 ≤
        n.factorization p * Real.log p * (Real.log 2 / Real.log Y) := by
      rw [show (n.factorization p : ℝ) * Real.log p * (Real.log 2 / Real.log Y) =
        n.factorization p * Real.log 2 * (Real.log p / Real.log Y) by ring]
      have h5 : 1 ≤ Real.log p / Real.log Y := by rwa [le_div_iff₀ hY, one_mul]
      nlinarith [mul_nonneg ha0 hl2.le]
    linarith

lemma div_log_card_le (n : ℕ) (hn : n ≠ 0) (Y : ℕ) (hY : 0 < Real.log Y) :
    Real.log (n.divisors.card : ℝ) ≤
      Y * Real.log (1 + Real.log n / Real.log 2) + Real.log 2 / Real.log Y * Real.log n := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hM : 0 ≤ Real.log (1 + Real.log n / Real.log 2) := by
    apply Real.log_nonneg
    have h := div_nonneg (Real.log_natCast_nonneg n) hl2.le
    linarith
  have hcard : (n.divisors.card : ℝ) = ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1) := by
    rw [Nat.card_divisors hn]
    push_cast
    rfl
  have hfilter : (#(n.primeFactors.filter (· < Y)) : ℝ) ≤ Y := by
    have h := Finset.card_le_card (s := n.primeFactors.filter (· < Y)) (t := Finset.range Y)
      (fun p hp => Finset.mem_range.2 (Finset.mem_filter.1 hp).2)
    rw [Finset.card_range] at h
    exact_mod_cast h
  rw [hcard, Real.log_prod (fun p _ => by positivity)]
  calc ∑ p ∈ n.primeFactors, Real.log ((n.factorization p : ℝ) + 1)
      ≤ ∑ p ∈ n.primeFactors,
          ((if p < Y then Real.log (1 + Real.log n / Real.log 2) else 0) +
            (n.factorization p : ℝ) * Real.log p * (Real.log 2 / Real.log Y)) :=
        Finset.sum_le_sum fun p hp => div_term_le n hn Y hY p (Nat.prime_of_mem_primeFactors hp)
    _ = #(n.primeFactors.filter (· < Y)) * Real.log (1 + Real.log n / Real.log 2) +
          Real.log n * (Real.log 2 / Real.log Y) := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← div_log_eq_sum n hn, ← Finset.sum_filter,
          Finset.sum_const, nsmul_eq_mul]
    _ ≤ Y * Real.log (1 + Real.log n / Real.log 2) + Real.log 2 / Real.log Y * Real.log n := by
        have h := mul_le_mul_of_nonneg_right hfilter hM
        linarith

lemma div_analytic (L : ℝ) (hL : 3 ≤ L) :
    ∃ Y : ℕ, 0 < Real.log Y ∧
      Y * Real.log (1 + L / Real.log 2) + Real.log 2 / Real.log Y * L ≤ 34 * L / Real.log L := by
  have hL0 : 0 < L := by linarith
  have hx1 : 1 ≤ Real.log L := by
    rw [Real.le_log_iff_exp_le hL0]
    have h := Real.exp_one_lt_d9
    linarith
  have hrr : Real.exp (Real.log L / 2) * Real.exp (Real.log L / 2) = L := by
    rw [← Real.exp_add, add_halves, Real.exp_log hL0]
  have hr1 : 1 ≤ Real.exp (Real.log L / 2) := Real.one_le_exp (by linarith)
  have hrx : Real.log L ^ 2 ≤ 8 * Real.exp (Real.log L / 2) := by
    have h := Real.quadratic_le_exp_of_nonneg (show 0 ≤ Real.log L / 2 by linarith)
    nlinarith
  have hl2 : 1 / 2 ≤ Real.log 2 := by
    have h := Real.log_two_gt_d9
    linarith
  have hl2' : Real.log 2 ≤ 1 := by
    have h := Real.log_two_lt_d9
    linarith
  have hYr : Real.exp (Real.log L / 2) ≤ (⌈Real.exp (Real.log L / 2)⌉₊ : ℝ) := Nat.le_ceil _
  have hYr2 : (⌈Real.exp (Real.log L / 2)⌉₊ : ℝ) ≤ 2 * Real.exp (Real.log L / 2) := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ Real.exp (Real.log L / 2) by linarith)
    linarith
  have hlogY : Real.log L / 2 ≤ Real.log (⌈Real.exp (Real.log L / 2)⌉₊ : ℝ) := by
    have h := Real.log_le_log (by linarith) hYr
    rwa [Real.log_exp] at h
  have hM0 : 0 ≤ Real.log (1 + L / Real.log 2) := by
    apply Real.log_nonneg
    have h := div_nonneg hL0.le (by linarith : (0 : ℝ) ≤ Real.log 2)
    linarith
  have hM : Real.log (1 + L / Real.log 2) ≤ 2 * Real.log L := by
    have h0 : L / Real.log 2 ≤ 2 * L := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    have h1 : 1 + L / Real.log 2 ≤ L ^ 2 := by nlinarith
    have h1' : 0 < 1 + L / Real.log 2 := by
      have h := div_nonneg hL0.le (by linarith : (0 : ℝ) ≤ Real.log 2)
      linarith
    have h2 := Real.log_le_log h1' h1
    rw [Real.log_pow] at h2
    exact_mod_cast h2
  refine ⟨⌈Real.exp (Real.log L / 2)⌉₊, by linarith, ?_⟩
  generalize (⌈Real.exp (Real.log L / 2)⌉₊ : ℝ) = Y at *
  generalize Real.exp (Real.log L / 2) = r at *
  generalize Real.log (1 + L / Real.log 2) = M at *
  generalize Real.log L = x at *
  have hT1 : Y * M ≤ 32 * L / x := by
    rw [le_div_iff₀ (by linarith)]
    have h : Y * M ≤ 2 * r * (2 * x) := mul_le_mul hYr2 hM hM0 (by linarith)
    have h' := mul_le_mul_of_nonneg_right h (by linarith : (0 : ℝ) ≤ x)
    nlinarith
  have hT2 : Real.log 2 / Real.log Y * L ≤ 2 * L / x := by
    have h : Real.log 2 / Real.log Y ≤ 2 / x := by
      rw [div_le_div_iff₀ (by linarith) (by linarith)]
      nlinarith
    calc Real.log 2 / Real.log Y * L ≤ 2 / x * L := mul_le_mul_of_nonneg_right h hL0.le
      _ = 2 * L / x := by ring
  have hsum : 34 * L / x = 32 * L / x + 2 * L / x := by ring
  linarith

/-- The number of divisors of `n` is at most `n ^ (34 / log (log n))` for large `n`. -/
theorem divisor_bound : ∃ C : ℝ, ∀ᶠ n : ℕ in Filter.atTop,
    (n.divisors.card : ℝ) ≤ (n : ℝ) ^ (C / Real.log (Real.log (n : ℝ))) := by
  refine ⟨34, ?_⟩
  have h := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 3
  filter_upwards [h, Filter.eventually_gt_atTop 0] with n hn hn0
  simp only [Function.comp] at hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
  obtain ⟨Y, hY, hYb⟩ := div_analytic (Real.log n) hn
  have hlog := div_log_card_le n hn0.ne' Y hY
  have hd : (0 : ℝ) < n.divisors.card := by
    exact_mod_cast Finset.card_pos.2 ⟨1, Nat.one_mem_divisors.2 hn0.ne'⟩
  rw [Real.rpow_def_of_pos hnpos, ← Real.log_le_iff_le_exp hd]
  calc Real.log (n.divisors.card : ℝ)
      ≤ Y * Real.log (1 + Real.log n / Real.log 2) + Real.log 2 / Real.log Y * Real.log n := hlog
    _ ≤ 34 * Real.log n / Real.log (Real.log n) := hYb
    _ = Real.log n * (34 / Real.log (Real.log n)) := by ring

section Asymptotics

open Filter

lemma asym_absorb (C : ℝ) (hC : 1 ≤ C) :
    ∀ᶠ L : ℝ in atTop, C * L ^ 3 ≤ Real.exp (L / Real.log L) := by
  have cp : (0 : ℝ) < |Real.log C| + 3 := by positivity
  have small := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (show (0 : ℝ) < 1 by norm_num)).bound
    (div_pos one_pos cp)
  filter_upwards [small, Real.tendsto_log_atTop.eventually_ge_atTop 1, eventually_gt_atTop 0]
    with L h l1 L0
  change ‖(Real.log L) ^ (2 : ℝ)‖ ≤ 1 / (|Real.log C| + 3) * ‖L ^ (1 : ℝ)‖ at h
  rw [Real.rpow_two, Real.rpow_one, Real.norm_of_nonneg (sq_nonneg _),
    Real.norm_of_nonneg L0.le] at h
  have sm : (|Real.log C| + 3) * (Real.log L) ^ 2 ≤ L := by
    calc
      _ ≤ (|Real.log C| + 3) * (1 / (|Real.log C| + 3) * L) :=
        mul_le_mul_of_nonneg_left h cp.le
      _ = L := by field_simp
  change 1 ≤ Real.log L at l1
  have l0 : 0 < Real.log L := by linarith
  have coeff : Real.log C + 3 * Real.log L ≤ (|Real.log C| + 3) * Real.log L := by
    have hh := le_mul_of_one_le_right (abs_nonneg (Real.log C)) l1
    linarith [le_abs_self (Real.log C)]
  have C0 : 0 < C := by linarith
  have prodpos : 0 < C * L ^ 3 := by positivity
  rw [← Real.log_le_log_iff prodpos (Real.exp_pos _), Real.log_exp,
    Real.log_mul C0.ne' (by positivity), Real.log_pow]
  apply (le_div_iff₀ l0).2
  calc
    _ ≤ (|Real.log C| + 3) * Real.log L * Real.log L := by
      push_cast
      exact mul_le_mul_of_nonneg_right coeff l0.le
    _ = (|Real.log C| + 3) * (Real.log L) ^ 2 := by ring
    _ ≤ _ := sm

theorem main_of
    (h1 : ∃ C : ℝ, ∀ᶠ n : ℕ in Filter.atTop,
      (n.divisors.card : ℝ) ≤ (n : ℝ) ^ (C / Real.log (Real.log (n : ℝ))))
    (h2 : ∃ C : ℝ, ∀ᶠ n : ℕ in Filter.atTop,
      (Erdos820.K n : ℝ) ≤ Real.exp (C * (n.divisors.card : ℝ) * Real.log (n : ℝ) ^ 3)) :
    type_of% @Erdos820.erdos_820.variants.two_pow_upper := by
  obtain ⟨C1, h1⟩ := h1
  obtain ⟨C2, h2⟩ := h2
  refine ⟨max C1 0 + 1, by positivity, fun ε hε => ?_⟩
  have lim := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [h1, h2, lim.eventually (asym_absorb (max C2 1) (le_max_right _ _)),
    (Real.tendsto_log_atTop.comp lim).eventually_ge_atTop 1, eventually_ge_atTop 3]
    with n hd hK habs hl hn
  simp only [Function.comp_apply] at habs hl
  have n1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have npos : (0 : ℝ) < n := by linarith
  have L0 : 0 < Real.log (n : ℝ) := Real.log_pos n1
  have l0 : 0 < Real.log (Real.log (n : ℝ)) := by linarith
  have d0 : (0 : ℝ) ≤ (n.divisors.card : ℝ) := Nat.cast_nonneg _
  have hd' : (n.divisors.card : ℝ) ≤ (n : ℝ) ^ (max C1 0 / Real.log (Real.log (n : ℝ))) :=
    hd.trans (Real.rpow_le_rpow_of_exponent_le n1.le
      (div_le_div_of_nonneg_right (le_max_left _ _) l0.le))
  have habs' : max C2 1 * Real.log (n : ℝ) ^ 3 ≤
      (n : ℝ) ^ (1 / Real.log (Real.log (n : ℝ))) := by
    rw [Real.rpow_def_of_pos npos, mul_one_div]
    exact habs
  refine lt_of_le_of_lt hK (Real.exp_lt_exp.2 ?_)
  calc C2 * (n.divisors.card : ℝ) * Real.log (n : ℝ) ^ 3
      ≤ max C2 1 * (n.divisors.card : ℝ) * Real.log (n : ℝ) ^ 3 := by
        have := le_max_left C2 1
        gcongr
    _ = max C2 1 * Real.log (n : ℝ) ^ 3 * (n.divisors.card : ℝ) := by ring
    _ ≤ (n : ℝ) ^ (1 / Real.log (Real.log (n : ℝ))) *
        (n : ℝ) ^ (max C1 0 / Real.log (Real.log (n : ℝ))) :=
        mul_le_mul habs' hd' d0 (Real.rpow_nonneg npos.le _)
    _ = (n : ℝ) ^ ((1 + max C1 0) / Real.log (Real.log (n : ℝ))) := by
        rw [← Real.rpow_add npos, add_div]
    _ < (n : ℝ) ^ ((max C1 0 + 1 + ε) / Real.log (Real.log (n : ℝ))) :=
        Real.rpow_lt_rpow_of_exponent_lt n1 (div_lt_div_of_pos_right (by linarith) l0)

end Asymptotics

end OpenB820

theorem OMA.solution : OMA.R_Erdos820_erdos_820_variants_log_log_exponent_R1.H2 := by
  obtain ⟨c, -, h⟩ := OpenB820.main_of OpenB820.divisor_bound OpenB820.K_bound
  exact ⟨c + 1, h 1 one_pos⟩
