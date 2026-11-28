import FormalConjectures.ErdosProblems.«897»

-- Reduction Erdos897.erdos_897.variants.parts.ii.R1 of Erdős Problem 897 (variant, part ii)
-- Credit: @LordMike
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Erdős 897, ratio variant: split by the signs of `f` on the primes

The statement asks: if `f` is additive, `f (p ^ k) / log (p ^ k)` is unbounded above, and either
`f (p ^ k) = f p` for all `k` or `f (p ^ k) = k * f p` for all `k`, is `f (n + 1) / f n`
unbounded above?

Remarks on the formal statement.
* The first alternative is vacuous as formalised: `k = 0` gives `f p = f 1 = 0` for every prime,
  so `f (p ^ k) = 0` and the limsup hypothesis fails. Only the completely additive alternative
  carries content, and then `f (a * b) = f a + f b` for all positive `a`, `b`.
* The ratio is a quotient of real numbers (`EReal.coe_div`), so `f (n + 1) / f n = 0` when
  `f n = 0`, and a negative ratio never helps. The conclusion says: for every `C` there are
  arbitrarily large `n` with `C < f (n + 1) / f n`.

`main` splits on the signs of `f` on the primes.
* Every prime has `f p > 0`: hypothesis `H1` (open; the case Erdős had in mind).
* Some prime has `f q < 0`: hypothesis `H2` (open).
* `f ≥ 0` on the primes and `f q = 0` for a prime `q`: proved here (`zero_case`). Take an odd
  prime `p ≠ q` with `f p > 0` and a prime `r ≠ p` with `f r > 0`. Lemma `lift` gives `t` such
  that every `m ≡ -1 mod p ^ t` has, for every `j`, a power `q ^ a` with `p ^ j ∣ q ^ a * m + 1`
  (lifting the exponent for `q ^ (p - 1)`, correcting one `p`-adic digit at a time). Put
  `m = r ^ φ(p ^ t) * (2 * p ^ t - 1)`, so `p ^ t ∣ m + 1` and `f m > 0`. For `n = q ^ a * m`
  this gives `f n = f m` and `f (n + 1) ≥ j * f p`, so the ratio is at least `j * f p / f m`.

Hypotheses. Both are special cases of the target, restated without `EReal` and filters.
* `H1` (open): the target for completely additive `f` that is positive at every prime.
* `H2` (open): the target for completely additive `f` that is negative at some prime.
-/

namespace OMA.R_Erdos897_erdos_897_variants_parts_ii_R1

open Real Filter

/-- Open: the positive case. A completely additive `f`, positive on the primes, with
`f p / log p` unbounded above has `f (n + 1) / f n` unbounded above. -/
def H1 : Prop :=
  ∀ f : ℕ → ℝ,
    (∀ a b : ℕ, 0 < a → 0 < b → f (a * b) = f a + f b) →
    (∀ p : ℕ, p.Prime → 0 < f p) →
    (∀ K : ℝ, ∃ p : ℕ, p.Prime ∧ K * Real.log p < f p) →
    ∀ (C : ℝ) (N : ℕ), ∃ n : ℕ, N ≤ n ∧ C < f (n + 1) / f n

/-- Open: the case with a negative value. A completely additive `f`, negative at some prime,
with `f p / log p` unbounded above has `f (n + 1) / f n` unbounded above. -/
def H2 : Prop :=
  ∀ f : ℕ → ℝ,
    (∀ a b : ℕ, 0 < a → 0 < b → f (a * b) = f a + f b) →
    (∃ q : ℕ, q.Prime ∧ f q < 0) →
    (∀ K : ℝ, ∃ p : ℕ, p.Prime ∧ K * Real.log p < f p) →
    ∀ (C : ℝ) (N : ℕ), ∃ n : ℕ, N ≤ n ∧ C < f (n + 1) / f n

/-- `(G - 1) ^ 2` divides `G ^ k - 1 - k * (G - 1)`. -/
lemma sq_dvd_pow_sub (G : ℤ) (k : ℕ) : (G - 1) ^ 2 ∣ G ^ k - 1 - k * (G - 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : G ^ (k + 1) - 1 - ((k + 1 : ℕ) : ℤ) * (G - 1)
        = G * (G ^ k - 1 - k * (G - 1)) + k * (G - 1) ^ 2 := by
      push_cast
      ring
    rw [e]
    exact dvd_add (dvd_mul_of_dvd_right ih _) (dvd_mul_left _ _)

/-- One step of the lifting: correct one `p`-adic digit by a power of `G`. -/
lemma lift_step (p : ℕ) [Fact p.Prime] (j : ℕ) (hj : 1 ≤ j) (G X : ℤ)
    (hG : (p : ℤ) ^ j ∣ G - 1) (hG' : ¬ (p : ℤ) ^ (j + 1) ∣ G - 1) (hX : (p : ℤ) ^ j ∣ X) :
    ∃ k : ℕ, (p : ℤ) ^ (j + 1) ∣ (X - 1) * G ^ k + 1 := by
  obtain ⟨u, hu⟩ := hG
  obtain ⟨z, hz⟩ := hX
  have hpu : ¬ (p : ℤ) ∣ u := by
    rintro ⟨u', hu'⟩
    exact hG' ⟨u', by rw [hu, hu', pow_succ]; ring⟩
  have hu0 : (u : ZMod p) ≠ 0 := by
    intro h
    exact hpu ((ZMod.intCast_zmod_eq_zero_iff_dvd u p).1 h)
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ZMod p) = (z : ZMod p) * (u : ZMod p)⁻¹ :=
    ⟨_, ZMod.natCast_zmod_val _⟩
  have hdiv : (p : ℤ) ∣ z - k * u := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1
    push_cast
    rw [hk, inv_mul_cancel_right₀ hu0, sub_self]
  refine ⟨k, ?_⟩
  have hsq : (p : ℤ) ^ (j + 1) ∣ (G - 1) ^ 2 := by
    rw [hu, mul_pow, ← pow_mul]
    exact dvd_mul_of_dvd_left (pow_dvd_pow _ (by omega)) _
  have hA : (p : ℤ) ^ (j + 1) ∣ G ^ k - 1 - k * (G - 1) := hsq.trans (sq_dvd_pow_sub G k)
  have hGk : (p : ℤ) ^ j ∣ G ^ k - 1 := by
    have h1 : G - 1 ∣ G ^ k - 1 - k * (G - 1) :=
      (dvd_pow_self _ two_ne_zero).trans (sq_dvd_pow_sub G k)
    have h2 : G - 1 ∣ G ^ k - 1 := by
      have := dvd_add h1 (dvd_mul_left (G - 1) (k : ℤ))
      simpa using this
    exact (Dvd.intro u hu.symm).trans h2
  have hXG : (p : ℤ) ^ (j + 1) ∣ X * (G ^ k - 1) := by
    have h1 : (p : ℤ) ^ j * (p : ℤ) ^ j ∣ X * (G ^ k - 1) :=
      mul_dvd_mul (Dvd.intro z hz.symm) hGk
    refine dvd_trans ?_ h1
    rw [← pow_add]
    exact pow_dvd_pow _ (by omega)
  have hrem : (p : ℤ) ^ (j + 1) ∣ X - k * (G - 1) := by
    have e : X - k * (G - 1) = (p : ℤ) ^ j * (z - k * u) := by rw [hz, hu]; ring
    rw [e, pow_succ]
    exact mul_dvd_mul_left _ hdiv
  have e : (X - 1) * G ^ k + 1
      = (X - k * (G - 1)) + X * (G ^ k - 1) - (G ^ k - 1 - k * (G - 1)) := by ring
  rw [e]
  exact dvd_sub (dvd_add hrem hXG) hA

/-- Lifting: for an odd prime `p` and a prime `q ≠ p` there is `t` such that every `m` with
`m ≡ -1 mod p ^ t` has, for every `j`, a power `q ^ a` with `q ^ a * m ≡ -1 mod p ^ j`. -/
lemma lift (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hp2 : p ≠ 2) (hpq : p ≠ q) :
    ∃ t : ℕ, ∀ m : ℕ, p ^ t ∣ m + 1 → ∀ j : ℕ, ∃ a : ℕ, p ^ j ∣ q ^ a * m + 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨g, hgdef⟩ : ∃ g : ℕ, g = q ^ (p - 1) := ⟨_, rfl⟩
  have hcop : Nat.Coprime q p := (Nat.coprime_primes hq hp).2 (Ne.symm hpq)
  have hg1 : g ≡ 1 [MOD p] := by
    have := Nat.ModEq.pow_totient hcop
    rwa [Nat.totient_prime hp, ← hgdef] at this
  have hg_gt : 1 < g := by
    rw [hgdef]
    exact Nat.one_lt_pow (by have := hp.two_le; omega) hq.one_lt
  have hpg : p ∣ g - 1 := (Nat.modEq_iff_dvd' hg_gt.le).1 hg1.symm
  have hpng : ¬ p ∣ g := by
    intro h
    rw [hgdef] at h
    exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).1 (hp.dvd_of_dvd_pow h))
  have hval : ∀ k : ℕ, padicValNat p (g ^ (p ^ k) - 1) = padicValNat p (g - 1) + k := by
    intro k
    have := padicValNat.pow_sub_pow hodd hg_gt hpg hpng (n := p ^ k) (pow_ne_zero _ hp.ne_zero)
    simpa [padicValNat.prime_pow] using this
  have hgk : ∀ k : ℕ, 1 < g ^ (p ^ k) := fun k =>
    Nat.one_lt_pow (pow_ne_zero _ hp.ne_zero) hg_gt
  have ht1 : 1 ≤ padicValNat p (g - 1) := by
    have h := (padicValNat_dvd_iff_le (p := p) (n := 1) (a := g - 1) (by omega)).1
      (by simpa using hpg)
    exact h
  refine ⟨padicValNat p (g - 1), fun m hm j => ?_⟩
  have hall : ∀ i : ℕ, ∃ a : ℕ, p ^ (padicValNat p (g - 1) + i) ∣ q ^ a * m + 1 := by
    intro i
    induction i with
    | zero => exact ⟨0, by simpa using hm⟩
    | succ i ih =>
      obtain ⟨a, ha⟩ := ih
      have hne : g ^ (p ^ i) - 1 ≠ 0 := by have := hgk i; omega
      have hd1 : p ^ (padicValNat p (g - 1) + i) ∣ g ^ (p ^ i) - 1 :=
        (padicValNat_dvd_iff_le hne).2 (by rw [hval i])
      have hd2 : ¬ p ^ (padicValNat p (g - 1) + i + 1) ∣ g ^ (p ^ i) - 1 := by
        intro h
        have := (padicValNat_dvd_iff_le hne).1 h
        rw [hval i] at this
        omega
      have hcast : ((g ^ (p ^ i) - 1 : ℕ) : ℤ) = (g : ℤ) ^ (p ^ i) - 1 := by
        rw [Nat.cast_sub (hgk i).le]
        push_cast
        ring
      have hG : (p : ℤ) ^ (padicValNat p (g - 1) + i) ∣ (g : ℤ) ^ (p ^ i) - 1 := by
        rw [← hcast]
        exact_mod_cast Int.natCast_dvd_natCast.2 hd1
      have hG' : ¬ (p : ℤ) ^ (padicValNat p (g - 1) + i + 1) ∣ (g : ℤ) ^ (p ^ i) - 1 := by
        rw [← hcast]
        intro h
        exact hd2 (Int.natCast_dvd_natCast.1 (by exact_mod_cast h))
      have hX : (p : ℤ) ^ (padicValNat p (g - 1) + i) ∣ ((q : ℤ) ^ a * m + 1) := by
        exact_mod_cast Int.natCast_dvd_natCast.2 ha
      obtain ⟨k, hk⟩ := lift_step p (padicValNat p (g - 1) + i) (by omega)
        ((g : ℤ) ^ (p ^ i)) ((q : ℤ) ^ a * m + 1) hG hG' hX
      refine ⟨a + (p - 1) * p ^ i * k, ?_⟩
      apply Int.natCast_dvd_natCast.1
      have e : ((q ^ (a + (p - 1) * p ^ i * k) * m + 1 : ℕ) : ℤ)
          = ((q : ℤ) ^ a * m + 1 - 1) * ((g : ℤ) ^ (p ^ i)) ^ k + 1 := by
        rw [hgdef]
        push_cast
        rw [pow_add, pow_mul, pow_mul]
        ring
      rw [e]
      exact_mod_cast hk
  obtain ⟨a, ha⟩ := hall j
  exact ⟨a, (pow_dvd_pow p (Nat.le_add_left j _)).trans ha⟩

/-- An additive function with `f (p ^ k) = k * f p` is given by the factorization. -/
lemma f_formula (f : ℕ → ℝ)
    (hadd : ∀ a b : ℕ, 0 < a → 0 < b → a.Coprime b → f (a * b) = f a + f b)
    (hpow : ∀ k p : ℕ, p.Prime → f (p ^ k) = k * f p) :
    ∀ n : ℕ, n ≠ 0 → f n = n.factorization.sum (fun p k => (k : ℝ) * f p) := by
  have hf1 : f 1 = 0 := by
    have := hadd 1 1 one_pos one_pos (Nat.coprime_one_left 1)
    simp at this
    linarith
  intro n
  refine Nat.recOnPosPrimePosCoprime ?_ ?_ ?_ ?_ n
  · intro p k hp _ _
    rw [hp.factorization_pow, Finsupp.sum_single_index (by simp)]
    exact hpow k p hp
  · intro h
    exact absurd rfl h
  · intro _
    rw [Nat.factorization_one, Finsupp.sum_zero_index]
    exact hf1
  · intro a b ha hb hab iha ihb _
    have ha0 : a ≠ 0 := by omega
    have hb0 : b ≠ 0 := by omega
    rw [Nat.factorization_mul_of_coprime hab,
      Finsupp.sum_add_index' (by intro p; simp) (by intro p k₁ k₂; push_cast; ring),
      ← iha ha0, ← ihb hb0]
    exact hadd a b (by omega) (by omega) hab

/-- Powers under complete additivity. -/
lemma ca_pow (f : ℕ → ℝ)
    (hca : ∀ a b : ℕ, 0 < a → 0 < b → f (a * b) = f a + f b)
    (a : ℕ) (ha : 0 < a) (k : ℕ) : f (a ^ k) = k * f a := by
  have hf1 : f 1 = 0 := by
    have := hca 1 1 one_pos one_pos
    simp at this
    linarith
  induction k with
  | zero => simp [hf1]
  | succ k ih =>
    rw [pow_succ, hca _ _ (pow_pos ha k) ha, ih]
    push_cast
    ring

/-- The case `f ≥ 0` with a zero at a prime, from the lifting statement. -/
lemma zero_case (f : ℕ → ℝ)
    (hca : ∀ a b : ℕ, 0 < a → 0 < b → f (a * b) = f a + f b)
    (hnn : ∀ n : ℕ, n ≠ 0 → 0 ≤ f n)
    (q₀ : ℕ) (hq₀ : q₀.Prime) (hz : f q₀ = 0)
    (hunb : ∀ K : ℝ, ∃ p : ℕ, p.Prime ∧ K * Real.log p < f p) :
    ∀ (C : ℝ) (N : ℕ), ∃ n : ℕ, N ≤ n ∧ C < f (n + 1) / f n := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨p, hp, hpK⟩ := hunb (max (f 2 / Real.log 2) 0)
  have hlp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hfp : 0 < f p := lt_of_le_of_lt (mul_nonneg (le_max_right _ _) hlp.le) hpK
  have hp2 : p ≠ 2 := by
    intro h
    rw [h] at hpK
    simp only [Nat.cast_ofNat] at hpK
    have h2 : f 2 / Real.log 2 * Real.log 2 ≤ max (f 2 / Real.log 2) 0 * Real.log 2 :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hl2.le
    rw [div_mul_cancel₀ _ hl2.ne'] at h2
    linarith
  have hpq : p ≠ q₀ := by
    intro h
    rw [h] at hfp
    linarith
  obtain ⟨r, hr, hrK⟩ := hunb (max (f p / Real.log p) 0)
  have hlr : 0 < Real.log r := Real.log_pos (by exact_mod_cast hr.one_lt)
  have hfr : 0 < f r := lt_of_le_of_lt (mul_nonneg (le_max_right _ _) hlr.le) hrK
  have hrp : r ≠ p := by
    intro h
    rw [h] at hrK
    have h2 : f p / Real.log p * Real.log p ≤ max (f p / Real.log p) 0 * Real.log p :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hlp.le
    rw [div_mul_cancel₀ _ hlp.ne'] at h2
    linarith
  obtain ⟨t, ht⟩ := lift p q₀ hp hq₀ hp2 hpq
  have hP : 0 < p ^ t := pow_pos hp.pos t
  have hcop : Nat.Coprime r (p ^ t) :=
    Nat.Coprime.pow_right t ((Nat.coprime_primes hr hp).2 hrp)
  have hdvd : p ^ t ∣ r ^ Nat.totient (p ^ t) * (2 * p ^ t - 1) + 1 := by
    have e1 : r ^ Nat.totient (p ^ t) ≡ 1 [MOD p ^ t] := Nat.ModEq.pow_totient hcop
    have e2 : r ^ Nat.totient (p ^ t) * (2 * p ^ t - 1) + 1
        ≡ 1 * (2 * p ^ t - 1) + 1 [MOD p ^ t] := (e1.mul_right _).add_right 1
    have e3 : 1 * (2 * p ^ t - 1) + 1 = 2 * p ^ t := by omega
    rw [e3] at e2
    exact (Nat.modEq_zero_iff_dvd).1
      (e2.trans ((Nat.modEq_zero_iff_dvd).2 (dvd_mul_left _ _)))
  have hw : 0 < 2 * p ^ t - 1 := by omega
  have hrpow : 0 < r ^ Nat.totient (p ^ t) := pow_pos hr.pos _
  have hmpos : 0 < r ^ Nat.totient (p ^ t) * (2 * p ^ t - 1) := Nat.mul_pos hrpow hw
  have hfm : 0 < f (r ^ Nat.totient (p ^ t) * (2 * p ^ t - 1)) := by
    rw [hca _ _ hrpow hw, ca_pow f hca r hr.pos]
    have h1' : (0 : ℝ) < (Nat.totient (p ^ t) : ℝ) := by
      exact_mod_cast Nat.totient_pos.2 hP
    have h2' : 0 ≤ f (2 * p ^ t - 1) := hnn _ (by omega)
    have h3' : 0 < (Nat.totient (p ^ t) : ℝ) * f r := mul_pos h1' hfr
    linarith
  intro C N
  obtain ⟨j₀, hj₀⟩ := exists_nat_gt (C * f (r ^ Nat.totient (p ^ t) * (2 * p ^ t - 1)) / f p)
  obtain ⟨a, s, hs⟩ := ht _ hdvd (max j₀ (N + 1))
  refine ⟨q₀ ^ a * (r ^ Nat.totient (p ^ t) * (2 * p ^ t - 1)), ?_, ?_⟩
  · have hle : p ^ (max j₀ (N + 1)) ≤
        q₀ ^ a * (r ^ Nat.totient (p ^ t) * (2 * p ^ t - 1)) + 1 :=
      Nat.le_of_dvd (Nat.succ_pos _) ⟨s, hs⟩
    have h2j : max j₀ (N + 1) < 2 ^ (max j₀ (N + 1)) := Nat.lt_two_pow_self
    have hpj : 2 ^ (max j₀ (N + 1)) ≤ p ^ (max j₀ (N + 1)) :=
      Nat.pow_le_pow_left hp.two_le _
    have hN : N + 1 ≤ max j₀ (N + 1) := le_max_right _ _
    omega
  · have hs0 : 0 < s := by
      rcases Nat.eq_zero_or_pos s with h | h
      · rw [h] at hs
        simp at hs
      · exact h
    have hfn : f (q₀ ^ a * (r ^ Nat.totient (p ^ t) * (2 * p ^ t - 1)))
        = f (r ^ Nat.totient (p ^ t) * (2 * p ^ t - 1)) := by
      rw [hca _ _ (pow_pos hq₀.pos a) hmpos, ca_pow f hca q₀ hq₀.pos, hz]
      ring
    have hfn1 : f (q₀ ^ a * (r ^ Nat.totient (p ^ t) * (2 * p ^ t - 1)) + 1)
        = (max j₀ (N + 1) : ℕ) * f p + f s := by
      rw [hs, hca _ _ (pow_pos hp.pos _) hs0, ca_pow f hca p hp.pos]
    rw [hfn, hfn1, lt_div_iff₀ hfm]
    have hj : C * f (r ^ Nat.totient (p ^ t) * (2 * p ^ t - 1)) / f p
        < (max j₀ (N + 1) : ℕ) :=
      lt_of_lt_of_le hj₀ (by exact_mod_cast le_max_left j₀ (N + 1))
    rw [div_lt_iff₀ hfp] at hj
    have hfs := hnn s hs0.ne'
    linarith

theorem main : H1 → H2 → type_of% @Erdos897.erdos_897.variants.parts.ii := by
  intro h1 h2 f hadd hlim hcase
  have hf1 : f 1 = 0 := by
    have := hadd 1 one_pos 1 one_pos (Nat.coprime_one_left 1)
    simp at this
    linarith
  -- unboundedness extracted from the limsup hypothesis
  have hfreq : ∀ K : ℝ, ∃ p k : ℕ, p.Prime ∧
      ((K : ℝ) : EReal) < (f (p ^ k) / Real.log ((p : ℝ) ^ k) : EReal) := by
    intro K
    by_contra hcon
    have hev : ∀ᶠ x : ℕ × ℕ in atTop ⊓ 𝓟 {(p, k) : ℕ × ℕ | p.Prime},
        (f (x.1 ^ x.2) / Real.log ((x.1 : ℝ) ^ x.2) : EReal) ≤ (K : EReal) := by
      have hmem : {(p, k) : ℕ × ℕ | p.Prime} ∈ atTop ⊓ 𝓟 {(p, k) : ℕ × ℕ | p.Prime} :=
        mem_inf_of_right (mem_principal_self _)
      filter_upwards [hmem] with x hx
      by_contra hlt
      exact hcon ⟨x.1, x.2, hx, not_le.mp hlt⟩
    have := Filter.limsup_le_of_le (h := hev)
    rw [hlim] at this
    exact absurd this (by simp)
  have hpowcase : ∀ k p : ℕ, p.Prime → f (p ^ k) = k * f p := by
    rcases hcase with hc | hc
    · exfalso
      obtain ⟨p, k, hp, hlt⟩ := hfreq 0
      have h0 : f (p ^ k) = 0 := by
        rw [hc k p hp, ← hc 0 p hp, pow_zero, hf1]
      rw [h0] at hlt
      simp at hlt
    · exact hc
  have hunb : ∀ K : ℝ, ∃ p : ℕ, p.Prime ∧ K * Real.log p < f p := by
    intro K
    obtain ⟨p, k, hp, hlt⟩ := hfreq (max K 0)
    refine ⟨p, hp, ?_⟩
    have hlp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
    rw [hpowcase k p hp, Real.log_pow] at hlt
    rw [← EReal.coe_div] at hlt
    have hlt' : max K 0 < (k * f p) / (k * Real.log p) := by exact_mod_cast hlt
    have hK : K * Real.log p ≤ max K 0 * Real.log p :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hlp.le
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      simp at hlt'
    · have hk' : (0 : ℝ) < k := by exact_mod_cast hk
      have : (k * f p) / (k * Real.log p) = f p / Real.log p := by
        field_simp
      rw [this, lt_div_iff₀ hlp] at hlt'
      linarith
  have hadd' : ∀ a b : ℕ, 0 < a → 0 < b → a.Coprime b → f (a * b) = f a + f b :=
    fun a b ha hb hab => hadd a ha b hb hab
  have hform := f_formula f hadd' hpowcase
  have hca : ∀ a b : ℕ, 0 < a → 0 < b → f (a * b) = f a + f b := by
    intro a b ha hb
    rw [hform _ (Nat.mul_ne_zero ha.ne' hb.ne'), hform a ha.ne', hform b hb.ne',
      Nat.factorization_mul ha.ne' hb.ne',
      Finsupp.sum_add_index' (by intro p; simp) (by intro p k₁ k₂; push_cast; ring)]
  have key : ∀ (C : ℝ) (N : ℕ), ∃ n : ℕ, N ≤ n ∧ C < f (n + 1) / f n := by
    by_cases hneg : ∃ q : ℕ, q.Prime ∧ f q < 0
    · exact h2 f hca hneg hunb
    by_cases hpos : ∀ p : ℕ, p.Prime → 0 < f p
    · exact h1 f hca hpos hunb
    push Not at hneg hpos
    obtain ⟨q₀, hq₀, hle⟩ := hpos
    have hz : f q₀ = 0 := le_antisymm hle (hneg q₀ hq₀)
    have hnn : ∀ n : ℕ, n ≠ 0 → 0 ≤ f n := by
      intro n hn
      rw [hform n hn, Finsupp.sum]
      refine Finset.sum_nonneg fun p hp => ?_
      rw [Nat.support_factorization] at hp
      exact mul_nonneg (Nat.cast_nonneg _) (hneg p (Nat.prime_of_mem_primeFactors hp))
    exact zero_case f hca hnn q₀ hq₀ hz hunb
  by_contra hne
  have hlt : Filter.atTop.limsup (fun n : ℕ => (f (n + 1) / f n : EReal)) < ⊤ :=
    lt_top_iff_ne_top.mpr hne
  obtain ⟨C, hC1, -⟩ := EReal.lt_iff_exists_real_btwn.mp hlt
  have hev := Filter.eventually_lt_of_limsup_lt hC1
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hev
  obtain ⟨n, hn, hC⟩ := key C N₀
  have h := hN₀ n hn
  rw [← EReal.coe_div] at h
  have h' : f (n + 1) / f n < C := by exact_mod_cast h
  linarith

end OMA.R_Erdos897_erdos_897_variants_parts_ii_R1
