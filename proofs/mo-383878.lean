import OMAStatements.S_mo_383878

-- Problem: Number of divisors of $2^k+1$
-- Upstream: formal-conjectures statements/mo-383878.lean:0 (declaration OMA.S_mo_383878.main)
-- Credit: @JamesSlash (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
--
-- Proof idea: for every subset S of the n primes, d = prod_{i in S} p_i is odd, so by Bang's
-- theorem (Zsigmondy for base 2) there is a prime q_S with ord_{q_S}(2) = 2 d. Then q_S divides
-- 2^d + 1, hence 2^k + 1, and the 2^n primes q_S are pairwise distinct. So 2^k + 1 has at least
-- 2^n distinct prime factors and at least 2^(2^n) >= (n + 1) 2^(2^n - n) divisors.
--
-- The lemmas from P_lemma to zsigmondy (Bang's theorem: a prime of order n for every n >= 7) are
-- taken from the merged proof proofs/Erdos977.erdos_977.variants.schinzel.lean
-- (PR #3563, @sebastianbachmaier), with the largest prime factor restated as maxPF so that only
-- Mathlib is needed. The rest is new.

open Polynomial

namespace OMAmo383878

/-- The largest prime factor of `n` (`0` when there is none). -/
def maxPF (n : ℕ) : ℕ := n.primeFactors.sup id

lemma maxPF_mem {n : ℕ} (h : 1 < n) : maxPF n ∈ n.primeFactors := by
  have hne : n.primeFactors.Nonempty := Nat.nonempty_primeFactors.2 h
  obtain ⟨x, hx, hx'⟩ := Finset.exists_mem_eq_sup n.primeFactors hne id
  rw [maxPF, hx']
  exact hx

lemma prime_maxPF (n : ℕ) (h : 1 < n) : (maxPF n).Prime :=
  (Nat.mem_primeFactors.1 (maxPF_mem h)).1

lemma maxPF_dvd {n : ℕ} (h : 1 < n) : maxPF n ∣ n :=
  (Nat.mem_primeFactors.1 (maxPF_mem h)).2.1

lemma le_maxPF {n p : ℕ} (hn : n ≠ 0) (hp : p.Prime) (hpn : p ∣ n) : p ≤ maxPF n :=
  Finset.le_sup (f := id) (Nat.mem_primeFactors.2 ⟨hp, hpn, hn⟩)

lemma two_pow_dvd_of_orderOf {q d : ℕ} [Fact q.Prime] (h : orderOf (2 : ZMod q) = d) :
    q ∣ 2 ^ d - 1 := by
  have h1 : (2 : ZMod q) ^ d = 1 := by rw [← h]; exact pow_orderOf_eq_one 2
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub Nat.one_le_two_pow, Nat.cast_pow]
  simp [h1]

lemma dvd_sub_one_of_orderOf {q d : ℕ} [Fact q.Prime] (h : orderOf (2 : ZMod q) = d)
    (hd : 0 < d) : d ∣ q - 1 := by
  have h1 : (2 : ZMod q) ^ d = 1 := by rw [← h]; exact pow_orderOf_eq_one 2
  rw [← h]
  apply ZMod.orderOf_dvd_card_sub_one
  intro h0
  rw [h0, zero_pow hd.ne'] at h1
  exact zero_ne_one h1

lemma P_lemma (a : ℤ) (ha : 2 ≤ |a|) (m q : ℕ) (hm : 0 < m) (hq : q.Prime) (hq2 : q ≠ 2)
    (hqm : q ∣ m) (hqd : (q : ℤ) ∣ eval a (cyclotomic m ℤ)) :
    (∀ t, t.Prime → t ∣ m → t ≤ q) ∧ ¬ ((q : ℤ) ^ 2 ∣ eval a (cyclotomic m ℤ)) := by
  haveI := Fact.mk hq
  obtain ⟨s, m', hm'q, hmeq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm.ne' q hq.one_lt.ne'
  have hm'0 : m' ≠ 0 := by rintro rfl; simp at hmeq; omega
  haveI : NeZero (m' : ZMod q) := ⟨by rw [Ne, ZMod.natCast_eq_zero_iff]; exact hm'q⟩
  have hroot : IsRoot (cyclotomic (q ^ s * m') (ZMod q)) (a : ZMod q) := by
    rw [IsRoot.def, ← hmeq]
    have := cyclotomic.eval_apply a m (Int.castRingHom (ZMod q))
    simp only [eq_intCast] at this
    rw [this, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hqd
  have hprim : IsPrimitiveRoot (a : ZMod q) m' :=
    (isRoot_cyclotomic_prime_pow_mul_iff_of_charP).1 hroot
  have ha0 : (a : ZMod q) ≠ 0 := hprim.ne_zero hm'0
  have hdvd : m' ∣ q - 1 := by
    rw [hprim.eq_orderOf]; exact ZMod.orderOf_dvd_card_sub_one ha0
  have hm'le : m' ≤ q - 1 := Nat.le_of_dvd (by have := hq.two_le; omega) hdvd
  refine ⟨fun t ht htm => ?_, ?_⟩
  · rw [hmeq] at htm
    rcases (Nat.Prime.dvd_mul ht).1 htm with h | h
    · exact le_of_eq ((Nat.prime_dvd_prime_iff_eq ht hq).1 (ht.dvd_of_dvd_pow h))
    · have := Nat.le_of_dvd (Nat.pos_of_ne_zero hm'0) h; omega
  · have hs : s ≠ 0 := by
      rintro rfl; simp at hmeq; exact hm'q (hmeq ▸ hqm)
    have hmd : m = (q ^ (s - 1) * m') * q := by
      rw [hmeq]
      obtain ⟨s', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hs
      simp [pow_succ]; ring
    have hdpos : 0 < q ^ (s - 1) * m' := by
      have := hq.pos; positivity
    have hb1 : (q : ℤ) ∣ a ^ (q ^ (s - 1) * m') - 1 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [mul_comm, pow_mul, hprim.pow_eq_one, one_pow, sub_self]
    obtain ⟨c, hc⟩ := hb1
    have hbne : a ^ (q ^ (s - 1) * m') - 1 ≠ 0 := by
      intro h0
      have h2 : |a ^ (q ^ (s - 1) * m')| = |a| ^ (q ^ (s - 1) * m') := abs_pow _ _
      have h3 : (2:ℤ) ≤ |a| ^ (q ^ (s - 1) * m') :=
        le_trans ha (le_self_pow₀ (by linarith) hdpos.ne')
      rw [show a ^ (q ^ (s - 1) * m') = 1 by linarith] at h2
      simp at h2; linarith
    have hdiv : (a ^ (q ^ (s - 1) * m') - 1) * eval a (cyclotomic m ℤ) ∣
        (a ^ (q ^ (s - 1) * m')) ^ q - 1 := by
      have hmem : q ^ (s - 1) * m' ∈ m.properDivisors := by
        rw [Nat.mem_properDivisors]; refine ⟨⟨q, hmd⟩, ?_⟩
        rw [hmd]; have := hq.two_le
        nlinarith
      have := eval_dvd (x := a) (X_pow_sub_one_mul_cyclotomic_dvd_X_pow_sub_one_of_dvd ℤ hmem)
      rw [← pow_mul, ← hmd]
      simpa [eval_mul, eval_sub, eval_pow, eval_X, eval_one] using this
    have hS : eval a (cyclotomic m ℤ) ∣ ∑ i ∈ Finset.range q, (a ^ (q ^ (s - 1) * m')) ^ i := by
      have hgeom : (a ^ (q ^ (s - 1) * m')) ^ q - 1 = (a ^ (q ^ (s - 1) * m') - 1) *
          ∑ i ∈ Finset.range q, (a ^ (q ^ (s - 1) * m')) ^ i := by
        rw [← geom_sum_mul]; ring
      rw [hgeom] at hdiv
      exact (mul_dvd_mul_iff_left hbne).1 hdiv
    have key := odd_sq_dvd_geom_sum₂_sub (R := ℤ) 1 c (hq.odd_of_ne_two hq2)
    simp only [one_pow, mul_one] at key
    rw [show (1:ℤ) + q * c = a ^ (q ^ (s - 1) * m') by linarith] at key
    intro hsq
    have h3 : (q:ℤ) ^ 2 ∣ (q : ℤ) := by
      have := (dvd_sub (hsq.trans hS) key)
      simpa using this
    have h4 : q ^ 2 ∣ q := by exact_mod_cast h3
    have := Nat.le_of_dvd hq.pos h4
    have := hq.two_le
    nlinarith

lemma le_of_prime_factors (N n e : ℕ) (hN : 1 < N) (hn : 0 < n)
    (h : ∀ q, q.Prime → q ∣ N → q ∣ n ∧ (∀ t, t.Prime → t ∣ n → t ≤ q) ∧ N.factorization q ≤ e) :
    N ≤ (maxPF n) ^ e := by
  obtain ⟨q, hq, hqN⟩ := Nat.exists_prime_and_dvd hN.ne'
  obtain ⟨hqn, hqmax, hqe⟩ := h q hq hqN
  have huniq : ∀ {d : ℕ}, d.Prime → d ∣ N → d = q := by
    intro d hd hdN
    obtain ⟨hdn, hdmax, _⟩ := h d hd hdN
    exact le_antisymm (hqmax _ hd hdn) (hdmax _ hq hqn)
  have hNe := Nat.eq_prime_pow_of_unique_prime_dvd (by omega) huniq
  have hf : N.factorization q = N.primeFactorsList.length := by
    conv_lhs => rw [hNe]
    simp [hq.factorization_pow]
  rw [hNe, ← hf]
  calc q ^ N.factorization q ≤ q ^ e := Nat.pow_le_pow_right hq.pos hqe
    _ ≤ _ := Nat.pow_le_pow_left (le_maxPF hn.ne' hq hqn) e

lemma norm_cyclotomic_le (m : ℕ) (hm : 0 < m) (Y : ℂ) :
    ‖eval Y (cyclotomic m ℂ)‖ ≤ (‖Y‖ + 1) ^ Nat.totient m := by
  have hζ := Complex.isPrimitiveRoot_exp m hm.ne'
  rw [cyclotomic_eq_prod_X_sub_primitiveRoots hζ, eval_prod, norm_prod,
    ← Complex.card_primitiveRoots m, ← Finset.prod_const]
  apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
  intro μ hμ
  rw [mem_primitiveRoots hm] at hμ
  simp only [eval_sub, eval_X, eval_C]
  calc ‖Y - μ‖ ≤ ‖Y‖ + ‖μ‖ := norm_sub_le _ _
    _ = ‖Y‖ + 1 := by rw [hμ.norm'_eq_one hm.ne']

lemma norm_cyclotomic_ge (m : ℕ) (hm : 0 < m) (Y : ℂ) (hY : 1 ≤ ‖Y‖) :
    (‖Y‖ - 1) ^ Nat.totient m ≤ ‖eval Y (cyclotomic m ℂ)‖ := by
  have hζ := Complex.isPrimitiveRoot_exp m hm.ne'
  rw [cyclotomic_eq_prod_X_sub_primitiveRoots hζ, eval_prod, norm_prod,
    ← Complex.card_primitiveRoots m, ← Finset.prod_const]
  apply Finset.prod_le_prod (fun _ _ => sub_nonneg.2 hY)
  intro μ hμ
  rw [mem_primitiveRoots hm] at hμ
  simp only [eval_sub, eval_X, eval_C]
  calc ‖Y‖ - 1 = ‖Y‖ - ‖μ‖ := by rw [hμ.norm'_eq_one hm.ne']
    _ ≤ ‖Y - μ‖ := norm_sub_norm_le _ _

lemma eval_cyclotomic_mul_pow (R : Type*) [CommRing R] (r : ℕ) (hr : r.Prime) (a : ℕ)
    (har : r ∣ a) : ∀ (t : ℕ) (z : R),
    eval z (cyclotomic (a * r ^ t) R) = eval (z ^ (r ^ t)) (cyclotomic a R)
  | 0, z => by simp
  | t + 1, z => by
    rw [pow_succ, ← mul_assoc, ← cyclotomic_expand_eq_cyclotomic hr (dvd_mul_of_dvd_left har _),
      expand_eval, eval_cyclotomic_mul_pow R r hr a har t, ← pow_mul]
    congr 2; ring

lemma lower_bound (r s m : ℕ) (hr : r.Prime) (hs : 1 ≤ s) (hm : 0 < m) (hrm : ¬ r ∣ m)
    (z : ℂ) (hz : 1 ≤ ‖z‖) :
    ((‖z‖ ^ (r ^ (s - 1))) ^ r - 1) ^ Nat.totient m ≤
      ‖eval z (cyclotomic (r ^ s * m) ℂ)‖ * (‖z‖ ^ (r ^ (s - 1)) + 1) ^ Nat.totient m := by
  have hk : r ^ s * m = (m * r) * r ^ (s - 1) := by
    obtain ⟨s', rfl⟩ := Nat.exists_eq_add_of_le' hs
    simp [pow_succ]; ring
  have h1 : eval z (cyclotomic (r ^ s * m) ℂ) =
      eval (z ^ (r ^ (s - 1))) (cyclotomic (m * r) ℂ) := by
    rw [hk, eval_cyclotomic_mul_pow ℂ r hr (m * r) (dvd_mul_left r m)]
  have h2 : eval (z ^ (r ^ (s - 1))) (cyclotomic (m * r) ℂ) *
      eval (z ^ (r ^ (s - 1))) (cyclotomic m ℂ) =
      eval ((z ^ (r ^ (s - 1))) ^ r) (cyclotomic m ℂ) := by
    rw [← eval_mul, ← cyclotomic_expand_eq_cyclotomic_mul hr hrm, expand_eval]
  have hy : ‖z ^ (r ^ (s - 1))‖ = ‖z‖ ^ (r ^ (s - 1)) := norm_pow _ _
  have hy1 : 1 ≤ ‖z ^ (r ^ (s - 1))‖ := hy ▸ one_le_pow₀ hz
  have h3 := norm_cyclotomic_ge m hm ((z ^ (r ^ (s - 1))) ^ r)
    (by rw [norm_pow]; exact one_le_pow₀ hy1)
  have h4 := norm_cyclotomic_le m hm (z ^ (r ^ (s - 1)))
  rw [norm_pow, hy] at h3
  rw [hy] at h4
  rw [h1]
  calc _ ≤ ‖eval ((z ^ (r ^ (s - 1))) ^ r) (cyclotomic m ℂ)‖ := h3
    _ = ‖eval (z ^ (r ^ (s - 1))) (cyclotomic (m * r) ℂ)‖ *
        ‖eval (z ^ (r ^ (s - 1))) (cyclotomic m ℂ)‖ := by rw [← h2, norm_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left h4 (norm_nonneg _)

lemma pow_ineq (u A c r : ℝ) (φ : ℕ) (hφ : φ ≠ 0) (hu : 0 < u + 1) (hc : 0 ≤ c)
    (hA : c * (u + 1) < A) (hr : r ≤ c ^ φ) : r * (u + 1) ^ φ < A ^ φ := by
  calc r * (u + 1) ^ φ ≤ c ^ φ * (u + 1) ^ φ := mul_le_mul_of_nonneg_right hr (pow_pos hu _).le
    _ = (c * (u + 1)) ^ φ := (mul_pow _ _ _).symm
    _ < A ^ φ := pow_lt_pow_left₀ hA (by positivity) hφ

lemma grow (u : ℝ) (hu : 14 / 5 ≤ u) : ∀ r : ℕ, 3 ≤ r → (r : ℝ) * (u + 1) < u ^ r - 1 := by
  intro r hr
  induction r, hr using Nat.le_induction with
  | base =>
    have h2 : 14 / 5 * u ≤ u * u := mul_le_mul_of_nonneg_right hu (by linarith)
    have h3 : 14 / 5 * (u * u) ≤ u * (u * u) := mul_le_mul_of_nonneg_right hu (by positivity)
    push_cast
    nlinarith
  | succ r hr ih =>
    have hu0 : 0 < u := by linarith
    have h1 := mul_lt_mul_of_pos_left ih hu0
    push_cast
    rw [pow_succ]
    have : (3:ℝ) ≤ r := by exact_mod_cast hr
    have h2 : (0:ℝ) ≤ (u + 1) * (u * r - r - 1) := mul_nonneg (by linarith) (by nlinarith)
    nlinarith

lemma grow2 : ∀ r : ℕ, 11 ≤ r → (r : ℝ) * (Real.sqrt 2 + 1) < Real.sqrt 2 ^ r - 1 := by
  have ht2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have ht : (1.4 : ℝ) < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have ht' : Real.sqrt 2 < 1.5 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  intro r hr
  induction r, hr using Nat.le_induction with
  | base =>
    have : Real.sqrt 2 ^ 11 = 32 * Real.sqrt 2 := by
      rw [show 11 = 2 * 5 + 1 by rfl, pow_succ, pow_mul, ht2]; norm_num
    rw [this]; push_cast; nlinarith
  | succ r hr ih =>
    have h1 := mul_lt_mul_of_pos_left ih (by linarith : (0:ℝ) < Real.sqrt 2)
    push_cast
    rw [pow_succ]
    have : (11:ℝ) ≤ r := by exact_mod_cast hr
    nlinarith

lemma grow3 : ∀ r : ℕ, 4 ≤ r → 3 * r + 1 < 2 ^ r := by
  intro r hr
  induction r, hr using Nat.le_induction with
  | base => norm_num
  | succ r hr ih => rw [pow_succ]; omega

lemma totient_ge_two (m : ℕ) (hm : 3 ≤ m) : 2 ≤ Nat.totient m := by
  have h1 := Nat.totient_even (by omega : 2 < m)
  have h2 : 0 < Nat.totient m := Nat.totient_pos.2 (by omega)
  obtain ⟨t, ht⟩ := h1
  omega


lemma conclude (X u A r : ℝ) (φ : ℕ) (hu : 0 < u + 1) (LB : A ^ φ ≤ X * (u + 1) ^ φ)
    (key : r * (u + 1) ^ φ < A ^ φ) : r < X :=
  lt_of_mul_lt_mul_right (lt_of_lt_of_le key LB) (pow_pos hu _).le

lemma cyc_two_complex (n : ℕ) :
    ‖eval (2:ℂ) (cyclotomic n ℂ)‖ = ((eval (2:ℤ) (cyclotomic n ℤ)).natAbs : ℝ) := by
  have := cyclotomic.eval_apply (2:ℤ) n (Int.castRingHom ℂ)
  simp only [eq_intCast, Int.cast_ofNat] at this
  rw [this, Complex.norm_intCast, Nat.cast_natAbs, Int.cast_abs]

lemma zsigmondy (n : ℕ) (hn : 7 ≤ n) : ∃ q, q.Prime ∧ orderOf (2 : ZMod q) = n := by
  have hN1 : 1 < (eval (2:ℤ) (cyclotomic n ℤ)).natAbs := by
    have := sub_one_lt_natAbs_cyclotomic_eval (n := n) (q := 2) (by omega) (by norm_num)
    simpa using this
  have hodd : ¬ (2:ℤ) ∣ eval (2:ℤ) (cyclotomic n ℤ) := by
    have h := sub_dvd_eval_sub (2:ℤ) 0 (cyclotomic n ℤ)
    rw [← coeff_zero_eq_eval_zero, cyclotomic_coeff_zero ℤ (by omega)] at h
    intro h2
    have := dvd_sub h2 h
    norm_num at this
  by_contra hcon
  push Not at hcon
  have hall : ∀ q, q.Prime → q ∣ (eval (2:ℤ) (cyclotomic n ℤ)).natAbs → q ∣ n := by
    intro q hq hqN
    by_contra hqn
    apply hcon q hq
    haveI := Fact.mk hq
    haveI : NeZero (n : ZMod q) := ⟨by rw [Ne, ZMod.natCast_eq_zero_iff]; exact hqn⟩
    have hroot : IsRoot (cyclotomic n (ZMod q)) (2 : ZMod q) := by
      rw [IsRoot.def]
      have := cyclotomic.eval_apply (2:ℤ) n (Int.castRingHom (ZMod q))
      simp only [eq_intCast, Int.cast_ofNat] at this
      rw [this, ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact Int.natCast_dvd.2 hqN
    exact ((isRoot_cyclotomic_iff).1 hroot).eq_orderOf.symm
  have hP : ∀ q, q.Prime → q ∣ (eval (2:ℤ) (cyclotomic n ℤ)).natAbs →
      q ∣ n ∧ (∀ t, t.Prime → t ∣ n → t ≤ q) ∧
        (eval (2:ℤ) (cyclotomic n ℤ)).natAbs.factorization q ≤ 1 := by
    intro q hq hqN
    have hqn := hall q hq hqN
    have hqΦ : (q:ℤ) ∣ eval (2:ℤ) (cyclotomic n ℤ) := Int.natCast_dvd.2 hqN
    have hq2 : q ≠ 2 := by rintro rfl; exact hodd (by exact_mod_cast hqΦ)
    obtain ⟨h1, h2⟩ := P_lemma 2 (by norm_num) n q (by omega) hq hq2 hqn hqΦ
    refine ⟨hqn, h1, ?_⟩
    by_contra hf
    push Not at hf
    apply h2
    have : q ^ 2 ∣ (eval (2:ℤ) (cyclotomic n ℤ)).natAbs :=
      (hq.pow_dvd_iff_le_factorization (by omega)).2 hf
    exact Int.natCast_dvd.2 (by exact_mod_cast this)
  have hle := le_of_prime_factors _ n 1 hN1 (by omega) hP
  rw [pow_one] at hle
  obtain ⟨q0, hq0, hq0N⟩ := Nat.exists_prime_and_dvd hN1.ne'
  obtain ⟨hq0n, -, -⟩ := hP q0 hq0 hq0N
  have hq02 : q0 ≠ 2 := by
    rintro rfl; exact hodd (by exact_mod_cast (Int.natCast_dvd.2 hq0N))
  have hrp : (maxPF n).Prime := prime_maxPF n (by omega)
  have hr3 : 3 ≤ maxPF n := by
    have := le_maxPF (by omega) hq0 hq0n
    have := hq0.two_le
    omega
  set r := maxPF n with hr
  obtain ⟨s, m, hrm, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : n ≠ 0) r (by omega)
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h] at hnm; omega
    · exact h
  have hs : 1 ≤ s := by
    rcases Nat.eq_zero_or_pos s with h | h
    · exfalso
      have hrn : r ∣ n := hr ▸ maxPF_dvd (show 1 < n by omega)
      rw [h, pow_zero, one_mul] at hnm; rw [hnm] at hrn; exact hrm hrn
    · exact h
  have LB := lower_bound r s m hrp hs hm hrm (2:ℂ) (by norm_num)
  rw [← hnm, cyc_two_complex] at LB
  have h2n : ‖(2:ℂ)‖ = 2 := by norm_num
  rw [h2n] at LB
  have hφ : Nat.totient m ≠ 0 := (Nat.totient_pos.2 hm).ne'
  have hrR : (3:ℝ) ≤ r := by exact_mod_cast hr3
  have key : (r:ℝ) < ((eval (2:ℤ) (cyclotomic n ℤ)).natAbs : ℝ) := by
    apply conclude _ _ _ _ _ (by positivity) LB
    rcases (by omega : s = 1 ∨ 2 ≤ s) with hs1 | hs2
    · subst hs1
      simp only [Nat.sub_self, pow_zero, pow_one]
      rcases (by omega : r = 3 ∨ 4 ≤ r) with hr3' | hr4
      · have hm3 : 3 ≤ m := by rw [hr3', pow_one] at hnm; omega
        have hφ2 := totient_ge_two m hm3
        apply pow_ineq _ _ (23 / 10) _ _ hφ (by norm_num) (by norm_num)
        · rw [hr3']; norm_num
        · rw [hr3']
          calc ((3:ℕ):ℝ) ≤ (23/10) ^ 2 := by norm_num
            _ ≤ _ := pow_le_pow_right₀ (by norm_num) hφ2
      · apply pow_ineq _ _ r _ _ hφ (by norm_num) (by positivity)
        · have := grow3 r hr4
          have : ((3 * r + 1 : ℕ) : ℝ) < ((2 ^ r : ℕ) : ℝ) := by exact_mod_cast this
          push_cast at this
          linarith
        · exact le_self_pow₀ (by linarith) hφ
    · have hu : (14 / 5 : ℝ) ≤ 2 ^ (r ^ (s - 1)) := by
        have h1 : 3 ≤ r ^ (s - 1) :=
          le_trans hr3 (Nat.le_self_pow (by omega) r)
        calc (14 / 5 : ℝ) ≤ 2 ^ 3 := by norm_num
          _ ≤ _ := pow_le_pow_right₀ (by norm_num) h1
      apply pow_ineq _ _ r _ _ hφ (by positivity) (by positivity)
      · exact grow _ hu r hr3
      · exact le_self_pow₀ (by linarith) hφ
  have : ((eval (2:ℤ) (cyclotomic n ℤ)).natAbs : ℝ) ≤ r := by exact_mod_cast hle
  linarith

/-- A prime `q` with `ord_q(2) = 2 d`, for `d = 1` or `d ≥ 4`. -/
lemma exists_prime_order (d : ℕ) (hd' : d = 1 ∨ 4 ≤ d) :
    ∃ q, q.Prime ∧ orderOf (2 : ZMod q) = 2 * d := by
  rcases hd' with rfl | h4
  · refine ⟨3, Nat.prime_three, ?_⟩
    rw [orderOf_eq_iff (by norm_num)]
    refine ⟨by decide, ?_⟩
    intro m hm hm0
    have hm1 : m = 1 := by omega
    subst hm1
    decide
  · exact zsigmondy (2 * d) (by omega)

/-- If `ord_q(2) = 2 d` and `k = d m` with `m` odd, then `q ∣ 2 ^ k + 1`. -/
lemma dvd_two_pow_add_one {q d k m : ℕ} (hq : q.Prime) (hd : 0 < d)
    (hord : orderOf (2 : ZMod q) = 2 * d) (hkm : k = d * m) (hm : Odd m) :
    q ∣ 2 ^ k + 1 := by
  haveI := Fact.mk hq
  have h1 : (2 : ZMod q) ^ d * (2 : ZMod q) ^ d = 1 := by
    rw [← pow_add, ← two_mul, ← hord]
    exact pow_orderOf_eq_one _
  have h2 : (2 : ZMod q) ^ d ≠ 1 := by
    intro h
    have h3 := orderOf_dvd_of_pow_eq_one h
    rw [hord] at h3
    have h4 := Nat.le_of_dvd hd h3
    omega
  have h3 : (2 : ZMod q) ^ d = -1 := by
    rcases mul_self_eq_one_iff.1 h1 with h | h
    · exact absurd h h2
    · exact h
  have h4 : (2 : ZMod q) ^ k = -1 := by
    rw [hkm, pow_mul, h3]
    exact hm.neg_one_pow
  have h5 : ((2 ^ k + 1 : ℕ) : ZMod q) = 0 := by
    push_cast
    rw [h4]
    exact neg_add_cancel 1
  exact (ZMod.natCast_eq_zero_iff _ _).1 h5

end OMAmo383878

theorem OMA.solution : type_of% @OMA.S_mo_383878.main := by
  intro n p _hn hinj hp
  classical
  have hodd_all : ∀ T : Finset (Fin n), Odd (∏ i ∈ T, p i) := by
    intro T
    apply Finset.prod_induction _ Odd (fun a b ha hb => ha.mul hb) odd_one
    intro i _
    exact (hp i).1.odd_of_ne_two (by have := (hp i).2; omega)
  have hdS : ∀ S : Finset (Fin n), ∃ q, q.Prime ∧
      orderOf (2 : ZMod q) = 2 * ∏ i ∈ S, p i ∧ q ∣ 2 ^ (∏ i, p i) + 1 := by
    intro S
    have hpos : 0 < ∏ i ∈ S, p i := Finset.prod_pos (fun i _ => (hp i).1.pos)
    have hsize : (∏ i ∈ S, p i) = 1 ∨ 4 ≤ ∏ i ∈ S, p i := by
      rcases S.eq_empty_or_nonempty with rfl | ⟨i, hi⟩
      · left; simp
      · right
        have h1 : p i ∣ ∏ j ∈ S, p j := Finset.dvd_prod_of_mem p hi
        have h2 := Nat.le_of_dvd hpos h1
        have h3 := (hp i).2
        omega
    obtain ⟨q, hq, hord⟩ := OMAmo383878.exists_prime_order _ hsize
    refine ⟨q, hq, hord, ?_⟩
    have hkm : (∏ i, p i) = (∏ i ∈ S, p i) * ∏ i ∈ Sᶜ, p i :=
      (Finset.prod_mul_prod_compl S p).symm
    exact OMAmo383878.dvd_two_pow_add_one hq hpos hord hkm (hodd_all Sᶜ)
  choose f hf using hdS
  have key : ∀ (i : Fin n) (U : Finset (Fin n)), (p i ∣ ∏ j ∈ U, p j) ↔ i ∈ U := by
    intro i U
    constructor
    · intro h
      obtain ⟨j, hj, hdvd⟩ := ((hp i).1.prime.dvd_finsetProd_iff p).1 h
      have hij : p i = p j := (Nat.prime_dvd_prime_iff_eq (hp i).1 (hp j).1).1 hdvd
      rw [hinj hij]
      exact hj
    · intro h
      exact Finset.dvd_prod_of_mem p h
  have hfinj : Function.Injective f := by
    intro S T hST
    have h1 := (hf S).2.1
    have h2 := (hf T).2.1
    rw [hST] at h1
    have hprod : ∏ i ∈ S, p i = ∏ i ∈ T, p i := by
      have h3 := h1.symm.trans h2
      omega
    ext i
    rw [← key i S, ← key i T, hprod]
  have hNne : 2 ^ (∏ i, p i) + 1 ≠ 0 := Nat.succ_ne_zero _
  have himg : (Finset.univ.image f) ⊆ (2 ^ (∏ i, p i) + 1).primeFactors := by
    intro q hq
    obtain ⟨S, -, rfl⟩ := Finset.mem_image.1 hq
    exact Nat.mem_primeFactors.2 ⟨(hf S).1, (hf S).2.2, hNne⟩
  have hcard : 2 ^ n ≤ (2 ^ (∏ i, p i) + 1).primeFactors.card := by
    have h1 : (Finset.univ.image f).card = 2 ^ n := by
      rw [Finset.card_image_of_injective _ hfinj, Finset.card_univ, Fintype.card_finset,
        Fintype.card_fin]
    rw [← h1]
    exact Finset.card_le_card himg
  have hdiv : 2 ^ (2 ^ (∏ i, p i) + 1).primeFactors.card ≤
      (2 ^ (∏ i, p i) + 1).divisors.card := by
    rw [Nat.card_divisors hNne, ← Finset.prod_const]
    apply Finset.prod_le_prod
    · intro x _
      exact Nat.zero_le _
    · intro x hx
      have hx' := Nat.mem_primeFactors.1 hx
      have h1 := hx'.1.factorization_pos_of_dvd hNne hx'.2.1
      omega
  have h1 : n < 2 ^ n := Nat.lt_two_pow_self
  have hfin : (n + 1) * 2 ^ (2 ^ n - n) ≤ 2 ^ (2 ^ n) := by
    calc (n + 1) * 2 ^ (2 ^ n - n) ≤ 2 ^ n * 2 ^ (2 ^ n - n) := Nat.mul_le_mul_right _ h1
      _ = 2 ^ (2 ^ n) := by
        rw [← pow_add]
        congr 1
        omega
  exact le_trans hfin (le_trans (Nat.pow_le_pow_right (by norm_num) hcard) hdiv)
