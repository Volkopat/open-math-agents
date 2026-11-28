import OMAStatements.S_oeis_a114965
import Mathlib

-- Problem: A114965: a(n) = n^2 + 34.
-- Upstream: formal-conjectures statements/oeis-a114965.lean:0 (declaration OMA.S_oeis_a114965.main)
-- Credit: @dries (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-! `n ^ 2 + 34` is never a perfect power `x ^ k`, `k > 1` (Cohn, Acta Arith. 65 (1993)).

* Even `k`: `n ^ 2 + 34` is `2` or `3` mod 4. Odd `k`: pass to an odd prime `p ∣ k`.
* `R = ℤ[√-34]` (as `QuadraticAlgebra ℤ (-34) 0`) is the integral closure of `ℤ` in
  `ℚ(√-34)`, hence Dedekind. Every nonzero ideal `I` has `I ^ 4` principal: by pigeonhole `I`
  contains `x ≠ 0` with `5 N(x) < 59 N(I)`, which reduces to ideals of norm at most 11; there
  `3, 11` are inert, `P2 ^ 2 = (2)`, `(4 ∓ √-34) = P2 P5 ^ 2` and `(1 ± √-34) = P5 P7`.
* Descent: `n + √-34` and `n - √-34` are coprime, so `(n + √-34) = I ^ p`; as
  `I ^ (p ^ 2) = I (I ^ 4) ^ ((p ^ 2 - 1) / 4)`, `I` is principal and `n + √-34 = z ^ p`.
* Cohn: no odd power `p > 1` in `R` has `√-34`-coefficient `1`. Here `z = a ± √-34` with `a` odd;
  `p ≡ 1 mod 4` is a `2`-adic argument, `p ≡ 3 mod 4` uses `z ^ 8 ≡ 1 mod 24`. -/

namespace OMA.A114965

open Ideal QuadraticAlgebra

abbrev R := QuadraticAlgebra ℤ (-34) 0
abbrev K := QuadraticAlgebra ℚ (-34) 0

instance : Fact (∀ r : ℚ, r ^ 2 ≠ -34 + 0 * r) := ⟨fun r _ => by nlinarith [sq_nonneg r]⟩

def φ : R →+* K where
  toFun z := ⟨z.re, z.im⟩
  map_one' := by ext <;> simp
  map_mul' _ _ := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' _ _ := by ext <;> simp

instance : Algebra R K := φ.toAlgebra

lemma am (z : R) : algebraMap R K z = ⟨z.re, z.im⟩ := rfl

lemma intQ {q : ℚ} (h : IsIntegral ℤ (algebraMap ℚ K q)) : ∃ n : ℤ, (n : ℚ) = q :=
  IsIntegrallyClosed.isIntegral_iff.1
    ((isIntegral_algHom_iff ((Algebra.ofId ℚ K).restrictScalars ℤ) (algebraMap ℚ K).injective).1 h)

lemma int_of_integral (x : K) (hx : IsIntegral ℤ x) : ∃ y : R, algebraMap R K y = x := by
  have hs : IsIntegral ℤ (star x) := hx.map (starRingEnd K).toIntAlgHom
  obtain ⟨u, hu⟩ := intQ (q := trace x) (by
    rw [show algebraMap ℚ K (trace x) = x + star x from algebraMap_trace_eq_add_star x]; exact hx.add hs)
  obtain ⟨m, hm⟩ := intQ (q := norm x) (by
    rw [show algebraMap ℚ K (norm x) = x * star x from algebraMap_norm_eq_mul_star x]; exact hx.mul hs)
  simp only [trace_def, norm_def] at hu hm
  obtain ⟨s, hs⟩ : ∃ s : ℤ, (s : ℚ) = 68 * x.im := IsIntegrallyClosed.isIntegral_iff.1
    (IsIntegral.of_pow two_pos (by
      rw [show (68 * x.im) ^ 2 = ((34 * (4 * m - u ^ 2) : ℤ) : ℚ) by push_cast; rw [hu, hm]; ring]
      exact isIntegral_algebraMap))
  have hsq : s ^ 2 = 34 * (4 * m - u ^ 2) := by
    have : (s : ℚ) ^ 2 = 34 * (4 * m - u ^ 2) := by rw [hs, hu, hm]; ring
    exact_mod_cast this
  obtain ⟨v, rfl⟩ : (34 : ℤ) ∣ s := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd s 34).1
    apply (by decide : ∀ x : ZMod 34, x ^ 2 = 0 → x = 0)
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (s ^ 2) 34).2 ⟨_, hsq⟩
    push_cast at this; exact this
  have huv : u ^ 2 + 34 * v ^ 2 = 4 * m := by nlinarith
  obtain ⟨u, rfl⟩ : (2 : ℤ) ∣ u := by
    rcases Int.even_or_odd u with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · exact ⟨k, by ring⟩
    · rcases Int.even_or_odd v with ⟨l, rfl⟩ | ⟨l, rfl⟩ <;> ring_nf at huv <;> omega
  obtain ⟨v, rfl⟩ : (2 : ℤ) ∣ v := by
    rcases Int.even_or_odd v with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · exact ⟨k, by ring⟩
    · ring_nf at huv; omega
  refine ⟨⟨u, v⟩, ?_⟩
  ext <;> simp [am] <;> push_cast at hu hs <;> linarith

lemma φinj : Function.Injective (algebraMap R K) := fun z w h => by
  simp [am, QuadraticAlgebra.ext_iff] at h; ext <;> simp [h]

instance : IsIntegralClosure R ℤ K where
  algebraMap_injective := φinj
  isIntegral_iff := fun {x} => ⟨int_of_integral x, fun ⟨y, hy⟩ => hy ▸ by
    have h : (ω : K) ^ 2 = algebraMap ℤ K (-34) := by ext <;> simp [sq]
    rw [show algebraMap R K y = algebraMap ℤ K y.re + algebraMap ℤ K y.im * ω by ext <;> simp [am]]
    exact isIntegral_algebraMap.add (isIntegral_algebraMap.mul
      (IsIntegral.of_pow two_pos (h ▸ isIntegral_algebraMap)))⟩

instance : IsDomain R := φinj.isDomain _

instance : IsDedekindDomain R := IsIntegralClosure.isDedekindDomain ℤ ℚ K R

lemma an (z : R) : Algebra.norm ℤ z = z.re ^ 2 + 34 * z.im ^ 2 := by
  rw [Algebra.norm_apply]; erw [det_toLinearMap_eq_norm]; simp [norm_def]; ring

lemma nsp (z : R) : absNorm (span {z}) = (z.re ^ 2 + 34 * z.im ^ 2).natAbs := by
  rw [absNorm_span_singleton, an]

lemma ndvd {I : Ideal R} {x : R} (h : x ∈ I) : (absNorm I : ℤ) ∣ x.re ^ 2 + 34 * x.im ^ 2 :=
  an x ▸ absNorm_dvd_norm_of_mem h

lemma exists_small (I : Ideal R) (hI : I ≠ ⊥) :
    ∃ x ∈ I, x ≠ 0 ∧ 5 * (x.re ^ 2 + 34 * x.im ^ 2) < 59 * (absNorm I : ℤ) := by
  have hM : 0 < absNorm I := Nat.pos_of_ne_zero (by rwa [Ne, absNorm_eq_zero_iff])
  set M := absNorm I with hMd
  obtain ⟨B, h4, h5⟩ : ∃ B, 5 * B ^ 2 ≤ M ∧ M < 5 * (B + 1) ^ 2 := ⟨Nat.sqrt (M / 5),
    by have := Nat.sqrt_le' (M / 5); omega, by have := Nat.lt_succ_sqrt' (M / 5); simp only [Nat.succ_eq_add_one] at this; omega⟩
  obtain ⟨A, h1, h2⟩ : ∃ A, A * (B + 1) ≤ M ∧ M < (A + 1) * (B + 1) := ⟨M / (B + 1),
    Nat.div_mul_le_self _ _, by have := Nat.div_add_mod M (B + 1); have := Nat.mod_lt M B.succ_pos; nlinarith⟩
  have h9 : A ^ 2 < 5 * M := by
    by_contra! h; nlinarith [Nat.pow_le_pow_left h1 2]
  have := I.finiteQuotientOfFreeOfNeBot hI
  have := Fintype.ofFinite (R ⧸ I)
  obtain ⟨p, q, hne, hpq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun ij : Fin (A + 1) × Fin (B + 1) => Ideal.Quotient.mk I ⟨(ij.1 : ℕ), (ij.2 : ℕ)⟩) (by
      rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, ← Nat.card_eq_fintype_card]
      exact h2)
  refine ⟨⟨(p.1 : ℕ) - (q.1 : ℕ), (p.2 : ℕ) - (q.2 : ℕ)⟩, ?_, fun h => hne ?_, ?_⟩
  · convert Ideal.Quotient.eq.1 hpq using 1; ext <;> simp
  · simp [QuadraticAlgebra.ext_iff, sub_eq_zero] at h
    exact Prod.ext (Fin.ext h.1) (Fin.ext h.2)
  · have := p.1.isLt; have := q.1.isLt; have := p.2.isLt; have := q.2.isLt
    have eA : (((p.1 : ℕ) : ℤ) - ((q.1 : ℕ) : ℤ)) ^ 2 ≤ (A : ℤ) ^ 2 := by apply sq_le_sq' <;> omega
    have eB : (((p.2 : ℕ) : ℤ) - ((q.2 : ℕ) : ℤ)) ^ 2 ≤ (B : ℤ) ^ 2 := by apply sq_le_sq' <;> omega
    have : (5 * (A ^ 2 + 34 * B ^ 2) : ℤ) < 59 * M := by exact_mod_cast (by nlinarith : 5 * (A ^ 2 + 34 * B ^ 2) < 59 * M)
    simp only; linarith

abbrev P4 (I : Ideal R) : Prop := (I ^ 4).IsPrincipal

lemma cancel_span {I : Ideal R} {y z : R} (hz : z ≠ 0) (h : I * span {y} = span {z}) :
    I.IsPrincipal := by
  have hy : y ≠ 0 := by rintro rfl; simp at h; exact hz (span_singleton_eq_bot.1 h.symm)
  obtain ⟨w, rfl⟩ := mem_span_singleton'.1
    ((Ideal.mul_le_right : I * span {y} ≤ span {y}) (h ▸ mem_span_singleton_self z))
  refine ⟨⟨w, (span_singleton_mul_right_inj hy).1 ?_⟩⟩
  rw [mul_comm, h, ← span_singleton_mul_span_singleton, submodule_span_eq, mul_comm]

lemma pr_cancel {I J : Ideal R} {x : R} (hx : x ≠ 0) (h : I * J = span {x}) (hJ : P4 J) : P4 I := by
  obtain ⟨y, hy⟩ := hJ
  refine cancel_span (y := y) (pow_ne_zero 4 hx) ?_
  rw [submodule_span_eq] at hy
  rw [← hy, ← mul_pow, h, span_singleton_pow]

lemma pr_mul {I J : Ideal R} (hI : P4 I) (hJ : P4 J) : P4 (I * J) := by
  obtain ⟨⟨a, ha⟩⟩ := hI
  obtain ⟨⟨b, hb⟩⟩ := hJ
  exact ⟨⟨a * b, by rw [mul_pow, ha, hb, submodule_span_eq, submodule_span_eq,
    span_singleton_mul_span_singleton]⟩⟩

lemma pr_span (z : R) : P4 (span {z}) := ⟨⟨z ^ 4, by rw [span_singleton_pow]⟩⟩

lemma fac {I : Ideal R} {x : R} (hx : x ∈ I) :
    ∃ J, span {x} = I * J ∧ x ∈ J ∧ (x.re ^ 2 + 34 * x.im ^ 2).natAbs = absNorm I * absNorm J := by
  obtain ⟨J, hJ⟩ := dvd_iff_le.2 ((span_singleton_le_iff_mem _).2 hx)
  exact ⟨J, hJ, (Ideal.mul_le_right : I * J ≤ J) (hJ ▸ mem_span_singleton_self x), by rw [← nsp, hJ, map_mul]⟩

lemma maxl {P : Ideal R} {p : ℕ} (hp : p.Prime) (h : absNorm P = p) : P.IsMaximal :=
  (isPrime_of_irreducible_absNorm (h ▸ hp)).isMaximal (by rintro rfl; simp [hp.ne_zero.symm] at h)

/-- A proper ideal containing `p` and an element of norm not divisible by `p ^ 2` is
`span {p, x}`, of norm `p`. -/
lemma uniq {M : Ideal R} (hM : M ≠ ⊤) {p : ℕ} (hp : p.Prime) {x : R} (pM : (p : R) ∈ M)
    (xM : x ∈ M) (hx : ¬ (p : ℤ) ^ 2 ∣ x.re ^ 2 + 34 * x.im ^ 2) :
    M = span {(p : R), x} ∧ absNorm M = p := by
  have key : ∀ S : Ideal R, S ≠ ⊤ → (p : R) ∈ S → x ∈ S → absNorm S = p := fun S hS h1 h2 => by
    have d1 := ndvd h1
    simp only [re_natCast, im_natCast] at d1
    obtain ⟨i, hi, he⟩ := (Nat.dvd_prime_pow hp).1 (by exact_mod_cast (by simpa using d1 : (absNorm S : ℤ) ∣ (p : ℤ) ^ 2))
    interval_cases i
    · exact absurd (absNorm_eq_one_iff.1 (by simpa using he)) hS
    · simpa using he
    · exact absurd (he ▸ ndvd h2) (by exact_mod_cast hx)
  have hS : span {(p : R), x} ≤ M := span_le.2 (by simp [Set.insert_subset_iff, pM, xM])
  have hn := key _ (ne_top_of_le_ne_top hM hS) (subset_span (by simp)) (subset_span (by simp))
  exact ⟨((maxl hp hn).eq_of_le hM hS).symm, key M hM pM xM⟩

lemma pk {M : Ideal R} (hM : M.IsPrime) {p : ℕ} {k c : ℤ} (h : k ^ 2 + 34 = p * c)
    (pM : (p : R) ∈ M) : ∃ s : ℤ, s ^ 2 = k ^ 2 ∧ (⟨s, 1⟩ : R) ∈ M := by
  have e : (⟨k, 1⟩ : R) * ⟨-k, 1⟩ = p * ((-c : ℤ) : R) := by
    ext <;> simp; linear_combination -h
  rcases hM.mem_or_mem (e ▸ M.mul_mem_right _ pM) with h | h
  exacts [⟨k, rfl, h⟩, ⟨-k, neg_sq k, h⟩]

/-- `3` and `11` are inert. -/
lemma inert {p : ℕ} (hp : p.Prime) (hres : ∀ a b : ZMod p, a ^ 2 + 34 * b ^ 2 = 0 → a = 0 ∧ b = 0)
    {M : Ideal R} (hM : M ≠ ⊤) (h : (p : R) ∈ M) : M = span {(p : R)} := by
  refine le_antisymm (fun x hx => ?_) ((span_singleton_le_iff_mem _).2 h)
  have d1 := ndvd h
  simp only [re_natCast, im_natCast] at d1
  obtain ⟨i, hi, he⟩ := (Nat.dvd_prime_pow hp).1 (by exact_mod_cast (by simpa using d1 : (absNorm M : ℤ) ∣ (p : ℤ) ^ 2))
  have hi0 : i ≠ 0 := by rintro rfl; exact hM (absNorm_eq_one_iff.1 (by simpa using he))
  have := (dvd_pow_self (p : ℤ) hi0).trans (he ▸ ndvd hx : ((p ^ i : ℕ) : ℤ) ∣ _)
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at this
  push_cast at this
  obtain ⟨h1, h2⟩ := hres _ _ this
  rw [mem_span_singleton, ← map_natCast (algebraMap ℤ R), algebraMap_dvd_iff]
  exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h1, (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h2⟩

lemma two {M : Ideal R} (hM : M.IsPrime) (h : (2 : R) ∈ M) : M = span {2, ω} ∧ absNorm M = 2 := by
  obtain ⟨s, hs, hsM⟩ := pk hM (p := 2) (k := 0) (c := 17) (by norm_num) (by exact_mod_cast h)
  have : (⟨s, 1⟩ : R) = ω := by ext <;> simp; nlinarith
  exact_mod_cast uniq hM.ne_top Nat.prime_two (by exact_mod_cast h) (this ▸ hsM) (by norm_num)

lemma two_sq {M : Ideal R} (hM : M.IsPrime) (h : (2 : R) ∈ M) : M * M = span {2} := by
  obtain ⟨J, hJ, -, hn⟩ := fac h
  rw [(two hM h).2] at hn
  have hJ2 : absNorm J = 2 := by simp at hn; omega
  rw [hJ, (two (maxl Nat.prime_two hJ2).isPrime (by exact_mod_cast hJ2 ▸ absNorm_mem J)).1, ← (two hM h).1]

lemma five {M : Ideal R} (hM : M.IsPrime) (h : (5 : R) ∈ M) : P4 M := by
  obtain ⟨s, hs, hsM⟩ := pk hM (p := 5) (k := 1) (c := 7) (by norm_num) (by exact_mod_cast h)
  set x : R := ⟨4, -s⟩
  have key : ∀ P : Ideal R, P ≠ ⊤ → (5 : R) ∈ P → x ∈ P → P = span {((5 : ℕ) : R), ⟨s, 1⟩} :=
    fun P hP h5 hx => (uniq hP (p := 5) (by norm_num) (by exact_mod_cast h5)
      (by rw [show (⟨s, 1⟩ : R) = s * (5 - x) by ext <;> simp [x]; nlinarith]
          exact P.mul_mem_left _ (P.sub_mem h5 hx)) (by norm_num [hs])).1
  have hMx : x ∈ M := by
    rw [show x = 5 - s * ⟨s, 1⟩ by ext <;> simp [x]; nlinarith]
    exact M.sub_mem h (M.mul_mem_left _ hsM)
  obtain ⟨M2, hM2, h2M⟩ := exists_le_maximal (span {(2 : R)}) (by
    rw [Ne, span_singleton_eq_top, isUnit_iff_norm_isUnit]; norm_num [norm_def, Int.isUnit_iff])
  have h2 : (2 : R) ∈ M2 := h2M (mem_span_singleton_self _)
  obtain ⟨J1, h1, hx1, hn1⟩ := fac (show x ∈ M2 by
    rw [show x = 2 * 2 - (s : R) * ω by ext <;> simp [x]]
    exact M2.sub_mem (M2.mul_mem_left _ h2)
      (M2.mul_mem_left _ (by rw [(two hM2.isPrime h2).1]; exact subset_span (by simp))))
  rw [(two hM2.isPrime h2).2] at hn1
  have hJ1 : absNorm J1 = 25 := by simp [x, hs] at hn1; omega
  obtain ⟨M', hM', hJM⟩ := exists_le_maximal J1 (by rintro rfl; simp at hJ1)
  have h5' : (5 : R) ∈ M' := by
    have := hJM (absNorm_mem J1); rw [hJ1] at this
    rcases hM'.isPrime.mem_or_mem (show (5 : R) * 5 ∈ M' by norm_num; exact_mod_cast this) with h | h <;> exact h
  rw [key M' hM'.ne_top h5' (hJM hx1), ← key M hM.ne_top h hMx] at hJM
  obtain ⟨J3, rfl⟩ := dvd_iff_le.2 hJM
  rw [map_mul, (uniq hM.ne_top (p := 5) (by norm_num) (by exact_mod_cast h) hsM (by norm_num [hs])).2] at hJ1
  have hJ3 : absNorm J3 = 5 := by omega
  have hJ3M := key J3 (maxl (by norm_num) hJ3).ne_top (by exact_mod_cast hJ3 ▸ absNorm_mem J3)
    ((Ideal.mul_le_right : M * J3 ≤ J3) hx1)
  rw [← key M hM.ne_top h hMx] at hJ3M
  refine cancel_span (y := 2) (z := x ^ 2) (pow_ne_zero 2 (by simp [x, QuadraticAlgebra.ext_iff])) ?_
  rw [← span_singleton_pow, h1, hJ3M, ← two_sq hM2.isPrime h2]; ring

lemma all4 : ∀ n : ℕ, ∀ I : Ideal R, absNorm I = n → I ≠ ⊥ → P4 I := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro I hIn hI
  have hn0 : n ≠ 0 := by rwa [← hIn, Ne, absNorm_eq_zero_iff]
  rcases lt_or_ge n 12 with hs | hs
  · by_cases ht : I = ⊤
    · exact ⟨⟨1, by simp [ht]⟩⟩
    obtain ⟨M, hM, hIM⟩ := exists_le_maximal I ht
    obtain ⟨J, rfl⟩ := dvd_iff_le.2 hIM
    rw [map_mul] at hIn
    have hM0 : absNorm M ≠ 0 := by rintro h; simp [h] at hIn; omega
    have hM1 : absNorm M ≠ 1 := by rw [Ne, absNorm_eq_one_iff]; exact hM.ne_top
    have hJ0 : absNorm J ≠ 0 := by rintro h; simp [h] at hIn; omega
    refine pr_mul ?_ (ih _ (by rw [← hIn]; exact lt_mul_left (by omega) (by omega)) J rfl
      (by rintro rfl; simp at hJ0))
    obtain ⟨q, hq, hqM⟩ : ∃ q, q.Prime ∧ q ∣ absNorm M ∧ (q : R) ∈ M := by
      have key : ∀ m : ℕ, m ≠ 0 → (m : R) ∈ M → ∃ q, q.Prime ∧ q ∣ m ∧ (q : R) ∈ M := by
        intro m
        induction m using Nat.recOnMul with
        | zero => simp
        | one => intro _ h; exact absurd ((eq_top_iff_one _).2 (by simpa using h)) hM.ne_top
        | prime p hp => exact fun _ h => ⟨p, hp, dvd_rfl, h⟩
        | mul a b iha ihb =>
          intro h0 h
          push_cast at h
          rcases hM.isPrime.mem_or_mem h with h | h
          · obtain ⟨q, h1, h2, h3⟩ := iha (by rintro rfl; simp at h0) h
            exact ⟨q, h1, h2.mul_right _, h3⟩
          · obtain ⟨q, h1, h2, h3⟩ := ihb (by rintro rfl; simp at h0) h
            exact ⟨q, h1, h2.mul_left _, h3⟩
      exact key _ hM0 (absNorm_mem M)
    have : q ≤ 11 := by
      have := Nat.le_of_dvd (by omega) hqM.1; have := Nat.le_of_dvd (by omega) (Dvd.intro _ hIn); omega
    interval_cases q <;> norm_num at hq
    · show (M ^ 4).IsPrincipal
      rw [show M ^ 4 = (M * M) ^ 2 by ring, two_sq hM.isPrime (by exact_mod_cast hqM.2)]
      exact ⟨⟨4, by rw [span_singleton_pow]; norm_num⟩⟩
    · rw [inert (p := 3) (by norm_num) (by decide) hM.ne_top hqM.2]; exact pr_span _
    · exact five hM.isPrime (by exact_mod_cast hqM.2)
    · obtain ⟨s, hs, hsM⟩ := pk hM.isPrime (p := 7) (k := 1) (c := 5) (by norm_num) hqM.2
      have h7 := (uniq hM.ne_top (p := 7) (by norm_num) hqM.2 hsM (by norm_num [hs])).2
      obtain ⟨J', hJ', -, hn⟩ := fac hsM
      rw [h7] at hn
      have : absNorm J' = 5 := by simp [hs] at hn; omega
      refine pr_cancel (J := J') (by simp [QuadraticAlgebra.ext_iff]) hJ'.symm
        (ih 5 (by have := Nat.le_of_dvd (by omega) (Dvd.intro _ hIn); omega) J' this
          (by rintro rfl; simp at this))
    · rw [inert (p := 11) (by norm_num) (by decide) hM.ne_top hqM.2]; exact pr_span _
  · obtain ⟨x, hxI, hx0, hxb⟩ := exists_small I hI
    obtain ⟨J, hJ, -, hn⟩ := fac hxI
    rw [hIn] at hn hxb
    have hJ0 : absNorm J ≠ 0 := fun h => hx0 (by
      simp [h] at hn; ext <;> simp <;> nlinarith [sq_nonneg x.re, sq_nonneg x.im])
    have : (x.re ^ 2 + 34 * x.im ^ 2) = ((n * absNorm J : ℕ) : ℤ) := by
      rw [← hn, Int.natCast_natAbs, abs_of_nonneg (by positivity)]
    rw [this] at hxb
    push_cast at hxb
    have : absNorm J ≤ 11 := by
      by_contra hc
      have : (12 : ℤ) ≤ absNorm J := by exact_mod_cast (by omega : 12 ≤ absNorm J)
      nlinarith
    exact pr_cancel hx0 hJ.symm (ih _ (by omega) J rfl (by rintro rfl; simp at hJ0))

lemma unit_cases (u : Rˣ) : (u : R) = 1 ∨ (u : R) = -1 := by
  have h := isUnit_iff_norm_isUnit.1 u.isUnit
  rw [Int.isUnit_iff, norm_def] at h
  have h1 : (u : R).im = 0 := by
    rcases h with h | h <;> nlinarith [sq_nonneg (u : R).re, sq_nonneg (u : R).im]
  rw [h1] at h
  rcases mul_self_eq_one_iff.1 (show (u : R).re * (u : R).re = 1 by
    rcases h with h | h <;> nlinarith [sq_nonneg (u : R).re]) with h2 | h2
  · left; ext <;> simp [h1, h2]
  · right; ext <;> simp [h1, h2]

set_option maxRecDepth 100000 in
lemma descent (p : ℕ) (hp : p.Prime) (hp2 : 2 < p) (n x : ℕ) (hx : n ^ 2 + 34 = x ^ p) :
    ∃ z : R, z ^ p = ⟨n, 1⟩ := by
  set w : R := ⟨n, 1⟩
  have hprod : w * star w = (x : R) ^ p := by
    rw [← Nat.cast_pow, ← hx]
    ext <;> simp only [w, re_mul, im_mul, re_star, im_star, re_natCast, im_natCast] <;> push_cast <;> ring
  have hsq : (w - star w) ^ 2 = -136 := by ext <;> simp [w, sq]
  have h4 : ∀ q : ℕ, q ∣ x → q ^ 2 ∣ n ^ 2 + 34 := fun q h =>
    hx ▸ (pow_dvd_pow_of_dvd h 2).trans (pow_dvd_pow x (by omega))
  have c2 : Nat.Coprime 2 x := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 fun h => by
    have := (ZMod.natCast_eq_zero_iff _ 4).2 (h4 2 h)
    push_cast at this; revert this; generalize (n : ZMod 4) = a; revert a; decide
  have c17 : Nat.Coprime 17 x := (Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 fun h => by
    have := (ZMod.natCast_eq_zero_iff _ 289).2 (h4 17 h)
    push_cast at this; revert this; generalize (n : ZMod 289) = a; revert a; decide
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2
    (show Nat.Coprime (x ^ p) (2 ^ 3 * 17) from ((c2.pow_left 3).mul_left c17).symm.pow_left p)
  have huv' := congrArg (Int.cast : ℤ → R) huv
  push_cast at huv'
  have hcop : IsCoprime w (star w) :=
    ⟨(u : R) * star w + (v : R) * (-w + 2 * star w), -(v : R) * star w, by
      linear_combination (u : R) * hprod - (v : R) * hsq + huv'⟩
  have hI : span {w} * span {star w} = span {(x : R)} ^ p := by
    rw [span_singleton_mul_span_singleton, span_singleton_pow, hprod]
  have hg : IsUnit (gcd (span {w}) (span {star w})) := by
    rw [gcd_eq_sup, (isCoprime_iff_sup_eq).1 ((isCoprime_span_singleton_iff _ _).2 hcop),
      ← one_eq_top]
    exact isUnit_one
  obtain ⟨I, hIw⟩ := exists_eq_pow_of_mul_eq_pow hg hI
  have hw0 : w ≠ 0 := by simp [w, QuadraticAlgebra.ext_iff]
  have hI0 : I ≠ ⊥ := by
    rintro rfl
    rw [bot_pow (by omega), span_singleton_eq_bot] at hIw
    exact hw0 hIw
  obtain ⟨⟨c, hc⟩⟩ := all4 _ I rfl hI0
  rw [submodule_span_eq] at hc
  obtain ⟨k, hk⟩ := hp.odd_of_ne_two (by omega)
  obtain ⟨⟨z0, hz0⟩⟩ := cancel_span (y := c ^ (k * k + k)) (pow_ne_zero p hw0) (by
    rw [← span_singleton_pow, ← hc, ← pow_mul, mul_comm, ← pow_succ,
      show 4 * (k * k + k) + 1 = p * p by subst hk; ring, pow_mul, ← hIw, span_singleton_pow])
  rw [hz0, submodule_span_eq, span_singleton_pow, span_singleton_eq_span_singleton] at hIw
  obtain ⟨e, he⟩ := hIw
  rcases unit_cases e with h | h
  · exact ⟨z0, by rw [← he, h, mul_one]⟩
  · exact ⟨-z0, by rw [Odd.neg_pow ⟨k, hk⟩, ← he, h]; ring⟩

lemma im_dvd (z : R) : ∀ n : ℕ, z.im ∣ (z ^ (n + 1)).im := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]; simp only [im_mul, zero_mul, add_zero]
    exact dvd_add (dvd_mul_left _ _) (dvd_mul_of_dvd_left ih _)

lemma pow_two_pow (a : ℤ) (ha : Odd a) : ∀ k : ℕ, ∃ α u : ℤ, Odd α ∧ Odd u ∧
    (⟨a, 1⟩ : R) ^ (2 ^ k) = ⟨α, 2 ^ k * u⟩ := by
  intro k
  induction k with
  | zero => exact ⟨a, 1, ha, odd_one, by simp⟩
  | succ k ih =>
    obtain ⟨α, u, hα, hu, h⟩ := ih
    refine ⟨α ^ 2 - 34 * (2 ^ k * u) ^ 2, α * u, ?_, hα.mul hu, ?_⟩
    · have he : Even (34 * (2 ^ k * u) ^ 2) := ⟨17 * (2 ^ k * u) ^ 2, by ring⟩
      exact hα.pow.sub_even he
    · rw [pow_succ, pow_mul, h]
      ext <;> simp [sq] <;> ring

lemma pow_mul_odd (ρ : ℕ) (α u : ℤ) (hα : Odd α) (hu : Odd u) : ∀ n : ℕ, ∃ A c : ℤ,
    Odd A ∧ 2 ∣ c - n ∧ (⟨α, 2 ^ ρ * u⟩ : R) ^ n = ⟨A, 2 ^ ρ * c⟩ := by
  intro n
  induction n with
  | zero => exact ⟨1, 0, odd_one, by simp, by ext <;> simp⟩
  | succ n ih =>
    obtain ⟨A, c, hA, hc, h⟩ := ih
    refine ⟨A * α - 34 * (2 ^ ρ * c) * (2 ^ ρ * u), A * u + c * α, ?_, ?_, ?_⟩
    · have he : Even (34 * (2 ^ ρ * c) * (2 ^ ρ * u)) :=
        ⟨17 * (2 ^ ρ * c) * (2 ^ ρ * u), by ring⟩
      exact (hA.mul hα).sub_even he
    · obtain ⟨s, hs⟩ := hA.mul hu
      obtain ⟨t, ht⟩ := hα
      obtain ⟨r, hr⟩ := hc
      exact ⟨s + c * t + r, by push_cast; linear_combination hs + c * ht + hr⟩
    · rw [pow_succ, h]
      ext <;> simp <;> ring

lemma two_pow_dvd (N : ℤ) (hN : Odd N) : ∀ k : ℕ, (2 : ℤ) ^ (k + 3) ∣ N ^ (2 ^ (k + 1)) - 1 := by
  intro k
  induction k with
  | zero =>
    obtain ⟨t, rfl⟩ := hN
    obtain ⟨s, hs⟩ := Int.even_mul_succ_self t
    exact ⟨s, by norm_num; linear_combination 4 * hs⟩
  | succ k ih =>
    obtain ⟨q, hq⟩ := ih
    refine ⟨q * (2 ^ (k + 2) * q + 1), ?_⟩
    rw [pow_succ 2 (k + 1), pow_mul]
    linear_combination (N ^ 2 ^ (k + 1) + 1 + 2 ^ (k + 3) * q) * hq

/-- The case `p ≡ 1 (mod 4)`: a `2`-adic argument. -/
lemma case_one_mod_four (a : ℤ) (ha : Odd a) (p : ℕ) (hp1 : 1 < p) (hp : p % 4 = 1) (ε : ℤ)
    (hε : ε = 1 ∨ ε = -1) : ((⟨a, 1⟩ : R) ^ p).im ≠ ε := by
  intro him
  obtain ⟨ρ, m, hm, hpm⟩ := Nat.exists_eq_two_pow_mul_odd (n := p - 1) (by omega)
  have hρ : 2 ≤ ρ := by
    rcases ρ with _ | _ | ρ
    · obtain ⟨j, rfl⟩ := hm; simp at hpm; omega
    · obtain ⟨j, rfl⟩ := hm; simp at hpm; omega
    · omega
  obtain ⟨α, u, hα, hu, h2⟩ := pow_two_pow a ha ρ
  obtain ⟨A, c, hA, hc, hw⟩ := pow_mul_odd ρ α u hα hu m
  have hzp : (⟨a, 1⟩ : R) ^ (p - 1) = ⟨A, 2 ^ ρ * c⟩ := by
    rw [hpm, pow_mul, h2, hw]
  have hz : (⟨a, 1⟩ : R) ^ p = ⟨A, 2 ^ ρ * c⟩ * ⟨a, 1⟩ := by
    rw [← hzp, ← pow_succ]; congr 1; omega
  have hcodd : Odd c := by
    obtain ⟨j, hj⟩ := hm
    obtain ⟨r, hr⟩ := hc
    exact ⟨r + j, by rw [hj] at hr; push_cast at hr; linarith⟩
  have hn : A ^ 2 + 34 * (2 ^ ρ * c) ^ 2 = (a ^ 2 + 34) ^ (p - 1) := by
    have := map_pow QuadraticAlgebra.norm (⟨a, 1⟩ : R) (p - 1)
    rw [hzp] at this; simp [norm_def] at this; linear_combination this
  rw [hz] at him
  simp at him
  -- `K = 2 ^ ρ = 4 L`
  obtain ⟨L, hL⟩ : ∃ L : ℤ, (2 : ℤ) ^ ρ = 4 * L :=
    ⟨2 ^ (ρ - 2), by rw [show ρ = (ρ - 2) + 2 by omega, pow_add]; norm_num; ring⟩
  have hdiv : (2 : ℤ) ^ (ρ + 2) ∣ (a ^ 2 + 34) ^ (p - 1) - 1 := by
    have h1 := two_pow_dvd (a ^ 2 + 34) (by
      exact ha.pow.add_even ⟨17, by ring⟩) (ρ - 1)
    rw [show ρ - 1 + 3 = ρ + 2 by omega, show ρ - 1 + 1 = ρ by omega] at h1
    refine h1.trans ?_
    rw [hpm, pow_mul]
    have := sub_dvd_pow_sub_pow ((a ^ 2 + 34) ^ 2 ^ ρ) 1 m
    rwa [one_pow] at this
  obtain ⟨q, hq⟩ := hdiv
  set K : ℤ := 2 ^ ρ with hK
  set P : ℤ := (a ^ 2 + 34) ^ (p - 1) with hP
  have hε2 : ε ^ 2 = 1 := by rcases hε with rfl | rfl <;> norm_num
  have h4K : (2 : ℤ) ^ (ρ + 2) = 4 * K := by rw [hK, pow_add]; ring
  rw [h4K] at hq
  have key : 2 * K * (ε * c * a) = 2 * K * (2 * (L * (c ^ 2 * a ^ 2 + 34 * c ^ 2) - q)) := by
    linear_combination hε2 + K * (c ^ 2 * a ^ 2 + 34 * c ^ 2) * hL
      + (A + ε - K * c * a) * him - hn - hq
  have hKne : (2 : ℤ) * K ≠ 0 := by rw [hK]; positivity
  have key2 := mul_left_cancel₀ hKne key
  have hodd : Odd (ε * c * a) := by
    have : Odd ε := by rcases hε with rfl | rfl <;> decide
    exact (this.mul hcodd).mul ha
  exact (Int.not_even_iff_odd.2 hodd) ⟨L * (c ^ 2 * a ^ 2 + 34 * c ^ 2) - q, by rw [key2]; ring⟩

/-- The case `p ≡ 3 (mod 4)`: `z ^ 8 ≡ 1 (mod 24)` for odd `a`, then a congruence modulo `24`. -/
lemma case_three_mod_four (a : ℤ) (ha : Odd a) (p : ℕ) (hp : p % 4 = 3) (ε : ℤ)
    (hε : ε = 1 ∨ ε = -1) : ((⟨a, 1⟩ : R) ^ p).im ≠ ε := by
  intro him
  obtain ⟨b, rfl⟩ := ha
  have h8 : algebraMap ℤ R 24 ∣ (⟨2 * b + 1, 1⟩ : R) ^ 8 - 1 := by
    refine algebraMap_dvd_iff.2 ⟨?_, ?_⟩ <;> simp [pow_succ] <;>
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 24).1 <;> push_cast <;>
      generalize (b : ZMod 24) = x <;> revert x <;> decide
  have hd : algebraMap ℤ R 24 ∣ (⟨2 * b + 1, 1⟩ : R) ^ p - (⟨2 * b + 1, 1⟩ : R) ^ (p % 8) := by
    rw [show (⟨2 * b + 1, 1⟩ : R) ^ p - (⟨2 * b + 1, 1⟩ : R) ^ (p % 8) =
        (((⟨2 * b + 1, 1⟩ : R) ^ 8) ^ (p / 8) - 1 ^ (p / 8)) * (⟨2 * b + 1, 1⟩ : R) ^ (p % 8) by
      rw [one_pow, sub_mul, one_mul, ← pow_mul, ← pow_add, Nat.div_add_mod]]
    exact (h8.trans (sub_dvd_pow_sub_pow _ _ _)).mul_right _
  have h := (algebraMap_dvd_iff.1 hd).2
  rw [im_sub, him] at h
  rcases (by omega : p % 8 = 3 ∨ p % 8 = 7) with h8 | h8 <;> rw [h8] at h <;>
    simp [pow_succ] at h <;>
    replace h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 24).2 (by exact_mod_cast h) <;>
    push_cast at h <;>
    rcases hε with rfl | rfl <;> push_cast at h <;> revert h <;>
      generalize (b : ZMod 24) = x <;> revert x <;> decide

lemma im_pow_ne_one (p : ℕ) (hp : p % 2 = 1) (hp1 : 1 < p) (z : R) : (z ^ p).im ≠ 1 := by
  intro h
  have hb : z.im = 1 ∨ z.im = -1 := by
    obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
    have hd := im_dvd z k
    rw [h] at hd
    rcases Int.isUnit_iff.1 (isUnit_of_dvd_one hd) with h' | h' <;> simp [h']
  have ha : Odd z.re := by
    refine Int.not_even_iff_odd.1 (fun ⟨c, hc⟩ => ?_)
    have h2 : algebraMap ℤ R 2 ∣ z ^ 2 :=
      algebraMap_dvd_iff.2 ⟨⟨2 * c ^ 2 - 17 * z.im ^ 2, by simp [sq, hc]; ring⟩, ⟨2 * c * z.im, by simp [sq, hc]; ring⟩⟩
    have := (algebraMap_dvd_iff.1 (h2.trans (pow_dvd_pow z (by omega : 2 ≤ p)))).2
    rw [h] at this
    omega
  have key : ∀ ε : ℤ, (ε = 1 ∨ ε = -1) → ((⟨z.re, 1⟩ : R) ^ p).im ≠ ε := by
    intro ε hε
    rcases (by omega : p % 4 = 1 ∨ p % 4 = 3) with h4 | h4
    · exact case_one_mod_four z.re ha p hp1 h4 ε hε
    · exact case_three_mod_four z.re ha p h4 ε hε
  rcases hb with hb | hb
  · have hz : z = ⟨z.re, 1⟩ := by ext <;> simp [hb]
    rw [hz] at h
    exact key 1 (Or.inl rfl) h
  · have hz : star z = ⟨z.re, 1⟩ := by ext <;> simp [hb]
    have hs : ((star z) ^ p).im = -1 := by
      rw [← star_pow]; exact (im_star _).trans (by rw [h])
    rw [hz] at hs
    exact key (-1) (Or.inr rfl) hs

end OMA.A114965

open OMA.A114965 in
theorem OMA.solution : type_of% @OMA.S_oeis_a114965.main := by
  intro n x k hk hx
  simp only [OMA.S_oeis_a114965.a] at hx
  rcases Nat.even_or_odd k with ⟨m, rfl⟩ | hodd
  · have h4 := congrArg (Nat.cast : ℕ → ZMod 4) (hx.trans (by ring : x ^ (m + m) = (x ^ m) ^ 2))
    push_cast at h4
    revert h4; generalize (n : ZMod 4) = u; generalize ((x : ZMod 4) ^ m) = v; revert u v; decide
  · have hp := Nat.minFac_prime (show k ≠ 1 by omega)
    have hp2 : k.minFac ≠ 2 := fun h => Nat.not_even_iff_odd.2 hodd (even_iff_two_dvd.2 (h ▸ k.minFac_dvd))
    obtain ⟨m, hm⟩ := k.minFac_dvd
    obtain ⟨z, hz⟩ := descent _ hp (by have := hp.two_le; omega) n (x ^ m)
      (by rw [hx, ← pow_mul, mul_comm, ← hm])
    exact im_pow_ne_one _ (Nat.odd_iff.1 (hp.odd_of_ne_two hp2)) hp.one_lt z (by rw [hz])
