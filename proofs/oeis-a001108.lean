import OMAStatements.S_oeis_a001108

-- Problem: A001108: a(n)-th triangular number is a square: a(n+1) = 6*a(n) - a(n-1) + 2, with a(0) = 0, a(1) = 1.
-- Upstream: formal-conjectures statements/oeis-a001108.lean:0 (declaration OMA.S_oeis_a001108.main)
-- Credit: @nerotulip90 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
--
-- Proof (Grok Bot w3): sigma 1 m is odd iff m = s^2 or 2 s^2 (multiplicativity of sigma and
-- Nat.sq_mul_squarefree). T = n(n+1)/2 = 2s^2 is impossible since n(n+1) is never a square, and
-- T = t^2 forces n to have even exponents at odd primes. Finally n(n+1) = 2t^2 iff
-- (2n+1)^2 - 8t^2 = 1, whose solutions are the powers of the fundamental Pell solution (3,1),
-- and x_k = 2 a(k) + 1.

namespace OMA.A001108Proof
open OMA.S_oeis_a001108 ArithmeticFunction

lemma odd_prod_iff {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℕ) :
    Odd (∏ i ∈ s, f i) ↔ ∀ i ∈ s, Odd (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Nat.odd_mul, ih, Finset.forall_mem_insert]

lemma sig_pp_odd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (e : ℕ) :
    Odd (sigma 1 (p ^ e)) ↔ Even e := by
  rw [sigma_one_apply_prime_pow hp]
  have hpo : Odd p := hp.odd_of_ne_two hp2
  induction e with
  | zero => simp
  | succ e ih =>
    have hq : ¬ Even (p ^ (e + 1)) := Nat.not_even_iff_odd.mpr hpo.pow
    rw [Finset.sum_range_succ, Nat.odd_add, Nat.even_add_one]
    tauto

lemma sig_2p_odd (e : ℕ) : Odd (sigma 1 (2 ^ e)) := by
  rw [sigma_one_apply_prime_pow Nat.prime_two]
  induction e with
  | zero => simp
  | succ e ih =>
    rw [Finset.sum_range_succ]
    exact ih.add_even (by rw [pow_succ']; exact even_two_mul _)

lemma sig_odd_iff {m : ℕ} (hm : m ≠ 0) :
    Odd (sigma 1 m) ↔ ∀ p, p.Prime → p ≠ 2 → Even (m.factorization p) := by
  rw [isMultiplicative_sigma.multiplicative_factorization _ hm, Finsupp.prod, odd_prod_iff]
  constructor
  · intro h p hp hp2
    by_cases hpm : p ∈ m.factorization.support
    · exact (sig_pp_odd hp hp2 _).mp (h p hpm)
    · rw [Finsupp.notMem_support_iff.mp hpm]; exact ⟨0, rfl⟩
  · intro h p hpm
    have hp : p.Prime := Nat.prime_of_mem_primeFactors (by simpa using hpm)
    by_cases hp2 : p = 2
    · subst hp2; exact sig_2p_odd _
    · exact (sig_pp_odd hp hp2 _).mpr (h p hp hp2)

lemma sqf_iff {m : ℕ} (hm : m ≠ 0) :
    (∀ p, p.Prime → p ≠ 2 → Even (m.factorization p)) ↔ ∃ s, m = s ^ 2 ∨ m = 2 * s ^ 2 := by
  constructor
  · intro h
    obtain ⟨a, b, hab, ha⟩ := Nat.sq_mul_squarefree m
    have ha0 : a ≠ 0 := by rintro rfl; simp at hab; exact hm hab.symm
    have hb0 : b ≠ 0 := by rintro rfl; simp at hab; exact hm hab.symm
    have hsub : ∀ p ∈ a.primeFactors, p = 2 := by
      intro p hp
      by_contra hp2
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hpa : p ∣ a := Nat.dvd_of_mem_primeFactors hp
      have h1 : a.factorization p = 1 := by
        have hle := ha.natFactorization_le_one p
        have hge : 1 ≤ a.factorization p := (hpp.dvd_iff_one_le_factorization ha0).mp hpa
        omega
      have := h p hpp hp2
      rw [← hab, Nat.factorization_mul (pow_ne_zero _ hb0) ha0, Finsupp.add_apply,
        Nat.factorization_pow, Finsupp.smul_apply, h1, smul_eq_mul] at this
      exact (Nat.not_even_iff_odd.mpr ⟨b.factorization p, by ring⟩) this
    have hprod := Nat.prod_primeFactors_of_squarefree ha
    refine ⟨b, ?_⟩
    by_cases h2 : 2 ∈ a.primeFactors
    · have : a.primeFactors = {2} := by
        ext p; constructor
        · intro hp; simp [hsub p hp]
        · intro hp; simp at hp; subst hp; exact h2
      rw [this] at hprod; simp at hprod
      right; rw [← hab, ← hprod]; ring
    · have : a.primeFactors = ∅ := by
        ext p; constructor
        · intro hp; exact absurd (hsub p hp ▸ hp) h2
        · simp
      rw [this] at hprod; simp at hprod
      left; rw [← hab, ← hprod]; ring
  · rintro ⟨s, rfl | rfl⟩ p hp hp2
    · have hs : s ≠ 0 := by rintro rfl; simp at hm
      rw [Nat.factorization_pow]; simp
    · have hs : s ≠ 0 := by rintro rfl; simp at hm
      rw [Nat.factorization_mul (by norm_num) (pow_ne_zero _ hs), Nat.factorization_pow,
        Nat.prime_two.factorization]
      simp [Ne.symm hp2]

def a₁ : Pell.Solution₁ (8 : ℤ) := Pell.Solution₁.mk 3 1 (by norm_num)

lemma a₁x : a₁.x = 3 := Pell.Solution₁.x_mk _ _ _
lemma a₁y : a₁.y = 1 := Pell.Solution₁.y_mk _ _ _

lemma fund : Pell.IsFundamental a₁ := by
  refine ⟨by rw [a₁x]; norm_num, by rw [a₁y]; norm_num, ?_⟩
  intro b hb
  rw [a₁x]
  by_contra h
  have hx : b.x = 2 := by omega
  have hp := b.prop
  rw [hx] at hp
  have : 8 * b.y ^ 2 = 3 := by linarith
  omega

noncomputable def X (k : ℕ) : ℤ := (a₁ ^ k).x
noncomputable def Y (k : ℕ) : ℤ := (a₁ ^ k).y

lemma X_succ (k : ℕ) : X (k + 1) = 3 * X k + 8 * Y k := by
  simp only [X, Y, pow_succ, Pell.Solution₁.x_mul, a₁x, a₁y]; ring

lemma Y_succ (k : ℕ) : Y (k + 1) = X k + 3 * Y k := by
  simp only [X, Y, pow_succ, Pell.Solution₁.y_mul, a₁x, a₁y]; ring

lemma X_rec (k : ℕ) : X (k + 2) = 6 * X (k + 1) - X k := by
  have h1 := X_succ (k + 1)
  have h2 := Y_succ k
  have h3 := X_succ k
  rw [h1, h2]; linarith

lemma Y_nonneg (k : ℕ) : 0 ≤ Y k := by
  induction k with
  | zero => simp [Y]
  | succ k ih =>
    rw [Y_succ]
    have : 0 < X k := Pell.Solution₁.x_pow_pos (by rw [a₁x]; norm_num) k
    linarith

lemma XY_prop (k : ℕ) : X k ^ 2 - 8 * Y k ^ 2 = 1 := (a₁ ^ k).prop

lemma aX (k : ℕ) : 2 * a k + 1 = X k ∧ 2 * a (k + 1) + 1 = X (k + 1) := by
  induction k with
  | zero =>
    refine ⟨by simp [a, X], ?_⟩
    simp [a, X, a₁x]
  | succ k ih =>
    refine ⟨ih.2, ?_⟩
    rw [X_rec]
    show 2 * (6 * a (k + 1) - a k + 2) + 1 = _
    linarith [ih.1, ih.2]

lemma tri_iff (n : ℕ) : (∃ t : ℕ, n * (n + 1) = 2 * t ^ 2) ↔ ∃ k, a k = n := by
  constructor
  · rintro ⟨t, ht⟩
    have hpr : ((2 * n + 1 : ℕ) : ℤ) ^ 2 - 8 * ((t : ℕ) : ℤ) ^ 2 = 1 := by
      have : ((n * (n + 1) : ℕ) : ℤ) = ((2 * t ^ 2 : ℕ) : ℤ) := by rw [ht]
      push_cast at this ⊢; linear_combination 4 * this
    let b : Pell.Solution₁ (8 : ℤ) := Pell.Solution₁.mk _ _ hpr
    obtain ⟨k, hk⟩ := fund.eq_pow_of_nonneg (a := b)
      (by simp [b, Pell.Solution₁.x_mk]) (by simp [b, Pell.Solution₁.y_mk])
    refine ⟨k, ?_⟩
    have h1 : X k = 2 * n + 1 := by
      simp only [X, ← hk, b, Pell.Solution₁.x_mk]; push_cast; ring
    have := (aX k).1
    linarith
  · rintro ⟨k, hk⟩
    have h1 := (aX k).1
    have hp := XY_prop k
    have hy := Y_nonneg k
    refine ⟨(Y k).toNat, ?_⟩
    have hY : ((Y k).toNat : ℤ) = Y k := Int.toNat_of_nonneg hy
    have : ((n * (n + 1) : ℕ) : ℤ) = ((2 * (Y k).toNat ^ 2 : ℕ) : ℤ) := by
      push_cast; rw [hY, ← hk]; nlinarith
    exact_mod_cast this


lemma sig_Q {m : ℕ} (hm : m ≠ 0) : Odd (sigma 1 m) ↔ ∃ s, m = s ^ 2 ∨ m = 2 * s ^ 2 :=
  (sig_odd_iff hm).trans (sqf_iff hm)

lemma not_four_sq {n s : ℕ} (hn : 0 < n) : n * (n + 1) ≠ 4 * s ^ 2 := by
  intro h
  rcases Nat.lt_or_ge n (2 * s) with h1 | h1
  · have : n + 1 ≤ 2 * s := h1
    nlinarith
  · nlinarith

lemma n_even_exp {n t : ℕ} (hn : 0 < n) (ht : n * (n + 1) = 2 * t ^ 2) :
    ∀ p, p.Prime → p ≠ 2 → Even (n.factorization p) := by
  intro p hp hp2
  have ht0 : t ≠ 0 := by rintro rfl; simp at ht; omega
  have hf := congrArg (fun m => m.factorization p) ht
  rw [Nat.factorization_mul (by omega) (by omega), Nat.factorization_mul (by norm_num)
    (pow_ne_zero _ ht0), Nat.factorization_pow, Nat.prime_two.factorization] at hf
  simp [Ne.symm hp2] at hf
  by_cases hpn : p ∣ n
  · have hn1 : ¬ p ∣ n + 1 := by
      intro h
      have : p ∣ 1 := (Nat.dvd_add_right hpn).mp h
      exact hp.one_lt.ne' (Nat.dvd_one.mp this)
    rw [Nat.factorization_eq_zero_of_not_dvd hn1] at hf
    exact ⟨t.factorization p, by omega⟩
  · rw [Nat.factorization_eq_zero_of_not_dvd hpn]; exact ⟨0, rfl⟩

end OMA.A001108Proof

open OMA.A001108Proof OMA.S_oeis_a001108 ArithmeticFunction in
theorem OMA.solution : type_of% @OMA.S_oeis_a001108.main := by
  intro n hn
  have hT : n * (n + 1) / 2 * 2 = n * (n + 1) :=
    Nat.div_mul_cancel (Nat.even_mul_succ_self n).two_dvd
  constructor
  · rintro ⟨_, h2⟩
    have hT0 : n * (n + 1) / 2 ≠ 0 := by
      intro h; rw [h] at hT; simp at hT; omega
    obtain ⟨s, hs | hs⟩ := (sig_Q hT0).mp h2
    · obtain ⟨k, hk⟩ := (tri_iff n).mp ⟨s, by rw [← hT, hs]; ring⟩
      refine ⟨k, ?_, hk⟩
      rcases Nat.eq_zero_or_pos k with rfl | hk1
      · simp [a] at hk; omega
      · exact hk1
    · exact absurd (by rw [← hT, hs]; ring) (not_four_sq (s := s) hn)
  · rintro ⟨k, _, hk⟩
    obtain ⟨t, ht⟩ := (tri_iff n).mpr ⟨k, hk⟩
    have ht0 : t ≠ 0 := by rintro rfl; simp at ht; omega
    refine ⟨(sig_odd_iff (by omega)).mpr (n_even_exp hn ht), ?_⟩
    have : n * (n + 1) / 2 = t ^ 2 := by rw [ht]; simp
    rw [this]
    exact (sig_Q (pow_ne_zero _ ht0)).mpr ⟨t, Or.inl rfl⟩
