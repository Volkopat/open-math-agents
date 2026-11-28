import FormalConjectures.Wikipedia.AgohGiuga

/-!
# Proof of `AgohGiuga.isWeakGiuga_iff_sum_primeFactors`

For a composite integer `n`, we prove `IsWeakGiuga n ↔ ∃ m : ℕ, ∑ p ∈ n.primeFactors, (1/p : ℚ) - 1/n = m`
by showing both sides are equivalent to `Squarefree n ∧ ∀ p ∈ n.primeFactors, p ∣ n / p - 1`:
1. Splitting `Finset.range n` into `n / p` blocks of length `p` shows
   `∑_{i=1}^{n-1} i^{φ(n)} ≡ (n / p) * (-1) (mod p)` for every `p ∈ n.primeFactors` via Fermat's
   little theorem (`p - 1 ∣ φ(n)`), giving `p ∣ 1 + ∑ i^{φ(n)} ↔ p ∣ n / p - 1`, which forces
   squarefreeness and hence equivalence with divisibility by `n`.
2. Clearing the denominator `n` in `∑_{p ∣ n} 1/p - 1/n = m` equates integrality with
   `n ∣ (∑_{p ∣ n} n / p - 1)`, which likewise is equivalent to
   `Squarefree n ∧ ∀ p ∈ n.primeFactors, p ∣ n / p - 1`.
-/

-- Problem: Agoh-Giuga conjecture — isWeakGiuga iff sum primeFactors
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/AgohGiuga.lean:113 (declaration AgohGiuga.isWeakGiuga_iff_sum_primeFactors)
-- Credit: @TheWaler (the owner of the agent is credited as the solver)

namespace AgohGiugaWeakProof

open AgohGiuga
open scoped Nat

private lemma one_lt_of_composite {n : ℕ} (hn : n.Composite) : 1 < n := by
  exact hn.1

private lemma dvd_of_squarefree_forall_primeFactors_dvd {n m : ℕ} (_hn0 : n ≠ 0)
    (hsq : Squarefree n) (h : ∀ p ∈ n.primeFactors, p ∣ m) : n ∣ m := by
  by_cases hm : m = 0
  · simp [hm]
  rw [← Nat.prod_primeFactors_of_squarefree hsq, Nat.prod_primeFactors_dvd_iff hm]
  exact fun p hp => Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hp, h p hp, hm⟩

private lemma squarefree_of_forall_primeFactors_dvd_div_sub_one {n : ℕ} (hn0 : n ≠ 0)
    (h : ∀ p ∈ n.primeFactors, p ∣ n / p - 1) : Squarefree n := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hpp
  have hpn : p ∣ n := dvd_trans (dvd_mul_right p p) hpp
  have hmem : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpn, hn0⟩
  have hdvd1 : p ∣ n / p - 1 := h p hmem
  rcases hpp with ⟨k, hk⟩
  have hdiv : n / p = p * k := by
    rw [hk, mul_assoc, Nat.mul_div_cancel_left _ hp.pos]
  have hdvd2 : p ∣ n / p := ⟨k, hdiv⟩
  have hge1 : 1 ≤ n / p := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hpn) hp.pos
  have h1 : p ∣ 1 := by
    have hadd : n / p - 1 + 1 = n / p := Nat.sub_add_cancel hge1
    exact (Nat.dvd_add_right hdvd1).mp (hadd.symm ▸ hdvd2)
  exact hp.not_dvd_one h1

private lemma sum_range_pow_zmod_mul (q d k : ℕ) :
    ((∑ i ∈ Finset.range (q * d), i ^ k : ℕ) : ZMod d) =
      (q : ZMod d) * ∑ r ∈ Finset.range d, (r : ZMod d) ^ k := by
  induction q with
  | zero =>
    simp
  | succ q ih =>
    rw [add_mul, one_mul, Finset.sum_range_add, Nat.cast_add, ih]
    have hblock : ((∑ r ∈ Finset.range d, (q * d + r) ^ k : ℕ) : ZMod d) =
        ∑ r ∈ Finset.range d, (r : ZMod d) ^ k := by
      push_cast
      refine Finset.sum_congr rfl fun r _ => ?_
      simp
    rw [hblock]
    push_cast
    ring

private lemma sum_range_pow_totient_zmod {n p : ℕ} (hn : 1 < n) (hp_mem : p ∈ n.primeFactors) :
    ∑ r ∈ Finset.range p, (r : ZMod p) ^ φ n = -1 := by
  have hp : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
  have hpn : p ∣ n := Nat.dvd_of_mem_primeFactors hp_mem
  have : Fact p.Prime := ⟨hp⟩
  have hφ_pos : 0 < φ n := Nat.totient_pos.mpr (by omega)
  have hφ_dvd : p - 1 ∣ φ n := by
    rw [← Nat.totient_prime hp]
    exact Nat.totient_dvd_of_dvd hpn
  rcases hφ_dvd with ⟨c, hc⟩
  rw [← Nat.Ico_zero_eq_range, Finset.sum_eq_sum_Ico_succ_bot hp.pos]
  have h0 : ((0 : ℕ) : ZMod p) ^ φ n = 0 := by
    rw [Nat.cast_zero, zero_pow hφ_pos.ne']
  rw [h0, zero_add]
  have hones : ∑ r ∈ Finset.Ico 1 p, (r : ZMod p) ^ φ n = ∑ _r ∈ Finset.Ico 1 p, (1 : ZMod p) := by
    refine Finset.sum_congr rfl fun r hr => ?_
    rcases Finset.mem_Ico.mp hr with ⟨hr1, hrp⟩
    have hr_ne : (r : ZMod p) ≠ 0 := by
      intro h0
      have hdvd : p ∣ r := (ZMod.natCast_eq_zero_iff r p).mp h0
      exact absurd (Nat.le_of_dvd (by omega) hdvd) (by omega)
    rw [hc, pow_mul, ZMod.pow_card_sub_one_eq_one hr_ne, one_pow]
  rw [hones, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one,
    Nat.cast_sub hp.pos, ZMod.natCast_self, Nat.cast_one, zero_sub]

private lemma sum_Ioo_eq_sum_range {n k : ℕ} (hk : 0 < k) :
    ∑ i ∈ Finset.Ioo 0 n, i ^ k = ∑ i ∈ Finset.range n, i ^ k := by
  by_cases hn : n = 0
  · subst hn; simp
  have hrange : Finset.range n = insert 0 (Finset.Ioo 0 n) := by
    ext x
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioo]
    omega
  rw [hrange, Finset.sum_insert (by simp), zero_pow hk.ne', zero_add]

private lemma isWeakGiuga_iff_char {n : ℕ} (hn : n.Composite) :
    IsWeakGiuga n ↔ Squarefree n ∧ ∀ p ∈ n.primeFactors, p ∣ n / p - 1 := by
  have hn1 : 1 < n := one_lt_of_composite hn
  have hn0 : n ≠ 0 := by omega
  have hφ_pos : 0 < φ n := Nat.totient_pos.mpr (by omega)
  have hp_iff : ∀ p ∈ n.primeFactors,
      p ∣ 1 + ∑ i ∈ Finset.Ioo 0 n, i ^ φ n ↔ p ∣ n / p - 1 := by
    intro p hp_mem
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
    have hpn : p ∣ n := Nat.dvd_of_mem_primeFactors hp_mem
    have hge1 : 1 ≤ n / p := Nat.div_pos (Nat.le_of_dvd (by omega) hpn) hp.pos
    rw [sum_Ioo_eq_sum_range hφ_pos, ← ZMod.natCast_eq_zero_iff, ← ZMod.natCast_eq_zero_iff]
    have hsum_mod : ((∑ i ∈ Finset.range n, i ^ φ n : ℕ) : ZMod p) = -((n / p : ℕ) : ZMod p) := by
      have h := sum_range_pow_zmod_mul (n / p) p (φ n)
      rw [Nat.div_mul_cancel hpn, sum_range_pow_totient_zmod hn1 hp_mem, mul_neg_one] at h
      exact h
    rw [Nat.cast_add, Nat.cast_one, hsum_mod, Nat.cast_sub hge1, Nat.cast_one]
    constructor <;> intro h
    · linear_combination -h
    · linear_combination -h
  constructor
  · rintro ⟨_, hdvd⟩
    have hall : ∀ p ∈ n.primeFactors, p ∣ n / p - 1 := fun p hp =>
      (hp_iff p hp).mp (dvd_trans (Nat.dvd_of_mem_primeFactors hp) hdvd)
    exact ⟨squarefree_of_forall_primeFactors_dvd_div_sub_one hn0 hall, hall⟩
  · rintro ⟨hsq, hall⟩
    refine ⟨hn, dvd_of_squarefree_forall_primeFactors_dvd hn0 hsq fun p hp => ?_⟩
    exact (hp_iff p hp).mpr (hall p hp)

private lemma sum_primeFactors_iff_char {n : ℕ} (hn : n.Composite) :
    (∃ m : ℕ, ∑ p ∈ n.primeFactors, (1 / p : ℚ) - 1 / n = m) ↔
      Squarefree n ∧ ∀ p ∈ n.primeFactors, p ∣ n / p - 1 := by
  have hn1 : 1 < n := one_lt_of_composite hn
  have hn0 : n ≠ 0 := by omega
  have hn_q_ne : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
  set S : ℕ := ∑ p ∈ n.primeFactors, n / p
  have hS_ge1 : 1 ≤ S := by
    rcases Nat.nonempty_primeFactors.mpr hn1 with ⟨p0, hp0⟩
    have h1 : 1 ≤ n / p0 := Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hp0))
      (Nat.prime_of_mem_primeFactors hp0).pos
    exact le_trans h1 (Finset.single_le_sum (f := fun p => n / p) (fun _ _ => Nat.zero_le _) hp0)
  have hclear : (n : ℚ) * (∑ p ∈ n.primeFactors, (1 / p : ℚ) - 1 / n) = ((S - 1 : ℕ) : ℚ) := by
    rw [mul_sub, Finset.mul_sum, mul_one_div_cancel hn_q_ne, Nat.cast_sub hS_ge1, Nat.cast_one]
    congr 1
    push_cast [S]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hpn : p ∣ n := Nat.dvd_of_mem_primeFactors hp
    have hp_ne : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero
    have hmul : ((n / p : ℕ) : ℚ) * (p : ℚ) = (n : ℚ) := by
      exact_mod_cast Nat.div_mul_cancel hpn
    rw [mul_one_div, div_eq_iff hp_ne]
    exact hmul.symm
  have hdvd_iff : (∃ m : ℕ, ∑ p ∈ n.primeFactors, (1 / p : ℚ) - 1 / n = m) ↔ n ∣ S - 1 := by
    constructor
    · rintro ⟨m, hm⟩
      refine ⟨m, ?_⟩
      have hq : ((S - 1 : ℕ) : ℚ) = ((n * m : ℕ) : ℚ) := by
        rw [← hclear, hm, Nat.cast_mul]
      exact Nat.cast_injective hq
    · rintro ⟨m, hm⟩
      refine ⟨m, ?_⟩
      apply mul_left_cancel₀ hn_q_ne
      rw [hclear, hm, Nat.cast_mul]
  have hp_sum_iff : ∀ p ∈ n.primeFactors, p ∣ S - 1 ↔ p ∣ n / p - 1 := by
    intro p hp
    have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpn : p ∣ n := Nat.dvd_of_mem_primeFactors hp
    have hge1 : 1 ≤ n / p := Nat.div_pos (Nat.le_of_dvd (by omega) hpn) hp_prime.pos
    have hsplit : S = n / p + ∑ q ∈ n.primeFactors.erase p, n / q :=
      (Finset.add_sum_erase n.primeFactors (fun q => n / q) hp).symm
    have hsub_eq : S - 1 = (n / p - 1) + ∑ q ∈ n.primeFactors.erase p, n / q := by
      omega
    have herase_dvd : p ∣ ∑ q ∈ n.primeFactors.erase p, n / q := by
      refine Finset.dvd_sum fun q hq => ?_
      rcases Finset.mem_erase.mp hq with ⟨hqp, hq_mem⟩
      have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq_mem
      have hqn : q ∣ n := Nat.dvd_of_mem_primeFactors hq_mem
      have hcop : Nat.Coprime p q := (Nat.coprime_primes hp_prime hq_prime).mpr (Ne.symm hqp)
      have hmul : p ∣ (n / q) * q := by rwa [Nat.div_mul_cancel hqn]
      exact hcop.dvd_of_dvd_mul_right hmul
    rw [hsub_eq, Nat.dvd_add_left herase_dvd]
  rw [hdvd_iff]
  constructor
  · intro hdvd
    have hall : ∀ p ∈ n.primeFactors, p ∣ n / p - 1 := fun p hp =>
      (hp_sum_iff p hp).mp (dvd_trans (Nat.dvd_of_mem_primeFactors hp) hdvd)
    exact ⟨squarefree_of_forall_primeFactors_dvd_div_sub_one hn0 hall, hall⟩
  · rintro ⟨hsq, hall⟩
    exact dvd_of_squarefree_forall_primeFactors_dvd hn0 hsq fun p hp =>
      (hp_sum_iff p hp).mpr (hall p hp)

end AgohGiugaWeakProof

theorem OMA.solution : type_of% @AgohGiuga.isWeakGiuga_iff_sum_primeFactors := by
  intro n hn
  exact (AgohGiugaWeakProof.isWeakGiuga_iff_char hn).trans
    (AgohGiugaWeakProof.sum_primeFactors_iff_char hn).symm
