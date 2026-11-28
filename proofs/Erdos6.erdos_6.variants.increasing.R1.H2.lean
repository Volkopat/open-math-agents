import OMAReductions.R_Erdos6_erdos_6_variants_increasing_R1
import Mathlib

/-!
Proof of Erdos6.erdos_6.variants.increasing.R1.H2: Bombieri-Vinogradov implies the
Maynard-Tao prime cluster theorem for admissible affine forms with a common slope.
-/

namespace Erdos6MaynardTao

open scoped BigOperators
open Finset

-- ## Section 1: Elementary arithmetic, CRT, and 1D Mertens bounds

/-- The modified totient function phi2(n) = prod_{p | n} (p - 2) for squarefree n. -/
noncomputable def phi2 (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors, (p - 2)

/-- The radical rad(n) = prod_{p | n} p. -/
def rad (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors, p

lemma squarefree_pos {n : ℕ} (hn : Squarefree n) : 0 < n := by
  rcases Nat.eq_zero_or_pos n with rfl | h
  · exfalso
    have h2 : IsUnit (2 : ℕ) := hn 2 (by simp)
    exact (by decide : ¬ IsUnit (2 : ℕ)) h2
  · exact h

lemma squarefree_ne_zero {n : ℕ} (hn : Squarefree n) : n ≠ 0 :=
  (squarefree_pos hn).ne'

lemma factorization_eq_one_of_squarefree {n p : ℕ} (hn : Squarefree n)
    (hp : p ∈ n.primeFactors) : n.factorization p = 1 := by
  have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hle : n.factorization p ≤ 1 := by
    by_contra hgt
    push Not at hgt
    have hdvd : p ^ 2 ∣ n := dvd_trans (pow_dvd_pow p hgt) (Nat.ordProj_dvd n p)
    have hu : IsUnit p := hn p (by simpa [sq] using hdvd)
    exact hprime.ne_one (Nat.isUnit_iff.mp hu)
  have hpos : 0 < n.factorization p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)
  exact le_antisymm hle hpos

lemma squarefree_eq_prod_primeFactors {n : ℕ} (hn : Squarefree n) :
    ∏ p ∈ n.primeFactors, p = n := by
  have h0 : n ≠ 0 := squarefree_ne_zero hn
  conv_rhs => rw [← Nat.prod_factorization_pow_eq_self h0]
  rw [Nat.primeFactors]
  refine Finset.prod_congr rfl ?_
  intro p hp
  have heq := factorization_eq_one_of_squarefree hn hp
  simp [heq]

lemma rad_eq_self_of_squarefree {n : ℕ} (hn : Squarefree n) : rad n = n :=
  squarefree_eq_prod_primeFactors hn

lemma rad_dvd_self (n : ℕ) : rad n ∣ n := by
  rcases eq_or_ne n 0 with rfl | h0
  · exact dvd_zero _
  · unfold rad
    conv_rhs => rw [← Nat.prod_factorization_pow_eq_self h0]
    rw [Nat.primeFactors]
    refine Finset.prod_dvd_prod_of_dvd _ _ ?_
    intro p hp
    have hpos : 0 < n.factorization p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)
    simpa using pow_dvd_pow p hpos

lemma rad_pos {n : ℕ} : 0 < rad n := by
  unfold rad
  refine Finset.prod_pos ?_
  intro p hp
  exact (Nat.prime_of_mem_primeFactors hp).pos

lemma squarefree_rad (n : ℕ) : Squarefree (rad n) := by
  unfold rad
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hsq
  have h1 : p ∣ ∏ q ∈ n.primeFactors, q := dvd_trans (dvd_mul_right p p) hsq
  rw [hp.prime.dvd_finsetProd_iff] at h1
  rcases h1 with ⟨q, hq, hpq⟩
  have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hpq_eq : p = q := (Nat.prime_dvd_prime_iff_eq hp hqprime).mp hpq
  subst hpq_eq
  rw [← Finset.mul_prod_erase _ _ hq] at hsq
  have hdvd_rest : p ∣ ∏ x ∈ n.primeFactors.erase p, x :=
    (mul_dvd_mul_iff_left hp.ne_zero).mp hsq
  rw [hp.prime.dvd_finsetProd_iff] at hdvd_rest
  rcases hdvd_rest with ⟨r, hr, hpr⟩
  have hr_mem : r ∈ n.primeFactors := Finset.mem_of_mem_erase hr
  have hr_ne : r ≠ p := Finset.ne_of_mem_erase hr
  have hr_prime : r.Prime := Nat.prime_of_mem_primeFactors hr_mem
  exact hr_ne ((Nat.prime_dvd_prime_iff_eq hp hr_prime).mp hpr).symm

lemma rad_primeFactors (n : ℕ) : (rad n).primeFactors = n.primeFactors := by
  ext p
  simp only [Nat.mem_primeFactors, ne_eq, rad_pos.ne', not_false_eq_true, and_true]
  constructor
  · rintro ⟨hp, hdvd⟩
    unfold rad at hdvd
    rw [hp.prime.dvd_finsetProd_iff] at hdvd
    rcases hdvd with ⟨q, hq, hpq⟩
    have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hq
    have heq : p = q := (Nat.prime_dvd_prime_iff_eq hp hqprime).mp hpq
    rw [heq]
    exact ⟨hqprime, Nat.dvd_of_mem_primeFactors hq, by
      intro h0
      subst h0
      simp at hq⟩
  · rintro ⟨hp, hdvd, h0⟩
    refine ⟨hp, ?_⟩
    unfold rad
    exact Finset.dvd_prod_of_mem _ (Nat.mem_primeFactors.mpr ⟨hp, hdvd, h0⟩)

lemma coprime_rad_iff {n W : ℕ} (hn : n ≠ 0) : Nat.Coprime (rad n) W ↔ Nat.Coprime n W := by
  constructor
  · intro h
    rw [Nat.coprime_iff_gcd_eq_one]
    by_contra hne
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
    have hpn : p ∣ n := dvd_trans hpdvd (Nat.gcd_dvd_left n W)
    have hpW : p ∣ W := dvd_trans hpdvd (Nat.gcd_dvd_right n W)
    have hpr : p ∣ rad n := by
      unfold rad
      exact Finset.dvd_prod_of_mem _ (Nat.mem_primeFactors.mpr ⟨hp, hpn, hn⟩)
    exact hp.not_dvd_one (h ▸ Nat.dvd_gcd hpr hpW)
  · intro h
    exact h.coprime_dvd_left (rad_dvd_self n)

lemma totient_eq_prod_primeFactors_of_squarefree {n : ℕ} (hn : Squarefree n) :
    Nat.totient n = ∏ p ∈ n.primeFactors, (p - 1) := by
  have h0 : n ≠ 0 := squarefree_ne_zero hn
  rw [Nat.totient_eq_prod_factorization h0, Finsupp.prod]
  refine Finset.prod_congr rfl ?_
  intro p hp
  have heq := factorization_eq_one_of_squarefree hn hp
  simp [heq]

lemma phi2_one : phi2 1 = 1 := by
  simp [phi2]

lemma phi2_prime {p : ℕ} (hp : p.Prime) : phi2 p = p - 2 := by
  simp [phi2, hp.primeFactors]

lemma phi2_mul_of_coprime {a b : ℕ} (hc : Nat.Coprime a b) :
    phi2 (a * b) = phi2 a * phi2 b := by
  unfold phi2
  rw [Nat.Coprime.primeFactors_mul hc]
  exact Finset.prod_union (Nat.Coprime.disjoint_primeFactors hc)

lemma phi2_pos_of_odd {n : ℕ} (h2 : ¬ 2 ∣ n) : 0 < phi2 n := by
  unfold phi2
  refine Finset.prod_pos ?_
  intro p hp
  have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpne2 : p ≠ 2 := by
    rintro rfl
    exact h2 (Nat.dvd_of_mem_primeFactors hp)
  have hp2 := hprime.two_le
  omega

lemma phi2_le_totient_of_squarefree {n : ℕ} (hn : Squarefree n) :
    phi2 n ≤ Nat.totient n := by
  rw [totient_eq_prod_primeFactors_of_squarefree hn, phi2]
  refine Finset.prod_le_prod (fun _ _ => Nat.zero_le _) ?_
  intro p _
  omega

lemma primeFactors_prod_subset_primes {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) :
    (∏ p ∈ s, p).primeFactors = s := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert p s hp ih =>
    rw [Finset.prod_insert hp]
    have hp_prime : p.Prime := hs p (Finset.mem_insert_self p s)
    have hs_prime : ∀ q ∈ s, q.Prime := fun q hq => hs q (Finset.mem_insert_of_mem hq)
    have hcop : Nat.Coprime p (∏ q ∈ s, q) := by
      refine Nat.Coprime.prod_right ?_
      intro q hq
      have hq_prime : q.Prime := hs_prime q hq
      have hne : p ≠ q := fun h => hp (h ▸ hq)
      exact (Nat.coprime_primes hp_prime hq_prime).mpr hne
    rw [hcop.primeFactors_mul, hp_prime.primeFactors, ih hs_prime, Finset.singleton_union]

lemma sum_phi2_divisors_eq_totient {n : ℕ} (hn : Squarefree n) :
    ∑ d ∈ n.divisors, phi2 d = Nat.totient n := by
  have h0 : n ≠ 0 := squarefree_ne_zero hn
  have hprod : ∏ p ∈ n.primeFactors, (1 + (p - 2)) = Nat.totient n := by
    rw [totient_eq_prod_primeFactors_of_squarefree hn]
    refine Finset.prod_congr rfl ?_
    intro p hp
    have := (Nat.prime_of_mem_primeFactors hp).two_le
    omega
  rw [← hprod, Finset.prod_one_add]
  symm
  refine Finset.sum_bij (fun s _ => ∏ p ∈ s, p) ?_ ?_ ?_ ?_
  · intro s hs
    rw [Finset.mem_powerset] at hs
    rw [Nat.mem_divisors]
    refine ⟨?_, h0⟩
    rw [← squarefree_eq_prod_primeFactors hn]
    exact Finset.prod_dvd_prod_of_subset _ _ _ hs
  · intro s₁ hs₁ s₂ hs₂ hEq
    rw [Finset.mem_powerset] at hs₁ hs₂
    have h1 := primeFactors_prod_subset_primes (fun p hp => Nat.prime_of_mem_primeFactors (hs₁ hp))
    have h2 := primeFactors_prod_subset_primes (fun p hp => Nat.prime_of_mem_primeFactors (hs₂ hp))
    rw [← h1, ← h2, hEq]
  · intro d hd
    rw [Nat.mem_divisors] at hd
    refine ⟨d.primeFactors, ?_, ?_⟩
    · rw [Finset.mem_powerset]
      exact Nat.primeFactors_mono hd.1 h0
    · exact squarefree_eq_prod_primeFactors (hn.squarefree_of_dvd hd.1)
  · intro s hs
    rw [Finset.mem_powerset] at hs
    have h1 := primeFactors_prod_subset_primes (fun p hp => Nat.prime_of_mem_primeFactors (hs hp))
    simp [phi2, h1]

lemma totient_lcm_mul_totient_gcd (a b : ℕ) :
    Nat.totient (Nat.lcm a b) * Nat.totient (Nat.gcd a b) = Nat.totient a * Nat.totient b := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  rcases eq_or_ne b 0 with rfl | hb
  · simp
  have hg : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_left b (Nat.pos_of_ne_zero ha)
  have hprod : Nat.lcm a b * Nat.gcd a b = a * b := Nat.lcm_mul_gcd a b
  have hmul : ∀ m n : ℕ,
      (Nat.totient m : ℚ) * (Nat.totient n : ℚ) =
        (m : ℚ) * (n : ℚ) * (∏ p ∈ m.primeFactors, (1 - (p : ℚ)⁻¹)) *
          (∏ p ∈ n.primeFactors, (1 - (p : ℚ)⁻¹)) := by
    intro m n
    rw [Nat.totient_eq_mul_prod_factors, Nat.totient_eq_mul_prod_factors]
    ring
  have hlcm_ne : Nat.lcm a b ≠ 0 := Nat.lcm_ne_zero ha hb
  have hgcd_ne : Nat.gcd a b ≠ 0 := hg.ne'
  have hlcm_pf : (Nat.lcm a b).primeFactors = a.primeFactors ∪ b.primeFactors := by
    ext p
    simp only [Nat.mem_primeFactors, Finset.mem_union, hlcm_ne, ha, hb, ne_eq, not_false_eq_true,
      and_true]
    constructor
    · rintro ⟨hp, hdvd⟩
      have hmul_dvd : p ∣ a * b := dvd_trans hdvd (by rw [← hprod]; exact dvd_mul_right _ _)
      rcases hp.dvd_mul.mp hmul_dvd with h | h
      · exact Or.inl ⟨hp, h⟩
      · exact Or.inr ⟨hp, h⟩
    · rintro (⟨hp, h⟩ | ⟨hp, h⟩)
      · exact ⟨hp, dvd_trans h (Nat.dvd_lcm_left a b)⟩
      · exact ⟨hp, dvd_trans h (Nat.dvd_lcm_right a b)⟩
  have hgcd_pf : (Nat.gcd a b).primeFactors = a.primeFactors ∩ b.primeFactors := by
    ext p
    simp only [Nat.mem_primeFactors, Finset.mem_inter, hgcd_ne, ha, hb, ne_eq, not_false_eq_true,
      and_true]
    constructor
    · rintro ⟨hp, hdvd⟩
      exact ⟨⟨hp, dvd_trans hdvd (Nat.gcd_dvd_left a b)⟩,
        ⟨hp, dvd_trans hdvd (Nat.gcd_dvd_right a b)⟩⟩
    · rintro ⟨⟨hp, h1⟩, ⟨_, h2⟩⟩
      exact ⟨hp, Nat.dvd_gcd h1 h2⟩
  have hq : ((Nat.totient (Nat.lcm a b) * Nat.totient (Nat.gcd a b) : ℕ) : ℚ) =
      ((Nat.totient a * Nat.totient b : ℕ) : ℚ) := by
    push_cast
    rw [hmul, hmul, hlcm_pf, hgcd_pf]
    have hmul_eq : (Nat.lcm a b : ℚ) * (Nat.gcd a b : ℚ) = (a : ℚ) * (b : ℚ) := by
      exact_mod_cast hprod
    rw [hmul_eq, mul_assoc, mul_assoc, Finset.prod_union_inter]
    ring
  exact_mod_cast hq

lemma totient_real_eq_mul_prod_factors (q : ℕ) :
    (Nat.totient q : ℝ) = (q : ℝ) * ∏ p ∈ q.primeFactors, (1 - (p : ℝ)⁻¹) := by
  have h := congrArg (fun x : ℚ => (x : ℝ)) (Nat.totient_eq_mul_prod_factors q)
  simpa [Rat.cast_prod] using h

lemma div_totient_le_card_primeFactors_add_one {q : ℕ} (hq : 0 < q) :
    (q : ℝ) / (Nat.totient q : ℝ) ≤ (q.primeFactors.card : ℝ) + 1 := by
  have h0 : q ≠ 0 := hq.ne'
  have hq_real := totient_real_eq_mul_prod_factors q
  have hinv : (q : ℝ) / (Nat.totient q : ℝ) = ∏ p ∈ q.primeFactors, ((p : ℝ) / ((p : ℝ) - 1)) := by
    rw [hq_real]
    have hq_ne : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr h0
    rw [div_mul_eq_div_div, div_self hq_ne, one_div, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl ?_
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have hp_ne : (p : ℝ) ≠ 0 := by linarith
    have hp1_ne : (p : ℝ) - 1 ≠ 0 := by linarith
    field_simp
  rw [hinv]
  set m := q.primeFactors.card
  let e : Fin m ↪o ℕ := q.primeFactors.orderEmbOfFin rfl
  have hprod_eq : ∏ p ∈ q.primeFactors, ((p : ℝ) / ((p : ℝ) - 1)) =
      ∏ i : Fin m, ((e i : ℝ) / ((e i : ℝ) - 1)) := by
    rw [← Finset.prod_coe_sort q.primeFactors]
    refine Fintype.prod_equiv (q.primeFactors.orderIsoOfFin rfl).symm _ _ ?_
    intro x
    have hx : e ((q.primeFactors.orderIsoOfFin rfl).symm x) = x.1 := by
      change ((q.primeFactors.orderIsoOfFin rfl) ((q.primeFactors.orderIsoOfFin rfl).symm x)).1 = x.1
      simp
    simp only [EquivLike.coe_coe] at hx ⊢
    rw [hx]
  rw [hprod_eq]
  have he_ge : ∀ i : Fin m, i.1 + 2 ≤ e i := by
    intro ⟨i, hi⟩
    induction i with
    | zero =>
      have hmem : e ⟨0, hi⟩ ∈ q.primeFactors := Finset.orderEmbOfFin_mem _ rfl ⟨0, hi⟩
      exact (Nat.prime_of_mem_primeFactors hmem).two_le
    | succ j ih =>
      have hj : j < m := Nat.lt_of_succ_lt hi
      have hlt : e ⟨j, hj⟩ < e ⟨j + 1, hi⟩ := e.strictMono (by simp)
      have hprev : j + 2 ≤ e ⟨j, hj⟩ := ih hj
      change j + 1 + 2 ≤ e ⟨j + 1, hi⟩
      omega
  have hle_prod : ∏ i : Fin m, ((e i : ℝ) / ((e i : ℝ) - 1)) ≤
      ∏ i : Fin m, (((i.1 + 2 : ℕ) : ℝ) / ((i.1 + 1 : ℕ) : ℝ)) := by
    refine Finset.prod_le_prod ?_ ?_
    · intro i _
      have h2 : (2 : ℝ) ≤ e i := by exact_mod_cast le_trans (by omega) (he_ge i)
      exact div_nonneg (by linarith) (by linarith)
    · intro i _
      have hge : ((i.1 + 2 : ℕ) : ℝ) ≤ e i := by exact_mod_cast he_ge i
      have h1 : (0 : ℝ) < (i.1 + 1 : ℕ) := by positivity
      have h2 : (0 : ℝ) < (e i : ℝ) - 1 := by
        have : (2 : ℝ) ≤ (i.1 + 2 : ℕ) := by push_cast; linarith
        linarith
      rw [div_le_div_iff₀ h2 h1]
      push_cast at hge ⊢
      nlinarith
  have htel : ∀ n : ℕ, ∏ i : Fin n, (((i.1 + 2 : ℕ) : ℝ) / ((i.1 + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
      rw [Fin.prod_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [ih]
      have hne : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      push_cast at hne ⊢
      field_simp
      ring
  exact le_trans hle_prod (le_of_eq (htel m))

lemma card_primeFactors_le_two_mul_log {q : ℕ} (hq : 1 ≤ q) :
    (q.primeFactors.card : ℝ) ≤ 2 * Real.log q := by
  have hpow : 2 ^ q.primeFactors.card ≤ q := by
    calc 2 ^ q.primeFactors.card
        = ∏ _p ∈ q.primeFactors, 2 := by simp
      _ ≤ ∏ p ∈ q.primeFactors, p := by
          refine Finset.prod_le_prod (fun _ _ => by norm_num) ?_
          intro p hp
          exact (Nat.prime_of_mem_primeFactors hp).two_le
      _ = rad q := rfl
      _ ≤ q := Nat.le_of_dvd hq (rad_dvd_self q)
  have hpow_r : (2 : ℝ) ^ q.primeFactors.card ≤ (q : ℝ) := by exact_mod_cast hpow
  have hlog := Real.log_le_log (by positivity) hpow_r
  rw [Real.log_pow] at hlog
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hc_nonneg : (0 : ℝ) ≤ q.primeFactors.card := Nat.cast_nonneg _
  nlinarith

lemma div_totient_le_two_mul_log_add_one {q : ℕ} (hq : 1 ≤ q) :
    (q : ℝ) / (Nat.totient q : ℝ) ≤ 2 * Real.log q + 1 :=
  le_trans (div_totient_le_card_primeFactors_add_one hq)
    (by linarith [card_primeFactors_le_two_mul_log hq])

lemma harmonic_sub_log_abs_le_one {Y : ℝ} (hY : 1 ≤ Y) :
    |(∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, (1 / (n : ℝ))) - Real.log Y| ≤ 1 := by
  set N := ⌊Y⌋₊
  have hN1 : 1 ≤ N := (Nat.le_floor_iff (by linarith)).mpr (by exact_mod_cast hY)
  have hN_le : (N : ℝ) ≤ Y := Nat.floor_le (by linarith)
  have hY_lt : Y < (N : ℝ) + 1 := Nat.lt_floor_add_one Y
  have hlow : Real.log ((N : ℝ) + 1) ≤ ∑ n ∈ Finset.Icc 1 N, (1 / (n : ℝ)) := by
    have hstep : ∀ n : ℕ, 1 ≤ n →
        Real.log ((n : ℝ) + 1) - Real.log (n : ℝ) ≤ 1 / (n : ℝ) := by
      intro n hn
      have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
      rw [← Real.log_div (by linarith) hn_pos.ne']
      have h := Real.log_le_sub_one_of_pos (div_pos (by linarith : (0 : ℝ) < n + 1) hn_pos)
      have heq : ((n : ℝ) + 1) / (n : ℝ) - 1 = 1 / (n : ℝ) := by field_simp; ring
      linarith
    have htel : ∀ M : ℕ, ∑ n ∈ Finset.Icc 1 M, (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ)) =
        Real.log ((M : ℝ) + 1) := by
      intro M
      induction M with
      | zero => simp
      | succ k ih =>
        have hIcc : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
          ext x
          simp only [Finset.mem_Icc, Finset.mem_insert]
          omega
        rw [hIcc, Finset.sum_insert (by simp), ih]
        push_cast
        ring
    rw [← htel N]
    exact Finset.sum_le_sum (fun n hn => hstep n (Finset.mem_Icc.mp hn).1)
  have hhigh : ∑ n ∈ Finset.Icc 1 N, (1 / (n : ℝ)) ≤ 1 + Real.log (N : ℝ) := by
    have hstep : ∀ n : ℕ, 2 ≤ n →
        1 / (n : ℝ) ≤ Real.log (n : ℝ) - Real.log ((n : ℝ) - 1) := by
      intro n hn
      have hn_pos : (0 : ℝ) < n := by positivity
      have hn1_pos : (0 : ℝ) < (n : ℝ) - 1 := by
        have : (2 : ℝ) ≤ n := by exact_mod_cast hn
        linarith
      have h := Real.log_le_sub_one_of_pos (div_pos hn1_pos hn_pos)
      rw [Real.log_div hn1_pos.ne' hn_pos.ne'] at h
      have heq : ((n : ℝ) - 1) / (n : ℝ) - 1 = -(1 / (n : ℝ)) := by field_simp; ring
      linarith
    have htel : ∀ M : ℕ, 1 ≤ M →
        ∑ n ∈ Finset.Icc 2 M, (Real.log (n : ℝ) - Real.log ((n : ℝ) - 1)) = Real.log (M : ℝ) := by
      intro M hM
      induction M with
      | zero => omega
      | succ k ih =>
        rcases eq_or_ne k 0 with rfl | hk
        · simp
        · have hk1 : 1 ≤ k := Nat.pos_of_ne_zero hk
          have hIcc : Finset.Icc 2 (k + 1) = insert (k + 1) (Finset.Icc 2 k) := by
            ext x
            simp only [Finset.mem_Icc, Finset.mem_insert]
            omega
          rw [hIcc, Finset.sum_insert (by simp), ih hk1]
          push_cast
          ring
    have hsplit : Finset.Icc 1 N = insert 1 (Finset.Icc 2 N) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hsplit, Finset.sum_insert (by simp), ← htel N hN1]
    simp only [Nat.cast_one, div_one, add_le_add_iff_left]
    exact Finset.sum_le_sum (fun n hn => hstep n (Finset.mem_Icc.mp hn).1)
  have hlog_le1 : Real.log Y ≤ Real.log ((N : ℝ) + 1) :=
    Real.log_le_log (by linarith) (le_of_lt hY_lt)
  have hlog_le2 : Real.log (N : ℝ) ≤ Real.log Y :=
    Real.log_le_log (Nat.cast_pos.mpr hN1) hN_le
  rw [abs_le]
  constructor <;> linarith

lemma harmonic_le_log_add_one {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Icc 1 N, (1 / (n : ℝ)) ≤ Real.log (N : ℝ) + 1 := by
  have h := harmonic_sub_log_abs_le_one (Y := (N : ℝ)) (by exact_mod_cast hN)
  rw [Nat.floor_natCast] at h
  linarith [(abs_le.mp h).2]

lemma sum_rpow_neg_three_halves_le_three (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, ((n : ℝ) ^ (-(3 / 2 : ℝ))) ≤ 3 := by
  rcases eq_or_ne N 0 with rfl | hN
  · simp
  have hN1 : 1 ≤ N := Nat.pos_of_ne_zero hN
  have hsplit : Finset.Icc 1 N = insert 1 (Finset.Icc 2 N) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [hsplit, Finset.sum_insert (by simp)]
  have h1 : ((1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) = 1 := by simp
  rw [h1]
  have hstep : ∀ n : ℕ, 2 ≤ n →
      (n : ℝ) ^ (-(3 / 2 : ℝ)) ≤ 2 * (1 / Real.sqrt ((n : ℝ) - 1) - 1 / Real.sqrt (n : ℝ)) := by
    intro n hn
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hn_pos : (0 : ℝ) < n := by linarith
    have hn1_pos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
    have hs_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn_pos
    have hs1_pos : 0 < Real.sqrt ((n : ℝ) - 1) := Real.sqrt_pos.mpr hn1_pos
    have hle_s : Real.sqrt ((n : ℝ) - 1) ≤ Real.sqrt (n : ℝ) :=
      Real.sqrt_le_sqrt (by linarith)
    have hpow : (n : ℝ) ^ (-(3 / 2 : ℝ)) = 1 / ((n : ℝ) * Real.sqrt (n : ℝ)) := by
      rw [Real.rpow_neg hn_pos.le, one_div]
      congr 1
      have h32 : (3 / 2 : ℝ) = 1 + 1 / 2 := by norm_num
      rw [h32, Real.rpow_add hn_pos, Real.rpow_one, Real.sqrt_eq_rpow]
    rw [hpow]
    have hdiff : Real.sqrt (n : ℝ) - Real.sqrt ((n : ℝ) - 1) =
        1 / (Real.sqrt (n : ℝ) + Real.sqrt ((n : ℝ) - 1)) := by
      have hsum_pos : 0 < Real.sqrt (n : ℝ) + Real.sqrt ((n : ℝ) - 1) := by linarith
      rw [eq_div_iff hsum_pos.ne']
      have hsq1 : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) := Real.mul_self_sqrt hn_pos.le
      have hsq2 : Real.sqrt ((n : ℝ) - 1) * Real.sqrt ((n : ℝ) - 1) = (n : ℝ) - 1 :=
        Real.mul_self_sqrt hn1_pos.le
      nlinarith
    have hrhs : 2 * (1 / Real.sqrt ((n : ℝ) - 1) - 1 / Real.sqrt (n : ℝ)) =
        2 / (Real.sqrt ((n : ℝ) - 1) * Real.sqrt (n : ℝ) *
          (Real.sqrt (n : ℝ) + Real.sqrt ((n : ℝ) - 1))) := by
      rw [one_div, one_div, inv_sub_inv hs1_pos.ne' hs_pos.ne', hdiff]
      field_simp
    rw [hrhs]
    have hden1 : 0 < (n : ℝ) * Real.sqrt (n : ℝ) := by positivity
    have hden2 : 0 < Real.sqrt ((n : ℝ) - 1) * Real.sqrt (n : ℝ) *
        (Real.sqrt (n : ℝ) + Real.sqrt ((n : ℝ) - 1)) := by positivity
    rw [div_le_div_iff₀ hden1 hden2]
    have hsq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) := Real.mul_self_sqrt hn_pos.le
    have hle1 : Real.sqrt ((n : ℝ) - 1) * Real.sqrt (n : ℝ) ≤ (n : ℝ) := by
      calc Real.sqrt ((n : ℝ) - 1) * Real.sqrt (n : ℝ)
          ≤ Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) := by nlinarith
        _ = (n : ℝ) := hsq
    have hle2 : Real.sqrt (n : ℝ) + Real.sqrt ((n : ℝ) - 1) ≤ 2 * Real.sqrt (n : ℝ) := by linarith
    have hprod_le : Real.sqrt ((n : ℝ) - 1) * Real.sqrt (n : ℝ) *
        (Real.sqrt (n : ℝ) + Real.sqrt ((n : ℝ) - 1)) ≤ (n : ℝ) * (2 * Real.sqrt (n : ℝ)) :=
      mul_le_mul hle1 hle2 (by positivity) hn_pos.le
    linarith
  have htel : ∀ M : ℕ, 1 ≤ M →
      ∑ n ∈ Finset.Icc 2 M, 2 * (1 / Real.sqrt ((n : ℝ) - 1) - 1 / Real.sqrt (n : ℝ)) =
      2 * (1 - 1 / Real.sqrt (M : ℝ)) := by
    intro M hM
    induction M with
    | zero => omega
    | succ k ih =>
      rcases eq_or_ne k 0 with rfl | hk
      · simp
      · have hk1 : 1 ≤ k := Nat.pos_of_ne_zero hk
        have hIcc : Finset.Icc 2 (k + 1) = insert (k + 1) (Finset.Icc 2 k) := by
          ext x
          simp only [Finset.mem_Icc, Finset.mem_insert]
          omega
        rw [hIcc, Finset.sum_insert (by simp), ih hk1]
        push_cast
        ring
  have hsum_le : ∑ n ∈ Finset.Icc 2 N, ((n : ℝ) ^ (-(3 / 2 : ℝ))) ≤
      2 * (1 - 1 / Real.sqrt (N : ℝ)) := by
    rw [← htel N hN1]
    exact Finset.sum_le_sum (fun n hn => hstep n (Finset.mem_Icc.mp hn).1)
  have hsqrt_nonneg : (0 : ℝ) ≤ 1 / Real.sqrt (N : ℝ) := by positivity
  linarith

lemma sum_moebius_divisors_eq_ite (n : ℕ) :
    ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) = if n = 1 then 1 else 0 := by
  have h : (∑ d ∈ n.divisors, ArithmeticFunction.moebius d : ℤ) = if n = 1 then 1 else 0 := by
    have h1 := congrFun (congrArg DFunLike.coe ArithmeticFunction.moebius_mul_coe_zeta) n
    simp only [ArithmeticFunction.mul_apply, ArithmeticFunction.one_apply] at h1
    rw [← h1]
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [Nat.sum_divisorsAntidiagonal (fun a b => ArithmeticFunction.moebius a * (ArithmeticFunction.zeta : ArithmeticFunction ℤ) b)]
      refine Finset.sum_congr rfl ?_
      intro d hd
      have hpos : 0 < n / d := Nat.div_pos
        (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.dvd_of_mem_divisors hd))
        (Nat.pos_of_mem_divisors hd)
      simp [ArithmeticFunction.zeta_apply, hpos.ne']
  exact_mod_cast h

lemma sum_moebius_div_eq_totient_div {W : ℕ} (hW : 0 < W) :
    ∑ d ∈ W.divisors, ((ArithmeticFunction.moebius d : ℝ) / (d : ℝ)) =
      (Nat.totient W : ℝ) / (W : ℝ) := by
  have hW_ne : (W : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hW.ne'
  rw [eq_div_iff hW_ne, Finset.sum_mul]
  have hreal : ∑ d ∈ W.divisors, (ArithmeticFunction.moebius d : ℝ) * ((W / d : ℕ) : ℝ) =
      (Nat.totient W : ℝ) := by
    have hstep1 :
        ∑ d ∈ W.divisors, (ArithmeticFunction.moebius d : ℝ) * ((W / d : ℕ) : ℝ) =
        ∑ d ∈ W.divisors, ∑ k ∈ (W / d).divisors,
          (ArithmeticFunction.moebius d : ℝ) * (Nat.totient k : ℝ) := by
      refine Finset.sum_congr rfl ?_
      intro d _
      rw [← Finset.mul_sum]
      congr 1
      exact_mod_cast (Nat.sum_totient (W / d)).symm
    have hstep2 :
        ∑ d ∈ W.divisors, ∑ k ∈ (W / d).divisors,
          (ArithmeticFunction.moebius d : ℝ) * (Nat.totient k : ℝ) =
        ∑ d ∈ W.divisors, ∑ k ∈ W.divisors,
          (if d * k ∣ W then (ArithmeticFunction.moebius d : ℝ) * (Nat.totient k : ℝ) else 0) := by
      refine Finset.sum_congr rfl ?_
      intro d hd
      rw [← Finset.sum_filter]
      refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext k
      have hd_dvd : d ∣ W := Nat.dvd_of_mem_divisors hd
      have hd_pos : 0 < d := Nat.pos_of_mem_divisors hd
      have hWd_pos : 0 < W / d := Nat.div_pos (Nat.le_of_dvd hW hd_dvd) hd_pos
      simp only [Nat.mem_divisors, Finset.mem_filter, hWd_pos.ne', hW.ne', ne_eq,
        not_false_eq_true, and_true]
      constructor
      · intro hk
        have hdk : d * k ∣ W := by
          rcases hk with ⟨c, hc⟩
          refine ⟨c, ?_⟩
          calc W = d * (W / d) := (Nat.mul_div_cancel' hd_dvd).symm
            _ = d * (k * c) := by rw [hc]
            _ = d * k * c := by ring
        exact ⟨dvd_trans (dvd_mul_left k d) hdk, hdk⟩
      · rintro ⟨_, hdk⟩
        rcases hdk with ⟨c, hc⟩
        refine ⟨c, ?_⟩
        have h1 : d * (W / d) = d * (k * c) := by
          rw [Nat.mul_div_cancel' hd_dvd, hc]; ring
        exact Nat.eq_of_mul_eq_mul_left hd_pos h1
    have hstep3 :
        ∑ d ∈ W.divisors, ∑ k ∈ W.divisors,
          (if d * k ∣ W then (ArithmeticFunction.moebius d : ℝ) * (Nat.totient k : ℝ) else 0) =
        ∑ k ∈ W.divisors, (Nat.totient k : ℝ) *
          (∑ d ∈ (W / k).divisors, (ArithmeticFunction.moebius d : ℝ)) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro k hk
      rw [Finset.mul_sum, ← Finset.sum_filter]
      have hk_dvd : k ∣ W := Nat.dvd_of_mem_divisors hk
      have hk_pos : 0 < k := Nat.pos_of_mem_divisors hk
      have hWk_pos : 0 < W / k := Nat.div_pos (Nat.le_of_dvd hW hk_dvd) hk_pos
      refine Finset.sum_congr ?_ (fun _ _ => mul_comm _ _)
      ext d
      simp only [Finset.mem_filter, Nat.mem_divisors, hW.ne', hWk_pos.ne', ne_eq,
        not_false_eq_true, and_true]
      constructor
      · rintro ⟨_, hdk⟩
        rcases hdk with ⟨c, hc⟩
        refine ⟨c, ?_⟩
        have h1 : k * (W / k) = k * (d * c) := by
          rw [Nat.mul_div_cancel' hk_dvd, hc]; ring
        exact Nat.eq_of_mul_eq_mul_left hk_pos h1
      · intro hd
        have hdk : d * k ∣ W := by
          rcases hd with ⟨c, hc⟩
          refine ⟨c, ?_⟩
          calc W = k * (W / k) := (Nat.mul_div_cancel' hk_dvd).symm
            _ = k * (d * c) := by rw [hc]
            _ = d * k * c := by ring
        exact ⟨dvd_trans (dvd_mul_right d k) hdk, hdk⟩
    rw [hstep1, hstep2, hstep3]
    rw [Finset.sum_eq_single W]
    · rw [Nat.div_self hW, sum_moebius_divisors_eq_ite]
      simp
    · intro k hk hne
      rw [sum_moebius_divisors_eq_ite]
      have hWk_ne : W / k ≠ 1 := by
        intro h1
        have hk_dvd : k ∣ W := Nat.dvd_of_mem_divisors hk
        have : W = k := by
          calc W = k * (W / k) := (Nat.mul_div_cancel' hk_dvd).symm
            _ = k * 1 := by rw [h1]
            _ = k := mul_one k
        exact hne this.symm
      simp [hWk_ne]
    · intro hnot
      exact absurd (Nat.mem_divisors.mpr ⟨dvd_refl W, hW.ne'⟩) hnot
  rw [← hreal]
  refine Finset.sum_congr rfl ?_
  intro d hd
  have hd_dvd : d ∣ W := Nat.dvd_of_mem_divisors hd
  have hd_ne : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_of_mem_divisors hd).ne'
  rw [div_mul_eq_mul_div, mul_div_assoc]
  congr 1
  rw [div_eq_iff hd_ne]
  exact_mod_cast (Nat.div_mul_cancel hd_dvd).symm

lemma harmonic_coprime_bound {W : ℕ} (hW : 0 < W) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Y : ℝ, 1 ≤ Y →
      |(∑ n ∈ (Finset.Icc 1 ⌊Y⌋₊).filter (fun n => Nat.Coprime n W), (1 / (n : ℝ))) -
        ((Nat.totient W : ℝ) / (W : ℝ)) * Real.log Y| ≤ C := by
  refine ⟨(W.divisors.card : ℝ) * (1 + Real.log W), by positivity, ?_⟩
  intro Y hY
  have hrewrite :
      ∑ n ∈ (Finset.Icc 1 ⌊Y⌋₊).filter (fun n => Nat.Coprime n W), (1 / (n : ℝ)) =
      ∑ d ∈ W.divisors, ((ArithmeticFunction.moebius d : ℝ) / (d : ℝ)) *
        (∑ m ∈ Finset.Icc 1 ⌊Y / (d : ℝ)⌋₊, (1 / (m : ℝ))) := by
    rw [Finset.sum_filter]
    have hstep1 :
        ∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, (if Nat.Coprime n W then (1 / (n : ℝ)) else 0) =
        ∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, ∑ d ∈ W.divisors,
          (if d ∣ n then (ArithmeticFunction.moebius d : ℝ) / (n : ℝ) else 0) := by
      refine Finset.sum_congr rfl ?_
      intro n hn
      have hn_pos : 0 < n := (Finset.mem_Icc.mp hn).1
      have hgcd_pos : 0 < Nat.gcd n W := Nat.gcd_pos_of_pos_left W hn_pos
      have hmob := sum_moebius_divisors_eq_ite (Nat.gcd n W)
      have hsub : (Nat.gcd n W).divisors = W.divisors.filter (fun d => d ∣ n) := by
        ext d
        simp only [Nat.mem_divisors, Finset.mem_filter, hgcd_pos.ne', hW.ne', ne_eq,
          not_false_eq_true, and_true]
        exact ⟨fun h => ⟨dvd_trans h (Nat.gcd_dvd_right n W), dvd_trans h (Nat.gcd_dvd_left n W)⟩,
          fun ⟨h1, h2⟩ => Nat.dvd_gcd h2 h1⟩
      rw [hsub, Finset.sum_filter] at hmob
      have hcop : Nat.Coprime n W ↔ Nat.gcd n W = 1 := Iff.rfl
      by_cases hc : Nat.Coprime n W
      · rw [if_pos hc]
        rw [if_pos (hcop.mp hc)] at hmob
        have hmul := congrArg (fun x => x * (1 / (n : ℝ))) hmob
        simp only [one_mul, Finset.sum_mul] at hmul
        rw [← hmul]
        refine Finset.sum_congr rfl ?_
        intro d _
        split_ifs <;> ring
      · rw [if_neg hc]
        rw [if_neg (fun h => hc (hcop.mpr h))] at hmob
        have hmul := congrArg (fun x => x * (1 / (n : ℝ))) hmob
        simp only [zero_mul, Finset.sum_mul] at hmul
        symm
        calc ∑ d ∈ W.divisors, (if d ∣ n then (ArithmeticFunction.moebius d : ℝ) / (n : ℝ) else 0)
            = ∑ d ∈ W.divisors, (if d ∣ n then (ArithmeticFunction.moebius d : ℝ) else 0) * (1 / (n : ℝ)) := by
              refine Finset.sum_congr rfl ?_
              intro d _
              split_ifs <;> ring
          _ = 0 := hmul
    rw [hstep1, Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro d hd
    have hd_pos : 0 < d := Nat.pos_of_mem_divisors hd
    rw [← Finset.sum_filter, Finset.mul_sum]
    symm
    refine Finset.sum_bij (fun m _ => d * m) ?_ ?_ ?_ ?_
    · intro m hm
      rw [Finset.mem_Icc] at hm
      rw [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨Nat.mul_pos hd_pos hm.1, ?_⟩, dvd_mul_right d m⟩
      have hle : (m : ℝ) ≤ Y / (d : ℝ) := le_trans (Nat.cast_le.mpr hm.2) (Nat.floor_le (by positivity))
      have hdm : ((d * m : ℕ) : ℝ) ≤ Y := by
        push_cast
        exact (le_div_iff₀ (Nat.cast_pos.mpr hd_pos)).mp hle |> fun h => by linarith
      exact (Nat.le_floor_iff (by linarith)).mpr hdm
    · intro m₁ _ m₂ _ hEq
      exact Nat.eq_of_mul_eq_mul_left hd_pos hEq
    · intro n hn
      rw [Finset.mem_filter, Finset.mem_Icc] at hn
      rcases hn.2 with ⟨m, rfl⟩
      refine ⟨m, Finset.mem_Icc.mpr ⟨?_, ?_⟩, rfl⟩
      · by_contra hm0
        push Not at hm0
        have : m = 0 := by omega
        subst this
        simp at hn
      · have hdm : ((d * m : ℕ) : ℝ) ≤ Y :=
          le_trans (Nat.cast_le.mpr hn.1.2) (Nat.floor_le (by linarith))
        have hm_le : (m : ℝ) ≤ Y / (d : ℝ) := by
          rw [le_div_iff₀ (Nat.cast_pos.mpr hd_pos)]
          push_cast at hdm
          linarith
        exact (Nat.le_floor_iff (by positivity)).mpr hm_le
    · intro m _
      push_cast
      ring
  rw [hrewrite, ← sum_moebius_div_eq_totient_div hW, Finset.sum_mul, ← Finset.sum_sub_distrib]
  calc |∑ d ∈ W.divisors,
          ((ArithmeticFunction.moebius d : ℝ) / (d : ℝ) *
            (∑ m ∈ Finset.Icc 1 ⌊Y / (d : ℝ)⌋₊, (1 / (m : ℝ))) -
          (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) * Real.log Y)|
      ≤ ∑ d ∈ W.divisors,
          |(ArithmeticFunction.moebius d : ℝ) / (d : ℝ) *
            ((∑ m ∈ Finset.Icc 1 ⌊Y / (d : ℝ)⌋₊, (1 / (m : ℝ))) - Real.log Y)| := by
        have h1 := Finset.abs_sum_le_sum_abs (fun d =>
          (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) *
            (∑ m ∈ Finset.Icc 1 ⌊Y / (d : ℝ)⌋₊, (1 / (m : ℝ))) -
          (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) * Real.log Y) W.divisors
        refine le_trans h1 (le_of_eq (Finset.sum_congr rfl (fun d _ => by ring_nf)))
    _ ≤ ∑ _d ∈ W.divisors, (1 + Real.log W) := by
        refine Finset.sum_le_sum ?_
        intro d hd
        have hd_pos : 0 < d := Nat.pos_of_mem_divisors hd
        have hd_le_W : d ≤ W := Nat.le_of_dvd hW (Nat.dvd_of_mem_divisors hd)
        have hmob_le : |(ArithmeticFunction.moebius d : ℝ) / (d : ℝ)| ≤ 1 := by
          have hd_abs : |(d : ℝ)| = (d : ℝ) := abs_of_pos (Nat.cast_pos.mpr hd_pos)
          rw [abs_div, hd_abs]
          have hm1 : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
            by_cases hsq : Squarefree d
            · rw [ArithmeticFunction.moebius_apply_of_squarefree hsq]
              simp
            · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
              simp
          have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd_pos
          exact (div_le_one (Nat.cast_pos.mpr hd_pos)).mpr (le_trans hm1 hd1)
        have hdiff : |(∑ m ∈ Finset.Icc 1 ⌊Y / (d : ℝ)⌋₊, (1 / (m : ℝ))) - Real.log Y| ≤
            1 + Real.log W := by
          by_cases hYd : 1 ≤ Y / (d : ℝ)
          · have hh := harmonic_sub_log_abs_le_one hYd
            rw [Real.log_div (by linarith) (Nat.cast_pos.mpr hd_pos).ne'] at hh
            have hlog_d : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg (by exact_mod_cast hd_pos)
            have hlog_dW : Real.log (d : ℝ) ≤ Real.log (W : ℝ) :=
              Real.log_le_log (Nat.cast_pos.mpr hd_pos) (by exact_mod_cast hd_le_W)
            rw [abs_le] at hh ⊢
            constructor <;> linarith
          · push Not at hYd
            have hfl : ⌊Y / (d : ℝ)⌋₊ = 0 := Nat.floor_eq_zero.mpr hYd
            rw [hfl]
            simp only [Finset.Icc_eq_empty_of_lt (by omega : 0 < 1), Finset.sum_empty, zero_sub,
              abs_neg]
            have hY_le_d : Y ≤ (d : ℝ) := (div_lt_one (Nat.cast_pos.mpr hd_pos)).mp hYd |>.le
            have hlog_Y : 0 ≤ Real.log Y := Real.log_nonneg hY
            rw [abs_of_nonneg hlog_Y]
            have hlog_YW : Real.log Y ≤ Real.log (W : ℝ) :=
              Real.log_le_log (by linarith) (le_trans hY_le_d (by exact_mod_cast hd_le_W))
            linarith
        rw [abs_mul]
        calc |(ArithmeticFunction.moebius d : ℝ) / (d : ℝ)| *
              |(∑ m ∈ Finset.Icc 1 ⌊Y / (d : ℝ)⌋₊, (1 / (m : ℝ))) - Real.log Y|
            ≤ 1 * (1 + Real.log W) :=
              mul_le_mul hmob_le hdiff (abs_nonneg _) (by norm_num)
          _ = 1 + Real.log W := one_mul _
    _ = (W.divisors.card : ℝ) * (1 + Real.log W) := by simp; ring

lemma geom_sum_inv_prime {p N : ℕ} (hp : 2 ≤ p) :
    ∑ e ∈ Finset.Icc 1 N, (1 / (p : ℝ) ^ e) =
      (1 - (1 / (p : ℝ)) ^ N) / ((p : ℝ) - 1) := by
  have hp_r : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp_pos : (0 : ℝ) < p := by linarith
  have hp1_ne : (p : ℝ) - 1 ≠ 0 := by linarith
  induction N with
  | zero => simp
  | succ k ih =>
    have hIcc : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hIcc, Finset.sum_insert (by simp), ih]
    rw [one_div_pow, one_div_pow, pow_succ]
    field_simp
    ring

lemma primePowVal_factorization {r : ℕ} {f : ∀ p ∈ r.primeFactors, ℕ} (q : ℕ) :
    (∏ p ∈ r.primeFactors.attach, p.1 ^ (f p.1 p.2)).factorization q =
      if hq : q ∈ r.primeFactors then f q hq else 0 := by
  rw [Nat.factorization_prod (fun p _ => pow_ne_zero _ (Nat.prime_of_mem_primeFactors p.2).ne_zero)]
  simp only [Finsupp.finsetSum_apply]
  by_cases hq : q ∈ r.primeFactors
  · rw [dif_pos hq]
    have hmem : (⟨q, hq⟩ : {p // p ∈ r.primeFactors}) ∈ r.primeFactors.attach := Finset.mem_attach _ _
    rw [Finset.sum_eq_single ⟨q, hq⟩]
    · rw [Nat.Prime.factorization_pow (Nat.prime_of_mem_primeFactors hq)]
      simp
    · intro p _ hpne
      rw [Nat.Prime.factorization_pow (Nat.prime_of_mem_primeFactors p.2)]
      have hne : p.1 ≠ q := fun h => hpne (Subtype.ext h)
      simp [hne]
    · intro hnot
      exact absurd hmem hnot
  · rw [dif_neg hq]
    refine Finset.sum_eq_zero ?_
    intro p _
    rw [Nat.Prime.factorization_pow (Nat.prime_of_mem_primeFactors p.2)]
    have hne : p.1 ≠ q := fun h => hq (h ▸ p.2)
    simp [hne]

lemma geom_prod_eq_sum_rad {r N : ℕ} (hr : Squarefree r) :
    ∃ T : Finset ℕ,
      (∀ n ∈ T, 0 < n ∧ rad n = r) ∧
      ((Finset.Icc 1 N).filter (fun n => rad n = r) ⊆ T) ∧
      ∏ p ∈ r.primeFactors, (∑ e ∈ Finset.Icc 1 N, (1 / (p : ℝ) ^ e)) =
        ∑ n ∈ T, (1 / (n : ℝ)) := by
  classical
  let S_exp := r.primeFactors.pi (fun _ => Finset.Icc 1 N)
  let val : (∀ p ∈ r.primeFactors, ℕ) → ℕ :=
    fun f => ∏ p ∈ r.primeFactors.attach, p.1 ^ (f p.1 p.2)
  have hval_pos : ∀ f ∈ S_exp, 0 < val f := by
    intro f _
    refine Finset.prod_pos ?_
    intro p _
    exact pow_pos (Nat.prime_of_mem_primeFactors p.2).pos _
  have hval_fac : ∀ f ∈ S_exp, ∀ q,
      (val f).factorization q = if hq : q ∈ r.primeFactors then f q hq else 0 := by
    intro f _ q
    exact primePowVal_factorization q
  have hval_rad : ∀ f ∈ S_exp, rad (val f) = r := by
    intro f hf
    have hpf : (val f).primeFactors = r.primeFactors := by
      ext q
      rw [← Nat.support_factorization, Finsupp.mem_support_iff, hval_fac f hf q]
      by_cases hq : q ∈ r.primeFactors
      · rw [dif_pos hq]
        have h1 : 1 ≤ f q hq := (Finset.mem_Icc.mp (Finset.mem_pi.mp hf q hq)).1
        exact ⟨fun _ => hq, fun _ => by omega⟩
      · simp [hq]
    unfold rad
    rw [hpf, squarefree_eq_prod_primeFactors hr]
  have hval_inj : Set.InjOn val (S_exp : Set (∀ p ∈ r.primeFactors, ℕ)) := by
    intro f₁ hf₁ f₂ hf₂ hEq
    funext p hp
    have h1 := hval_fac f₁ hf₁ p
    have h2 := hval_fac f₂ hf₂ p
    rw [dif_pos hp] at h1 h2
    rw [← h1, ← h2, hEq]
  refine ⟨S_exp.image val, ?_, ?_, ?_⟩
  · intro n hn
    rcases Finset.mem_image.mp hn with ⟨f, hf, rfl⟩
    exact ⟨hval_pos f hf, hval_rad f hf⟩
  · intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    rcases hn with ⟨⟨hn1, hnN⟩, hrad⟩
    have hn_pf : n.primeFactors = r.primeFactors := by
      rw [← rad_primeFactors n, hrad]
    let f : ∀ p ∈ r.primeFactors, ℕ := fun p _ => n.factorization p
    refine Finset.mem_image.mpr ⟨f, ?_, ?_⟩
    · rw [Finset.mem_pi]
      intro p hp
      rw [Finset.mem_Icc]
      have hp_n : p ∈ n.primeFactors := hn_pf.symm ▸ hp
      have hpos : 1 ≤ n.factorization p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp_n)
      have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hle_pow : n.factorization p ≤ p ^ n.factorization p :=
        le_trans (Nat.lt_two_pow_self.le) (Nat.pow_le_pow_left hp_prime.two_le _)
      have hpow_le : p ^ n.factorization p ≤ n :=
        Nat.le_of_dvd (by omega) (Nat.ordProj_dvd n p)
      exact ⟨hpos, le_trans (le_trans hle_pow hpow_le) hnN⟩
    · dsimp only [val, f]
      rw [Finset.prod_attach (f := fun p => p ^ n.factorization p)]
      rw [← hn_pf]
      exact Nat.prod_factorization_pow_eq_self (by omega)
  · rw [Finset.prod_sum, Finset.sum_image hval_inj]
    refine Finset.sum_congr rfl ?_
    intro f _
    dsimp only [val]
    rw [Nat.cast_prod, one_div, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl ?_
    intro p _
    simp [one_div]

lemma sum_log_add_one_div_mul_rad_le (M : ℕ) :
    ∑ m ∈ Finset.Icc 1 M, ((Real.log (m : ℝ) + 1) / ((m : ℝ) * (rad m : ℝ))) ≤ 135 := by
  classical
  -- Decompose each m in Icc 1 M as a * u^2 * v^3 with a | rad m
  let aPart : ℕ → ℕ := fun m =>
    ∏ p ∈ m.primeFactors.filter (fun p => m.factorization p = 1), p
  let uPart : ℕ → ℕ := fun m =>
    ∏ p ∈ m.primeFactors.filter (fun p => 2 ≤ m.factorization p),
      p ^ (if Even (m.factorization p) then m.factorization p / 2 else (m.factorization p - 3) / 2)
  let vPart : ℕ → ℕ := fun m =>
    ∏ p ∈ m.primeFactors.filter (fun p => 2 ≤ m.factorization p ∧ Odd (m.factorization p)), p
  have hdecomp : ∀ m : ℕ, 1 ≤ m → m = aPart m * (uPart m) ^ 2 * (vPart m) ^ 3 := by
    intro m hm
    have hm0 : m ≠ 0 := by omega
    have hprod := (Nat.prod_factorization_pow_eq_self hm0).symm
    -- Show every prime p in m.primeFactors has matching exponent
    have hpart1 : m = (∏ p ∈ m.primeFactors.filter (fun p => m.factorization p = 1), p ^ m.factorization p) *
        (∏ p ∈ m.primeFactors.filter (fun p => 2 ≤ m.factorization p), p ^ m.factorization p) := by
      conv_lhs => rw [hprod]
      rw [← Finset.prod_union]
      · refine Finset.prod_congr ?_ (fun _ _ => rfl)
        ext p
        simp only [Finset.mem_union, Finset.mem_filter]
        constructor
        · intro hp
          have hpos : 1 ≤ m.factorization p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)
          by_cases h1 : m.factorization p = 1
          · exact Or.inl ⟨hp, h1⟩
          · exact Or.inr ⟨hp, by omega⟩
        · rintro (⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp
      · rw [Finset.disjoint_filter]
        intro p _ h1 h2
        omega
    have ha_eq : ∏ p ∈ m.primeFactors.filter (fun p => m.factorization p = 1), p ^ m.factorization p = aPart m := by
      refine Finset.prod_congr rfl ?_
      intro p hp
      rw [(Finset.mem_filter.mp hp).2, pow_one]
    have huv_eq :
        ∏ p ∈ m.primeFactors.filter (fun p => 2 ≤ m.factorization p), p ^ m.factorization p =
        (uPart m) ^ 2 * (vPart m) ^ 3 := by
      have hsplit : m.primeFactors.filter (fun p => 2 ≤ m.factorization p) =
          (m.primeFactors.filter (fun p => 2 ≤ m.factorization p ∧ Even (m.factorization p))) ∪
          (m.primeFactors.filter (fun p => 2 ≤ m.factorization p ∧ Odd (m.factorization p))) := by
        ext p
        simp only [Finset.mem_union, Finset.mem_filter]
        constructor
        · rintro ⟨hp, h2⟩
          rcases Nat.even_or_odd (m.factorization p) with he | ho
          · exact Or.inl ⟨hp, h2, he⟩
          · exact Or.inr ⟨hp, h2, ho⟩
        · rintro (⟨hp, h2, _⟩ | ⟨hp, h2, _⟩) <;> exact ⟨hp, h2⟩
      have hdisj : Disjoint
          (m.primeFactors.filter (fun p => 2 ≤ m.factorization p ∧ Even (m.factorization p)))
          (m.primeFactors.filter (fun p => 2 ≤ m.factorization p ∧ Odd (m.factorization p))) := by
        rw [Finset.disjoint_filter]
        intro p _ ⟨_, he⟩ ⟨_, ho⟩
        exact Nat.not_even_iff_odd.mpr ho he
      have hu_split : (uPart m) ^ 2 =
          (∏ p ∈ m.primeFactors.filter (fun p => 2 ≤ m.factorization p ∧ Even (m.factorization p)),
            p ^ m.factorization p) *
          (∏ p ∈ m.primeFactors.filter (fun p => 2 ≤ m.factorization p ∧ Odd (m.factorization p)),
            p ^ (m.factorization p - 3)) := by
        dsimp only [uPart]
        rw [← Finset.prod_pow, hsplit, Finset.prod_union hdisj]
        congr 1
        · refine Finset.prod_congr rfl ?_
          intro p hp
          have he : Even (m.factorization p) := (Finset.mem_filter.mp hp).2.2
          rw [if_pos he, ← pow_mul]
          congr 1
          rcases he with ⟨c, hc⟩
          omega
        · refine Finset.prod_congr rfl ?_
          intro p hp
          have h2 : 2 ≤ m.factorization p := (Finset.mem_filter.mp hp).2.1
          have ho : Odd (m.factorization p) := (Finset.mem_filter.mp hp).2.2
          rw [if_neg (Nat.not_even_iff_odd.mpr ho), ← pow_mul]
          congr 1
          rcases ho with ⟨c, hc⟩
          omega
      rw [hsplit, Finset.prod_union hdisj, hu_split, mul_assoc]
      congr 1
      dsimp only [vPart]
      rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl ?_
      intro p hp
      have h2 : 2 ≤ m.factorization p := (Finset.mem_filter.mp hp).2.1
      have ho : Odd (m.factorization p) := (Finset.mem_filter.mp hp).2.2
      rw [← pow_add]
      congr 1
      rcases ho with ⟨c, hc⟩
      omega
    calc m = (∏ p ∈ m.primeFactors.filter (fun p => m.factorization p = 1), p ^ m.factorization p) *
            (∏ p ∈ m.primeFactors.filter (fun p => 2 ≤ m.factorization p), p ^ m.factorization p) := hpart1
      _ = aPart m * ((uPart m) ^ 2 * (vPart m) ^ 3) := by rw [ha_eq, huv_eq]
      _ = aPart m * (uPart m) ^ 2 * (vPart m) ^ 3 := by ring
  have ha_le_rad : ∀ m : ℕ, 1 ≤ m → aPart m ≤ rad m := by
    intro m hm
    refine Nat.le_of_dvd rad_pos ?_
    exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)
  have ha_pos : ∀ m : ℕ, 1 ≤ aPart m := fun m =>
    Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos)
  have hu_pos : ∀ m : ℕ, 1 ≤ uPart m := fun m =>
    Finset.prod_pos (fun p hp => pow_pos (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos _)
  have hv_pos : ∀ m : ℕ, 1 ≤ vPart m := fun m =>
    Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos)
  -- Step 1: bound each term by 5 * (aPart m)^(-3/2) * (uPart m)^(-3/2) * (vPart m)^(-3/2)
  have hterm : ∀ m ∈ Finset.Icc 1 M,
      (Real.log (m : ℝ) + 1) / ((m : ℝ) * (rad m : ℝ)) ≤
      5 * (((aPart m : ℝ) ^ (-(3 / 2 : ℝ))) * ((uPart m : ℝ) ^ (-(3 / 2 : ℝ))) *
        ((vPart m : ℝ) ^ (-(3 / 2 : ℝ)))) := by
    intro m hm
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr hm1
    have hlog : Real.log (m : ℝ) + 1 ≤ 5 * (m : ℝ) ^ (1 / 4 : ℝ) := by
      have h1 := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hm_pos (1 / 4 : ℝ))
      rw [Real.log_rpow hm_pos] at h1
      have hrp_pos : (0 : ℝ) < (m : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hm_pos _
      linarith
    have hrad_ge : (aPart m : ℝ) ≤ (rad m : ℝ) := by exact_mod_cast ha_le_rad m hm1
    have ha1 : (1 : ℝ) ≤ aPart m := by exact_mod_cast ha_pos m
    have hu1 : (1 : ℝ) ≤ uPart m := by exact_mod_cast hu_pos m
    have hv1 : (1 : ℝ) ≤ vPart m := by exact_mod_cast hv_pos m
    have hden_ge : ((aPart m : ℝ) * (uPart m : ℝ) * (vPart m : ℝ)) ^ (3 / 2 : ℝ) ≤
        (m : ℝ) ^ (3 / 4 : ℝ) * (rad m : ℝ) := by
      have hm_eq : (m : ℝ) = (aPart m : ℝ) * (uPart m : ℝ) ^ 2 * (vPart m : ℝ) ^ 3 := by
        exact_mod_cast hdecomp m hm1
      rw [hm_eq]
      rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity)]
      rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity)]
      have ha_pow : (aPart m : ℝ) ^ (3 / 2 : ℝ) ≤ (aPart m : ℝ) ^ (3 / 4 : ℝ) * (rad m : ℝ) := by
        have h1 : (aPart m : ℝ) ^ (3 / 2 : ℝ) ≤ (aPart m : ℝ) ^ (7 / 4 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le ha1 (by norm_num)
        have h2 : (aPart m : ℝ) ^ (7 / 4 : ℝ) = (aPart m : ℝ) ^ (3 / 4 : ℝ) * (aPart m : ℝ) := by
          have h74 : (7 / 4 : ℝ) = 3 / 4 + 1 := by norm_num
          rw [h74, Real.rpow_add (by positivity), Real.rpow_one]
        rw [h2] at h1
        exact le_trans h1 (mul_le_mul_of_nonneg_left hrad_ge (by positivity))
      have hu_pow : (uPart m : ℝ) ^ (3 / 2 : ℝ) = ((uPart m : ℝ) ^ 2) ^ (3 / 4 : ℝ) := by
        rw [← Real.rpow_natCast (uPart m : ℝ) 2, ← Real.rpow_mul (by positivity)]
        norm_num
      have hv_pow : (vPart m : ℝ) ^ (3 / 2 : ℝ) ≤ ((vPart m : ℝ) ^ 3) ^ (3 / 4 : ℝ) := by
        rw [← Real.rpow_natCast (vPart m : ℝ) 3, ← Real.rpow_mul (by positivity)]
        exact Real.rpow_le_rpow_of_exponent_le hv1 (by norm_num)
      rw [hu_pow]
      calc (aPart m : ℝ) ^ (3 / 2 : ℝ) * ((uPart m : ℝ) ^ 2) ^ (3 / 4 : ℝ) * (vPart m : ℝ) ^ (3 / 2 : ℝ)
          ≤ ((aPart m : ℝ) ^ (3 / 4 : ℝ) * (rad m : ℝ)) * ((uPart m : ℝ) ^ 2) ^ (3 / 4 : ℝ) *
              ((vPart m : ℝ) ^ 3) ^ (3 / 4 : ℝ) := by
            have h12 := mul_le_mul_of_nonneg_right ha_pow (by positivity : (0 : ℝ) ≤ ((uPart m : ℝ) ^ 2) ^ (3 / 4 : ℝ))
            exact mul_le_mul h12 hv_pow (by positivity) (by positivity)
        _ = (aPart m : ℝ) ^ (3 / 4 : ℝ) * ((uPart m : ℝ) ^ 2) ^ (3 / 4 : ℝ) *
              ((vPart m : ℝ) ^ 3) ^ (3 / 4 : ℝ) * (rad m : ℝ) := by ring
    have hsplit_m : (m : ℝ) = (m : ℝ) ^ (1 / 4 : ℝ) * (m : ℝ) ^ (3 / 4 : ℝ) := by
      rw [← Real.rpow_add hm_pos]
      norm_num
    have hinv_eq :
        ((aPart m : ℝ) ^ (-(3 / 2 : ℝ))) * ((uPart m : ℝ) ^ (-(3 / 2 : ℝ))) *
          ((vPart m : ℝ) ^ (-(3 / 2 : ℝ))) =
        1 / ((aPart m : ℝ) * (uPart m : ℝ) * (vPart m : ℝ)) ^ (3 / 2 : ℝ) := by
      rw [Real.rpow_neg (by positivity), Real.rpow_neg (by positivity), Real.rpow_neg (by positivity),
        Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity)]
      field_simp
    rw [hinv_eq]
    calc (Real.log (m : ℝ) + 1) / ((m : ℝ) * (rad m : ℝ))
        ≤ (5 * (m : ℝ) ^ (1 / 4 : ℝ)) / ((m : ℝ) ^ (1 / 4 : ℝ) * (m : ℝ) ^ (3 / 4 : ℝ) * (rad m : ℝ)) := by
          rw [← hsplit_m]
          exact div_le_div_of_nonneg_right hlog (by positivity)
      _ = 5 / ((m : ℝ) ^ (3 / 4 : ℝ) * (rad m : ℝ)) := by
          have hrp_ne : (m : ℝ) ^ (1 / 4 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hm_pos _).ne'
          field_simp
      _ ≤ 5 / ((aPart m : ℝ) * (uPart m : ℝ) * (vPart m : ℝ)) ^ (3 / 2 : ℝ) := by
          exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hden_ge
      _ = 5 * (1 / ((aPart m : ℝ) * (uPart m : ℝ) * (vPart m : ℝ)) ^ (3 / 2 : ℝ)) := by ring
  -- Step 2: inject m -> (aPart m, uPart m, vPart m) into (Icc 1 M)^3
  let triple : ℕ → ℕ × ℕ × ℕ := fun m => (aPart m, uPart m, vPart m)
  have htriple_mem : ∀ m ∈ Finset.Icc 1 M,
      triple m ∈ (Finset.Icc 1 M) ×ˢ ((Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M)) := by
    intro m hm
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have hmM : m ≤ M := (Finset.mem_Icc.mp hm).2
    have hd := hdecomp m hm1
    have ha_le : aPart m ≤ m := by
      have h1 : 1 ≤ (uPart m) ^ 2 * (vPart m) ^ 3 :=
        Nat.mul_pos (pow_pos (hu_pos m) 2) (pow_pos (hv_pos m) 3)
      calc aPart m = aPart m * 1 := (mul_one _).symm
        _ ≤ aPart m * ((uPart m) ^ 2 * (vPart m) ^ 3) := Nat.mul_le_mul_left _ h1
        _ = m := by rw [← mul_assoc]; exact hd.symm
    have hu_le : uPart m ≤ m := by
      have h1 : uPart m ≤ (uPart m) ^ 2 := by
        calc uPart m = uPart m * 1 := (mul_one _).symm
          _ ≤ uPart m * uPart m := Nat.mul_le_mul_left _ (hu_pos m)
          _ = (uPart m) ^ 2 := (sq _).symm
      have h2 : (uPart m) ^ 2 ≤ m := by
        calc (uPart m) ^ 2 = 1 * (uPart m) ^ 2 * 1 := by ring
          _ ≤ aPart m * (uPart m) ^ 2 * (vPart m) ^ 3 :=
            Nat.mul_le_mul (Nat.mul_le_mul_right _ (ha_pos m)) (Nat.one_le_pow 3 _ (hv_pos m))
          _ = m := hd.symm
      exact le_trans h1 h2
    have hv_le : vPart m ≤ m := by
      have h1 : vPart m ≤ (vPart m) ^ 3 := by
        have hv1 := hv_pos m
        calc vPart m = vPart m * 1 * 1 := by ring
          _ ≤ vPart m * vPart m * vPart m :=
            Nat.mul_le_mul (Nat.mul_le_mul_left _ hv1) hv1
          _ = (vPart m) ^ 3 := by ring
      have h2 : (vPart m) ^ 3 ≤ m := by
        calc (vPart m) ^ 3 = 1 * (vPart m) ^ 3 := (one_mul _).symm
          _ ≤ (aPart m * (uPart m) ^ 2) * (vPart m) ^ 3 :=
            Nat.mul_le_mul_right _ (Nat.mul_pos (ha_pos m) (pow_pos (hu_pos m) 2))
          _ = m := hd.symm
      exact le_trans h1 h2
    simp only [triple, Finset.mem_product, Finset.mem_Icc]
    exact ⟨⟨ha_pos m, le_trans ha_le hmM⟩, ⟨hu_pos m, le_trans hu_le hmM⟩, ⟨hv_pos m, le_trans hv_le hmM⟩⟩
  have htriple_inj : Set.InjOn triple (Finset.Icc 1 M : Set ℕ) := by
    intro m₁ hm₁ m₂ hm₂ hEq
    have h1 := hdecomp m₁ (Finset.mem_Icc.mp hm₁).1
    have h2 := hdecomp m₂ (Finset.mem_Icc.mp hm₂).1
    have ha : aPart m₁ = aPart m₂ := congrArg Prod.fst hEq
    have hu : uPart m₁ = uPart m₂ := congrArg (fun x => x.2.1) hEq
    have hv : vPart m₁ = vPart m₂ := congrArg (fun x => x.2.2) hEq
    rw [h1, h2, ha, hu, hv]
  calc ∑ m ∈ Finset.Icc 1 M, ((Real.log (m : ℝ) + 1) / ((m : ℝ) * (rad m : ℝ)))
      ≤ ∑ m ∈ Finset.Icc 1 M,
          5 * (((aPart m : ℝ) ^ (-(3 / 2 : ℝ))) * ((uPart m : ℝ) ^ (-(3 / 2 : ℝ))) *
            ((vPart m : ℝ) ^ (-(3 / 2 : ℝ)))) := Finset.sum_le_sum hterm
    _ = 5 * ∑ x ∈ (Finset.Icc 1 M).image triple,
          ((x.1 : ℝ) ^ (-(3 / 2 : ℝ))) * ((x.2.1 : ℝ) ^ (-(3 / 2 : ℝ))) *
            ((x.2.2 : ℝ) ^ (-(3 / 2 : ℝ))) := by
        rw [← Finset.mul_sum, Finset.sum_image htriple_inj]
    _ ≤ 5 * ∑ x ∈ (Finset.Icc 1 M) ×ˢ ((Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M)),
          ((x.1 : ℝ) ^ (-(3 / 2 : ℝ))) * ((x.2.1 : ℝ) ^ (-(3 / 2 : ℝ))) *
            ((x.2.2 : ℝ) ^ (-(3 / 2 : ℝ))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
        · intro x hx
          rcases Finset.mem_image.mp hx with ⟨m, hm, rfl⟩
          exact htriple_mem m hm
        · intro x _ _
          positivity
    _ = 5 * ((∑ a ∈ Finset.Icc 1 M, ((a : ℝ) ^ (-(3 / 2 : ℝ)))) *
          (∑ u ∈ Finset.Icc 1 M, ((u : ℝ) ^ (-(3 / 2 : ℝ)))) *
          (∑ v ∈ Finset.Icc 1 M, ((v : ℝ) ^ (-(3 / 2 : ℝ))))) := by
        congr 1
        rw [Finset.sum_product]
        simp_rw [Finset.sum_product, mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul]
    _ ≤ 5 * (3 * 3 * 3) := by
        have h3 := sum_rpow_neg_three_halves_le_three M
        have h0 : 0 ≤ ∑ a ∈ Finset.Icc 1 M, ((a : ℝ) ^ (-(3 / 2 : ℝ))) :=
          Finset.sum_nonneg (fun _ _ => by positivity)
        nlinarith
    _ = 135 := by norm_num

lemma mertens_1d {W : ℕ} (hW : 0 < W) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Y : ℝ, 1 ≤ Y →
      |(∑ r ∈ (Finset.Icc 1 ⌊Y⌋₊).filter (fun r => Squarefree r ∧ Nat.Coprime r W),
          (1 / (Nat.totient r : ℝ))) -
        ((Nat.totient W : ℝ) / (W : ℝ)) * Real.log Y| ≤ C := by
  classical
  obtain ⟨C₁, hC₁_nonneg, hC₁⟩ := harmonic_coprime_bound hW
  refine ⟨C₁ + 135, by linarith, ?_⟩
  intro Y hY
  set S_W := (Finset.Icc 1 ⌊Y⌋₊).filter (fun r => Squarefree r ∧ Nat.Coprime r W)
  set H_W := (Finset.Icc 1 ⌊Y⌋₊).filter (fun n => Nat.Coprime n W)
  have hY_fl_pos : 1 ≤ ⌊Y⌋₊ := (Nat.le_floor_iff (by linarith)).mpr (by exact_mod_cast hY)
  -- Group H_W by rad n
  have hH_fiber :
      ∑ n ∈ H_W, (1 / (n : ℝ)) =
      ∑ r ∈ S_W, ∑ n ∈ (Finset.Icc 1 ⌊Y⌋₊).filter (fun n => rad n = r), (1 / (n : ℝ)) := by
    have hmap : ∀ n ∈ H_W, rad n ∈ S_W := by
      intro n hn
      rw [Finset.mem_filter, Finset.mem_Icc] at hn
      rw [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨rad_pos, le_trans (Nat.le_of_dvd hn.1.1 (rad_dvd_self n)) hn.1.2⟩,
        squarefree_rad n, (coprime_rad_iff (by omega)).mpr hn.2⟩
    rw [← Finset.sum_fiberwise_of_maps_to hmap]
    refine Finset.sum_congr rfl ?_
    intro r hr
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, H_W, S_W] at hr ⊢
    constructor
    · rintro ⟨⟨hn, _⟩, hrad⟩
      exact ⟨hn, hrad⟩
    · rintro ⟨hn, hrad⟩
      refine ⟨⟨hn, ?_⟩, hrad⟩
      exact (coprime_rad_iff (by omega)).mp (hrad ▸ hr.2.2)
  -- For any N >= floor Y, compare GN(r) with HW
  let G : ℕ → ℕ → ℝ := fun N r =>
    ∏ p ∈ r.primeFactors, (∑ e ∈ Finset.Icc 1 N, (1 / (p : ℝ) ^ e))
  have hG_le : ∀ N r, Squarefree r → G N r ≤ 1 / (Nat.totient r : ℝ) := by
    intro N r hr
    dsimp only [G]
    rw [totient_eq_prod_primeFactors_of_squarefree hr, Nat.cast_prod, one_div,
      ← Finset.prod_inv_distrib]
    refine Finset.prod_le_prod ?_ ?_
    · intro p _
      exact Finset.sum_nonneg (fun _ _ => by positivity)
    · intro p hp
      have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
      rw [geom_sum_inv_prime hp2]
      have hp_r : (2 : ℝ) ≤ p := by exact_mod_cast hp2
      have hden_pos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
      have hcast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]; simp
      rw [hcast, ← one_div]
      refine div_le_div_of_nonneg_right ?_ hden_pos.le
      have : (0 : ℝ) ≤ (1 / (p : ℝ)) ^ N := by positivity
      linarith
  have hG_tendsto : ∀ r, Squarefree r →
      Filter.Tendsto (fun N => G N r) Filter.atTop (nhds (1 / (Nat.totient r : ℝ))) := by
    intro r hr
    dsimp only [G]
    rw [totient_eq_prod_primeFactors_of_squarefree hr, Nat.cast_prod, one_div,
      ← Finset.prod_inv_distrib]
    refine tendsto_finsetProd r.primeFactors ?_
    intro p hp
    have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
    have hp_r : (2 : ℝ) ≤ p := by exact_mod_cast hp2
    have hcast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    rw [hcast, ← one_div]
    have hfun : (fun N => ∑ e ∈ Finset.Icc 1 N, (1 / (p : ℝ) ^ e)) =
        fun N => (1 - (1 / (p : ℝ)) ^ N) / ((p : ℝ) - 1) := by
      funext N
      exact geom_sum_inv_prime hp2
    rw [hfun]
    have hlt1 : (1 / (p : ℝ)) < 1 := by rw [div_lt_one (by linarith)]; linarith
    have hzero : Filter.Tendsto (fun N => (1 / (p : ℝ)) ^ N) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hlt1
    have hsub : Filter.Tendsto (fun N => (1 : ℝ) - (1 / (p : ℝ)) ^ N) Filter.atTop (nhds (1 - 0)) :=
      tendsto_const_nhds.sub hzero
    simpa using hsub.div_const ((p : ℝ) - 1)
  -- Lower bound: sum{HW} 1/n <= sum{SW} 1/phi(r)
  have hlow : ∑ n ∈ H_W, (1 / (n : ℝ)) ≤ ∑ r ∈ S_W, (1 / (Nat.totient r : ℝ)) := by
    rw [hH_fiber]
    refine Finset.sum_le_sum ?_
    intro r hr
    have hr_sq : Squarefree r := (Finset.mem_filter.mp hr).2.1
    obtain ⟨T, _, hsub, hG_eq⟩ := geom_prod_eq_sum_rad (N := ⌊Y⌋₊) hr_sq
    calc ∑ n ∈ (Finset.Icc 1 ⌊Y⌋₊).filter (fun n => rad n = r), (1 / (n : ℝ))
        ≤ ∑ n ∈ T, (1 / (n : ℝ)) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ = G ⌊Y⌋₊ r := hG_eq.symm
      _ ≤ 1 / (Nat.totient r : ℝ) := hG_le ⌊Y⌋₊ r hr_sq
  -- Upper bound: for all N >= floor Y, sum{SW} G N r - sum{HW} 1/n <= 135
  have hup_N : ∀ N : ℕ, ⌊Y⌋₊ ≤ N →
      (∑ r ∈ S_W, G N r) - (∑ n ∈ H_W, (1 / (n : ℝ))) ≤ 135 := by
    intro N hNY
    rw [hH_fiber, ← Finset.sum_sub_distrib]
    -- For each r in SW, choose Tr from geomprodeqsumrad
    choose T hT_prop hT_sub hT_eq using fun r (hr : r ∈ S_W) =>
      geom_prod_eq_sum_rad (r := r) (N := N) (Finset.mem_filter.mp hr).2.1
    have hdiff_eq :
        ∑ r ∈ S_W, (G N r - ∑ n ∈ (Finset.Icc 1 ⌊Y⌋₊).filter (fun n => rad n = r), (1 / (n : ℝ))) =
        ∑ r ∈ S_W.attach, ∑ n ∈ (T r.1 r.2) \ ((Finset.Icc 1 ⌊Y⌋₊).filter (fun n => rad n = r.1)),
          (1 / (n : ℝ)) := by
      rw [← Finset.sum_attach S_W]
      refine Finset.sum_congr rfl ?_
      intro r _
      have hsub1 : (Finset.Icc 1 ⌊Y⌋₊).filter (fun n => rad n = r.1) ⊆ T r.1 r.2 := by
        refine Subset.trans ?_ (hT_sub r.1 r.2)
        intro n hn
        rw [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
        exact ⟨⟨hn.1.1, le_trans hn.1.2 hNY⟩, hn.2⟩
      dsimp only [G]
      rw [hT_eq r.1 r.2, Finset.sum_sdiff_eq_sub hsub1]
    rw [hdiff_eq]
    -- Collect all n appearing in the disjoint union of tail sets into a single Finset U
    let U : Finset ℕ := S_W.attach.biUnion (fun r =>
      (T r.1 r.2) \ ((Finset.Icc 1 ⌊Y⌋₊).filter (fun n => rad n = r.1)))
    have hdisj : Set.PairwiseDisjoint (S_W.attach : Set {x // x ∈ S_W})
        (fun r => (T r.1 r.2) \ ((Finset.Icc 1 ⌊Y⌋₊).filter (fun n => rad n = r.1))) := by
      intro r₁ _ r₂ _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro n hn₁ hn₂
      have hrad₁ := (hT_prop r₁.1 r₁.2 n (Finset.mem_sdiff.mp hn₁).1).2
      have hrad₂ := (hT_prop r₂.1 r₂.2 n (Finset.mem_sdiff.mp hn₂).1).2
      exact hne (Subtype.ext (hrad₁.symm.trans hrad₂))
    rw [← Finset.sum_biUnion hdisj]
    -- Every n in U has rad n <= floor Y, n > floor Y, and m := n / rad n >= 1 with rad m | rad n
    let M_max : ℕ := U.sup id + 1
    have hU_prop : ∀ n ∈ U,
        0 < n ∧ ⌊Y⌋₊ < n ∧ rad n ≤ ⌊Y⌋₊ ∧ 1 ≤ n / rad n ∧ n / rad n ≤ M_max := by
      intro n hn
      rcases Finset.mem_biUnion.mp hn with ⟨r, _, hnr⟩
      rw [Finset.mem_sdiff] at hnr
      have hpos_rad := hT_prop r.1 r.2 n hnr.1
      have hr_le : r.1 ≤ ⌊Y⌋₊ := (Finset.mem_Icc.mp (Finset.mem_filter.mp r.2).1).2
      have hgt : ⌊Y⌋₊ < n := by
        by_contra hle
        push Not at hle
        exact hnr.2 (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hpos_rad.1, hle⟩, hpos_rad.2⟩)
      have hdiv_pos : 1 ≤ n / rad n := Nat.div_pos (Nat.le_of_dvd hpos_rad.1 (rad_dvd_self n)) rad_pos
      have hdiv_le : n / rad n ≤ M_max :=
        le_trans (Nat.div_le_self n (rad n)) (le_trans (Finset.le_sup (f := id) hn) (Nat.le_succ _))
      exact ⟨hpos_rad.1, hgt, hpos_rad.2 ▸ hr_le, hdiv_pos, hdiv_le⟩
    -- Group n in U by m = n / rad n in Icc 1 M_max
    have hmaps : ∀ n ∈ U, n / rad n ∈ Finset.Icc 1 M_max := by
      intro n hn
      have hp := hU_prop n hn
      exact Finset.mem_Icc.mpr ⟨hp.2.2.2.1, hp.2.2.2.2⟩
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    -- Bound each fiber over m by (log m + 1) / (m * rad m)
    have hfiber_le : ∀ m ∈ Finset.Icc 1 M_max,
        ∑ n ∈ U.filter (fun n => n / rad n = m), (1 / (n : ℝ)) ≤
          (Real.log (m : ℝ) + 1) / ((m : ℝ) * (rad m : ℝ)) := by
      intro m hm
      have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
      have hm_pos_r : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm1
      have hrad_pos_r : (0 : ℝ) < (rad m : ℝ) := Nat.cast_pos.mpr rad_pos
      have hmrad_pos_r : (0 : ℝ) < (m : ℝ) * (rad m : ℝ) := mul_pos hm_pos_r hrad_pos_r
      -- Map n -> rad n / rad m into Ioc (floor (Y / (m * rad m))) (floor (Y / rad m))
      let A := ⌊Y / ((m : ℝ) * (rad m : ℝ))⌋₊
      let B := ⌊Y / (rad m : ℝ)⌋₊
      let tMap : ℕ → ℕ := fun n => rad n / rad m
      have ht_mem : ∀ n ∈ U.filter (fun n => n / rad n = m), tMap n ∈ Finset.Ioc A B := by
        intro n hn
        have hnU : n ∈ U := (Finset.mem_filter.mp hn).1
        have hnm : n / rad n = m := (Finset.mem_filter.mp hn).2
        have hp := hU_prop n hnU
        have hn_eq : rad n * m = n := by
          rw [← hnm, Nat.mul_div_cancel' (rad_dvd_self n)]
        have hrad_m_dvd : rad m ∣ rad n := by
          have hm_dvd_n : m ∣ n := ⟨rad n, by linarith⟩
          have hpf_sub : m.primeFactors ⊆ n.primeFactors := Nat.primeFactors_mono hm_dvd_n (by omega)
          unfold rad
          exact Finset.prod_dvd_prod_of_subset _ _ _ hpf_sub
        have ht_mul : tMap n * rad m = rad n := Nat.div_mul_cancel hrad_m_dvd
        rw [Finset.mem_Ioc]
        constructor
        · -- A < tMap n
          have hY_lt_n : Y < (n : ℝ) := by
            have : (⌊Y⌋₊ : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hp.2.1
            linarith [Nat.lt_floor_add_one Y]
          have htm_gt : Y < (tMap n : ℝ) * ((m : ℝ) * (rad m : ℝ)) := by
            have heq : (tMap n : ℝ) * ((m : ℝ) * (rad m : ℝ)) = (n : ℝ) := by
              have : tMap n * (m * rad m) = n := by
                calc tMap n * (m * rad m) = (tMap n * rad m) * m := by ring
                  _ = rad n * m := by rw [ht_mul]
                  _ = n := hn_eq
              exact_mod_cast this
            linarith
          have hdiv_lt : Y / ((m : ℝ) * (rad m : ℝ)) < (tMap n : ℝ) := by
            rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (m : ℝ) * (rad m : ℝ))]
            exact htm_gt
          exact (Nat.floor_lt (by positivity)).mpr hdiv_lt
        · -- tMap n <= B
          have hrad_le_Y : (rad n : ℝ) ≤ Y :=
            le_trans (Nat.cast_le.mpr hp.2.2.1) (Nat.floor_le (by linarith))
          have hle : (tMap n : ℝ) ≤ Y / (rad m : ℝ) := by
            rw [le_div_iff₀ (Nat.cast_pos.mpr rad_pos)]
            have : (tMap n : ℝ) * (rad m : ℝ) = (rad n : ℝ) := by exact_mod_cast ht_mul
            linarith
          exact (Nat.le_floor_iff (by positivity)).mpr hle
      have ht_inj : Set.InjOn tMap (U.filter (fun n => n / rad n = m) : Set ℕ) := by
        intro n₁ hn₁ n₂ hn₂ hEq
        have hp₁ := hU_prop n₁ (Finset.mem_filter.mp hn₁).1
        have hp₂ := hU_prop n₂ (Finset.mem_filter.mp hn₂).1
        have hm₁ : n₁ / rad n₁ = m := (Finset.mem_filter.mp hn₁).2
        have hm₂ : n₂ / rad n₂ = m := (Finset.mem_filter.mp hn₂).2
        have h1 : rad n₁ * m = n₁ := by rw [← hm₁, Nat.mul_div_cancel' (rad_dvd_self n₁)]
        have h2 : rad n₂ * m = n₂ := by rw [← hm₂, Nat.mul_div_cancel' (rad_dvd_self n₂)]
        have hd₁ : rad m ∣ rad n₁ := Finset.prod_dvd_prod_of_subset _ _ _
          (Nat.primeFactors_mono ⟨rad n₁, by linarith⟩ (by omega))
        have hd₂ : rad m ∣ rad n₂ := Finset.prod_dvd_prod_of_subset _ _ _
          (Nat.primeFactors_mono ⟨rad n₂, by linarith⟩ (by omega))
        have hrad_eq : rad n₁ = rad n₂ := by
          rw [← Nat.div_mul_cancel hd₁, ← Nat.div_mul_cancel hd₂]
          exact congrArg (· * rad m) hEq
        rw [← h1, ← h2, hrad_eq]
      have hterm_eq : ∀ n ∈ U.filter (fun n => n / rad n = m),
          (1 / (n : ℝ)) = (1 / ((m : ℝ) * (rad m : ℝ))) * (1 / (tMap n : ℝ)) := by
        intro n hn
        have hp := hU_prop n (Finset.mem_filter.mp hn).1
        have hnm : n / rad n = m := (Finset.mem_filter.mp hn).2
        have hn_eq : rad n * m = n := by rw [← hnm, Nat.mul_div_cancel' (rad_dvd_self n)]
        have hd : rad m ∣ rad n := Finset.prod_dvd_prod_of_subset _ _ _
          (Nat.primeFactors_mono ⟨rad n, by linarith⟩ (by omega))
        have hnat : (m * rad m) * tMap n = n := by
          calc (m * rad m) * tMap n = (tMap n * rad m) * m := by ring
            _ = rad n * m := by rw [Nat.div_mul_cancel hd]
            _ = n := hn_eq
        have hreal : ((m : ℝ) * (rad m : ℝ)) * (tMap n : ℝ) = (n : ℝ) := by exact_mod_cast hnat
        rw [← hreal]
        field_simp
      have hsum_Ioc : ∑ t ∈ Finset.Ioc A B, (1 / (t : ℝ)) ≤ Real.log (m : ℝ) + 1 := by
        by_cases hB : B = 0
        · rw [hB]
          simp only [Finset.Ioc_eq_empty_of_le (Nat.zero_le A), Finset.sum_empty]
          have : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by exact_mod_cast hm1)
          linarith
        · have hB1 : 1 ≤ B := Nat.pos_of_ne_zero hB
          by_cases hA : A = 0
          · rw [hA]
            have hIoc : Finset.Ioc 0 B = Finset.Icc 1 B := by
              ext x; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
            rw [hIoc]
            have hY_lt : Y / ((m : ℝ) * (rad m : ℝ)) < 1 :=
              (Nat.floor_eq_zero).mp hA
            have hB_le_m : (B : ℝ) ≤ (m : ℝ) := by
              have h1 : (B : ℝ) ≤ Y / (rad m : ℝ) := Nat.floor_le (by positivity)
              have h2 : Y / (rad m : ℝ) < (m : ℝ) := by
                rw [div_lt_iff₀ (Nat.cast_pos.mpr rad_pos)]
                have := (div_lt_one (by positivity : (0 : ℝ) < (m : ℝ) * (rad m : ℝ))).mp hY_lt
                linarith
              linarith
            calc ∑ t ∈ Finset.Icc 1 B, (1 / (t : ℝ))
                ≤ Real.log (B : ℝ) + 1 := harmonic_le_log_add_one hB1
              _ ≤ Real.log (m : ℝ) + 1 := by
                  linarith [Real.log_le_log (Nat.cast_pos.mpr hB1) hB_le_m]
          · have hA1 : 1 ≤ A := Nat.pos_of_ne_zero hA
            by_cases hAB : A ≤ B
            · have hsplit : Finset.Icc 1 B = Finset.Icc 1 A ∪ Finset.Ioc A B := by
                ext x; simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]; omega
              have hdisj : Disjoint (Finset.Icc 1 A) (Finset.Ioc A B) := by
                rw [Finset.disjoint_left]
                intro x hx1 hx2
                simp only [Finset.mem_Icc, Finset.mem_Ioc] at hx1 hx2
                omega
              have hsum_eq : ∑ t ∈ Finset.Ioc A B, (1 / (t : ℝ)) =
                  (∑ t ∈ Finset.Icc 1 B, (1 / (t : ℝ))) - (∑ t ∈ Finset.Icc 1 A, (1 / (t : ℝ))) := by
                rw [hsplit, Finset.sum_union hdisj]
                ring
              rw [hsum_eq]
              have hB_up : ∑ t ∈ Finset.Icc 1 B, (1 / (t : ℝ)) ≤
                  Real.log (Y / (rad m : ℝ)) + 1 := by
                have hY_ge1 : 1 ≤ Y / (rad m : ℝ) := by
                  have h1 : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB1
                  exact le_trans h1 (Nat.floor_le (by positivity))
                have hb := harmonic_sub_log_abs_le_one hY_ge1
                linarith [(abs_le.mp hb).2]
              have hA_low : Real.log (Y / ((m : ℝ) * (rad m : ℝ))) ≤
                  ∑ t ∈ Finset.Icc 1 A, (1 / (t : ℝ)) := by
                have hY_ge1 : 1 ≤ Y / ((m : ℝ) * (rad m : ℝ)) := by
                  have h1 : (1 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA1
                  exact le_trans h1 (Nat.floor_le (by positivity))
                -- Actually sum_{1..A} 1/t >= log(A+1) >= log(Y/(m*rad m))!
                have hstep : ∀ n : ℕ, 1 ≤ n →
                    Real.log ((n : ℝ) + 1) - Real.log (n : ℝ) ≤ 1 / (n : ℝ) := by
                  intro n hn
                  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
                  rw [← Real.log_div (by linarith) hn_pos.ne']
                  have h := Real.log_le_sub_one_of_pos (div_pos (by linarith : (0 : ℝ) < n + 1) hn_pos)
                  have heq : ((n : ℝ) + 1) / (n : ℝ) - 1 = 1 / (n : ℝ) := by field_simp; ring
                  linarith
                have htel : ∀ K : ℕ, ∑ n ∈ Finset.Icc 1 K,
                    (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ)) = Real.log ((K : ℝ) + 1) := by
                  intro K
                  induction K with
                  | zero => simp
                  | succ k ih =>
                    have hIcc : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
                      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
                    rw [hIcc, Finset.sum_insert (by simp), ih]; push_cast; ring
                have hge_A1 : Real.log ((A : ℝ) + 1) ≤ ∑ t ∈ Finset.Icc 1 A, (1 / (t : ℝ)) := by
                  rw [← htel A]
                  exact Finset.sum_le_sum (fun n hn => hstep n (Finset.mem_Icc.mp hn).1)
                exact le_trans (Real.log_le_log (by linarith) (Nat.lt_floor_add_one _).le) hge_A1
              have hlog_sub : Real.log (Y / (rad m : ℝ)) - Real.log (Y / ((m : ℝ) * (rad m : ℝ))) =
                  Real.log (m : ℝ) := by
                rw [← Real.log_div (by positivity) (by positivity)]
                congr 1
                have hY_ne : Y ≠ 0 := by linarith
                have hrad_ne : (rad m : ℝ) ≠ 0 := (Nat.cast_pos.mpr rad_pos).ne'
                field_simp
              linarith
            · push Not at hAB
              rw [Finset.Ioc_eq_empty_of_le hAB.le, Finset.sum_empty]
              have : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by exact_mod_cast hm1)
              linarith
      calc ∑ n ∈ U.filter (fun n => n / rad n = m), (1 / (n : ℝ))
          = (1 / ((m : ℝ) * (rad m : ℝ))) *
              ∑ n ∈ U.filter (fun n => n / rad n = m), (1 / (tMap n : ℝ)) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl hterm_eq
        _ = (1 / ((m : ℝ) * (rad m : ℝ))) *
              ∑ t ∈ (U.filter (fun n => n / rad n = m)).image tMap, (1 / (t : ℝ)) := by
            rw [Finset.sum_image ht_inj]
        _ ≤ (1 / ((m : ℝ) * (rad m : ℝ))) * ∑ t ∈ Finset.Ioc A B, (1 / (t : ℝ)) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
            intro t ht
            rcases Finset.mem_image.mp ht with ⟨n, hn, rfl⟩
            exact ht_mem n hn
        _ ≤ (1 / ((m : ℝ) * (rad m : ℝ))) * (Real.log (m : ℝ) + 1) :=
            mul_le_mul_of_nonneg_left hsum_Ioc (by positivity)
        _ = (Real.log (m : ℝ) + 1) / ((m : ℝ) * (rad m : ℝ)) := by ring
    exact le_trans (Finset.sum_le_sum hfiber_le) (sum_log_add_one_div_mul_rad_le M_max)
  -- Take N -> infinity to conclude sum{SW} 1/phi(r) - sum{HW} 1/n <= 135
  have hup : (∑ r ∈ S_W, (1 / (Nat.totient r : ℝ))) - (∑ n ∈ H_W, (1 / (n : ℝ))) ≤ 135 := by
    have htend : Filter.Tendsto
        (fun N => (∑ r ∈ S_W, G N r) - (∑ n ∈ H_W, (1 / (n : ℝ)))) Filter.atTop
        (nhds ((∑ r ∈ S_W, (1 / (Nat.totient r : ℝ))) - (∑ n ∈ H_W, (1 / (n : ℝ))))) := by
      refine (tendsto_finsetSum S_W ?_).sub tendsto_const_nhds
      intro r hr
      exact hG_tendsto r (Finset.mem_filter.mp hr).2.1
    exact le_of_tendsto htend (Filter.eventually_atTop.mpr ⟨⌊Y⌋₊, hup_N⟩)
  have hH_abs := hC₁ Y hY
  rw [abs_le] at hH_abs ⊢
  constructor <;> linarith

/-- Product lower bound: prod{x in s} (1 - f x) >= 1 - sum{x in s} f x for f x in [0, 1]. -/
lemma prod_one_sub_ge_one_sub_sum {α : Type*} (s : Finset α) (f : α → ℝ)
    (hf0 : ∀ x ∈ s, 0 ≤ f x) (hf1 : ∀ x ∈ s, f x ≤ 1) :
    1 - ∑ x ∈ s, f x ≤ ∏ x ∈ s, (1 - f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have hfa0 : 0 ≤ f a := hf0 a (Finset.mem_insert_self a s)
    have hfa1 : f a ≤ 1 := hf1 a (Finset.mem_insert_self a s)
    have hs := ih (fun x hx => hf0 x (Finset.mem_insert_of_mem hx))
      (fun x hx => hf1 x (Finset.mem_insert_of_mem hx))
    have hsum_nonneg : 0 ≤ ∑ x ∈ s, f x := Finset.sum_nonneg (fun x hx => hf0 x (Finset.mem_insert_of_mem hx))
    nlinarith

/-- Product of (1 + f x) is bounded by exp(sum f x) for f x >= 0. -/
lemma prod_one_add_le_exp_sum {α : Type*} (s : Finset α) (f : α → ℝ)
    (hf0 : ∀ x ∈ s, 0 ≤ f x) :
    ∏ x ∈ s, (1 + f x) ≤ Real.exp (∑ x ∈ s, f x) := by
  rw [Real.exp_sum]
  refine Finset.prod_le_prod (fun x hx => by linarith [hf0 x hx]) ?_
  intro x _
  linarith [Real.add_one_le_exp (f x)]

/-- Bound on sum of 1 / (p - c)^2 over primes p > D0. -/
lemma sum_inv_sub_sq_primes_le {D0 c : ℕ} (hD : c + 2 ≤ D0) (s : Finset ℕ)
    (hs : ∀ p ∈ s, D0 < p) :
    ∑ p ∈ s, (1 / ((p : ℝ) - (c : ℝ)) ^ 2) ≤ 1 / ((D0 : ℝ) - (c : ℝ) - 1) := by
  let M := s.sup id
  have hsub : s ⊆ Finset.Icc (D0 + 1) M := by
    intro p hp
    exact Finset.mem_Icc.mpr ⟨hs p hp, Finset.le_sup (f := id) hp⟩
  have hstep : ∀ n ∈ Finset.Icc (D0 + 1) M,
      1 / ((n : ℝ) - (c : ℝ)) ^ 2 ≤
        1 / ((n : ℝ) - (c : ℝ) - 1) - 1 / ((n : ℝ) - (c : ℝ)) := by
    intro n hn
    have hnD : D0 + 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have h1 : (1 : ℝ) < (n : ℝ) - (c : ℝ) := by
      have : c + 3 ≤ n := by omega
      have : ((c + 3 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast this
      push_cast at this; linarith
    have hden1 : (0 : ℝ) < (n : ℝ) - (c : ℝ) - 1 := by linarith
    have hden2 : (0 : ℝ) < (n : ℝ) - (c : ℝ) := by linarith
    have heq : 1 / ((n : ℝ) - (c : ℝ) - 1) - 1 / ((n : ℝ) - (c : ℝ)) =
        1 / (((n : ℝ) - (c : ℝ) - 1) * ((n : ℝ) - (c : ℝ))) := by
      field_simp; ring
    rw [heq]
    refine div_le_div_of_nonneg_left (by norm_num) (by positivity) ?_
    nlinarith
  have htel : ∀ K : ℕ, D0 ≤ K →
      ∑ n ∈ Finset.Icc (D0 + 1) K, (1 / ((n : ℝ) - (c : ℝ) - 1) - 1 / ((n : ℝ) - (c : ℝ))) =
        1 / ((D0 : ℝ) - (c : ℝ)) - 1 / ((K : ℝ) - (c : ℝ)) := by
    intro K hK
    induction K with
    | zero =>
      have : D0 = 0 := by omega
      subst this; simp
    | succ k ih =>
      by_cases hk : D0 ≤ k
      · have hIcc : Finset.Icc (D0 + 1) (k + 1) = insert (k + 1) (Finset.Icc (D0 + 1) k) := by
          ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        rw [hIcc, Finset.sum_insert (by simp), ih hk]
        push_cast; ring
      · have : k + 1 = D0 := by omega
        rw [this, Finset.Icc_eq_empty_of_lt (by omega : D0 < D0 + 1), Finset.sum_empty]
        ring
  by_cases hM : D0 ≤ M
  · calc ∑ p ∈ s, (1 / ((p : ℝ) - (c : ℝ)) ^ 2)
        ≤ ∑ n ∈ Finset.Icc (D0 + 1) M, (1 / ((n : ℝ) - (c : ℝ)) ^ 2) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ ≤ ∑ n ∈ Finset.Icc (D0 + 1) M,
            (1 / ((n : ℝ) - (c : ℝ) - 1) - 1 / ((n : ℝ) - (c : ℝ))) :=
          Finset.sum_le_sum hstep
      _ = 1 / ((D0 : ℝ) - (c : ℝ)) - 1 / ((M : ℝ) - (c : ℝ)) := htel M hM
      _ ≤ 1 / ((D0 : ℝ) - (c : ℝ)) := by
          have hMc : (0 : ℝ) < (M : ℝ) - (c : ℝ) := by
            have : c + 2 ≤ M := by omega
            have : ((c + 2 : ℕ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast this
            push_cast at this; linarith
          linarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 1) hMc.le]
      _ ≤ 1 / ((D0 : ℝ) - (c : ℝ) - 1) := by
          have hDc : (1 : ℝ) ≤ (D0 : ℝ) - (c : ℝ) - 1 := by
            have : ((c + 2 : ℕ) : ℝ) ≤ (D0 : ℝ) := by exact_mod_cast hD
            push_cast at this; linarith
          exact div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
  · have hs_empty : s = ∅ := by
      ext p
      simp only [Finset.notMem_empty, iff_false]
      intro hp
      have h1 := hs p hp
      have h2 : p ≤ M := Finset.le_sup (f := id) hp
      omega
    rw [hs_empty, Finset.sum_empty]
    have hDc : (1 : ℝ) ≤ (D0 : ℝ) - (c : ℝ) - 1 := by
      have : ((c + 2 : ℕ) : ℝ) ≤ (D0 : ℝ) := by exact_mod_cast hD
      push_cast at this; linarith
    positivity

/-- Multiplicative upper bound on sum over squarefree numbers whose prime factors are all > D0. -/
lemma sum_mult_squarefree_le_exp {D0 c : ℕ} (hD : c + 2 ≤ D0)
    (S : Finset ℕ)
    (hS : ∀ n ∈ S, Squarefree n ∧ ∀ p ∈ n.primeFactors, D0 < p)
    (f : ℕ → ℝ) (hf_nonneg : ∀ p, 0 ≤ f p)
    (hf_le : ∀ p, D0 < p → f p ≤ 1 / ((p : ℝ) - (c : ℝ)) ^ 2) :
    ∑ n ∈ S, (∏ p ∈ n.primeFactors, f p) ≤ Real.exp (1 / ((D0 : ℝ) - (c : ℝ) - 1)) := by
  classical
  let P : Finset ℕ := S.biUnion Nat.primeFactors
  have hP : ∀ p ∈ P, D0 < p := by
    intro p hp
    rcases Finset.mem_biUnion.mp hp with ⟨n, hn, hpn⟩
    exact (hS n hn).2 p hpn
  have hP_prime : ∀ p ∈ P, p.Prime := by
    intro p hp
    rcases Finset.mem_biUnion.mp hp with ⟨n, _, hpn⟩
    exact Nat.prime_of_mem_primeFactors hpn
  have hsum_le : ∑ n ∈ S, (∏ p ∈ n.primeFactors, f p) ≤ ∏ p ∈ P, (1 + f p) := by
    rw [Finset.prod_one_add]
    have hmaps : ∀ n ∈ S, n.primeFactors ∈ P.powerset := by
      intro n hn
      rw [Finset.mem_powerset]
      intro p hp
      exact Finset.mem_biUnion.mpr ⟨n, hn, hp⟩
    have hinj : Set.InjOn Nat.primeFactors (S : Set ℕ) := by
      intro n₁ hn₁ n₂ hn₂ hEq
      rw [← squarefree_eq_prod_primeFactors (hS n₁ hn₁).1,
        ← squarefree_eq_prod_primeFactors (hS n₂ hn₂).1, hEq]
    calc ∑ n ∈ S, (∏ p ∈ n.primeFactors, f p)
        = ∑ s ∈ S.image Nat.primeFactors, (∏ p ∈ s, f p) :=
          (Finset.sum_image (f := fun s => ∏ p ∈ s, f p) hinj).symm
      _ ≤ ∑ s ∈ P.powerset, (∏ p ∈ s, f p) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
          · intro s hs
            rcases Finset.mem_image.mp hs with ⟨n, hn, rfl⟩
            exact hmaps n hn
          · intro s _ _
            exact Finset.prod_nonneg (fun p _ => hf_nonneg p)
  calc ∑ n ∈ S, (∏ p ∈ n.primeFactors, f p)
      ≤ ∏ p ∈ P, (1 + f p) := hsum_le
    _ ≤ Real.exp (∑ p ∈ P, f p) := prod_one_add_le_exp_sum P f (fun p _ => hf_nonneg p)
    _ ≤ Real.exp (∑ p ∈ P, (1 / ((p : ℝ) - (c : ℝ)) ^ 2)) :=
        Real.exp_le_exp.mpr (Finset.sum_le_sum (fun p hp => hf_le p (hP p hp)))
    _ ≤ Real.exp (1 / ((D0 : ℝ) - (c : ℝ) - 1)) :=
        Real.exp_le_exp.mpr (sum_inv_sub_sq_primes_le hD P hP)

/-- Primorial W(D0) = prod_{p <= D0, p prime} p. -/
def primorial (D0 : ℕ) : ℕ :=
  ∏ p ∈ (Finset.range (D0 + 1)).filter Nat.Prime, p

lemma primorial_pos (D0 : ℕ) : 0 < primorial D0 :=
  Finset.prod_pos (fun _ hp => (Finset.mem_filter.mp hp).2.pos)

lemma prime_dvd_primorial_iff {D0 p : ℕ} (hp : p.Prime) :
    p ∣ primorial D0 ↔ p ≤ D0 := by
  unfold primorial
  rw [hp.prime.dvd_finsetProd_iff]
  constructor
  · rintro ⟨q, hq, hpq⟩
    rw [Finset.mem_filter, Finset.mem_range] at hq
    have heq : p = q := (Nat.prime_dvd_prime_iff_eq hp hq.2).mp hpq
    omega
  · intro hle
    exact ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp⟩, dvd_refl p⟩

lemma prime_gt_of_coprime_primorial {D0 n p : ℕ} (hc : Nat.Coprime n (primorial D0))
    (hp : p ∈ n.primeFactors) : D0 < p := by
  have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
  by_contra hle
  push Not at hle
  have h1 : p ∣ n := Nat.dvd_of_mem_primeFactors hp
  have h2 : p ∣ primorial D0 := (prime_dvd_primorial_iff hprime).mpr hle
  exact hprime.not_dvd_one (hc.gcd_eq_one ▸ Nat.dvd_gcd h1 h2)

lemma coprime_mul_primorial_iff {D0 M n : ℕ} (hM : 0 < M) (hMD : M ≤ D0) :
    Nat.Coprime n (M * primorial D0) ↔ Nat.Coprime n (primorial D0) := by
  constructor
  · exact Nat.Coprime.coprime_dvd_right (dvd_mul_left _ _)
  · intro hc
    rw [Nat.coprime_mul_iff_right]
    refine ⟨?_, hc⟩
    rw [Nat.coprime_iff_gcd_eq_one]
    by_contra hne
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
    have hpn : p ∣ n := dvd_trans hpdvd (Nat.gcd_dvd_left n M)
    have hpM : p ∣ M := dvd_trans hpdvd (Nat.gcd_dvd_right n M)
    have hp_le : p ≤ D0 := le_trans (Nat.le_of_dvd hM hpM) hMD
    have hpW : p ∣ primorial D0 := (prime_dvd_primorial_iff hp).mpr hp_le
    exact hp.not_dvd_one (hc.gcd_eq_one ▸ Nat.dvd_gcd hpn hpW)

lemma totient_mul_primorial {D0 M : ℕ} (hM : 0 < M) (hMD : M ≤ D0) :
    Nat.totient (M * primorial D0) = M * Nat.totient (primorial D0) := by
  have hW_pos : 0 < primorial D0 := primorial_pos D0
  have hMW_ne : M * primorial D0 ≠ 0 := mul_ne_zero hM.ne' hW_pos.ne'
  have hpf : (M * primorial D0).primeFactors = (primorial D0).primeFactors := by
    ext p
    simp only [Nat.mem_primeFactors]
    constructor
    · rintro ⟨hp, hdvd, _⟩
      rcases hp.dvd_mul.mp hdvd with h | h
      · exact ⟨hp, (prime_dvd_primorial_iff hp).mpr (le_trans (Nat.le_of_dvd hM h) hMD), hW_pos.ne'⟩
      · exact ⟨hp, h, hW_pos.ne'⟩
    · rintro ⟨hp, h, _⟩
      exact ⟨hp, dvd_mul_of_dvd_right h M, hMW_ne⟩
  have hq : (Nat.totient (M * primorial D0) : ℚ) = (M * Nat.totient (primorial D0) : ℚ) := by
    rw [Nat.totient_eq_mul_prod_factors, Nat.totient_eq_mul_prod_factors, hpf]
    push_cast
    ring
  exact_mod_cast hq

/-- Chinese Remainder Theorem over any Finset of pairwise coprime moduli. -/
lemma crt_finset {ι : Type*} (s : Finset ι) (m r : ι → ℕ)
    (hcop : (s : Set ι).Pairwise (fun i j => Nat.Coprime (m i) (m j))) :
    ∃ x : ℕ, ∀ i ∈ s, x ≡ r i [MOD m i] := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a s ha ih =>
    have hcop_s : (s : Set ι).Pairwise (fun i j => Nat.Coprime (m i) (m j)) :=
      hcop.mono (Finset.subset_insert a s)
    obtain ⟨x₀, hx₀⟩ := ih hcop_s
    have hcop_a : Nat.Coprime (m a) (∏ i ∈ s, m i) := by
      refine Nat.Coprime.prod_right ?_
      intro i hi
      exact hcop (Finset.mem_insert_self a s) (Finset.mem_insert_of_mem hi)
        (fun h => ha (h ▸ hi))
    let sol := Nat.chineseRemainder hcop_a (r a) x₀
    refine ⟨sol.1, ?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | his
    · exact sol.2.1
    · have h1 : sol.1 ≡ x₀ [MOD ∏ j ∈ s, m j] := sol.2.2
      have h2 : sol.1 ≡ x₀ [MOD m i] := Nat.ModEq.of_dvd (Finset.dvd_prod_of_mem m his) h1
      exact h2.trans (hx₀ i his)

/-- Admissibility yields a single residue v0 coprime to W for all affine forms M * v0 + b + a. -/
lemma exists_admissible_shift (D0 M b : ℕ) (H : Finset ℕ)
    (hadm : ∀ p, p.Prime → ∃ x, ∀ a ∈ H, ¬ p ∣ M * x + b + a) :
    ∃ v0 : ℕ, ∀ a ∈ H, Nat.Coprime (M * v0 + b + a) (primorial D0) := by
  classical
  let P := (Finset.range (D0 + 1)).filter Nat.Prime
  choose xp hxp using fun p (hp : p ∈ P) => hadm p (Finset.mem_filter.mp hp).2
  let r : ℕ → ℕ := fun p => if hp : p ∈ P then xp p hp else 0
  have hcop : (P : Set ℕ).Pairwise (fun p q => Nat.Coprime p q) := by
    intro p hp q hq hne
    exact (Nat.coprime_primes (Finset.mem_filter.mp hp).2 (Finset.mem_filter.mp hq).2).mpr hne
  obtain ⟨v0, hv0⟩ := crt_finset P id r hcop
  refine ⟨v0, ?_⟩
  intro a ha
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra hne
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
  have hpL : p ∣ M * v0 + b + a := dvd_trans hpdvd (Nat.gcd_dvd_left _ _)
  have hpW : p ∣ primorial D0 := dvd_trans hpdvd (Nat.gcd_dvd_right _ _)
  have hp_le : p ≤ D0 := (prime_dvd_primorial_iff hp).mp hpW
  have hpP : p ∈ P := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp⟩
  have hmod : v0 ≡ xp p hpP [MOD p] := by
    have h := hv0 p hpP
    simpa [r, hpP] using h
  have hmodL : M * v0 + b + a ≡ M * xp p hpP + b + a [MOD p] :=
    ((hmod.mul_left M).add_right b).add_right a
  have hp_xp : p ∣ M * xp p hpP + b + a := (Nat.ModEq.dvd_iff hmodL (dvd_refl p)).mp hpL
  exact hxp p hpP a ha hp_xp

-- ## Section 2: Exact Selberg diagonalization via k by k matrices

lemma pairwise_coprime_of_squarefree_prod {ι : Type*} [DecidableEq ι] {s : Finset ι} {f : ι → ℕ}
    (hs : Squarefree (∏ i ∈ s, f i)) :
    (s : Set ι).Pairwise (fun i j => Nat.Coprime (f i) (f j)) := by
  intro i hi j hj hne
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra hgcd
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hgcd
  have hpi : p ∣ f i := dvd_trans hpdvd (Nat.gcd_dvd_left _ _)
  have hpj : p ∣ f j := dvd_trans hpdvd (Nat.gcd_dvd_right _ _)
  have hprod_dvd : f i * f j ∣ ∏ l ∈ s, f l := by
    rw [← Finset.mul_prod_erase s f hi]
    have hj_er : j ∈ s.erase i := Finset.mem_erase.mpr ⟨hne.symm, hj⟩
    exact mul_dvd_mul_left (f i) (Finset.dvd_prod_of_mem f hj_er)
  have hpp : p * p ∣ ∏ l ∈ s, f l := dvd_trans (mul_dvd_mul hpi hpj) hprod_dvd
  exact hp.ne_one (Nat.isUnit_iff.mp (hs p hpp))

lemma totient_prod_of_squarefree {ι : Type*} [DecidableEq ι] {s : Finset ι} {f : ι → ℕ}
    (hs : Squarefree (∏ i ∈ s, f i)) :
    Nat.totient (∏ i ∈ s, f i) = ∏ i ∈ s, Nat.totient (f i) := by
  have hcop := pairwise_coprime_of_squarefree_prod hs
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hs_sq : Squarefree (∏ i ∈ s, f i) :=
      hs.squarefree_of_dvd (by rw [Finset.prod_insert ha]; exact dvd_mul_left _ _)
    have hca : Nat.Coprime (f a) (∏ i ∈ s, f i) := by
      refine Nat.Coprime.prod_right ?_
      intro i hi
      exact hcop (Finset.mem_insert_self a s) (Finset.mem_insert_of_mem hi) (fun h => ha (h ▸ hi))
    rw [Nat.totient_mul hca, ih hs_sq (hcop.mono (Finset.subset_insert a s))]

lemma phi2_prod_of_squarefree {ι : Type*} [DecidableEq ι] {s : Finset ι} {f : ι → ℕ}
    (hs : Squarefree (∏ i ∈ s, f i)) :
    phi2 (∏ i ∈ s, f i) = ∏ i ∈ s, phi2 (f i) := by
  have hcop := pairwise_coprime_of_squarefree_prod hs
  induction s using Finset.induction_on with
  | empty => simp [phi2_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hs_sq : Squarefree (∏ i ∈ s, f i) :=
      hs.squarefree_of_dvd (by rw [Finset.prod_insert ha]; exact dvd_mul_left _ _)
    have hca : Nat.Coprime (f a) (∏ i ∈ s, f i) := by
      refine Nat.Coprime.prod_right ?_
      intro i hi
      exact hcop (Finset.mem_insert_self a s) (Finset.mem_insert_of_mem hi) (fun h => ha (h ▸ hi))
    rw [phi2_mul_of_coprime hca, ih hs_sq (hcop.mono (Finset.subset_insert a s))]

lemma moebius_prod_of_squarefree {ι : Type*} [DecidableEq ι] {s : Finset ι} {f : ι → ℕ}
    (hs : Squarefree (∏ i ∈ s, f i)) :
    (ArithmeticFunction.moebius (∏ i ∈ s, f i) : ℝ) =
      ∏ i ∈ s, (ArithmeticFunction.moebius (f i) : ℝ) := by
  have hcop := pairwise_coprime_of_squarefree_prod hs
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hs_sq : Squarefree (∏ i ∈ s, f i) :=
      hs.squarefree_of_dvd (by rw [Finset.prod_insert ha]; exact dvd_mul_left _ _)
    have hca : Nat.Coprime (f a) (∏ i ∈ s, f i) := by
      refine Nat.Coprime.prod_right ?_
      intro i hi
      exact hcop (Finset.mem_insert_self a s) (Finset.mem_insert_of_mem hi) (fun h => ha (h ▸ hi))
    have hmul : ArithmeticFunction.moebius (f a * ∏ i ∈ s, f i) =
        ArithmeticFunction.moebius (f a) * ArithmeticFunction.moebius (∏ i ∈ s, f i) :=
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hca
    rw [hmul]
    push_cast
    rw [ih hs_sq (hcop.mono (Finset.subset_insert a s))]

lemma moebius_real_eq_prod_primeFactors {n : ℕ} (hn : Squarefree n) :
    (ArithmeticFunction.moebius n : ℝ) = ∏ _p ∈ n.primeFactors, (-1 : ℝ) := by
  have hprod : ∏ p ∈ n.primeFactors, p = n := squarefree_eq_prod_primeFactors hn
  have hsq_prod : Squarefree (∏ p ∈ n.primeFactors, p) := hprod.symm ▸ hn
  conv_lhs => rw [← hprod]
  rw [moebius_prod_of_squarefree hsq_prod]
  refine Finset.prod_congr rfl ?_
  intro p hp
  rw [ArithmeticFunction.moebius_apply_prime (Nat.prime_of_mem_primeFactors hp)]
  simp

lemma sum_piFinset_prod {ι α : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α]
    (s : ι → Finset α) (f : ι → α → ℝ) :
    ∑ x ∈ Fintype.piFinset s, ∏ i : ι, f i (x i) = ∏ i : ι, ∑ a ∈ s i, f i a := by
  rw [Finset.prod_sum]
  symm
  refine Finset.sum_bij (fun g _ i => g i (Finset.mem_univ i)) ?_ ?_ ?_ ?_
  · intro g hg
    rw [Fintype.mem_piFinset]
    intro i
    exact Finset.mem_pi.mp hg i (Finset.mem_univ i)
  · intro g₁ _ g₂ _ hEq
    funext i hi
    exact congrFun hEq i
  · intro x hx
    refine ⟨fun i _ => x i, Finset.mem_pi.mpr (fun i _ => Fintype.mem_piFinset.mp hx i), rfl⟩
  · intro g _
    rw [Finset.prod_attach (f := fun i => f i (g i (Finset.mem_univ i)))]

lemma moebius_sq_eq_one_of_squarefree {n : ℕ} (hn : Squarefree n) :
    (ArithmeticFunction.moebius n : ℝ) ^ 2 = 1 := by
  rw [moebius_real_eq_prod_primeFactors hn, Finset.prod_const, ← pow_mul, mul_comm, pow_mul]
  norm_num

lemma sum_moebius_mul_div_totient_eq {v : ℕ} (hv : Squarefree v) :
    ∑ t ∈ v.divisors, (ArithmeticFunction.moebius t : ℝ) * (t : ℝ) / (Nat.totient t : ℝ) =
      (ArithmeticFunction.moebius v : ℝ) / (Nat.totient v : ℝ) := by
  have hv0 : v ≠ 0 := squarefree_ne_zero hv
  have hprod : ∏ p ∈ v.primeFactors, (1 + (-(p : ℝ) / ((p : ℝ) - 1))) =
      (ArithmeticFunction.moebius v : ℝ) / (Nat.totient v : ℝ) := by
    rw [moebius_real_eq_prod_primeFactors hv, totient_eq_prod_primeFactors_of_squarefree hv,
      Nat.cast_prod, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl ?_
    intro p hp
    have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
    have hcast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
    have hden : (p : ℝ) - 1 ≠ 0 := by
      have : (2 : ℝ) ≤ p := by exact_mod_cast hp2
      linarith
    rw [hcast]
    field_simp
    ring
  rw [← hprod, Finset.prod_one_add]
  symm
  refine Finset.sum_bij (fun s _ => ∏ p ∈ s, p) ?_ ?_ ?_ ?_
  · intro s hs
    rw [Finset.mem_powerset] at hs
    rw [Nat.mem_divisors]
    refine ⟨?_, hv0⟩
    rw [← squarefree_eq_prod_primeFactors hv]
    exact Finset.prod_dvd_prod_of_subset _ _ _ hs
  · intro s₁ hs₁ s₂ hs₂ hEq
    rw [Finset.mem_powerset] at hs₁ hs₂
    have h1 := primeFactors_prod_subset_primes (fun p hp => Nat.prime_of_mem_primeFactors (hs₁ hp))
    have h2 := primeFactors_prod_subset_primes (fun p hp => Nat.prime_of_mem_primeFactors (hs₂ hp))
    rw [← h1, ← h2, hEq]
  · intro t ht
    rw [Nat.mem_divisors] at ht
    refine ⟨t.primeFactors, ?_, ?_⟩
    · rw [Finset.mem_powerset]
      exact Nat.primeFactors_mono ht.1 hv0
    · exact squarefree_eq_prod_primeFactors (hv.squarefree_of_dvd ht.1)
  · intro s hs
    rw [Finset.mem_powerset] at hs
    have hdvd : (∏ p ∈ s, p) ∣ v := by
      rw [← squarefree_eq_prod_primeFactors hv]
      exact Finset.prod_dvd_prod_of_subset _ _ _ hs
    have ht_sq : Squarefree (∏ p ∈ s, p) := hv.squarefree_of_dvd hdvd
    have hpf : (∏ p ∈ s, p).primeFactors = s :=
      primeFactors_prod_subset_primes (fun p hp => Nat.prime_of_mem_primeFactors (hs hp))
    rw [moebius_real_eq_prod_primeFactors ht_sq, totient_eq_prod_primeFactors_of_squarefree ht_sq,
      hpf, Nat.cast_prod, Nat.cast_prod, ← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl ?_
    intro p hp
    have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors (hs hp)).two_le
    have hcast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
    rw [hcast]
    ring

/-- Valid k-tuple for the Selberg sieve: prod d is squarefree, coprime to W, and <= R. -/
def Valid {k : ℕ} (W R : ℕ) (d : Fin k → ℕ) : Prop :=
  Squarefree (∏ i : Fin k, d i) ∧ Nat.Coprime (∏ i : Fin k, d i) W ∧ ∏ i : Fin k, d i ≤ R

noncomputable def validSet (k W R : ℕ) : Finset (Fin k → ℕ) := by
  classical
  exact (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (Valid W R)

lemma valid_pos_at {k W R : ℕ} {d : Fin k → ℕ} (hd : Valid W R d) (i : Fin k) : 0 < d i := by
  have hprod_pos : 0 < ∏ j : Fin k, d j := squarefree_pos hd.1
  by_contra h0
  push Not at h0
  have : d i = 0 := by omega
  have : ∏ j : Fin k, d j = 0 := Finset.prod_eq_zero (Finset.mem_univ i) this
  omega

lemma valid_le_R_at {k W R : ℕ} {d : Fin k → ℕ} (hd : Valid W R d) (i : Fin k) : d i ≤ R := by
  have hprod_pos : 0 < ∏ j : Fin k, d j := squarefree_pos hd.1
  exact le_trans (Nat.le_of_dvd hprod_pos (Finset.dvd_prod_of_mem d (Finset.mem_univ i))) hd.2.2

lemma mem_validSet_iff {k W R : ℕ} {d : Fin k → ℕ} :
    d ∈ validSet k W R ↔ Valid W R d := by
  classical
  unfold validSet
  simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc, and_iff_right_iff_imp]
  intro hd i
  exact ⟨valid_pos_at hd i, valid_le_R_at hd i⟩

lemma valid_squarefree_at {k W R : ℕ} {d : Fin k → ℕ} (hd : Valid W R d) (i : Fin k) :
    Squarefree (d i) :=
  hd.1.squarefree_of_dvd (Finset.dvd_prod_of_mem d (Finset.mem_univ i))

lemma valid_coprime_W_at {k W R : ℕ} {d : Fin k → ℕ} (hd : Valid W R d) (i : Fin k) :
    Nat.Coprime (d i) W :=
  hd.2.1.coprime_dvd_left (Finset.dvd_prod_of_mem d (Finset.mem_univ i))

lemma valid_pairwise_coprime {k W R : ℕ} {d : Fin k → ℕ} (hd : Valid W R d) :
    Pairwise (fun i j => Nat.Coprime (d i) (d j)) := by
  have h := pairwise_coprime_of_squarefree_prod hd.1
  intro i j hij
  exact h (Finset.mem_coe.mpr (Finset.mem_univ i)) (Finset.mem_coe.mpr (Finset.mem_univ j)) hij

lemma valid_of_dvd {k W R : ℕ} {d r : Fin k → ℕ} (hr : Valid W R r) (hdvd : ∀ i, d i ∣ r i) :
    Valid W R d := by
  have hprod_dvd : (∏ i : Fin k, d i) ∣ (∏ i : Fin k, r i) :=
    Finset.prod_dvd_prod_of_dvd _ _ (fun i _ => hdvd i)
  exact ⟨hr.1.squarefree_of_dvd hprod_dvd,
    hr.2.1.coprime_dvd_left hprod_dvd,
    le_trans (Nat.le_of_dvd (squarefree_pos hr.1) hprod_dvd) hr.2.2⟩

/-- Sieve weights lambdad obtained by Mobius inversion from yr. -/
noncomputable def lambdaOfY (k W R : ℕ) (y : (Fin k → ℕ) → ℝ) (d : Fin k → ℕ) : ℝ := by
  classical
  exact if Valid W R d then
    (∏ i : Fin k, (ArithmeticFunction.moebius (d i) : ℝ) * (d i : ℝ)) *
      ∑ r ∈ (validSet k W R).filter (fun r => ∀ i, d i ∣ r i),
        y r / (∏ i : Fin k, (Nat.totient (r i) : ℝ))
  else 0

/-- Exact Selberg diagonalization identity for sum{u | d} lambdad / prod d. -/
lemma sum_lambda_div_prod_eq {k W R : ℕ} (y : (Fin k → ℕ) → ℝ) {u : Fin k → ℕ}
    (hu : Valid W R u) :
    ∑ d ∈ (validSet k W R).filter (fun d => ∀ i, u i ∣ d i),
        lambdaOfY k W R y d / (∏ i : Fin k, (d i : ℝ)) =
      (∏ i : Fin k, (ArithmeticFunction.moebius (u i) : ℝ)) * y u /
        (∏ i : Fin k, (Nat.totient (u i) : ℝ)) := by
  classical
  have hrewrite :
      ∑ d ∈ (validSet k W R).filter (fun d => ∀ i, u i ∣ d i),
        lambdaOfY k W R y d / (∏ i : Fin k, (d i : ℝ)) =
      ∑ d ∈ (validSet k W R).filter (fun d => ∀ i, u i ∣ d i),
        ∑ r ∈ (validSet k W R).filter (fun r => ∀ i, d i ∣ r i),
          (∏ i : Fin k, (ArithmeticFunction.moebius (d i) : ℝ)) *
            (y r / (∏ i : Fin k, (Nat.totient (r i) : ℝ))) := by
    refine Finset.sum_congr rfl ?_
    intro d hd
    have hdV : Valid W R d := mem_validSet_iff.mp (Finset.mem_filter.mp hd).1
    unfold lambdaOfY
    rw [if_pos hdV, Finset.prod_mul_distrib]
    have hprod_ne : (∏ i : Fin k, (d i : ℝ)) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.mpr ?_
      intro i _
      exact (Nat.cast_pos.mpr (valid_pos_at hdV i)).ne'
    rw [Finset.mul_sum]
    field_simp
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => by ring
  rw [hrewrite]
  -- Swap sum over d and r
  have hswap :
      ∑ d ∈ (validSet k W R).filter (fun d => ∀ i, u i ∣ d i),
        ∑ r ∈ (validSet k W R).filter (fun r => ∀ i, d i ∣ r i),
          (∏ i : Fin k, (ArithmeticFunction.moebius (d i) : ℝ)) *
            (y r / (∏ i : Fin k, (Nat.totient (r i) : ℝ))) =
      ∑ r ∈ (validSet k W R).filter (fun r => ∀ i, u i ∣ r i),
        (y r / (∏ i : Fin k, (Nat.totient (r i) : ℝ))) *
          ∑ d ∈ (validSet k W R).filter (fun d => ∀ i, u i ∣ d i ∧ d i ∣ r i),
            (∏ i : Fin k, (ArithmeticFunction.moebius (d i) : ℝ)) := by
    trans (∑ d ∈ validSet k W R, ∑ r ∈ validSet k W R,
      if (∀ i, u i ∣ d i) ∧ (∀ i, d i ∣ r i) then
        (∏ i : Fin k, (ArithmeticFunction.moebius (d i) : ℝ)) *
          (y r / (∏ i : Fin k, (Nat.totient (r i) : ℝ)))
      else 0)
    · rw [Finset.sum_filter]
      refine Finset.sum_congr rfl ?_
      intro d _
      by_cases h1 : ∀ i, u i ∣ d i
      · rw [if_pos h1, Finset.sum_filter]
        refine Finset.sum_congr rfl ?_
        intro r _
        simp [h1]
      · rw [if_neg h1]
        symm
        refine Finset.sum_eq_zero ?_
        intro r _
        simp [h1]
    · rw [Finset.sum_comm, Finset.sum_filter]
      refine Finset.sum_congr rfl ?_
      intro r _
      by_cases h1 : ∀ i, u i ∣ r i
      · rw [if_pos h1, Finset.mul_sum, Finset.sum_filter]
        refine Finset.sum_congr rfl ?_
        intro d _
        by_cases h2 : ∀ i, u i ∣ d i ∧ d i ∣ r i
        · have h2' : (∀ i, u i ∣ d i) ∧ (∀ i, d i ∣ r i) :=
            ⟨fun i => (h2 i).1, fun i => (h2 i).2⟩
          rw [if_pos h2', if_pos h2, mul_comm]
        · have h2' : ¬ ((∀ i, u i ∣ d i) ∧ (∀ i, d i ∣ r i)) :=
            fun h => h2 (fun i => ⟨h.1 i, h.2 i⟩)
          rw [if_neg h2', if_neg h2]
      · rw [if_neg h1]
        refine Finset.sum_eq_zero ?_
        intro d _
        have hnot : ¬ ((∀ i, u i ∣ d i) ∧ (∀ i, d i ∣ r i)) := by
          rintro ⟨h2, h3⟩
          exact h1 (fun i => dvd_trans (h2 i) (h3 i))
        rw [if_neg hnot]
  rw [hswap]
  -- Evaluate the inner sum for each r with u | r
  have hinner : ∀ r ∈ (validSet k W R).filter (fun r => ∀ i, u i ∣ r i),
      ∑ d ∈ (validSet k W R).filter (fun d => ∀ i, u i ∣ d i ∧ d i ∣ r i),
        (∏ i : Fin k, (ArithmeticFunction.moebius (d i) : ℝ)) =
      if r = u then (∏ i : Fin k, (ArithmeticFunction.moebius (u i) : ℝ)) else 0 := by
    intro r hr
    have hrV : Valid W R r := mem_validSet_iff.mp (Finset.mem_filter.mp hr).1
    have hur : ∀ i, u i ∣ r i := (Finset.mem_filter.mp hr).2
    -- Any d with d | r is automatically in validSet k W R!
    have hset_eq : (validSet k W R).filter (fun d => ∀ i, u i ∣ d i ∧ d i ∣ r i) =
        Fintype.piFinset (fun i : Fin k => (r i).divisors.filter (fun x => u i ∣ x)) := by
      ext d
      simp only [Finset.mem_filter, mem_validSet_iff, Fintype.mem_piFinset, Nat.mem_divisors]
      constructor
      · rintro ⟨_, h⟩ i
        exact ⟨⟨(h i).2, (valid_pos_at hrV i).ne'⟩, (h i).1⟩
      · intro h
        refine ⟨valid_of_dvd hrV (fun i => (h i).1.1), fun i => ⟨(h i).2, (h i).1.1⟩⟩
    rw [hset_eq, sum_piFinset_prod (f := fun _ x => (ArithmeticFunction.moebius x : ℝ))]
    have hfac : ∀ i : Fin k,
        ∑ x ∈ (r i).divisors.filter (fun x => u i ∣ x), (ArithmeticFunction.moebius x : ℝ) =
        if r i = u i then (ArithmeticFunction.moebius (u i) : ℝ) else 0 := by
      intro i
      have hri_sq : Squarefree (r i) := valid_squarefree_at hrV i
      have hui_dvd : u i ∣ r i := hur i
      have hri_pos : 0 < r i := valid_pos_at hrV i
      have hui_pos : 0 < u i := valid_pos_at hu i
      have hq_pos : 0 < r i / u i := Nat.div_pos (Nat.le_of_dvd hri_pos hui_dvd) hui_pos
      have hbij : ∑ x ∈ (r i).divisors.filter (fun x => u i ∣ x), (ArithmeticFunction.moebius x : ℝ) =
          ∑ t ∈ (r i / u i).divisors, (ArithmeticFunction.moebius (u i * t) : ℝ) := by
        symm
        refine Finset.sum_bij (fun t _ => u i * t) ?_ ?_ ?_ ?_
        · intro t ht
          rw [Nat.mem_divisors] at ht
          rw [Finset.mem_filter, Nat.mem_divisors]
          refine ⟨⟨?_, hri_pos.ne'⟩, dvd_mul_right _ _⟩
          have := mul_dvd_mul_left (u i) ht.1
          rwa [Nat.mul_div_cancel' hui_dvd] at this
        · intro t₁ _ t₂ _ hEq
          exact Nat.eq_of_mul_eq_mul_left hui_pos hEq
        · intro x hx
          rw [Finset.mem_filter, Nat.mem_divisors] at hx
          rcases hx.2 with ⟨t, rfl⟩
          refine ⟨t, Nat.mem_divisors.mpr ⟨?_, hq_pos.ne'⟩, rfl⟩
          rcases hx.1.1 with ⟨c, hc⟩
          refine ⟨c, ?_⟩
          have h1 : u i * (r i / u i) = u i * (t * c) := by
            rw [Nat.mul_div_cancel' hui_dvd, hc]; ring
          exact Nat.eq_of_mul_eq_mul_left hui_pos h1
        · intro _ _; rfl
      rw [hbij]
      have hcop_all : ∀ t ∈ (r i / u i).divisors, Nat.Coprime (u i) t := by
        intro t ht
        have ht_dvd : t ∣ r i / u i := Nat.dvd_of_mem_divisors ht
        have hmul_dvd : u i * t ∣ r i := by
          have := mul_dvd_mul_left (u i) ht_dvd
          rwa [Nat.mul_div_cancel' hui_dvd] at this
        have hsq : Squarefree (u i * t) := hri_sq.squarefree_of_dvd hmul_dvd
        exact Nat.coprime_of_squarefree_mul hsq
      have hpull : ∑ t ∈ (r i / u i).divisors, (ArithmeticFunction.moebius (u i * t) : ℝ) =
          (ArithmeticFunction.moebius (u i) : ℝ) *
            ∑ t ∈ (r i / u i).divisors, (ArithmeticFunction.moebius t : ℝ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro t ht
        rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (hcop_all t ht)]
        push_cast
        rfl
      rw [hpull, sum_moebius_divisors_eq_ite]
      have hdiv_eq : r i / u i = 1 ↔ r i = u i := by
        constructor
        · intro h
          calc r i = u i * (r i / u i) := (Nat.mul_div_cancel' hui_dvd).symm
            _ = u i * 1 := by rw [h]
            _ = u i := mul_one _
        · intro h; rw [h, Nat.div_self hui_pos]
      by_cases hEq : r i = u i
      · rw [if_pos hEq, if_pos (hdiv_eq.mpr hEq), mul_one]
      · rw [if_neg hEq, if_neg (fun h => hEq (hdiv_eq.mp h)), mul_zero]
    simp_rw [hfac]
    by_cases hEq : r = u
    · subst hEq
      simp
    · rw [if_neg hEq]
      have hex : ∃ i : Fin k, r i ≠ u i := by
        by_contra hall
        push Not at hall
        exact hEq (funext hall)
      rcases hex with ⟨i, hi⟩
      exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
  rw [Finset.sum_congr rfl (fun r hr => by rw [hinner r hr])]
  rw [Finset.sum_eq_single u]
  · rw [if_pos rfl]; ring
  · intro r _ hne
    rw [if_neg hne, mul_zero]
  · intro hnot
    exact absurd (Finset.mem_filter.mpr ⟨mem_validSet_iff.mpr hu, fun i => dvd_refl (u i)⟩) hnot

/-- Modified sieve variable y^{(idx)}a for S2(idx). -/
noncomputable def yMod (k W R : ℕ) (y : (Fin k → ℕ) → ℝ) (idx : Fin k) (a : Fin k → ℕ) : ℝ := by
  classical
  exact if Valid W R a ∧ a idx = 1 then
    (∏ i ∈ Finset.univ.erase idx, (ArithmeticFunction.moebius (a i) : ℝ) * (phi2 (a i) : ℝ)) *
      ∑ d ∈ (validSet k W R).filter (fun d => d idx = 1 ∧ ∀ i, a i ∣ d i),
        lambdaOfY k W R y d / (∏ i ∈ Finset.univ.erase idx, (Nat.totient (d i) : ℝ))
  else 0

/-- Exact formula for y^{(idx)}a in terms of yr. -/
lemma yMod_eq_sum {k W R : ℕ} (y : (Fin k → ℕ) → ℝ) (idx : Fin k) {a : Fin k → ℕ}
    (ha : Valid W R a) (ha_idx : a idx = 1) :
    yMod k W R y idx a =
      (∏ i ∈ Finset.univ.erase idx,
        ((phi2 (a i) : ℝ) * (a i : ℝ) / (Nat.totient (a i) : ℝ) ^ 2)) *
      ∑ r ∈ (validSet k W R).filter (fun r => ∀ i ∈ Finset.univ.erase idx, a i ∣ r i),
        (∏ i ∈ Finset.univ.erase idx,
          (ArithmeticFunction.moebius (r i / a i) : ℝ) / (Nat.totient (r i / a i) : ℝ) ^ 2) *
        (y r / (Nat.totient (r idx) : ℝ)) := by
  classical
  unfold yMod
  rw [if_pos ⟨ha, ha_idx⟩]
  -- Expand lambdaOfY inside the sum over d
  have hstep1 :
      ∑ d ∈ (validSet k W R).filter (fun d => d idx = 1 ∧ ∀ i, a i ∣ d i),
        lambdaOfY k W R y d / (∏ i ∈ Finset.univ.erase idx, (Nat.totient (d i) : ℝ)) =
      ∑ d ∈ (validSet k W R).filter (fun d => d idx = 1 ∧ ∀ i, a i ∣ d i),
        ∑ r ∈ (validSet k W R).filter (fun r => ∀ i, d i ∣ r i),
          (∏ i ∈ Finset.univ.erase idx,
            (ArithmeticFunction.moebius (d i) : ℝ) * (d i : ℝ) / (Nat.totient (d i) : ℝ)) *
          (y r / (∏ i : Fin k, (Nat.totient (r i) : ℝ))) := by
    refine Finset.sum_congr rfl ?_
    intro d hd
    have hdV : Valid W R d := mem_validSet_iff.mp (Finset.mem_filter.mp hd).1
    have hd_idx : d idx = 1 := (Finset.mem_filter.mp hd).2.1
    unfold lambdaOfY
    rw [if_pos hdV, ← Finset.mul_prod_erase _ _ (Finset.mem_univ idx), hd_idx]
    simp only [ArithmeticFunction.moebius_apply_one, Int.cast_one, Nat.cast_one, mul_one, one_mul]
    rw [Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl ?_
    intro r _
    rw [Finset.prod_div_distrib]
    ring
  rw [hstep1]
  -- Swap sum over d and r
  have hswap :
      ∑ d ∈ (validSet k W R).filter (fun d => d idx = 1 ∧ ∀ i, a i ∣ d i),
        ∑ r ∈ (validSet k W R).filter (fun r => ∀ i, d i ∣ r i),
          (∏ i ∈ Finset.univ.erase idx,
            (ArithmeticFunction.moebius (d i) : ℝ) * (d i : ℝ) / (Nat.totient (d i) : ℝ)) *
          (y r / (∏ i : Fin k, (Nat.totient (r i) : ℝ))) =
      ∑ r ∈ (validSet k W R).filter (fun r => ∀ i ∈ Finset.univ.erase idx, a i ∣ r i),
        (y r / (∏ i : Fin k, (Nat.totient (r i) : ℝ))) *
          ∑ d ∈ (validSet k W R).filter (fun d => d idx = 1 ∧ ∀ i ∈ Finset.univ.erase idx, a i ∣ d i ∧ d i ∣ r i),
            ∏ i ∈ Finset.univ.erase idx,
              (ArithmeticFunction.moebius (d i) : ℝ) * (d i : ℝ) / (Nat.totient (d i) : ℝ) := by
    trans (∑ d ∈ validSet k W R, ∑ r ∈ validSet k W R,
      if (d idx = 1 ∧ ∀ i, a i ∣ d i) ∧ (∀ i, d i ∣ r i) then
        (∏ i ∈ Finset.univ.erase idx,
          (ArithmeticFunction.moebius (d i) : ℝ) * (d i : ℝ) / (Nat.totient (d i) : ℝ)) *
        (y r / (∏ i : Fin k, (Nat.totient (r i) : ℝ)))
      else 0)
    · rw [Finset.sum_filter]
      refine Finset.sum_congr rfl ?_
      intro d _
      by_cases h1 : d idx = 1 ∧ ∀ i, a i ∣ d i
      · rw [if_pos h1, Finset.sum_filter]
        refine Finset.sum_congr rfl ?_
        intro r _
        simp [h1]
      · rw [if_neg h1]
        symm
        refine Finset.sum_eq_zero ?_
        intro r _
        simp [h1]
    · rw [Finset.sum_comm, Finset.sum_filter]
      refine Finset.sum_congr rfl ?_
      intro r _
      by_cases h1 : ∀ i ∈ Finset.univ.erase idx, a i ∣ r i
      · rw [if_pos h1, Finset.mul_sum, Finset.sum_filter]
        refine Finset.sum_congr rfl ?_
        intro d _
        have hcond : ((d idx = 1 ∧ ∀ i, a i ∣ d i) ∧ (∀ i, d i ∣ r i)) ↔
            (d idx = 1 ∧ ∀ i ∈ Finset.univ.erase idx, a i ∣ d i ∧ d i ∣ r i) := by
          constructor
          · rintro ⟨⟨hdi, had⟩, hdr⟩
            exact ⟨hdi, fun i _ => ⟨had i, hdr i⟩⟩
          · rintro ⟨hdi, hall⟩
            refine ⟨⟨hdi, ?_⟩, ?_⟩
            · intro i
              by_cases hi : i = idx
              · subst hi; rw [ha_idx, hdi]
              · exact (hall i (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩)).1
            · intro i
              by_cases hi : i = idx
              · subst hi; rw [hdi]; exact one_dvd _
              · exact (hall i (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩)).2
        by_cases h2 : d idx = 1 ∧ ∀ i ∈ Finset.univ.erase idx, a i ∣ d i ∧ d i ∣ r i
        · rw [if_pos (hcond.mpr h2), if_pos h2, mul_comm]
        · rw [if_neg (fun h => h2 (hcond.mp h)), if_neg h2]
      · rw [if_neg h1]
        refine Finset.sum_eq_zero ?_
        intro d _
        have hnot : ¬ ((d idx = 1 ∧ ∀ i, a i ∣ d i) ∧ (∀ i, d i ∣ r i)) := by
          rintro ⟨⟨_, had⟩, hdr⟩
          exact h1 (fun i _ => dvd_trans (had i) (hdr i))
        rw [if_neg hnot]
  rw [hswap]
  -- Evaluate inner sum over d for each r
  have hinner : ∀ r ∈ (validSet k W R).filter (fun r => ∀ i ∈ Finset.univ.erase idx, a i ∣ r i),
      ∑ d ∈ (validSet k W R).filter (fun d => d idx = 1 ∧ ∀ i ∈ Finset.univ.erase idx, a i ∣ d i ∧ d i ∣ r i),
        ∏ i ∈ Finset.univ.erase idx,
          (ArithmeticFunction.moebius (d i) : ℝ) * (d i : ℝ) / (Nat.totient (d i) : ℝ) =
      ∏ i ∈ Finset.univ.erase idx,
        ((ArithmeticFunction.moebius (a i) : ℝ) * (a i : ℝ) / (Nat.totient (a i) : ℝ) *
          ((ArithmeticFunction.moebius (r i / a i) : ℝ) / (Nat.totient (r i / a i) : ℝ))) := by
    intro r hr
    have hrV : Valid W R r := mem_validSet_iff.mp (Finset.mem_filter.mp hr).1
    have har : ∀ i ∈ Finset.univ.erase idx, a i ∣ r i := (Finset.mem_filter.mp hr).2
    let dom : Fin k → Finset ℕ := fun i =>
      if i = idx then {1} else (r i).divisors.filter (fun x => a i ∣ x)
    have hset_eq :
        (validSet k W R).filter (fun d => d idx = 1 ∧ ∀ i ∈ Finset.univ.erase idx, a i ∣ d i ∧ d i ∣ r i) =
        Fintype.piFinset dom := by
      ext d
      simp only [Finset.mem_filter, mem_validSet_iff, Fintype.mem_piFinset, dom]
      constructor
      · rintro ⟨_, hdi, hall⟩ i
        by_cases hi : i = idx
        · subst hi; simp [hdi]
        · rw [if_neg hi, Finset.mem_filter, Nat.mem_divisors]
          have h := hall i (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩)
          exact ⟨⟨h.2, (valid_pos_at hrV i).ne'⟩, h.1⟩
      · intro h
        have hdi : d idx = 1 := by
          have := h idx
          simpa using this
        have hall : ∀ i ∈ Finset.univ.erase idx, a i ∣ d i ∧ d i ∣ r i := by
          intro i hi
          have hne : i ≠ idx := (Finset.mem_erase.mp hi).1
          have := h i
          rw [if_neg hne, Finset.mem_filter, Nat.mem_divisors] at this
          exact ⟨this.2, this.1.1⟩
        have hdvd : ∀ i, d i ∣ r i := by
          intro i
          by_cases hi : i = idx
          · subst hi; rw [hdi]; exact one_dvd _
          · exact (hall i (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩)).2
        exact ⟨valid_of_dvd hrV hdvd, hdi, hall⟩
    rw [hset_eq]
    -- Factor sum over Fintype.piFinset dom into product over Fin k
    have hfactor :
        ∑ d ∈ Fintype.piFinset dom,
          ∏ i ∈ Finset.univ.erase idx,
            (ArithmeticFunction.moebius (d i) : ℝ) * (d i : ℝ) / (Nat.totient (d i) : ℝ) =
        ∏ i : Fin k, ∑ x ∈ dom i,
          if i = idx then (1 : ℝ) else
            (ArithmeticFunction.moebius x : ℝ) * (x : ℝ) / (Nat.totient x : ℝ) := by
      rw [← sum_piFinset_prod]
      refine Finset.sum_congr rfl ?_
      intro d _
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ idx), if_pos rfl, one_mul]
      refine Finset.prod_congr rfl ?_
      intro i hi
      rw [if_neg (Finset.mem_erase.mp hi).1]
    rw [hfactor, ← Finset.mul_prod_erase _ _ (Finset.mem_univ idx)]
    have hidx_val : ∑ x ∈ dom idx,
        (if idx = idx then (1 : ℝ) else
          (ArithmeticFunction.moebius x : ℝ) * (x : ℝ) / (Nat.totient x : ℝ)) = 1 := by
      simp [dom]
    rw [hidx_val, one_mul]
    refine Finset.prod_congr rfl ?_
    intro i hi
    have hne : i ≠ idx := (Finset.mem_erase.mp hi).1
    simp only [dom, if_neg hne]
    have hri_sq : Squarefree (r i) := valid_squarefree_at hrV i
    have hai_dvd : a i ∣ r i := har i hi
    have hri_pos : 0 < r i := valid_pos_at hrV i
    have hai_pos : 0 < a i := valid_pos_at ha i
    have hq_pos : 0 < r i / a i := Nat.div_pos (Nat.le_of_dvd hri_pos hai_dvd) hai_pos
    have hq_sq : Squarefree (r i / a i) := hri_sq.squarefree_of_dvd (Nat.div_dvd_of_dvd hai_dvd)
    have hbij :
        ∑ x ∈ (r i).divisors.filter (fun x => a i ∣ x),
          (ArithmeticFunction.moebius x : ℝ) * (x : ℝ) / (Nat.totient x : ℝ) =
        ∑ t ∈ (r i / a i).divisors,
          (ArithmeticFunction.moebius (a i * t) : ℝ) * ((a i * t : ℕ) : ℝ) /
            (Nat.totient (a i * t) : ℝ) := by
      symm
      refine Finset.sum_bij (fun t _ => a i * t) ?_ ?_ ?_ ?_
      · intro t ht
        rw [Nat.mem_divisors] at ht
        rw [Finset.mem_filter, Nat.mem_divisors]
        refine ⟨⟨?_, hri_pos.ne'⟩, dvd_mul_right _ _⟩
        have := mul_dvd_mul_left (a i) ht.1
        rwa [Nat.mul_div_cancel' hai_dvd] at this
      · intro t₁ _ t₂ _ hEq
        exact Nat.eq_of_mul_eq_mul_left hai_pos hEq
      · intro x hx
        rw [Finset.mem_filter, Nat.mem_divisors] at hx
        rcases hx.2 with ⟨t, rfl⟩
        refine ⟨t, Nat.mem_divisors.mpr ⟨?_, hq_pos.ne'⟩, rfl⟩
        rcases hx.1.1 with ⟨c, hc⟩
        refine ⟨c, ?_⟩
        have h1 : a i * (r i / a i) = a i * (t * c) := by
          rw [Nat.mul_div_cancel' hai_dvd, hc]; ring
        exact Nat.eq_of_mul_eq_mul_left hai_pos h1
      · intro _ _; rfl
    rw [hbij]
    have hcop_all : ∀ t ∈ (r i / a i).divisors, Nat.Coprime (a i) t := by
      intro t ht
      have hmul_dvd : a i * t ∣ r i := by
        have := mul_dvd_mul_left (a i) (Nat.dvd_of_mem_divisors ht)
        rwa [Nat.mul_div_cancel' hai_dvd] at this
      exact Nat.coprime_of_squarefree_mul (hri_sq.squarefree_of_dvd hmul_dvd)
    have hpull :
        ∑ t ∈ (r i / a i).divisors,
          (ArithmeticFunction.moebius (a i * t) : ℝ) * ((a i * t : ℕ) : ℝ) /
            (Nat.totient (a i * t) : ℝ) =
        ((ArithmeticFunction.moebius (a i) : ℝ) * (a i : ℝ) / (Nat.totient (a i) : ℝ)) *
          ∑ t ∈ (r i / a i).divisors,
            (ArithmeticFunction.moebius t : ℝ) * (t : ℝ) / (Nat.totient t : ℝ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro t ht
      have hc := hcop_all t ht
      rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hc, Nat.totient_mul hc]
      push_cast
      ring
    rw [hpull, sum_moebius_mul_div_totient_eq hq_sq]
  -- Combine all factors and simplify
  rw [Finset.sum_congr rfl (fun r hr => by rw [hinner r hr])]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro r hr
  have hrV : Valid W R r := mem_validSet_iff.mp (Finset.mem_filter.mp hr).1
  have har : ∀ i ∈ Finset.univ.erase idx, a i ∣ r i := (Finset.mem_filter.mp hr).2
  have hphi_split : (∏ i : Fin k, (Nat.totient (r i) : ℝ)) =
      (Nat.totient (r idx) : ℝ) *
      (∏ i ∈ Finset.univ.erase idx, (Nat.totient (a i) : ℝ)) *
      (∏ i ∈ Finset.univ.erase idx, (Nat.totient (r i / a i) : ℝ)) := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ idx), mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl ?_
    intro i hi
    have hri_sq : Squarefree (r i) := valid_squarefree_at hrV i
    have hai_dvd : a i ∣ r i := har i hi
    have hmul : a i * (r i / a i) = r i := Nat.mul_div_cancel' hai_dvd
    have hc : Nat.Coprime (a i) (r i / a i) :=
      Nat.coprime_of_squarefree_mul (hmul.symm ▸ hri_sq)
    have htot : Nat.totient (r i) = Nat.totient (a i) * Nat.totient (r i / a i) := by
      conv_lhs => rw [← hmul]
      exact Nat.totient_mul hc
    exact_mod_cast htot
  rw [hphi_split]
  have hmob_sq : ∀ i ∈ Finset.univ.erase idx, (ArithmeticFunction.moebius (a i) : ℝ) ^ 2 = 1 :=
    fun i _ => moebius_sq_eq_one_of_squarefree (valid_squarefree_at ha i)
  have hcombine :
      (∏ i ∈ Finset.univ.erase idx, (ArithmeticFunction.moebius (a i) : ℝ) * (phi2 (a i) : ℝ)) *
      (∏ i ∈ Finset.univ.erase idx,
        ((ArithmeticFunction.moebius (a i) : ℝ) * (a i : ℝ) / (Nat.totient (a i) : ℝ) *
          ((ArithmeticFunction.moebius (r i / a i) : ℝ) / (Nat.totient (r i / a i) : ℝ)))) /
      ((∏ i ∈ Finset.univ.erase idx, (Nat.totient (a i) : ℝ)) *
        (∏ i ∈ Finset.univ.erase idx, (Nat.totient (r i / a i) : ℝ))) =
      (∏ i ∈ Finset.univ.erase idx,
        ((phi2 (a i) : ℝ) * (a i : ℝ) / (Nat.totient (a i) : ℝ) ^ 2)) *
      (∏ i ∈ Finset.univ.erase idx,
        ((ArithmeticFunction.moebius (r i / a i) : ℝ) / (Nat.totient (r i / a i) : ℝ) ^ 2)) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_div_distrib,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl ?_
    intro i hi
    have hms := hmob_sq i hi
    have h1 : (ArithmeticFunction.moebius (a i) : ℝ) * (ArithmeticFunction.moebius (a i) : ℝ) = 1 := by
      linarith [sq (ArithmeticFunction.moebius (a i) : ℝ)]
    have hphi_a_ne : (Nat.totient (a i) : ℝ) ≠ 0 :=
      (Nat.cast_pos.mpr (Nat.totient_pos.mpr (valid_pos_at ha i))).ne'
    have hq_pos : 0 < r i / a i :=
      Nat.div_pos (Nat.le_of_dvd (valid_pos_at hrV i) (har i hi)) (valid_pos_at ha i)
    have hphi_q_ne : (Nat.totient (r i / a i) : ℝ) ≠ 0 :=
      (Nat.cast_pos.mpr (Nat.totient_pos.mpr hq_pos)).ne'
    field_simp
    linear_combination (phi2 (a i) : ℝ) * (a i : ℝ) * (ArithmeticFunction.moebius (r i / a i) : ℝ) * h1
  calc (∏ i ∈ Finset.univ.erase idx, (ArithmeticFunction.moebius (a i) : ℝ) * (phi2 (a i) : ℝ)) *
        (y r / ((Nat.totient (r idx) : ℝ) *
          (∏ i ∈ Finset.univ.erase idx, (Nat.totient (a i) : ℝ)) *
          (∏ i ∈ Finset.univ.erase idx, (Nat.totient (r i / a i) : ℝ))) *
        ∏ i ∈ Finset.univ.erase idx,
          ((ArithmeticFunction.moebius (a i) : ℝ) * (a i : ℝ) / (Nat.totient (a i) : ℝ) *
            ((ArithmeticFunction.moebius (r i / a i) : ℝ) / (Nat.totient (r i / a i) : ℝ))))
      = ((∏ i ∈ Finset.univ.erase idx, (ArithmeticFunction.moebius (a i) : ℝ) * (phi2 (a i) : ℝ)) *
          (∏ i ∈ Finset.univ.erase idx,
            ((ArithmeticFunction.moebius (a i) : ℝ) * (a i : ℝ) / (Nat.totient (a i) : ℝ) *
              ((ArithmeticFunction.moebius (r i / a i) : ℝ) / (Nat.totient (r i / a i) : ℝ)))) /
          ((∏ i ∈ Finset.univ.erase idx, (Nat.totient (a i) : ℝ)) *
            (∏ i ∈ Finset.univ.erase idx, (Nat.totient (r i / a i) : ℝ)))) *
        (y r / (Nat.totient (r idx) : ℝ)) := by ring
    _ = ((∏ i ∈ Finset.univ.erase idx,
            ((phi2 (a i) : ℝ) * (a i : ℝ) / (Nat.totient (a i) : ℝ) ^ 2)) *
          (∏ i ∈ Finset.univ.erase idx,
            ((ArithmeticFunction.moebius (r i / a i) : ℝ) / (Nat.totient (r i / a i) : ℝ) ^ 2))) *
        (y r / (Nat.totient (r idx) : ℝ)) := by rw [hcombine]
    _ = _ := by ring

/-- Valid k by k matrix for Selberg diagonalization. -/
def ValidMat {k : ℕ} (W R : ℕ) (m : Fin k × Fin k → ℕ) : Prop :=
  Squarefree (∏ p : Fin k × Fin k, m p) ∧ Nat.Coprime (∏ p : Fin k × Fin k, m p) W ∧
    ∏ p : Fin k × Fin k, m p ≤ R

noncomputable def validMatSet (k W R : ℕ) : Finset (Fin k × Fin k → ℕ) := by
  classical
  exact (Fintype.piFinset (fun _ : Fin k × Fin k => Finset.Icc 1 R)).filter (ValidMat W R)

def rowProd {k : ℕ} (m : Fin k × Fin k → ℕ) (i : Fin k) : ℕ :=
  ∏ j : Fin k, m (i, j)

def colProd {k : ℕ} (m : Fin k × Fin k → ℕ) (j : Fin k) : ℕ :=
  ∏ i : Fin k, m (i, j)

lemma prod_rowProd_eq {k : ℕ} (m : Fin k × Fin k → ℕ) :
    ∏ i : Fin k, rowProd m i = ∏ p : Fin k × Fin k, m p := by
  unfold rowProd
  rw [Fintype.prod_prod_type]

lemma prod_colProd_eq {k : ℕ} (m : Fin k × Fin k → ℕ) :
    ∏ j : Fin k, colProd m j = ∏ p : Fin k × Fin k, m p := by
  unfold colProd
  rw [Fintype.prod_prod_type_right]

lemma validMat_rowProd_valid {k W R : ℕ} {m : Fin k × Fin k → ℕ} (hm : ValidMat W R m) :
    Valid W R (rowProd m) := by
  unfold Valid
  rw [prod_rowProd_eq]
  exact hm

lemma validMat_colProd_valid {k W R : ℕ} {m : Fin k × Fin k → ℕ} (hm : ValidMat W R m) :
    Valid W R (colProd m) := by
  unfold Valid
  rw [prod_colProd_eq]
  exact hm

lemma mem_validMatSet_iff {k W R : ℕ} {m : Fin k × Fin k → ℕ} :
    m ∈ validMatSet k W R ↔ ValidMat W R m := by
  classical
  unfold validMatSet
  simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc, and_iff_right_iff_imp]
  intro hm p
  have hprod_pos : 0 < ∏ q : Fin k × Fin k, m q := squarefree_pos hm.1
  have hp_pos : 0 < m p := by
    by_contra h0
    push Not at h0
    have : m p = 0 := by omega
    have : ∏ q : Fin k × Fin k, m q = 0 := Finset.prod_eq_zero (Finset.mem_univ p) this
    omega
  exact ⟨hp_pos, le_trans (Nat.le_of_dvd hprod_pos (Finset.dvd_prod_of_mem m (Finset.mem_univ p))) hm.2.2⟩

lemma nat_prod_dvd_of_coprime {ι : Type*} [DecidableEq ι] {s : Finset ι} {f : ι → ℕ} {n : ℕ}
    (hcop : (s : Set ι).Pairwise (fun i j => Nat.Coprime (f i) (f j)))
    (hdvd : ∀ i ∈ s, f i ∣ n) :
    (∏ i ∈ s, f i) ∣ n := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have hca : Nat.Coprime (f a) (∏ i ∈ s, f i) := by
      refine Nat.Coprime.prod_right ?_
      intro i hi
      exact hcop (Finset.mem_insert_self a s) (Finset.mem_insert_of_mem hi) (fun h => ha (h ▸ hi))
    exact hca.mul_dvd_of_dvd_of_dvd (hdvd a (Finset.mem_insert_self a s))
      (ih (hcop.mono (Finset.subset_insert a s)) (fun i hi => hdvd i (Finset.mem_insert_of_mem hi)))

/-- Key divisibility equivalence between matrix entries and row/column products for valid d, e. -/
lemma mat_dvd_iff_row_col_dvd {k W R : ℕ} {d e : Fin k → ℕ} (hd : Valid W R d) (he : Valid W R e)
    (m : Fin k × Fin k → ℕ) :
    (∀ p : Fin k × Fin k, m p ∣ Nat.gcd (d p.1) (e p.2)) ↔
      (ValidMat W R m ∧ (∀ i, rowProd m i ∣ d i) ∧ (∀ j, colProd m j ∣ e j)) := by
  constructor
  · intro hm
    have hrow_dvd : ∀ i, rowProd m i ∣ d i := by
      intro i
      unfold rowProd
      have hcop : ((Finset.univ : Finset (Fin k)) : Set (Fin k)).Pairwise
          (fun j₁ j₂ => Nat.Coprime (m (i, j₁)) (m (i, j₂))) := by
        intro j₁ _ j₂ _ hne
        have h1 : m (i, j₁) ∣ e j₁ := dvd_trans (hm (i, j₁)) (Nat.gcd_dvd_right _ _)
        have h2 : m (i, j₂) ∣ e j₂ := dvd_trans (hm (i, j₂)) (Nat.gcd_dvd_right _ _)
        exact (valid_pairwise_coprime he hne).coprime_dvd_left h1 |>.coprime_dvd_right h2
      exact nat_prod_dvd_of_coprime hcop (fun j _ => dvd_trans (hm (i, j)) (Nat.gcd_dvd_left _ _))
    have hcol_dvd : ∀ j, colProd m j ∣ e j := by
      intro j
      unfold colProd
      have hcop : ((Finset.univ : Finset (Fin k)) : Set (Fin k)).Pairwise
          (fun i₁ i₂ => Nat.Coprime (m (i₁, j)) (m (i₂, j))) := by
        intro i₁ _ i₂ _ hne
        have h1 : m (i₁, j) ∣ d i₁ := dvd_trans (hm (i₁, j)) (Nat.gcd_dvd_left _ _)
        have h2 : m (i₂, j) ∣ d i₂ := dvd_trans (hm (i₂, j)) (Nat.gcd_dvd_left _ _)
        exact (valid_pairwise_coprime hd hne).coprime_dvd_left h1 |>.coprime_dvd_right h2
      exact nat_prod_dvd_of_coprime hcop (fun i _ => dvd_trans (hm (i, j)) (Nat.gcd_dvd_right _ _))
    have hvalid_row : Valid W R (rowProd m) := valid_of_dvd hd hrow_dvd
    have hvalid_mat : ValidMat W R m := by
      unfold ValidMat
      rw [← prod_rowProd_eq]
      exact hvalid_row
    exact ⟨hvalid_mat, hrow_dvd, hcol_dvd⟩
  · rintro ⟨_, hrow, hcol⟩ ⟨i, j⟩
    refine Nat.dvd_gcd ?_ ?_
    · exact dvd_trans (Finset.dvd_prod_of_mem (fun j' => m (i, j')) (Finset.mem_univ j)) (hrow i)
    · exact dvd_trans (Finset.dvd_prod_of_mem (fun i' => m (i', j)) (Finset.mem_univ i)) (hcol j)

/-- Exact matrix identity for M_1. -/
lemma M1_eq_matrix_sum {k W R : ℕ} (y : (Fin k → ℕ) → ℝ) :
    ∑ d ∈ validSet k W R,
      ∑ e ∈ (validSet k W R).filter (fun e => ∀ i j : Fin k, i ≠ j → Nat.Coprime (d i) (e j)),
        (lambdaOfY k W R y d * lambdaOfY k W R y e) / (∏ i : Fin k, (Nat.lcm (d i) (e i) : ℝ)) =
    ∑ m ∈ validMatSet k W R,
      (∏ p : Fin k × Fin k,
        if p.1 = p.2 then 1 / (Nat.totient (m p) : ℝ)
        else (ArithmeticFunction.moebius (m p) : ℝ) / (Nat.totient (m p) : ℝ) ^ 2) *
      y (rowProd m) * y (colProd m) := by
  classical
  -- Rewrite LHS as sum over all d, e in validSet with indicator expanded via matrix m
  have hstep1 :
      ∑ d ∈ validSet k W R,
        ∑ e ∈ (validSet k W R).filter (fun e => ∀ i j : Fin k, i ≠ j → Nat.Coprime (d i) (e j)),
          (lambdaOfY k W R y d * lambdaOfY k W R y e) / (∏ i : Fin k, (Nat.lcm (d i) (e i) : ℝ)) =
      ∑ d ∈ validSet k W R, ∑ e ∈ validSet k W R,
        (lambdaOfY k W R y d / (∏ i : Fin k, (d i : ℝ))) *
        (lambdaOfY k W R y e / (∏ j : Fin k, (e j : ℝ))) *
        ∑ m ∈ (validMatSet k W R).filter (fun m => (∀ i, rowProd m i ∣ d i) ∧ (∀ j, colProd m j ∣ e j)),
          ∏ p : Fin k × Fin k,
            if p.1 = p.2 then (Nat.totient (m p) : ℝ) else (ArithmeticFunction.moebius (m p) : ℝ) := by
    refine Finset.sum_congr rfl ?_
    intro d hd
    have hdV : Valid W R d := mem_validSet_iff.mp hd
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro e he
    have heV : Valid W R e := mem_validSet_iff.mp he
    -- Express the matrix sum as product over p : Fin k x Fin k
    have hmat_set :
        (validMatSet k W R).filter (fun m => (∀ i, rowProd m i ∣ d i) ∧ (∀ j, colProd m j ∣ e j)) =
        Fintype.piFinset (fun p : Fin k × Fin k => (Nat.gcd (d p.1) (e p.2)).divisors) := by
      ext m
      simp only [Finset.mem_filter, mem_validMatSet_iff, Fintype.mem_piFinset, Nat.mem_divisors]
      have hgcd_ne : ∀ p : Fin k × Fin k, Nat.gcd (d p.1) (e p.2) ≠ 0 :=
        fun p => (Nat.gcd_pos_of_pos_left (e p.2) (valid_pos_at hdV p.1)).ne'
      simp only [hgcd_ne, ne_eq, not_false_eq_true, and_true]
      exact (mat_dvd_iff_row_col_dvd hdV heV m).symm
    rw [hmat_set, sum_piFinset_prod (f := fun (p : Fin k × Fin k) x =>
      if p.1 = p.2 then (Nat.totient x : ℝ) else (ArithmeticFunction.moebius x : ℝ))]
    have hprod_eval :
        ∏ p : Fin k × Fin k, ∑ x ∈ (Nat.gcd (d p.1) (e p.2)).divisors,
          (if p.1 = p.2 then (Nat.totient x : ℝ) else (ArithmeticFunction.moebius x : ℝ)) =
        (∏ i : Fin k, (Nat.gcd (d i) (e i) : ℝ)) *
          (if ∀ i j : Fin k, i ≠ j → Nat.Coprime (d i) (e j) then (1 : ℝ) else 0) := by
      have h1 : ∀ p : Fin k × Fin k,
          ∑ x ∈ (Nat.gcd (d p.1) (e p.2)).divisors,
            (if p.1 = p.2 then (Nat.totient x : ℝ) else (ArithmeticFunction.moebius x : ℝ)) =
          if p.1 = p.2 then (Nat.gcd (d p.1) (e p.2) : ℝ)
          else if Nat.Coprime (d p.1) (e p.2) then 1 else 0 := by
        intro p
        by_cases hp : p.1 = p.2
        · rw [if_pos hp]
          simp only [if_pos hp]
          exact_mod_cast Nat.sum_totient (Nat.gcd (d p.1) (e p.2))
        · rw [if_neg hp]
          simp only [if_neg hp, sum_moebius_divisors_eq_ite]
      simp_rw [h1]
      by_cases hcop : ∀ i j : Fin k, i ≠ j → Nat.Coprime (d i) (e j)
      · rw [if_pos hcop, mul_one, Fintype.prod_prod_type]
        refine Finset.prod_congr rfl ?_
        intro i _
        rw [Finset.prod_eq_single i]
        · simp
        · intro j _ hji
          rw [if_neg (Ne.symm hji), if_pos (hcop i j (Ne.symm hji))]
        · intro hnot; exact absurd (Finset.mem_univ i) hnot
      · rw [if_neg hcop, mul_zero]
        push Not at hcop
        rcases hcop with ⟨i, j, hij, hncop⟩
        refine Finset.prod_eq_zero (Finset.mem_univ (i, j)) ?_
        rw [if_neg hij, if_neg hncop]
    rw [hprod_eval]
    by_cases hcop : ∀ i j : Fin k, i ≠ j → Nat.Coprime (d i) (e j)
    · rw [if_pos hcop, if_pos hcop, mul_one]
      have hlcm_eq : (∏ i : Fin k, (Nat.lcm (d i) (e i) : ℝ)) * (∏ i : Fin k, (Nat.gcd (d i) (e i) : ℝ)) =
          (∏ i : Fin k, (d i : ℝ)) * (∏ j : Fin k, (e j : ℝ)) := by
        rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl ?_
        intro i _
        exact_mod_cast Nat.lcm_mul_gcd (d i) (e i)
      have hd_ne : (∏ i : Fin k, (d i : ℝ)) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr (fun i _ => (Nat.cast_pos.mpr (valid_pos_at hdV i)).ne')
      have he_ne : (∏ j : Fin k, (e j : ℝ)) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr (fun j _ => (Nat.cast_pos.mpr (valid_pos_at heV j)).ne')
      have hlcm_ne : (∏ i : Fin k, (Nat.lcm (d i) (e i) : ℝ)) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr (fun i _ =>
          (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Nat.lcm_ne_zero (valid_pos_at hdV i).ne' (valid_pos_at heV i).ne'))).ne')
      rw [div_mul_div_comm, div_mul_eq_mul_div, div_eq_div_iff hlcm_ne (mul_ne_zero hd_ne he_ne)]
      linear_combination (lambdaOfY k W R y d * lambdaOfY k W R y e) * hlcm_eq.symm
    · rw [if_neg hcop, if_neg hcop, mul_zero, mul_zero]
  rw [hstep1]
  -- Swap sum over (d, e) and m
  have hswap :
      ∑ d ∈ validSet k W R, ∑ e ∈ validSet k W R,
        (lambdaOfY k W R y d / (∏ i : Fin k, (d i : ℝ))) *
        (lambdaOfY k W R y e / (∏ j : Fin k, (e j : ℝ))) *
        ∑ m ∈ (validMatSet k W R).filter (fun m => (∀ i, rowProd m i ∣ d i) ∧ (∀ j, colProd m j ∣ e j)),
          (∏ p : Fin k × Fin k,
            if p.1 = p.2 then (Nat.totient (m p) : ℝ) else (ArithmeticFunction.moebius (m p) : ℝ)) =
      ∑ m ∈ validMatSet k W R,
        (∏ p : Fin k × Fin k,
          if p.1 = p.2 then (Nat.totient (m p) : ℝ) else (ArithmeticFunction.moebius (m p) : ℝ)) *
        (∑ d ∈ (validSet k W R).filter (fun d => ∀ i, rowProd m i ∣ d i),
          lambdaOfY k W R y d / (∏ i : Fin k, (d i : ℝ))) *
        (∑ e ∈ (validSet k W R).filter (fun e => ∀ j, colProd m j ∣ e j),
          lambdaOfY k W R y e / (∏ j : Fin k, (e j : ℝ))) := by
    trans (∑ d ∈ validSet k W R, ∑ e ∈ validSet k W R, ∑ m ∈ validMatSet k W R,
      if (∀ i, rowProd m i ∣ d i) ∧ (∀ j, colProd m j ∣ e j) then
        (∏ p : Fin k × Fin k,
          if p.1 = p.2 then (Nat.totient (m p) : ℝ) else (ArithmeticFunction.moebius (m p) : ℝ)) *
        (lambdaOfY k W R y d / (∏ i : Fin k, (d i : ℝ))) *
        (lambdaOfY k W R y e / (∏ j : Fin k, (e j : ℝ)))
      else 0)
    · refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun e _ => ?_
      rw [Finset.mul_sum, Finset.sum_filter]
      refine Finset.sum_congr rfl fun m _ => ?_
      split_ifs <;> ring
    · calc ∑ d ∈ validSet k W R, ∑ e ∈ validSet k W R, ∑ m ∈ validMatSet k W R, _
          = ∑ d ∈ validSet k W R, ∑ m ∈ validMatSet k W R, ∑ e ∈ validSet k W R, _ :=
            Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
        _ = ∑ m ∈ validMatSet k W R, ∑ d ∈ validSet k W R, ∑ e ∈ validSet k W R, _ :=
            Finset.sum_comm
        _ = _ := by
            refine Finset.sum_congr rfl fun m _ => ?_
            have hrhs :
                (∏ p : Fin k × Fin k,
                  if p.1 = p.2 then (Nat.totient (m p) : ℝ) else (ArithmeticFunction.moebius (m p) : ℝ)) *
                (∑ d ∈ (validSet k W R).filter (fun d => ∀ i, rowProd m i ∣ d i),
                  lambdaOfY k W R y d / (∏ i : Fin k, (d i : ℝ))) *
                (∑ e ∈ (validSet k W R).filter (fun e => ∀ j, colProd m j ∣ e j),
                  lambdaOfY k W R y e / (∏ j : Fin k, (e j : ℝ))) =
                ∑ d ∈ (validSet k W R).filter (fun d => ∀ i, rowProd m i ∣ d i),
                  ∑ e ∈ (validSet k W R).filter (fun e => ∀ j, colProd m j ∣ e j),
                    (∏ p : Fin k × Fin k,
                      if p.1 = p.2 then (Nat.totient (m p) : ℝ) else (ArithmeticFunction.moebius (m p) : ℝ)) *
                    (lambdaOfY k W R y d / (∏ i : Fin k, (d i : ℝ))) *
                    (lambdaOfY k W R y e / (∏ j : Fin k, (e j : ℝ))) := by
              rw [Finset.mul_sum (s := (validSet k W R).filter (fun d => ∀ i, rowProd m i ∣ d i)),
                Finset.sum_mul]
              refine Finset.sum_congr rfl fun d _ => ?_
              rw [Finset.mul_sum]
            rw [hrhs]
            conv_rhs => rw [Finset.sum_filter]
            refine Finset.sum_congr rfl fun d _ => ?_
            by_cases h1 : ∀ i, rowProd m i ∣ d i
            · rw [if_pos h1]
              conv_rhs => rw [Finset.sum_filter]
              refine Finset.sum_congr rfl fun e _ => ?_
              by_cases h2 : ∀ j, colProd m j ∣ e j
              · rw [if_pos ⟨h1, h2⟩, if_pos h2]
              · rw [if_neg (fun h => h2 h.2), if_neg h2]
            · rw [if_neg h1]
              refine Finset.sum_eq_zero fun e _ => ?_
              rw [if_neg (fun h => h1 h.1)]
  rw [hswap]
  refine Finset.sum_congr rfl ?_
  intro m hm
  have hmV : ValidMat W R m := mem_validMatSet_iff.mp hm
  have hrowV : Valid W R (rowProd m) := validMat_rowProd_valid hmV
  have hcolV : Valid W R (colProd m) := validMat_colProd_valid hmV
  rw [sum_lambda_div_prod_eq y hrowV, sum_lambda_div_prod_eq y hcolV]
  -- Simplify totient and moebius products
  have hmob_row : (∏ i : Fin k, (ArithmeticFunction.moebius (rowProd m i) : ℝ)) =
      ∏ p : Fin k × Fin k, (ArithmeticFunction.moebius (m p) : ℝ) := by
    rw [← moebius_prod_of_squarefree hrowV.1, prod_rowProd_eq, moebius_prod_of_squarefree hmV.1]
  have hmob_col : (∏ j : Fin k, (ArithmeticFunction.moebius (colProd m j) : ℝ)) =
      ∏ p : Fin k × Fin k, (ArithmeticFunction.moebius (m p) : ℝ) := by
    rw [← moebius_prod_of_squarefree hcolV.1, prod_colProd_eq, moebius_prod_of_squarefree hmV.1]
  have htot_row : (∏ i : Fin k, (Nat.totient (rowProd m i) : ℝ)) =
      ∏ p : Fin k × Fin k, (Nat.totient (m p) : ℝ) := by
    have h1 : ∏ i : Fin k, Nat.totient (rowProd m i) = ∏ p : Fin k × Fin k, Nat.totient (m p) := by
      rw [← totient_prod_of_squarefree hrowV.1, prod_rowProd_eq, totient_prod_of_squarefree hmV.1]
    exact_mod_cast h1
  have htot_col : (∏ j : Fin k, (Nat.totient (colProd m j) : ℝ)) =
      ∏ p : Fin k × Fin k, (Nat.totient (m p) : ℝ) := by
    have h1 : ∏ j : Fin k, Nat.totient (colProd m j) = ∏ p : Fin k × Fin k, Nat.totient (m p) := by
      rw [← totient_prod_of_squarefree hcolV.1, prod_colProd_eq, totient_prod_of_squarefree hmV.1]
    exact_mod_cast h1
  rw [hmob_row, hmob_col, htot_row, htot_col]
  have hmob_sq : (∏ p : Fin k × Fin k, (ArithmeticFunction.moebius (m p) : ℝ)) *
      (∏ p : Fin k × Fin k, (ArithmeticFunction.moebius (m p) : ℝ)) = 1 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one ?_
    intro p _
    have hp_sq : Squarefree (m p) := hmV.1.squarefree_of_dvd (Finset.dvd_prod_of_mem m (Finset.mem_univ p))
    have := moebius_sq_eq_one_of_squarefree hp_sq
    linarith [sq (ArithmeticFunction.moebius (m p) : ℝ)]
  have hcoeff :
      (∏ p : Fin k × Fin k,
        if p.1 = p.2 then (Nat.totient (m p) : ℝ) else (ArithmeticFunction.moebius (m p) : ℝ)) /
      ((∏ p : Fin k × Fin k, (Nat.totient (m p) : ℝ)) *
        (∏ p : Fin k × Fin k, (Nat.totient (m p) : ℝ))) =
      ∏ p : Fin k × Fin k,
        if p.1 = p.2 then 1 / (Nat.totient (m p) : ℝ)
        else (ArithmeticFunction.moebius (m p) : ℝ) / (Nat.totient (m p) : ℝ) ^ 2 := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl ?_
    intro p _
    have hp_pos : 0 < m p := squarefree_pos (hmV.1.squarefree_of_dvd (Finset.dvd_prod_of_mem m (Finset.mem_univ p)))
    have hphi_ne : (Nat.totient (m p) : ℝ) ≠ 0 := (Nat.cast_pos.mpr (Nat.totient_pos.mpr hp_pos)).ne'
    split_ifs
    · field_simp
    · ring
  calc (∏ p : Fin k × Fin k,
          if p.1 = p.2 then (Nat.totient (m p) : ℝ) else (ArithmeticFunction.moebius (m p) : ℝ)) *
        ((∏ p : Fin k × Fin k, (ArithmeticFunction.moebius (m p) : ℝ)) * y (rowProd m) /
          (∏ p : Fin k × Fin k, (Nat.totient (m p) : ℝ))) *
        ((∏ p : Fin k × Fin k, (ArithmeticFunction.moebius (m p) : ℝ)) * y (colProd m) /
          (∏ p : Fin k × Fin k, (Nat.totient (m p) : ℝ)))
      = ((∏ p : Fin k × Fin k,
            if p.1 = p.2 then (Nat.totient (m p) : ℝ) else (ArithmeticFunction.moebius (m p) : ℝ)) /
          ((∏ p : Fin k × Fin k, (Nat.totient (m p) : ℝ)) *
            (∏ p : Fin k × Fin k, (Nat.totient (m p) : ℝ)))) *
        ((∏ p : Fin k × Fin k, (ArithmeticFunction.moebius (m p) : ℝ)) *
          (∏ p : Fin k × Fin k, (ArithmeticFunction.moebius (m p) : ℝ))) *
        y (rowProd m) * y (colProd m) := by ring
    _ = _ := by rw [hcoeff, hmob_sq, mul_one]

/-- Exact matrix identity for M_2(idx) when 2 | W. -/
lemma M2_eq_matrix_sum {k W R : ℕ} (h2W : 2 ∣ W) (y : (Fin k → ℕ) → ℝ) (idx : Fin k) :
    ∑ d ∈ (validSet k W R).filter (fun d => d idx = 1),
      ∑ e ∈ (validSet k W R).filter (fun e => e idx = 1 ∧ ∀ i j : Fin k, i ≠ j → Nat.Coprime (d i) (e j)),
        (lambdaOfY k W R y d * lambdaOfY k W R y e) /
          (∏ i : Fin k, (Nat.totient (Nat.lcm (d i) (e i)) : ℝ)) =
    ∑ m ∈ (validMatSet k W R).filter (fun m => rowProd m idx = 1 ∧ colProd m idx = 1),
      (∏ p : Fin k × Fin k,
        if p.1 = p.2 then 1 / (phi2 (m p) : ℝ)
        else (ArithmeticFunction.moebius (m p) : ℝ) / (phi2 (m p) : ℝ) ^ 2) *
      yMod k W R y idx (rowProd m) * yMod k W R y idx (colProd m) := by
  classical
  have hphi2_ne_of_copW : ∀ n : ℕ, Nat.Coprime n W → (phi2 n : ℝ) ≠ 0 := by
    intro n hc
    have hnot2 : ¬ 2 ∣ n := by
      intro h2n
      exact (by decide : ¬ (2 : ℕ) ∣ 1) (hc.gcd_eq_one ▸ Nat.dvd_gcd h2n h2W)
    exact (Nat.cast_pos.mpr (phi2_pos_of_odd hnot2)).ne'
  -- Step 1: expand 1 / phi(lcm(di, ei)) and coprimality indicator into matrix sum
  have hstep1 :
      ∑ d ∈ (validSet k W R).filter (fun d => d idx = 1),
        ∑ e ∈ (validSet k W R).filter (fun e => e idx = 1 ∧ ∀ i j : Fin k, i ≠ j → Nat.Coprime (d i) (e j)),
          (lambdaOfY k W R y d * lambdaOfY k W R y e) /
            (∏ i : Fin k, (Nat.totient (Nat.lcm (d i) (e i)) : ℝ)) =
      ∑ d ∈ (validSet k W R).filter (fun d => d idx = 1),
        ∑ e ∈ (validSet k W R).filter (fun e => e idx = 1),
          (lambdaOfY k W R y d / (∏ i ∈ Finset.univ.erase idx, (Nat.totient (d i) : ℝ))) *
          (lambdaOfY k W R y e / (∏ j ∈ Finset.univ.erase idx, (Nat.totient (e j) : ℝ))) *
          ∑ m ∈ ((validMatSet k W R).filter (fun m => rowProd m idx = 1 ∧ colProd m idx = 1)).filter
              (fun m => (∀ i, rowProd m i ∣ d i) ∧ (∀ j, colProd m j ∣ e j)),
            ∏ p : Fin k × Fin k,
              if p.1 = p.2 then (phi2 (m p) : ℝ) else (ArithmeticFunction.moebius (m p) : ℝ) := by
    refine Finset.sum_congr rfl ?_
    intro d hd
    have hdV : Valid W R d := mem_validSet_iff.mp (Finset.mem_filter.mp hd).1
    have hd_idx : d idx = 1 := (Finset.mem_filter.mp hd).2
    have hfilter_e :
        (validSet k W R).filter (fun e => e idx = 1 ∧ ∀ i j : Fin k, i ≠ j → Nat.Coprime (d i) (e j)) =
        ((validSet k W R).filter (fun e => e idx = 1)).filter
          (fun e => ∀ i j : Fin k, i ≠ j → Nat.Coprime (d i) (e j)) := by
      ext e; simp [and_assoc]
    rw [hfilter_e, Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro e he
    have heV : Valid W R e := mem_validSet_iff.mp (Finset.mem_filter.mp he).1
    have he_idx : e idx = 1 := (Finset.mem_filter.mp he).2
    have hmat_set :
        ((validMatSet k W R).filter (fun m => rowProd m idx = 1 ∧ colProd m idx = 1)).filter
          (fun m => (∀ i, rowProd m i ∣ d i) ∧ (∀ j, colProd m j ∣ e j)) =
        Fintype.piFinset (fun p : Fin k × Fin k => (Nat.gcd (d p.1) (e p.2)).divisors) := by
      ext m
      simp only [Finset.mem_filter, mem_validMatSet_iff, Fintype.mem_piFinset, Nat.mem_divisors]
      have hgcd_ne : ∀ p : Fin k × Fin k, Nat.gcd (d p.1) (e p.2) ≠ 0 :=
        fun p => (Nat.gcd_pos_of_pos_left (e p.2) (valid_pos_at hdV p.1)).ne'
      simp only [hgcd_ne, ne_eq, not_false_eq_true, and_true]
      constructor
      · rintro ⟨⟨hmV, _, _⟩, hrow, hcol⟩
        exact (mat_dvd_iff_row_col_dvd hdV heV m).mpr ⟨hmV, hrow, hcol⟩
      · intro hm
        obtain ⟨hmV, hrow, hcol⟩ := (mat_dvd_iff_row_col_dvd hdV heV m).mp hm
        have hri1 : rowProd m idx = 1 := Nat.dvd_one.mp (hd_idx ▸ hrow idx)
        have hci1 : colProd m idx = 1 := Nat.dvd_one.mp (he_idx ▸ hcol idx)
        exact ⟨⟨hmV, hri1, hci1⟩, hrow, hcol⟩
    rw [hmat_set, sum_piFinset_prod (f := fun (p : Fin k × Fin k) x =>
      if p.1 = p.2 then (phi2 x : ℝ) else (ArithmeticFunction.moebius x : ℝ))]
    have hprod_eval :
        ∏ p : Fin k × Fin k, ∑ x ∈ (Nat.gcd (d p.1) (e p.2)).divisors,
          (if p.1 = p.2 then (phi2 x : ℝ) else (ArithmeticFunction.moebius x : ℝ)) =
        (∏ i : Fin k, (Nat.totient (Nat.gcd (d i) (e i)) : ℝ)) *
          (if ∀ i j : Fin k, i ≠ j → Nat.Coprime (d i) (e j) then (1 : ℝ) else 0) := by
      have h1 : ∀ p : Fin k × Fin k,
          ∑ x ∈ (Nat.gcd (d p.1) (e p.2)).divisors,
            (if p.1 = p.2 then (phi2 x : ℝ) else (ArithmeticFunction.moebius x : ℝ)) =
          if p.1 = p.2 then (Nat.totient (Nat.gcd (d p.1) (e p.2)) : ℝ)
          else if Nat.Coprime (d p.1) (e p.2) then 1 else 0 := by
        intro p
        by_cases hp : p.1 = p.2
        · rw [if_pos hp]
          simp only [if_pos hp]
          have hgcd_sq : Squarefree (Nat.gcd (d p.1) (e p.2)) :=
            (valid_squarefree_at hdV p.1).squarefree_of_dvd (Nat.gcd_dvd_left _ _)
          exact_mod_cast sum_phi2_divisors_eq_totient hgcd_sq
        · rw [if_neg hp]
          simp only [if_neg hp, sum_moebius_divisors_eq_ite]
      simp_rw [h1]
      by_cases hcop : ∀ i j : Fin k, i ≠ j → Nat.Coprime (d i) (e j)
      · rw [if_pos hcop, mul_one, Fintype.prod_prod_type]
        refine Finset.prod_congr rfl ?_
        intro i _
        rw [Finset.prod_eq_single i]
        · simp
        · intro j _ hji
          rw [if_neg (Ne.symm hji), if_pos (hcop i j (Ne.symm hji))]
        · intro hnot; exact absurd (Finset.mem_univ i) hnot
      · rw [if_neg hcop, mul_zero]
        push Not at hcop
        rcases hcop with ⟨i, j, hij, hncop⟩
        refine Finset.prod_eq_zero (Finset.mem_univ (i, j)) ?_
        rw [if_neg hij, if_neg hncop]
    rw [hprod_eval]
    by_cases hcop : ∀ i j : Fin k, i ≠ j → Nat.Coprime (d i) (e j)
    · rw [if_pos hcop, if_pos hcop, mul_one]
      have hd_er : (∏ i ∈ Finset.univ.erase idx, (Nat.totient (d i) : ℝ)) =
          ∏ i : Fin k, (Nat.totient (d i) : ℝ) := by
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ idx), hd_idx]
        simp
      have he_er : (∏ j ∈ Finset.univ.erase idx, (Nat.totient (e j) : ℝ)) =
          ∏ j : Fin k, (Nat.totient (e j) : ℝ) := by
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ idx), he_idx]
        simp
      rw [hd_er, he_er]
      have hlcm_eq : (∏ i : Fin k, (Nat.totient (Nat.lcm (d i) (e i)) : ℝ)) *
          (∏ i : Fin k, (Nat.totient (Nat.gcd (d i) (e i)) : ℝ)) =
          (∏ i : Fin k, (Nat.totient (d i) : ℝ)) * (∏ j : Fin k, (Nat.totient (e j) : ℝ)) := by
        rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl ?_
        intro i _
        exact_mod_cast totient_lcm_mul_totient_gcd (d i) (e i)
      have hd_ne : (∏ i : Fin k, (Nat.totient (d i) : ℝ)) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr (fun i _ => (Nat.cast_pos.mpr (Nat.totient_pos.mpr (valid_pos_at hdV i))).ne')
      have he_ne : (∏ j : Fin k, (Nat.totient (e j) : ℝ)) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr (fun j _ => (Nat.cast_pos.mpr (Nat.totient_pos.mpr (valid_pos_at heV j))).ne')
      have hlcm_ne : (∏ i : Fin k, (Nat.totient (Nat.lcm (d i) (e i)) : ℝ)) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr (fun i _ =>
          (Nat.cast_pos.mpr (Nat.totient_pos.mpr
            (Nat.pos_of_ne_zero (Nat.lcm_ne_zero (valid_pos_at hdV i).ne' (valid_pos_at heV i).ne')))).ne')
      rw [div_mul_div_comm, div_mul_eq_mul_div, div_eq_div_iff hlcm_ne (mul_ne_zero hd_ne he_ne)]
      linear_combination (lambdaOfY k W R y d * lambdaOfY k W R y e) * hlcm_eq.symm
    · rw [if_neg hcop, if_neg hcop, mul_zero, mul_zero]
  rw [hstep1]
  -- Step 2: swap sum over (d, e) and m
  set Mset := (validMatSet k W R).filter (fun m => rowProd m idx = 1 ∧ colProd m idx = 1)
  set Dset := (validSet k W R).filter (fun d => d idx = 1)
  have hswap :
      ∑ d ∈ Dset, ∑ e ∈ Dset,
        (lambdaOfY k W R y d / (∏ i ∈ Finset.univ.erase idx, (Nat.totient (d i) : ℝ))) *
        (lambdaOfY k W R y e / (∏ j ∈ Finset.univ.erase idx, (Nat.totient (e j) : ℝ))) *
        ∑ m ∈ Mset.filter (fun m => (∀ i, rowProd m i ∣ d i) ∧ (∀ j, colProd m j ∣ e j)),
          (∏ p : Fin k × Fin k,
            if p.1 = p.2 then (phi2 (m p) : ℝ) else (ArithmeticFunction.moebius (m p) : ℝ)) =
      ∑ m ∈ Mset,
        (∏ p : Fin k × Fin k,
          if p.1 = p.2 then (phi2 (m p) : ℝ) else (ArithmeticFunction.moebius (m p) : ℝ)) *
        (∑ d ∈ (validSet k W R).filter (fun d => d idx = 1 ∧ ∀ i, rowProd m i ∣ d i),
          lambdaOfY k W R y d / (∏ i ∈ Finset.univ.erase idx, (Nat.totient (d i) : ℝ))) *
        (∑ e ∈ (validSet k W R).filter (fun e => e idx = 1 ∧ ∀ j, colProd m j ∣ e j),
          lambdaOfY k W R y e / (∏ j ∈ Finset.univ.erase idx, (Nat.totient (e j) : ℝ))) := by
    trans (∑ d ∈ Dset, ∑ e ∈ Dset, ∑ m ∈ Mset,
      if (∀ i, rowProd m i ∣ d i) ∧ (∀ j, colProd m j ∣ e j) then
        (∏ p : Fin k × Fin k,
          if p.1 = p.2 then (phi2 (m p) : ℝ) else (ArithmeticFunction.moebius (m p) : ℝ)) *
        (lambdaOfY k W R y d / (∏ i ∈ Finset.univ.erase idx, (Nat.totient (d i) : ℝ))) *
        (lambdaOfY k W R y e / (∏ j ∈ Finset.univ.erase idx, (Nat.totient (e j) : ℝ)))
      else 0)
    · refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun e _ => ?_
      rw [Finset.mul_sum, Finset.sum_filter]
      refine Finset.sum_congr rfl fun m _ => ?_
      split_ifs <;> ring
    · calc ∑ d ∈ Dset, ∑ e ∈ Dset, ∑ m ∈ Mset, _
          = ∑ d ∈ Dset, ∑ m ∈ Mset, ∑ e ∈ Dset, _ :=
            Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
        _ = ∑ m ∈ Mset, ∑ d ∈ Dset, ∑ e ∈ Dset, _ := Finset.sum_comm
        _ = _ := by
            refine Finset.sum_congr rfl fun m _ => ?_
            have hD1 : (validSet k W R).filter (fun d => d idx = 1 ∧ ∀ i, rowProd m i ∣ d i) =
                Dset.filter (fun d => ∀ i, rowProd m i ∣ d i) := by ext d; simp [Dset, and_assoc]
            have hD2 : (validSet k W R).filter (fun e => e idx = 1 ∧ ∀ j, colProd m j ∣ e j) =
                Dset.filter (fun e => ∀ j, colProd m j ∣ e j) := by ext e; simp [Dset, and_assoc]
            rw [hD1, hD2]
            have hrhs :
                (∏ p : Fin k × Fin k,
                  if p.1 = p.2 then (phi2 (m p) : ℝ) else (ArithmeticFunction.moebius (m p) : ℝ)) *
                (∑ d ∈ Dset.filter (fun d => ∀ i, rowProd m i ∣ d i),
                  lambdaOfY k W R y d / (∏ i ∈ Finset.univ.erase idx, (Nat.totient (d i) : ℝ))) *
                (∑ e ∈ Dset.filter (fun e => ∀ j, colProd m j ∣ e j),
                  lambdaOfY k W R y e / (∏ j ∈ Finset.univ.erase idx, (Nat.totient (e j) : ℝ))) =
                ∑ d ∈ Dset.filter (fun d => ∀ i, rowProd m i ∣ d i),
                  ∑ e ∈ Dset.filter (fun e => ∀ j, colProd m j ∣ e j),
                    (∏ p : Fin k × Fin k,
                      if p.1 = p.2 then (phi2 (m p) : ℝ) else (ArithmeticFunction.moebius (m p) : ℝ)) *
                    (lambdaOfY k W R y d / (∏ i ∈ Finset.univ.erase idx, (Nat.totient (d i) : ℝ))) *
                    (lambdaOfY k W R y e / (∏ j ∈ Finset.univ.erase idx, (Nat.totient (e j) : ℝ))) := by
              rw [Finset.mul_sum (s := Dset.filter (fun d => ∀ i, rowProd m i ∣ d i)),
                Finset.sum_mul]
              refine Finset.sum_congr rfl fun d _ => ?_
              rw [Finset.mul_sum]
            rw [hrhs]
            conv_rhs => rw [Finset.sum_filter]
            refine Finset.sum_congr rfl fun d _ => ?_
            by_cases h1 : ∀ i, rowProd m i ∣ d i
            · rw [if_pos h1]
              conv_rhs => rw [Finset.sum_filter]
              refine Finset.sum_congr rfl fun e _ => ?_
              by_cases h2 : ∀ j, colProd m j ∣ e j
              · rw [if_pos ⟨h1, h2⟩, if_pos h2]
              · rw [if_neg (fun h => h2 h.2), if_neg h2]
            · rw [if_neg h1]
              refine Finset.sum_eq_zero fun e _ => ?_
              rw [if_neg (fun h => h1 h.1)]
  rw [hswap]
  refine Finset.sum_congr rfl ?_
  intro m hm
  have hmV : ValidMat W R m := mem_validMatSet_iff.mp (Finset.mem_filter.mp hm).1
  have hri1 : rowProd m idx = 1 := (Finset.mem_filter.mp hm).2.1
  have hci1 : colProd m idx = 1 := (Finset.mem_filter.mp hm).2.2
  have hrowV : Valid W R (rowProd m) := validMat_rowProd_valid hmV
  have hcolV : Valid W R (colProd m) := validMat_colProd_valid hmV
  -- Express inner sums in terms of yMod
  have hsum_row :
      ∑ d ∈ (validSet k W R).filter (fun d => d idx = 1 ∧ ∀ i, rowProd m i ∣ d i),
        lambdaOfY k W R y d / (∏ i ∈ Finset.univ.erase idx, (Nat.totient (d i) : ℝ)) =
      (∏ i ∈ Finset.univ.erase idx, (ArithmeticFunction.moebius (rowProd m i) : ℝ)) *
        yMod k W R y idx (rowProd m) /
        (∏ i ∈ Finset.univ.erase idx, (phi2 (rowProd m i) : ℝ)) := by
    unfold yMod
    rw [if_pos ⟨hrowV, hri1⟩, Finset.prod_mul_distrib]
    have hmob_sq : (∏ i ∈ Finset.univ.erase idx, (ArithmeticFunction.moebius (rowProd m i) : ℝ)) *
        (∏ i ∈ Finset.univ.erase idx, (ArithmeticFunction.moebius (rowProd m i) : ℝ)) = 1 := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_eq_one fun i _ => ?_
      have := moebius_sq_eq_one_of_squarefree (valid_squarefree_at hrowV i)
      linarith [sq (ArithmeticFunction.moebius (rowProd m i) : ℝ)]
    have hphi2_ne : (∏ i ∈ Finset.univ.erase idx, (phi2 (rowProd m i) : ℝ)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun i _ => hphi2_ne_of_copW _ (valid_coprime_W_at hrowV i))
    symm
    calc (∏ i ∈ Finset.univ.erase idx, (ArithmeticFunction.moebius (rowProd m i) : ℝ)) *
          ((∏ i ∈ Finset.univ.erase idx, (ArithmeticFunction.moebius (rowProd m i) : ℝ)) *
            (∏ i ∈ Finset.univ.erase idx, (phi2 (rowProd m i) : ℝ)) *
            ∑ d ∈ (validSet k W R).filter (fun d => d idx = 1 ∧ ∀ i, rowProd m i ∣ d i),
              lambdaOfY k W R y d / (∏ i ∈ Finset.univ.erase idx, (Nat.totient (d i) : ℝ))) /
          (∏ i ∈ Finset.univ.erase idx, (phi2 (rowProd m i) : ℝ))
        = ((∏ i ∈ Finset.univ.erase idx, (ArithmeticFunction.moebius (rowProd m i) : ℝ)) *
            (∏ i ∈ Finset.univ.erase idx, (ArithmeticFunction.moebius (rowProd m i) : ℝ))) *
          ((∏ i ∈ Finset.univ.erase idx, (phi2 (rowProd m i) : ℝ)) *
            (∑ d ∈ (validSet k W R).filter (fun d => d idx = 1 ∧ ∀ i, rowProd m i ∣ d i),
              lambdaOfY k W R y d / (∏ i ∈ Finset.univ.erase idx, (Nat.totient (d i) : ℝ))) /
            (∏ i ∈ Finset.univ.erase idx, (phi2 (rowProd m i) : ℝ))) := by ring
      _ = _ := by rw [hmob_sq, one_mul, mul_div_cancel_left₀ _ hphi2_ne]
  have hsum_col :
      ∑ e ∈ (validSet k W R).filter (fun e => e idx = 1 ∧ ∀ j, colProd m j ∣ e j),
        lambdaOfY k W R y e / (∏ j ∈ Finset.univ.erase idx, (Nat.totient (e j) : ℝ)) =
      (∏ j ∈ Finset.univ.erase idx, (ArithmeticFunction.moebius (colProd m j) : ℝ)) *
        yMod k W R y idx (colProd m) /
        (∏ j ∈ Finset.univ.erase idx, (phi2 (colProd m j) : ℝ)) := by
    unfold yMod
    rw [if_pos ⟨hcolV, hci1⟩, Finset.prod_mul_distrib]
    have hmob_sq : (∏ j ∈ Finset.univ.erase idx, (ArithmeticFunction.moebius (colProd m j) : ℝ)) *
        (∏ j ∈ Finset.univ.erase idx, (ArithmeticFunction.moebius (colProd m j) : ℝ)) = 1 := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_eq_one fun j _ => ?_
      have := moebius_sq_eq_one_of_squarefree (valid_squarefree_at hcolV j)
      linarith [sq (ArithmeticFunction.moebius (colProd m j) : ℝ)]
    have hphi2_ne : (∏ j ∈ Finset.univ.erase idx, (phi2 (colProd m j) : ℝ)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun j _ => hphi2_ne_of_copW _ (valid_coprime_W_at hcolV j))
    symm
    calc (∏ j ∈ Finset.univ.erase idx, (ArithmeticFunction.moebius (colProd m j) : ℝ)) *
          ((∏ j ∈ Finset.univ.erase idx, (ArithmeticFunction.moebius (colProd m j) : ℝ)) *
            (∏ j ∈ Finset.univ.erase idx, (phi2 (colProd m j) : ℝ)) *
            ∑ e ∈ (validSet k W R).filter (fun e => e idx = 1 ∧ ∀ j, colProd m j ∣ e j),
              lambdaOfY k W R y e / (∏ j ∈ Finset.univ.erase idx, (Nat.totient (e j) : ℝ))) /
          (∏ j ∈ Finset.univ.erase idx, (phi2 (colProd m j) : ℝ))
        = ((∏ j ∈ Finset.univ.erase idx, (ArithmeticFunction.moebius (colProd m j) : ℝ)) *
            (∏ j ∈ Finset.univ.erase idx, (ArithmeticFunction.moebius (colProd m j) : ℝ))) *
          ((∏ j ∈ Finset.univ.erase idx, (phi2 (colProd m j) : ℝ)) *
            (∑ e ∈ (validSet k W R).filter (fun e => e idx = 1 ∧ ∀ j, colProd m j ∣ e j),
              lambdaOfY k W R y e / (∏ j ∈ Finset.univ.erase idx, (Nat.totient (e j) : ℝ))) /
            (∏ j ∈ Finset.univ.erase idx, (phi2 (colProd m j) : ℝ))) := by ring
      _ = _ := by rw [hmob_sq, one_mul, mul_div_cancel_left₀ _ hphi2_ne]
  rw [hsum_row, hsum_col]
  -- Drop erase idx using rowProd m idx = 1 and colProd m idx = 1
  have hmob_row : (∏ i ∈ Finset.univ.erase idx, (ArithmeticFunction.moebius (rowProd m i) : ℝ)) =
      ∏ p : Fin k × Fin k, (ArithmeticFunction.moebius (m p) : ℝ) := by
    have h1 : (∏ i ∈ Finset.univ.erase idx, (ArithmeticFunction.moebius (rowProd m i) : ℝ)) =
        ∏ i : Fin k, (ArithmeticFunction.moebius (rowProd m i) : ℝ) := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ idx), hri1]; simp
    rw [h1, ← moebius_prod_of_squarefree hrowV.1, prod_rowProd_eq, moebius_prod_of_squarefree hmV.1]
  have hmob_col : (∏ j ∈ Finset.univ.erase idx, (ArithmeticFunction.moebius (colProd m j) : ℝ)) =
      ∏ p : Fin k × Fin k, (ArithmeticFunction.moebius (m p) : ℝ) := by
    have h1 : (∏ j ∈ Finset.univ.erase idx, (ArithmeticFunction.moebius (colProd m j) : ℝ)) =
        ∏ j : Fin k, (ArithmeticFunction.moebius (colProd m j) : ℝ) := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ idx), hci1]; simp
    rw [h1, ← moebius_prod_of_squarefree hcolV.1, prod_colProd_eq, moebius_prod_of_squarefree hmV.1]
  have hphi2_row : (∏ i ∈ Finset.univ.erase idx, (phi2 (rowProd m i) : ℝ)) =
      ∏ p : Fin k × Fin k, (phi2 (m p) : ℝ) := by
    have h1 : ∏ i ∈ Finset.univ.erase idx, phi2 (rowProd m i) = ∏ i : Fin k, phi2 (rowProd m i) := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ idx), hri1, phi2_one, one_mul]
    have h2 : ∏ i : Fin k, phi2 (rowProd m i) = ∏ p : Fin k × Fin k, phi2 (m p) := by
      rw [← phi2_prod_of_squarefree hrowV.1, prod_rowProd_eq, phi2_prod_of_squarefree hmV.1]
    exact_mod_cast h1.trans h2
  have hphi2_col : (∏ j ∈ Finset.univ.erase idx, (phi2 (colProd m j) : ℝ)) =
      ∏ p : Fin k × Fin k, (phi2 (m p) : ℝ) := by
    have h1 : ∏ j ∈ Finset.univ.erase idx, phi2 (colProd m j) = ∏ j : Fin k, phi2 (colProd m j) := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ idx), hci1, phi2_one, one_mul]
    have h2 : ∏ j : Fin k, phi2 (colProd m j) = ∏ p : Fin k × Fin k, phi2 (m p) := by
      rw [← phi2_prod_of_squarefree hcolV.1, prod_colProd_eq, phi2_prod_of_squarefree hmV.1]
    exact_mod_cast h1.trans h2
  rw [hmob_row, hmob_col, hphi2_row, hphi2_col]
  have hmob_sq : (∏ p : Fin k × Fin k, (ArithmeticFunction.moebius (m p) : ℝ)) *
      (∏ p : Fin k × Fin k, (ArithmeticFunction.moebius (m p) : ℝ)) = 1 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun p _ => ?_
    have hp_sq : Squarefree (m p) := hmV.1.squarefree_of_dvd (Finset.dvd_prod_of_mem m (Finset.mem_univ p))
    have := moebius_sq_eq_one_of_squarefree hp_sq
    linarith [sq (ArithmeticFunction.moebius (m p) : ℝ)]
  have hcoeff :
      (∏ p : Fin k × Fin k,
        if p.1 = p.2 then (phi2 (m p) : ℝ) else (ArithmeticFunction.moebius (m p) : ℝ)) /
      ((∏ p : Fin k × Fin k, (phi2 (m p) : ℝ)) *
        (∏ p : Fin k × Fin k, (phi2 (m p) : ℝ))) =
      ∏ p : Fin k × Fin k,
        if p.1 = p.2 then 1 / (phi2 (m p) : ℝ)
        else (ArithmeticFunction.moebius (m p) : ℝ) / (phi2 (m p) : ℝ) ^ 2 := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun p _ => ?_
    have hcop_p : Nat.Coprime (m p) W := hmV.2.1.coprime_dvd_left (Finset.dvd_prod_of_mem m (Finset.mem_univ p))
    have hne : (phi2 (m p) : ℝ) ≠ 0 := hphi2_ne_of_copW _ hcop_p
    split_ifs
    · field_simp
    · ring
  calc (∏ p : Fin k × Fin k,
          if p.1 = p.2 then (phi2 (m p) : ℝ) else (ArithmeticFunction.moebius (m p) : ℝ)) *
        ((∏ p : Fin k × Fin k, (ArithmeticFunction.moebius (m p) : ℝ)) * yMod k W R y idx (rowProd m) /
          (∏ p : Fin k × Fin k, (phi2 (m p) : ℝ))) *
        ((∏ p : Fin k × Fin k, (ArithmeticFunction.moebius (m p) : ℝ)) * yMod k W R y idx (colProd m) /
          (∏ p : Fin k × Fin k, (phi2 (m p) : ℝ)))
      = ((∏ p : Fin k × Fin k,
            if p.1 = p.2 then (phi2 (m p) : ℝ) else (ArithmeticFunction.moebius (m p) : ℝ)) /
          ((∏ p : Fin k × Fin k, (phi2 (m p) : ℝ)) *
            (∏ p : Fin k × Fin k, (phi2 (m p) : ℝ)))) *
        ((∏ p : Fin k × Fin k, (ArithmeticFunction.moebius (m p) : ℝ)) *
          (∏ p : Fin k × Fin k, (ArithmeticFunction.moebius (m p) : ℝ))) *
        yMod k W R y idx (rowProd m) * yMod k W R y idx (colProd m) := by ring
    _ = _ := by rw [hcoeff, hmob_sq, mul_one]

-- ### Quantitative bounds on lambdaOfY, M1, yMod, and M2

lemma exp_sub_one_le_two_mul {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    Real.exp t - 1 ≤ 2 * t := by
  have h := Real.exp_bound (x := t) (by rw [abs_of_nonneg ht0]; linarith) (n := 2) (by norm_num)
  simp [Finset.sum_range_succ, Nat.factorial] at h
  rw [abs_le] at h
  have hsq : t ^ 2 ≤ (1 / 2 : ℝ) * t := by nlinarith
  nlinarith [h.2, abs_of_nonneg ht0]

lemma sum_inv_totient_sq_le_exp {D0 R : ℕ} (hD : 4 ≤ D0) :
    ∑ s ∈ (Finset.Icc 1 R).filter (fun s => Squarefree s ∧ Nat.Coprime s (primorial D0)),
      (1 / (Nat.totient s : ℝ) ^ 2) ≤ Real.exp (1 / ((D0 : ℝ) - 2)) := by
  let S := (Finset.Icc 1 R).filter (fun s => Squarefree s ∧ Nat.Coprime s (primorial D0))
  have hS : ∀ n ∈ S, Squarefree n ∧ ∀ p ∈ n.primeFactors, D0 < p := by
    intro n hn
    have h := (Finset.mem_filter.mp hn).2
    exact ⟨h.1, fun p hp => prime_gt_of_coprime_primorial h.2 hp⟩
  have hterm : ∀ n ∈ S, 1 / (Nat.totient n : ℝ) ^ 2 =
      ∏ p ∈ n.primeFactors, (1 / ((p : ℝ) - 1) ^ 2) := by
    intro n hn
    have hsq := (hS n hn).1
    rw [totient_eq_prod_primeFactors_of_squarefree hsq, Nat.cast_prod, ← Finset.prod_pow,
      one_div, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
    have hcast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
    rw [hcast, one_div]
  rw [Finset.sum_congr rfl hterm]
  have hbound := sum_mult_squarefree_le_exp (D0 := D0) (c := 1) (by omega) S hS
    (fun p => 1 / ((p : ℝ) - 1) ^ 2) (fun _ => by positivity) (fun p _ => by simp)
  have heq : (D0 : ℝ) - ((1 : ℕ) : ℝ) - 1 = (D0 : ℝ) - 2 := by push_cast; ring
  rw [heq] at hbound
  exact hbound

lemma sum_inv_phi2_sq_le_exp {D0 R : ℕ} (hD : 5 ≤ D0) :
    ∑ s ∈ (Finset.Icc 1 R).filter (fun s => Squarefree s ∧ Nat.Coprime s (primorial D0)),
      (1 / (phi2 s : ℝ) ^ 2) ≤ Real.exp (1 / ((D0 : ℝ) - 3)) := by
  let S := (Finset.Icc 1 R).filter (fun s => Squarefree s ∧ Nat.Coprime s (primorial D0))
  have hS : ∀ n ∈ S, Squarefree n ∧ ∀ p ∈ n.primeFactors, D0 < p := by
    intro n hn
    have h := (Finset.mem_filter.mp hn).2
    exact ⟨h.1, fun p hp => prime_gt_of_coprime_primorial h.2 hp⟩
  have hterm : ∀ n ∈ S, 1 / (phi2 n : ℝ) ^ 2 =
      ∏ p ∈ n.primeFactors, (1 / ((p : ℝ) - 2) ^ 2) := by
    intro n hn
    unfold phi2
    rw [Nat.cast_prod, ← Finset.prod_pow, one_div, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hpD : D0 < p := (hS n hn).2 p hp
    have hcast : ((p - 2 : ℕ) : ℝ) = (p : ℝ) - 2 := by rw [Nat.cast_sub (by omega)]; simp
    rw [hcast, one_div]
  rw [Finset.sum_congr rfl hterm]
  have hbound := sum_mult_squarefree_le_exp (D0 := D0) (c := 2) (by omega) S hS
    (fun p => 1 / ((p : ℝ) - 2) ^ 2) (fun _ => by positivity) (fun p _ => by simp)
  have heq : (D0 : ℝ) - ((2 : ℕ) : ℝ) - 1 = (D0 : ℝ) - 3 := by push_cast; ring
  rw [heq] at hbound
  exact hbound

lemma sum_inv_phi2_le_two_mul_sum_inv_totient {D0 U : ℕ} (hD : 5 ≤ D0) :
    ∑ u ∈ (Finset.Icc 1 U).filter (fun u => Squarefree u ∧ Nat.Coprime u (primorial D0)),
      (1 / (phi2 u : ℝ)) ≤
    2 * ∑ u ∈ (Finset.Icc 1 U).filter (fun u => Squarefree u ∧ Nat.Coprime u (primorial D0)),
      (1 / (Nat.totient u : ℝ)) := by
  classical
  let S := (Finset.Icc 1 U).filter (fun u => Squarefree u ∧ Nat.Coprime u (primorial D0))
  have hS : ∀ n ∈ S, Squarefree n ∧ ∀ p ∈ n.primeFactors, D0 < p := by
    intro n hn
    have h := (Finset.mem_filter.mp hn).2
    exact ⟨h.1, fun p hp => prime_gt_of_coprime_primorial h.2 hp⟩
  -- For each u in S, 1 / phi2 u = (1 / phi u) * sum_{d | u} 1 / phi2 d
  have hdecomp : ∀ u ∈ S, 1 / (phi2 u : ℝ) =
      ∑ d ∈ u.divisors, (1 / ((Nat.totient d : ℝ) * (phi2 d : ℝ))) * (1 / (Nat.totient (u / d) : ℝ)) := by
    intro u hu
    have hu_sq : Squarefree u := (hS u hu).1
    have hu0 : u ≠ 0 := squarefree_ne_zero hu_sq
    have hprod : 1 / (phi2 u : ℝ) = (1 / (Nat.totient u : ℝ)) *
        ∏ p ∈ u.primeFactors, (1 + 1 / ((p : ℝ) - 2)) := by
      unfold phi2
      rw [totient_eq_prod_primeFactors_of_squarefree hu_sq, Nat.cast_prod, Nat.cast_prod,
        one_div, one_div, ← Finset.prod_inv_distrib, ← Finset.prod_inv_distrib,
        ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun p hp => ?_
      have hpD : D0 < p := (hS u hu).2 p hp
      have hp1 : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
      have hp2 : ((p - 2 : ℕ) : ℝ) = (p : ℝ) - 2 := by rw [Nat.cast_sub (by omega)]; simp
      have hne1 : (p : ℝ) - 1 ≠ 0 := by
        have : (5 : ℝ) < p := by exact_mod_cast (by omega : 5 < p)
        linarith
      have hne2 : (p : ℝ) - 2 ≠ 0 := by
        have : (5 : ℝ) < p := by exact_mod_cast (by omega : 5 < p)
        linarith
      rw [hp1, hp2]
      field_simp
      ring
    rw [hprod, Finset.prod_one_add, Finset.mul_sum]
    refine Finset.sum_bij (fun s _ => ∏ p ∈ s, p) ?_ ?_ ?_ ?_
    · intro s hs
      rw [Finset.mem_powerset] at hs
      rw [Nat.mem_divisors]
      exact ⟨by rw [← squarefree_eq_prod_primeFactors hu_sq]; exact Finset.prod_dvd_prod_of_subset _ _ _ hs, hu0⟩
    · intro s₁ hs₁ s₂ hs₂ hEq
      rw [Finset.mem_powerset] at hs₁ hs₂
      have h1 := primeFactors_prod_subset_primes (fun p hp => Nat.prime_of_mem_primeFactors (hs₁ hp))
      have h2 := primeFactors_prod_subset_primes (fun p hp => Nat.prime_of_mem_primeFactors (hs₂ hp))
      rw [← h1, ← h2, hEq]
    · intro d hd
      rw [Nat.mem_divisors] at hd
      refine ⟨d.primeFactors, Finset.mem_powerset.mpr (Nat.primeFactors_mono hd.1 hu0),
        squarefree_eq_prod_primeFactors (hu_sq.squarefree_of_dvd hd.1)⟩
    · intro s hs
      rw [Finset.mem_powerset] at hs
      set d := ∏ p ∈ s, p
      have hd_dvd : d ∣ u := by
        rw [← squarefree_eq_prod_primeFactors hu_sq]
        exact Finset.prod_dvd_prod_of_subset _ _ _ hs
      have hpf_d : d.primeFactors = s :=
        primeFactors_prod_subset_primes (fun p hp => Nat.prime_of_mem_primeFactors (hs hp))
      have hmul : d * (u / d) = u := Nat.mul_div_cancel' hd_dvd
      have hcop : Nat.Coprime d (u / d) := Nat.coprime_of_squarefree_mul (hmul.symm ▸ hu_sq)
      have htot_u : (Nat.totient u : ℝ) = (Nat.totient d : ℝ) * (Nat.totient (u / d) : ℝ) := by
        have : Nat.totient u = Nat.totient d * Nat.totient (u / d) := by
          conv_lhs => rw [← hmul]
          exact Nat.totient_mul hcop
        exact_mod_cast this
      have hphi2_d : ∏ p ∈ s, (1 / ((p : ℝ) - 2)) = 1 / (phi2 d : ℝ) := by
        unfold phi2
        rw [hpf_d, Nat.cast_prod, one_div, ← Finset.prod_inv_distrib]
        refine Finset.prod_congr rfl fun p hp => ?_
        have hpD : D0 < p := (hS u hu).2 p (hs hp)
        have hp2 : ((p - 2 : ℕ) : ℝ) = (p : ℝ) - 2 := by rw [Nat.cast_sub (by omega)]; simp
        rw [hp2, one_div]
      rw [htot_u, hphi2_d]
      ring
  rw [Finset.sum_congr rfl hdecomp]
  -- Swap sum over u and d: each (d, u/d) is in S x S
  have hle_prod :
      ∑ u ∈ S, ∑ d ∈ u.divisors, (1 / ((Nat.totient d : ℝ) * (phi2 d : ℝ))) * (1 / (Nat.totient (u / d) : ℝ)) ≤
      (∑ d ∈ S, (1 / ((Nat.totient d : ℝ) * (phi2 d : ℝ)))) * (∑ t ∈ S, (1 / (Nat.totient t : ℝ))) := by
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    rw [← Finset.sum_product']
    -- Map (u, d) -> (d, u / d) injectively into S x S
    let sigmaSet := S.sigma (fun u => u.divisors)
    have hsig : ∑ u ∈ S, ∑ d ∈ u.divisors, (1 / ((Nat.totient d : ℝ) * (phi2 d : ℝ))) * (1 / (Nat.totient (u / d) : ℝ)) =
        ∑ x ∈ sigmaSet, (1 / ((Nat.totient x.2 : ℝ) * (phi2 x.2 : ℝ))) * (1 / (Nat.totient (x.1 / x.2) : ℝ)) :=
      (Finset.sum_sigma S (fun u => u.divisors) (fun x => (1 / ((Nat.totient x.2 : ℝ) * (phi2 x.2 : ℝ))) * (1 / (Nat.totient (x.1 / x.2) : ℝ)))).symm
    rw [hsig]
    let emb : (Σ _ : ℕ, ℕ) → ℕ × ℕ := fun x => (x.2, x.1 / x.2)
    have hemb_mem : ∀ x ∈ sigmaSet, emb x ∈ S ×ˢ S := by
      intro x hx
      rw [Finset.mem_sigma] at hx
      rcases hx with ⟨huS, hdu⟩
      have hd_dvd : x.2 ∣ x.1 := Nat.dvd_of_mem_divisors hdu
      have hu_mem := Finset.mem_filter.mp huS
      have hu1 : 1 ≤ x.1 := (Finset.mem_Icc.mp hu_mem.1).1
      have huU : x.1 ≤ U := (Finset.mem_Icc.mp hu_mem.1).2
      have hd1 : 1 ≤ x.2 := Nat.pos_of_mem_divisors hdu
      have hq1 : 1 ≤ x.1 / x.2 := Nat.div_pos (Nat.le_of_dvd hu1 hd_dvd) hd1
      have hq_dvd : x.1 / x.2 ∣ x.1 := Nat.div_dvd_of_dvd hd_dvd
      rw [Finset.mem_product]
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hd1, le_trans (Nat.le_of_dvd hu1 hd_dvd) huU⟩,
        hu_mem.2.1.squarefree_of_dvd hd_dvd, hu_mem.2.2.coprime_dvd_left hd_dvd⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hq1, le_trans (Nat.le_of_dvd hu1 hq_dvd) huU⟩,
        hu_mem.2.1.squarefree_of_dvd hq_dvd, hu_mem.2.2.coprime_dvd_left hq_dvd⟩⟩
    have hemb_inj : Set.InjOn emb (sigmaSet : Set (Σ _ : ℕ, ℕ)) := by
      intro x₁ hx₁ x₂ hx₂ hEq
      have hd₁ : x₁.2 ∣ x₁.1 := Nat.dvd_of_mem_divisors (Finset.mem_sigma.mp hx₁).2
      have hd₂ : x₂.2 ∣ x₂.1 := Nat.dvd_of_mem_divisors (Finset.mem_sigma.mp hx₂).2
      have hfst : x₁.2 = x₂.2 := congrArg Prod.fst hEq
      have hsnd : x₁.1 / x₁.2 = x₂.1 / x₂.2 := congrArg Prod.snd hEq
      have hu_eq : x₁.1 = x₂.1 := by
        rw [← Nat.mul_div_cancel' hd₁, ← Nat.mul_div_cancel' hd₂, hsnd, hfst]
      exact Sigma.ext hu_eq (heq_of_eq hfst)
    calc ∑ x ∈ sigmaSet, (1 / ((Nat.totient x.2 : ℝ) * (phi2 x.2 : ℝ))) * (1 / (Nat.totient (x.1 / x.2) : ℝ))
        = ∑ y ∈ sigmaSet.image emb,
            (1 / ((Nat.totient y.1 : ℝ) * (phi2 y.1 : ℝ))) * (1 / (Nat.totient y.2 : ℝ)) := by
          rw [Finset.sum_image hemb_inj]
      _ ≤ ∑ y ∈ S ×ˢ S,
            (1 / ((Nat.totient y.1 : ℝ) * (phi2 y.1 : ℝ))) * (1 / (Nat.totient y.2 : ℝ)) :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (fun y hy => by rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩; exact hemb_mem x hx)
            (fun _ _ _ => by positivity)
  -- Bound sum_{d in S} 1 / (phi d * phi2 d) <= exp (1 / (D0 - 3)) <= 2
  have hsum_d_le : ∑ d ∈ S, (1 / ((Nat.totient d : ℝ) * (phi2 d : ℝ))) ≤ 2 := by
    have hterm : ∀ d ∈ S, 1 / ((Nat.totient d : ℝ) * (phi2 d : ℝ)) =
        ∏ p ∈ d.primeFactors, (1 / (((p : ℝ) - 1) * ((p : ℝ) - 2))) := by
      intro d hd
      have hsq := (hS d hd).1
      unfold phi2
      rw [totient_eq_prod_primeFactors_of_squarefree hsq, Nat.cast_prod, Nat.cast_prod,
        ← Finset.prod_mul_distrib, one_div, ← Finset.prod_inv_distrib]
      refine Finset.prod_congr rfl fun p hp => ?_
      have hpD : D0 < p := (hS d hd).2 p hp
      have hp1 : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
      have hp2 : ((p - 2 : ℕ) : ℝ) = (p : ℝ) - 2 := by rw [Nat.cast_sub (by omega)]; simp
      rw [hp1, hp2, one_div]
    rw [Finset.sum_congr rfl hterm]
    have h1 := sum_mult_squarefree_le_exp (D0 := D0) (c := 2) (by omega) S hS
      (fun p => 1 / (((p : ℝ) - 1) * ((p : ℝ) - 2)))
      (fun p => by
        by_cases hp : 2 ≤ p
        · have : (2 : ℝ) ≤ p := by exact_mod_cast hp
          exact div_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        · have hp_le : p ≤ 1 := by omega
          rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hp_le with rfl | rfl <;> norm_num)
      (fun p hp => by
        have hp5 : (5 : ℝ) < p := by exact_mod_cast (by omega : 5 < p)
        have hden1 : (0 : ℝ) < ((p : ℝ) - 2) ^ 2 := sq_pos_of_pos (by linarith)
        have hden2 : (0 : ℝ) < ((p : ℝ) - 1) * ((p : ℝ) - 2) := by nlinarith
        have hcast : ((2 : ℕ) : ℝ) = 2 := by norm_num
        rw [hcast]
        refine div_le_div_of_nonneg_left (by norm_num) hden1 ?_
        nlinarith)
    have hD_r : (5 : ℝ) ≤ D0 := by exact_mod_cast hD
    have harg_nonneg : (0 : ℝ) ≤ 1 / ((D0 : ℝ) - (2 : ℕ) - 1) := by
      push_cast; exact div_nonneg (by norm_num) (by linarith)
    have harg : 1 / ((D0 : ℝ) - (2 : ℕ) - 1) ≤ 1 / 2 := by
      push_cast
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      linarith
    have hexp2 : Real.exp (1 / ((D0 : ℝ) - (2 : ℕ) - 1)) ≤ 2 := by
      have h2 := exp_sub_one_le_two_mul harg_nonneg harg
      linarith
    exact le_trans h1 hexp2
  exact le_trans hle_prod (mul_le_mul_of_nonneg_right hsum_d_le
    (Finset.sum_nonneg (fun _ _ => by positivity)))

/-- Elementary upper bound on |lambda_d| for any y with 0 <= y <= 1. -/
lemma lambdaOfY_abs_le {k W R : ℕ} (hR : 1 ≤ R) (y : (Fin k → ℕ) → ℝ)
    (hy0 : ∀ r, 0 ≤ y r) (hy1 : ∀ r, y r ≤ 1) (d : Fin k → ℕ) :
    |lambdaOfY k W R y d| ≤ (2 * Real.log R + 2) ^ (3 * k) := by
  classical
  unfold lambdaOfY
  by_cases hd : Valid W R d
  · rw [if_pos hd, abs_mul]
    have hlogR_nonneg : 0 ≤ Real.log (R : ℝ) := Real.log_nonneg (by exact_mod_cast hR)
    have hprod_le : |∏ i : Fin k, (ArithmeticFunction.moebius (d i) : ℝ) * (d i : ℝ)| =
        ∏ i : Fin k, (d i : ℝ) := by
      rw [Finset.abs_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      have hd_abs : |(d i : ℝ)| = (d i : ℝ) := abs_of_pos (Nat.cast_pos.mpr (valid_pos_at hd i))
      rw [abs_mul, hd_abs]
      have hsq : Squarefree (d i) := valid_squarefree_at hd i
      have h1 : |(ArithmeticFunction.moebius (d i) : ℝ)| = 1 := by
        rw [moebius_real_eq_prod_primeFactors hsq, Finset.abs_prod]
        simp
      rw [h1, one_mul]
    rw [hprod_le]
    -- Bound the sum over r by (1 / prod phi(di)) times (sum{s in Icc 1 R} 1 / phi(s))^k
    have hsum_nonneg : 0 ≤ ∑ r ∈ (validSet k W R).filter (fun r => ∀ i, d i ∣ r i),
        y r / (∏ i : Fin k, (Nat.totient (r i) : ℝ)) :=
      Finset.sum_nonneg fun r _ => div_nonneg (hy0 r) (Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _)
    rw [abs_of_nonneg hsum_nonneg]
    -- Map r -> (fun i => r i / d i) injectively into (Fin k -> Icc 1 R)
    let qMap : (Fin k → ℕ) → (Fin k → ℕ) := fun r i => r i / d i
    have hq_mem : ∀ r ∈ (validSet k W R).filter (fun r => ∀ i, d i ∣ r i),
        qMap r ∈ Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R) := by
      intro r hr
      have hrV := mem_validSet_iff.mp (Finset.mem_filter.mp hr).1
      have hdvd := (Finset.mem_filter.mp hr).2
      rw [Fintype.mem_piFinset]
      intro i
      rw [Finset.mem_Icc]
      exact ⟨Nat.div_pos (Nat.le_of_dvd (valid_pos_at hrV i) (hdvd i)) (valid_pos_at hd i),
        le_trans (Nat.div_le_self _ _) (valid_le_R_at hrV i)⟩
    have hq_inj : Set.InjOn qMap (((validSet k W R).filter (fun r => ∀ i, d i ∣ r i)) : Set (Fin k → ℕ)) := by
      intro r₁ hr₁ r₂ hr₂ hEq
      have hd₁ := (Finset.mem_filter.mp hr₁).2
      have hd₂ := (Finset.mem_filter.mp hr₂).2
      funext i
      rw [← Nat.mul_div_cancel' (hd₁ i), ← Nat.mul_div_cancel' (hd₂ i)]
      exact congrArg (d i * ·) (congrFun hEq i)
    have hsum_le :
        (∏ i : Fin k, (d i : ℝ)) *
        ∑ r ∈ (validSet k W R).filter (fun r => ∀ i, d i ∣ r i),
          y r / (∏ i : Fin k, (Nat.totient (r i) : ℝ)) ≤
        (∏ i : Fin k, ((d i : ℝ) / (Nat.totient (d i) : ℝ))) *
          (∑ s ∈ Finset.Icc 1 R, (1 / (Nat.totient s : ℝ))) ^ k := by
      have hpi_eq : (∑ s ∈ Finset.Icc 1 R, (1 / (Nat.totient s : ℝ))) ^ k =
          ∑ q ∈ Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R),
            ∏ i : Fin k, (1 / (Nat.totient (q i) : ℝ)) := by
        rw [sum_piFinset_prod (f := fun (_ : Fin k) s => 1 / (Nat.totient s : ℝ))]
        simp
      rw [hpi_eq, Finset.mul_sum, Finset.mul_sum]
      calc ∑ r ∈ (validSet k W R).filter (fun r => ∀ i, d i ∣ r i),
              (∏ i : Fin k, (d i : ℝ)) * (y r / (∏ i : Fin k, (Nat.totient (r i) : ℝ)))
          ≤ ∑ r ∈ (validSet k W R).filter (fun r => ∀ i, d i ∣ r i),
              (∏ i : Fin k, ((d i : ℝ) / (Nat.totient (d i) : ℝ))) *
                (∏ i : Fin k, (1 / (Nat.totient (qMap r i) : ℝ))) := by
            refine Finset.sum_le_sum fun r hr => ?_
            have hrV := mem_validSet_iff.mp (Finset.mem_filter.mp hr).1
            have hdvd := (Finset.mem_filter.mp hr).2
            have htot_r : ∏ i : Fin k, (Nat.totient (r i) : ℝ) =
                (∏ i : Fin k, (Nat.totient (d i) : ℝ)) * (∏ i : Fin k, (Nat.totient (qMap r i) : ℝ)) := by
              rw [← Finset.prod_mul_distrib]
              refine Finset.prod_congr rfl fun i _ => ?_
              have hmul : d i * qMap r i = r i := Nat.mul_div_cancel' (hdvd i)
              have hc : Nat.Coprime (d i) (qMap r i) :=
                Nat.coprime_of_squarefree_mul (hmul.symm ▸ valid_squarefree_at hrV i)
              have : Nat.totient (r i) = Nat.totient (d i) * Nat.totient (qMap r i) := by
                conv_lhs => rw [← hmul]; exact Nat.totient_mul hc
              exact_mod_cast this
            rw [htot_r, Finset.prod_div_distrib, Finset.prod_div_distrib, Finset.prod_const_one]
            have hden_pos : (0 : ℝ) < (∏ i : Fin k, (Nat.totient (d i) : ℝ)) *
                (∏ i : Fin k, (Nat.totient (qMap r i) : ℝ)) := by
              refine mul_pos (Finset.prod_pos fun i _ => Nat.cast_pos.mpr (Nat.totient_pos.mpr (valid_pos_at hd i)))
                (Finset.prod_pos fun i _ => Nat.cast_pos.mpr (Nat.totient_pos.mpr
                  (Nat.div_pos (Nat.le_of_dvd (valid_pos_at hrV i) (hdvd i)) (valid_pos_at hd i))))
            calc (∏ i : Fin k, (d i : ℝ)) *
                  (y r / ((∏ i : Fin k, (Nat.totient (d i) : ℝ)) * (∏ i : Fin k, (Nat.totient (qMap r i) : ℝ))))
                ≤ (∏ i : Fin k, (d i : ℝ)) *
                  (1 / ((∏ i : Fin k, (Nat.totient (d i) : ℝ)) * (∏ i : Fin k, (Nat.totient (qMap r i) : ℝ)))) :=
                  mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (hy1 r) hden_pos.le)
                    (Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _)
              _ = _ := by ring
        _ = ∑ q ∈ ((validSet k W R).filter (fun r => ∀ i, d i ∣ r i)).image qMap,
              (∏ i : Fin k, ((d i : ℝ) / (Nat.totient (d i) : ℝ))) *
                (∏ i : Fin k, (1 / (Nat.totient (q i) : ℝ))) := by
            rw [Finset.sum_image (f := fun q => (∏ i : Fin k, ((d i : ℝ) / (Nat.totient (d i) : ℝ))) *
              (∏ i : Fin k, (1 / (Nat.totient (q i) : ℝ)))) hq_inj]
        _ ≤ ∑ q ∈ Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R),
              (∏ i : Fin k, ((d i : ℝ) / (Nat.totient (d i) : ℝ))) *
                (∏ i : Fin k, (1 / (Nat.totient (q i) : ℝ))) :=
            Finset.sum_le_sum_of_subset_of_nonneg
              (fun q hq => by rcases Finset.mem_image.mp hq with ⟨r, hr, rfl⟩; exact hq_mem r hr)
              (fun _ _ _ => mul_nonneg (Finset.prod_nonneg fun _ _ => by positivity)
                (Finset.prod_nonneg fun _ _ => by positivity))
    -- Bound each factor by (2 * log R + 2)
    have hfac1 : ∏ i : Fin k, ((d i : ℝ) / (Nat.totient (d i) : ℝ)) ≤ (2 * Real.log R + 2) ^ k := by
      calc ∏ i : Fin k, ((d i : ℝ) / (Nat.totient (d i) : ℝ))
          ≤ ∏ _i : Fin k, (2 * Real.log R + 2) := by
            refine Finset.prod_le_prod (fun _ _ => by positivity) fun i _ => ?_
            have h1 := div_totient_le_two_mul_log_add_one (valid_pos_at hd i)
            have h2 : Real.log (d i : ℝ) ≤ Real.log (R : ℝ) :=
              Real.log_le_log (Nat.cast_pos.mpr (valid_pos_at hd i)) (Nat.cast_le.mpr (valid_le_R_at hd i))
            linarith
        _ = (2 * Real.log R + 2) ^ k := by simp
    have hfac2 : ∑ s ∈ Finset.Icc 1 R, (1 / (Nat.totient s : ℝ)) ≤ (2 * Real.log R + 2) ^ 2 := by
      calc ∑ s ∈ Finset.Icc 1 R, (1 / (Nat.totient s : ℝ))
          = ∑ s ∈ Finset.Icc 1 R, ((s : ℝ) / (Nat.totient s : ℝ)) * (1 / (s : ℝ)) := by
            refine Finset.sum_congr rfl fun s hs => ?_
            have hs_ne : (s : ℝ) ≠ 0 := (Nat.cast_pos.mpr (Finset.mem_Icc.mp hs).1).ne'
            field_simp
        _ ≤ ∑ s ∈ Finset.Icc 1 R, (2 * Real.log R + 2) * (1 / (s : ℝ)) := by
            refine Finset.sum_le_sum fun s hs => ?_
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            have h1 := div_totient_le_two_mul_log_add_one (Finset.mem_Icc.mp hs).1
            have h2 : Real.log (s : ℝ) ≤ Real.log (R : ℝ) :=
              Real.log_le_log (Nat.cast_pos.mpr (Finset.mem_Icc.mp hs).1)
                (Nat.cast_le.mpr (Finset.mem_Icc.mp hs).2)
            linarith
        _ = (2 * Real.log R + 2) * ∑ s ∈ Finset.Icc 1 R, (1 / (s : ℝ)) := (Finset.mul_sum ..).symm
        _ ≤ (2 * Real.log R + 2) * (2 * Real.log R + 2) :=
            mul_le_mul_of_nonneg_left (by linarith [harmonic_le_log_add_one hR]) (by linarith)
        _ = (2 * Real.log R + 2) ^ 2 := (sq _).symm
    calc (∏ i : Fin k, (d i : ℝ)) *
          ∑ r ∈ (validSet k W R).filter (fun r => ∀ i, d i ∣ r i),
            y r / (∏ i : Fin k, (Nat.totient (r i) : ℝ))
        ≤ (∏ i : Fin k, ((d i : ℝ) / (Nat.totient (d i) : ℝ))) *
            (∑ s ∈ Finset.Icc 1 R, (1 / (Nat.totient s : ℝ))) ^ k := hsum_le
      _ ≤ (2 * Real.log R + 2) ^ k * ((2 * Real.log R + 2) ^ 2) ^ k :=
          mul_le_mul hfac1
            (pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => by positivity) hfac2 k)
            (by positivity) (by positivity)
      _ = (2 * Real.log R + 2) ^ (3 * k) := by rw [← pow_mul, ← pow_add]; ring_nf
  · rw [if_neg hd, abs_zero]
    have hlogR_nonneg : 0 ≤ Real.log (R : ℝ) := Real.log_nonneg (by exact_mod_cast hR)
    positivity

/-- Upper bound on M1 in terms of the diagonal sum T1 plus O(k^2 / D0) times MU^k. -/
lemma M1_le_T1_add_err {k D0 R U : ℕ} (hD : 2 * k ^ 2 + 10 ≤ D0) (hR : 1 ≤ R) (_hUR : U ≤ R)
    (y : (Fin k → ℕ) → ℝ) (hy0 : ∀ r, 0 ≤ y r) (hy1 : ∀ r, y r ≤ 1)
    (hy_supp : ∀ r, (∃ i, U < r i) → y r = 0) :
    let W := primorial D0
    let M_U := ∑ s ∈ (Finset.Icc 1 U).filter (fun s => Squarefree s ∧ Nat.Coprime s W),
      (1 / (Nat.totient s : ℝ))
    ∑ d ∈ validSet k W R,
      ∑ e ∈ (validSet k W R).filter (fun e => ∀ i j : Fin k, i ≠ j → Nat.Coprime (d i) (e j)),
        (lambdaOfY k W R y d * lambdaOfY k W R y e) / (∏ i : Fin k, (Nat.lcm (d i) (e i) : ℝ)) ≤
    (∑ r ∈ validSet k W R, y r ^ 2 / (∏ i : Fin k, (Nat.totient (r i) : ℝ))) +
      (2 * (k : ℝ) ^ 2 / ((D0 : ℝ) - 2)) * M_U ^ k := by
  classical
  intro W M_U
  rw [M1_eq_matrix_sum]
  let isDiag : (Fin k × Fin k → ℕ) → Prop := fun m => ∀ p : Fin k × Fin k, p.1 ≠ p.2 → m p = 1
  rw [← Finset.sum_filter_add_sum_filter_not (validMatSet k W R) isDiag]
  -- Part 1: diagonal matrices give exactly T_1
  have hdiag :
      ∑ m ∈ (validMatSet k W R).filter isDiag,
        (∏ p : Fin k × Fin k,
          if p.1 = p.2 then 1 / (Nat.totient (m p) : ℝ)
          else (ArithmeticFunction.moebius (m p) : ℝ) / (Nat.totient (m p) : ℝ) ^ 2) *
        y (rowProd m) * y (colProd m) =
      ∑ r ∈ validSet k W R, y r ^ 2 / (∏ i : Fin k, (Nat.totient (r i) : ℝ)) := by
    refine Finset.sum_bij (fun m _ i => m (i, i)) ?_ ?_ ?_ ?_
    · intro m hm
      have hmV := mem_validMatSet_iff.mp (Finset.mem_filter.mp hm).1
      have hmd := (Finset.mem_filter.mp hm).2
      rw [mem_validSet_iff]
      have hrow_eq : rowProd m = fun i => m (i, i) := by
        funext i
        unfold rowProd
        rw [Finset.prod_eq_single i]
        · intro j _ hji; exact hmd (i, j) (Ne.symm hji)
        · intro h; exact absurd (Finset.mem_univ i) h
      rw [← hrow_eq]
      exact validMat_rowProd_valid hmV
    · intro m₁ hm₁ m₂ hm₂ hEq
      have hd₁ := (Finset.mem_filter.mp hm₁).2
      have hd₂ := (Finset.mem_filter.mp hm₂).2
      funext ⟨i, j⟩
      by_cases hij : i = j
      · subst hij; exact congrFun hEq i
      · rw [hd₁ (i, j) hij, hd₂ (i, j) hij]
    · intro r hr
      have hrV := mem_validSet_iff.mp hr
      let m : Fin k × Fin k → ℕ := fun p => if p.1 = p.2 then r p.1 else 1
      have hprod_m : ∏ p : Fin k × Fin k, m p = ∏ i : Fin k, r i := by
        rw [Fintype.prod_prod_type]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [Finset.prod_eq_single i]
        · simp [m]
        · intro j _ hji; simp [m, Ne.symm hji]
        · intro h; exact absurd (Finset.mem_univ i) h
      refine ⟨m, Finset.mem_filter.mpr ⟨mem_validMatSet_iff.mpr ?_, ?_⟩, ?_⟩
      · unfold ValidMat; rw [hprod_m]; exact hrV
      · intro p hp; simp [m, hp]
      · funext i; simp [m]
    · intro m hm
      have hmd := (Finset.mem_filter.mp hm).2
      have hrow_eq : rowProd m = fun i => m (i, i) := by
        funext i; unfold rowProd
        rw [Finset.prod_eq_single i]
        · intro j _ hji; exact hmd (i, j) (Ne.symm hji)
        · intro h; exact absurd (Finset.mem_univ i) h
      have hcol_eq : colProd m = fun i => m (i, i) := by
        funext j; unfold colProd
        rw [Finset.prod_eq_single j]
        · intro i _ hij; exact hmd (i, j) hij
        · intro h; exact absurd (Finset.mem_univ j) h
      have hprod_eq :
          (∏ p : Fin k × Fin k,
            if p.1 = p.2 then 1 / (Nat.totient (m p) : ℝ)
            else (ArithmeticFunction.moebius (m p) : ℝ) / (Nat.totient (m p) : ℝ) ^ 2) =
          1 / (∏ i : Fin k, (Nat.totient (m (i, i)) : ℝ)) := by
        rw [Fintype.prod_prod_type, one_div, ← Finset.prod_inv_distrib]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [Finset.prod_eq_single i]
        · simp [one_div]
        · intro j _ hji
          rw [if_neg (Ne.symm hji), hmd (i, j) (Ne.symm hji)]
          simp
        · intro h; exact absurd (Finset.mem_univ i) h
      rw [hrow_eq, hcol_eq, hprod_eq]
      ring
  rw [hdiag]
  -- Part 2: bound off-diagonal matrices
  refine add_le_add_right ?_ _
  let S_U := (Finset.Icc 1 U).filter (fun s => Squarefree s ∧ Nat.Coprime s W)
  let S_R := (Finset.Icc 1 R).filter (fun s => Squarefree s ∧ Nat.Coprime s W)
  let Off := (Finset.univ : Finset (Fin k × Fin k)).filter (fun p => p.1 ≠ p.2)
  let dom : Fin k × Fin k → Finset ℕ := fun p => if p.1 = p.2 then S_U else S_R
  let A_set := (Fintype.piFinset dom).filter (fun m => ¬ isDiag m)
  have hoff_le :
      ∑ m ∈ (validMatSet k W R).filter (fun m => ¬ isDiag m),
        (∏ p : Fin k × Fin k,
          if p.1 = p.2 then 1 / (Nat.totient (m p) : ℝ)
          else (ArithmeticFunction.moebius (m p) : ℝ) / (Nat.totient (m p) : ℝ) ^ 2) *
        y (rowProd m) * y (colProd m) ≤
      ∑ m ∈ A_set,
        ∏ p : Fin k × Fin k,
          if p.1 = p.2 then 1 / (Nat.totient (m p) : ℝ) else 1 / (Nat.totient (m p) : ℝ) ^ 2 := by
    -- Filter to matrices where all diagonal entries are <= U (others have y(rowProd m) = 0)
    let GoodOff := ((validMatSet k W R).filter (fun m => ¬ isDiag m)).filter
      (fun m => ∀ i : Fin k, m (i, i) ≤ U)
    have hzero :
        ∑ m ∈ (validMatSet k W R).filter (fun m => ¬ isDiag m),
          (∏ p : Fin k × Fin k,
            if p.1 = p.2 then 1 / (Nat.totient (m p) : ℝ)
            else (ArithmeticFunction.moebius (m p) : ℝ) / (Nat.totient (m p) : ℝ) ^ 2) *
          y (rowProd m) * y (colProd m) =
        ∑ m ∈ GoodOff,
          (∏ p : Fin k × Fin k,
            if p.1 = p.2 then 1 / (Nat.totient (m p) : ℝ)
            else (ArithmeticFunction.moebius (m p) : ℝ) / (Nat.totient (m p) : ℝ) ^ 2) *
          y (rowProd m) * y (colProd m) := by
      symm
      refine Finset.sum_subset (Finset.filter_subset _ _) ?_
      intro m hm hnot
      have hex : ∃ i : Fin k, U < m (i, i) := by
        by_contra hall
        push Not at hall
        exact hnot (Finset.mem_filter.mpr ⟨hm, hall⟩)
      rcases hex with ⟨i, hi⟩
      have hmV := mem_validMatSet_iff.mp (Finset.mem_filter.mp hm).1
      have hle_row : m (i, i) ≤ rowProd m i :=
        Nat.le_of_dvd (valid_pos_at (validMat_rowProd_valid hmV) i)
          (Finset.dvd_prod_of_mem (fun j => m (i, j)) (Finset.mem_univ i))
      have hy0' : y (rowProd m) = 0 := hy_supp (rowProd m) ⟨i, lt_of_lt_of_le hi hle_row⟩
      simp [hy0']
    rw [hzero]
    have hsub : GoodOff ⊆ A_set := by
      intro m hm
      rw [Finset.mem_filter, Finset.mem_filter, mem_validMatSet_iff] at hm
      rcases hm with ⟨⟨hmV, hnd⟩, hdiagU⟩
      rw [Finset.mem_filter, Fintype.mem_piFinset]
      refine ⟨?_, hnd⟩
      intro p
      have hp_dvd : m p ∣ ∏ q : Fin k × Fin k, m q := Finset.dvd_prod_of_mem m (Finset.mem_univ p)
      have hp_sq : Squarefree (m p) := hmV.1.squarefree_of_dvd hp_dvd
      have hp_cop : Nat.Coprime (m p) W := hmV.2.1.coprime_dvd_left hp_dvd
      have hp_pos : 1 ≤ m p := squarefree_pos hp_sq
      have hp_leR : m p ≤ R := le_trans (Nat.le_of_dvd (squarefree_pos hmV.1) hp_dvd) hmV.2.2
      dsimp only [dom]
      by_cases heq : p.1 = p.2
      · rw [if_pos heq]
        have hp_leU : m p ≤ U := by
          rcases p with ⟨i, j⟩
          dsimp only at heq
          subst heq
          exact hdiagU i
        exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp_pos, hp_leU⟩, hp_sq, hp_cop⟩
      · rw [if_neg heq]
        exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp_pos, hp_leR⟩, hp_sq, hp_cop⟩
    calc ∑ m ∈ GoodOff,
            (∏ p : Fin k × Fin k,
              if p.1 = p.2 then 1 / (Nat.totient (m p) : ℝ)
              else (ArithmeticFunction.moebius (m p) : ℝ) / (Nat.totient (m p) : ℝ) ^ 2) *
            y (rowProd m) * y (colProd m)
        ≤ ∑ m ∈ GoodOff,
            ∏ p : Fin k × Fin k,
              if p.1 = p.2 then 1 / (Nat.totient (m p) : ℝ) else 1 / (Nat.totient (m p) : ℝ) ^ 2 := by
          refine Finset.sum_le_sum fun m hm => ?_
          have h1 := le_abs_self ((∏ p : Fin k × Fin k,
            if p.1 = p.2 then 1 / (Nat.totient (m p) : ℝ)
            else (ArithmeticFunction.moebius (m p) : ℝ) / (Nat.totient (m p) : ℝ) ^ 2) *
            y (rowProd m) * y (colProd m))
          refine le_trans h1 ?_
          rw [abs_mul, abs_mul, abs_of_nonneg (hy0 _), abs_of_nonneg (hy0 _), Finset.abs_prod]
          have hprod_le :
              ∏ p : Fin k × Fin k,
                |if p.1 = p.2 then 1 / (Nat.totient (m p) : ℝ)
                 else (ArithmeticFunction.moebius (m p) : ℝ) / (Nat.totient (m p) : ℝ) ^ 2| ≤
              ∏ p : Fin k × Fin k,
                if p.1 = p.2 then 1 / (Nat.totient (m p) : ℝ) else 1 / (Nat.totient (m p) : ℝ) ^ 2 := by
            refine Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun p _ => ?_
            split_ifs
            · rw [abs_of_nonneg (div_nonneg (by norm_num) (Nat.cast_nonneg _))]
            · have hden : (0 : ℝ) ≤ (Nat.totient (m p) : ℝ) ^ 2 := sq_nonneg _
              rw [abs_div, abs_of_nonneg hden]
              refine div_le_div_of_nonneg_right ?_ hden
              by_cases hsq : Squarefree (m p)
              · rw [ArithmeticFunction.moebius_apply_of_squarefree hsq]; simp
              · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]; simp
          have hy_prod_le : y (rowProd m) * y (colProd m) ≤ 1 := by
            nlinarith [hy0 (rowProd m), hy1 (rowProd m), hy0 (colProd m), hy1 (colProd m)]
          have hp_nonneg : 0 ≤ ∏ p : Fin k × Fin k,
              if p.1 = p.2 then 1 / (Nat.totient (m p) : ℝ) else 1 / (Nat.totient (m p) : ℝ) ^ 2 :=
            Finset.prod_nonneg (fun p _ => by split_ifs <;> positivity)
          have habs_nonneg : 0 ≤ ∏ x : Fin k × Fin k,
              |if x.1 = x.2 then 1 / (Nat.totient (m x) : ℝ)
               else (ArithmeticFunction.moebius (m x) : ℝ) / (Nat.totient (m x) : ℝ) ^ 2| :=
            Finset.prod_nonneg (fun _ _ => abs_nonneg _)
          calc (∏ x : Fin k × Fin k,
                |if x.1 = x.2 then 1 / (Nat.totient (m x) : ℝ)
                 else (ArithmeticFunction.moebius (m x) : ℝ) / (Nat.totient (m x) : ℝ) ^ 2|) *
                y (rowProd m) * y (colProd m)
              = (∏ x : Fin k × Fin k,
                |if x.1 = x.2 then 1 / (Nat.totient (m x) : ℝ)
                 else (ArithmeticFunction.moebius (m x) : ℝ) / (Nat.totient (m x) : ℝ) ^ 2|) *
                (y (rowProd m) * y (colProd m)) := by ring
            _ ≤ (∏ p : Fin k × Fin k,
                if p.1 = p.2 then 1 / (Nat.totient (m p) : ℝ) else 1 / (Nat.totient (m p) : ℝ) ^ 2) * 1 :=
                mul_le_mul hprod_le hy_prod_le (mul_nonneg (hy0 _) (hy0 _)) hp_nonneg
            _ = _ := mul_one _
      _ ≤ ∑ m ∈ A_set,
            ∏ p : Fin k × Fin k,
              if p.1 = p.2 then 1 / (Nat.totient (m p) : ℝ) else 1 / (Nat.totient (m p) : ℝ) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun m _ _ => Finset.prod_nonneg (fun p _ => by split_ifs <;> positivity))
  -- Evaluate sum over A_set = sum over piFinset dom - sum over diagonal in piFinset dom
  have hA_eq :
      ∑ m ∈ A_set,
        (∏ p : Fin k × Fin k,
          if p.1 = p.2 then 1 / (Nat.totient (m p) : ℝ) else 1 / (Nat.totient (m p) : ℝ) ^ 2) =
      M_U ^ k * ((∑ s ∈ S_R, (1 / (Nat.totient s : ℝ) ^ 2)) ^ Off.card - 1) := by
    have hsplit := Finset.sum_filter_add_sum_filter_not (Fintype.piFinset dom) isDiag
      (fun m => ∏ p : Fin k × Fin k,
        if p.1 = p.2 then 1 / (Nat.totient (m p) : ℝ) else 1 / (Nat.totient (m p) : ℝ) ^ 2)
    have htot :
        ∑ m ∈ Fintype.piFinset dom,
          (∏ p : Fin k × Fin k,
            if p.1 = p.2 then 1 / (Nat.totient (m p) : ℝ) else 1 / (Nat.totient (m p) : ℝ) ^ 2) =
        M_U ^ k * (∑ s ∈ S_R, (1 / (Nat.totient s : ℝ) ^ 2)) ^ Off.card := by
      rw [sum_piFinset_prod (f := fun (p : Fin k × Fin k) x =>
        if p.1 = p.2 then 1 / (Nat.totient x : ℝ) else 1 / (Nat.totient x : ℝ) ^ 2)]
      rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun p : Fin k × Fin k => p.1 = p.2)]
      congr 1
      · have hcard : ((Finset.univ : Finset (Fin k × Fin k)).filter (fun p => p.1 = p.2)).card = k := by
          have hbij : (Finset.univ : Finset (Fin k × Fin k)).filter (fun p => p.1 = p.2) =
              Finset.univ.image (fun i : Fin k => (i, i)) := by
            ext ⟨i, j⟩
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
            exact ⟨fun h => ⟨i, by subst h; rfl⟩, by rintro ⟨l, h⟩; cases h; rfl⟩
          rw [hbij, Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h),
            Finset.card_univ, Fintype.card_fin]
        calc ∏ p ∈ Finset.univ.filter (fun p : Fin k × Fin k => p.1 = p.2),
                ∑ a ∈ dom p, (if p.1 = p.2 then 1 / (Nat.totient a : ℝ) else 1 / (Nat.totient a : ℝ) ^ 2)
            = ∏ _p ∈ Finset.univ.filter (fun p : Fin k × Fin k => p.1 = p.2), M_U := by
              refine Finset.prod_congr rfl fun p hp => ?_
              have heq := (Finset.mem_filter.mp hp).2
              simp [dom, heq, M_U, S_U]
          _ = M_U ^ k := by rw [Finset.prod_const, hcard]
      · calc ∏ p ∈ Finset.univ.filter (fun p : Fin k × Fin k => ¬ p.1 = p.2),
                ∑ a ∈ dom p, (if p.1 = p.2 then 1 / (Nat.totient a : ℝ) else 1 / (Nat.totient a : ℝ) ^ 2)
            = ∏ _p ∈ Off, ∑ s ∈ S_R, (1 / (Nat.totient s : ℝ) ^ 2) := by
              refine Finset.prod_congr rfl fun p hp => ?_
              have hne := (Finset.mem_filter.mp hp).2
              simp [dom, hne]
          _ = (∑ s ∈ S_R, (1 / (Nat.totient s : ℝ) ^ 2)) ^ Off.card := Finset.prod_const _
    have hdiag_pi :
        ∑ m ∈ (Fintype.piFinset dom).filter isDiag,
          (∏ p : Fin k × Fin k,
            if p.1 = p.2 then 1 / (Nat.totient (m p) : ℝ) else 1 / (Nat.totient (m p) : ℝ) ^ 2) =
        M_U ^ k := by
      have h1R : 1 ∈ S_R :=
        Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_refl 1, hR⟩,
          squarefree_one, Nat.coprime_one_left _⟩
      have hbij :
          ∑ m ∈ (Fintype.piFinset dom).filter isDiag,
            (∏ p : Fin k × Fin k,
              if p.1 = p.2 then 1 / (Nat.totient (m p) : ℝ) else 1 / (Nat.totient (m p) : ℝ) ^ 2) =
          ∑ u ∈ Fintype.piFinset (fun _ : Fin k => S_U),
            ∏ i : Fin k, (1 / (Nat.totient (u i) : ℝ)) := by
        refine Finset.sum_bij (fun m _ i => m (i, i)) ?_ ?_ ?_ ?_
        · intro m hm
          have hpi := Fintype.mem_piFinset.mp (Finset.mem_filter.mp hm).1
          rw [Fintype.mem_piFinset]
          intro i
          simpa [dom] using hpi (i, i)
        · intro m₁ hm₁ m₂ hm₂ hEq
          have hd₁ := (Finset.mem_filter.mp hm₁).2
          have hd₂ := (Finset.mem_filter.mp hm₂).2
          funext ⟨i, j⟩
          by_cases hij : i = j
          · subst hij; exact congrFun hEq i
          · rw [hd₁ (i, j) hij, hd₂ (i, j) hij]
        · intro u hu
          have hu' := Fintype.mem_piFinset.mp hu
          refine ⟨fun p => if p.1 = p.2 then u p.1 else 1, Finset.mem_filter.mpr ⟨?_, ?_⟩, ?_⟩
          · rw [Fintype.mem_piFinset]
            intro p
            dsimp only [dom]
            split_ifs
            · exact hu' p.1
            · exact h1R
          · intro p hp; simp [hp]
          · funext i; simp
        · intro m hm
          have hmd := (Finset.mem_filter.mp hm).2
          rw [Fintype.prod_prod_type]
          refine Finset.prod_congr rfl fun i _ => ?_
          rw [Finset.prod_eq_single i]
          · simp
          · intro j _ hji
            rw [if_neg (Ne.symm hji), hmd (i, j) (Ne.symm hji)]
            simp
          · intro h; exact absurd (Finset.mem_univ i) h
      rw [hbij, sum_piFinset_prod (f := fun _ x => 1 / (Nat.totient x : ℝ))]
      simp [M_U, S_U]
    linarith
  have hOff_card : Off.card ≤ k ^ 2 := by
    calc Off.card ≤ (Finset.univ : Finset (Fin k × Fin k)).card := Finset.card_filter_le _ _
      _ = k ^ 2 := by simp [sq]
  have hSR_ge1 : 1 ≤ ∑ s ∈ S_R, (1 / (Nat.totient s : ℝ) ^ 2) := by
    have h1R : 1 ∈ S_R :=
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_refl 1, hR⟩, squarefree_one, Nat.coprime_one_left _⟩
    calc (1 : ℝ) = 1 / (Nat.totient 1 : ℝ) ^ 2 := by simp
      _ ≤ ∑ s ∈ S_R, (1 / (Nat.totient s : ℝ) ^ 2) :=
        Finset.single_le_sum (f := fun s => 1 / (Nat.totient s : ℝ) ^ 2)
          (fun s _ => div_nonneg (by norm_num) (sq_nonneg _)) h1R
  have hSR_le : ∑ s ∈ S_R, (1 / (Nat.totient s : ℝ) ^ 2) ≤ Real.exp (1 / ((D0 : ℝ) - 2)) :=
    sum_inv_totient_sq_le_exp (by omega)
  have hpow_le : (∑ s ∈ S_R, (1 / (Nat.totient s : ℝ) ^ 2)) ^ Off.card - 1 ≤
      2 * (k : ℝ) ^ 2 / ((D0 : ℝ) - 2) := by
    have h1 : (∑ s ∈ S_R, (1 / (Nat.totient s : ℝ) ^ 2)) ^ Off.card ≤
        (Real.exp (1 / ((D0 : ℝ) - 2))) ^ (k ^ 2) := by
      calc (∑ s ∈ S_R, (1 / (Nat.totient s : ℝ) ^ 2)) ^ Off.card
          ≤ (∑ s ∈ S_R, (1 / (Nat.totient s : ℝ) ^ 2)) ^ (k ^ 2) :=
            pow_le_pow_right₀ hSR_ge1 hOff_card
        _ ≤ (Real.exp (1 / ((D0 : ℝ) - 2))) ^ (k ^ 2) :=
            pow_le_pow_left₀ (by linarith) hSR_le _
    rw [← Real.exp_nat_mul] at h1
    have hD_pos2 : (0 : ℝ) < (D0 : ℝ) - 2 := by
      have : (10 : ℝ) ≤ D0 := by exact_mod_cast (by omega : 10 ≤ D0)
      linarith
    have ht0 : 0 ≤ ((k ^ 2 : ℕ) : ℝ) * (1 / ((D0 : ℝ) - 2)) :=
      mul_nonneg (Nat.cast_nonneg _) (div_nonneg (by norm_num) hD_pos2.le)
    have ht1 : ((k ^ 2 : ℕ) : ℝ) * (1 / ((D0 : ℝ) - 2)) ≤ 1 / 2 := by
      have hD_r : (2 * (k : ℝ) ^ 2 + 10) ≤ (D0 : ℝ) := by exact_mod_cast hD
      push_cast
      rw [mul_one_div, div_le_div_iff₀ hD_pos2 (by norm_num)]
      linarith
    have h2 := exp_sub_one_le_two_mul ht0 ht1
    push_cast at h1 h2
    have heq : 2 * ((k : ℝ) ^ 2 * (1 / ((D0 : ℝ) - 2))) = 2 * (k : ℝ) ^ 2 / ((D0 : ℝ) - 2) := by ring
    linarith
  have hMU_nonneg : 0 ≤ M_U ^ k := pow_nonneg (Finset.sum_nonneg (fun _ _ => by positivity)) k
  calc ∑ m ∈ (validMatSet k W R).filter (fun m => ¬ isDiag m),
          (∏ p : Fin k × Fin k,
            if p.1 = p.2 then 1 / (Nat.totient (m p) : ℝ)
            else (ArithmeticFunction.moebius (m p) : ℝ) / (Nat.totient (m p) : ℝ) ^ 2) *
          y (rowProd m) * y (colProd m)
      ≤ M_U ^ k * ((∑ s ∈ S_R, (1 / (Nat.totient s : ℝ) ^ 2)) ^ Off.card - 1) := by
        rw [← hA_eq]; exact hoff_le
    _ ≤ M_U ^ k * (2 * (k : ℝ) ^ 2 / ((D0 : ℝ) - 2)) :=
        mul_le_mul_of_nonneg_left hpow_le hMU_nonneg
    _ = (2 * (k : ℝ) ^ 2 / ((D0 : ℝ) - 2)) * M_U ^ k := mul_comm _ _

/-- Clean main term Ybar(idx, u) for S2(idx). -/
noncomputable def YBar {k : ℕ} (W R : ℕ) (y : (Fin k → ℕ) → ℝ) (idx : Fin k) (u : Fin k → ℕ) : ℝ := by
  classical
  exact ∑ r ∈ (validSet k W R).filter (fun r => ∀ i ∈ Finset.univ.erase idx, r i = u i),
    y r / (Nat.totient (r idx) : ℝ)

/-- Approximation |yMod - YBar| <= (3 * k / (D0 - 2)) * Z1_bound and support of yMod. -/
lemma yMod_approx {k D0 R U : ℕ} (hD : 2 * k + 10 ≤ D0) (hR : 1 ≤ R) (_hUR : U ≤ R)
    (y : (Fin k → ℕ) → ℝ) (gBound : ℕ → ℝ)
    (hy0 : ∀ r, 0 ≤ y r) (hg0 : ∀ n, 0 ≤ gBound n)
    (hy_supp : ∀ r, (∃ i, U < r i) → y r = 0)
    (hy_le_g : ∀ r (idx : Fin k), y r ≤ gBound (r idx))
    (idx : Fin k) :
    let W := primorial D0
    let S_U := (Finset.Icc 1 U).filter (fun s => Squarefree s ∧ Nat.Coprime s W)
    let Z1B := ∑ s ∈ S_U, gBound s / (Nat.totient s : ℝ)
    (∀ a, (∃ i, U < a i) → yMod k W R y idx a = 0) ∧
    (∀ a, Valid W R a → a idx = 1 →
      0 ≤ YBar W R y idx a ∧
      YBar W R y idx a ≤ Z1B ∧
      |yMod k W R y idx a - YBar W R y idx a| ≤ (3 * (k : ℝ) / ((D0 : ℝ) - 2)) * Z1B ∧
      |yMod k W R y idx a| ≤ 2 * Z1B) := by
  classical
  intro W S_U Z1B
  have hZ1B_nonneg : 0 ≤ Z1B := Finset.sum_nonneg (fun s _ => div_nonneg (hg0 s) (Nat.cast_nonneg _))
  -- Part 1: support of yMod
  have hsupp : ∀ a, (∃ i, U < a i) → yMod k W R y idx a = 0 := by
    intro a ⟨i, hi⟩
    by_cases hcond : Valid W R a ∧ a idx = 1
    · rw [yMod_eq_sum y idx hcond.1 hcond.2]
      refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun r hr => ?_)
      by_cases hi_idx : i = idx
      · subst hi_idx
        -- a idx = 1 < U? No, U < a idx = 1 implies U = 0, so r idx >= 1 > U
        have hrV := mem_validSet_iff.mp (Finset.mem_filter.mp hr).1
        have hr_pos : 1 ≤ r i := valid_pos_at hrV i
        have hyr : y r = 0 := hy_supp r ⟨i, by omega⟩
        simp [hyr]
      · have hdvd : a i ∣ r i := (Finset.mem_filter.mp hr).2 i (Finset.mem_erase.mpr ⟨hi_idx, Finset.mem_univ i⟩)
        have hrV := mem_validSet_iff.mp (Finset.mem_filter.mp hr).1
        have hle : a i ≤ r i := Nat.le_of_dvd (valid_pos_at hrV i) hdvd
        have hyr : y r = 0 := hy_supp r ⟨i, lt_of_lt_of_le hi hle⟩
        simp [hyr]
    · unfold yMod; rw [if_neg hcond]
  refine ⟨hsupp, ?_⟩
  intro a ha ha_idx
  -- Helper: for any tuple b (with Valid W R b, b idx = 1), sum_{r : ∀ i ≠ idx, r i = b i} y r / phi(r idx) <= Z1B
  have hfiber_le_Z1B : ∀ b : Fin k → ℕ,
      ∑ r ∈ (validSet k W R).filter (fun r => ∀ i ∈ Finset.univ.erase idx, r i = b i),
        y r / (Nat.totient (r idx) : ℝ) ≤ Z1B := by
    intro b
    let F := (validSet k W R).filter (fun r => ∀ i ∈ Finset.univ.erase idx, r i = b i)
    let F_good := F.filter (fun r => r idx ≤ U)
    have hzero : ∑ r ∈ F, y r / (Nat.totient (r idx) : ℝ) =
        ∑ r ∈ F_good, y r / (Nat.totient (r idx) : ℝ) := by
      symm
      refine Finset.sum_subset (Finset.filter_subset _ _) fun r hr hnot => ?_
      have hgt : U < r idx := by
        by_contra hle; push Not at hle
        exact hnot (Finset.mem_filter.mpr ⟨hr, hle⟩)
      simp [hy_supp r ⟨idx, hgt⟩]
    rw [hzero]
    have hinj : Set.InjOn (fun r : Fin k → ℕ => r idx) (F_good : Set (Fin k → ℕ)) := by
      intro r₁ hr₁ r₂ hr₂ hEq
      have h1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hr₁).1).2
      have h2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hr₂).1).2
      funext i
      by_cases hi : i = idx
      · subst hi; exact hEq
      · rw [h1 i (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩),
          h2 i (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩)]
    have hsub : F_good.image (fun r => r idx) ⊆ S_U := by
      intro s hs
      rcases Finset.mem_image.mp hs with ⟨r, hr, rfl⟩
      have hrV := mem_validSet_iff.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).1
      have hrU := (Finset.mem_filter.mp hr).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨valid_pos_at hrV idx, hrU⟩,
        valid_squarefree_at hrV idx, valid_coprime_W_at hrV idx⟩
    calc ∑ r ∈ F_good, y r / (Nat.totient (r idx) : ℝ)
        ≤ ∑ r ∈ F_good, gBound (r idx) / (Nat.totient (r idx) : ℝ) :=
          Finset.sum_le_sum fun r _ => div_le_div_of_nonneg_right (hy_le_g r idx) (Nat.cast_nonneg _)
      _ = ∑ s ∈ F_good.image (fun r => r idx), gBound s / (Nat.totient s : ℝ) :=
          (Finset.sum_image (f := fun s => gBound s / (Nat.totient s : ℝ)) hinj).symm
      _ ≤ Z1B := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun s _ _ => div_nonneg (hg0 s) (Nat.cast_nonneg _))
  have hYBar_nonneg : 0 ≤ YBar W R y idx a :=
    Finset.sum_nonneg fun r _ => div_nonneg (hy0 r) (Nat.cast_nonneg _)
  have hYBar_le : YBar W R y idx a ≤ Z1B := hfiber_le_Z1B a
  -- Now bound |yMod - YBar| using yModeqsum
  rw [yMod_eq_sum y idx ha ha_idx]
  set P_a := ∏ i ∈ Finset.univ.erase idx, ((phi2 (a i) : ℝ) * (a i : ℝ) / (Nat.totient (a i) : ℝ) ^ 2)
  -- Bound 1 - 1 / (D0 - 2) <= P_a <= 1
  have hPa_bounds : 1 - 1 / ((D0 : ℝ) - 2) ≤ P_a ∧ P_a ≤ 1 := by
    have hPa_eq : P_a = ∏ p ∈ (∏ i ∈ Finset.univ.erase idx, a i).primeFactors,
        (1 - 1 / ((p : ℝ) - 1) ^ 2) := by
      have hprod_sq : Squarefree (∏ i ∈ Finset.univ.erase idx, a i) :=
        ha.1.squarefree_of_dvd (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.subset_univ _))
      have htot := totient_prod_of_squarefree hprod_sq
      have hphi2 := phi2_prod_of_squarefree hprod_sq
      have hcomb : P_a = (phi2 (∏ i ∈ Finset.univ.erase idx, a i) : ℝ) *
          ((∏ i ∈ Finset.univ.erase idx, a i : ℕ) : ℝ) /
          (Nat.totient (∏ i ∈ Finset.univ.erase idx, a i) : ℝ) ^ 2 := by
        dsimp only [P_a]
        rw [hphi2, htot, Finset.prod_div_distrib, Finset.prod_mul_distrib, Nat.cast_prod,
          Nat.cast_prod, Nat.cast_prod, Finset.prod_pow]
      rw [hcomb]
      set A := ∏ i ∈ Finset.univ.erase idx, a i
      have hA_cop : Nat.Coprime A W :=
        ha.2.1.coprime_dvd_left (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.subset_univ _))
      unfold phi2
      rw [totient_eq_prod_primeFactors_of_squarefree hprod_sq]
      conv_lhs =>
        arg 1
        arg 2
        rw [← squarefree_eq_prod_primeFactors hprod_sq]
      simp only [Nat.cast_prod, ← Finset.prod_pow]
      rw [← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]
      refine Finset.prod_congr rfl fun p hp => ?_
      have hpD : D0 < p := prime_gt_of_coprime_primorial hA_cop hp
      have hp1 : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
      have hp2 : ((p - 2 : ℕ) : ℝ) = (p : ℝ) - 2 := by rw [Nat.cast_sub (by omega)]; simp
      have hne1 : (p : ℝ) - 1 ≠ 0 := by
        have : (10 : ℝ) < p := by exact_mod_cast (by omega : 10 < p)
        linarith
      rw [hp1, hp2]
      field_simp
      ring
    rw [hPa_eq]
    set A := ∏ i ∈ Finset.univ.erase idx, a i
    have hA_cop : Nat.Coprime A W :=
      ha.2.1.coprime_dvd_left (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.subset_univ _))
    have hp_gt : ∀ p ∈ A.primeFactors, D0 < p := fun p hp => prime_gt_of_coprime_primorial hA_cop hp
    constructor
    · have h1 := prod_one_sub_ge_one_sub_sum A.primeFactors (fun p => 1 / ((p : ℝ) - 1) ^ 2)
        (fun _ _ => by positivity)
        (fun p hp => by
          have : (10 : ℝ) < p := by exact_mod_cast (by have := hp_gt p hp; omega : 10 < p)
          rw [div_le_one (sq_pos_of_pos (by linarith))]; nlinarith)
      have h2 := sum_inv_sub_sq_primes_le (D0 := D0) (c := 1) (by omega) A.primeFactors hp_gt
      have heq : (D0 : ℝ) - (1 : ℕ) - 1 = (D0 : ℝ) - 2 := by push_cast; ring
      rw [heq] at h2
      linarith
    · calc ∏ p ∈ A.primeFactors, (1 - 1 / ((p : ℝ) - 1) ^ 2)
          ≤ ∏ _p ∈ A.primeFactors, (1 : ℝ) := by
            refine Finset.prod_le_prod ?_ (fun p _ => by linarith [show (0 : ℝ) ≤ 1 / ((p : ℝ) - 1) ^ 2 by positivity])
            intro p hp
            have : (10 : ℝ) < p := by exact_mod_cast (by have := hp_gt p hp; omega : 10 < p)
            have : 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 := by rw [div_le_one (sq_pos_of_pos (by linarith))]; nlinarith
            linarith
        _ = 1 := Finset.prod_const_one
  -- Split inner sum into r = a on erase idx (gives YBar) and remainder E
  set Rset := (validSet k W R).filter (fun r => ∀ i ∈ Finset.univ.erase idx, a i ∣ r i)
  let eqOnErase : (Fin k → ℕ) → Prop := fun r => ∀ i ∈ Finset.univ.erase idx, r i = a i
  rw [← Finset.sum_filter_add_sum_filter_not Rset eqOnErase]
  have hmain_part :
      ∑ r ∈ Rset.filter eqOnErase,
        (∏ i ∈ Finset.univ.erase idx,
          (ArithmeticFunction.moebius (r i / a i) : ℝ) / (Nat.totient (r i / a i) : ℝ) ^ 2) *
        (y r / (Nat.totient (r idx) : ℝ)) = YBar W R y idx a := by
    unfold YBar
    have hset : Rset.filter eqOnErase = (validSet k W R).filter eqOnErase := by
      ext r
      simp only [Finset.mem_filter, Rset, eqOnErase, and_assoc]
      constructor
      · rintro ⟨h1, _, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨h1, fun i hi => (h3 i hi) ▸ dvd_refl _, h3⟩
    rw [hset]
    refine Finset.sum_congr rfl fun r hr => ?_
    have heq := (Finset.mem_filter.mp hr).2
    have hprod1 : (∏ i ∈ Finset.univ.erase idx,
        (ArithmeticFunction.moebius (r i / a i) : ℝ) / (Nat.totient (r i / a i) : ℝ) ^ 2) = 1 := by
      refine Finset.prod_eq_one fun i hi => ?_
      rw [heq i hi, Nat.div_self (valid_pos_at ha i)]
      simp
    rw [hprod1, one_mul]
  rw [hmain_part]
  -- Bound the tail sum E over Rset.filter (not eqOnErase)
  set E := ∑ r ∈ Rset.filter (fun r => ¬ eqOnErase r),
    (∏ i ∈ Finset.univ.erase idx,
      (ArithmeticFunction.moebius (r i / a i) : ℝ) / (Nat.totient (r i / a i) : ℝ) ^ 2) *
    (y r / (Nat.totient (r idx) : ℝ))
  have hE_abs : |E| ≤ (2 * (k : ℝ) / ((D0 : ℝ) - 2)) * Z1B := by
    let S_R := (Finset.Icc 1 R).filter (fun s => Squarefree s ∧ Nat.Coprime s W)
    let vDom : Fin k → Finset ℕ := fun i => if i = idx then {1} else S_R
    let Vset := (Fintype.piFinset vDom).filter (fun v => ∃ i ∈ Finset.univ.erase idx, v i ≠ 1)
    let vMap : (Fin k → ℕ) → (Fin k → ℕ) := fun r i => if i = idx then 1 else r i / a i
    have hv_maps : ∀ r ∈ Rset.filter (fun r => ¬ eqOnErase r), vMap r ∈ Vset := by
      intro r hr
      have hrR := (Finset.mem_filter.mp hr).1
      have hne := (Finset.mem_filter.mp hr).2
      have hrV := mem_validSet_iff.mp (Finset.mem_filter.mp hrR).1
      have hdvd := (Finset.mem_filter.mp hrR).2
      rw [Finset.mem_filter, Fintype.mem_piFinset]
      refine ⟨?_, ?_⟩
      · intro i
        dsimp only [vDom, vMap]
        by_cases hi : i = idx
        · simp [hi]
        · rw [if_neg hi, if_neg hi]
          have hmem_er : i ∈ Finset.univ.erase idx := Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩
          have hq_dvd : r i / a i ∣ r i := Nat.div_dvd_of_dvd (hdvd i hmem_er)
          exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
            ⟨Nat.div_pos (Nat.le_of_dvd (valid_pos_at hrV i) (hdvd i hmem_er)) (valid_pos_at ha i),
             le_trans (Nat.div_le_self _ _) (valid_le_R_at hrV i)⟩,
            (valid_squarefree_at hrV i).squarefree_of_dvd hq_dvd,
            (valid_coprime_W_at hrV i).coprime_dvd_left hq_dvd⟩
      · dsimp only [eqOnErase] at hne
        push Not at hne
        rcases hne with ⟨i, hi, hri⟩
        refine ⟨i, hi, ?_⟩
        have hne_idx : i ≠ idx := (Finset.mem_erase.mp hi).1
        simp only [vMap, if_neg hne_idx]
        intro h1
        apply hri
        calc r i = a i * (r i / a i) := (Nat.mul_div_cancel' (hdvd i hi)).symm
          _ = a i * 1 := by rw [h1]
          _ = a i := mul_one _
    -- Bound |E| by summing absolute values and grouping by v = vMap r
    calc |E| ≤ ∑ r ∈ Rset.filter (fun r => ¬ eqOnErase r),
          |(∏ i ∈ Finset.univ.erase idx,
            (ArithmeticFunction.moebius (r i / a i) : ℝ) / (Nat.totient (r i / a i) : ℝ) ^ 2) *
           (y r / (Nat.totient (r idx) : ℝ))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ r ∈ Rset.filter (fun r => ¬ eqOnErase r),
          (∏ i ∈ Finset.univ.erase idx, (1 / (Nat.totient (vMap r i) : ℝ) ^ 2)) *
          (y r / (Nat.totient (r idx) : ℝ)) := by
          refine Finset.sum_le_sum fun r _ => ?_
          rw [abs_mul, abs_of_nonneg (div_nonneg (hy0 r) (Nat.cast_nonneg _)), Finset.abs_prod]
          refine mul_le_mul_of_nonneg_right ?_ (div_nonneg (hy0 r) (Nat.cast_nonneg _))
          refine Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun i hi => ?_
          have hne_idx : i ≠ idx := (Finset.mem_erase.mp hi).1
          simp only [vMap, if_neg hne_idx]
          have hden_nonneg : (0 : ℝ) ≤ (Nat.totient (r i / a i) : ℝ) ^ 2 := sq_nonneg _
          rw [abs_div, abs_of_nonneg hden_nonneg]
          refine div_le_div_of_nonneg_right ?_ hden_nonneg
          by_cases hsq : Squarefree (r i / a i)
          · rw [ArithmeticFunction.moebius_apply_of_squarefree hsq]; simp
          · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]; simp
      _ = ∑ v ∈ Vset, (∏ i ∈ Finset.univ.erase idx, (1 / (Nat.totient (v i) : ℝ) ^ 2)) *
            ∑ r ∈ (Rset.filter (fun r => ¬ eqOnErase r)).filter (fun r => vMap r = v),
              y r / (Nat.totient (r idx) : ℝ) := by
          rw [← Finset.sum_fiberwise_of_maps_to hv_maps]
          refine Finset.sum_congr rfl fun v _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun r hr => ?_
          rw [(Finset.mem_filter.mp hr).2]
      _ ≤ ∑ v ∈ Vset, (∏ i ∈ Finset.univ.erase idx, (1 / (Nat.totient (v i) : ℝ) ^ 2)) * Z1B := by
          refine Finset.sum_le_sum fun v _ => mul_le_mul_of_nonneg_left ?_
            (Finset.prod_nonneg fun _ _ => by positivity)
          have hsub_fib : (Rset.filter (fun r => ¬ eqOnErase r)).filter (fun r => vMap r = v) ⊆
              (validSet k W R).filter (fun r => ∀ i ∈ Finset.univ.erase idx, r i = a i * v i) := by
            intro r hr
            have hrR := (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).1
            have hveq := (Finset.mem_filter.mp hr).2
            refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hrR).1, fun i hi => ?_⟩
            have hne_idx : i ≠ idx := (Finset.mem_erase.mp hi).1
            have hvi : r i / a i = v i := by
              have := congrFun hveq i
              simpa [vMap, hne_idx] using this
            rw [← hvi, Nat.mul_div_cancel' ((Finset.mem_filter.mp hrR).2 i hi)]
          exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub_fib
            (fun r _ _ => div_nonneg (hy0 r) (Nat.cast_nonneg _)))
            (hfiber_le_Z1B (fun i => a i * v i))
      _ = (∑ v ∈ Vset, ∏ i ∈ Finset.univ.erase idx, (1 / (Nat.totient (v i) : ℝ) ^ 2)) * Z1B :=
          (Finset.sum_mul ..).symm
      _ ≤ (2 * (k : ℝ) / ((D0 : ℝ) - 2)) * Z1B := by
          refine mul_le_mul_of_nonneg_right ?_ hZ1B_nonneg
          -- Sum over Vset = (sum{SR} 1/phi^2)^(k-1) - 1
          have h1R : 1 ∈ S_R :=
            Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_refl 1, hR⟩, squarefree_one, Nat.coprime_one_left _⟩
          have htot_v : ∑ v ∈ Fintype.piFinset vDom,
              (∏ i ∈ Finset.univ.erase idx, (1 / (Nat.totient (v i) : ℝ) ^ 2)) =
              (∑ s ∈ S_R, (1 / (Nat.totient s : ℝ) ^ 2)) ^ (Finset.univ.erase idx).card := by
            have heq_f : ∀ v ∈ Fintype.piFinset vDom,
                (∏ i ∈ Finset.univ.erase idx, (1 / (Nat.totient (v i) : ℝ) ^ 2)) =
                ∏ i : Fin k, (if i = idx then (1 : ℝ) else 1 / (Nat.totient (v i) : ℝ) ^ 2) := by
              intro v _
              rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ idx), if_pos rfl, one_mul]
              exact Finset.prod_congr rfl fun i hi => by rw [if_neg (Finset.mem_erase.mp hi).1]
            rw [Finset.sum_congr rfl heq_f, sum_piFinset_prod (f := fun i x =>
              if i = idx then (1 : ℝ) else 1 / (Nat.totient x : ℝ) ^ 2)]
            rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ idx)]
            have hidx1 : ∑ a ∈ vDom idx, (if idx = idx then (1 : ℝ) else 1 / (Nat.totient a : ℝ) ^ 2) = 1 := by
              simp [vDom]
            rw [hidx1, one_mul]
            calc ∏ i ∈ Finset.univ.erase idx,
                    ∑ a ∈ vDom i, (if i = idx then (1 : ℝ) else 1 / (Nat.totient a : ℝ) ^ 2)
                = ∏ _i ∈ Finset.univ.erase idx, ∑ s ∈ S_R, (1 / (Nat.totient s : ℝ) ^ 2) := by
                  refine Finset.prod_congr rfl fun i hi => ?_
                  simp [vDom, (Finset.mem_erase.mp hi).1]
              _ = _ := Finset.prod_const _
          have hone_v : (fun _ : Fin k => (1 : ℕ)) ∈ Fintype.piFinset vDom := by
            rw [Fintype.mem_piFinset]
            intro i; dsimp only [vDom]; split_ifs <;> simp [h1R]
          have hVset_eq : Vset = (Fintype.piFinset vDom).erase (fun _ => 1) := by
            ext v
            simp only [Vset, Finset.mem_filter, Finset.mem_erase, Fintype.mem_piFinset]
            constructor
            · rintro ⟨hv, i, hi, hvi⟩
              exact ⟨fun h => hvi (congrFun h i), hv⟩
            · rintro ⟨hne, hv⟩
              refine ⟨hv, ?_⟩
              have hex : ∃ i : Fin k, v i ≠ 1 := by
                by_contra hall; push Not at hall; exact hne (funext hall)
              rcases hex with ⟨i, hi⟩
              have hne_idx : i ≠ idx := by
                intro hEq
                have := hv idx
                simp [vDom] at this
                rw [hEq] at hi
                exact hi this
              exact ⟨i, ⟨hne_idx, Finset.mem_univ i⟩, hi⟩
          rw [hVset_eq, Finset.sum_erase_eq_sub hone_v, htot_v]
          have h1term : ∏ i ∈ Finset.univ.erase idx, (1 / (Nat.totient (1 : ℕ) : ℝ) ^ 2) = 1 := by simp
          rw [h1term]
          have hcard_le : (Finset.univ.erase idx).card ≤ k := by
            calc (Finset.univ.erase idx).card ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_le_card (Finset.erase_subset _ _)
              _ = k := by simp
          have hSR_ge1 : 1 ≤ ∑ s ∈ S_R, (1 / (Nat.totient s : ℝ) ^ 2) := by
            calc (1 : ℝ) = 1 / (Nat.totient 1 : ℝ) ^ 2 := by simp
              _ ≤ ∑ s ∈ S_R, (1 / (Nat.totient s : ℝ) ^ 2) :=
                Finset.single_le_sum (f := fun s => 1 / (Nat.totient s : ℝ) ^ 2)
                  (fun s _ => div_nonneg (by norm_num) (sq_nonneg _)) h1R
          have hSR_le := sum_inv_totient_sq_le_exp (D0 := D0) (R := R) (by omega)
          have h1 : (∑ s ∈ S_R, (1 / (Nat.totient s : ℝ) ^ 2)) ^ (Finset.univ.erase idx).card ≤
              (Real.exp (1 / ((D0 : ℝ) - 2))) ^ k :=
            le_trans (pow_le_pow_right₀ hSR_ge1 hcard_le) (pow_le_pow_left₀ (by linarith) hSR_le k)
          rw [← Real.exp_nat_mul] at h1
          have hD_pos : (0 : ℝ) < (D0 : ℝ) - 2 := by
            have : (10 : ℝ) ≤ D0 := by exact_mod_cast (by omega : 10 ≤ D0)
            linarith
          have ht0 : 0 ≤ (k : ℝ) * (1 / ((D0 : ℝ) - 2)) :=
            mul_nonneg (Nat.cast_nonneg _) (div_nonneg (by norm_num) hD_pos.le)
          have ht1 : (k : ℝ) * (1 / ((D0 : ℝ) - 2)) ≤ 1 / 2 := by
            have hD_r : (2 * (k : ℝ) + 10) ≤ (D0 : ℝ) := by exact_mod_cast hD
            rw [mul_one_div, div_le_div_iff₀ hD_pos (by norm_num)]
            linarith
          have h2 := exp_sub_one_le_two_mul ht0 ht1
          have heq : 2 * ((k : ℝ) * (1 / ((D0 : ℝ) - 2))) = 2 * (k : ℝ) / ((D0 : ℝ) - 2) := by ring
          linarith
  -- Combine |P_a * (YBar + E) - YBar| <= (3 * k / (D0 - 2)) * Z1B
  have hD_pos2 : (0 : ℝ) < (D0 : ℝ) - 2 := by
    have : (10 : ℝ) ≤ D0 := by exact_mod_cast (by omega : 10 ≤ D0)
    linarith
  have hPa_nonneg : 0 ≤ P_a := by
    have : (10 : ℝ) ≤ D0 := by exact_mod_cast (by omega : 10 ≤ D0)
    have : 1 / ((D0 : ℝ) - 2) ≤ 1 := by rw [div_le_one hD_pos2]; linarith
    linarith [hPa_bounds.1]
  have hdiff_bound : |P_a * (YBar W R y idx a + E) - YBar W R y idx a| ≤
      (3 * (k : ℝ) / ((D0 : ℝ) - 2)) * Z1B := by
    have heq : P_a * (YBar W R y idx a + E) - YBar W R y idx a =
        (P_a - 1) * YBar W R y idx a + P_a * E := by ring
    rw [heq]
    have htri := abs_add_le ((P_a - 1) * YBar W R y idx a) (P_a * E)
    rw [abs_mul, abs_mul, abs_of_nonneg hYBar_nonneg, abs_of_nonneg hPa_nonneg] at htri
    have hPa1 : |P_a - 1| ≤ 1 / ((D0 : ℝ) - 2) := by
      rw [abs_le]
      constructor <;> linarith [hPa_bounds.1, hPa_bounds.2]
    have h1 : |P_a - 1| * YBar W R y idx a ≤ (1 / ((D0 : ℝ) - 2)) * Z1B :=
      mul_le_mul hPa1 hYBar_le hYBar_nonneg (div_nonneg (by norm_num) hD_pos2.le)
    have h2 : P_a * |E| ≤ (2 * (k : ℝ) / ((D0 : ℝ) - 2)) * Z1B :=
      le_trans (mul_le_mul_of_nonneg_right hPa_bounds.2 (abs_nonneg _)) (by linarith [hE_abs])
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by
      have : 0 < k := Fin.pos idx
      exact_mod_cast this
    have hD_pos : (0 : ℝ) < (D0 : ℝ) - 2 := by
      have : (10 : ℝ) ≤ D0 := by exact_mod_cast (by omega : 10 ≤ D0)
      linarith
    have h3 : (1 / ((D0 : ℝ) - 2)) * Z1B ≤ ((k : ℝ) / ((D0 : ℝ) - 2)) * Z1B :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hk1 hD_pos.le) hZ1B_nonneg
    have hsum : ((k : ℝ) / ((D0 : ℝ) - 2)) * Z1B + (2 * (k : ℝ) / ((D0 : ℝ) - 2)) * Z1B =
        (3 * (k : ℝ) / ((D0 : ℝ) - 2)) * Z1B := by ring
    linarith
  have habs_le : |P_a * (YBar W R y idx a + E)| ≤ 2 * Z1B := by
    rw [abs_mul, abs_of_nonneg hPa_nonneg]
    have htri := abs_add_le (YBar W R y idx a) E
    rw [abs_of_nonneg hYBar_nonneg] at htri
    have h2k : 2 * (k : ℝ) / ((D0 : ℝ) - 2) ≤ 1 := by
      have hD_r : (2 * (k : ℝ) + 10) ≤ (D0 : ℝ) := by exact_mod_cast hD
      rw [div_le_one (by linarith)]
      linarith
    have hE_le : |E| ≤ Z1B :=
      le_trans hE_abs (by nlinarith)
    have hsum_le : |YBar W R y idx a + E| ≤ 2 * Z1B := by linarith
    calc P_a * |YBar W R y idx a + E|
        ≤ 1 * (2 * Z1B) := mul_le_mul hPa_bounds.2 hsum_le (abs_nonneg _) (by norm_num)
      _ = 2 * Z1B := one_mul _
  exact ⟨hYBar_nonneg, hYBar_le, hdiff_bound, habs_le⟩

set_option maxHeartbeats 400000 in
/-- Lower bound on M2(idx) in terms of T2(idx) minus O(k^2 / D0) times Z1B^2 times (2 times MU)^(k-1). -/
lemma M2_ge_T2_sub_err {k D0 R U : ℕ} (hD : 2 * k ^ 2 + 10 ≤ D0) (hR : 1 ≤ R) (hUR : U ≤ R)
    (y : (Fin k → ℕ) → ℝ) (gBound : ℕ → ℝ)
    (hy0 : ∀ r, 0 ≤ y r) (hg0 : ∀ n, 0 ≤ gBound n)
    (hy_supp : ∀ r, (∃ i, U < r i) → y r = 0)
    (hy_le_g : ∀ r (idx : Fin k), y r ≤ gBound (r idx))
    (idx : Fin k) :
    let W := primorial D0
    let S_U := (Finset.Icc 1 U).filter (fun s => Squarefree s ∧ Nat.Coprime s W)
    let M_U := ∑ s ∈ S_U, (1 / (Nat.totient s : ℝ))
    let Z1B := ∑ s ∈ S_U, gBound s / (Nat.totient s : ℝ)
    (∑ u ∈ (validSet k W R).filter (fun u => u idx = 1),
      (YBar W R y idx u) ^ 2 / (∏ i ∈ Finset.univ.erase idx, (Nat.totient (u i) : ℝ))) -
    (16 * (k : ℝ) ^ 2 / ((D0 : ℝ) - 3)) * Z1B ^ 2 * (2 * M_U) ^ (k - 1) ≤
    ∑ d ∈ (validSet k W R).filter (fun d => d idx = 1),
      ∑ e ∈ (validSet k W R).filter (fun e => e idx = 1 ∧ ∀ i j : Fin k, i ≠ j → Nat.Coprime (d i) (e j)),
        (lambdaOfY k W R y d * lambdaOfY k W R y e) /
          (∏ i : Fin k, (Nat.totient (Nat.lcm (d i) (e i)) : ℝ)) := by
  classical
  intro W S_U M_U Z1B
  have h2W : 2 ∣ W := (prime_dvd_primorial_iff Nat.prime_two).mpr (by omega)
  have hD_lin : 2 * k + 10 ≤ D0 := by nlinarith
  obtain ⟨hyMod_supp, hyMod_prop⟩ := yMod_approx hD_lin hR hUR y gBound hy0 hg0 hy_supp hy_le_g idx
  have hZ1B_nonneg : 0 ≤ Z1B := Finset.sum_nonneg (fun s _ => div_nonneg (hg0 s) (Nat.cast_nonneg _))
  have hMU_nonneg : 0 ≤ M_U := Finset.sum_nonneg (fun _ _ => by positivity)
  have hk1 : 1 ≤ k := Fin.pos idx
  have hcard_er : (Finset.univ.erase idx).card = k - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ idx), Finset.card_univ, Fintype.card_fin]
  rw [M2_eq_matrix_sum h2W]
  let Mset := (validMatSet k W R).filter (fun m => rowProd m idx = 1 ∧ colProd m idx = 1)
  let isDiag : (Fin k × Fin k → ℕ) → Prop := fun m => ∀ p : Fin k × Fin k, p.1 ≠ p.2 → m p = 1
  rw [← Finset.sum_filter_add_sum_filter_not Mset isDiag]
  -- Part 1: Diagonal sum >= T2 - (6 * k / (D0 - 2)) * Z1B^2 * M_U^(k-1)
  have hdiag_eq :
      ∑ m ∈ Mset.filter isDiag,
        (∏ p : Fin k × Fin k,
          if p.1 = p.2 then 1 / (phi2 (m p) : ℝ)
          else (ArithmeticFunction.moebius (m p) : ℝ) / (phi2 (m p) : ℝ) ^ 2) *
        yMod k W R y idx (rowProd m) * yMod k W R y idx (colProd m) =
      ∑ u ∈ (validSet k W R).filter (fun u => u idx = 1),
        (yMod k W R y idx u) ^ 2 / (∏ i ∈ Finset.univ.erase idx, (phi2 (u i) : ℝ)) := by
    refine Finset.sum_bij (fun m _ i => m (i, i)) ?_ ?_ ?_ ?_
    · intro m hm
      have hmM := (Finset.mem_filter.mp hm).1
      have hmd := (Finset.mem_filter.mp hm).2
      have hmV := mem_validMatSet_iff.mp (Finset.mem_filter.mp hmM).1
      have hri1 := (Finset.mem_filter.mp hmM).2.1
      have hrow_eq : rowProd m = fun i => m (i, i) := by
        funext i; unfold rowProd
        rw [Finset.prod_eq_single i]
        · intro j _ hji; exact hmd (i, j) (Ne.symm hji)
        · intro h; exact absurd (Finset.mem_univ i) h
      refine Finset.mem_filter.mpr ⟨mem_validSet_iff.mpr ?_, ?_⟩
      · rw [← hrow_eq]; exact validMat_rowProd_valid hmV
      · have := congrFun hrow_eq idx; linarith
    · intro m₁ hm₁ m₂ hm₂ hEq
      have hd₁ := (Finset.mem_filter.mp hm₁).2
      have hd₂ := (Finset.mem_filter.mp hm₂).2
      funext ⟨i, j⟩
      by_cases hij : i = j
      · subst hij; exact congrFun hEq i
      · rw [hd₁ (i, j) hij, hd₂ (i, j) hij]
    · intro u hu
      have huV := mem_validSet_iff.mp (Finset.mem_filter.mp hu).1
      have hui := (Finset.mem_filter.mp hu).2
      let m : Fin k × Fin k → ℕ := fun p => if p.1 = p.2 then u p.1 else 1
      have hprod_m : ∏ p : Fin k × Fin k, m p = ∏ i : Fin k, u i := by
        rw [Fintype.prod_prod_type]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [Finset.prod_eq_single i]
        · simp [m]
        · intro j _ hji; simp [m, Ne.symm hji]
        · intro h; exact absurd (Finset.mem_univ i) h
      have hrm : rowProd m idx = 1 := by
        unfold rowProd
        rw [Finset.prod_eq_single idx]
        · simp [m, hui]
        · intro j _ hji; simp [m, Ne.symm hji]
        · intro h; exact absurd (Finset.mem_univ idx) h
      have hcm : colProd m idx = 1 := by
        unfold colProd
        rw [Finset.prod_eq_single idx]
        · simp [m, hui]
        · intro i _ hij; simp [m, hij]
        · intro h; exact absurd (Finset.mem_univ idx) h
      refine ⟨m, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨mem_validMatSet_iff.mpr ?_, hrm, hcm⟩,
        fun p hp => by simp [m, hp]⟩, funext fun i => by simp [m]⟩
      unfold ValidMat; rw [hprod_m]; exact huV
    · intro m hm
      have hmM := (Finset.mem_filter.mp hm).1
      have hmd := (Finset.mem_filter.mp hm).2
      have hri1 := (Finset.mem_filter.mp hmM).2.1
      have hrow_eq : rowProd m = fun i => m (i, i) := by
        funext i; unfold rowProd
        rw [Finset.prod_eq_single i]
        · intro j _ hji; exact hmd (i, j) (Ne.symm hji)
        · intro h; exact absurd (Finset.mem_univ i) h
      have hcol_eq : colProd m = fun i => m (i, i) := by
        funext j; unfold colProd
        rw [Finset.prod_eq_single j]
        · intro i _ hij; exact hmd (i, j) hij
        · intro h; exact absurd (Finset.mem_univ j) h
      have hmii : m (idx, idx) = 1 := by
        have := congrFun hrow_eq idx; linarith
      have hprod_eq :
          (∏ p : Fin k × Fin k,
            if p.1 = p.2 then 1 / (phi2 (m p) : ℝ)
            else (ArithmeticFunction.moebius (m p) : ℝ) / (phi2 (m p) : ℝ) ^ 2) =
          1 / (∏ i ∈ Finset.univ.erase idx, (phi2 (m (i, i)) : ℝ)) := by
        rw [Fintype.prod_prod_type, ← Finset.mul_prod_erase _ _ (Finset.mem_univ idx)]
        have hidx_row : ∏ j : Fin k, (if idx = j then 1 / (phi2 (m (idx, j)) : ℝ)
            else (ArithmeticFunction.moebius (m (idx, j)) : ℝ) / (phi2 (m (idx, j)) : ℝ) ^ 2) = 1 := by
          rw [Finset.prod_eq_single idx]
          · simp [hmii, phi2_one]
          · intro j _ hji; rw [if_neg (Ne.symm hji), hmd (idx, j) (Ne.symm hji)]; simp [phi2_one]
          · intro h; exact absurd (Finset.mem_univ idx) h
        rw [hidx_row, one_mul, one_div, ← Finset.prod_inv_distrib]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [Finset.prod_eq_single i]
        · simp [one_div]
        · intro j _ hji; rw [if_neg (Ne.symm hji), hmd (i, j) (Ne.symm hji)]; simp [phi2_one]
        · intro h; exact absurd (Finset.mem_univ i) h
      rw [hrow_eq, hcol_eq, hprod_eq]
      ring
  have hdiag_low :
      (∑ u ∈ (validSet k W R).filter (fun u => u idx = 1),
        (YBar W R y idx u) ^ 2 / (∏ i ∈ Finset.univ.erase idx, (Nat.totient (u i) : ℝ))) -
      (6 * (k : ℝ) / ((D0 : ℝ) - 2)) * Z1B ^ 2 * M_U ^ (k - 1) ≤
      ∑ u ∈ (validSet k W R).filter (fun u => u idx = 1),
        (yMod k W R y idx u) ^ 2 / (∏ i ∈ Finset.univ.erase idx, (phi2 (u i) : ℝ)) := by
    let Uset := ((validSet k W R).filter (fun u => u idx = 1)).filter (fun u => ∀ i ∈ Finset.univ.erase idx, u i ≤ U)
    have hYBar_zero_out :
        ∑ u ∈ (validSet k W R).filter (fun u => u idx = 1),
          (YBar W R y idx u) ^ 2 / (∏ i ∈ Finset.univ.erase idx, (Nat.totient (u i) : ℝ)) =
        ∑ u ∈ Uset, (YBar W R y idx u) ^ 2 / (∏ i ∈ Finset.univ.erase idx, (Nat.totient (u i) : ℝ)) := by
      symm
      refine Finset.sum_subset (Finset.filter_subset _ _) fun u hu hnot => ?_
      have hex : ∃ i ∈ Finset.univ.erase idx, U < u i := by
        by_contra hall; push Not at hall
        exact hnot (Finset.mem_filter.mpr ⟨hu, hall⟩)
      rcases hex with ⟨i, hi, hUi⟩
      have hY0 : YBar W R y idx u = 0 := by
        unfold YBar
        refine Finset.sum_eq_zero fun r hr => ?_
        have hri := (Finset.mem_filter.mp hr).2 i hi
        simp [hy_supp r ⟨i, hri.symm ▸ hUi⟩]
      simp [hY0]
    have hdrop :
        ∑ u ∈ Uset, (yMod k W R y idx u) ^ 2 / (∏ i ∈ Finset.univ.erase idx, (Nat.totient (u i) : ℝ)) ≤
        ∑ u ∈ (validSet k W R).filter (fun u => u idx = 1),
          (yMod k W R y idx u) ^ 2 / (∏ i ∈ Finset.univ.erase idx, (phi2 (u i) : ℝ)) := by
      calc ∑ u ∈ Uset, (yMod k W R y idx u) ^ 2 / (∏ i ∈ Finset.univ.erase idx, (Nat.totient (u i) : ℝ))
          ≤ ∑ u ∈ Uset, (yMod k W R y idx u) ^ 2 / (∏ i ∈ Finset.univ.erase idx, (phi2 (u i) : ℝ)) := by
            refine Finset.sum_le_sum fun u hu => ?_
            have huV := mem_validSet_iff.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hu).1).1
            have hphi2_pos : 0 < ∏ i ∈ Finset.univ.erase idx, (phi2 (u i) : ℝ) := by
              refine Finset.prod_pos fun i _ => Nat.cast_pos.mpr (phi2_pos_of_odd ?_)
              intro h2u
              exact (by decide : ¬ (2 : ℕ) ∣ 1)
                ((valid_coprime_W_at huV i).gcd_eq_one ▸ Nat.dvd_gcd h2u h2W)
            have hle_den : ∏ i ∈ Finset.univ.erase idx, (phi2 (u i) : ℝ) ≤
                ∏ i ∈ Finset.univ.erase idx, (Nat.totient (u i) : ℝ) :=
              Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _)
                (fun i _ => Nat.cast_le.mpr (phi2_le_totient_of_squarefree (valid_squarefree_at huV i)))
            exact div_le_div_of_nonneg_left (sq_nonneg _) hphi2_pos hle_den
        _ ≤ ∑ u ∈ (validSet k W R).filter (fun u => u idx = 1),
              (yMod k W R y idx u) ^ 2 / (∏ i ∈ Finset.univ.erase idx, (phi2 (u i) : ℝ)) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              (fun _ _ _ => div_nonneg (sq_nonneg _) (Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _))
    -- On Uset, (YBar)^2 - (yMod)^2 <= 2 * YBar * |yMod - YBar| <= (6 * k / (D0 - 2)) * Z1B^2
    have hdiff_Uset :
        (∑ u ∈ Uset, (YBar W R y idx u) ^ 2 / (∏ i ∈ Finset.univ.erase idx, (Nat.totient (u i) : ℝ))) -
        (∑ u ∈ Uset, (yMod k W R y idx u) ^ 2 / (∏ i ∈ Finset.univ.erase idx, (Nat.totient (u i) : ℝ))) ≤
        (6 * (k : ℝ) / ((D0 : ℝ) - 2)) * Z1B ^ 2 * M_U ^ (k - 1) := by
      rw [← Finset.sum_sub_distrib]
      have hterm_le : ∀ u ∈ Uset,
          (YBar W R y idx u) ^ 2 / (∏ i ∈ Finset.univ.erase idx, (Nat.totient (u i) : ℝ)) -
          (yMod k W R y idx u) ^ 2 / (∏ i ∈ Finset.univ.erase idx, (Nat.totient (u i) : ℝ)) ≤
          ((6 * (k : ℝ) / ((D0 : ℝ) - 2)) * Z1B ^ 2) *
            ∏ i ∈ Finset.univ.erase idx, (1 / (Nat.totient (u i) : ℝ)) := by
        intro u hu
        have huF := (Finset.mem_filter.mp hu).1
        have huV := mem_validSet_iff.mp (Finset.mem_filter.mp huF).1
        have hui := (Finset.mem_filter.mp huF).2
        obtain ⟨hY0, hYle, hdiff, _⟩ := hyMod_prop u huV hui
        have hsq_diff : (YBar W R y idx u) ^ 2 - (yMod k W R y idx u) ^ 2 ≤
            2 * YBar W R y idx u * |yMod k W R y idx u - YBar W R y idx u| := by
          have h1 : (yMod k W R y idx u) ^ 2 =
              (YBar W R y idx u) ^ 2 + 2 * YBar W R y idx u * (yMod k W R y idx u - YBar W R y idx u) +
              (yMod k W R y idx u - YBar W R y idx u) ^ 2 := by ring
          have h2 : -(yMod k W R y idx u - YBar W R y idx u) ≤ |yMod k W R y idx u - YBar W R y idx u| :=
            neg_le_abs _
          nlinarith [sq_nonneg (yMod k W R y idx u - YBar W R y idx u)]
        have hsq_le : (YBar W R y idx u) ^ 2 - (yMod k W R y idx u) ^ 2 ≤
            (6 * (k : ℝ) / ((D0 : ℝ) - 2)) * Z1B ^ 2 := by
          calc (YBar W R y idx u) ^ 2 - (yMod k W R y idx u) ^ 2
              ≤ 2 * YBar W R y idx u * |yMod k W R y idx u - YBar W R y idx u| := hsq_diff
            _ ≤ 2 * Z1B * ((3 * (k : ℝ) / ((D0 : ℝ) - 2)) * Z1B) :=
                mul_le_mul (by linarith) hdiff (abs_nonneg _) (by linarith)
            _ = (6 * (k : ℝ) / ((D0 : ℝ) - 2)) * Z1B ^ 2 := by ring
        rw [← sub_div, Finset.prod_div_distrib, Finset.prod_const_one, mul_one_div]
        exact div_le_div_of_nonneg_right hsq_le (Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _)
      have hUset_sum_le :
          ∑ u ∈ Uset, (∏ i ∈ Finset.univ.erase idx, (1 / (Nat.totient (u i) : ℝ))) ≤ M_U ^ (k - 1) := by
        let domU : Fin k → Finset ℕ := fun i => if i = idx then {1} else S_U
        have hsubU : Uset ⊆ Fintype.piFinset domU := by
          intro u hu
          have huF := (Finset.mem_filter.mp hu).1
          have huV := mem_validSet_iff.mp (Finset.mem_filter.mp huF).1
          have hui := (Finset.mem_filter.mp huF).2
          have huLe := (Finset.mem_filter.mp hu).2
          rw [Fintype.mem_piFinset]
          intro i
          dsimp only [domU]
          by_cases hi : i = idx
          · subst hi; simp [hui]
          · rw [if_neg hi]
            exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨valid_pos_at huV i,
              huLe i (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩)⟩,
              valid_squarefree_at huV i, valid_coprime_W_at huV i⟩
        calc ∑ u ∈ Uset, (∏ i ∈ Finset.univ.erase idx, (1 / (Nat.totient (u i) : ℝ)))
            ≤ ∑ u ∈ Fintype.piFinset domU, (∏ i ∈ Finset.univ.erase idx, (1 / (Nat.totient (u i) : ℝ))) :=
              Finset.sum_le_sum_of_subset_of_nonneg hsubU (fun _ _ _ => Finset.prod_nonneg fun _ _ => by positivity)
          _ = ∑ u ∈ Fintype.piFinset domU,
                ∏ i : Fin k, (if i = idx then (1 : ℝ) else 1 / (Nat.totient (u i) : ℝ)) := by
              refine Finset.sum_congr rfl fun u _ => ?_
              rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ idx), if_pos rfl, one_mul]
              exact Finset.prod_congr rfl fun i hi => by rw [if_neg (Finset.mem_erase.mp hi).1]
          _ = ∏ i : Fin k, ∑ a ∈ domU i, (if i = idx then (1 : ℝ) else 1 / (Nat.totient a : ℝ)) :=
              sum_piFinset_prod domU (fun i a => if i = idx then (1 : ℝ) else 1 / (Nat.totient a : ℝ))
          _ = M_U ^ (k - 1) := by
              rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ idx)]
              have h1 : ∑ a ∈ domU idx, (if idx = idx then (1 : ℝ) else 1 / (Nat.totient a : ℝ)) = 1 := by
                simp [domU]
              rw [h1, one_mul]
              calc ∏ i ∈ Finset.univ.erase idx,
                      ∑ a ∈ domU i, (if i = idx then (1 : ℝ) else 1 / (Nat.totient a : ℝ))
                  = ∏ _i ∈ Finset.univ.erase idx, M_U := by
                    refine Finset.prod_congr rfl fun i hi => by simp [domU, (Finset.mem_erase.mp hi).1, M_U]
                _ = M_U ^ (k - 1) := by rw [Finset.prod_const, hcard_er]
      have hD_pos2 : (0 : ℝ) < (D0 : ℝ) - 2 := by
        have : (10 : ℝ) ≤ D0 := by exact_mod_cast (by omega : 10 ≤ D0)
        linarith
      calc ∑ u ∈ Uset, ((YBar W R y idx u) ^ 2 / (∏ i ∈ Finset.univ.erase idx, (Nat.totient (u i) : ℝ)) -
              (yMod k W R y idx u) ^ 2 / (∏ i ∈ Finset.univ.erase idx, (Nat.totient (u i) : ℝ)))
          ≤ ∑ u ∈ Uset, ((6 * (k : ℝ) / ((D0 : ℝ) - 2)) * Z1B ^ 2) *
              ∏ i ∈ Finset.univ.erase idx, (1 / (Nat.totient (u i) : ℝ)) := Finset.sum_le_sum hterm_le
        _ = ((6 * (k : ℝ) / ((D0 : ℝ) - 2)) * Z1B ^ 2) *
              ∑ u ∈ Uset, ∏ i ∈ Finset.univ.erase idx, (1 / (Nat.totient (u i) : ℝ)) := (Finset.mul_sum ..).symm
        _ ≤ ((6 * (k : ℝ) / ((D0 : ℝ) - 2)) * Z1B ^ 2) * M_U ^ (k - 1) :=
            mul_le_mul_of_nonneg_left hUset_sum_le
              (mul_nonneg (div_nonneg (by positivity) hD_pos2.le) (sq_nonneg _))
    linarith
  -- Part 2: Bound off-diagonal sum in absolute value by (8 * k^2 / (D0 - 3)) * Z1B^2 * (2 * M_U)^(k-1)
  have hoff_abs :
      |∑ m ∈ Mset.filter (fun m => ¬ isDiag m),
        (∏ p : Fin k × Fin k,
          if p.1 = p.2 then 1 / (phi2 (m p) : ℝ)
          else (ArithmeticFunction.moebius (m p) : ℝ) / (phi2 (m p) : ℝ) ^ 2) *
        yMod k W R y idx (rowProd m) * yMod k W R y idx (colProd m)| ≤
      (8 * (k : ℝ) ^ 2 / ((D0 : ℝ) - 3)) * Z1B ^ 2 * (2 * M_U) ^ (k - 1) := by
    let S_R := (Finset.Icc 1 R).filter (fun s => Squarefree s ∧ Nat.Coprime s W)
    let GoodOff := (Mset.filter (fun m => ¬ isDiag m)).filter
      (fun m => ∀ i ∈ Finset.univ.erase idx, m (i, i) ≤ U)
    have hzero :
        ∑ m ∈ Mset.filter (fun m => ¬ isDiag m),
          (∏ p : Fin k × Fin k,
            if p.1 = p.2 then 1 / (phi2 (m p) : ℝ)
            else (ArithmeticFunction.moebius (m p) : ℝ) / (phi2 (m p) : ℝ) ^ 2) *
          yMod k W R y idx (rowProd m) * yMod k W R y idx (colProd m) =
        ∑ m ∈ GoodOff,
          (∏ p : Fin k × Fin k,
            if p.1 = p.2 then 1 / (phi2 (m p) : ℝ)
            else (ArithmeticFunction.moebius (m p) : ℝ) / (phi2 (m p) : ℝ) ^ 2) *
          yMod k W R y idx (rowProd m) * yMod k W R y idx (colProd m) := by
      symm
      refine Finset.sum_subset (Finset.filter_subset _ _) fun m hm hnot => ?_
      have hex : ∃ i ∈ Finset.univ.erase idx, U < m (i, i) := by
        by_contra hall; push Not at hall
        exact hnot (Finset.mem_filter.mpr ⟨hm, hall⟩)
      rcases hex with ⟨i, _, hi⟩
      have hmV := mem_validMatSet_iff.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hm).1).1
      have hle_row : m (i, i) ≤ rowProd m i :=
        Nat.le_of_dvd (valid_pos_at (validMat_rowProd_valid hmV) i)
          (Finset.dvd_prod_of_mem (fun j => m (i, j)) (Finset.mem_univ i))
      have hy0' : yMod k W R y idx (rowProd m) = 0 :=
        hyMod_supp (rowProd m) ⟨i, lt_of_lt_of_le hi hle_row⟩
      rw [hy0', mul_zero, zero_mul]
    rw [hzero]
    let domM : Fin k × Fin k → Finset ℕ := fun p =>
      if p.1 = idx ∨ p.2 = idx then {1} else if p.1 = p.2 then S_U else S_R
    let Aset := (Fintype.piFinset domM).filter (fun m => ¬ isDiag m)
    have hsub : GoodOff ⊆ Aset := by
      intro m hm
      have hm1 := (Finset.mem_filter.mp hm).1
      have hmU := (Finset.mem_filter.mp hm).2
      have hmM := (Finset.mem_filter.mp hm1).1
      have hnd := (Finset.mem_filter.mp hm1).2
      have hmV := mem_validMatSet_iff.mp (Finset.mem_filter.mp hmM).1
      have hri1 := (Finset.mem_filter.mp hmM).2.1
      have hci1 := (Finset.mem_filter.mp hmM).2.2
      refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun p => ?_, hnd⟩
      dsimp only [domM]
      by_cases hidx : p.1 = idx ∨ p.2 = idx
      · rw [if_pos hidx, Finset.mem_singleton]
        rcases hidx with h1 | h2
        · have hdvd : m p ∣ rowProd m idx := by
            rcases p with ⟨i, j⟩; dsimp only at h1; rw [h1]
            exact Finset.dvd_prod_of_mem (fun j' => m (idx, j')) (Finset.mem_univ j)
          exact Nat.dvd_one.mp (hri1 ▸ hdvd)
        · have hdvd : m p ∣ colProd m idx := by
            rcases p with ⟨i, j⟩; dsimp only at h2; rw [h2]
            exact Finset.dvd_prod_of_mem (fun i' => m (i', idx)) (Finset.mem_univ i)
          exact Nat.dvd_one.mp (hci1 ▸ hdvd)
      · rw [if_neg hidx]
        have hp_dvd : m p ∣ ∏ q : Fin k × Fin k, m q := Finset.dvd_prod_of_mem m (Finset.mem_univ p)
        have hp_sq : Squarefree (m p) := hmV.1.squarefree_of_dvd hp_dvd
        have hp_cop : Nat.Coprime (m p) W := hmV.2.1.coprime_dvd_left hp_dvd
        have hp_pos : 1 ≤ m p := squarefree_pos hp_sq
        have hp_leR : m p ≤ R := le_trans (Nat.le_of_dvd (squarefree_pos hmV.1) hp_dvd) hmV.2.2
        by_cases heq : p.1 = p.2
        · rw [if_pos heq]
          have hleU : m p ≤ U := by
            rcases p with ⟨i, j⟩; dsimp only at hidx heq; subst heq
            exact hmU i (Finset.mem_erase.mpr ⟨fun h => hidx (Or.inl h), Finset.mem_univ i⟩)
          exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp_pos, hleU⟩, hp_sq, hp_cop⟩
        · rw [if_neg heq]
          exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp_pos, hp_leR⟩, hp_sq, hp_cop⟩
    have hstep_abs :
        |∑ m ∈ GoodOff,
          (∏ p : Fin k × Fin k,
            if p.1 = p.2 then 1 / (phi2 (m p) : ℝ)
            else (ArithmeticFunction.moebius (m p) : ℝ) / (phi2 (m p) : ℝ) ^ 2) *
          yMod k W R y idx (rowProd m) * yMod k W R y idx (colProd m)| ≤
        4 * Z1B ^ 2 * ∑ m ∈ Aset,
          ∏ p : Fin k × Fin k,
            if p.1 = p.2 then 1 / (phi2 (m p) : ℝ) else 1 / (phi2 (m p) : ℝ) ^ 2 := by
      calc |∑ m ∈ GoodOff, _|
          ≤ ∑ m ∈ GoodOff,
              |(∏ p : Fin k × Fin k,
                if p.1 = p.2 then 1 / (phi2 (m p) : ℝ)
                else (ArithmeticFunction.moebius (m p) : ℝ) / (phi2 (m p) : ℝ) ^ 2) *
               yMod k W R y idx (rowProd m) * yMod k W R y idx (colProd m)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ m ∈ GoodOff,
              (4 * Z1B ^ 2) * ∏ p : Fin k × Fin k,
                if p.1 = p.2 then 1 / (phi2 (m p) : ℝ) else 1 / (phi2 (m p) : ℝ) ^ 2 := by
            refine Finset.sum_le_sum fun m hm => ?_
            have hmM := (Finset.mem_filter.mp (Finset.mem_filter.mp hm).1).1
            have hmV := mem_validMatSet_iff.mp (Finset.mem_filter.mp hmM).1
            have hri1 := (Finset.mem_filter.mp hmM).2.1
            have hci1 := (Finset.mem_filter.mp hmM).2.2
            have hy1 := (hyMod_prop (rowProd m) (validMat_rowProd_valid hmV) hri1).2.2.2
            have hy2 := (hyMod_prop (colProd m) (validMat_colProd_valid hmV) hci1).2.2.2
            rw [abs_mul, abs_mul, Finset.abs_prod]
            have hprod_le :
                ∏ p : Fin k × Fin k,
                  |if p.1 = p.2 then 1 / (phi2 (m p) : ℝ)
                   else (ArithmeticFunction.moebius (m p) : ℝ) / (phi2 (m p) : ℝ) ^ 2| ≤
                ∏ p : Fin k × Fin k,
                  if p.1 = p.2 then 1 / (phi2 (m p) : ℝ) else 1 / (phi2 (m p) : ℝ) ^ 2 := by
              refine Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun p _ => ?_
              split_ifs
              · rw [abs_of_nonneg (div_nonneg (by norm_num) (Nat.cast_nonneg _))]
              · have hden : (0 : ℝ) ≤ (phi2 (m p) : ℝ) ^ 2 := sq_nonneg _
                rw [abs_div, abs_of_nonneg hden]
                refine div_le_div_of_nonneg_right ?_ hden
                by_cases hsq : Squarefree (m p)
                · rw [ArithmeticFunction.moebius_apply_of_squarefree hsq]; simp
                · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]; simp
            have hy_prod : |yMod k W R y idx (rowProd m)| * |yMod k W R y idx (colProd m)| ≤ 4 * Z1B ^ 2 := by
              nlinarith [abs_nonneg (yMod k W R y idx (rowProd m)), abs_nonneg (yMod k W R y idx (colProd m))]
            have hp_nonneg : 0 ≤ ∏ p : Fin k × Fin k,
                if p.1 = p.2 then 1 / (phi2 (m p) : ℝ) else 1 / (phi2 (m p) : ℝ) ^ 2 :=
              Finset.prod_nonneg (fun _ _ => by split_ifs <;> positivity)
            nlinarith [abs_nonneg (yMod k W R y idx (rowProd m)), abs_nonneg (yMod k W R y idx (colProd m)),
              Finset.prod_nonneg (s := (Finset.univ : Finset (Fin k × Fin k)))
                (f := fun p => |if p.1 = p.2 then 1 / (phi2 (m p) : ℝ)
                  else (ArithmeticFunction.moebius (m p) : ℝ) / (phi2 (m p) : ℝ) ^ 2|)
                (fun _ _ => abs_nonneg _)]
        _ = 4 * Z1B ^ 2 * ∑ m ∈ GoodOff,
              ∏ p : Fin k × Fin k,
                if p.1 = p.2 then 1 / (phi2 (m p) : ℝ) else 1 / (phi2 (m p) : ℝ) ^ 2 := (Finset.mul_sum ..).symm
        _ ≤ 4 * Z1B ^ 2 * ∑ m ∈ Aset,
              ∏ p : Fin k × Fin k,
                if p.1 = p.2 then 1 / (phi2 (m p) : ℝ) else 1 / (phi2 (m p) : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_left
              (Finset.sum_le_sum_of_subset_of_nonneg hsub
                (fun _ _ _ => Finset.prod_nonneg (fun _ _ => by split_ifs <;> positivity)))
              (by positivity)
    let M2_U := ∑ s ∈ S_U, (1 / (phi2 s : ℝ))
    let Off' := (Finset.univ : Finset (Fin k × Fin k)).filter (fun p => p.1 ≠ idx ∧ p.2 ≠ idx ∧ p.1 ≠ p.2)
    have hAset_eq :
        ∑ m ∈ Aset,
          (∏ p : Fin k × Fin k,
            if p.1 = p.2 then 1 / (phi2 (m p) : ℝ) else 1 / (phi2 (m p) : ℝ) ^ 2) =
        M2_U ^ (k - 1) * ((∑ s ∈ S_R, (1 / (phi2 s : ℝ) ^ 2)) ^ Off'.card - 1) := by
      have hsplit := Finset.sum_filter_add_sum_filter_not (Fintype.piFinset domM) isDiag
        (fun m => ∏ p : Fin k × Fin k,
          if p.1 = p.2 then 1 / (phi2 (m p) : ℝ) else 1 / (phi2 (m p) : ℝ) ^ 2)
      have htot :
          ∑ m ∈ Fintype.piFinset domM,
            (∏ p : Fin k × Fin k,
              if p.1 = p.2 then 1 / (phi2 (m p) : ℝ) else 1 / (phi2 (m p) : ℝ) ^ 2) =
          M2_U ^ (k - 1) * (∑ s ∈ S_R, (1 / (phi2 s : ℝ) ^ 2)) ^ Off'.card := by
        rw [sum_piFinset_prod domM (fun (p : Fin k × Fin k) x =>
          if p.1 = p.2 then 1 / (phi2 x : ℝ) else 1 / (phi2 x : ℝ) ^ 2)]
        let Diag' := (Finset.univ : Finset (Fin k × Fin k)).filter (fun p => p.1 ≠ idx ∧ p.2 ≠ idx ∧ p.1 = p.2)
        have hpart :
            ∏ p : Fin k × Fin k,
              (∑ a ∈ domM p, if p.1 = p.2 then 1 / (phi2 a : ℝ) else 1 / (phi2 a : ℝ) ^ 2) =
            (∏ p ∈ Diag', ∑ a ∈ domM p, if p.1 = p.2 then 1 / (phi2 a : ℝ) else 1 / (phi2 a : ℝ) ^ 2) *
            (∏ p ∈ Off', ∑ a ∈ domM p, if p.1 = p.2 then 1 / (phi2 a : ℝ) else 1 / (phi2 a : ℝ) ^ 2) := by
          rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun p : Fin k × Fin k => p.1 = idx ∨ p.2 = idx)]
          have hidx_one :
              ∏ p ∈ Finset.univ.filter (fun p : Fin k × Fin k => p.1 = idx ∨ p.2 = idx),
                (∑ a ∈ domM p, if p.1 = p.2 then 1 / (phi2 a : ℝ) else 1 / (phi2 a : ℝ) ^ 2) = 1 := by
            refine Finset.prod_eq_one fun p hp => ?_
            have h := (Finset.mem_filter.mp hp).2
            simp [domM, h, phi2_one]
          rw [hidx_one, one_mul]
          rw [← Finset.prod_filter_mul_prod_filter_not _ (fun p : Fin k × Fin k => p.1 = p.2)]
          congr 1
          · refine Finset.prod_congr ?_ (fun _ _ => rfl)
            ext p; simp [Diag', not_or, and_assoc]
          · refine Finset.prod_congr ?_ (fun _ _ => rfl)
            ext p; simp [Off', not_or, and_assoc]
        rw [hpart]
        have hDiag_card : Diag'.card = k - 1 := by
          have hbij : Diag' = (Finset.univ.erase idx).image (fun i : Fin k => (i, i)) := by
            ext ⟨i, j⟩
            simp only [Diag', Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
              Finset.mem_erase, and_true]
            constructor
            · rintro ⟨hi, _, rfl⟩; exact ⟨i, hi, rfl⟩
            · rintro ⟨l, hl, hEq⟩; cases hEq; exact ⟨hl, hl, rfl⟩
          rw [hbij, Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h), hcard_er]
        congr 1
        · calc ∏ p ∈ Diag', ∑ a ∈ domM p, (if p.1 = p.2 then 1 / (phi2 a : ℝ) else 1 / (phi2 a : ℝ) ^ 2)
              = ∏ _p ∈ Diag', M2_U := by
                refine Finset.prod_congr rfl fun p hp => ?_
                have h := (Finset.mem_filter.mp hp).2
                simp [domM, h.2.1, h.2.2, M2_U]
            _ = M2_U ^ (k - 1) := by rw [Finset.prod_const, hDiag_card]
        · calc ∏ p ∈ Off', ∑ a ∈ domM p, (if p.1 = p.2 then 1 / (phi2 a : ℝ) else 1 / (phi2 a : ℝ) ^ 2)
              = ∏ _p ∈ Off', ∑ s ∈ S_R, (1 / (phi2 s : ℝ) ^ 2) := by
                refine Finset.prod_congr rfl fun p hp => ?_
                have h := (Finset.mem_filter.mp hp).2
                simp [domM, h.1, h.2.1, h.2.2]
            _ = _ := Finset.prod_const _
      have hdiag_pi :
          ∑ m ∈ (Fintype.piFinset domM).filter isDiag,
            (∏ p : Fin k × Fin k,
              if p.1 = p.2 then 1 / (phi2 (m p) : ℝ) else 1 / (phi2 (m p) : ℝ) ^ 2) =
          M2_U ^ (k - 1) := by
        have h1R : 1 ∈ S_R :=
          Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_refl 1, hR⟩, squarefree_one, Nat.coprime_one_left _⟩
        let domU : Fin k → Finset ℕ := fun i => if i = idx then {1} else S_U
        have hbij :
            ∑ m ∈ (Fintype.piFinset domM).filter isDiag,
              (∏ p : Fin k × Fin k,
                if p.1 = p.2 then 1 / (phi2 (m p) : ℝ) else 1 / (phi2 (m p) : ℝ) ^ 2) =
            ∑ u ∈ Fintype.piFinset domU,
              ∏ i : Fin k, (if i = idx then (1 : ℝ) else 1 / (phi2 (u i) : ℝ)) := by
          refine Finset.sum_bij (fun m _ i => m (i, i)) ?_ ?_ ?_ ?_
          · intro m hm
            have hpi := Fintype.mem_piFinset.mp (Finset.mem_filter.mp hm).1
            rw [Fintype.mem_piFinset]
            intro i
            have hi := hpi (i, i)
            dsimp only [domU, domM] at hi ⊢
            by_cases he : i = idx
            · subst he; simpa using hi
            · simpa [he] using hi
          · intro m₁ hm₁ m₂ hm₂ hEq
            have hd₁ := (Finset.mem_filter.mp hm₁).2
            have hd₂ := (Finset.mem_filter.mp hm₂).2
            funext ⟨i, j⟩
            by_cases hij : i = j
            · subst hij; exact congrFun hEq i
            · rw [hd₁ (i, j) hij, hd₂ (i, j) hij]
          · intro u hu
            have hu' := Fintype.mem_piFinset.mp hu
            refine ⟨fun p => if p.1 = p.2 then u p.1 else 1, Finset.mem_filter.mpr ⟨?_, fun p hp => by simp [hp]⟩,
              funext fun i => by simp⟩
            rw [Fintype.mem_piFinset]
            intro p
            dsimp only [domM]
            by_cases hidx : p.1 = idx ∨ p.2 = idx
            · rw [if_pos hidx, Finset.mem_singleton]
              by_cases heq : p.1 = p.2
              · rw [if_pos heq]
                have hp1 : p.1 = idx := by rcases hidx with h1 | h2; exact h1; exact heq.trans h2
                have := hu' idx
                simp [domU] at this
                rw [hp1, this]
              · rw [if_neg heq]
            · rw [if_neg hidx]
              by_cases heq : p.1 = p.2
              · rw [if_pos heq, if_pos heq]
                have hp1 : p.1 ≠ idx := fun h => hidx (Or.inl h)
                have := hu' p.1
                simpa [domU, hp1] using this
              · rw [if_neg heq, if_neg heq]
                exact h1R
          · intro m hm
            have hpi := Fintype.mem_piFinset.mp (Finset.mem_filter.mp hm).1
            have hmd := (Finset.mem_filter.mp hm).2
            have hmii : m (idx, idx) = 1 := by
              have := hpi (idx, idx)
              simpa [domM] using this
            rw [Fintype.prod_prod_type]
            refine Finset.prod_congr rfl fun i _ => ?_
            rw [Finset.prod_eq_single i]
            · by_cases hi : i = idx
              · subst hi; simp [hmii, phi2_one]
              · simp [hi]
            · intro j _ hji
              rw [if_neg (Ne.symm hji), hmd (i, j) (Ne.symm hji)]
              simp [phi2_one]
            · intro h; exact absurd (Finset.mem_univ i) h
        rw [hbij, sum_piFinset_prod domU (fun i a => if i = idx then (1 : ℝ) else 1 / (phi2 a : ℝ))]
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ idx)]
        have h1 : ∑ a ∈ domU idx, (if idx = idx then (1 : ℝ) else 1 / (phi2 a : ℝ)) = 1 := by simp [domU]
        rw [h1, one_mul]
        calc ∏ i ∈ Finset.univ.erase idx, ∑ a ∈ domU i, (if i = idx then (1 : ℝ) else 1 / (phi2 a : ℝ))
            = ∏ _i ∈ Finset.univ.erase idx, M2_U :=
              Finset.prod_congr rfl fun i hi => by simp [domU, (Finset.mem_erase.mp hi).1, M2_U]
          _ = M2_U ^ (k - 1) := by rw [Finset.prod_const, hcard_er]
      linarith
    have hM2U_le : M2_U ≤ 2 * M_U := sum_inv_phi2_le_two_mul_sum_inv_totient (by omega)
    have hM2U_nonneg : 0 ≤ M2_U := Finset.sum_nonneg (fun _ _ => by positivity)
    have hOff'_card : Off'.card ≤ k ^ 2 := by
      calc Off'.card ≤ (Finset.univ : Finset (Fin k × Fin k)).card := Finset.card_filter_le _ _
        _ = k ^ 2 := by simp [sq]
    have h1R : 1 ∈ S_R :=
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_refl 1, hR⟩, squarefree_one, Nat.coprime_one_left _⟩
    have hSR_ge1 : 1 ≤ ∑ s ∈ S_R, (1 / (phi2 s : ℝ) ^ 2) := by
      calc (1 : ℝ) = 1 / (phi2 1 : ℝ) ^ 2 := by simp [phi2_one]
        _ ≤ ∑ s ∈ S_R, (1 / (phi2 s : ℝ) ^ 2) :=
          Finset.single_le_sum (f := fun s => 1 / (phi2 s : ℝ) ^ 2)
            (fun s _ => div_nonneg (by norm_num) (sq_nonneg _)) h1R
    have hSR_le : ∑ s ∈ S_R, (1 / (phi2 s : ℝ) ^ 2) ≤ Real.exp (1 / ((D0 : ℝ) - 3)) :=
      sum_inv_phi2_sq_le_exp (by omega)
    have hD_pos3 : (0 : ℝ) < (D0 : ℝ) - 3 := by
      have : (10 : ℝ) ≤ D0 := by exact_mod_cast (by omega : 10 ≤ D0)
      linarith
    have hpow_le : (∑ s ∈ S_R, (1 / (phi2 s : ℝ) ^ 2)) ^ Off'.card - 1 ≤
        2 * (k : ℝ) ^ 2 / ((D0 : ℝ) - 3) := by
      have h1 : (∑ s ∈ S_R, (1 / (phi2 s : ℝ) ^ 2)) ^ Off'.card ≤
          (Real.exp (1 / ((D0 : ℝ) - 3))) ^ (k ^ 2) :=
        le_trans (pow_le_pow_right₀ hSR_ge1 hOff'_card) (pow_le_pow_left₀ (by linarith) hSR_le _)
      rw [← Real.exp_nat_mul] at h1
      have ht0 : 0 ≤ ((k ^ 2 : ℕ) : ℝ) * (1 / ((D0 : ℝ) - 3)) :=
        mul_nonneg (Nat.cast_nonneg _) (div_nonneg (by norm_num) hD_pos3.le)
      have ht1 : ((k ^ 2 : ℕ) : ℝ) * (1 / ((D0 : ℝ) - 3)) ≤ 1 / 2 := by
        have hD_r : (2 * (k : ℝ) ^ 2 + 10) ≤ (D0 : ℝ) := by exact_mod_cast hD
        push_cast
        rw [mul_one_div, div_le_div_iff₀ hD_pos3 (by norm_num)]
        linarith
      have h2 := exp_sub_one_le_two_mul ht0 ht1
      push_cast at h1 h2
      have heq : 2 * ((k : ℝ) ^ 2 * (1 / ((D0 : ℝ) - 3))) = 2 * (k : ℝ) ^ 2 / ((D0 : ℝ) - 3) := by ring
      linarith
    have hA_le :
        M2_U ^ (k - 1) * ((∑ s ∈ S_R, (1 / (phi2 s : ℝ) ^ 2)) ^ Off'.card - 1) ≤
        (2 * M_U) ^ (k - 1) * (2 * (k : ℝ) ^ 2 / ((D0 : ℝ) - 3)) := by
      refine mul_le_mul (pow_le_pow_left₀ hM2U_nonneg hM2U_le _) hpow_le ?_ (by positivity)
      have : (1 : ℝ) ≤ (∑ s ∈ S_R, (1 / (phi2 s : ℝ) ^ 2)) ^ Off'.card := one_le_pow₀ hSR_ge1
      linarith
    calc |∑ m ∈ GoodOff, _|
        ≤ 4 * Z1B ^ 2 * (M2_U ^ (k - 1) * ((∑ s ∈ S_R, (1 / (phi2 s : ℝ) ^ 2)) ^ Off'.card - 1)) := by
          rw [← hAset_eq]; exact hstep_abs
      _ ≤ 4 * Z1B ^ 2 * ((2 * M_U) ^ (k - 1) * (2 * (k : ℝ) ^ 2 / ((D0 : ℝ) - 3))) :=
          mul_le_mul_of_nonneg_left hA_le (by positivity)
      _ = (8 * (k : ℝ) ^ 2 / ((D0 : ℝ) - 3)) * Z1B ^ 2 * (2 * M_U) ^ (k - 1) := by ring
  -- Combine Part 1 and Part 2
  have hD_pos3 : (0 : ℝ) < (D0 : ℝ) - 3 := by
    have : (10 : ℝ) ≤ D0 := by exact_mod_cast (by omega : 10 ≤ D0)
    linarith
  have hD_pos2 : (0 : ℝ) < (D0 : ℝ) - 2 := by linarith
  have hk_le_k2 : (k : ℝ) ≤ (k : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    nlinarith
  have hfrac_le : 6 * (k : ℝ) / ((D0 : ℝ) - 2) ≤ 8 * (k : ℝ) ^ 2 / ((D0 : ℝ) - 3) := by
    rw [div_le_div_iff₀ hD_pos2 hD_pos3]
    nlinarith
  have hMU_pow_le : M_U ^ (k - 1) ≤ (2 * M_U) ^ (k - 1) :=
    pow_le_pow_left₀ hMU_nonneg (by linarith) _
  have hcomb_err :
      (6 * (k : ℝ) / ((D0 : ℝ) - 2)) * Z1B ^ 2 * M_U ^ (k - 1) +
      (8 * (k : ℝ) ^ 2 / ((D0 : ℝ) - 3)) * Z1B ^ 2 * (2 * M_U) ^ (k - 1) ≤
      (16 * (k : ℝ) ^ 2 / ((D0 : ℝ) - 3)) * Z1B ^ 2 * (2 * M_U) ^ (k - 1) := by
    have h1 : (6 * (k : ℝ) / ((D0 : ℝ) - 2)) * Z1B ^ 2 * M_U ^ (k - 1) ≤
        (8 * (k : ℝ) ^ 2 / ((D0 : ℝ) - 3)) * Z1B ^ 2 * (2 * M_U) ^ (k - 1) := by
      have ha : (6 * (k : ℝ) / ((D0 : ℝ) - 2)) * Z1B ^ 2 ≤
          (8 * (k : ℝ) ^ 2 / ((D0 : ℝ) - 3)) * Z1B ^ 2 :=
        mul_le_mul_of_nonneg_right hfrac_le (sq_nonneg _)
      exact mul_le_mul ha hMU_pow_le (pow_nonneg hMU_nonneg _) (by positivity)
    have h88 : (8 * (k : ℝ) ^ 2 / ((D0 : ℝ) - 3)) * Z1B ^ 2 * (2 * M_U) ^ (k - 1) +
        (8 * (k : ℝ) ^ 2 / ((D0 : ℝ) - 3)) * Z1B ^ 2 * (2 * M_U) ^ (k - 1) =
        (16 * (k : ℝ) ^ 2 / ((D0 : ℝ) - 3)) * Z1B ^ 2 * (2 * M_U) ^ (k - 1) := by ring
    linarith
  have hneg_off : -((8 * (k : ℝ) ^ 2 / ((D0 : ℝ) - 3)) * Z1B ^ 2 * (2 * M_U) ^ (k - 1)) ≤
      ∑ m ∈ Mset.filter (fun m => ¬ isDiag m),
        (∏ p : Fin k × Fin k,
          if p.1 = p.2 then 1 / (phi2 (m p) : ℝ)
          else (ArithmeticFunction.moebius (m p) : ℝ) / (phi2 (m p) : ℝ) ^ 2) *
        yMod k W R y idx (rowProd m) * yMod k W R y idx (colProd m) :=
    (abs_le.mp hoff_abs).1
  rw [hdiag_eq]
  linarith

-- ## Section 3: Relating S1 and S2 to M1, M2, and Bombieri-Vinogradov

/-- Prime counting function theta(x; q, a). -/
noncomputable def theta (x : ℝ) (q a : ℕ) : ℝ :=
  ∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter (fun p => p.Prime ∧ p % q = a % q), Real.log (p : ℝ)

lemma coprime_lcm_left {a b c : ℕ} (ha : Nat.Coprime a c) (hb : Nat.Coprime b c) :
    Nat.Coprime (Nat.lcm a b) c :=
  (ha.mul_left hb).coprime_dvd_left ⟨Nat.gcd a b, (Nat.lcm_mul_gcd a b).symm⟩

lemma L_form_coprime_W {D0 M b v0 h_i : ℕ} (hc : Nat.Coprime (M * v0 + b + h_i) (primorial D0))
    (n : ℕ) :
    Nat.Coprime (M * primorial D0 * n + (M * v0 + b + h_i)) (primorial D0) := by
  have heq : M * primorial D0 * n + (M * v0 + b + h_i) = (M * v0 + b + h_i) + (M * n) * (primorial D0) := by
    ring
  rw [heq, Nat.coprime_add_mul_right_left]
  exact hc

lemma L_form_pairwise_coprime {D0 M b v0 : ℕ} {h₁ h₂ : ℕ}
    (hne : h₁ ≠ h₂) (hh₁ : h₁ ≤ D0) (hh₂ : h₂ ≤ D0)
    (hc₁ : Nat.Coprime (M * v0 + b + h₁) (primorial D0)) (n : ℕ) :
    Nat.Coprime (M * primorial D0 * n + (M * v0 + b + h₁))
      (M * primorial D0 * n + (M * v0 + b + h₂)) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra hgcd
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hgcd
  have hp1 : p ∣ M * primorial D0 * n + (M * v0 + b + h₁) := dvd_trans hpdvd (Nat.gcd_dvd_left _ _)
  have hp2 : p ∣ M * primorial D0 * n + (M * v0 + b + h₂) := dvd_trans hpdvd (Nat.gcd_dvd_right _ _)
  have hp_le : p ≤ D0 := by
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hsub : (M * primorial D0 * n + (M * v0 + b + h₂)) -
          (M * primorial D0 * n + (M * v0 + b + h₁)) = h₂ - h₁ := by omega
      have hpd : p ∣ h₂ - h₁ := hsub ▸ Nat.dvd_sub hp2 hp1
      exact le_trans (Nat.le_of_dvd (by omega) hpd) (by omega)
    · have hsub : (M * primorial D0 * n + (M * v0 + b + h₁)) -
          (M * primorial D0 * n + (M * v0 + b + h₂)) = h₁ - h₂ := by omega
      have hpd : p ∣ h₁ - h₂ := hsub ▸ Nat.dvd_sub hp1 hp2
      exact le_trans (Nat.le_of_dvd (by omega) hpd) (by omega)
  have hpW : p ∣ primorial D0 := (prime_dvd_primorial_iff hp).mpr hp_le
  have hcL := L_form_coprime_W hc₁ n
  exact hp.not_dvd_one (hcL.gcd_eq_one ▸ Nat.dvd_gcd hp1 hpW)

/-- In any interval Ioc a (a + Q) of length Q >= 1, there is exactly one element congruent to c mod Q. -/
lemma card_modEq_Ioc_block {Q : ℕ} (hQ : 0 < Q) (a c : ℕ) :
    ((Finset.Ioc a (a + Q)).filter (fun n => n ≡ c [MOD Q])).card = 1 := by
  -- The unique element is a + 1 + ((c + Q - (a + 1) % Q) % Q)
  let r := (c % Q + Q - (a + 1) % Q) % Q
  let x := a + 1 + r
  have hr_lt : r < Q := Nat.mod_lt _ hQ
  have hx_mem : x ∈ (Finset.Ioc a (a + Q)).filter (fun n => n ≡ c [MOD Q]) := by
    rw [Finset.mem_filter, Finset.mem_Ioc]
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    rw [Nat.ModEq]
    have h1 : (a + 1) % Q < Q := Nat.mod_lt _ hQ
    have h2 : c % Q < Q := Nat.mod_lt _ hQ
    have heq : (a + 1 + (c % Q + Q - (a + 1) % Q) % Q) % Q =
        ((a + 1) % Q + (c % Q + Q - (a + 1) % Q)) % Q := by
      simp only [Nat.add_mod, Nat.mod_mod]
    have heq2 : (a + 1) % Q + (c % Q + Q - (a + 1) % Q) = c % Q + Q := by omega
    rw [heq, heq2, Nat.add_mod_right, Nat.mod_mod]
  rw [Finset.card_eq_one]
  refine ⟨x, ?_⟩
  ext y
  simp only [Finset.mem_singleton]
  constructor
  · intro hy
    rw [Finset.mem_filter, Finset.mem_Ioc] at hy
    have hxy : y ≡ x [MOD Q] := hy.2.trans (Finset.mem_filter.mp hx_mem).2.symm
    have hx_bounds := Finset.mem_Ioc.mp (Finset.mem_filter.mp hx_mem).1
    rcases le_total y x with hle | hge
    · have hdvd : Q ∣ x - y := (Nat.modEq_iff_dvd' hle).mp hxy
      have hdiff_lt : x - y < Q := by omega
      have : x - y = 0 := by
        by_contra hne
        have := Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hdvd
        omega
      omega
    · have hdvd : Q ∣ y - x := (Nat.modEq_iff_dvd' hge).mp hxy.symm
      have hdiff_lt : y - x < Q := by omega
      have : y - x = 0 := by
        by_contra hne
        have := Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hdvd
        omega
      omega
  · rintro rfl; exact hx_mem

/-- In an interval Ioc X (2 * X), the number of elements congruent to c mod Q is X / Q + O(1). -/
lemma count_modEq_Ioc {Q : ℕ} (hQ : 0 < Q) (X c : ℕ) :
    |(((Finset.Ioc X (2 * X)).filter (fun n => n ≡ c [MOD Q])).card : ℝ) - (X : ℝ) / (Q : ℝ)| ≤ 1 := by
  -- Prove for any a and L: L / Q <= card(Ioc a (a + L) with n = c mod Q) <= L / Q + 1
  have hgen : ∀ q a, ((Finset.Ioc a (a + q * Q)).filter (fun n => n ≡ c [MOD Q])).card = q := by
    intro q
    induction q with
    | zero => intro a; simp
    | succ m ih =>
      intro a
      have hsplit : Finset.Ioc a (a + (m + 1) * Q) =
          Finset.Ioc a (a + m * Q) ∪ Finset.Ioc (a + m * Q) (a + m * Q + Q) := by
        ext n
        simp only [Finset.mem_Ioc, Finset.mem_union]
        have : (m + 1) * Q = m * Q + Q := by ring
        omega
      have hdisj : Disjoint (Finset.Ioc a (a + m * Q)) (Finset.Ioc (a + m * Q) (a + m * Q + Q)) := by
        rw [Finset.disjoint_left]
        intro n h1 h2
        simp only [Finset.mem_Ioc] at h1 h2
        omega
      rw [hsplit, Finset.filter_union, Finset.card_union_of_disjoint
        (Finset.disjoint_filter_filter hdisj), ih a, card_modEq_Ioc_block hQ]
  set q := X / Q
  set r := X % Q
  have hXr : X = q * Q + r := (Nat.div_add_mod' X Q).symm
  have hr_lt : r < Q := Nat.mod_lt X hQ
  have h2X : 2 * X = X + q * Q + r := by omega
  have hlow_sub : (Finset.Ioc X (X + q * Q)).filter (fun n => n ≡ c [MOD Q]) ⊆
      (Finset.Ioc X (2 * X)).filter (fun n => n ≡ c [MOD Q]) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Ioc] at hn ⊢
    exact ⟨⟨hn.1.1, by omega⟩, hn.2⟩
  have hhigh_sub : (Finset.Ioc X (2 * X)).filter (fun n => n ≡ c [MOD Q]) ⊆
      (Finset.Ioc X (X + (q + 1) * Q)).filter (fun n => n ≡ c [MOD Q]) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Ioc] at hn ⊢
    have : (q + 1) * Q = q * Q + Q := by ring
    exact ⟨⟨hn.1.1, by omega⟩, hn.2⟩
  have hcard_ge : q ≤ ((Finset.Ioc X (2 * X)).filter (fun n => n ≡ c [MOD Q])).card := by
    rw [← hgen q X]
    exact Finset.card_le_card hlow_sub
  have hcard_le : ((Finset.Ioc X (2 * X)).filter (fun n => n ≡ c [MOD Q])).card ≤ q + 1 := by
    rw [← hgen (q + 1) X]
    exact Finset.card_le_card hhigh_sub
  have hq_le : (q : ℝ) ≤ (X : ℝ) / (Q : ℝ) := by
    rw [le_div_iff₀ (Nat.cast_pos.mpr hQ)]
    exact_mod_cast (by omega : q * Q ≤ X)
  have hX_le : (X : ℝ) / (Q : ℝ) ≤ (q : ℝ) + 1 := by
    rw [div_le_iff₀ (Nat.cast_pos.mpr hQ)]
    have : X ≤ (q + 1) * Q := by
      have : (q + 1) * Q = q * Q + Q := by ring
      omega
    have hcast : (X : ℝ) ≤ ((q + 1 : ℕ) : ℝ) * (Q : ℝ) := by exact_mod_cast this
    push_cast at hcast
    linarith
  have hc1 : (q : ℝ) ≤ (((Finset.Ioc X (2 * X)).filter (fun n => n ≡ c [MOD Q])).card : ℝ) := by
    exact_mod_cast hcard_ge
  have hc2 : (((Finset.Ioc X (2 * X)).filter (fun n => n ≡ c [MOD Q])).card : ℝ) ≤ (q : ℝ) + 1 := by
    exact_mod_cast hcard_le
  rw [abs_le]
  constructor <;> linarith

/-- Elementary cardinality bound on validSet k W R. -/
lemma card_validSet_le {k W R : ℕ} (hR : 1 ≤ R) :
    ((validSet k W R).card : ℝ) ≤ (R : ℝ) * (Real.log (R : ℝ) + 1) ^ k := by
  have hR_pos : (0 : ℝ) < R := Nat.cast_pos.mpr hR
  have h1 : ((validSet k W R).card : ℝ) ≤
      (R : ℝ) * ∑ d ∈ validSet k W R, (1 / (∏ i : Fin k, (d i : ℝ))) := by
    rw [Finset.mul_sum]
    have hcard : ((validSet k W R).card : ℝ) = ∑ _d ∈ validSet k W R, (1 : ℝ) := by simp
    rw [hcard]
    refine Finset.sum_le_sum fun d hd => ?_
    have hdV := mem_validSet_iff.mp hd
    have hprod_pos : (0 : ℝ) < ∏ i : Fin k, (d i : ℝ) :=
      Finset.prod_pos fun i _ => Nat.cast_pos.mpr (valid_pos_at hdV i)
    have hprod_le : (∏ i : Fin k, (d i : ℝ)) ≤ (R : ℝ) := by
      have : (∏ i : Fin k, d i : ℕ) ≤ R := hdV.2.2
      exact_mod_cast this
    rw [mul_one_div, one_le_div hprod_pos]
    exact hprod_le
  have h2 : ∑ d ∈ validSet k W R, (1 / (∏ i : Fin k, (d i : ℝ))) ≤
      (∑ s ∈ Finset.Icc 1 R, (1 / (s : ℝ))) ^ k := by
    have hsub : validSet k W R ⊆ Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R) := by
      intro d hd
      have hdV := mem_validSet_iff.mp hd
      exact Fintype.mem_piFinset.mpr fun i => Finset.mem_Icc.mpr ⟨valid_pos_at hdV i, valid_le_R_at hdV i⟩
    calc ∑ d ∈ validSet k W R, (1 / (∏ i : Fin k, (d i : ℝ)))
        = ∑ d ∈ validSet k W R, (∏ i : Fin k, (1 / (d i : ℝ))) := by
          refine Finset.sum_congr rfl fun d _ => ?_
          rw [Finset.prod_div_distrib, Finset.prod_const_one]
      _ ≤ ∑ d ∈ Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R), (∏ i : Fin k, (1 / (d i : ℝ))) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Finset.prod_nonneg fun _ _ => by positivity)
      _ = (∑ s ∈ Finset.Icc 1 R, (1 / (s : ℝ))) ^ k := by
          rw [sum_piFinset_prod (fun _ : Fin k => Finset.Icc 1 R) (fun _ s => 1 / (s : ℝ))]
          simp
  exact le_trans h1 (mul_le_mul_of_nonneg_left
    (le_trans h2 (pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => by positivity) (harmonic_le_log_add_one hR) k))
    hR_pos.le)

/-- Linear congruence solver: if gcd(A, q) = 1, there exists c such that A * n + B = 0 mod q iff n = c mod q. -/
lemma exists_linear_congr_sol {A B q : ℕ} (hq : 0 < q) (hc : Nat.Coprime A q) :
    ∃ c : ℕ, ∀ n : ℕ, q ∣ A * n + B ↔ n ≡ c [MOD q] := by
  let invA : ℕ := ((Nat.gcdA A q % (q : ℤ) + q) % q).toNat
  have hinvA : A * invA ≡ 1 [MOD q] := by
    have hbez : (A : ℤ) * Nat.gcdA A q + (q : ℤ) * Nat.gcdB A q = 1 := by
      have := Nat.gcd_eq_gcd_ab A q
      rw [hc.gcd_eq_one] at this
      push_cast at this
      linarith
    have hmod : ((invA : ℕ) : ℤ) ≡ Nat.gcdA A q [ZMOD (q : ℤ)] := by
      dsimp only [invA]
      have hnn : 0 ≤ (Nat.gcdA A q % (q : ℤ) + (q : ℤ)) % (q : ℤ) :=
        Int.emod_nonneg _ (Int.ofNat_ne_zero.mpr hq.ne')
      rw [Int.toNat_of_nonneg hnn]
      rw [Int.ModEq, Int.emod_emod, Int.add_emod_right, Int.emod_emod]
    have hmul : ((A * invA : ℕ) : ℤ) ≡ (1 : ℤ) [ZMOD (q : ℤ)] := by
      push_cast
      have h1 : (A : ℤ) * (invA : ℤ) ≡ (A : ℤ) * Nat.gcdA A q [ZMOD (q : ℤ)] := hmod.mul_left _
      have h2 : (A : ℤ) * Nat.gcdA A q ≡ 1 [ZMOD (q : ℤ)] := by
        rw [Int.modEq_iff_dvd]
        exact ⟨Nat.gcdB A q, by linarith⟩
      exact h1.trans h2
    exact Int.natCast_modEq_iff.mp hmul
  let c : ℕ := (invA * (q - B % q)) % q
  refine ⟨c, fun n => ?_⟩
  have hc_sol : q ∣ A * c + B := by
    have h1 : A * c ≡ A * (invA * (q - B % q)) [MOD q] :=
      (Nat.mod_modEq _ q).mul_left A
    have h2 : A * (invA * (q - B % q)) ≡ 1 * (q - B % q) [MOD q] := by
      rw [← mul_assoc]
      exact hinvA.mul_right _
    have h3 : A * c + B ≡ (q - B % q) + B [MOD q] := by
      simpa using (h1.trans h2).add_right B
    have h4 : (q - B % q) + B ≡ 0 [MOD q] := by
      have hlt : B % q < q := Nat.mod_lt B hq
      have hdiv : q ∣ (q - B % q) + B := by
        refine ⟨1 + B / q, ?_⟩
        have hdm := Nat.div_add_mod B q
        have hmul : q * (1 + B / q) = q + q * (B / q) := by ring
        omega
      exact Nat.modEq_zero_iff_dvd.mpr hdiv
    exact Nat.modEq_zero_iff_dvd.mp (h3.trans h4)
  constructor
  · intro hn
    have hdiff : A * n ≡ A * c [MOD q] := by
      have h1 : A * n + B ≡ A * c + B [MOD q] :=
        (Nat.modEq_zero_iff_dvd.mpr hn).trans (Nat.modEq_zero_iff_dvd.mpr hc_sol).symm
      exact Nat.ModEq.add_right_cancel' B h1
    exact Nat.ModEq.cancel_left_of_coprime hc.symm hdiff
  · intro hn
    have h1 : A * n + B ≡ A * c + B [MOD q] := (hn.mul_left A).add_right B
    exact (Nat.ModEq.dvd_iff h1 (dvd_refl q)).mpr hc_sol

/-- Upper bound on S1 in terms of X times M1 plus R^2 times (2 times log R + 2)^(8 times k). -/
lemma S1_le_mul_M1_add_err {k D0 M b v0 R X : ℕ}
    (hM : 0 < M) (hMD : M ≤ D0) (hR : 1 ≤ R)
    (h : Fin k → ℕ) (h_inj : Function.Injective h) (hhD : ∀ i, h i ≤ D0)
    (hcop : ∀ i, Nat.Coprime (M * v0 + b + h i) (primorial D0))
    (y : (Fin k → ℕ) → ℝ) (hy0 : ∀ r, 0 ≤ y r) (hy1 : ∀ r, y r ≤ 1) :
    let W := primorial D0
    let L : Fin k → ℕ → ℕ := fun i n => M * W * n + (M * v0 + b + h i)
    ∑ n ∈ Finset.Ioc X (2 * X),
      (∑ d ∈ (validSet k W R).filter (fun d => ∀ i, d i ∣ L i n), lambdaOfY k W R y d) ^ 2 ≤
    (X : ℝ) * (∑ d ∈ validSet k W R,
      ∑ e ∈ (validSet k W R).filter (fun e => ∀ i j : Fin k, i ≠ j → Nat.Coprime (d i) (e j)),
        (lambdaOfY k W R y d * lambdaOfY k W R y e) / (∏ i : Fin k, (Nat.lcm (d i) (e i) : ℝ))) +
    (R : ℝ) ^ 2 * (2 * Real.log (R : ℝ) + 2) ^ (8 * k) := by
  classical
  intro W L
  -- Step 1: expand square and swap sums
  have hexpand :
      ∑ n ∈ Finset.Ioc X (2 * X),
        (∑ d ∈ (validSet k W R).filter (fun d => ∀ i, d i ∣ L i n), lambdaOfY k W R y d) ^ 2 =
      ∑ d ∈ validSet k W R,
        ∑ e ∈ (validSet k W R).filter (fun e => ∀ i j : Fin k, i ≠ j → Nat.Coprime (d i) (e j)),
          (lambdaOfY k W R y d * lambdaOfY k W R y e) *
            (((Finset.Ioc X (2 * X)).filter (fun n => ∀ i, Nat.lcm (d i) (e i) ∣ L i n)).card : ℝ) := by
    have h1 :
        ∑ n ∈ Finset.Ioc X (2 * X),
          (∑ d ∈ (validSet k W R).filter (fun d => ∀ i, d i ∣ L i n), lambdaOfY k W R y d) ^ 2 =
        ∑ n ∈ Finset.Ioc X (2 * X), ∑ d ∈ validSet k W R, ∑ e ∈ validSet k W R,
          if (∀ i, Nat.lcm (d i) (e i) ∣ L i n) then lambdaOfY k W R y d * lambdaOfY k W R y e else 0 := by
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [sq, Finset.sum_mul]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun d _ => ?_
      by_cases hd : ∀ i, d i ∣ L i n
      · rw [if_pos hd, Finset.sum_filter]
        refine Finset.sum_congr rfl fun e _ => ?_
        have hiff : (∀ i, Nat.lcm (d i) (e i) ∣ L i n) ↔ (∀ i, e i ∣ L i n) := by
          constructor
          · intro hl i; exact dvd_trans (Nat.dvd_lcm_right _ _) (hl i)
          · intro he i; exact Nat.lcm_dvd (hd i) (he i)
        by_cases he : ∀ i, e i ∣ L i n
        · rw [if_pos he, if_pos (hiff.mpr he)]
        · rw [if_neg he, if_neg (fun h => he (hiff.mp h))]
      · rw [if_neg hd]
        symm
        refine Finset.sum_eq_zero fun e _ => ?_
        have hnot : ¬ (∀ i, Nat.lcm (d i) (e i) ∣ L i n) := fun hl =>
          hd (fun i => dvd_trans (Nat.dvd_lcm_left _ _) (hl i))
        rw [if_neg hnot]
    rw [h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.sum_comm, Finset.sum_filter]
    refine Finset.sum_congr rfl fun e _ => ?_
    by_cases hcp : ∀ i j : Fin k, i ≠ j → Nat.Coprime (d i) (e j)
    · rw [if_pos hcp, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
    · rw [if_neg hcp]
      push Not at hcp
      rcases hcp with ⟨i, j, hij, hncop⟩
      refine Finset.sum_eq_zero fun n _ => ?_
      have hnot : ¬ (∀ l, Nat.lcm (d l) (e l) ∣ L l n) := by
        intro hl
        have hdi : d i ∣ L i n := dvd_trans (Nat.dvd_lcm_left _ _) (hl i)
        have hej : e j ∣ L j n := dvd_trans (Nat.dvd_lcm_right _ _) (hl j)
        have hpair := L_form_pairwise_coprime (fun heq => hij (h_inj heq)) (hhD i) (hhD j) (hcop i) n
        exact hncop (hpair.coprime_dvd_left hdi |>.coprime_dvd_right hej)
      rw [if_neg hnot]
  rw [hexpand]
  -- Step 2: for each contributing (d, e), count is X / prod lcm + err with |err| <= 1
  have hcount_err : ∀ d ∈ validSet k W R,
      ∀ e ∈ (validSet k W R).filter (fun e => ∀ i j : Fin k, i ≠ j → Nat.Coprime (d i) (e j)),
        |(((Finset.Ioc X (2 * X)).filter (fun n => ∀ i, Nat.lcm (d i) (e i) ∣ L i n)).card : ℝ) -
          (X : ℝ) / (∏ i : Fin k, (Nat.lcm (d i) (e i) : ℝ))| ≤ 1 := by
    intro d hd e he
    have hdV := mem_validSet_iff.mp hd
    have heV := mem_validSet_iff.mp (Finset.mem_filter.mp he).1
    have hde_cop := (Finset.mem_filter.mp he).2
    let q : Fin k → ℕ := fun i => Nat.lcm (d i) (e i)
    have hq_pos : ∀ i, 0 < q i := fun i =>
      Nat.pos_of_ne_zero (Nat.lcm_ne_zero (valid_pos_at hdV i).ne' (valid_pos_at heV i).ne')
    have hq_copW : ∀ i, Nat.Coprime (q i) W := fun i =>
      coprime_lcm_left (valid_coprime_W_at hdV i) (valid_coprime_W_at heV i)
    have hq_copMW : ∀ i, Nat.Coprime (M * W) (q i) := fun i =>
      ((coprime_mul_primorial_iff hM hMD).mpr (hq_copW i)).symm
    have hq_pair : ((Finset.univ : Finset (Fin k)) : Set (Fin k)).Pairwise (fun i j => Nat.Coprime (q i) (q j)) := by
      intro i _ j _ hij
      refine coprime_lcm_left ?_ ?_
      · exact (coprime_lcm_left (valid_pairwise_coprime hdV hij).symm (hde_cop i j hij).symm).symm
      · exact (coprime_lcm_left (hde_cop j i hij.symm) (valid_pairwise_coprime heV hij).symm).symm
    choose ci hci using fun i : Fin k => exists_linear_congr_sol (B := M * v0 + b + h i) (hq_pos i) (hq_copMW i)
    obtain ⟨c, hc⟩ := crt_finset Finset.univ q ci hq_pair
    set Q := ∏ i : Fin k, q i
    have hQ_pos : 0 < Q := Finset.prod_pos (fun i _ => hq_pos i)
    have hfilter_eq : (Finset.Ioc X (2 * X)).filter (fun n => ∀ i, q i ∣ L i n) =
        (Finset.Ioc X (2 * X)).filter (fun n => n ≡ c [MOD Q]) := by
      ext n
      simp only [Finset.mem_filter, and_congr_right_iff]
      intro _
      constructor
      · intro hall
        have hmod_i : ∀ i : Fin k, n ≡ c [MOD q i] := fun i =>
          ((hci i n).mp (hall i)).trans (hc i (Finset.mem_univ i)).symm
        -- By pairwise coprimality, n = c mod prod q_i
        have hmod_prod : ∀ s : Finset (Fin k), n ≡ c [MOD ∏ i ∈ s, q i] := by
          intro s
          induction s using Finset.induction_on with
          | empty => simpa using Nat.modEq_one (a := n) (b := c)
          | insert a s ha ih =>
            rw [Finset.prod_insert ha]
            have hca : Nat.Coprime (q a) (∏ i ∈ s, q i) := by
              refine Nat.Coprime.prod_right fun i hi =>
                hq_pair (Finset.mem_univ a) (Finset.mem_univ i) (fun h => ha (h ▸ hi))
            exact (Nat.modEq_and_modEq_iff_modEq_mul hca).mp ⟨hmod_i a, ih⟩
        exact hmod_prod Finset.univ
      · intro hmod i
        have h1 : n ≡ c [MOD q i] := Nat.ModEq.of_dvd (Finset.dvd_prod_of_mem q (Finset.mem_univ i)) hmod
        exact (hci i n).mpr (h1.trans (hc i (Finset.mem_univ i)))
    rw [hfilter_eq]
    have hQ_cast : (Q : ℝ) = ∏ i : Fin k, (Nat.lcm (d i) (e i) : ℝ) := by
      dsimp only [Q, q]; rw [Nat.cast_prod]
    rw [← hQ_cast]
    exact count_modEq_Ioc hQ_pos X c
  -- Step 3: combine main term and error term
  have hmain_split :
      (∑ d ∈ validSet k W R,
        ∑ e ∈ (validSet k W R).filter (fun e => ∀ i j : Fin k, i ≠ j → Nat.Coprime (d i) (e j)),
          (lambdaOfY k W R y d * lambdaOfY k W R y e) *
            (((Finset.Ioc X (2 * X)).filter (fun n => ∀ i, Nat.lcm (d i) (e i) ∣ L i n)).card : ℝ)) -
      (X : ℝ) * (∑ d ∈ validSet k W R,
        ∑ e ∈ (validSet k W R).filter (fun e => ∀ i j : Fin k, i ≠ j → Nat.Coprime (d i) (e j)),
          (lambdaOfY k W R y d * lambdaOfY k W R y e) / (∏ i : Fin k, (Nat.lcm (d i) (e i) : ℝ))) ≤
      (R : ℝ) ^ 2 * (2 * Real.log (R : ℝ) + 2) ^ (8 * k) := by
    rw [Finset.mul_sum]
    simp_rw [Finset.mul_sum]
    rw [← Finset.sum_sub_distrib]
    have hdiff_le :
        ∑ d ∈ validSet k W R,
          ((∑ e ∈ (validSet k W R).filter (fun e => ∀ i j : Fin k, i ≠ j → Nat.Coprime (d i) (e j)),
            (lambdaOfY k W R y d * lambdaOfY k W R y e) *
              (((Finset.Ioc X (2 * X)).filter (fun n => ∀ i, Nat.lcm (d i) (e i) ∣ L i n)).card : ℝ)) -
          (∑ e ∈ (validSet k W R).filter (fun e => ∀ i j : Fin k, i ≠ j → Nat.Coprime (d i) (e j)),
            (X : ℝ) * ((lambdaOfY k W R y d * lambdaOfY k W R y e) / (∏ i : Fin k, (Nat.lcm (d i) (e i) : ℝ))))) ≤
        ∑ d ∈ validSet k W R, ∑ e ∈ validSet k W R,
          |lambdaOfY k W R y d| * |lambdaOfY k W R y e| := by
      refine Finset.sum_le_sum fun d hd => ?_
      rw [← Finset.sum_sub_distrib]
      calc ∑ e ∈ (validSet k W R).filter (fun e => ∀ i j : Fin k, i ≠ j → Nat.Coprime (d i) (e j)),
              ((lambdaOfY k W R y d * lambdaOfY k W R y e) *
                (((Finset.Ioc X (2 * X)).filter (fun n => ∀ i, Nat.lcm (d i) (e i) ∣ L i n)).card : ℝ) -
              (X : ℝ) * ((lambdaOfY k W R y d * lambdaOfY k W R y e) / (∏ i : Fin k, (Nat.lcm (d i) (e i) : ℝ))))
          ≤ ∑ e ∈ (validSet k W R).filter (fun e => ∀ i j : Fin k, i ≠ j → Nat.Coprime (d i) (e j)),
              |lambdaOfY k W R y d| * |lambdaOfY k W R y e| := by
            refine Finset.sum_le_sum fun e he => ?_
            have heq : (lambdaOfY k W R y d * lambdaOfY k W R y e) *
                  (((Finset.Ioc X (2 * X)).filter (fun n => ∀ i, Nat.lcm (d i) (e i) ∣ L i n)).card : ℝ) -
                (X : ℝ) * ((lambdaOfY k W R y d * lambdaOfY k W R y e) / (∏ i : Fin k, (Nat.lcm (d i) (e i) : ℝ))) =
                (lambdaOfY k W R y d * lambdaOfY k W R y e) *
                  ((((Finset.Ioc X (2 * X)).filter (fun n => ∀ i, Nat.lcm (d i) (e i) ∣ L i n)).card : ℝ) -
                    (X : ℝ) / (∏ i : Fin k, (Nat.lcm (d i) (e i) : ℝ))) := by ring
            rw [heq]
            calc (lambdaOfY k W R y d * lambdaOfY k W R y e) * _
                ≤ |(lambdaOfY k W R y d * lambdaOfY k W R y e) * _| := le_abs_self _
              _ = |lambdaOfY k W R y d| * |lambdaOfY k W R y e| *
                    |(((Finset.Ioc X (2 * X)).filter (fun n => ∀ i, Nat.lcm (d i) (e i) ∣ L i n)).card : ℝ) -
                      (X : ℝ) / (∏ i : Fin k, (Nat.lcm (d i) (e i) : ℝ))| := by rw [abs_mul, abs_mul]
              _ ≤ |lambdaOfY k W R y d| * |lambdaOfY k W R y e| * 1 :=
                  mul_le_mul_of_nonneg_left (hcount_err d hd e he) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
              _ = _ := mul_one _
        _ ≤ ∑ e ∈ validSet k W R, |lambdaOfY k W R y d| * |lambdaOfY k W R y e| :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              (fun _ _ _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
    have hlogR_nonneg : 0 ≤ Real.log (R : ℝ) := Real.log_nonneg (by exact_mod_cast hR)
    have hlam := lambdaOfY_abs_le (W := W) hR y hy0 hy1
    have hsum_lam : ∑ d ∈ validSet k W R, |lambdaOfY k W R y d| ≤
        (R : ℝ) * (2 * Real.log (R : ℝ) + 2) ^ (4 * k) := by
      calc ∑ d ∈ validSet k W R, |lambdaOfY k W R y d|
          ≤ ∑ _d ∈ validSet k W R, (2 * Real.log (R : ℝ) + 2) ^ (3 * k) :=
            Finset.sum_le_sum fun d _ => hlam d
        _ = ((validSet k W R).card : ℝ) * (2 * Real.log (R : ℝ) + 2) ^ (3 * k) := by simp
        _ ≤ ((R : ℝ) * (Real.log (R : ℝ) + 1) ^ k) * (2 * Real.log (R : ℝ) + 2) ^ (3 * k) :=
            mul_le_mul_of_nonneg_right (card_validSet_le hR) (by positivity)
        _ ≤ ((R : ℝ) * (2 * Real.log (R : ℝ) + 2) ^ k) * (2 * Real.log (R : ℝ) + 2) ^ (3 * k) := by
            refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)) (by positivity)
            exact pow_le_pow_left₀ (by linarith) (by linarith) k
        _ = (R : ℝ) * (2 * Real.log (R : ℝ) + 2) ^ (4 * k) := by
            rw [mul_assoc, ← pow_add]; ring_nf
    calc _ ≤ ∑ d ∈ validSet k W R, ∑ e ∈ validSet k W R, |lambdaOfY k W R y d| * |lambdaOfY k W R y e| := hdiff_le
      _ = (∑ d ∈ validSet k W R, |lambdaOfY k W R y d|) ^ 2 := by
          rw [sq, Finset.sum_mul]
          refine Finset.sum_congr rfl fun d _ => (Finset.mul_sum ..).symm
      _ ≤ ((R : ℝ) * (2 * Real.log (R : ℝ) + 2) ^ (4 * k)) ^ 2 :=
          pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => abs_nonneg _) hsum_lam 2
      _ = (R : ℝ) ^ 2 * (2 * Real.log (R : ℝ) + 2) ^ (8 * k) := by
          rw [mul_pow, ← pow_mul]; ring_nf
  linarith

/-- Trivial upper bound on |theta(x; q, a) - x / phi(q)| for x >= 3 and 1 <= q <= floor x. -/
lemma theta_sub_div_totient_abs_le {x : ℝ} (hx : 3 ≤ x) {q a : ℕ}
    (hq1 : 1 ≤ q) (hqx : q ≤ ⌊x⌋₊) :
    |theta x q a - x / (Nat.totient q : ℝ)| ≤ 5 * x * Real.log x / (q : ℝ) := by
  have hx_pos : (0 : ℝ) < x := by linarith
  have hq_pos : (0 : ℝ) < q := Nat.cast_pos.mpr hq1
  have hlog3 : 1 ≤ Real.log x := by
    have he : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    have h1 : (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    rw [h1]
    exact Real.log_le_log (Real.exp_pos 1) (le_trans he.le hx)
  -- Upper bound on theta x q a: at most (floor x / q + 1) primes, each with log p <= log x
  have htheta_nonneg : 0 ≤ theta x q a := by
    unfold theta
    refine Finset.sum_nonneg fun p hp => ?_
    have hp2 : 2 ≤ p := (Finset.mem_filter.mp hp).2.1.two_le
    exact Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ p))
  have htheta_le : theta x q a ≤ 2 * x * Real.log x / (q : ℝ) := by
    let F := (Finset.range (⌊x⌋₊ + 1)).filter (fun p => p.Prime ∧ p % q = a % q)
    have hcard_le : F.card ≤ ⌊x⌋₊ / q + 1 := by
      have hinj : Set.InjOn (fun p => p / q) (F : Set ℕ) := by
        intro p₁ hp₁ p₂ hp₂ hEq
        dsimp only at hEq
        have hm₁ := (Finset.mem_filter.mp hp₁).2.2
        have hm₂ := (Finset.mem_filter.mp hp₂).2.2
        rw [← Nat.div_add_mod p₁ q, ← Nat.div_add_mod p₂ q, hEq, hm₁, hm₂]
      have hsub : F.image (fun p => p / q) ⊆ Finset.range (⌊x⌋₊ / q + 1) := by
        intro m hm
        rcases Finset.mem_image.mp hm with ⟨p, hp, rfl⟩
        have hp_le : p ≤ ⌊x⌋₊ := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hp).1)
        exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right hp_le))
      calc F.card = (F.image (fun p => p / q)).card := (Finset.card_image_of_injOn hinj).symm
        _ ≤ (Finset.range (⌊x⌋₊ / q + 1)).card := Finset.card_le_card hsub
        _ = ⌊x⌋₊ / q + 1 := Finset.card_range _
    have hcard_r : (F.card : ℝ) ≤ 2 * x / (q : ℝ) := by
      have h1 : (F.card : ℝ) ≤ ((⌊x⌋₊ / q : ℕ) : ℝ) + 1 := by exact_mod_cast hcard_le
      have h2 : ((⌊x⌋₊ / q : ℕ) : ℝ) ≤ x / (q : ℝ) := by
        rw [le_div_iff₀ hq_pos]
        have : (⌊x⌋₊ / q) * q ≤ ⌊x⌋₊ := Nat.div_mul_le_self ⌊x⌋₊ q
        exact le_trans (by exact_mod_cast this) (Nat.floor_le hx_pos.le)
      have h3 : (1 : ℝ) ≤ x / (q : ℝ) := by
        rw [one_le_div hq_pos]
        exact le_trans (Nat.cast_le.mpr hqx) (Nat.floor_le hx_pos.le)
      have h2x : 2 * x / (q : ℝ) = x / (q : ℝ) + x / (q : ℝ) := by ring
      linarith
    calc theta x q a
        ≤ ∑ _p ∈ F, Real.log x := by
          refine Finset.sum_le_sum fun p hp => ?_
          have hp_pos : (0 : ℝ) < p := Nat.cast_pos.mpr (Finset.mem_filter.mp hp).2.1.pos
          have hp_le : (p : ℝ) ≤ x :=
            le_trans (Nat.cast_le.mpr (Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hp).1)))
              (Nat.floor_le hx_pos.le)
          exact Real.log_le_log hp_pos hp_le
      _ = (F.card : ℝ) * Real.log x := by simp
      _ ≤ (2 * x / (q : ℝ)) * Real.log x := mul_le_mul_of_nonneg_right hcard_r (by linarith)
      _ = 2 * x * Real.log x / (q : ℝ) := by ring
  -- Upper bound on x / phi(q) <= 3 * x * log x / q
  have hmain_le : x / (Nat.totient q : ℝ) ≤ 3 * x * Real.log x / (q : ℝ) := by
    have hq_le_x : (q : ℝ) ≤ x := le_trans (Nat.cast_le.mpr hqx) (Nat.floor_le hx_pos.le)
    have hlogq : Real.log (q : ℝ) ≤ Real.log x := Real.log_le_log hq_pos hq_le_x
    have hdiv_phi := div_totient_le_two_mul_log_add_one hq1
    have hphi_pos : (0 : ℝ) < Nat.totient q := Nat.cast_pos.mpr (Nat.totient_pos.mpr hq1)
    have heq : x / (Nat.totient q : ℝ) = (x / (q : ℝ)) * ((q : ℝ) / (Nat.totient q : ℝ)) := by
      field_simp
    rw [heq]
    calc (x / (q : ℝ)) * ((q : ℝ) / (Nat.totient q : ℝ))
        ≤ (x / (q : ℝ)) * (3 * Real.log x) :=
          mul_le_mul_of_nonneg_left (by linarith) (div_nonneg hx_pos.le hq_pos.le)
      _ = 3 * x * Real.log x / (q : ℝ) := by ring
  have hmain_nonneg : 0 ≤ x / (Nat.totient q : ℝ) := div_nonneg hx_pos.le (Nat.cast_nonneg _)
  have h5 : 5 * x * Real.log x / (q : ℝ) = 2 * x * Real.log x / (q : ℝ) + 3 * x * Real.log x / (q : ℝ) := by
    ring
  rw [abs_le]
  constructor <;> linarith

/-- Existence of a coprime residue function a* maximizing |theta(x; q, a) - x / phi(q)| for each q. -/
lemma exists_max_coprime_residue (x : ℝ) :
    ∃ aStar : ℕ → ℕ, (∀ q, Nat.Coprime (aStar q) q) ∧
      ∀ q a, 1 ≤ q → Nat.Coprime a q →
        |theta x q a - x / (Nat.totient q : ℝ)| ≤ |theta x q (aStar q) - x / (Nat.totient q : ℝ)| := by
  classical
  have hex : ∀ q : ℕ, ∃ a₀ : ℕ, Nat.Coprime a₀ q ∧
      ∀ a, 1 ≤ q → Nat.Coprime a q →
        |theta x q a - x / (Nat.totient q : ℝ)| ≤ |theta x q a₀ - x / (Nat.totient q : ℝ)| := by
    intro q
    by_cases hq : 1 ≤ q
    · let S := (Finset.Icc 1 q).filter (fun a => Nat.Coprime a q)
      have h1S : 1 ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_refl 1, hq⟩, Nat.coprime_one_left q⟩
      obtain ⟨a₀, ha₀S, hmax⟩ := Finset.exists_max_image S
        (fun a => |theta x q a - x / (Nat.totient q : ℝ)|) ⟨1, h1S⟩
      refine ⟨a₀, (Finset.mem_filter.mp ha₀S).2, fun a _ hca => ?_⟩
      let a' : ℕ := if a % q = 0 then 1 else a % q
      have ha'S : a' ∈ S := by
        dsimp only [a']
        split_ifs with h0
        · exact h1S
        · refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.pos_of_ne_zero h0, (Nat.mod_lt a hq).le⟩, ?_⟩
          rw [Nat.coprime_iff_gcd_eq_one, ← Nat.gcd_rec]
          exact hca.symm.gcd_eq_one
      have hmod_eq : a' % q = a % q := by
        dsimp only [a']
        split_ifs with h0
        · have hq1 : q = 1 := by
            have hq_dvd : q ∣ a := Nat.dvd_of_mod_eq_zero h0
            exact Nat.dvd_one.mp (hca.gcd_eq_one ▸ Nat.dvd_gcd hq_dvd (dvd_refl q))
          subst hq1; rw [Nat.mod_one, Nat.mod_one]
        · exact Nat.mod_mod a q
      have htheta_eq : theta x q a = theta x q a' := by
        unfold theta
        simp only [hmod_eq]
      rw [htheta_eq]
      exact hmax a' ha'S
    · refine ⟨1, Nat.coprime_one_left q, fun _ hq1 _ => absurd hq1 hq⟩
  choose aStar haStar_cop haStar_max using hex
  exact ⟨aStar, haStar_cop, fun q a hq hca => haStar_max q a hq hca⟩

/-- Product of gcd(m, f y) over pairwise coprime f y equals gcd(m, prod f y). -/
lemma prod_gcd_of_pairwise_coprime {ι : Type*} [DecidableEq ι] {s : Finset ι} {f : ι → ℕ}
    (hcop : (s : Set ι).Pairwise (fun i j => Nat.Coprime (f i) (f j))) (m : ℕ) :
    ∏ i ∈ s, Nat.gcd m (f i) = Nat.gcd m (∏ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hca : Nat.Coprime (f a) (∏ i ∈ s, f i) := by
      refine Nat.Coprime.prod_right fun i hi =>
        hcop (Finset.mem_insert_self a s) (Finset.mem_insert_of_mem hi) (fun h => ha (h ▸ hi))
    rw [ih (hcop.mono (Finset.subset_insert a s)), Nat.Coprime.gcd_mul m hca]

/-- Bound on sum_Q cnt(Q)^2 / Q via 3k-factorization and pairwise gcd matrix. -/
lemma sum_pair_count_sq_div_le {k W R : ℕ} (hR : 1 ≤ R) (idx : Fin k) :
    let Pairs := (validSet k W R ×ˢ validSet k W R).filter
      (fun p => p.1 idx = 1 ∧ p.2 idx = 1 ∧ ∀ i j : Fin k, i ≠ j → Nat.Coprime (p.1 i) (p.2 j))
    let qProd : (Fin k → ℕ) × (Fin k → ℕ) → ℕ := fun p => ∏ i : Fin k, Nat.lcm (p.1 i) (p.2 i)
    ∑ Q ∈ (Finset.Icc 1 (R ^ 2)).filter Squarefree,
      (((Pairs.filter (fun p => qProd p = Q)).card : ℝ) ^ 2 / (Q : ℝ)) ≤
    (2 * Real.log (R : ℝ) + 1) ^ (9 * k ^ 2) := by
  classical
  intro Pairs qProd
  let J := Fin k × Fin 3
  -- Map each valid pair (d, e) to a 3k-tuple (ui, vi, wi) whose product is prod lcm(di, ei)
  let fac3 : (Fin k → ℕ) × (Fin k → ℕ) → J → ℕ := fun p j =>
    if j.2 = 0 then p.1 j.1 / Nat.gcd (p.1 j.1) (p.2 j.1)
    else if j.2 = 1 then p.2 j.1 / Nat.gcd (p.1 j.1) (p.2 j.1)
    else Nat.gcd (p.1 j.1) (p.2 j.1)
  have hfac3_prod : ∀ p ∈ Pairs, ∏ j : J, fac3 p j = qProd p := by
    intro p hp
    have hdV := mem_validSet_iff.mp (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
    have heV := mem_validSet_iff.mp (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).2
    dsimp only [qProd, J]
    rw [Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Fin.prod_univ_three]
    dsimp only [fac3]
    simp only [Fin.isValue, ite_true, Fin.one_eq_zero_iff, Fin.reduceEq, ite_false]
    set g := Nat.gcd (p.1 i) (p.2 i)
    have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left (p.2 i) (valid_pos_at hdV i)
    have hd_mul : p.1 i / g * g = p.1 i := Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)
    have he_mul : p.2 i / g * g = p.2 i := Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)
    have hmul_eq : (p.1 i / g * (p.2 i / g) * g) * g = Nat.lcm (p.1 i) (p.2 i) * g := by
      calc (p.1 i / g * (p.2 i / g) * g) * g
          = (p.1 i / g * g) * (p.2 i / g * g) := by ring
        _ = p.1 i * p.2 i := by rw [hd_mul, he_mul]
        _ = Nat.lcm (p.1 i) (p.2 i) * g := (Nat.lcm_mul_gcd _ _).symm
    exact Nat.eq_of_mul_eq_mul_right hg_pos hmul_eq
  have hfac3_inj : Set.InjOn fac3 (Pairs : Set ((Fin k → ℕ) × (Fin k → ℕ))) := by
    intro p₁ hp₁ p₂ hp₂ hEq
    have h1 : ∀ i, p₁.1 i = p₂.1 i := by
      intro i
      have h0 : fac3 p₁ (i, 0) = fac3 p₂ (i, 0) := congrFun hEq (i, 0)
      have h2 : fac3 p₁ (i, 2) = fac3 p₂ (i, 2) := congrFun hEq (i, 2)
      simp only [fac3, Fin.isValue, ite_true, Fin.reduceEq, ite_false] at h0 h2
      rw [← Nat.div_mul_cancel (Nat.gcd_dvd_left (p₁.1 i) (p₁.2 i)),
        ← Nat.div_mul_cancel (Nat.gcd_dvd_left (p₂.1 i) (p₂.2 i)), h0, h2]
    have h2 : ∀ i, p₁.2 i = p₂.2 i := by
      intro i
      have h1' : fac3 p₁ (i, 1) = fac3 p₂ (i, 1) := congrFun hEq (i, 1)
      have h2' : fac3 p₁ (i, 2) = fac3 p₂ (i, 2) := congrFun hEq (i, 2)
      simp only [fac3, Fin.isValue, ite_true, Fin.reduceEq, ite_false] at h1' h2'
      rw [← Nat.div_mul_cancel (Nat.gcd_dvd_right (p₁.1 i) (p₁.2 i)),
        ← Nat.div_mul_cancel (Nat.gcd_dvd_right (p₂.1 i) (p₂.2 i)), h1', h2']
    exact Prod.ext (funext h1) (funext h2)
  -- Now map each triple (Q, p₁, p₂) with qProd p₁ = Q = qProd p₂ to the J x J gcd matrix
  let Dom := Fintype.piFinset (fun _ : J × J => Finset.Icc 1 (R ^ 2))
  let gcdMat : ((Fin k → ℕ) × (Fin k → ℕ)) × ((Fin k → ℕ) × (Fin k → ℕ)) → (J × J → ℕ) :=
    fun pp z => Nat.gcd (fac3 pp.1 z.1) (fac3 pp.2 z.2)
  have hQ_bound : ∀ Q ∈ (Finset.Icc 1 (R ^ 2)).filter Squarefree,
      (((Pairs.filter (fun p => qProd p = Q)).card : ℝ) ^ 2 / (Q : ℝ)) ≤
      ∑ c ∈ Dom.filter (fun c => ∏ z : J × J, c z = Q), (1 / (Q : ℝ)) := by
    intro Q hQ
    have hQ_mem := Finset.mem_filter.mp hQ
    have hQ_sq : Squarefree Q := hQ_mem.2
    have hQ_pos : 0 < Q := squarefree_pos hQ_sq
    have hQ_le : Q ≤ R ^ 2 := (Finset.mem_Icc.mp hQ_mem.1).2
    let F := Pairs.filter (fun p => qProd p = Q)
    have hmaps : ∀ pp ∈ F ×ˢ F, gcdMat pp ∈ Dom.filter (fun c => ∏ z : J × J, c z = Q) := by
      intro pp hpp
      have hp1 := Finset.mem_filter.mp (Finset.mem_product.mp hpp).1
      have hp2 := Finset.mem_filter.mp (Finset.mem_product.mp hpp).2
      have hprod1 : ∏ x : J, fac3 pp.1 x = Q := (hfac3_prod pp.1 hp1.1).trans hp1.2
      have hprod2 : ∏ y : J, fac3 pp.2 y = Q := (hfac3_prod pp.2 hp2.1).trans hp2.2
      have hcop1 := pairwise_coprime_of_squarefree_prod (hprod1.symm ▸ hQ_sq)
      have hcop2 := pairwise_coprime_of_squarefree_prod (hprod2.symm ▸ hQ_sq)
      have hrow : ∀ x : J, ∏ y : J, gcdMat pp (x, y) = fac3 pp.1 x := by
        intro x
        dsimp only [gcdMat]
        rw [prod_gcd_of_pairwise_coprime hcop2, hprod2]
        exact Nat.gcd_eq_left (hprod1 ▸ Finset.dvd_prod_of_mem (fac3 pp.1) (Finset.mem_univ x))
      have hprod_all : ∏ z : J × J, gcdMat pp z = Q := by
        rw [Fintype.prod_prod_type]
        simp_rw [hrow]
        exact hprod1
      refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun z => Finset.mem_Icc.mpr ⟨?_, ?_⟩, hprod_all⟩
      · have hz_dvd : gcdMat pp z ∣ Q := hprod_all ▸ Finset.dvd_prod_of_mem (gcdMat pp) (Finset.mem_univ z)
        exact squarefree_pos (hQ_sq.squarefree_of_dvd hz_dvd)
      · have hz_dvd : gcdMat pp z ∣ Q := hprod_all ▸ Finset.dvd_prod_of_mem (gcdMat pp) (Finset.mem_univ z)
        exact le_trans (Nat.le_of_dvd hQ_pos hz_dvd) hQ_le
    have hinj : Set.InjOn gcdMat ((F ×ˢ F : Finset _) : Set _) := by
      intro pp₁ hpp₁ pp₂ hpp₂ hEq
      have hrow_rec : ∀ pp ∈ F ×ˢ F, ∀ x : J, ∏ y : J, gcdMat pp (x, y) = fac3 pp.1 x := by
        intro pp hpp x
        have hp1 := Finset.mem_filter.mp (Finset.mem_product.mp hpp).1
        have hp2 := Finset.mem_filter.mp (Finset.mem_product.mp hpp).2
        have hprod1 : ∏ x' : J, fac3 pp.1 x' = Q := (hfac3_prod pp.1 hp1.1).trans hp1.2
        have hprod2 : ∏ y' : J, fac3 pp.2 y' = Q := (hfac3_prod pp.2 hp2.1).trans hp2.2
        have hcop2 := pairwise_coprime_of_squarefree_prod (hprod2.symm ▸ hQ_sq)
        dsimp only [gcdMat]
        rw [prod_gcd_of_pairwise_coprime hcop2, hprod2]
        exact Nat.gcd_eq_left (hprod1 ▸ Finset.dvd_prod_of_mem (fac3 pp.1) (Finset.mem_univ x))
      have hcol_rec : ∀ pp ∈ F ×ˢ F, ∀ y : J, ∏ x : J, gcdMat pp (x, y) = fac3 pp.2 y := by
        intro pp hpp y
        have hp1 := Finset.mem_filter.mp (Finset.mem_product.mp hpp).1
        have hp2 := Finset.mem_filter.mp (Finset.mem_product.mp hpp).2
        have hprod1 : ∏ x' : J, fac3 pp.1 x' = Q := (hfac3_prod pp.1 hp1.1).trans hp1.2
        have hprod2 : ∏ y' : J, fac3 pp.2 y' = Q := (hfac3_prod pp.2 hp2.1).trans hp2.2
        have hcop1 := pairwise_coprime_of_squarefree_prod (hprod1.symm ▸ hQ_sq)
        dsimp only [gcdMat]
        simp_rw [Nat.gcd_comm (fac3 pp.1 _)]
        rw [prod_gcd_of_pairwise_coprime hcop1, hprod1]
        exact Nat.gcd_eq_left (hprod2 ▸ Finset.dvd_prod_of_mem (fac3 pp.2) (Finset.mem_univ y))
      have hf1 : fac3 pp₁.1 = fac3 pp₂.1 := by
        funext x
        rw [← hrow_rec pp₁ hpp₁ x, ← hrow_rec pp₂ hpp₂ x, hEq]
      have hf2 : fac3 pp₁.2 = fac3 pp₂.2 := by
        funext y
        rw [← hcol_rec pp₁ hpp₁ y, ← hcol_rec pp₂ hpp₂ y, hEq]
      have hp1_eq : pp₁.1 = pp₂.1 := hfac3_inj
        (Finset.mem_filter.mp (Finset.mem_product.mp hpp₁).1).1
        (Finset.mem_filter.mp (Finset.mem_product.mp hpp₂).1).1 hf1
      have hp2_eq : pp₁.2 = pp₂.2 := hfac3_inj
        (Finset.mem_filter.mp (Finset.mem_product.mp hpp₁).2).1
        (Finset.mem_filter.mp (Finset.mem_product.mp hpp₂).2).1 hf2
      exact Prod.ext hp1_eq hp2_eq
    have hcard_le : F.card ^ 2 ≤ (Dom.filter (fun c => ∏ z : J × J, c z = Q)).card := by
      calc F.card ^ 2 = (F ×ˢ F).card := by rw [Finset.card_product, sq]
        _ = ((F ×ˢ F).image gcdMat).card := (Finset.card_image_of_injOn hinj).symm
        _ ≤ (Dom.filter (fun c => ∏ z : J × J, c z = Q)).card :=
            Finset.card_le_card (fun c hc => by rcases Finset.mem_image.mp hc with ⟨pp, hpp, rfl⟩; exact hmaps pp hpp)
    rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hcard_le) (Nat.cast_nonneg _)
  -- Sum over Q and collapse into Dom
  have hcard_JJ : Fintype.card (J × J) = 9 * k ^ 2 := by
    simp only [J, Fintype.card_prod, Fintype.card_fin]
    ring
  calc ∑ Q ∈ (Finset.Icc 1 (R ^ 2)).filter Squarefree,
          (((Pairs.filter (fun p => qProd p = Q)).card : ℝ) ^ 2 / (Q : ℝ))
      ≤ ∑ Q ∈ (Finset.Icc 1 (R ^ 2)).filter Squarefree,
          ∑ c ∈ Dom.filter (fun c => ∏ z : J × J, c z = Q), (1 / (Q : ℝ)) :=
        Finset.sum_le_sum hQ_bound
    _ = ∑ Q ∈ (Finset.Icc 1 (R ^ 2)).filter Squarefree,
          ∑ c ∈ Dom.filter (fun c => ∏ z : J × J, c z = Q), (∏ z : J × J, (1 / (c z : ℝ))) := by
        refine Finset.sum_congr rfl fun Q _ => Finset.sum_congr rfl fun c hc => ?_
        have hpeq : (∏ z : J × J, c z) = Q := (Finset.mem_filter.mp hc).2
        rw [Finset.prod_div_distrib, Finset.prod_const_one, ← Nat.cast_prod, hpeq]
    _ ≤ ∑ c ∈ Dom, (∏ z : J × J, (1 / (c z : ℝ))) := by
        have hdisj : Set.PairwiseDisjoint (((Finset.Icc 1 (R ^ 2)).filter Squarefree : Finset ℕ) : Set ℕ)
            (fun Q => Dom.filter (fun c => ∏ z : J × J, c z = Q)) := by
          intro Q₁ _ Q₂ _ hne
          change Disjoint _ _
          rw [Finset.disjoint_left]
          intro c hc₁ hc₂
          exact hne ((Finset.mem_filter.mp hc₁).2.symm.trans (Finset.mem_filter.mp hc₂).2)
        rw [← Finset.sum_biUnion hdisj]
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => Finset.prod_nonneg fun _ _ => by positivity)
        intro c hc
        rcases Finset.mem_biUnion.mp hc with ⟨Q, _, hcQ⟩
        exact (Finset.mem_filter.mp hcQ).1
    _ = (∑ n ∈ Finset.Icc 1 (R ^ 2), (1 / (n : ℝ))) ^ (9 * k ^ 2) := by
        dsimp only [Dom]
        rw [sum_piFinset_prod (fun _ : J × J => Finset.Icc 1 (R ^ 2)) (fun _ n => 1 / (n : ℝ)),
          Finset.prod_const, Finset.card_univ, hcard_JJ]
    _ ≤ (2 * Real.log (R : ℝ) + 1) ^ (9 * k ^ 2) := by
        have hR2 : 1 ≤ R ^ 2 := by nlinarith
        have hharm := harmonic_le_log_add_one hR2
        have hlogR2 : Real.log ((R ^ 2 : ℕ) : ℝ) = 2 * Real.log (R : ℝ) := by
          push_cast; rw [Real.log_pow]; ring
        rw [hlogR2] at hharm
        exact pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => by positivity) hharm _

/-- CRT bijection for S_2(idx): inner prime sum equals theta(x2; q, a) - theta(x1; q, a). -/
lemma S2_inner_sum_eq_theta_sub {k D0 M b v0 R X : ℕ}
    (hM : 0 < M) (hMD : M ≤ D0)
    (h : Fin k → ℕ) (h_inj : Function.Injective h) (hhD : ∀ i, h i ≤ D0)
    (hcop : ∀ i, Nat.Coprime (M * v0 + b + h i) (primorial D0))
    (idx : Fin k) {d e : Fin k → ℕ} (hd : Valid (primorial D0) R d) (he : Valid (primorial D0) R e)
    (hd_idx : d idx = 1) (he_idx : e idx = 1)
    (hde_cop : ∀ i j : Fin k, i ≠ j → Nat.Coprime (d i) (e j)) :
    let W := primorial D0
    let L : Fin k → ℕ → ℕ := fun i n => M * W * n + (M * v0 + b + h i)
    let Q := ∏ i : Fin k, Nat.lcm (d i) (e i)
    let q := M * W * Q
    let x1 : ℝ := (M * W * X + (M * v0 + b + h idx) : ℕ)
    let x2 : ℝ := (2 * M * W * X + (M * v0 + b + h idx) : ℕ)
    ∃ a : ℕ, Nat.Coprime a q ∧
      ∑ n ∈ (Finset.Ioc X (2 * X)).filter (fun n => ∀ i, Nat.lcm (d i) (e i) ∣ L i n),
        (if (L idx n).Prime then Real.log (L idx n : ℝ) else 0) =
      theta x2 q a - theta x1 q a := by
  classical
  intro W L Q q x1 x2
  set B_idx := M * v0 + b + h idx
  let qi : Fin k → ℕ := fun i => Nat.lcm (d i) (e i)
  have hqi_pos : ∀ i, 0 < qi i := fun i =>
    Nat.pos_of_ne_zero (Nat.lcm_ne_zero (valid_pos_at hd i).ne' (valid_pos_at he i).ne')
  have hqi_idx : qi idx = 1 := by simp [qi, hd_idx, he_idx]
  have hqi_copW : ∀ i, Nat.Coprime (qi i) W := fun i =>
    coprime_lcm_left (valid_coprime_W_at hd i) (valid_coprime_W_at he i)
  have hqi_copMW : ∀ i, Nat.Coprime (M * W) (qi i) := fun i =>
    ((coprime_mul_primorial_iff hM hMD).mpr (hqi_copW i)).symm
  have hqi_pair : ((Finset.univ : Finset (Fin k)) : Set (Fin k)).Pairwise
      (fun i j => Nat.Coprime (qi i) (qi j)) := by
    intro i _ j _ hij
    refine coprime_lcm_left ?_ ?_
    · exact (coprime_lcm_left (valid_pairwise_coprime hd hij).symm (hde_cop i j hij).symm).symm
    · exact (coprime_lcm_left (hde_cop j i hij.symm) (valid_pairwise_coprime he hij).symm).symm
  -- Build moduli on Option (Fin k): none -> M * W, some i -> qi i
  let modFn : Option (Fin k) → ℕ := fun o => match o with
    | none => M * W
    | some i => qi i
  let resFn : Option (Fin k) → ℕ := fun o => match o with
    | none => B_idx
    | some i => (((((h idx : ℤ) - (h i : ℤ)) % (qi i : ℤ)) + (qi i : ℤ)) % (qi i : ℤ)).toNat
  have hmod_pair : ((Finset.univ : Finset (Option (Fin k))) : Set (Option (Fin k))).Pairwise
      (fun o₁ o₂ => Nat.Coprime (modFn o₁) (modFn o₂)) := by
    intro o₁ _ o₂ _ hne
    rcases o₁ with _ | i <;> rcases o₂ with _ | j
    · exact absurd rfl hne
    · exact hqi_copMW j
    · exact (hqi_copMW i).symm
    · exact hqi_pair (Finset.mem_univ i) (Finset.mem_univ j) (fun heq => hne (congrArg some heq))
  obtain ⟨a, ha⟩ := crt_finset Finset.univ modFn resFn hmod_pair
  -- Prove resFn o is coprime to modFn o for all o, hence a is coprime to q = M * W * Q
  have ha_copMW : Nat.Coprime a (M * W) := by
    have h1 : a ≡ B_idx [MOD M * W] := ha none (Finset.mem_univ none)
    have hB_cop : Nat.Coprime B_idx (M * W) := (coprime_mul_primorial_iff hM hMD).mpr (hcop idx)
    rw [Nat.coprime_iff_gcd_eq_one, Nat.ModEq.gcd_eq h1]
    exact hB_cop.gcd_eq_one
  have ha_copqi : ∀ i : Fin k, Nat.Coprime a (qi i) := by
    intro i
    by_cases hi : i = idx
    · subst hi; rw [hqi_idx]; exact Nat.coprime_one_right _
    · have h1 : a ≡ resFn (some i) [MOD qi i] := ha (some i) (Finset.mem_univ (some i))
      have hres_mod : ((resFn (some i) : ℕ) : ℤ) ≡ (h idx : ℤ) - (h i : ℤ) [ZMOD (qi i : ℤ)] := by
        dsimp only [resFn]
        have hnn : 0 ≤ (((h idx : ℤ) - (h i : ℤ)) % (qi i : ℤ) + (qi i : ℤ)) % (qi i : ℤ) :=
          Int.emod_nonneg _ (Int.ofNat_ne_zero.mpr (hqi_pos i).ne')
        rw [Int.toNat_of_nonneg hnn, Int.ModEq, Int.emod_emod, Int.add_emod_right, Int.emod_emod]
      rw [Nat.coprime_iff_gcd_eq_one, Nat.ModEq.gcd_eq h1]
      by_contra hne
      obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
      have hpr : p ∣ resFn (some i) := dvd_trans hpdvd (Nat.gcd_dvd_left _ _)
      have hpq : p ∣ qi i := dvd_trans hpdvd (Nat.gcd_dvd_right _ _)
      have hp_int : (p : ℤ) ∣ (h idx : ℤ) - (h i : ℤ) := by
        have h1' : (p : ℤ) ∣ (resFn (some i) : ℤ) := Int.ofNat_dvd.mpr hpr
        have h2' : (p : ℤ) ∣ (qi i : ℤ) := Int.ofNat_dvd.mpr hpq
        have h3' : (qi i : ℤ) ∣ (h idx : ℤ) - (h i : ℤ) - (resFn (some i) : ℤ) :=
          Int.modEq_iff_dvd.mp hres_mod
        have h4' : (p : ℤ) ∣ (h idx : ℤ) - (h i : ℤ) - (resFn (some i) : ℤ) := dvd_trans h2' h3'
        have := dvd_add h4' h1'
        simpa using this
      have hne_h : h idx ≠ h i := fun heq => hi (h_inj heq).symm
      have hp_le : p ≤ D0 := by
        rcases lt_or_gt_of_ne hne_h with hlt | hgt
        · have hd : p ∣ h i - h idx := by
            rw [← Int.ofNat_dvd]
            have : ((h i - h idx : ℕ) : ℤ) = -((h idx : ℤ) - (h i : ℤ)) := by
              rw [Nat.cast_sub hlt.le]; ring
            rw [this]
            exact dvd_neg.mpr hp_int
          exact le_trans (Nat.le_of_dvd (by omega) hd) (by have := hhD i; omega)
        · have hd : p ∣ h idx - h i := by
            rw [← Int.ofNat_dvd]
            have : ((h idx - h i : ℕ) : ℤ) = (h idx : ℤ) - (h i : ℤ) := Nat.cast_sub hgt.le
            rw [this]; exact hp_int
          exact le_trans (Nat.le_of_dvd (by omega) hd) (by have := hhD idx; omega)
      have hpW : p ∣ W := (prime_dvd_primorial_iff hp).mpr hp_le
      exact hp.not_dvd_one ((hqi_copW i).gcd_eq_one ▸ Nat.dvd_gcd hpq hpW)
  have ha_copq : Nat.Coprime a q :=
    Nat.Coprime.mul_right ha_copMW (Nat.Coprime.prod_right fun i _ => ha_copqi i)
  refine ⟨a, ha_copq, ?_⟩
  -- Express theta x2 q a - theta x1 q a as sum over Ioc (M times W times X + Bidx) (2 times M times W times X + Bidx)
  set n1 := M * W * X + B_idx
  set n2 := 2 * M * W * X + B_idx
  have htheta_sub : theta x2 q a - theta x1 q a =
      ∑ p ∈ (Finset.Ioc n1 n2).filter (fun p => p.Prime ∧ p % q = a % q), Real.log (p : ℝ) := by
    unfold theta
    have hfl1 : ⌊x1⌋₊ = n1 := by dsimp only [x1, n1, B_idx]; exact Nat.floor_natCast _
    have hfl2 : ⌊x2⌋₊ = n2 := by dsimp only [x2, n2, B_idx]; exact Nat.floor_natCast _
    have hle12 : n1 ≤ n2 := by
      dsimp only [n1, n2]
      have : M * W * X ≤ 2 * M * W * X := by
        calc M * W * X = 1 * (M * W * X) := (one_mul _).symm
          _ ≤ 2 * (M * W * X) := Nat.mul_le_mul_right _ (by omega)
          _ = 2 * M * W * X := by ring
      omega
    rw [hfl1, hfl2]
    have hsub : (Finset.range (n1 + 1)).filter (fun p => p.Prime ∧ p % q = a % q) ⊆
        (Finset.range (n2 + 1)).filter (fun p => p.Prime ∧ p % q = a % q) := by
      intro p hp
      rw [Finset.mem_filter, Finset.mem_range] at hp ⊢
      exact ⟨by omega, hp.2⟩
    rw [← Finset.sum_sdiff_eq_sub hsub]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext p
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨⟨?_, by omega⟩, h2⟩
      by_contra hle
      exact h3 ⟨by omega, h2⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨by omega, h3⟩, fun h => by omega⟩
  rw [htheta_sub]
  -- Bijection n |-> L idx n between filtered Ioc X (2 * X) and filtered Ioc n1 n2
  have hmod_iff : ∀ p : ℕ, p % q = a % q ↔
      (p ≡ B_idx [MOD M * W] ∧ ∀ i : Fin k, (p : ℤ) ≡ (h idx : ℤ) - (h i : ℤ) [ZMOD (qi i : ℤ)]) := by
    intro p
    have hp_iff : p % q = a % q ↔ p ≡ a [MOD M * W] ∧ ∀ i : Fin k, p ≡ a [MOD qi i] := by
      change p ≡ a [MOD M * W * Q] ↔ _
      have hcop_MWQ : Nat.Coprime (M * W) Q := Nat.Coprime.prod_right fun i _ => hqi_copMW i
      rw [← Nat.modEq_and_modEq_iff_modEq_mul hcop_MWQ]
      refine and_congr_right fun _ => ?_
      constructor
      · intro hQ i
        exact Nat.ModEq.of_dvd (Finset.dvd_prod_of_mem qi (Finset.mem_univ i)) hQ
      · intro hall
        have hprod : ∀ s : Finset (Fin k), p ≡ a [MOD ∏ i ∈ s, qi i] := by
          intro s
          induction s using Finset.induction_on with
          | empty => simpa using Nat.modEq_one (a := p) (b := a)
          | insert j s hj ih =>
            rw [Finset.prod_insert hj]
            have hcj : Nat.Coprime (qi j) (∏ i ∈ s, qi i) :=
              Nat.Coprime.prod_right fun i hi =>
                hqi_pair (Finset.mem_univ j) (Finset.mem_univ i) (fun heq => hj (heq ▸ hi))
            exact (Nat.modEq_and_modEq_iff_modEq_mul hcj).mp ⟨hall j, ih⟩
        exact hprod Finset.univ
    rw [hp_iff]
    refine and_congr ?_ (forall_congr' fun i => ?_)
    · have haMW : a ≡ B_idx [MOD M * W] := ha none (Finset.mem_univ none)
      exact ⟨fun h1 => h1.trans haMW, fun h1 => h1.trans haMW.symm⟩
    · have hai : a ≡ resFn (some i) [MOD qi i] := ha (some i) (Finset.mem_univ (some i))
      have hres_mod : ((resFn (some i) : ℕ) : ℤ) ≡ (h idx : ℤ) - (h i : ℤ) [ZMOD (qi i : ℤ)] := by
        dsimp only [resFn]
        have hnn : 0 ≤ (((h idx : ℤ) - (h i : ℤ)) % (qi i : ℤ) + (qi i : ℤ)) % (qi i : ℤ) :=
          Int.emod_nonneg _ (Int.ofNat_ne_zero.mpr (hqi_pos i).ne')
        rw [Int.toNat_of_nonneg hnn, Int.ModEq, Int.emod_emod, Int.add_emod_right, Int.emod_emod]
      constructor
      · intro h1
        exact (Int.natCast_modEq_iff.mpr (h1.trans hai)).trans hres_mod
      · intro h1
        have h2 : (p : ℤ) ≡ (resFn (some i) : ℤ) [ZMOD (qi i : ℤ)] := h1.trans hres_mod.symm
        exact (Int.natCast_modEq_iff.mp h2).trans hai.symm
  have hMW_pos : 0 < M * W := Nat.mul_pos hM (primorial_pos D0)
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun n _ => L idx n) ?_ ?_ ?_ ?_
  · intro n hn
    rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Ioc] at hn
    rcases hn with ⟨⟨⟨hnX, hn2X⟩, hdvd⟩, hprime⟩
    rw [Finset.mem_filter, Finset.mem_Ioc]
    refine ⟨⟨?_, ?_⟩, hprime, (hmod_iff (L idx n)).mpr ⟨?_, ?_⟩⟩
    · dsimp only [L, n1, B_idx]
      have : M * W * X < M * W * n := Nat.mul_lt_mul_of_pos_left hnX hMW_pos
      omega
    · dsimp only [L, n2, B_idx]
      have : M * W * n ≤ M * W * (2 * X) := Nat.mul_le_mul_left _ hn2X
      linarith
    · dsimp only [L, B_idx]
      rw [Nat.ModEq, Nat.mul_add_mod]
    · intro i
      have hLi : (qi i : ℤ) ∣ (L i n : ℤ) := Int.ofNat_dvd.mpr (hdvd i)
      have hdiff : (L idx n : ℤ) - ((h idx : ℤ) - (h i : ℤ)) = (L i n : ℤ) := by
        dsimp only [L]; push_cast; ring
      rw [Int.modEq_iff_dvd]
      have hneg : (h idx : ℤ) - (h i : ℤ) - (L idx n : ℤ) = -(L i n : ℤ) := by linarith
      rw [hneg]
      exact dvd_neg.mpr hLi
  · intro n₁ _ n₂ _ hEq
    dsimp only [L] at hEq
    exact Nat.eq_of_mul_eq_mul_left hMW_pos (by omega)
  · intro p hp
    rw [Finset.mem_filter, Finset.mem_Ioc] at hp
    rcases hp with ⟨⟨hp1, hp2⟩, hprime, hmod⟩
    obtain ⟨hpMW, hpi⟩ := (hmod_iff p).mp hmod
    have hp_ge_B : B_idx ≤ p := by dsimp only [n1] at hp1; omega
    have hMW_dvd : M * W ∣ p - B_idx := (Nat.modEq_iff_dvd' hp_ge_B).mp hpMW.symm
    let n := (p - B_idx) / (M * W)
    have hLn : L idx n = p := by
      dsimp only [L, B_idx, n]
      rw [Nat.mul_div_cancel' hMW_dvd]
      omega
    refine ⟨n, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨?_, ?_⟩, ?_⟩, hLn.symm ▸ hprime⟩, hLn⟩
    · have : M * W * X < M * W * n := by dsimp only [n1, L, B_idx] at hp1 hLn; omega
      exact Nat.lt_of_mul_lt_mul_left this
    · have : M * W * n ≤ M * W * (2 * X) := by dsimp only [n2, L, B_idx] at hp2 hLn; linarith
      exact Nat.le_of_mul_le_mul_left this hMW_pos
    · intro i
      have h1 : (qi i : ℤ) ∣ (h idx : ℤ) - (h i : ℤ) - (p : ℤ) := Int.modEq_iff_dvd.mp (hpi i)
      have h2 : (L i n : ℤ) = -((h idx : ℤ) - (h i : ℤ) - (p : ℤ)) := by
        rw [← hLn]; dsimp only [L]; push_cast; ring
      exact Int.ofNat_dvd.mp (h2 ▸ dvd_neg.mpr h1)
  · intro _ _; rfl

set_option maxHeartbeats 400000 in
/-- Lower bound on S_2(idx) from Bombieri-Vinogradov, with explicit Cauchy-Schwarz error. -/
lemma S2_ge_mul_M2_sub_BV_err {k D0 M b v0 R X : ℕ}
    (hM : 0 < M) (hMD : M ≤ D0) (hR : 1 ≤ R) (hRX : R < X)
    (h : Fin k → ℕ) (h_inj : Function.Injective h) (hhD : ∀ i, h i ≤ D0)
    (hcop : ∀ i, Nat.Coprime (M * v0 + b + h i) (primorial D0))
    (y : (Fin k → ℕ) → ℝ) (hy0 : ∀ r, 0 ≤ y r) (hy1 : ∀ r, y r ≤ 1)
    (idx : Fin k)
    {A B C : ℝ} (_hC : 0 ≤ C)
    (hBV : ∀ x : ℝ, 2 ≤ x → ∀ a : ℕ → ℕ, (∀ q, Nat.Coprime (a q) q) →
      ∑ q ∈ Finset.Icc 1 ⌊Real.sqrt x / Real.log x ^ B⌋₊,
        |theta x q (a q) - x / (Nat.totient q : ℝ)| ≤ C * x / Real.log x ^ A)
    (hx1_ge3 : (3 : ℝ) ≤ (M * primorial D0 * X + (M * v0 + b + h idx) : ℕ))
    (hQ_le_x1 : M * primorial D0 * R ^ 2 ≤
      ⌊Real.sqrt ((M * primorial D0 * X + (M * v0 + b + h idx) : ℕ) : ℝ) /
        Real.log ((M * primorial D0 * X + (M * v0 + b + h idx) : ℕ) : ℝ) ^ B⌋₊)
    (hQ_le_x2 : M * primorial D0 * R ^ 2 ≤
      ⌊Real.sqrt ((2 * M * primorial D0 * X + (M * v0 + b + h idx) : ℕ) : ℝ) /
        Real.log ((2 * M * primorial D0 * X + (M * v0 + b + h idx) : ℕ) : ℝ) ^ B⌋₊)
    (hQ_le_fl1 : M * primorial D0 * R ^ 2 ≤ M * primorial D0 * X + (M * v0 + b + h idx)) :
    let W := primorial D0
    let L : Fin k → ℕ → ℕ := fun i n => M * W * n + (M * v0 + b + h i)
    let x1 : ℝ := (M * W * X + (M * v0 + b + h idx) : ℕ)
    let x2 : ℝ := (2 * M * W * X + (M * v0 + b + h idx) : ℕ)
    ((W : ℝ) / (Nat.totient W : ℝ)) * (X : ℝ) *
      (∑ d ∈ (validSet k W R).filter (fun d => d idx = 1),
        ∑ e ∈ (validSet k W R).filter (fun e => e idx = 1 ∧ ∀ i j : Fin k, i ≠ j → Nat.Coprime (d i) (e j)),
          (lambdaOfY k W R y d * lambdaOfY k W R y e) /
            (∏ i : Fin k, (Nat.totient (Nat.lcm (d i) (e i)) : ℝ))) -
    (2 * Real.log (R : ℝ) + 2) ^ (6 * k) *
      Real.sqrt ((2 * Real.log (R : ℝ) + 1) ^ (9 * k ^ 2)) *
      (Real.sqrt (5 * C * x2 ^ 2 * Real.log x2 / Real.log x2 ^ A) +
        Real.sqrt (5 * C * x1 ^ 2 * Real.log x1 / Real.log x1 ^ A)) ≤
    ∑ n ∈ Finset.Ioc X (2 * X),
      (if (L idx n).Prime then Real.log (L idx n : ℝ) else 0) *
        (∑ d ∈ (validSet k W R).filter (fun d => ∀ i, d i ∣ L i n), lambdaOfY k W R y d) ^ 2 := by
  classical
  intro W L x1 x2
  have hW_pos : 0 < W := primorial_pos D0
  have hMW_pos : 0 < M * W := Nat.mul_pos hM hW_pos
  -- Step 1: For L idx n prime and n > X > R, d idx | L idx n implies d idx = 1
  have hS2_expand :
      ∑ n ∈ Finset.Ioc X (2 * X),
        (if (L idx n).Prime then Real.log (L idx n : ℝ) else 0) *
          (∑ d ∈ (validSet k W R).filter (fun d => ∀ i, d i ∣ L i n), lambdaOfY k W R y d) ^ 2 =
      ∑ d ∈ (validSet k W R).filter (fun d => d idx = 1),
        ∑ e ∈ (validSet k W R).filter (fun e => e idx = 1 ∧ ∀ i j : Fin k, i ≠ j → Nat.Coprime (d i) (e j)),
          (lambdaOfY k W R y d * lambdaOfY k W R y e) *
            ∑ n ∈ (Finset.Ioc X (2 * X)).filter (fun n => ∀ i, Nat.lcm (d i) (e i) ∣ L i n),
              (if (L idx n).Prime then Real.log (L idx n : ℝ) else 0) := by
    let D1 := (validSet k W R).filter (fun d => d idx = 1)
    have hdrop_d : ∀ n ∈ Finset.Ioc X (2 * X),
        (if (L idx n).Prime then Real.log (L idx n : ℝ) else 0) *
          (∑ d ∈ (validSet k W R).filter (fun d => ∀ i, d i ∣ L i n), lambdaOfY k W R y d) ^ 2 =
        (if (L idx n).Prime then Real.log (L idx n : ℝ) else 0) *
          (∑ d ∈ D1.filter (fun d => ∀ i, d i ∣ L i n), lambdaOfY k W R y d) ^ 2 := by
      intro n hn
      by_cases hp : (L idx n).Prime
      · rw [if_pos hp]
        congr 2
        refine Finset.sum_congr ?_ (fun _ _ => rfl)
        ext d
        simp only [D1, Finset.mem_filter, mem_validSet_iff, and_assoc]
        constructor
        · rintro ⟨hdV, hdvd⟩
          have hd_le : d idx ≤ R := valid_le_R_at hdV idx
          have hL_gt : R < L idx n := by
            have hnX : X < n := (Finset.mem_Ioc.mp hn).1
            have : 1 * n ≤ M * W * n := Nat.mul_le_mul_right n hMW_pos
            dsimp only [L]; omega
          rcases hp.eq_one_or_self_of_dvd (d idx) (hdvd idx) with h1 | hself
          · exact ⟨hdV, h1, hdvd⟩
          · omega
        · rintro ⟨hdV, _, hdvd⟩; exact ⟨hdV, hdvd⟩
      · rw [if_neg hp, zero_mul, zero_mul]
    rw [Finset.sum_congr rfl hdrop_d]
    have h1 :
        ∑ n ∈ Finset.Ioc X (2 * X),
          (if (L idx n).Prime then Real.log (L idx n : ℝ) else 0) *
            (∑ d ∈ D1.filter (fun d => ∀ i, d i ∣ L i n), lambdaOfY k W R y d) ^ 2 =
        ∑ n ∈ Finset.Ioc X (2 * X), ∑ d ∈ D1, ∑ e ∈ D1,
          if (∀ i, Nat.lcm (d i) (e i) ∣ L i n) then
            (lambdaOfY k W R y d * lambdaOfY k W R y e) *
              (if (L idx n).Prime then Real.log (L idx n : ℝ) else 0)
          else 0 := by
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [sq, Finset.sum_mul, Finset.mul_sum]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun d _ => ?_
      by_cases hd : ∀ i, d i ∣ L i n
      · rw [if_pos hd, Finset.sum_filter]
        refine Finset.sum_congr rfl fun e _ => ?_
        have hiff : (∀ i, Nat.lcm (d i) (e i) ∣ L i n) ↔ (∀ i, e i ∣ L i n) :=
          ⟨fun hl i => dvd_trans (Nat.dvd_lcm_right _ _) (hl i), fun he i => Nat.lcm_dvd (hd i) (he i)⟩
        by_cases he : ∀ i, e i ∣ L i n
        · rw [if_pos he, if_pos (hiff.mpr he)]; ring
        · rw [if_neg he, if_neg (fun h => he (hiff.mp h))]
      · rw [if_neg hd]
        symm
        refine Finset.sum_eq_zero fun e _ => ?_
        have hnot : ¬ (∀ i, Nat.lcm (d i) (e i) ∣ L i n) := fun hl =>
          hd (fun i => dvd_trans (Nat.dvd_lcm_left _ _) (hl i))
        rw [if_neg hnot]
    rw [h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    have hfil : (validSet k W R).filter (fun e => e idx = 1 ∧ ∀ i j : Fin k, i ≠ j → Nat.Coprime (d i) (e j)) =
        D1.filter (fun e => ∀ i j : Fin k, i ≠ j → Nat.Coprime (d i) (e j)) := by
      ext e; simp [D1, and_assoc]
    rw [hfil, Finset.sum_comm]
    conv_rhs => rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun e _ => ?_
    by_cases hcp : ∀ i j : Fin k, i ≠ j → Nat.Coprime (d i) (e j)
    · rw [if_pos hcp, ← Finset.sum_filter, Finset.mul_sum]
    · rw [if_neg hcp]
      push Not at hcp
      rcases hcp with ⟨i, j, hij, hncop⟩
      refine Finset.sum_eq_zero fun n _ => ?_
      have hnot : ¬ (∀ l, Nat.lcm (d l) (e l) ∣ L l n) := by
        intro hl
        have hdi : d i ∣ L i n := dvd_trans (Nat.dvd_lcm_left _ _) (hl i)
        have hej : e j ∣ L j n := dvd_trans (Nat.dvd_lcm_right _ _) (hl j)
        have hpair := L_form_pairwise_coprime (fun heq => hij (h_inj heq)) (hhD i) (hhD j) (hcop i) n
        exact hncop (hpair.coprime_dvd_left hdi |>.coprime_dvd_right hej)
      rw [if_neg hnot]
  rw [hS2_expand]
  -- Step 2: Obtain aStar1, aStar2 maximizing BV errors for x1, x2
  obtain ⟨a1, ha1_cop, ha1_max⟩ := exists_max_coprime_residue x1
  obtain ⟨a2, ha2_cop, ha2_max⟩ := exists_max_coprime_residue x2
  let E1 : ℕ → ℝ := fun q => |theta x1 q (a1 q) - x1 / (Nat.totient q : ℝ)|
  let E2 : ℕ → ℝ := fun q => |theta x2 q (a2 q) - x2 / (Nat.totient q : ℝ)|
  let Pairs := (validSet k W R ×ˢ validSet k W R).filter
    (fun p => p.1 idx = 1 ∧ p.2 idx = 1 ∧ ∀ i j : Fin k, i ≠ j → Nat.Coprime (p.1 i) (p.2 j))
  let qProd : (Fin k → ℕ) × (Fin k → ℕ) → ℕ := fun p => ∏ i : Fin k, Nat.lcm (p.1 i) (p.2 i)
  -- For each pair (d, e) in Pairs, main term is (W / phi W) * X / phi(Q), error <= E2(MWQ) + E1(MWQ)
  have hpair_bound : ∀ p ∈ Pairs,
      |∑ n ∈ (Finset.Ioc X (2 * X)).filter (fun n => ∀ i, Nat.lcm (p.1 i) (p.2 i) ∣ L i n),
          (if (L idx n).Prime then Real.log (L idx n : ℝ) else 0) -
        ((W : ℝ) / (Nat.totient W : ℝ)) * (X : ℝ) / (∏ i : Fin k, (Nat.totient (Nat.lcm (p.1 i) (p.2 i)) : ℝ))| ≤
      E2 (M * W * qProd p) + E1 (M * W * qProd p) := by
    intro p hp
    have hp_mem := Finset.mem_filter.mp hp
    have hdV := mem_validSet_iff.mp (Finset.mem_product.mp hp_mem.1).1
    have heV := mem_validSet_iff.mp (Finset.mem_product.mp hp_mem.1).2
    obtain ⟨a, ha_cop, htheta_eq⟩ := S2_inner_sum_eq_theta_sub hM hMD h h_inj hhD hcop idx hdV heV
      hp_mem.2.1 hp_mem.2.2.1 hp_mem.2.2.2
    rw [htheta_eq]
    have hQ_pos : 0 < qProd p := Finset.prod_pos fun i _ =>
      Nat.pos_of_ne_zero (Nat.lcm_ne_zero (valid_pos_at hdV i).ne' (valid_pos_at heV i).ne')
    have hQ_sq : Squarefree (qProd p) := by
      have hpair : ((Finset.univ : Finset (Fin k)) : Set (Fin k)).Pairwise
          (fun i j => Nat.Coprime (Nat.lcm (p.1 i) (p.2 i)) (Nat.lcm (p.1 j) (p.2 j))) := by
        intro i _ j _ hij
        refine coprime_lcm_left ?_ ?_
        · exact (coprime_lcm_left (valid_pairwise_coprime hdV hij).symm (hp_mem.2.2.2 i j hij).symm).symm
        · exact (coprime_lcm_left (hp_mem.2.2.2 j i hij.symm) (valid_pairwise_coprime heV hij).symm).symm
      have hsq_each : ∀ i : Fin k, Squarefree (Nat.lcm (p.1 i) (p.2 i)) := by
        intro i
        have hmul : Nat.lcm (p.1 i) (p.2 i) = p.1 i * (p.2 i / Nat.gcd (p.1 i) (p.2 i)) := by
          have hg := Nat.gcd_pos_of_pos_left (p.2 i) (valid_pos_at hdV i)
          have h1 : Nat.lcm (p.1 i) (p.2 i) * Nat.gcd (p.1 i) (p.2 i) =
              p.1 i * (p.2 i / Nat.gcd (p.1 i) (p.2 i)) * Nat.gcd (p.1 i) (p.2 i) := by
            rw [Nat.lcm_mul_gcd, mul_assoc, Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)]
          exact Nat.eq_of_mul_eq_mul_right hg h1
        rw [hmul]
        have hcop_part : Nat.Coprime (p.1 i) (p.2 i / Nat.gcd (p.1 i) (p.2 i)) :=
          Nat.coprime_of_dvd' fun q hqp hq1 hq2 => by
            have hq2' : q ∣ p.2 i := dvd_trans hq2 (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right _ _))
            have hqg : q ∣ Nat.gcd (p.1 i) (p.2 i) := Nat.dvd_gcd hq1 hq2'
            have hqq : q * q ∣ p.2 i := by
              rw [← Nat.div_mul_cancel (Nat.gcd_dvd_right (p.1 i) (p.2 i))]
              exact mul_dvd_mul hq2 hqg
            exact absurd (Nat.isUnit_iff.mp (valid_squarefree_at heV i q hqq)) hqp.ne_one
        exact (Nat.squarefree_mul hcop_part).mpr ⟨valid_squarefree_at hdV i,
          (valid_squarefree_at heV i).squarefree_of_dvd (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right _ _))⟩
      have hprod_sq : ∀ s : Finset (Fin k), Squarefree (∏ i ∈ s, Nat.lcm (p.1 i) (p.2 i)) := by
        intro s
        induction s using Finset.induction_on with
        | empty => simp
        | insert j s hj ih =>
          rw [Finset.prod_insert hj]
          have hcj : Nat.Coprime (Nat.lcm (p.1 j) (p.2 j)) (∏ i ∈ s, Nat.lcm (p.1 i) (p.2 i)) :=
            Nat.Coprime.prod_right fun i hi =>
              hpair (Finset.mem_univ j) (Finset.mem_univ i) (fun heq => hj (heq ▸ hi))
          exact (Nat.squarefree_mul hcj).mpr ⟨hsq_each j, ih⟩
      exact hprod_sq Finset.univ
    have hQ_copW : Nat.Coprime (qProd p) W :=
      Nat.Coprime.prod_left fun i _ =>
        coprime_lcm_left (valid_coprime_W_at hdV i) (valid_coprime_W_at heV i)
    have hMW_copQ : Nat.Coprime (M * W) (qProd p) :=
      ((coprime_mul_primorial_iff hM hMD).mpr hQ_copW).symm
    have hphi_q : (Nat.totient (M * W * qProd p) : ℝ) =
        (M : ℝ) * (Nat.totient W : ℝ) * (∏ i : Fin k, (Nat.totient (Nat.lcm (p.1 i) (p.2 i)) : ℝ)) := by
      rw [Nat.totient_mul hMW_copQ, totient_mul_primorial hM hMD, totient_prod_of_squarefree hQ_sq]
      push_cast; rfl
    have hmain_eq : x2 / (Nat.totient (M * W * qProd p) : ℝ) - x1 / (Nat.totient (M * W * qProd p) : ℝ) =
        ((W : ℝ) / (Nat.totient W : ℝ)) * (X : ℝ) /
          (∏ i : Fin k, (Nat.totient (Nat.lcm (p.1 i) (p.2 i)) : ℝ)) := by
      rw [← sub_div, hphi_q]
      have hx_sub : x2 - x1 = (M : ℝ) * (W : ℝ) * (X : ℝ) := by
        dsimp only [x1, x2]; push_cast; ring
      rw [hx_sub]
      have hM_ne : (M : ℝ) ≠ 0 := (Nat.cast_pos.mpr hM).ne'
      have hphiW_ne : (Nat.totient W : ℝ) ≠ 0 := (Nat.cast_pos.mpr (Nat.totient_pos.mpr hW_pos)).ne'
      have hphiQ_ne : (∏ i : Fin k, (Nat.totient (Nat.lcm (p.1 i) (p.2 i)) : ℝ)) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun i _ =>
          (Nat.cast_pos.mpr (Nat.totient_pos.mpr (Nat.pos_of_ne_zero
            (Nat.lcm_ne_zero (valid_pos_at hdV i).ne' (valid_pos_at heV i).ne')))).ne'
      field_simp
    rw [← hmain_eq]
    have hsplit : (theta x2 (M * W * qProd p) a - theta x1 (M * W * qProd p) a) -
        (x2 / (Nat.totient (M * W * qProd p) : ℝ) - x1 / (Nat.totient (M * W * qProd p) : ℝ)) =
        (theta x2 (M * W * qProd p) a - x2 / (Nat.totient (M * W * qProd p) : ℝ)) -
        (theta x1 (M * W * qProd p) a - x1 / (Nat.totient (M * W * qProd p) : ℝ)) := by ring
    rw [hsplit]
    have hq_pos : 1 ≤ M * W * qProd p := Nat.mul_pos hMW_pos hQ_pos
    calc |(theta x2 (M * W * qProd p) a - x2 / (Nat.totient (M * W * qProd p) : ℝ)) -
          (theta x1 (M * W * qProd p) a - x1 / (Nat.totient (M * W * qProd p) : ℝ))|
        ≤ |theta x2 (M * W * qProd p) a - x2 / (Nat.totient (M * W * qProd p) : ℝ)| +
          |theta x1 (M * W * qProd p) a - x1 / (Nat.totient (M * W * qProd p) : ℝ)| := abs_sub _ _
      _ ≤ E2 (M * W * qProd p) + E1 (M * W * qProd p) :=
          add_le_add (ha2_max _ _ hq_pos ha_cop) (ha1_max _ _ hq_pos ha_cop)
  -- Step 3: Bound sum_{p in Pairs} |lam p.1 * lam p.2| * (E2(MWQ) + E1(MWQ)) via Cauchy-Schwarz + BV
  have hQ_maps : ∀ p ∈ Pairs, qProd p ∈ (Finset.Icc 1 (R ^ 2)).filter Squarefree := by
    intro p hp
    have hp_mem := Finset.mem_filter.mp hp
    have hdV := mem_validSet_iff.mp (Finset.mem_product.mp hp_mem.1).1
    have heV := mem_validSet_iff.mp (Finset.mem_product.mp hp_mem.1).2
    have hQ_pos : 1 ≤ qProd p := Finset.prod_pos fun i _ =>
      Nat.pos_of_ne_zero (Nat.lcm_ne_zero (valid_pos_at hdV i).ne' (valid_pos_at heV i).ne')
    have hQ_le : qProd p ≤ R ^ 2 := by
      calc qProd p = ∏ i : Fin k, Nat.lcm (p.1 i) (p.2 i) := rfl
        _ ≤ ∏ i : Fin k, (p.1 i * p.2 i) :=
            Finset.prod_le_prod' fun i _ =>
              Nat.le_of_dvd (Nat.mul_pos (valid_pos_at hdV i) (valid_pos_at heV i))
                (by rw [← Nat.lcm_mul_gcd]; exact dvd_mul_right _ _)
        _ = (∏ i : Fin k, p.1 i) * (∏ i : Fin k, p.2 i) := Finset.prod_mul_distrib
        _ ≤ R * R := Nat.mul_le_mul hdV.2.2 heV.2.2
        _ = R ^ 2 := (sq R).symm
    have hQ_sq : Squarefree (qProd p) := by
      have hpair : ((Finset.univ : Finset (Fin k)) : Set (Fin k)).Pairwise
          (fun i j => Nat.Coprime (Nat.lcm (p.1 i) (p.2 i)) (Nat.lcm (p.1 j) (p.2 j))) := by
        intro i _ j _ hij
        refine coprime_lcm_left ?_ ?_
        · exact (coprime_lcm_left (valid_pairwise_coprime hdV hij).symm (hp_mem.2.2.2 i j hij).symm).symm
        · exact (coprime_lcm_left (hp_mem.2.2.2 j i hij.symm) (valid_pairwise_coprime heV hij).symm).symm
      have hsq_each : ∀ i : Fin k, Squarefree (Nat.lcm (p.1 i) (p.2 i)) := by
        intro i
        have hmul : Nat.lcm (p.1 i) (p.2 i) = p.1 i * (p.2 i / Nat.gcd (p.1 i) (p.2 i)) := by
          have hg := Nat.gcd_pos_of_pos_left (p.2 i) (valid_pos_at hdV i)
          have h1 : Nat.lcm (p.1 i) (p.2 i) * Nat.gcd (p.1 i) (p.2 i) =
              p.1 i * (p.2 i / Nat.gcd (p.1 i) (p.2 i)) * Nat.gcd (p.1 i) (p.2 i) := by
            rw [Nat.lcm_mul_gcd, mul_assoc, Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)]
          exact Nat.eq_of_mul_eq_mul_right hg h1
        rw [hmul]
        have hcop_part : Nat.Coprime (p.1 i) (p.2 i / Nat.gcd (p.1 i) (p.2 i)) :=
          Nat.coprime_of_dvd' fun q hqp hq1 hq2 => by
            have hq2' : q ∣ p.2 i := dvd_trans hq2 (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right _ _))
            have hqg : q ∣ Nat.gcd (p.1 i) (p.2 i) := Nat.dvd_gcd hq1 hq2'
            have hqq : q * q ∣ p.2 i := by
              rw [← Nat.div_mul_cancel (Nat.gcd_dvd_right (p.1 i) (p.2 i))]
              exact mul_dvd_mul hq2 hqg
            exact absurd (Nat.isUnit_iff.mp (valid_squarefree_at heV i q hqq)) hqp.ne_one
        exact (Nat.squarefree_mul hcop_part).mpr ⟨valid_squarefree_at hdV i,
          (valid_squarefree_at heV i).squarefree_of_dvd (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right _ _))⟩
      have hprod_sq : ∀ s : Finset (Fin k), Squarefree (∏ i ∈ s, Nat.lcm (p.1 i) (p.2 i)) := by
        intro s
        induction s using Finset.induction_on with
        | empty => simp
        | insert j s hj ih =>
          rw [Finset.prod_insert hj]
          have hcj : Nat.Coprime (Nat.lcm (p.1 j) (p.2 j)) (∏ i ∈ s, Nat.lcm (p.1 i) (p.2 i)) :=
            Nat.Coprime.prod_right fun i hi =>
              hpair (Finset.mem_univ j) (Finset.mem_univ i) (fun heq => hj (heq ▸ hi))
          exact (Nat.squarefree_mul hcj).mpr ⟨hsq_each j, ih⟩
      exact hprod_sq Finset.univ
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hQ_pos, hQ_le⟩, hQ_sq⟩
  -- Helper: Cauchy-Schwarz bound for E (applied to both (x1, a1, E1) and (x2, a2, E2))
  have hCS_err : ∀ (x : ℝ) (aStar : ℕ → ℕ),
      3 ≤ x → (∀ q, Nat.Coprime (aStar q) q) →
      M * W * R ^ 2 ≤ ⌊Real.sqrt x / Real.log x ^ B⌋₊ →
      M * W * R ^ 2 ≤ ⌊x⌋₊ →
      ∑ Q ∈ (Finset.Icc 1 (R ^ 2)).filter Squarefree,
        ((Pairs.filter (fun p => qProd p = Q)).card : ℝ) *
          |theta x (M * W * Q) (aStar (M * W * Q)) - x / (Nat.totient (M * W * Q) : ℝ)| ≤
      Real.sqrt ((2 * Real.log (R : ℝ) + 1) ^ (9 * k ^ 2)) *
        Real.sqrt (5 * C * x ^ 2 * Real.log x / Real.log x ^ A) := by
    intro x aStar hx3 haStar_cop hQ_BV hQ_fl
    let SQ := (Finset.Icc 1 (R ^ 2)).filter Squarefree
    let E : ℕ → ℝ := fun q => |theta x q (aStar q) - x / (Nat.totient q : ℝ)|
    -- Cauchy-Schwarz: sum_Q (cnt Q / sqrt Q) * (sqrt Q * E(MWQ)) <= sqrt(sum cnt^2/Q) * sqrt(sum Q * E^2)
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq SQ
      (fun Q => ((Pairs.filter (fun p => qProd p = Q)).card : ℝ) / Real.sqrt (Q : ℝ))
      (fun Q => Real.sqrt (Q : ℝ) * E (M * W * Q))
    have hlhs_eq :
        ∑ Q ∈ SQ, (((Pairs.filter (fun p => qProd p = Q)).card : ℝ) / Real.sqrt (Q : ℝ)) *
          (Real.sqrt (Q : ℝ) * E (M * W * Q)) =
        ∑ Q ∈ SQ, ((Pairs.filter (fun p => qProd p = Q)).card : ℝ) * E (M * W * Q) := by
      refine Finset.sum_congr rfl fun Q hQ => ?_
      have hQ_pos : (0 : ℝ) < Q := Nat.cast_pos.mpr (Finset.mem_Icc.mp (Finset.mem_filter.mp hQ).1).1
      have hsq_ne : Real.sqrt (Q : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hQ_pos).ne'
      field_simp
    have hrhs1_eq :
        ∑ Q ∈ SQ, (((Pairs.filter (fun p => qProd p = Q)).card : ℝ) / Real.sqrt (Q : ℝ)) ^ 2 =
        ∑ Q ∈ SQ, (((Pairs.filter (fun p => qProd p = Q)).card : ℝ) ^ 2 / (Q : ℝ)) := by
      refine Finset.sum_congr rfl fun Q hQ => ?_
      have hQ_nonneg : (0 : ℝ) ≤ Q := Nat.cast_nonneg _
      rw [div_pow, Real.sq_sqrt hQ_nonneg]
    have hrhs2_eq :
        ∑ Q ∈ SQ, (Real.sqrt (Q : ℝ) * E (M * W * Q)) ^ 2 =
        ∑ Q ∈ SQ, (Q : ℝ) * E (M * W * Q) ^ 2 := by
      refine Finset.sum_congr rfl fun Q hQ => ?_
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    rw [hlhs_eq, hrhs1_eq, hrhs2_eq] at hcs
    have hsum1_le : ∑ Q ∈ SQ, (((Pairs.filter (fun p => qProd p = Q)).card : ℝ) ^ 2 / (Q : ℝ)) ≤
        (2 * Real.log (R : ℝ) + 1) ^ (9 * k ^ 2) := sum_pair_count_sq_div_le hR idx
    have hsum2_le : ∑ Q ∈ SQ, (Q : ℝ) * E (M * W * Q) ^ 2 ≤
        5 * C * x ^ 2 * Real.log x / Real.log x ^ A := by
      have hterm2 : ∀ Q ∈ SQ, (Q : ℝ) * E (M * W * Q) ^ 2 ≤
          (5 * x * Real.log x) * E (M * W * Q) := by
        intro Q hQ
        have hQ_mem := Finset.mem_Icc.mp (Finset.mem_filter.mp hQ).1
        have hMWQ_pos : 1 ≤ M * W * Q := Nat.mul_pos hMW_pos hQ_mem.1
        have hMWQ_le : M * W * Q ≤ ⌊x⌋₊ := le_trans (Nat.mul_le_mul_left _ hQ_mem.2) hQ_fl
        have hE_triv : E (M * W * Q) ≤ 5 * x * Real.log x / ((M * W * Q : ℕ) : ℝ) :=
          theta_sub_div_totient_abs_le hx3 hMWQ_pos hMWQ_le
        have hE_le2 : (Q : ℝ) * E (M * W * Q) ≤ 5 * x * Real.log x := by
          have hMW1 : (1 : ℝ) ≤ (M * W : ℕ) := by exact_mod_cast hMW_pos
          have hQ_pos_r : (0 : ℝ) < Q := Nat.cast_pos.mpr hQ_mem.1
          calc (Q : ℝ) * E (M * W * Q)
              ≤ (Q : ℝ) * (5 * x * Real.log x / ((M * W : ℕ) * (Q : ℝ))) := by
                have hcast : ((M * W * Q : ℕ) : ℝ) = ((M * W : ℕ) : ℝ) * (Q : ℝ) := by push_cast; ring
                rw [← hcast]
                exact mul_le_mul_of_nonneg_left hE_triv hQ_pos_r.le
            _ = 5 * x * Real.log x / ((M * W : ℕ) : ℝ) := by field_simp
            _ ≤ 5 * x * Real.log x := by
                have hlogx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
                exact div_le_self (by positivity) hMW1
        calc (Q : ℝ) * E (M * W * Q) ^ 2 = ((Q : ℝ) * E (M * W * Q)) * E (M * W * Q) := by ring
          _ ≤ (5 * x * Real.log x) * E (M * W * Q) :=
              mul_le_mul_of_nonneg_right hE_le2 (abs_nonneg _)
      have hBV_sum : ∑ Q ∈ SQ, E (M * W * Q) ≤ C * x / Real.log x ^ A := by
        have hinj : Set.InjOn (fun Q => M * W * Q) (SQ : Set ℕ) :=
          fun _ _ _ _ hEq => Nat.eq_of_mul_eq_mul_left hMW_pos hEq
        have hsub : SQ.image (fun Q => M * W * Q) ⊆ Finset.Icc 1 ⌊Real.sqrt x / Real.log x ^ B⌋₊ := by
          intro q hq
          rcases Finset.mem_image.mp hq with ⟨Q, hQ, rfl⟩
          have hQ_mem := Finset.mem_Icc.mp (Finset.mem_filter.mp hQ).1
          exact Finset.mem_Icc.mpr ⟨Nat.mul_pos hMW_pos hQ_mem.1,
            le_trans (Nat.mul_le_mul_left _ hQ_mem.2) hQ_BV⟩
        calc ∑ Q ∈ SQ, E (M * W * Q)
            = ∑ q ∈ SQ.image (fun Q => M * W * Q), E q := (Finset.sum_image (f := E) hinj).symm
          _ ≤ ∑ q ∈ Finset.Icc 1 ⌊Real.sqrt x / Real.log x ^ B⌋₊, E q :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => abs_nonneg _)
          _ ≤ C * x / Real.log x ^ A := hBV x (by linarith) aStar haStar_cop
      have hlogx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
      calc ∑ Q ∈ SQ, (Q : ℝ) * E (M * W * Q) ^ 2
          ≤ ∑ Q ∈ SQ, (5 * x * Real.log x) * E (M * W * Q) := Finset.sum_le_sum hterm2
        _ = (5 * x * Real.log x) * ∑ Q ∈ SQ, E (M * W * Q) := (Finset.mul_sum ..).symm
        _ ≤ (5 * x * Real.log x) * (C * x / Real.log x ^ A) :=
            mul_le_mul_of_nonneg_left hBV_sum (by positivity)
        _ = 5 * C * x ^ 2 * Real.log x / Real.log x ^ A := by ring
    have hprod_le : (∑ Q ∈ SQ, ((Pairs.filter (fun p => qProd p = Q)).card : ℝ) * E (M * W * Q)) ^ 2 ≤
        (2 * Real.log (R : ℝ) + 1) ^ (9 * k ^ 2) * (5 * C * x ^ 2 * Real.log x / Real.log x ^ A) :=
      le_trans hcs (mul_le_mul hsum1_le hsum2_le
        (Finset.sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
        (pow_nonneg (by linarith [Real.log_nonneg (by exact_mod_cast hR : (1 : ℝ) ≤ R)]) _))
    have hlhs_nn : 0 ≤ ∑ Q ∈ SQ, ((Pairs.filter (fun p => qProd p = Q)).card : ℝ) * E (M * W * Q) :=
      Finset.sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)
    have hsqrt_le := Real.sqrt_le_sqrt hprod_le
    rw [Real.sqrt_sq hlhs_nn, Real.sqrt_mul
      (pow_nonneg (by linarith [Real.log_nonneg (by exact_mod_cast hR : (1 : ℝ) ≤ R)]) _)] at hsqrt_le
    exact hsqrt_le
  -- Step 4: Put main term and BV error term together
  have hS2_as_Pairs :
      ∑ d ∈ (validSet k W R).filter (fun d => d idx = 1),
        ∑ e ∈ (validSet k W R).filter (fun e => e idx = 1 ∧ ∀ i j : Fin k, i ≠ j → Nat.Coprime (d i) (e j)),
          (lambdaOfY k W R y d * lambdaOfY k W R y e) *
            ∑ n ∈ (Finset.Ioc X (2 * X)).filter (fun n => ∀ i, Nat.lcm (d i) (e i) ∣ L i n),
              (if (L idx n).Prime then Real.log (L idx n : ℝ) else 0) =
      ∑ p ∈ Pairs, (lambdaOfY k W R y p.1 * lambdaOfY k W R y p.2) *
        ∑ n ∈ (Finset.Ioc X (2 * X)).filter (fun n => ∀ i, Nat.lcm (p.1 i) (p.2 i) ∣ L i n),
          (if (L idx n).Prime then Real.log (L idx n : ℝ) else 0) := by
    conv_rhs => rw [Finset.sum_filter, Finset.sum_product]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun d _ => ?_
    by_cases hd : d idx = 1
    · rw [if_pos hd, Finset.sum_filter]
      refine Finset.sum_congr rfl fun e _ => by simp [hd]
    · rw [if_neg hd]
      symm
      refine Finset.sum_eq_zero fun e _ => by simp [hd]
  have hM2_as_Pairs :
      ((W : ℝ) / (Nat.totient W : ℝ)) * (X : ℝ) *
        (∑ d ∈ (validSet k W R).filter (fun d => d idx = 1),
          ∑ e ∈ (validSet k W R).filter (fun e => e idx = 1 ∧ ∀ i j : Fin k, i ≠ j → Nat.Coprime (d i) (e j)),
            (lambdaOfY k W R y d * lambdaOfY k W R y e) /
              (∏ i : Fin k, (Nat.totient (Nat.lcm (d i) (e i)) : ℝ))) =
      ∑ p ∈ Pairs, (lambdaOfY k W R y p.1 * lambdaOfY k W R y p.2) *
        (((W : ℝ) / (Nat.totient W : ℝ)) * (X : ℝ) /
          (∏ i : Fin k, (Nat.totient (Nat.lcm (p.1 i) (p.2 i)) : ℝ))) := by
    conv_rhs => rw [Finset.sum_filter, Finset.sum_product]
    rw [Finset.mul_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun d _ => ?_
    by_cases hd : d idx = 1
    · rw [if_pos hd, Finset.mul_sum, Finset.sum_filter]
      refine Finset.sum_congr rfl fun e _ => ?_
      by_cases he : e idx = 1 ∧ ∀ i j : Fin k, i ≠ j → Nat.Coprime (d i) (e j)
      · rw [if_pos he, if_pos ⟨hd, he⟩]; ring
      · rw [if_neg he, if_neg (fun h => he h.2)]
    · rw [if_neg hd]
      symm
      refine Finset.sum_eq_zero fun e _ => by simp [hd]
  rw [hS2_as_Pairs, hM2_as_Pairs]
  have hdiff_bound :
      (∑ p ∈ Pairs, (lambdaOfY k W R y p.1 * lambdaOfY k W R y p.2) *
        (((W : ℝ) / (Nat.totient W : ℝ)) * (X : ℝ) /
          (∏ i : Fin k, (Nat.totient (Nat.lcm (p.1 i) (p.2 i)) : ℝ)))) -
      (∑ p ∈ Pairs, (lambdaOfY k W R y p.1 * lambdaOfY k W R y p.2) *
        ∑ n ∈ (Finset.Ioc X (2 * X)).filter (fun n => ∀ i, Nat.lcm (p.1 i) (p.2 i) ∣ L i n),
          (if (L idx n).Prime then Real.log (L idx n : ℝ) else 0)) ≤
      (2 * Real.log (R : ℝ) + 2) ^ (6 * k) *
        Real.sqrt ((2 * Real.log (R : ℝ) + 1) ^ (9 * k ^ 2)) *
        (Real.sqrt (5 * C * x2 ^ 2 * Real.log x2 / Real.log x2 ^ A) +
          Real.sqrt (5 * C * x1 ^ 2 * Real.log x1 / Real.log x1 ^ A)) := by
    rw [← Finset.sum_sub_distrib]
    have hlam := lambdaOfY_abs_le (W := W) hR y hy0 hy1
    have hlogR_nn : 0 ≤ Real.log (R : ℝ) := Real.log_nonneg (by exact_mod_cast hR)
    have hlam_sq : ∀ p : (Fin k → ℕ) × (Fin k → ℕ),
        |lambdaOfY k W R y p.1 * lambdaOfY k W R y p.2| ≤ (2 * Real.log (R : ℝ) + 2) ^ (6 * k) := by
      intro p
      rw [abs_mul]
      calc |lambdaOfY k W R y p.1| * |lambdaOfY k W R y p.2|
          ≤ (2 * Real.log (R : ℝ) + 2) ^ (3 * k) * (2 * Real.log (R : ℝ) + 2) ^ (3 * k) :=
            mul_le_mul (hlam p.1) (hlam p.2) (abs_nonneg _) (by positivity)
        _ = (2 * Real.log (R : ℝ) + 2) ^ (6 * k) := by rw [← pow_add]; ring_nf
    have hstep1 :
        ∑ p ∈ Pairs,
          ((lambdaOfY k W R y p.1 * lambdaOfY k W R y p.2) *
            (((W : ℝ) / (Nat.totient W : ℝ)) * (X : ℝ) /
              (∏ i : Fin k, (Nat.totient (Nat.lcm (p.1 i) (p.2 i)) : ℝ))) -
          (lambdaOfY k W R y p.1 * lambdaOfY k W R y p.2) *
            ∑ n ∈ (Finset.Ioc X (2 * X)).filter (fun n => ∀ i, Nat.lcm (p.1 i) (p.2 i) ∣ L i n),
              (if (L idx n).Prime then Real.log (L idx n : ℝ) else 0)) ≤
        (2 * Real.log (R : ℝ) + 2) ^ (6 * k) *
          ∑ p ∈ Pairs, (E2 (M * W * qProd p) + E1 (M * W * qProd p)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun p hp => ?_
      have heq : (lambdaOfY k W R y p.1 * lambdaOfY k W R y p.2) *
            (((W : ℝ) / (Nat.totient W : ℝ)) * (X : ℝ) /
              (∏ i : Fin k, (Nat.totient (Nat.lcm (p.1 i) (p.2 i)) : ℝ))) -
          (lambdaOfY k W R y p.1 * lambdaOfY k W R y p.2) *
            ∑ n ∈ (Finset.Ioc X (2 * X)).filter (fun n => ∀ i, Nat.lcm (p.1 i) (p.2 i) ∣ L i n),
              (if (L idx n).Prime then Real.log (L idx n : ℝ) else 0) =
          -(lambdaOfY k W R y p.1 * lambdaOfY k W R y p.2) *
            ((∑ n ∈ (Finset.Ioc X (2 * X)).filter (fun n => ∀ i, Nat.lcm (p.1 i) (p.2 i) ∣ L i n),
              (if (L idx n).Prime then Real.log (L idx n : ℝ) else 0)) -
            ((W : ℝ) / (Nat.totient W : ℝ)) * (X : ℝ) /
              (∏ i : Fin k, (Nat.totient (Nat.lcm (p.1 i) (p.2 i)) : ℝ))) := by ring
      rw [heq]
      calc _ ≤ |-(lambdaOfY k W R y p.1 * lambdaOfY k W R y p.2) * _| := le_abs_self _
        _ = |lambdaOfY k W R y p.1 * lambdaOfY k W R y p.2| * |_ - _| := by rw [abs_mul, abs_neg]
        _ ≤ (2 * Real.log (R : ℝ) + 2) ^ (6 * k) * (E2 (M * W * qProd p) + E1 (M * W * qProd p)) :=
            mul_le_mul (hlam_sq p) (hpair_bound p hp) (abs_nonneg _) (by positivity)
    have hgroup :
        ∑ p ∈ Pairs, (E2 (M * W * qProd p) + E1 (M * W * qProd p)) =
        (∑ Q ∈ (Finset.Icc 1 (R ^ 2)).filter Squarefree,
          ((Pairs.filter (fun p => qProd p = Q)).card : ℝ) * E2 (M * W * Q)) +
        (∑ Q ∈ (Finset.Icc 1 (R ^ 2)).filter Squarefree,
          ((Pairs.filter (fun p => qProd p = Q)).card : ℝ) * E1 (M * W * Q)) := by
      rw [← Finset.sum_fiberwise_of_maps_to hQ_maps, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun Q _ => ?_
      have h1 : ∑ p ∈ Pairs.filter (fun p => qProd p = Q), (E2 (M * W * qProd p) + E1 (M * W * qProd p)) =
          ∑ _p ∈ Pairs.filter (fun p => qProd p = Q), (E2 (M * W * Q) + E1 (M * W * Q)) :=
        Finset.sum_congr rfl fun p hp => by rw [(Finset.mem_filter.mp hp).2]
      rw [h1, Finset.sum_const, nsmul_eq_mul, mul_add]
    have hle12 : M * W * X ≤ 2 * M * W * X := by
      calc M * W * X = 1 * (M * W * X) := (one_mul _).symm
        _ ≤ 2 * (M * W * X) := Nat.mul_le_mul_right _ (by omega)
        _ = 2 * M * W * X := by ring
    have hx2_ge3 : 3 ≤ x2 := by
      have h12 : x1 ≤ x2 := by
        dsimp only [x1, x2]
        exact_mod_cast (by omega : M * W * X + (M * v0 + b + h idx) ≤ 2 * M * W * X + (M * v0 + b + h idx))
      linarith
    have hQ_fl1' : M * W * R ^ 2 ≤ ⌊x1⌋₊ := by
      dsimp only [x1]; rw [Nat.floor_natCast]; exact hQ_le_fl1
    have hQ_fl2' : M * W * R ^ 2 ≤ ⌊x2⌋₊ := by
      dsimp only [x2]; rw [Nat.floor_natCast]
      exact le_trans hQ_le_fl1 (Nat.add_le_add_right hle12 _)
    have hCS1 := hCS_err x1 a1 hx1_ge3 ha1_cop hQ_le_x1 hQ_fl1'
    have hCS2 := hCS_err x2 a2 hx2_ge3 ha2_cop hQ_le_x2 hQ_fl2'
    calc _ ≤ (2 * Real.log (R : ℝ) + 2) ^ (6 * k) *
              ((∑ Q ∈ (Finset.Icc 1 (R ^ 2)).filter Squarefree,
                ((Pairs.filter (fun p => qProd p = Q)).card : ℝ) * E2 (M * W * Q)) +
              (∑ Q ∈ (Finset.Icc 1 (R ^ 2)).filter Squarefree,
                ((Pairs.filter (fun p => qProd p = Q)).card : ℝ) * E1 (M * W * Q))) := by
            rw [← hgroup]; exact hstep1
      _ ≤ (2 * Real.log (R : ℝ) + 2) ^ (6 * k) *
            (Real.sqrt ((2 * Real.log (R : ℝ) + 1) ^ (9 * k ^ 2)) *
              Real.sqrt (5 * C * x2 ^ 2 * Real.log x2 / Real.log x2 ^ A) +
            Real.sqrt ((2 * Real.log (R : ℝ) + 1) ^ (9 * k ^ 2)) *
              Real.sqrt (5 * C * x1 ^ 2 * Real.log x1 / Real.log x1 ^ A)) :=
            mul_le_mul_of_nonneg_left (add_le_add hCS2 hCS1) (by positivity)
      _ = _ := by ring
  linarith

-- ## Section 4: Maynard-Tao weight, 1D Riemann block bounds, and discrete Chebyshev

noncomputable def tVal (k R : ℕ) (n : ℕ) : ℝ :=
  (k : ℝ) * Real.log (n : ℝ) / Real.log (R : ℝ)

noncomputable def gWeight (A : ℝ) (k R : ℕ) (n : ℕ) : ℝ :=
  1 / (1 + A * tVal k R n)

noncomputable def yWeight (A : ℝ) (k D0 R U : ℕ) (r : Fin k → ℕ) : ℝ := by
  classical
  exact if Valid (primorial D0) R r ∧ ∀ i, r i ≤ U then ∏ i : Fin k, gWeight A k R (r i) else 0

lemma tVal_nonneg {k R n : ℕ} (hR : 2 ≤ R) (hn : 1 ≤ n) : 0 ≤ tVal k R n := by
  unfold tVal
  have hlogR : 0 < Real.log (R : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < R))
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hlogn) hlogR.le

lemma gWeight_nonneg {A : ℝ} (hA : 0 < A) {k R n : ℕ} (hR : 2 ≤ R) (hn : 1 ≤ n) :
    0 ≤ gWeight A k R n := by
  unfold gWeight
  have ht := tVal_nonneg (k := k) hR hn
  have hden : 0 < 1 + A * tVal k R n := by nlinarith
  exact div_nonneg (by norm_num) hden.le

lemma gWeight_le_one {A : ℝ} (hA : 0 < A) {k R n : ℕ} (hR : 2 ≤ R) (hn : 1 ≤ n) :
    gWeight A k R n ≤ 1 := by
  unfold gWeight
  have ht := tVal_nonneg (k := k) hR hn
  rw [div_le_one (by nlinarith)]
  nlinarith

lemma gWeight_antitone {A : ℝ} (hA : 0 < A) {k R m n : ℕ} (hR : 2 ≤ R) (hm : 1 ≤ m) (hmn : m ≤ n) :
    gWeight A k R n ≤ gWeight A k R m := by
  unfold gWeight tVal
  have hlogR : 0 < Real.log (R : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < R))
  have hlog_le : Real.log (m : ℝ) ≤ Real.log (n : ℝ) :=
    Real.log_le_log (Nat.cast_pos.mpr hm) (Nat.cast_le.mpr hmn)
  have ht_le : (k : ℝ) * Real.log (m : ℝ) / Real.log (R : ℝ) ≤
      (k : ℝ) * Real.log (n : ℝ) / Real.log (R : ℝ) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlog_le (Nat.cast_nonneg _)) hlogR.le
  have htm : 0 ≤ (k : ℝ) * Real.log (m : ℝ) / Real.log (R : ℝ) := tVal_nonneg hR hm
  refine div_le_div_of_nonneg_left (by norm_num) (by nlinarith) (by nlinarith)

lemma yWeight_bounds {A : ℝ} (hA : 0 < A) {k D0 R U : ℕ} (hR : 2 ≤ R) :
    (∀ r, 0 ≤ yWeight A k D0 R U r) ∧
    (∀ r, yWeight A k D0 R U r ≤ 1) ∧
    (∀ r, (∃ i, U < r i) → yWeight A k D0 R U r = 0) ∧
    (∀ r (idx : Fin k), yWeight A k D0 R U r ≤ gWeight A k R (r idx)) := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r; unfold yWeight
    split_ifs with h
    · exact Finset.prod_nonneg fun i _ => gWeight_nonneg hA hR (valid_pos_at h.1 i)
    · exact le_refl 0
  · intro r; unfold yWeight
    split_ifs with h
    · calc ∏ i : Fin k, gWeight A k R (r i)
          ≤ ∏ _i : Fin k, (1 : ℝ) :=
            Finset.prod_le_prod (fun i _ => gWeight_nonneg hA hR (valid_pos_at h.1 i))
              (fun i _ => gWeight_le_one hA hR (valid_pos_at h.1 i))
        _ = 1 := Finset.prod_const_one
    · norm_num
  · intro r ⟨i, hi⟩; unfold yWeight
    rw [if_neg (fun h => not_le_of_gt hi (h.2 i))]
  · intro r idx; unfold yWeight
    split_ifs with h
    · rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ idx)]
      have hrest : ∏ i ∈ Finset.univ.erase idx, gWeight A k R (r i) ≤ 1 := by
        calc ∏ i ∈ Finset.univ.erase idx, gWeight A k R (r i)
            ≤ ∏ _i ∈ Finset.univ.erase idx, (1 : ℝ) :=
              Finset.prod_le_prod (fun i _ => gWeight_nonneg hA hR (valid_pos_at h.1 i))
                (fun i _ => gWeight_le_one hA hR (valid_pos_at h.1 i))
          _ = 1 := Finset.prod_const_one
      calc gWeight A k R (r idx) * ∏ i ∈ Finset.univ.erase idx, gWeight A k R (r i)
          ≤ gWeight A k R (r idx) * 1 :=
            mul_le_mul_of_nonneg_left hrest (gWeight_nonneg hA hR (valid_pos_at h.1 idx))
        _ = gWeight A k R (r idx) := mul_one _
    · -- Even if r idx = 0, gWeight A k R 0 = 1 / (1 + 0) = 1 >= 0!
      unfold gWeight tVal
      by_cases h0 : r idx = 0
      · simp [h0]
      · exact gWeight_nonneg hA hR (Nat.pos_of_ne_zero h0)

/-- Trivial upper bound T1 <= Z2^k. -/
lemma T1_le_Z2_pow {A : ℝ} (hA : 0 < A) {k D0 R U : ℕ} (hR : 2 ≤ R) :
    let W := primorial D0
    let S_U := (Finset.Icc 1 U).filter (fun s => Squarefree s ∧ Nat.Coprime s W)
    let Z2 := ∑ s ∈ S_U, (gWeight A k R s) ^ 2 / (Nat.totient s : ℝ)
    ∑ r ∈ validSet k W R, (yWeight A k D0 R U r) ^ 2 / (∏ i : Fin k, (Nat.totient (r i) : ℝ)) ≤
      Z2 ^ k := by
  classical
  intro W S_U Z2
  let Good := (validSet k W R).filter (fun r => ∀ i, r i ≤ U)
  have hzero :
      ∑ r ∈ validSet k W R, (yWeight A k D0 R U r) ^ 2 / (∏ i : Fin k, (Nat.totient (r i) : ℝ)) =
      ∑ r ∈ Good, ∏ i : Fin k, ((gWeight A k R (r i)) ^ 2 / (Nat.totient (r i) : ℝ)) := by
    have h1 :
        ∑ r ∈ validSet k W R, (yWeight A k D0 R U r) ^ 2 / (∏ i : Fin k, (Nat.totient (r i) : ℝ)) =
        ∑ r ∈ Good, (yWeight A k D0 R U r) ^ 2 / (∏ i : Fin k, (Nat.totient (r i) : ℝ)) := by
      symm
      refine Finset.sum_subset (Finset.filter_subset _ _) fun r hr hnot => ?_
      have hex : ∃ i, U < r i := by
        by_contra hall; push Not at hall
        exact hnot (Finset.mem_filter.mpr ⟨hr, hall⟩)
      rw [(yWeight_bounds hA hR).2.2.1 r hex]
      simp
    rw [h1]
    refine Finset.sum_congr rfl fun r hr => ?_
    have hrV := mem_validSet_iff.mp (Finset.mem_filter.mp hr).1
    have hrU := (Finset.mem_filter.mp hr).2
    unfold yWeight
    rw [if_pos ⟨hrV, hrU⟩, ← Finset.prod_pow, Finset.prod_div_distrib]
  rw [hzero]
  have hsub : Good ⊆ Fintype.piFinset (fun _ : Fin k => S_U) := by
    intro r hr
    have hrV := mem_validSet_iff.mp (Finset.mem_filter.mp hr).1
    have hrU := (Finset.mem_filter.mp hr).2
    exact Fintype.mem_piFinset.mpr fun i => Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨valid_pos_at hrV i, hrU i⟩, valid_squarefree_at hrV i, valid_coprime_W_at hrV i⟩
  calc ∑ r ∈ Good, ∏ i : Fin k, ((gWeight A k R (r i)) ^ 2 / (Nat.totient (r i) : ℝ))
      ≤ ∑ r ∈ Fintype.piFinset (fun _ : Fin k => S_U),
          ∏ i : Fin k, ((gWeight A k R (r i)) ^ 2 / (Nat.totient (r i) : ℝ)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun _ _ _ => Finset.prod_nonneg fun _ _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
    _ = Z2 ^ k := by
        rw [sum_piFinset_prod (fun _ : Fin k => S_U) (fun _ s => (gWeight A k R s) ^ 2 / (Nat.totient s : ℝ))]
        simp [Z2]

/-- Exact 1D identity: t * g(t)^2 = (1 / A) * (g(t) - g(t)^2). -/
lemma tVal_mul_gWeight_sq {A : ℝ} (hA : 0 < A) {k R s : ℕ} (hR : 2 ≤ R) (hs : 1 ≤ s) :
    tVal k R s * (gWeight A k R s) ^ 2 = (1 / A) * (gWeight A k R s - (gWeight A k R s) ^ 2) := by
  unfold gWeight
  have ht := tVal_nonneg (k := k) hR hs
  have hden : 1 + A * tVal k R s ≠ 0 := by nlinarith
  field_simp
  ring

/-- Pointwise bound: t^2 * g(t)^2 <= 1 / A^2. -/
lemma tVal_sq_mul_gWeight_sq_le {A : ℝ} (hA : 0 < A) {k R s : ℕ} (hR : 2 ≤ R) (hs : 1 ≤ s) :
    (tVal k R s) ^ 2 * (gWeight A k R s) ^ 2 ≤ 1 / A ^ 2 := by
  unfold gWeight
  have ht := tVal_nonneg (k := k) hR hs
  have hden : 0 < 1 + A * tVal k R s := by nlinarith
  have h1 : tVal k R s / (1 + A * tVal k R s) ≤ 1 / A := by
    rw [div_le_div_iff₀ hden hA]
    nlinarith
  have hsq : (tVal k R s / (1 + A * tVal k R s)) ^ 2 ≤ (1 / A) ^ 2 :=
    pow_le_pow_left₀ (div_nonneg ht hden.le) h1 2
  calc (tVal k R s) ^ 2 * (1 / (1 + A * tVal k R s)) ^ 2
      = (tVal k R s / (1 + A * tVal k R s)) ^ 2 := by ring
    _ ≤ (1 / A) ^ 2 := hsq
    _ = 1 / A ^ 2 := by ring

/-- Antitone weight sum over multiples of a prime p in S_U is at most 1/(p-1) times the full sum. -/
lemma sum_div_prime_le_inv_pred {D0 U p : ℕ} (hp : p.Prime)
    (w : ℕ → ℝ) (hw0 : ∀ n, 1 ≤ n → 0 ≤ w n) (hw_anti : ∀ m n, 1 ≤ m → m ≤ n → w n ≤ w m) :
    let W := primorial D0
    let S_U := (Finset.Icc 1 U).filter (fun s => Squarefree s ∧ Nat.Coprime s W)
    ∑ s ∈ S_U.filter (fun s => p ∣ s), w s / (Nat.totient s : ℝ) ≤
      (1 / ((p : ℝ) - 1)) * ∑ s ∈ S_U, w s / (Nat.totient s : ℝ) := by
  classical
  intro W S_U
  let divP : ℕ → ℕ := fun s => s / p
  have hmaps : ∀ s ∈ S_U.filter (fun s => p ∣ s), divP s ∈ S_U := by
    intro s hs
    have hsU := Finset.mem_filter.mp (Finset.mem_filter.mp hs).1
    have hps := (Finset.mem_filter.mp hs).2
    have hs1 : 1 ≤ s := (Finset.mem_Icc.mp hsU.1).1
    have hs_le : s ≤ U := (Finset.mem_Icc.mp hsU.1).2
    have hq_dvd : s / p ∣ s := Nat.div_dvd_of_dvd hps
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨Nat.div_pos (Nat.le_of_dvd hs1 hps) hp.pos, le_trans (Nat.div_le_self s p) hs_le⟩,
      hsU.2.1.squarefree_of_dvd hq_dvd, hsU.2.2.coprime_dvd_left hq_dvd⟩
  have hinj : Set.InjOn divP ((S_U.filter (fun s => p ∣ s)) : Set ℕ) := by
    intro s₁ hs₁ s₂ hs₂ hEq
    have h1 := (Finset.mem_filter.mp hs₁).2
    have h2 := (Finset.mem_filter.mp hs₂).2
    dsimp only [divP] at hEq
    rw [← Nat.mul_div_cancel' h1, ← Nat.mul_div_cancel' h2, hEq]
  have hp1 : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
    have := hp.two_le
    rw [Nat.cast_sub (by omega)]; simp
  calc ∑ s ∈ S_U.filter (fun s => p ∣ s), w s / (Nat.totient s : ℝ)
      ≤ ∑ s ∈ S_U.filter (fun s => p ∣ s), (1 / ((p : ℝ) - 1)) * (w (divP s) / (Nat.totient (divP s) : ℝ)) := by
        refine Finset.sum_le_sum fun s hs => ?_
        have hsU := Finset.mem_filter.mp (Finset.mem_filter.mp hs).1
        have hps := (Finset.mem_filter.mp hs).2
        have hmul : p * divP s = s := Nat.mul_div_cancel' hps
        have hcop : Nat.Coprime p (divP s) := Nat.coprime_of_squarefree_mul (hmul.symm ▸ hsU.2.1)
        have htot : (Nat.totient s : ℝ) = ((p : ℝ) - 1) * (Nat.totient (divP s) : ℝ) := by
          have : Nat.totient s = (p - 1) * Nat.totient (divP s) := by
            conv_lhs => rw [← hmul]
            rw [Nat.totient_mul hcop, Nat.totient_prime hp]
          have hcast : (Nat.totient s : ℝ) = ((p - 1 : ℕ) : ℝ) * (Nat.totient (divP s) : ℝ) := by
            exact_mod_cast this
          rw [hcast, hp1]
        have hq1 : 1 ≤ divP s := Nat.div_pos (Nat.le_of_dvd (Finset.mem_Icc.mp hsU.1).1 hps) hp.pos
        have hw_le : w s ≤ w (divP s) := hw_anti (divP s) s hq1 (Nat.div_le_self s p)
        have hp_r : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
        rw [htot]
        have heq : (1 / ((p : ℝ) - 1)) * (w (divP s) / (Nat.totient (divP s) : ℝ)) =
            w (divP s) / (((p : ℝ) - 1) * (Nat.totient (divP s) : ℝ)) := by
          rw [one_div, div_eq_mul_inv, div_eq_mul_inv, mul_inv]; ring
        rw [heq]
        exact div_le_div_of_nonneg_right hw_le (mul_nonneg (by linarith) (Nat.cast_nonneg _))
    _ = (1 / ((p : ℝ) - 1)) * ∑ s ∈ S_U.filter (fun s => p ∣ s), w (divP s) / (Nat.totient (divP s) : ℝ) :=
        (Finset.mul_sum ..).symm
    _ = (1 / ((p : ℝ) - 1)) * ∑ t ∈ (S_U.filter (fun s => p ∣ s)).image divP, w t / (Nat.totient t : ℝ) := by
        rw [Finset.sum_image (f := fun t => w t / (Nat.totient t : ℝ)) hinj]
    _ ≤ (1 / ((p : ℝ) - 1)) * ∑ t ∈ S_U, w t / (Nat.totient t : ℝ) := by
        have hp_r : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
        refine mul_le_mul_of_nonneg_left ?_ (div_nonneg (by norm_num) (by linarith))
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun t ht _ =>
          div_nonneg (hw0 t (Finset.mem_Icc.mp (Finset.mem_filter.mp ht).1).1) (Nat.cast_nonneg _)
        intro t ht
        rcases Finset.mem_image.mp ht with ⟨s, hs, rfl⟩
        exact hmaps s hs

/-- Union bound for nonnegative Finset sums. -/
lemma finset_sum_union_le {α : Type*} [DecidableEq α] {s t : Finset α} {f : α → ℝ}
    (hf : ∀ x ∈ s ∪ t, 0 ≤ f x) :
    ∑ x ∈ s ∪ t, f x ≤ ∑ x ∈ s, f x + ∑ x ∈ t, f x := by
  have h := Finset.sum_union_inter (s₁ := s) (s₂ := t) (f := f)
  have hnn : 0 ≤ ∑ x ∈ s ∩ t, f x :=
    Finset.sum_nonneg fun x hx => hf x (Finset.mem_union_left t (Finset.mem_inter.mp hx).1)
  linarith

/-- Union bound for nonnegative Finset biUnion sums. -/
lemma finset_sum_biUnion_le {α β : Type*} [DecidableEq β] {s : Finset α} {t : α → Finset β}
    {f : β → ℝ} (hf : ∀ a ∈ s, ∀ x ∈ t a, 0 ≤ f x) :
    ∑ x ∈ s.biUnion t, f x ≤ ∑ a ∈ s, ∑ x ∈ t a, f x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    have hf_union : ∀ x ∈ t a ∪ s.biUnion t, 0 ≤ f x := fun x hx => by
      rcases Finset.mem_union.mp hx with hx1 | hx2
      · exact hf a (Finset.mem_insert_self a s) x hx1
      · rcases Finset.mem_biUnion.mp hx2 with ⟨b, hb, hxb⟩
        exact hf b (Finset.mem_insert_of_mem hb) x hxb
    have h1 := finset_sum_union_le hf_union
    have h2 := ih (fun b hb => hf b (Finset.mem_insert_of_mem hb))
    linarith

set_option maxHeartbeats 600000 in
/-- Discrete Chebyshev lower bound on T_2(idx) for Maynard-Tao weights. -/
lemma T2_ge_chebyshev {A T : ℝ} (hA : 0 < A) (_hT : 0 < T)
    {k D0 R U : ℕ} (hk : 2 ≤ k) (hD : 4 ≤ D0) (hR : 2 ≤ R) (hU1 : 1 ≤ U)
    (hU_pow : (U : ℝ) ≤ (R : ℝ) ^ (T / (k : ℝ))) (idx : Fin k) :
    let W := primorial D0
    let S_U := (Finset.Icc 1 U).filter (fun s => Squarefree s ∧ Nat.Coprime s W)
    let M_U := ∑ s ∈ S_U, (1 / (Nat.totient s : ℝ))
    let Z1 := ∑ s ∈ S_U, gWeight A k R s / (Nat.totient s : ℝ)
    let Z2 := ∑ s ∈ S_U, (gWeight A k R s) ^ 2 / (Nat.totient s : ℝ)
    let mu := (Z1 - Z2) / (A * Z2)
    let delta := (k : ℝ) - T - ((k - 1 : ℕ) : ℝ) * mu
    0 < delta →
    Z1 ^ 2 * Z2 ^ (k - 1) *
      (1 - ((k - 1 : ℕ) : ℝ) * (M_U / (A ^ 2 * Z2)) / delta ^ 2 -
        (3 * (k : ℝ) ^ 2 / ((D0 : ℝ) - 2))) ≤
    ∑ u ∈ (validSet k W R).filter (fun u => u idx = 1),
      (YBar W R (yWeight A k D0 R U) idx u) ^ 2 /
        (∏ i ∈ Finset.univ.erase idx, (Nat.totient (u i) : ℝ)) := by
  classical
  intro W S_U M_U Z1 Z2 mu delta hdelta
  have h1SU : 1 ∈ S_U :=
    Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_refl 1, hU1⟩, squarefree_one, Nat.coprime_one_left _⟩
  have hZ1_pos : 0 < Z1 := by
    have h1 : 0 < gWeight A k R 1 / (Nat.totient 1 : ℝ) := by
      unfold gWeight tVal; simp
    exact lt_of_lt_of_le h1 (Finset.single_le_sum (f := fun s => gWeight A k R s / (Nat.totient s : ℝ))
      (fun s hs => div_nonneg (gWeight_nonneg hA hR (Finset.mem_Icc.mp (Finset.mem_filter.mp hs).1).1)
        (Nat.cast_nonneg _)) h1SU)
  have hZ2_pos : 0 < Z2 := by
    have h1 : 0 < (gWeight A k R 1) ^ 2 / (Nat.totient 1 : ℝ) := by
      unfold gWeight tVal; simp
    exact lt_of_lt_of_le h1 (Finset.single_le_sum (f := fun s => (gWeight A k R s) ^ 2 / (Nat.totient s : ℝ))
      (fun s hs => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)) h1SU)
  have hlogR_pos : 0 < Real.log (R : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < R))
  have hcard_er : (Finset.univ.erase idx).card = k - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ idx), Finset.card_univ, Fintype.card_fin]
  let w : ℕ → ℝ := fun s => (gWeight A k R s) ^ 2 / (Nat.totient s : ℝ)
  have hw_nn : ∀ s, 0 ≤ w s := fun s => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
  let domU : Fin k → Finset ℕ := fun i => if i = idx then {1} else S_U
  let PiU := Fintype.piFinset domU
  let Good := PiU.filter (fun u => Squarefree (∏ i ∈ Finset.univ.erase idx, u i) ∧
    (∏ i ∈ Finset.univ.erase idx, u i) * U ≤ R)
  -- Step 1: Good is a subset of (validSet k W R).filter (fun u => u idx = 1)
  have hGood_sub : Good ⊆ (validSet k W R).filter (fun u => u idx = 1) := by
    intro u hu
    have hpi := Fintype.mem_piFinset.mp (Finset.mem_filter.mp hu).1
    have hcond := (Finset.mem_filter.mp hu).2
    have huidx : u idx = 1 := by simpa [domU] using hpi idx
    have hprod_eq : ∏ i : Fin k, u i = ∏ i ∈ Finset.univ.erase idx, u i := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ idx), huidx, one_mul]
    have hcopW : Nat.Coprime (∏ i : Fin k, u i) W := by
      refine Nat.Coprime.prod_left fun i _ => ?_
      by_cases hi : i = idx
      · subst hi; rw [huidx]; exact Nat.coprime_one_left W
      · have := hpi i; simp only [domU, if_neg hi] at this
        exact (Finset.mem_filter.mp this).2.2
    have hleR : ∏ i : Fin k, u i ≤ R := by
      rw [hprod_eq]
      calc ∏ i ∈ Finset.univ.erase idx, u i
          = (∏ i ∈ Finset.univ.erase idx, u i) * 1 := (mul_one _).symm
        _ ≤ (∏ i ∈ Finset.univ.erase idx, u i) * U := Nat.mul_le_mul_left _ hU1
        _ ≤ R := hcond.2
    exact Finset.mem_filter.mpr ⟨mem_validSet_iff.mpr ⟨hprod_eq.symm ▸ hcond.1, hcopW, hleR⟩, huidx⟩
  -- Step 2: For u in Good, YBar idx u = (prod_{er} g(u i)) * (Z1 - B u)
  let B : (Fin k → ℕ) → ℝ := fun u =>
    ∑ s ∈ S_U.filter (fun s => ¬ Nat.Coprime s (∏ i ∈ Finset.univ.erase idx, u i)),
      gWeight A k R s / (Nat.totient s : ℝ)
  have hYBar_good : ∀ u ∈ Good,
      YBar W R (yWeight A k D0 R U) idx u =
        (∏ i ∈ Finset.univ.erase idx, gWeight A k R (u i)) * (Z1 - B u) := by
    intro u hu
    have hpi := Fintype.mem_piFinset.mp (Finset.mem_filter.mp hu).1
    have hcond := (Finset.mem_filter.mp hu).2
    have huU : ∀ i ∈ Finset.univ.erase idx, u i ∈ S_U := fun i hi => by
      have := hpi i; simpa [domU, (Finset.mem_erase.mp hi).1] using this
    have hcop_er_W : Nat.Coprime (∏ i ∈ Finset.univ.erase idx, u i) W :=
      Nat.Coprime.prod_left fun i hi => (Finset.mem_filter.mp (huU i hi)).2.2
    have hZ1_split : Z1 - B u =
        ∑ s ∈ S_U.filter (fun s => Nat.Coprime s (∏ i ∈ Finset.univ.erase idx, u i)),
          gWeight A k R s / (Nat.totient s : ℝ) := by
      have h := Finset.sum_filter_add_sum_filter_not S_U
        (fun s => Nat.Coprime s (∏ i ∈ Finset.univ.erase idx, u i))
        (fun s => gWeight A k R s / (Nat.totient s : ℝ))
      dsimp only [Z1, B]; linarith
    rw [hZ1_split, Finset.mul_sum]
    unfold YBar
    -- Restrict YBar to r idx <= U (others have yWeight = 0)
    let F := (validSet k W R).filter (fun r => ∀ i ∈ Finset.univ.erase idx, r i = u i)
    have hF_trim :
        ∑ r ∈ F, yWeight A k D0 R U r / (Nat.totient (r idx) : ℝ) =
        ∑ r ∈ F.filter (fun r => r idx ≤ U), yWeight A k D0 R U r / (Nat.totient (r idx) : ℝ) := by
      symm
      refine Finset.sum_subset (Finset.filter_subset _ _) fun r hr hnot => ?_
      have hgt : U < r idx := by
        by_contra hle; push Not at hle; exact hnot (Finset.mem_filter.mpr ⟨hr, hle⟩)
      simp [(yWeight_bounds hA hR).2.2.1 r ⟨idx, hgt⟩]
    rw [hF_trim]
    refine Finset.sum_bij (fun r _ => r idx) ?_ ?_ ?_ ?_
    · intro r hr
      have hrF := (Finset.mem_filter.mp hr).1
      have hrU := (Finset.mem_filter.mp hr).2
      have hrV := mem_validSet_iff.mp (Finset.mem_filter.mp hrF).1
      have hreq := (Finset.mem_filter.mp hrF).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨valid_pos_at hrV idx, hrU⟩,
        valid_squarefree_at hrV idx, valid_coprime_W_at hrV idx⟩, ?_⟩
      refine Nat.Coprime.prod_right fun i hi => ?_
      rw [← hreq i hi]
      exact valid_pairwise_coprime hrV (Finset.mem_erase.mp hi).1.symm
    · intro r₁ hr₁ r₂ hr₂ hEq
      have h1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hr₁).1).2
      have h2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hr₂).1).2
      funext i
      by_cases hi : i = idx
      · subst hi; exact hEq
      · rw [h1 i (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩),
          h2 i (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩)]
    · intro s hs
      have hsSU := Finset.mem_filter.mp (Finset.mem_filter.mp hs).1
      have hsc := (Finset.mem_filter.mp hs).2
      let r : Fin k → ℕ := Function.update u idx s
      have hr_er : ∀ i ∈ Finset.univ.erase idx, r i = u i := fun i hi =>
        Function.update_of_ne (Finset.mem_erase.mp hi).1 _ _
      have hr_idx : r idx = s := Function.update_self idx s u
      have hprod_r : ∏ i : Fin k, r i = s * ∏ i ∈ Finset.univ.erase idx, u i := by
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ idx), hr_idx]
        congr 1; exact Finset.prod_congr rfl hr_er
      have hrV : Valid W R r := by
        refine ⟨?_, ?_, ?_⟩
        · rw [hprod_r]; exact (Nat.squarefree_mul hsc).mpr ⟨hsSU.2.1, hcond.1⟩
        · rw [hprod_r]; exact hsSU.2.2.mul_left hcop_er_W
        · rw [hprod_r]
          calc s * ∏ i ∈ Finset.univ.erase idx, u i
              ≤ U * ∏ i ∈ Finset.univ.erase idx, u i := Nat.mul_le_mul_right _ (Finset.mem_Icc.mp hsSU.1).2
            _ = (∏ i ∈ Finset.univ.erase idx, u i) * U := mul_comm _ _
            _ ≤ R := hcond.2
      exact ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨mem_validSet_iff.mpr hrV, hr_er⟩,
        hr_idx.symm ▸ (Finset.mem_Icc.mp hsSU.1).2⟩, hr_idx⟩
    · intro r hr
      have hrF := (Finset.mem_filter.mp hr).1
      have hrU := (Finset.mem_filter.mp hr).2
      have hrV := mem_validSet_iff.mp (Finset.mem_filter.mp hrF).1
      have hreq := (Finset.mem_filter.mp hrF).2
      have hallU : ∀ i, r i ≤ U := fun i => by
        by_cases hi : i = idx
        · subst hi; exact hrU
        · rw [hreq i (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩)]
          exact (Finset.mem_Icc.mp (Finset.mem_filter.mp (huU i (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩))).1).2
      unfold yWeight
      rw [if_pos ⟨hrV, hallU⟩, ← Finset.mul_prod_erase _ _ (Finset.mem_univ idx),
        Finset.prod_congr rfl (fun i hi => by rw [hreq i hi])]
      ring
  -- Step 3: Restrict T_2 to Good and use (Z1 - B u)^2 >= Z1^2 - 2 * Z1 * B u
  have hT2_step :
      Z1 ^ 2 * (∑ u ∈ Good, ∏ i ∈ Finset.univ.erase idx, w (u i)) -
      2 * Z1 * (∑ u ∈ Good, (∏ i ∈ Finset.univ.erase idx, w (u i)) * B u) ≤
      ∑ u ∈ (validSet k W R).filter (fun u => u idx = 1),
        (YBar W R (yWeight A k D0 R U) idx u) ^ 2 /
          (∏ i ∈ Finset.univ.erase idx, (Nat.totient (u i) : ℝ)) := by
    calc Z1 ^ 2 * (∑ u ∈ Good, ∏ i ∈ Finset.univ.erase idx, w (u i)) -
          2 * Z1 * (∑ u ∈ Good, (∏ i ∈ Finset.univ.erase idx, w (u i)) * B u)
        = ∑ u ∈ Good, (∏ i ∈ Finset.univ.erase idx, w (u i)) * (Z1 ^ 2 - 2 * Z1 * B u) := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun u _ => by ring
      _ ≤ ∑ u ∈ Good, (∏ i ∈ Finset.univ.erase idx, w (u i)) * (Z1 - B u) ^ 2 := by
          refine Finset.sum_le_sum fun u _ =>
            mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (B u)])
              (Finset.prod_nonneg fun _ _ => hw_nn _)
      _ = ∑ u ∈ Good, (YBar W R (yWeight A k D0 R U) idx u) ^ 2 /
            (∏ i ∈ Finset.univ.erase idx, (Nat.totient (u i) : ℝ)) := by
          refine Finset.sum_congr rfl fun u hu => ?_
          rw [hYBar_good u hu, mul_pow, ← Finset.prod_pow, mul_div_right_comm]
          congr 1
          dsimp only [w]
          rw [Finset.prod_div_distrib]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hGood_sub
          (fun _ _ _ => div_nonneg (sq_nonneg _) (Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _))
  -- Helper: full sum over PiU of prod_{er} w(u i) equals Z2^(k-1)
  have hPiU_total : ∑ u ∈ PiU, (∏ i ∈ Finset.univ.erase idx, w (u i)) = Z2 ^ (k - 1) := by
    have heq : ∀ u ∈ PiU, (∏ i ∈ Finset.univ.erase idx, w (u i)) =
        ∏ i : Fin k, (if i = idx then (1 : ℝ) else w (u i)) := fun u _ => by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ idx), if_pos rfl, one_mul]
      exact Finset.prod_congr rfl fun i hi => by rw [if_neg (Finset.mem_erase.mp hi).1]
    rw [Finset.sum_congr rfl heq, sum_piFinset_prod domU (fun i a => if i = idx then (1 : ℝ) else w a)]
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ idx)]
    have h1 : ∑ a ∈ domU idx, (if idx = idx then (1 : ℝ) else w a) = 1 := by simp [domU]
    rw [h1, one_mul]
    calc ∏ i ∈ Finset.univ.erase idx, ∑ a ∈ domU i, (if i = idx then (1 : ℝ) else w a)
        = ∏ _i ∈ Finset.univ.erase idx, Z2 :=
          Finset.prod_congr rfl fun i hi => by simp [domU, (Finset.mem_erase.mp hi).1, Z2, w]
      _ = Z2 ^ (k - 1) := by rw [Finset.prod_const, hcard_er]
  -- Step 4: Bound sum_{u in Good} (prod w) * B u <= (k / (D0 - 2)) * Z1 * Z2^(k - 1)
  have hB_bound : ∑ u ∈ Good, (∏ i ∈ Finset.univ.erase idx, w (u i)) * B u ≤
      ((k : ℝ) / ((D0 : ℝ) - 2)) * Z1 * Z2 ^ (k - 1) := by
    let P_all : Finset ℕ := S_U.biUnion Nat.primeFactors
    have hP_gt : ∀ p ∈ P_all, D0 < p := fun p hp => by
      rcases Finset.mem_biUnion.mp hp with ⟨s, hs, hps⟩
      exact prime_gt_of_coprime_primorial (Finset.mem_filter.mp hs).2.2 hps
    have hP_prime : ∀ p ∈ P_all, p.Prime := fun p hp => by
      rcases Finset.mem_biUnion.mp hp with ⟨_, _, hps⟩
      exact Nat.prime_of_mem_primeFactors hps
    -- For each u in PiU, B u <= Z1 times sum{i in er} sum{p in (u i).primeFactors} 1 / (p - 1)
    have hBu_le : ∀ u ∈ PiU,
        B u ≤ Z1 * ∑ i ∈ Finset.univ.erase idx, ∑ p ∈ P_all,
          if p ∣ u i then 1 / ((p : ℝ) - 1) else 0 := by
      intro u hu
      have huU : ∀ i ∈ Finset.univ.erase idx, u i ∈ S_U := fun i hi => by
        have := Fintype.mem_piFinset.mp hu i; simpa [domU, (Finset.mem_erase.mp hi).1] using this
      -- Each s in SU not coprime to prod{er} u i has some p | s and p | u i for some i in er
      have hsub_s : S_U.filter (fun s => ¬ Nat.Coprime s (∏ i ∈ Finset.univ.erase idx, u i)) ⊆
          (Finset.univ.erase idx).biUnion (fun i =>
            (P_all.filter (fun p => p ∣ u i)).biUnion (fun p => S_U.filter (fun s => p ∣ s))) := by
        intro s hs
        have hsSU := (Finset.mem_filter.mp hs).1
        have hnc := (Finset.mem_filter.mp hs).2
        rw [Nat.coprime_iff_gcd_eq_one] at hnc
        obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hnc
        have hps : p ∣ s := dvd_trans hpdvd (Nat.gcd_dvd_left _ _)
        have hpu : p ∣ ∏ i ∈ Finset.univ.erase idx, u i := dvd_trans hpdvd (Nat.gcd_dvd_right _ _)
        rw [hp.prime.dvd_finsetProd_iff] at hpu
        rcases hpu with ⟨i, hi, hpui⟩
        have hs_ne0 : s ≠ 0 := by have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hsSU).1).1; omega
        have hpP : p ∈ P_all := Finset.mem_biUnion.mpr ⟨s, hsSU,
          Nat.mem_primeFactors.mpr ⟨hp, hps, hs_ne0⟩⟩
        exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_biUnion.mpr
          ⟨p, Finset.mem_filter.mpr ⟨hpP, hpui⟩, Finset.mem_filter.mpr ⟨hsSU, hps⟩⟩⟩
      calc B u ≤ ∑ i ∈ Finset.univ.erase idx, ∑ p ∈ P_all.filter (fun p => p ∣ u i),
              ∑ s ∈ S_U.filter (fun s => p ∣ s), gWeight A k R s / (Nat.totient s : ℝ) := by
            have hg_nn : ∀ s ∈ S_U, 0 ≤ gWeight A k R s / (Nat.totient s : ℝ) := fun s hs =>
              div_nonneg (gWeight_nonneg hA hR (Finset.mem_Icc.mp (Finset.mem_filter.mp hs).1).1) (Nat.cast_nonneg _)
            refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub_s fun s hs _ => ?_) ?_
            · rcases Finset.mem_biUnion.mp hs with ⟨_, _, h1⟩
              rcases Finset.mem_biUnion.mp h1 with ⟨_, _, h2⟩
              exact hg_nn s (Finset.mem_filter.mp h2).1
            · refine le_trans (finset_sum_biUnion_le fun _ _ s hs => ?_)
                (Finset.sum_le_sum fun _ _ => finset_sum_biUnion_le fun _ _ s hs =>
                  hg_nn s (Finset.mem_filter.mp hs).1)
              rcases Finset.mem_biUnion.mp hs with ⟨_, _, h2⟩
              exact hg_nn s (Finset.mem_filter.mp h2).1
        _ ≤ ∑ i ∈ Finset.univ.erase idx, ∑ p ∈ P_all.filter (fun p => p ∣ u i),
              (1 / ((p : ℝ) - 1)) * Z1 := by
            refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun p hp => ?_
            exact sum_div_prime_le_inv_pred (hP_prime p (Finset.mem_filter.mp hp).1) (gWeight A k R)
              (fun n hn => gWeight_nonneg hA hR hn) (fun m n hm hmn => gWeight_antitone hA hR hm hmn)
        _ = Z1 * ∑ i ∈ Finset.univ.erase idx, ∑ p ∈ P_all,
              if p ∣ u i then 1 / ((p : ℝ) - 1) else 0 := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.sum_filter, Finset.mul_sum]
            refine Finset.sum_congr rfl fun p _ => by split_ifs <;> ring
    -- Swap sums over u, i, p
    have hfactor_p : ∀ i ∈ Finset.univ.erase idx, ∀ p ∈ P_all,
        ∑ u ∈ PiU, (∏ j ∈ Finset.univ.erase idx, w (u j)) * (if p ∣ u i then (1 : ℝ) else 0) ≤
          (1 / ((p : ℝ) - 1)) * Z2 ^ (k - 1) := by
      intro i hi p hp
      have heq_f : ∀ u ∈ PiU,
          (∏ j ∈ Finset.univ.erase idx, w (u j)) * (if p ∣ u i then (1 : ℝ) else 0) =
          ∏ j : Fin k, (if j = idx then (1 : ℝ) else if j = i then (if p ∣ u j then w (u j) else 0) else w (u j)) := by
        intro u _
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ idx), if_pos rfl, one_mul,
          ← Finset.mul_prod_erase _ _ hi, ← Finset.mul_prod_erase (Finset.univ.erase idx) _ hi]
        have hne_i : i ≠ idx := (Finset.mem_erase.mp hi).1
        rw [if_neg hne_i, if_pos rfl]
        have hrest : ∏ j ∈ (Finset.univ.erase idx).erase i,
            (if j = idx then (1 : ℝ) else if j = i then (if p ∣ u j then w (u j) else 0) else w (u j)) =
            ∏ j ∈ (Finset.univ.erase idx).erase i, w (u j) :=
          Finset.prod_congr rfl fun j hj => by
            rw [if_neg (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1,
              if_neg (Finset.mem_erase.mp hj).1]
        rw [hrest]
        split_ifs <;> ring
      rw [Finset.sum_congr rfl heq_f, sum_piFinset_prod domU
        (fun j a => if j = idx then (1 : ℝ) else if j = i then (if p ∣ a then w a else 0) else w a)]
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ idx)]
      have h1 : ∑ a ∈ domU idx, (if idx = idx then (1 : ℝ) else
          if idx = i then (if p ∣ a then w a else 0) else w a) = 1 := by simp [domU]
      rw [h1, one_mul, ← Finset.mul_prod_erase _ _ hi]
      have hne_i : i ≠ idx := (Finset.mem_erase.mp hi).1
      have hterm_i : ∑ a ∈ domU i, (if i = idx then (1 : ℝ) else if i = i then (if p ∣ a then w a else 0) else w a) =
          ∑ a ∈ S_U.filter (fun s => p ∣ s), (gWeight A k R a) ^ 2 / (Nat.totient a : ℝ) := by
        simp [domU, hne_i, Finset.sum_filter, w]
      have hrest_Z2 : ∏ j ∈ (Finset.univ.erase idx).erase i,
          ∑ a ∈ domU j, (if j = idx then (1 : ℝ) else if j = i then (if p ∣ a then w a else 0) else w a) =
          Z2 ^ (k - 2) := by
        calc ∏ j ∈ (Finset.univ.erase idx).erase i, _
            = ∏ _j ∈ (Finset.univ.erase idx).erase i, Z2 :=
              Finset.prod_congr rfl fun j hj => by
                simp [domU, (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1,
                  (Finset.mem_erase.mp hj).1, Z2, w]
          _ = Z2 ^ (k - 2) := by
              rw [Finset.prod_const, Finset.card_erase_of_mem hi, hcard_er]; rfl
      rw [hterm_i, hrest_Z2]
      have hdp := sum_div_prime_le_inv_pred (D0 := D0) (U := U) (hP_prime p hp)
        (fun n => (gWeight A k R n) ^ 2) (fun _ _ => sq_nonneg _)
        (fun m n hm hmn => pow_le_pow_left₀ (gWeight_nonneg hA hR (le_trans hm hmn))
          (gWeight_antitone hA hR hm hmn) 2)
      calc (∑ a ∈ S_U.filter (fun s => p ∣ s), (gWeight A k R a) ^ 2 / (Nat.totient a : ℝ)) * Z2 ^ (k - 2)
          ≤ ((1 / ((p : ℝ) - 1)) * Z2) * Z2 ^ (k - 2) :=
            mul_le_mul_of_nonneg_right hdp (pow_nonneg hZ2_pos.le _)
        _ = (1 / ((p : ℝ) - 1)) * (Z2 * Z2 ^ (k - 2)) := by ring
        _ = (1 / ((p : ℝ) - 1)) * Z2 ^ (k - 1) := by
            rw [← pow_succ']
            congr 2; omega
    calc ∑ u ∈ Good, (∏ i ∈ Finset.univ.erase idx, w (u i)) * B u
        ≤ ∑ u ∈ PiU, (∏ i ∈ Finset.univ.erase idx, w (u i)) * B u :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun u _ _ => mul_nonneg (Finset.prod_nonneg fun _ _ => hw_nn _)
              (Finset.sum_nonneg fun s hs => div_nonneg
                (gWeight_nonneg hA hR (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hs).1).1).1)
                (Nat.cast_nonneg _)))
      _ ≤ ∑ u ∈ PiU, (∏ i ∈ Finset.univ.erase idx, w (u i)) *
            (Z1 * ∑ i ∈ Finset.univ.erase idx, ∑ p ∈ P_all, if p ∣ u i then 1 / ((p : ℝ) - 1) else 0) :=
          Finset.sum_le_sum fun u hu => mul_le_mul_of_nonneg_left (hBu_le u hu)
            (Finset.prod_nonneg fun _ _ => hw_nn _)
      _ = Z1 * ∑ i ∈ Finset.univ.erase idx, ∑ p ∈ P_all,
            (1 / ((p : ℝ) - 1)) *
              ∑ u ∈ PiU, (∏ j ∈ Finset.univ.erase idx, w (u j)) * (if p ∣ u i then (1 : ℝ) else 0) := by
          rw [Finset.mul_sum]
          calc ∑ u ∈ PiU, (∏ j ∈ Finset.univ.erase idx, w (u j)) *
                (Z1 * ∑ i ∈ Finset.univ.erase idx, ∑ p ∈ P_all, if p ∣ u i then 1 / ((p : ℝ) - 1) else 0)
              = ∑ u ∈ PiU, ∑ i ∈ Finset.univ.erase idx, ∑ p ∈ P_all,
                  Z1 * ((1 / ((p : ℝ) - 1)) *
                    ((∏ j ∈ Finset.univ.erase idx, w (u j)) * (if p ∣ u i then (1 : ℝ) else 0))) := by
                refine Finset.sum_congr rfl fun u _ => ?_
                rw [Finset.mul_sum, Finset.mul_sum]
                refine Finset.sum_congr rfl fun i _ => ?_
                rw [Finset.mul_sum, Finset.mul_sum]
                refine Finset.sum_congr rfl fun p _ => by split_ifs <;> ring
            _ = ∑ i ∈ Finset.univ.erase idx, ∑ u ∈ PiU, ∑ p ∈ P_all, _ := Finset.sum_comm
            _ = ∑ i ∈ Finset.univ.erase idx, ∑ p ∈ P_all, ∑ u ∈ PiU, _ :=
                Finset.sum_congr rfl fun _ _ => Finset.sum_comm
            _ = _ := by
                refine Finset.sum_congr rfl fun i _ => ?_
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl fun p _ => ?_
                rw [Finset.mul_sum, Finset.mul_sum]
      _ ≤ Z1 * ∑ _i ∈ Finset.univ.erase idx, ∑ p ∈ P_all, (1 / ((p : ℝ) - 1) ^ 2) * Z2 ^ (k - 1) := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun p hp => ?_) hZ1_pos.le
          have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hP_prime p hp).two_le
          calc (1 / ((p : ℝ) - 1)) * _ ≤ (1 / ((p : ℝ) - 1)) * ((1 / ((p : ℝ) - 1)) * Z2 ^ (k - 1)) :=
                mul_le_mul_of_nonneg_left (hfactor_p i hi p hp) (div_nonneg (by norm_num) (by linarith))
            _ = (1 / ((p : ℝ) - 1) ^ 2) * Z2 ^ (k - 1) := by
                rw [← mul_assoc, one_div_mul_one_div, ← sq]
      _ = Z1 * (((k - 1 : ℕ) : ℝ) * (∑ p ∈ P_all, (1 / ((p : ℝ) - 1) ^ 2)) * Z2 ^ (k - 1)) := by
          rw [Finset.sum_const, hcard_er, nsmul_eq_mul, ← Finset.sum_mul]; ring
      _ ≤ ((k : ℝ) / ((D0 : ℝ) - 2)) * Z1 * Z2 ^ (k - 1) := by
          have hP_sum := sum_inv_sub_sq_primes_le (D0 := D0) (c := 1) (by omega) P_all hP_gt
          simp only [Nat.cast_one] at hP_sum
          have heqD : (D0 : ℝ) - 1 - 1 = (D0 : ℝ) - 2 := by ring
          rw [heqD] at hP_sum
          have hk_le : ((k - 1 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.sub_le k 1
          have hD_pos : (0 : ℝ) < (D0 : ℝ) - 2 := by
            have : (4 : ℝ) ≤ D0 := by exact_mod_cast hD
            linarith
          have h1 : ((k - 1 : ℕ) : ℝ) * (∑ p ∈ P_all, (1 / ((p : ℝ) - 1) ^ 2)) ≤ (k : ℝ) / ((D0 : ℝ) - 2) := by
            calc ((k - 1 : ℕ) : ℝ) * (∑ p ∈ P_all, (1 / ((p : ℝ) - 1) ^ 2))
                ≤ (k : ℝ) * (1 / ((D0 : ℝ) - 2)) :=
                  mul_le_mul hk_le hP_sum (Finset.sum_nonneg fun _ _ => by positivity) (Nat.cast_nonneg _)
              _ = (k : ℝ) / ((D0 : ℝ) - 2) := by ring
          have h2 := mul_le_mul_of_nonneg_right h1 (pow_nonneg hZ2_pos.le (k - 1))
          have h3 := mul_le_mul_of_nonneg_left h2 hZ1_pos.le
          linarith
  -- Step 5: Bound PiU \ Good <= BadCoprime + BadSimplex
  let BadCop := PiU.filter (fun u => ¬ Squarefree (∏ i ∈ Finset.univ.erase idx, u i))
  let BadSimp := PiU.filter (fun u => R < (∏ i ∈ Finset.univ.erase idx, u i) * U)
  have hGood_low :
      Z2 ^ (k - 1) - (∑ u ∈ BadCop, ∏ i ∈ Finset.univ.erase idx, w (u i)) -
        (∑ u ∈ BadSimp, ∏ i ∈ Finset.univ.erase idx, w (u i)) ≤
      ∑ u ∈ Good, ∏ i ∈ Finset.univ.erase idx, w (u i) := by
    have hsplit := Finset.sum_filter_add_sum_filter_not PiU
      (fun u => Squarefree (∏ i ∈ Finset.univ.erase idx, u i) ∧ (∏ i ∈ Finset.univ.erase idx, u i) * U ≤ R)
      (fun u => ∏ i ∈ Finset.univ.erase idx, w (u i))
    have hsub : PiU.filter (fun u => ¬ (Squarefree (∏ i ∈ Finset.univ.erase idx, u i) ∧
        (∏ i ∈ Finset.univ.erase idx, u i) * U ≤ R)) ⊆ BadCop ∪ BadSimp := by
      intro u hu
      have h1 := Finset.mem_filter.mp hu
      rw [Finset.mem_union]
      by_cases hsq : Squarefree (∏ i ∈ Finset.univ.erase idx, u i)
      · exact Or.inr (Finset.mem_filter.mpr ⟨h1.1, by
          have : ¬ ((∏ i ∈ Finset.univ.erase idx, u i) * U ≤ R) := fun hle => h1.2 ⟨hsq, hle⟩
          omega⟩)
      · exact Or.inl (Finset.mem_filter.mpr ⟨h1.1, hsq⟩)
    have hbad_le :
        ∑ u ∈ PiU.filter (fun u => ¬ (Squarefree (∏ i ∈ Finset.univ.erase idx, u i) ∧
          (∏ i ∈ Finset.univ.erase idx, u i) * U ≤ R)), ∏ i ∈ Finset.univ.erase idx, w (u i) ≤
        (∑ u ∈ BadCop, ∏ i ∈ Finset.univ.erase idx, w (u i)) +
          (∑ u ∈ BadSimp, ∏ i ∈ Finset.univ.erase idx, w (u i)) :=
      le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Finset.prod_nonneg fun _ _ => hw_nn _))
        (finset_sum_union_le (fun _ _ => Finset.prod_nonneg fun _ _ => hw_nn _))
    dsimp only [Good]
    linarith
  -- Step 5a: Bound BadCop <= (k^2 / (D0 - 2)) * Z2^(k - 1)
  have hBadCop_le : ∑ u ∈ BadCop, ∏ i ∈ Finset.univ.erase idx, w (u i) ≤
      ((k : ℝ) ^ 2 / ((D0 : ℝ) - 2)) * Z2 ^ (k - 1) := by
    let P_all : Finset ℕ := S_U.biUnion Nat.primeFactors
    have hP_gt : ∀ p ∈ P_all, D0 < p := fun p hp => by
      rcases Finset.mem_biUnion.mp hp with ⟨s, hs, hps⟩
      exact prime_gt_of_coprime_primorial (Finset.mem_filter.mp hs).2.2 hps
    have hP_prime : ∀ p ∈ P_all, p.Prime := fun p hp => by
      rcases Finset.mem_biUnion.mp hp with ⟨_, _, hps⟩
      exact Nat.prime_of_mem_primeFactors hps
    let PairsEr := ((Finset.univ.erase idx) ×ˢ (Finset.univ.erase idx)).filter (fun p => p.1 ≠ p.2)
    have hsub_cop : BadCop ⊆ PairsEr.biUnion (fun ij =>
        P_all.biUnion (fun p => PiU.filter (fun u => p ∣ u ij.1 ∧ p ∣ u ij.2))) := by
      intro u hu
      have hpi := (Finset.mem_filter.mp hu).1
      have hnsq := (Finset.mem_filter.mp hu).2
      -- If every u i is squarefree (for i in er), prod_{er} u i not squarefree implies two share a prime p
      have hu_sq : ∀ i ∈ Finset.univ.erase idx, Squarefree (u i) := fun i hi => by
        have := Fintype.mem_piFinset.mp hpi i; simp only [domU, if_neg (Finset.mem_erase.mp hi).1] at this
        exact (Finset.mem_filter.mp this).2.1
      have hex_pair : ∃ i ∈ Finset.univ.erase idx, ∃ j ∈ Finset.univ.erase idx, i ≠ j ∧ ¬ Nat.Coprime (u i) (u j) := by
        by_contra hall
        push Not at hall
        apply hnsq
        have hsq_s : ∀ s : Finset (Fin k), s ⊆ Finset.univ.erase idx → Squarefree (∏ i ∈ s, u i) := by
          intro s hs
          induction s using Finset.induction_on with
          | empty => simp
          | insert a s ha ih =>
            rw [Finset.prod_insert ha]
            have ha_er : a ∈ Finset.univ.erase idx := hs (Finset.mem_insert_self a s)
            have hca : Nat.Coprime (u a) (∏ i ∈ s, u i) :=
              Nat.Coprime.prod_right fun j hj =>
                hall a ha_er j (hs (Finset.mem_insert_of_mem hj)) (fun heq => ha (heq ▸ hj))
            exact (Nat.squarefree_mul hca).mpr ⟨hu_sq a ha_er, ih (Subset.trans (Finset.subset_insert a s) hs)⟩
        exact hsq_s (Finset.univ.erase idx) Subset.rfl
      rcases hex_pair with ⟨i, hi, j, hj, hij, hnc⟩
      rw [Nat.coprime_iff_gcd_eq_one] at hnc
      obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hnc
      have hpi_d : p ∣ u i := dvd_trans hpdvd (Nat.gcd_dvd_left _ _)
      have hpj_d : p ∣ u j := dvd_trans hpdvd (Nat.gcd_dvd_right _ _)
      have hui_SU : u i ∈ S_U := by
        have := Fintype.mem_piFinset.mp hpi i; simpa [domU, (Finset.mem_erase.mp hi).1] using this
      have hui_ne0 : u i ≠ 0 := by have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hui_SU).1).1; omega
      have hpP : p ∈ P_all := Finset.mem_biUnion.mpr ⟨u i, hui_SU,
        Nat.mem_primeFactors.mpr ⟨hp, hpi_d, hui_ne0⟩⟩
      exact Finset.mem_biUnion.mpr ⟨(i, j), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hi, hj⟩, hij⟩,
        Finset.mem_biUnion.mpr ⟨p, hpP, Finset.mem_filter.mpr ⟨hpi, hpi_d, hpj_d⟩⟩⟩
    have hpair_p : ∀ ij ∈ PairsEr, ∀ p ∈ P_all,
        ∑ u ∈ PiU.filter (fun u => p ∣ u ij.1 ∧ p ∣ u ij.2), ∏ l ∈ Finset.univ.erase idx, w (u l) ≤
          (1 / ((p : ℝ) - 1) ^ 2) * Z2 ^ (k - 1) := by
      intro ⟨i, j⟩ hij p hp
      have hmem := Finset.mem_filter.mp hij
      have hi : i ∈ Finset.univ.erase idx := (Finset.mem_product.mp hmem.1).1
      have hj : j ∈ Finset.univ.erase idx := (Finset.mem_product.mp hmem.1).2
      have hne_ij : i ≠ j := hmem.2
      have hne_i : i ≠ idx := (Finset.mem_erase.mp hi).1
      have hne_j : j ≠ idx := (Finset.mem_erase.mp hj).1
      let domP : Fin k → Finset ℕ := fun l =>
        if l = idx then {1} else if l = i ∨ l = j then S_U.filter (fun s => p ∣ s) else S_U
      have hset_eq : PiU.filter (fun u => p ∣ u i ∧ p ∣ u j) = Fintype.piFinset domP := by
        ext u
        simp only [Finset.mem_filter, PiU, Fintype.mem_piFinset, domP, domU]
        constructor
        · rintro ⟨hu, hpi_d, hpj_d⟩ l
          by_cases hl : l = idx
          · rw [hl, if_pos rfl]; simpa using hu idx
          · rw [if_neg hl]
            by_cases hlj : l = i ∨ l = j
            · rw [if_pos hlj, Finset.mem_filter]
              refine ⟨by simpa [hl] using hu l, ?_⟩
              rcases hlj with rfl | rfl <;> assumption
            · rw [if_neg hlj]; simpa [hl] using hu l
        · intro hu
          refine ⟨fun l => ?_, ?_, ?_⟩
          · have := hu l
            by_cases hl : l = idx
            · rw [hl, if_pos rfl] at this ⊢; exact this
            · rw [if_neg hl] at this ⊢
              split_ifs at this
              · exact (Finset.mem_filter.mp this).1
              · exact this
          · have := hu i
            simp only [if_neg hne_i, true_or, ite_true, Finset.mem_filter] at this
            exact this.2
          · have := hu j
            simp only [if_neg hne_j, or_true, ite_true, Finset.mem_filter] at this
            exact this.2
      rw [hset_eq]
      have heq_f : ∀ u ∈ Fintype.piFinset domP,
          (∏ l ∈ Finset.univ.erase idx, w (u l)) = ∏ l : Fin k, (if l = idx then (1 : ℝ) else w (u l)) :=
        fun u _ => by
          rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ idx), if_pos rfl, one_mul]
          exact Finset.prod_congr rfl fun l hl => by rw [if_neg (Finset.mem_erase.mp hl).1]
      rw [Finset.sum_congr rfl heq_f, sum_piFinset_prod domP (fun l a => if l = idx then (1 : ℝ) else w a)]
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ idx)]
      have h1 : ∑ a ∈ domP idx, (if idx = idx then (1 : ℝ) else w a) = 1 := by simp [domP]
      rw [h1, one_mul, ← Finset.mul_prod_erase _ _ hi]
      have hj_er : j ∈ (Finset.univ.erase idx).erase i := Finset.mem_erase.mpr ⟨hne_ij.symm, hj⟩
      rw [← Finset.mul_prod_erase _ _ hj_er]
      have hi_val : ∑ a ∈ domP i, (if i = idx then (1 : ℝ) else w a) = ∑ s ∈ S_U.filter (fun s => p ∣ s), w s := by
        simp [domP, hne_i]
      have hj_val : ∑ a ∈ domP j, (if j = idx then (1 : ℝ) else w a) = ∑ s ∈ S_U.filter (fun s => p ∣ s), w s := by
        simp [domP, hne_j]
      have hrest_val : ∏ l ∈ ((Finset.univ.erase idx).erase i).erase j,
          ∑ a ∈ domP l, (if l = idx then (1 : ℝ) else w a) = Z2 ^ (k - 3) := by
        calc ∏ l ∈ ((Finset.univ.erase idx).erase i).erase j, _
            = ∏ _l ∈ ((Finset.univ.erase idx).erase i).erase j, Z2 :=
              Finset.prod_congr rfl fun l hl => by
                have hlj := (Finset.mem_erase.mp hl).1
                have hli := (Finset.mem_erase.mp (Finset.mem_erase.mp hl).2).1
                have hlidx := (Finset.mem_erase.mp (Finset.mem_erase.mp (Finset.mem_erase.mp hl).2).2).1
                simp [domP, hlidx, hli, hlj, Z2, w]
          _ = Z2 ^ (k - 3) := by
              rw [Finset.prod_const, Finset.card_erase_of_mem hj_er, Finset.card_erase_of_mem hi, hcard_er]; rfl
      have hk3 : 3 ≤ k := by
        have hcard3 : 2 ≤ (Finset.univ.erase idx).card := by
          have : ({i, j} : Finset (Fin k)) ⊆ Finset.univ.erase idx := by
            intro x hx; rcases Finset.mem_insert.mp hx with rfl | hx'
            · exact hi
            · rw [Finset.mem_singleton.mp hx']; exact hj
          have := Finset.card_le_card this
          rw [Finset.card_pair hne_ij] at this
          exact this
        omega
      rw [hi_val, hj_val, hrest_val]
      have hdp : ∑ s ∈ S_U.filter (fun s => p ∣ s), w s ≤ (1 / ((p : ℝ) - 1)) * Z2 :=
        sum_div_prime_le_inv_pred (D0 := D0) (U := U) (hP_prime p hp)
          (fun n => (gWeight A k R n) ^ 2) (fun _ _ => sq_nonneg _)
          (fun m n hm hmn => pow_le_pow_left₀ (gWeight_nonneg hA hR (le_trans hm hmn))
            (gWeight_antitone hA hR hm hmn) 2)
      have hdp_nn : 0 ≤ ∑ s ∈ S_U.filter (fun s => p ∣ s), w s := Finset.sum_nonneg fun _ _ => hw_nn _
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hP_prime p hp).two_le
      calc (∑ s ∈ S_U.filter (fun s => p ∣ s), w s) * ((∑ s ∈ S_U.filter (fun s => p ∣ s), w s) * Z2 ^ (k - 3))
          ≤ ((1 / ((p : ℝ) - 1)) * Z2) * (((1 / ((p : ℝ) - 1)) * Z2) * Z2 ^ (k - 3)) :=
            mul_le_mul hdp (mul_le_mul_of_nonneg_right hdp (pow_nonneg hZ2_pos.le _))
              (mul_nonneg hdp_nn (pow_nonneg hZ2_pos.le _)) (mul_nonneg (div_nonneg (by norm_num) (by linarith)) hZ2_pos.le)
        _ = (1 / ((p : ℝ) - 1) ^ 2) * (Z2 * (Z2 * Z2 ^ (k - 3))) := by
            have hmul_eq : ((1 / ((p : ℝ) - 1)) * Z2) * (((1 / ((p : ℝ) - 1)) * Z2) * Z2 ^ (k - 3)) =
                ((1 / ((p : ℝ) - 1)) * (1 / ((p : ℝ) - 1))) * (Z2 * (Z2 * Z2 ^ (k - 3))) := by ring
            rw [hmul_eq, one_div_mul_one_div, ← sq]
        _ = (1 / ((p : ℝ) - 1) ^ 2) * Z2 ^ (k - 1) := by
            rw [← pow_succ', ← pow_succ']
            congr 2; omega
    calc ∑ u ∈ BadCop, ∏ i ∈ Finset.univ.erase idx, w (u i)
        ≤ ∑ ij ∈ PairsEr, ∑ p ∈ P_all,
            ∑ u ∈ PiU.filter (fun u => p ∣ u ij.1 ∧ p ∣ u ij.2), ∏ l ∈ Finset.univ.erase idx, w (u l) :=
          le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub_cop (fun _ _ _ => Finset.prod_nonneg fun _ _ => hw_nn _))
            (le_trans (finset_sum_biUnion_le fun _ _ _ _ => Finset.prod_nonneg fun _ _ => hw_nn _)
              (Finset.sum_le_sum fun _ _ => finset_sum_biUnion_le fun _ _ _ _ => Finset.prod_nonneg fun _ _ => hw_nn _))
      _ ≤ ∑ _ij ∈ PairsEr, ∑ p ∈ P_all, (1 / ((p : ℝ) - 1) ^ 2) * Z2 ^ (k - 1) :=
          Finset.sum_le_sum fun ij hij => Finset.sum_le_sum fun p hp => hpair_p ij hij p hp
      _ = (PairsEr.card : ℝ) * (∑ p ∈ P_all, (1 / ((p : ℝ) - 1) ^ 2)) * Z2 ^ (k - 1) := by
          rw [Finset.sum_const, nsmul_eq_mul, ← Finset.sum_mul]; ring
      _ ≤ ((k : ℝ) ^ 2 / ((D0 : ℝ) - 2)) * Z2 ^ (k - 1) := by
          have hcard_le : (PairsEr.card : ℝ) ≤ (k : ℝ) ^ 2 := by
            have h1 : PairsEr.card ≤ k * k := by
              calc PairsEr.card ≤ ((Finset.univ.erase idx) ×ˢ (Finset.univ.erase idx)).card := Finset.card_filter_le _ _
                _ = (k - 1) * (k - 1) := by rw [Finset.card_product, hcard_er]
                _ ≤ k * k := Nat.mul_le_mul (Nat.sub_le k 1) (Nat.sub_le k 1)
            have : (PairsEr.card : ℝ) ≤ ((k * k : ℕ) : ℝ) := Nat.cast_le.mpr h1
            push_cast at this; linarith [sq (k : ℝ)]
          have hP_sum := sum_inv_sub_sq_primes_le (D0 := D0) (c := 1) (by omega) P_all hP_gt
          simp only [Nat.cast_one] at hP_sum
          have heqD : (D0 : ℝ) - 1 - 1 = (D0 : ℝ) - 2 := by ring
          rw [heqD] at hP_sum
          have h1 : (PairsEr.card : ℝ) * (∑ p ∈ P_all, (1 / ((p : ℝ) - 1) ^ 2)) ≤ (k : ℝ) ^ 2 / ((D0 : ℝ) - 2) := by
            calc (PairsEr.card : ℝ) * (∑ p ∈ P_all, (1 / ((p : ℝ) - 1) ^ 2))
                ≤ (k : ℝ) ^ 2 * (1 / ((D0 : ℝ) - 2)) :=
                  mul_le_mul hcard_le hP_sum (Finset.sum_nonneg fun _ _ => by positivity) (sq_nonneg _)
              _ = (k : ℝ) ^ 2 / ((D0 : ℝ) - 2) := by ring
          exact mul_le_mul_of_nonneg_right h1 (pow_nonneg hZ2_pos.le _)
  -- Step 5b: Discrete Chebyshev bound on BadSimp
  have hBadSimp_le : ∑ u ∈ BadSimp, ∏ i ∈ Finset.univ.erase idx, w (u i) ≤
      ((k - 1 : ℕ) : ℝ) * Z2 ^ (k - 2) * (M_U / A ^ 2) / delta ^ 2 := by
    let X : (Fin k → ℕ) → ℝ := fun u => ∑ i ∈ Finset.univ.erase idx, (tVal k R (u i) - mu)
    -- Every u in BadSimp satisfies delta < X u, hence delta^2 <= (X u)^2
    have hX_gt : ∀ u ∈ BadSimp, delta ^ 2 ≤ (X u) ^ 2 := by
      intro u hu
      have hpi := Fintype.mem_piFinset.mp (Finset.mem_filter.mp hu).1
      have hgt : R < (∏ i ∈ Finset.univ.erase idx, u i) * U := (Finset.mem_filter.mp hu).2
      have hR_lt : (R : ℝ) < ((∏ i ∈ Finset.univ.erase idx, u i : ℕ) : ℝ) * (U : ℝ) := by
        exact_mod_cast hgt
      have hprod_pos : ∀ i ∈ Finset.univ.erase idx, (0 : ℝ) < (u i : ℝ) := fun i hi => by
        have := Fintype.mem_piFinset.mp (Finset.mem_filter.mp hu).1 i
        simp only [domU, if_neg (Finset.mem_erase.mp hi).1] at this
        exact Nat.cast_pos.mpr (Finset.mem_Icc.mp (Finset.mem_filter.mp this).1).1
      have hlog_lt : Real.log (R : ℝ) <
          (∑ i ∈ Finset.univ.erase idx, Real.log (u i : ℝ)) + Real.log (U : ℝ) := by
        have h1 := Real.log_lt_log (by exact_mod_cast (by omega : 0 < R)) hR_lt
        have hprod_ne : ((∏ i ∈ Finset.univ.erase idx, u i : ℕ) : ℝ) ≠ 0 := by
          rw [Nat.cast_prod]
          exact Finset.prod_ne_zero_iff.mpr fun i hi => (hprod_pos i hi).ne'
        have hU_ne : (U : ℝ) ≠ 0 := (Nat.cast_pos.mpr (by omega : 0 < U)).ne'
        rw [Real.log_mul hprod_ne hU_ne,
          Nat.cast_prod, Real.log_prod (fun i hi => (hprod_pos i hi).ne')] at h1
        exact h1
      have hlogU_le : Real.log (U : ℝ) ≤ (T / (k : ℝ)) * Real.log (R : ℝ) := by
        have h1 := Real.log_le_log (by exact_mod_cast (by omega : 0 < U)) hU_pow
        rwa [Real.log_rpow (by exact_mod_cast (by omega : 0 < R))] at h1
      have hsum_t : (k : ℝ) - T < ∑ i ∈ Finset.univ.erase idx, tVal k R (u i) := by
        have hk_pos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
        have h1 : (1 - T / (k : ℝ)) * Real.log (R : ℝ) < ∑ i ∈ Finset.univ.erase idx, Real.log (u i : ℝ) := by
          linarith
        have h2 : (k : ℝ) * ((1 - T / (k : ℝ)) * Real.log (R : ℝ)) / Real.log (R : ℝ) <
            (k : ℝ) * (∑ i ∈ Finset.univ.erase idx, Real.log (u i : ℝ)) / Real.log (R : ℝ) :=
          div_lt_div_of_pos_right (mul_lt_mul_of_pos_left h1 hk_pos) hlogR_pos
        have hlhs : (k : ℝ) * ((1 - T / (k : ℝ)) * Real.log (R : ℝ)) / Real.log (R : ℝ) = (k : ℝ) - T := by
          field_simp
        have hrhs : (k : ℝ) * (∑ i ∈ Finset.univ.erase idx, Real.log (u i : ℝ)) / Real.log (R : ℝ) =
            ∑ i ∈ Finset.univ.erase idx, tVal k R (u i) := by
          rw [Finset.mul_sum, Finset.sum_div]; rfl
        linarith
      have hXu : X u = (∑ i ∈ Finset.univ.erase idx, tVal k R (u i)) - ((k - 1 : ℕ) : ℝ) * mu := by
        dsimp only [X]
        rw [Finset.sum_sub_distrib, Finset.sum_const, hcard_er, nsmul_eq_mul]
      have hlt : delta < X u := by dsimp only [delta]; linarith
      exact pow_le_pow_left₀ hdelta.le hlt.le 2
    -- Mean zero identity: sum{s in SU} w s times (tVal s - mu) = 0
    have hmean_zero : ∑ s ∈ S_U, w s * (tVal k R s - mu) = 0 := by
      have h1 : ∑ s ∈ S_U, w s * tVal k R s = (1 / A) * (Z1 - Z2) := by
        calc ∑ s ∈ S_U, w s * tVal k R s
            = ∑ s ∈ S_U, (1 / A) * (gWeight A k R s / (Nat.totient s : ℝ) -
                (gWeight A k R s) ^ 2 / (Nat.totient s : ℝ)) := by
              refine Finset.sum_congr rfl fun s hs => ?_
              have htid := tVal_mul_gWeight_sq (k := k) hA hR (Finset.mem_Icc.mp (Finset.mem_filter.mp hs).1).1
              dsimp only [w]
              have : (gWeight A k R s) ^ 2 / (Nat.totient s : ℝ) * tVal k R s =
                  (tVal k R s * (gWeight A k R s) ^ 2) / (Nat.totient s : ℝ) := by ring
              rw [this, htid]; ring
          _ = (1 / A) * (Z1 - Z2) := by rw [← Finset.mul_sum, Finset.sum_sub_distrib]
      calc ∑ s ∈ S_U, w s * (tVal k R s - mu)
          = (∑ s ∈ S_U, w s * tVal k R s) - mu * (∑ s ∈ S_U, w s) := by
            simp_rw [mul_sub]; rw [Finset.sum_sub_distrib, ← Finset.sum_mul, mul_comm]
        _ = (1 / A) * (Z1 - Z2) - ((Z1 - Z2) / (A * Z2)) * Z2 := by rw [h1]
        _ = 0 := by have hAne := hA.ne'; have hZ2ne := hZ2_pos.ne'; field_simp; ring
    -- Second moment bound: sum{s in SU} w s times (tVal s - mu)^2 <= MU / A^2
    have hvar_le : ∑ s ∈ S_U, w s * (tVal k R s - mu) ^ 2 ≤ M_U / A ^ 2 := by
      have h1 : ∑ s ∈ S_U, w s * (tVal k R s - mu) ^ 2 =
          (∑ s ∈ S_U, w s * (tVal k R s) ^ 2) - mu ^ 2 * Z2 := by
        have hstep : ∀ s ∈ S_U, w s * (tVal k R s - mu) ^ 2 =
            w s * (tVal k R s) ^ 2 - 2 * mu * (w s * (tVal k R s - mu)) - mu ^ 2 * w s :=
          fun s _ => by ring
        rw [Finset.sum_congr rfl hstep, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum, hmean_zero, mul_zero, sub_zero]
      have h2 : ∑ s ∈ S_U, w s * (tVal k R s) ^ 2 ≤ M_U / A ^ 2 := by
        calc ∑ s ∈ S_U, w s * (tVal k R s) ^ 2
            ≤ ∑ s ∈ S_U, (1 / A ^ 2) * (1 / (Nat.totient s : ℝ)) := by
              refine Finset.sum_le_sum fun s hs => ?_
              have hts := tVal_sq_mul_gWeight_sq_le (k := k) hA hR (Finset.mem_Icc.mp (Finset.mem_filter.mp hs).1).1
              dsimp only [w]
              have : (gWeight A k R s) ^ 2 / (Nat.totient s : ℝ) * (tVal k R s) ^ 2 =
                  ((tVal k R s) ^ 2 * (gWeight A k R s) ^ 2) * (1 / (Nat.totient s : ℝ)) := by ring
              rw [this]
              exact mul_le_mul_of_nonneg_right hts (by positivity)
          _ = M_U / A ^ 2 := by rw [← Finset.mul_sum]; dsimp only [M_U]; ring
      have hmu2_nn : 0 ≤ mu ^ 2 * Z2 := mul_nonneg (sq_nonneg _) hZ2_pos.le
      linarith
    -- Expand sum{PiU} (prod w) times (X u)^2 = (k - 1) times Z2^(k - 2) times sum{SU} w s times (t s - mu)^2
    have hvar_expand :
        ∑ u ∈ PiU, (∏ i ∈ Finset.univ.erase idx, w (u i)) * (X u) ^ 2 =
        ((k - 1 : ℕ) : ℝ) * Z2 ^ (k - 2) * ∑ s ∈ S_U, w s * (tVal k R s - mu) ^ 2 := by
      have hsq : ∀ u ∈ PiU, (X u) ^ 2 =
          ∑ i ∈ Finset.univ.erase idx, ∑ j ∈ Finset.univ.erase idx,
            (tVal k R (u i) - mu) * (tVal k R (u j) - mu) := fun u _ => by
        dsimp only [X]; rw [sq, Finset.sum_mul]; simp_rw [Finset.mul_sum]
      calc ∑ u ∈ PiU, (∏ l ∈ Finset.univ.erase idx, w (u l)) * (X u) ^ 2
          = ∑ u ∈ PiU, ∑ i ∈ Finset.univ.erase idx, ∑ j ∈ Finset.univ.erase idx,
              (∏ l ∈ Finset.univ.erase idx, w (u l)) * ((tVal k R (u i) - mu) * (tVal k R (u j) - mu)) := by
            refine Finset.sum_congr rfl fun u hu => ?_
            rw [hsq u hu, Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => Finset.mul_sum ..
        _ = ∑ i ∈ Finset.univ.erase idx, ∑ j ∈ Finset.univ.erase idx,
              ∑ u ∈ PiU, (∏ l ∈ Finset.univ.erase idx, w (u l)) *
                ((tVal k R (u i) - mu) * (tVal k R (u j) - mu)) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun _ _ => Finset.sum_comm
        _ = ∑ i ∈ Finset.univ.erase idx,
              ∑ u ∈ PiU, (∏ l ∈ Finset.univ.erase idx, w (u l)) * (tVal k R (u i) - mu) ^ 2 := by
            refine Finset.sum_congr rfl fun i hi => ?_
            rw [Finset.sum_eq_single i]
            · refine Finset.sum_congr rfl fun u _ => by ring
            · intro j hj hji
              -- Cross term vanishes because mean is 0!
              have hne_i : i ≠ idx := (Finset.mem_erase.mp hi).1
              have hne_j : j ≠ idx := (Finset.mem_erase.mp hj).1
              have heq_f : ∀ u ∈ PiU,
                  (∏ l ∈ Finset.univ.erase idx, w (u l)) * ((tVal k R (u i) - mu) * (tVal k R (u j) - mu)) =
                  ∏ l : Fin k, (if l = idx then (1 : ℝ) else
                    if l = i then w (u l) * (tVal k R (u l) - mu) else
                    if l = j then w (u l) * (tVal k R (u l) - mu) else w (u l)) := by
                intro u _
                rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ idx), if_pos rfl, one_mul,
                  ← Finset.mul_prod_erase _ _ hi, ← Finset.mul_prod_erase (Finset.univ.erase idx) _ hi]
                have hj_er : j ∈ (Finset.univ.erase idx).erase i := Finset.mem_erase.mpr ⟨hji, hj⟩
                rw [← Finset.mul_prod_erase _ _ hj_er, ← Finset.mul_prod_erase ((Finset.univ.erase idx).erase i) _ hj_er]
                rw [if_neg hne_i, if_pos rfl, if_neg hne_j, if_neg hji, if_pos rfl]
                have hrest : ∏ l ∈ ((Finset.univ.erase idx).erase i).erase j,
                    (if l = idx then (1 : ℝ) else
                      if l = i then w (u l) * (tVal k R (u l) - mu) else
                      if l = j then w (u l) * (tVal k R (u l) - mu) else w (u l)) =
                    ∏ l ∈ ((Finset.univ.erase idx).erase i).erase j, w (u l) :=
                  Finset.prod_congr rfl fun l hl => by
                    rw [if_neg (Finset.mem_erase.mp (Finset.mem_erase.mp (Finset.mem_erase.mp hl).2).2).1,
                      if_neg (Finset.mem_erase.mp (Finset.mem_erase.mp hl).2).1,
                      if_neg (Finset.mem_erase.mp hl).1]
                rw [hrest]; ring
              rw [Finset.sum_congr rfl heq_f, sum_piFinset_prod domU
                (fun l a => if l = idx then (1 : ℝ) else
                  if l = i then w a * (tVal k R a - mu) else
                  if l = j then w a * (tVal k R a - mu) else w a)]
              refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
              simp [domU, hne_i, hmean_zero]
            · intro hnot; exact absurd hi hnot
        _ = ∑ _i ∈ Finset.univ.erase idx, Z2 ^ (k - 2) * ∑ s ∈ S_U, w s * (tVal k R s - mu) ^ 2 := by
            refine Finset.sum_congr rfl fun i hi => ?_
            have hne_i : i ≠ idx := (Finset.mem_erase.mp hi).1
            have heq_f : ∀ u ∈ PiU,
                (∏ l ∈ Finset.univ.erase idx, w (u l)) * (tVal k R (u i) - mu) ^ 2 =
                ∏ l : Fin k, (if l = idx then (1 : ℝ) else
                  if l = i then w (u l) * (tVal k R (u l) - mu) ^ 2 else w (u l)) := by
              intro u _
              rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ idx), if_pos rfl, one_mul,
                ← Finset.mul_prod_erase _ _ hi, ← Finset.mul_prod_erase (Finset.univ.erase idx) _ hi]
              rw [if_neg hne_i, if_pos rfl]
              have hrest : ∏ l ∈ (Finset.univ.erase idx).erase i,
                  (if l = idx then (1 : ℝ) else
                    if l = i then w (u l) * (tVal k R (u l) - mu) ^ 2 else w (u l)) =
                  ∏ l ∈ (Finset.univ.erase idx).erase i, w (u l) :=
                Finset.prod_congr rfl fun l hl => by
                  rw [if_neg (Finset.mem_erase.mp (Finset.mem_erase.mp hl).2).1,
                    if_neg (Finset.mem_erase.mp hl).1]
              rw [hrest]; ring
            rw [Finset.sum_congr rfl heq_f, sum_piFinset_prod domU
              (fun l a => if l = idx then (1 : ℝ) else
                if l = i then w a * (tVal k R a - mu) ^ 2 else w a)]
            rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ idx)]
            have h1 : ∑ a ∈ domU idx, (if idx = idx then (1 : ℝ) else
                if idx = i then w a * (tVal k R a - mu) ^ 2 else w a) = 1 := by simp [domU]
            rw [h1, one_mul, ← Finset.mul_prod_erase _ _ hi]
            have hi_val : ∑ a ∈ domU i, (if i = idx then (1 : ℝ) else
                if i = i then w a * (tVal k R a - mu) ^ 2 else w a) =
                ∑ s ∈ S_U, w s * (tVal k R s - mu) ^ 2 := by simp [domU, hne_i]
            have hrest_Z2 : ∏ l ∈ (Finset.univ.erase idx).erase i,
                ∑ a ∈ domU l, (if l = idx then (1 : ℝ) else
                  if l = i then w a * (tVal k R a - mu) ^ 2 else w a) = Z2 ^ (k - 2) := by
              calc ∏ l ∈ (Finset.univ.erase idx).erase i, _
                  = ∏ _l ∈ (Finset.univ.erase idx).erase i, Z2 :=
                    Finset.prod_congr rfl fun l hl => by
                      simp [domU, (Finset.mem_erase.mp (Finset.mem_erase.mp hl).2).1,
                        (Finset.mem_erase.mp hl).1, Z2, w]
                _ = Z2 ^ (k - 2) := by
                    rw [Finset.prod_const, Finset.card_erase_of_mem hi, hcard_er]; rfl
            rw [hi_val, hrest_Z2, mul_comm]
        _ = ((k - 1 : ℕ) : ℝ) * Z2 ^ (k - 2) * ∑ s ∈ S_U, w s * (tVal k R s - mu) ^ 2 := by
            rw [Finset.sum_const, hcard_er, nsmul_eq_mul]; ring
    rw [le_div_iff₀ (sq_pos_of_pos hdelta)]
    calc (∑ u ∈ BadSimp, ∏ i ∈ Finset.univ.erase idx, w (u i)) * delta ^ 2
        = ∑ u ∈ BadSimp, (∏ i ∈ Finset.univ.erase idx, w (u i)) * delta ^ 2 := Finset.sum_mul ..
      _ ≤ ∑ u ∈ BadSimp, (∏ i ∈ Finset.univ.erase idx, w (u i)) * (X u) ^ 2 :=
          Finset.sum_le_sum fun u hu => mul_le_mul_of_nonneg_left (hX_gt u hu)
            (Finset.prod_nonneg fun _ _ => hw_nn _)
      _ ≤ ∑ u ∈ PiU, (∏ i ∈ Finset.univ.erase idx, w (u i)) * (X u) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ => mul_nonneg (Finset.prod_nonneg fun _ _ => hw_nn _) (sq_nonneg _))
      _ = ((k - 1 : ℕ) : ℝ) * Z2 ^ (k - 2) * ∑ s ∈ S_U, w s * (tVal k R s - mu) ^ 2 := hvar_expand
      _ ≤ ((k - 1 : ℕ) : ℝ) * Z2 ^ (k - 2) * (M_U / A ^ 2) :=
          mul_le_mul_of_nonneg_left hvar_le (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hZ2_pos.le _))
  -- Step 6: Combine all bounds
  have hZ2_pow : Z2 ^ (k - 1) = Z2 * Z2 ^ (k - 2) := by
    rw [← pow_succ']; congr 1; omega
  have hsimp_rewrite :
      Z1 ^ 2 * (((k - 1 : ℕ) : ℝ) * Z2 ^ (k - 2) * (M_U / A ^ 2) / delta ^ 2) =
      Z1 ^ 2 * Z2 ^ (k - 1) * (((k - 1 : ℕ) : ℝ) * (M_U / (A ^ 2 * Z2)) / delta ^ 2) := by
    rw [hZ2_pow]
    have hZ2ne : Z2 ≠ 0 := hZ2_pos.ne'
    have hAne : A ≠ 0 := hA.ne'
    have hdne : delta ≠ 0 := hdelta.ne'
    field_simp
  have hk_le_k2 : (k : ℝ) ≤ (k : ℝ) ^ 2 := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith
  have hD_pos : (0 : ℝ) < (D0 : ℝ) - 2 := by
    have : (4 : ℝ) ≤ D0 := by exact_mod_cast hD
    linarith
  have h2k_le : 2 * ((k : ℝ) / ((D0 : ℝ) - 2)) + (k : ℝ) ^ 2 / ((D0 : ℝ) - 2) ≤
      3 * (k : ℝ) ^ 2 / ((D0 : ℝ) - 2) := by
    have h1 : 2 * ((k : ℝ) / ((D0 : ℝ) - 2)) ≤ 2 * (k : ℝ) ^ 2 / ((D0 : ℝ) - 2) := by
      have heq : 2 * ((k : ℝ) / ((D0 : ℝ) - 2)) = (2 * (k : ℝ)) / ((D0 : ℝ) - 2) := by ring
      rw [heq]
      exact div_le_div_of_nonneg_right (by linarith) hD_pos.le
    have h2 : 2 * (k : ℝ) ^ 2 / ((D0 : ℝ) - 2) + (k : ℝ) ^ 2 / ((D0 : ℝ) - 2) =
        3 * (k : ℝ) ^ 2 / ((D0 : ℝ) - 2) := by ring
    linarith
  have hfinal_comb :
      Z1 ^ 2 * Z2 ^ (k - 1) *
        (1 - ((k - 1 : ℕ) : ℝ) * (M_U / (A ^ 2 * Z2)) / delta ^ 2 -
          (3 * (k : ℝ) ^ 2 / ((D0 : ℝ) - 2))) ≤
      Z1 ^ 2 * (∑ u ∈ Good, ∏ i ∈ Finset.univ.erase idx, w (u i)) -
        2 * Z1 * (∑ u ∈ Good, (∏ i ∈ Finset.univ.erase idx, w (u i)) * B u) := by
    have h1 : Z1 ^ 2 * (Z2 ^ (k - 1) - ((k : ℝ) ^ 2 / ((D0 : ℝ) - 2)) * Z2 ^ (k - 1) -
          ((k - 1 : ℕ) : ℝ) * Z2 ^ (k - 2) * (M_U / A ^ 2) / delta ^ 2) ≤
        Z1 ^ 2 * (∑ u ∈ Good, ∏ i ∈ Finset.univ.erase idx, w (u i)) :=
      mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
    have h2 : 2 * Z1 * (∑ u ∈ Good, (∏ i ∈ Finset.univ.erase idx, w (u i)) * B u) ≤
        2 * ((k : ℝ) / ((D0 : ℝ) - 2)) * Z1 ^ 2 * Z2 ^ (k - 1) := by
      have := mul_le_mul_of_nonneg_left hB_bound (by linarith : (0 : ℝ) ≤ 2 * Z1)
      linarith
    have h3 : (2 * ((k : ℝ) / ((D0 : ℝ) - 2)) + (k : ℝ) ^ 2 / ((D0 : ℝ) - 2)) * (Z1 ^ 2 * Z2 ^ (k - 1)) ≤
        (3 * (k : ℝ) ^ 2 / ((D0 : ℝ) - 2)) * (Z1 ^ 2 * Z2 ^ (k - 1)) :=
      mul_le_mul_of_nonneg_right h2k_le (mul_nonneg (sq_nonneg _) (pow_nonneg hZ2_pos.le _))
    linarith
  exact le_trans hfinal_comb hT2_step

/-- 1D Riemann block approximation for antitone f on [0, T] via 1D Mertens. -/
lemma riemann_block_approx {D0 k R U L : ℕ} {T C_W : ℝ}
    (hT : 0 < T) (hk : 1 ≤ k) (hR : 2 ≤ R) (hL : 1 ≤ L) (hC : 0 ≤ C_W)
    (hU : U = ⌊(R : ℝ) ^ (T / (k : ℝ))⌋₊)
    (hMertens : ∀ Y : ℝ, 1 ≤ Y →
      |(∑ r ∈ (Finset.Icc 1 ⌊Y⌋₊).filter (fun r => Squarefree r ∧ Nat.Coprime r (primorial D0)),
          (1 / (Nat.totient r : ℝ))) -
        ((Nat.totient (primorial D0) : ℝ) / (primorial D0 : ℝ)) * Real.log Y| ≤ C_W)
    (f : ℝ → ℝ) (hf0 : ∀ t, 0 ≤ t → 0 ≤ f t) (hf1 : ∀ t, 0 ≤ t → f t ≤ 1)
    (hf_anti : ∀ s t, 0 ≤ s → s ≤ t → f t ≤ f s) :
    let W := primorial D0
    let cW := (Nat.totient W : ℝ) / (W : ℝ)
    let S_U := (Finset.Icc 1 U).filter (fun s => Squarefree s ∧ Nat.Coprime s W)
    let delta := T / (L : ℝ)
    (cW * Real.log (R : ℝ) / (k : ℝ)) * (∑ j ∈ Finset.range L, delta * f (((j + 1 : ℕ) : ℝ) * delta)) -
      2 * (L : ℝ) * C_W ≤
      ∑ s ∈ S_U, f (tVal k R s) / (Nat.totient s : ℝ) ∧
    ∑ s ∈ S_U, f (tVal k R s) / (Nat.totient s : ℝ) ≤
      (cW * Real.log (R : ℝ) / (k : ℝ)) * (∑ j ∈ Finset.range L, delta * f ((j : ℝ) * delta)) +
        2 * (L : ℝ) * C_W + 1 := by
  classical
  intro W cW S_U delta
  have hlogR_pos : 0 < Real.log (R : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < R))
  have hR_pos : (0 : ℝ) < R := by exact_mod_cast (by omega : 0 < R)
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hL_pos : (0 : ℝ) < L := Nat.cast_pos.mpr hL
  have hdelta_pos : 0 < delta := div_pos hT hL_pos
  let Y : ℕ → ℝ := fun j => (R : ℝ) ^ (((j : ℝ) * delta) / (k : ℝ))
  let N : ℕ → ℕ := fun j => ⌊Y j⌋₊
  have hY_ge1 : ∀ j, 1 ≤ Y j := fun j =>
    Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ R)) (by positivity)
  have hY_mono : ∀ i j, i ≤ j → Y i ≤ Y j := fun i j hij =>
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ R))
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hij) hdelta_pos.le) hk_pos.le)
  have hN_mono : ∀ i j, i ≤ j → N i ≤ N j := fun i j hij => Nat.floor_mono (hY_mono i j hij)
  have hN0 : N 0 = 1 := by simp [N, Y]
  have hNL : N L = U := by
    rw [hU]
    change ⌊Y L⌋₊ = ⌊(R : ℝ) ^ (T / (k : ℝ))⌋₊
    congr 1
    dsimp only [Y, delta]
    congr 1
    field_simp
  -- Block sum identity: sum{s in SU} = f(0) + sum{j in range L} sum{s in Ioc (N j) (N (j+1)), sqfree, cop W}
  let block : ℕ → Finset ℕ := fun j =>
    (Finset.Ioc (N j) (N (j + 1))).filter (fun s => Squarefree s ∧ Nat.Coprime s W)
  have hS_U_split :
      ∑ s ∈ S_U, f (tVal k R s) / (Nat.totient s : ℝ) =
      f (tVal k R 1) + ∑ j ∈ Finset.range L, ∑ s ∈ block j, f (tVal k R s) / (Nat.totient s : ℝ) := by
    have hU1 : 1 ≤ U := by rw [← hNL, ← hN0]; exact hN_mono 0 L (Nat.zero_le L)
    have h1SU : 1 ∈ S_U :=
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_refl 1, hU1⟩, squarefree_one, Nat.coprime_one_left _⟩
    rw [← Finset.add_sum_erase _ _ h1SU]
    have h1term : f (tVal k R 1) / (Nat.totient 1 : ℝ) = f (tVal k R 1) := by simp
    rw [h1term]
    congr 1
    have hdisj : Set.PairwiseDisjoint (Finset.range L : Set ℕ) block := by
      intro i _ j _ hij
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro s hsi hsj
      have hi1 := Finset.mem_Ioc.mp (Finset.mem_filter.mp hsi).1
      have hj1 := Finset.mem_Ioc.mp (Finset.mem_filter.mp hsj).1
      rcases lt_or_gt_of_ne hij with hlt | hgt
      · have := hN_mono (i + 1) j (by omega); omega
      · have := hN_mono (j + 1) i (by omega); omega
    rw [← Finset.sum_biUnion hdisj]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext s
    simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_Icc, Finset.mem_biUnion,
      Finset.mem_range, Finset.mem_Ioc, S_U, block]
    constructor
    · rintro ⟨hs1, ⟨h1s, hsU⟩, hsq, hcop⟩
      -- Find minimal j < L such that s <= N (j + 1)
      have hex : ∃ j, j < L ∧ s ≤ N (j + 1) := ⟨L - 1, by omega, by
        have : L - 1 + 1 = L := by omega
        rw [this, hNL]; exact hsU⟩
      classical
      let j := Nat.find hex
      have hj_spec := Nat.find_spec hex
      have hj_gt : N j < s := by
        by_cases hj0 : j = 0
        · rw [hj0, hN0]; omega
        · have hj_prev := Nat.find_min hex (m := j - 1) (by omega)
          push Not at hj_prev
          have hsub : j - 1 + 1 = j := by omega
          have := hj_prev (by omega)
          rwa [hsub] at this
      exact ⟨j, hj_spec.1, ⟨hj_gt, hj_spec.2⟩, hsq, hcop⟩
    · rintro ⟨j, hjL, ⟨hj_gt, hj_le⟩, hsq, hcop⟩
      have hN0_le : 1 ≤ N j := hN0 ▸ hN_mono 0 j (Nat.zero_le j)
      have hNj1_le : N (j + 1) ≤ U := hNL ▸ hN_mono (j + 1) L (by omega)
      exact ⟨by omega, ⟨by omega, le_trans hj_le hNj1_le⟩, hsq, hcop⟩
  -- On each block j, tVal k R s lies in [j * delta, (j + 1) * delta]
  have ht_block : ∀ j ∈ Finset.range L, ∀ s ∈ block j,
      (j : ℝ) * delta ≤ tVal k R s ∧ tVal k R s ≤ ((j + 1 : ℕ) : ℝ) * delta := by
    intro j _ s hs
    have hIoc := Finset.mem_Ioc.mp (Finset.mem_filter.mp hs).1
    have hN0_le : 1 ≤ N j := hN0 ▸ hN_mono 0 j (Nat.zero_le j)
    have hs_pos : (0 : ℝ) < s := Nat.cast_pos.mpr (by omega)
    have hY_lt_s : Y j < (s : ℝ) := by
      have h1 : (N j : ℝ) + 1 ≤ (s : ℝ) := by exact_mod_cast hIoc.1
      linarith [Nat.lt_floor_add_one (Y j)]
    have hs_le_Y : (s : ℝ) ≤ Y (j + 1) :=
      le_trans (Nat.cast_le.mpr hIoc.2) (Nat.floor_le (by linarith [hY_ge1 (j + 1)]))
    have hlog1 : Real.log (Y j) ≤ Real.log (s : ℝ) :=
      Real.log_le_log (by linarith [hY_ge1 j]) hY_lt_s.le
    have hlog2 : Real.log (s : ℝ) ≤ Real.log (Y (j + 1)) :=
      Real.log_le_log hs_pos hs_le_Y
    rw [Real.log_rpow hR_pos] at hlog1 hlog2
    unfold tVal
    constructor
    · rw [le_div_iff₀ hlogR_pos]
      have heq : (k : ℝ) * (((j : ℝ) * delta / (k : ℝ)) * Real.log (R : ℝ)) =
          (j : ℝ) * delta * Real.log (R : ℝ) := by field_simp
      nlinarith
    · rw [div_le_iff₀ hlogR_pos]
      have heq : (k : ℝ) * ((((j + 1 : ℕ) : ℝ) * delta / (k : ℝ)) * Real.log (R : ℝ)) =
          ((j + 1 : ℕ) : ℝ) * delta * Real.log (R : ℝ) := by field_simp
      nlinarith
  -- Sum of 1/phi(s) on block j is cW times (delta / k) times log R + error in [-2 times CW, 2 times CW]
  have hblock_mass : ∀ j ∈ Finset.range L,
      |(∑ s ∈ block j, (1 / (Nat.totient s : ℝ))) - (cW * Real.log (R : ℝ) / (k : ℝ)) * delta| ≤ 2 * C_W := by
    intro j _
    let M : ℕ → ℝ := fun n =>
      ∑ r ∈ (Finset.Icc 1 n).filter (fun r => Squarefree r ∧ Nat.Coprime r W), (1 / (Nat.totient r : ℝ))
    have hdiff_M : ∑ s ∈ block j, (1 / (Nat.totient s : ℝ)) = M (N (j + 1)) - M (N j) := by
      have hsub : (Finset.Icc 1 (N j)).filter (fun r => Squarefree r ∧ Nat.Coprime r W) ⊆
          (Finset.Icc 1 (N (j + 1))).filter (fun r => Squarefree r ∧ Nat.Coprime r W) := by
        intro r hr
        rw [Finset.mem_filter, Finset.mem_Icc] at hr ⊢
        exact ⟨⟨hr.1.1, le_trans hr.1.2 (hN_mono j (j + 1) (Nat.le_succ j))⟩, hr.2⟩
      rw [← Finset.sum_sdiff_eq_sub hsub]
      refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext s
      simp only [block, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc]
      have hN0_le : 1 ≤ N j := hN0 ▸ hN_mono 0 j (Nat.zero_le j)
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨⟨⟨by omega, h2⟩, h3⟩, fun h => by omega⟩
      · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
        refine ⟨⟨?_, h2⟩, h3⟩
        by_contra hle
        exact h4 ⟨⟨h1, by omega⟩, h3⟩
    rw [hdiff_M]
    have h1 := hMertens (Y (j + 1)) (hY_ge1 (j + 1))
    have h2 := hMertens (Y j) (hY_ge1 j)
    have hlog_diff : cW * Real.log (Y (j + 1)) - cW * Real.log (Y j) =
        (cW * Real.log (R : ℝ) / (k : ℝ)) * delta := by
      dsimp only [Y]
      rw [Real.log_rpow hR_pos, Real.log_rpow hR_pos]
      push_cast; field_simp; ring
    rw [abs_le] at h1 h2 ⊢
    constructor <;> linarith
  -- Derive lower and upper bounds
  rw [hS_U_split]
  have hf1_bounds : 0 ≤ f (tVal k R 1) ∧ f (tVal k R 1) ≤ 1 := by
    have ht1 : 0 ≤ tVal k R 1 := tVal_nonneg hR (le_refl 1)
    exact ⟨hf0 _ ht1, hf1 _ ht1⟩
  constructor
  · -- Lower bound
    have hsum_low :
        ∑ j ∈ Finset.range L,
          ((cW * Real.log (R : ℝ) / (k : ℝ)) * (delta * f (((j + 1 : ℕ) : ℝ) * delta)) - 2 * C_W) ≤
        ∑ j ∈ Finset.range L, ∑ s ∈ block j, f (tVal k R s) / (Nat.totient s : ℝ) := by
      refine Finset.sum_le_sum fun j hj => ?_
      have hfj_nn : 0 ≤ f (((j + 1 : ℕ) : ℝ) * delta) := hf0 _ (by positivity)
      have hfj_le1 : f (((j + 1 : ℕ) : ℝ) * delta) ≤ 1 := hf1 _ (by positivity)
      have hmass := (abs_le.mp (hblock_mass j hj)).1
      calc (cW * Real.log (R : ℝ) / (k : ℝ)) * (delta * f (((j + 1 : ℕ) : ℝ) * delta)) - 2 * C_W
          ≤ ((cW * Real.log (R : ℝ) / (k : ℝ)) * delta - 2 * C_W) * f (((j + 1 : ℕ) : ℝ) * delta) := by
            have : 2 * C_W * f (((j + 1 : ℕ) : ℝ) * delta) ≤ 2 * C_W := by nlinarith
            linarith
        _ ≤ (∑ s ∈ block j, (1 / (Nat.totient s : ℝ))) * f (((j + 1 : ℕ) : ℝ) * delta) :=
            mul_le_mul_of_nonneg_right (by linarith) hfj_nn
        _ = ∑ s ∈ block j, f (((j + 1 : ℕ) : ℝ) * delta) / (Nat.totient s : ℝ) := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun s _ => by ring
        _ ≤ ∑ s ∈ block j, f (tVal k R s) / (Nat.totient s : ℝ) := by
            refine Finset.sum_le_sum fun s hs => div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
            have ht := ht_block j hj s hs
            exact hf_anti _ _ (by linarith [show (0 : ℝ) ≤ (j : ℝ) * delta by positivity]) ht.2
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum_low
    linarith
  · -- Upper bound
    have hsum_high :
        ∑ j ∈ Finset.range L, ∑ s ∈ block j, f (tVal k R s) / (Nat.totient s : ℝ) ≤
        ∑ j ∈ Finset.range L,
          ((cW * Real.log (R : ℝ) / (k : ℝ)) * (delta * f ((j : ℝ) * delta)) + 2 * C_W) := by
      refine Finset.sum_le_sum fun j hj => ?_
      have hfj_nn : 0 ≤ f ((j : ℝ) * delta) := hf0 _ (by positivity)
      have hfj_le1 : f ((j : ℝ) * delta) ≤ 1 := hf1 _ (by positivity)
      have hmass := (abs_le.mp (hblock_mass j hj)).2
      calc ∑ s ∈ block j, f (tVal k R s) / (Nat.totient s : ℝ)
          ≤ ∑ s ∈ block j, f ((j : ℝ) * delta) / (Nat.totient s : ℝ) := by
            refine Finset.sum_le_sum fun s hs => div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
            exact hf_anti _ _ (by positivity) (ht_block j hj s hs).1
        _ = (∑ s ∈ block j, (1 / (Nat.totient s : ℝ))) * f ((j : ℝ) * delta) := by
            rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun _ _ => by ring
        _ ≤ ((cW * Real.log (R : ℝ) / (k : ℝ)) * delta + 2 * C_W) * f ((j : ℝ) * delta) :=
            mul_le_mul_of_nonneg_right (by linarith) hfj_nn
        _ ≤ (cW * Real.log (R : ℝ) / (k : ℝ)) * (delta * f ((j : ℝ) * delta)) + 2 * C_W := by
            have : 2 * C_W * f ((j : ℝ) * delta) ≤ 2 * C_W := by nlinarith
            linarith
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum_high
    linarith

/-- Elementary Riemann sum bounds for f_1(t) = 1 / (1 + A t) on [0, T] with T = (exp A - 1) / A. -/
lemma riemann_sum_g1_bounds {A : ℝ} (hA : 0 < A) {L : ℕ} (hL : 1 ≤ L) :
    let T := (Real.exp A - 1) / A
    let delta := T / (L : ℝ)
    1 - T / (L : ℝ) ≤ ∑ j ∈ Finset.range L, delta * (1 / (1 + A * (((j + 1 : ℕ) : ℝ) * delta))) ∧
    ∑ j ∈ Finset.range L, delta * (1 / (1 + A * ((j : ℝ) * delta))) ≤ 1 + T / (L : ℝ) := by
  intro T delta
  have hT_pos : 0 < T := div_pos (by linarith [Real.add_one_lt_exp hA.ne']) hA
  have hL_pos : (0 : ℝ) < L := Nat.cast_pos.mpr hL
  have hdelta_pos : 0 < delta := div_pos hT_pos hL_pos
  -- Step bounds for antiderivative F_1(t) = log(1 + A t) / A
  have hstep : ∀ j : ℕ,
      delta * (1 / (1 + A * (((j + 1 : ℕ) : ℝ) * delta))) ≤
        Real.log (1 + A * (((j + 1 : ℕ) : ℝ) * delta)) / A - Real.log (1 + A * ((j : ℝ) * delta)) / A ∧
      Real.log (1 + A * (((j + 1 : ℕ) : ℝ) * delta)) / A - Real.log (1 + A * ((j : ℝ) * delta)) / A ≤
        delta * (1 / (1 + A * ((j : ℝ) * delta))) := by
    intro j
    set a := 1 + A * ((j : ℝ) * delta)
    set b := 1 + A * (((j + 1 : ℕ) : ℝ) * delta)
    have ha_pos : 0 < a := by dsimp only [a]; positivity
    have hb_pos : 0 < b := by dsimp only [b]; positivity
    have hba : b - a = A * delta := by dsimp only [a, b]; push_cast; ring
    have hlog_eq : Real.log b / A - Real.log a / A = Real.log (b / a) / A := by
      rw [← sub_div, Real.log_div hb_pos.ne' ha_pos.ne']
    rw [hlog_eq]
    constructor
    · have h2 : 1 - a / b = A * delta / b := by
        have : (b - a) / b = 1 - a / b := by field_simp
        rw [← this, hba]
      have h3 : A * delta / b ≤ Real.log (b / a) := by
        have : -Real.log (b / a) = Real.log (a / b) := by
          rw [Real.log_div ha_pos.ne' hb_pos.ne', Real.log_div hb_pos.ne' ha_pos.ne']; ring
        linarith [Real.log_le_sub_one_of_pos (div_pos ha_pos hb_pos)]
      have h4 := div_le_div_of_nonneg_right h3 hA.le
      have h5 : A * delta / b / A = delta * (1 / b) := by field_simp
      linarith
    · have h1 := Real.log_le_sub_one_of_pos (div_pos hb_pos ha_pos)
      have h2 : b / a - 1 = A * delta / a := by
        have : (b - a) / a = b / a - 1 := by field_simp
        rw [← this, hba]
      have h3 := div_le_div_of_nonneg_right (by linarith : Real.log (b / a) ≤ A * delta / a) hA.le
      have h4 : A * delta / a / A = delta * (1 / a) := by field_simp
      linarith
  have htel_F : ∑ j ∈ Finset.range L,
      (Real.log (1 + A * (((j + 1 : ℕ) : ℝ) * delta)) / A - Real.log (1 + A * ((j : ℝ) * delta)) / A) = 1 := by
    have hsum : ∀ n : ℕ, ∑ j ∈ Finset.range n,
        (Real.log (1 + A * (((j + 1 : ℕ) : ℝ) * delta)) / A - Real.log (1 + A * ((j : ℝ) * delta)) / A) =
        Real.log (1 + A * ((n : ℝ) * delta)) / A := by
      intro n
      induction n with
      | zero => simp
      | succ m ih => rw [Finset.sum_range_succ, ih]; ring
    rw [hsum L]
    have hAT : 1 + A * ((L : ℝ) * delta) = Real.exp A := by
      dsimp only [delta, T]; field_simp; ring
    rw [hAT, Real.log_exp, div_self hA.ne']
  have hgap :
      (∑ j ∈ Finset.range L, delta * (1 / (1 + A * ((j : ℝ) * delta)))) -
      (∑ j ∈ Finset.range L, delta * (1 / (1 + A * (((j + 1 : ℕ) : ℝ) * delta)))) ≤ T / (L : ℝ) := by
    rw [← Finset.sum_sub_distrib]
    have hsum : ∀ n : ℕ, ∑ j ∈ Finset.range n,
        (delta * (1 / (1 + A * ((j : ℝ) * delta))) - delta * (1 / (1 + A * (((j + 1 : ℕ) : ℝ) * delta)))) =
        delta * (1 - 1 / (1 + A * ((n : ℝ) * delta))) := by
      intro n
      induction n with
      | zero => simp
      | succ m ih => rw [Finset.sum_range_succ, ih]; ring
    rw [hsum L]
    have hnn : 0 ≤ 1 / (1 + A * ((L : ℝ) * delta)) := by positivity
    nlinarith
  have hlow_F : ∑ j ∈ Finset.range L, delta * (1 / (1 + A * (((j + 1 : ℕ) : ℝ) * delta))) ≤ 1 := by
    conv_rhs => rw [← htel_F]
    exact Finset.sum_le_sum fun j _ => (hstep j).1
  have hhigh_F : 1 ≤ ∑ j ∈ Finset.range L, delta * (1 / (1 + A * ((j : ℝ) * delta))) := by
    conv_lhs => rw [← htel_F]
    exact Finset.sum_le_sum fun j _ => (hstep j).2
  constructor <;> linarith

/-- Elementary Riemann sum bounds for f_2(t) = 1 / (1 + A t)^2 on [0, T] with T = (exp A - 1) / A. -/
lemma riemann_sum_g2_bounds {A : ℝ} (hA : 0 < A) {L : ℕ} (hL : 1 ≤ L) :
    let T := (Real.exp A - 1) / A
    let delta := T / (L : ℝ)
    let I2 := (1 - Real.exp (-A)) / A
    I2 - T / (L : ℝ) ≤ ∑ j ∈ Finset.range L, delta * (1 / (1 + A * (((j + 1 : ℕ) : ℝ) * delta)) ^ 2) ∧
    ∑ j ∈ Finset.range L, delta * (1 / (1 + A * ((j : ℝ) * delta)) ^ 2) ≤ I2 + T / (L : ℝ) := by
  intro T delta I2
  have hT_pos : 0 < T := div_pos (by linarith [Real.add_one_lt_exp hA.ne']) hA
  have hL_pos : (0 : ℝ) < L := Nat.cast_pos.mpr hL
  have hdelta_pos : 0 < delta := div_pos hT_pos hL_pos
  -- Step bounds for antiderivative F_2(t) = -1 / (A * (1 + A t))
  have hstep : ∀ j : ℕ,
      delta * (1 / (1 + A * (((j + 1 : ℕ) : ℝ) * delta)) ^ 2) ≤
        (1 / (A * (1 + A * ((j : ℝ) * delta))) - 1 / (A * (1 + A * (((j + 1 : ℕ) : ℝ) * delta)))) ∧
      (1 / (A * (1 + A * ((j : ℝ) * delta))) - 1 / (A * (1 + A * (((j + 1 : ℕ) : ℝ) * delta)))) ≤
        delta * (1 / (1 + A * ((j : ℝ) * delta)) ^ 2) := by
    intro j
    set a := 1 + A * ((j : ℝ) * delta)
    set b := 1 + A * (((j + 1 : ℕ) : ℝ) * delta)
    have ha_pos : 0 < a := by dsimp only [a]; positivity
    have hb_pos : 0 < b := by dsimp only [b]; positivity
    have hab : a ≤ b := by dsimp only [a, b]; push_cast; nlinarith
    have hdiff : 1 / (A * a) - 1 / (A * b) = delta / (a * b) := by
      have hba : b - a = A * delta := by dsimp only [a, b]; push_cast; ring
      have h1 : 1 / (A * a) - 1 / (A * b) = (b - a) / (A * a * b) := by field_simp
      rw [h1, hba]; field_simp
    rw [hdiff]
    constructor
    · rw [mul_one_div]
      exact div_le_div_of_nonneg_left hdelta_pos.le (mul_pos ha_pos hb_pos) (by nlinarith)
    · rw [mul_one_div]
      exact div_le_div_of_nonneg_left hdelta_pos.le (sq_pos_of_pos ha_pos) (by nlinarith)
  have htel_F : ∑ j ∈ Finset.range L,
      (1 / (A * (1 + A * ((j : ℝ) * delta))) - 1 / (A * (1 + A * (((j + 1 : ℕ) : ℝ) * delta)))) = I2 := by
    have hsum : ∀ n : ℕ, ∑ j ∈ Finset.range n,
        (1 / (A * (1 + A * ((j : ℝ) * delta))) - 1 / (A * (1 + A * (((j + 1 : ℕ) : ℝ) * delta)))) =
        1 / A - 1 / (A * (1 + A * ((n : ℝ) * delta))) := by
      intro n
      induction n with
      | zero => simp
      | succ m ih => rw [Finset.sum_range_succ, ih]; ring
    rw [hsum L]
    have hAT : 1 + A * ((L : ℝ) * delta) = Real.exp A := by
      dsimp only [delta, T]; field_simp; ring
    dsimp only [I2]
    rw [hAT, Real.exp_neg]
    have hene : Real.exp A ≠ 0 := (Real.exp_pos A).ne'
    field_simp
  have hgap :
      (∑ j ∈ Finset.range L, delta * (1 / (1 + A * ((j : ℝ) * delta)) ^ 2)) -
      (∑ j ∈ Finset.range L, delta * (1 / (1 + A * (((j + 1 : ℕ) : ℝ) * delta)) ^ 2)) ≤ T / (L : ℝ) := by
    rw [← Finset.sum_sub_distrib]
    have hsum : ∀ n : ℕ, ∑ j ∈ Finset.range n,
        (delta * (1 / (1 + A * ((j : ℝ) * delta)) ^ 2) - delta * (1 / (1 + A * (((j + 1 : ℕ) : ℝ) * delta)) ^ 2)) =
        delta * (1 - 1 / (1 + A * ((n : ℝ) * delta)) ^ 2) := by
      intro n
      induction n with
      | zero => simp
      | succ m ih => rw [Finset.sum_range_succ, ih]; ring
    rw [hsum L]
    have hnn : 0 ≤ 1 / (1 + A * ((L : ℝ) * delta)) ^ 2 := by positivity
    nlinarith
  have hlow_F : ∑ j ∈ Finset.range L, delta * (1 / (1 + A * (((j + 1 : ℕ) : ℝ) * delta)) ^ 2) ≤ I2 := by
    rw [← htel_F]; exact Finset.sum_le_sum fun j _ => (hstep j).1
  have hhigh_F : I2 ≤ ∑ j ∈ Finset.range L, delta * (1 / (1 + A * ((j : ℝ) * delta)) ^ 2) := by
    rw [← htel_F]; exact Finset.sum_le_sum fun j _ => (hstep j).2
  constructor <;> linarith

-- ## Section 5: Final assembly of Maynard-Tao from Bombieri-Vinogradov

/-- Elementary logarithm bound: log x <= x^alpha / alpha for x > 0 and alpha > 0. -/
lemma log_le_rpow_div {x α : ℝ} (hx : 0 < x) (hα : 0 < α) :
    Real.log x ≤ x ^ α / α := by
  have h1 := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx α)
  rw [Real.log_rpow hx] at h1
  rw [le_div_iff₀ hα]
  linarith

set_option maxHeartbeats 600000 in
/-- Existence of a sufficiently large dyadic scale X satisfying all asymptotic inequalities. -/
lemma exists_large_X_params {k M W Bmax L N : ℕ} {B C' T C_W eps I2 : ℝ}
    (hk : 2 ≤ k) (hM : 0 < M) (hW : 0 < W) (_hL : 1 ≤ L)
    (hC' : 0 ≤ C') (hT : 0 < T) (hTk : T < (k : ℝ))
    (_hCW : 0 ≤ C_W) (heps : 0 < eps) (hI2 : 0 < I2) :
    let cW : ℝ := (Nat.totient W : ℝ) / (W : ℝ)
    let mBV : ℕ := 5 * k ^ 2 + 6 * k + 10
    let A_BV : ℝ := ((2 * mBV + 1 : ℕ) : ℝ)
    ∃ X : ℕ, N < X ∧
      let R := ⌊(X : ℝ) ^ ((1 : ℝ) / 5)⌋₊
      let U := ⌊(R : ℝ) ^ (T / (k : ℝ))⌋₊
      let scale := cW * Real.log (R : ℝ) / (k : ℝ)
      2 ≤ R ∧ R < X ∧ 1 ≤ U ∧ U ≤ R ∧
      1 ≤ (1 / 2 : ℝ) * scale ∧
      1 ≤ (I2 / 2) * scale ∧
      Real.log ((2 * M * W * X + Bmax : ℕ) : ℝ) ≤ 6 * Real.log (R : ℝ) ∧
      2 * (L : ℝ) * C_W + 1 ≤ eps * scale ∧
      C_W ≤ T * scale ∧
      (R : ℝ) ^ 2 * (2 * Real.log (R : ℝ) + 2) ^ (8 * k) ≤
        (1 / 10 : ℝ) * (X : ℝ) * ((I2 / 2) * scale) ^ k ∧
      (∀ b' ≤ Bmax,
        let x1 : ℝ := ((M * W * X + b' : ℕ) : ℝ)
        let x2 : ℝ := ((2 * M * W * X + b' : ℕ) : ℝ)
        (3 : ℝ) ≤ x1 ∧
        M * W * R ^ 2 ≤ ⌊Real.sqrt x1 / Real.log x1 ^ B⌋₊ ∧
        M * W * R ^ 2 ≤ ⌊Real.sqrt x2 / Real.log x2 ^ B⌋₊ ∧
        M * W * R ^ 2 ≤ M * W * X + b' ∧
        (2 * Real.log (R : ℝ) + 2) ^ (6 * k) *
          Real.sqrt ((2 * Real.log (R : ℝ) + 1) ^ (9 * k ^ 2)) *
          (Real.sqrt (5 * C' * x2 ^ 2 * Real.log x2 / Real.log x2 ^ A_BV) +
            Real.sqrt (5 * C' * x1 ^ 2 * Real.log x1 / Real.log x1 ^ A_BV)) ≤
          (1 / 10 : ℝ) * ((W : ℝ) / (Nat.totient W : ℝ)) * (X : ℝ) *
            ((1 / 2 : ℝ) * scale) ^ 2 * ((I2 / 2) * scale) ^ (k - 1)) := by
  intro cW mBV A_BV
  have hMW_pos : 0 < M * W := Nat.mul_pos hM hW
  have hMW_r : (1 : ℝ) ≤ (M * W : ℕ) := by exact_mod_cast hMW_pos
  have hcW_pos : 0 < cW := div_pos (Nat.cast_pos.mpr (Nat.totient_pos.mpr hW)) (Nat.cast_pos.mpr hW)
  have hcW_le1 : cW ≤ 1 := by
    dsimp only [cW]
    rw [div_le_one (Nat.cast_pos.mpr hW)]
    exact_mod_cast Nat.totient_le W
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr (by omega)
  -- Explicit thresholds for X
  let Bpos : ℝ := max B 0
  let αB : ℝ := 1 / (20 * (Bpos + 1))
  have hαB_pos : 0 < αB := by dsimp only [αB, Bpos]; positivity
  let KB : ℝ := (1 / αB) ^ Bpos
  have hKB_pos : 0 < KB := Real.rpow_pos_of_pos (div_pos one_pos hαB_pos) _
  let K_BV : ℝ := 20 * (4 : ℝ) ^ (6 * k) * (4 : ℝ) ^ (5 * k ^ 2) * Real.sqrt (5 * C') * (3 * (M * W : ℝ))
  let K_log : ℝ := max 10 (max ((2 * (k : ℝ)) / cW)
    (max ((2 * (k : ℝ)) / (I2 * cW))
      (max (((2 * (L : ℝ) * C_W + 1) * (k : ℝ)) / (eps * cW))
        (max ((C_W * (k : ℝ)) / (T * cW)) K_BV))))
  let αS : ℝ := 1 / (40 * (k : ℝ))
  have hαS_pos : 0 < αS := by dsimp only [αS]; positivity
  let KS : ℝ := 10 * (4 / αS) ^ (8 * k)
  let X1 : ℕ := N + Bmax + 3 * M * W + 100
  let X2 : ℕ := (Nat.ceil (Real.exp K_log) + 2) ^ 5
  let X3 : ℕ := (64 * (3 * M * W + Bmax) + 2) ^ 5
  let X4 : ℕ := (Nat.ceil (2 * (M * W : ℝ) * KB + 2) + 2) ^ 20
  let X5 : ℕ := (Nat.ceil KS + 2) ^ 3
  obtain ⟨X, hX_ge1, hX_ge2, hX_ge3, hX_ge4, hX_ge5⟩ :
      ∃ X : ℕ, X1 ≤ X ∧ X2 ≤ X ∧ X3 ≤ X ∧ X4 ≤ X ∧ X5 ≤ X :=
    ⟨max X1 (max X2 (max X3 (max X4 X5))),
      le_max_left _ _,
      le_trans (le_max_left _ _) (le_max_right _ _),
      le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _)),
      le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))),
      le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))⟩
  have hX_pos : (0 : ℝ) < X := Nat.cast_pos.mpr (by dsimp only [X1] at hX_ge1; omega)
  have hX_ge32 : (32 : ℝ) ≤ X := by exact_mod_cast (by dsimp only [X1] at hX_ge1; omega : 32 ≤ X)
  let R := ⌊(X : ℝ) ^ ((1 : ℝ) / 5)⌋₊
  let U := ⌊(R : ℝ) ^ (T / (k : ℝ))⌋₊
  let scale := cW * Real.log (R : ℝ) / (k : ℝ)
  -- Basic bounds on R: (1/2) * X^(1/5) <= R <= X^(1/5) and exp K_log <= R
  have hX5_ge2 : (2 : ℝ) ≤ (X : ℝ) ^ ((1 : ℝ) / 5) := by
    have h1 : (2 : ℝ) = ((32 : ℝ) ^ ((1 : ℝ) / 5)) := by
      have : (32 : ℝ) = (2 : ℝ) ^ (5 : ℕ) := by norm_num
      rw [this, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
    rw [h1]
    exact Real.rpow_le_rpow (by norm_num) hX_ge32 (by norm_num)
  have hR_le_X5 : (R : ℝ) ≤ (X : ℝ) ^ ((1 : ℝ) / 5) := Nat.floor_le (by positivity)
  have hR_ge_half : (X : ℝ) ^ ((1 : ℝ) / 5) / 2 ≤ (R : ℝ) := by
    have hlt := Nat.lt_floor_add_one ((X : ℝ) ^ ((1 : ℝ) / 5))
    linarith
  have hR_ge2 : 2 ≤ R := (Nat.le_floor_iff (by positivity)).mpr (by exact_mod_cast hX5_ge2)
  have hR_pos : (0 : ℝ) < R := Nat.cast_pos.mpr (by omega)
  have hR_lt_X : R < X := by
    have h1 : (X : ℝ) ^ ((1 : ℝ) / 5) < (X : ℝ) := by
      have hX_gt1 : (1 : ℝ) < X := by linarith
      calc (X : ℝ) ^ ((1 : ℝ) / 5) < (X : ℝ) ^ (1 : ℝ) := Real.rpow_lt_rpow_of_exponent_lt hX_gt1 (by norm_num)
        _ = (X : ℝ) := Real.rpow_one _
    have : (R : ℝ) < (X : ℝ) := lt_of_le_of_lt hR_le_X5 h1
    exact_mod_cast this
  have hU_ge1 : 1 ≤ U := by
    have h1 : (1 : ℝ) ≤ (R : ℝ) ^ (T / (k : ℝ)) :=
      Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ R)) (by positivity)
    exact (Nat.le_floor_iff (by positivity)).mpr (by exact_mod_cast h1)
  have hU_le_R : U ≤ R := by
    have h1 : (R : ℝ) ^ (T / (k : ℝ)) ≤ (R : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ R))
        ((div_le_one hk_pos).mpr hTk.le)
    rw [Real.rpow_one] at h1
    have h2 : (U : ℝ) ≤ (R : ℝ) := le_trans (Nat.floor_le (by positivity)) h1
    exact_mod_cast h2
  -- Lower bound: K_log <= log R <= log X
  have hKlog_le_logR : K_log ≤ Real.log (R : ℝ) := by
    have h1 : ((Nat.ceil (Real.exp K_log) + 2 : ℕ) : ℝ) ^ (5 : ℕ) ≤ (X : ℝ) := by exact_mod_cast hX_ge2
    have h2 : ((Nat.ceil (Real.exp K_log) + 2 : ℕ) : ℝ) ≤ (X : ℝ) ^ ((1 : ℝ) / 5) := by
      have hpow := Real.rpow_le_rpow (by positivity) h1 (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 5)
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)] at hpow
      simpa using hpow
    have h3 : Real.exp K_log ≤ (R : ℝ) := by
      have hlt := Nat.lt_floor_add_one ((X : ℝ) ^ ((1 : ℝ) / 5))
      have hceil := Nat.le_ceil (Real.exp K_log)
      push_cast at h2
      linarith
    have := Real.log_le_log (Real.exp_pos K_log) h3
    rwa [Real.log_exp] at this
  have hlogR_ge10 : 10 ≤ Real.log (R : ℝ) := le_trans (le_max_left _ _) hKlog_le_logR
  have hlogR_le_logX : Real.log (R : ℝ) ≤ Real.log (X : ℝ) :=
    Real.log_le_log hR_pos (Nat.cast_le.mpr hR_lt_X.le)
  have hlogX_ge10 : 10 ≤ Real.log (X : ℝ) := le_trans hlogR_ge10 hlogR_le_logX
  -- Scale lower bounds from K_log
  have hscale_half : 1 ≤ (1 / 2 : ℝ) * scale := by
    have h1 : (2 * (k : ℝ)) / cW ≤ Real.log (R : ℝ) :=
      le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hKlog_le_logR
    dsimp only [scale]
    rw [div_le_iff₀ hcW_pos] at h1
    have h2 : 1 ≤ cW * Real.log (R : ℝ) / (2 * (k : ℝ)) := by
      rw [one_le_div (by positivity)]; linarith only [h1]
    have heq : (1 / 2 : ℝ) * (cW * Real.log (R : ℝ) / (k : ℝ)) = cW * Real.log (R : ℝ) / (2 * (k : ℝ)) := by ring
    linarith only [h2, heq]
  have hscale_I2 : 1 ≤ (I2 / 2) * scale := by
    have h1 : (2 * (k : ℝ)) / (I2 * cW) ≤ Real.log (R : ℝ) :=
      le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hKlog_le_logR
    dsimp only [scale]
    rw [div_le_iff₀ (mul_pos hI2 hcW_pos)] at h1
    have h2 : 1 ≤ (I2 / 2) * (cW * Real.log (R : ℝ) / (k : ℝ)) := by
      have heq : (I2 / 2) * (cW * Real.log (R : ℝ) / (k : ℝ)) =
          (Real.log (R : ℝ) * (I2 * cW)) / (2 * (k : ℝ)) := by ring
      rw [heq, one_le_div (by positivity)]
      linarith
    exact h2
  have hL_CW : 2 * (L : ℝ) * C_W + 1 ≤ eps * scale := by
    have h1 : ((2 * (L : ℝ) * C_W + 1) * (k : ℝ)) / (eps * cW) ≤ Real.log (R : ℝ) :=
      le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
        (le_trans (le_max_right _ _) (le_max_right _ _)))) hKlog_le_logR
    dsimp only [scale]
    rw [div_le_iff₀ (mul_pos heps hcW_pos)] at h1
    have heq : eps * (cW * Real.log (R : ℝ) / (k : ℝ)) = (Real.log (R : ℝ) * (eps * cW)) / (k : ℝ) := by ring
    rw [heq, le_div_iff₀ hk_pos]
    exact h1
  have hCW_le : C_W ≤ T * scale := by
    have h1 : (C_W * (k : ℝ)) / (T * cW) ≤ Real.log (R : ℝ) :=
      le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
        (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))))) hKlog_le_logR
    dsimp only [scale]
    rw [div_le_iff₀ (mul_pos hT hcW_pos)] at h1
    have heq : T * (cW * Real.log (R : ℝ) / (k : ℝ)) = (Real.log (R : ℝ) * (T * cW)) / (k : ℝ) := by ring
    rw [heq, le_div_iff₀ hk_pos]
    exact h1
  have hKBV_le : K_BV ≤ Real.log (X : ℝ) :=
    le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))))
      (le_trans hKlog_le_logR hlogR_le_logX)
  -- (b) log (2 * M * W * X + Bmax) <= 6 * log R
  have hlog_max : Real.log ((2 * M * W * X + Bmax : ℕ) : ℝ) ≤ 6 * Real.log (R : ℝ) := by
    have hX3_r : ((64 * (3 * M * W + Bmax) + 2 : ℕ) : ℝ) ^ (5 : ℕ) ≤ (X : ℝ) := by exact_mod_cast hX_ge3
    have hX5_ge : ((64 * (3 * M * W + Bmax) + 2 : ℕ) : ℝ) ≤ (X : ℝ) ^ ((1 : ℝ) / 5) := by
      have hpow := Real.rpow_le_rpow (by positivity) hX3_r (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 5)
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)] at hpow
      simpa using hpow
    have hle_R6 : ((2 * M * W * X + Bmax : ℕ) : ℝ) ≤ (R : ℝ) ^ (6 : ℕ) := by
      have h1 : ((2 * M * W * X + Bmax : ℕ) : ℝ) ≤ ((3 * M * W + Bmax : ℕ) : ℝ) * (X : ℝ) := by
        have hX1 : 1 ≤ X := by dsimp only [X1] at hX_ge1; omega
        have hnat : 2 * M * W * X + Bmax ≤ (3 * M * W + Bmax) * X := by
          have h23 : 2 * M * W * X ≤ 3 * M * W * X := by
            have : 2 * (M * W * X) ≤ 3 * (M * W * X) := Nat.mul_le_mul_right _ (by omega)
            linarith only [this]
          calc 2 * M * W * X + Bmax ≤ 3 * M * W * X + Bmax * X :=
                Nat.add_le_add h23 (Nat.le_mul_of_pos_right Bmax hX1)
            _ = (3 * M * W + Bmax) * X := by ring
        exact_mod_cast hnat
      have hR6_ge : ((X : ℝ) ^ ((1 : ℝ) / 5) / 2) ^ (6 : ℕ) ≤ (R : ℝ) ^ (6 : ℕ) :=
        pow_le_pow_left₀ (by positivity) hR_ge_half 6
      have hpow6 : ((X : ℝ) ^ ((1 : ℝ) / 5) / 2) ^ (6 : ℕ) = (X : ℝ) ^ ((1 : ℝ) / 5) / 64 * (X : ℝ) := by
        rw [div_pow, ← Real.rpow_natCast ((X : ℝ) ^ _), ← Real.rpow_mul hX_pos.le]
        have heq : (1 : ℝ) / 5 * (6 : ℕ) = 1 / 5 + 1 := by norm_num
        rw [heq, Real.rpow_add hX_pos, Real.rpow_one]
        ring
      have hcoeff : ((3 * M * W + Bmax : ℕ) : ℝ) ≤ (X : ℝ) ^ ((1 : ℝ) / 5) / 64 := by
        push_cast at hX5_ge ⊢
        linarith only [hX5_ge]
      calc ((2 * M * W * X + Bmax : ℕ) : ℝ)
          ≤ ((3 * M * W + Bmax : ℕ) : ℝ) * (X : ℝ) := h1
        _ ≤ ((X : ℝ) ^ ((1 : ℝ) / 5) / 64) * (X : ℝ) := mul_le_mul_of_nonneg_right hcoeff hX_pos.le
        _ = ((X : ℝ) ^ ((1 : ℝ) / 5) / 2) ^ (6 : ℕ) := hpow6.symm
        _ ≤ (R : ℝ) ^ (6 : ℕ) := hR6_ge
    have hpos : (0 : ℝ) < ((2 * M * W * X + Bmax : ℕ) : ℝ) := by
      have hX1 : 0 < X := by dsimp only [X1] at hX_ge1; omega
      have : 0 < 2 * M * W * X + Bmax :=
        Nat.add_pos_left (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by omega : 0 < 2) hM) hW) hX1) Bmax
      exact_mod_cast this
    calc Real.log ((2 * M * W * X + Bmax : ℕ) : ℝ)
        ≤ Real.log ((R : ℝ) ^ (6 : ℕ)) := Real.log_le_log hpos hle_R6
      _ = 6 * Real.log (R : ℝ) := by rw [Real.log_pow]; ring
  -- (f) S1 error bound
  have hS1_err : (R : ℝ) ^ 2 * (2 * Real.log (R : ℝ) + 2) ^ (8 * k) ≤
      (1 / 10 : ℝ) * (X : ℝ) * ((I2 / 2) * scale) ^ k := by
    have hscale_pow : (1 : ℝ) ≤ ((I2 / 2) * scale) ^ k := one_le_pow₀ hscale_I2
    have hlog_bd : 2 * Real.log (R : ℝ) + 2 ≤ (4 / αS) * (X : ℝ) ^ αS := by
      have h1 : Real.log (X : ℝ) ≤ (X : ℝ) ^ αS / αS := log_le_rpow_div hX_pos hαS_pos
      have h2 : 2 * Real.log (R : ℝ) + 2 ≤ 4 * Real.log (X : ℝ) := by linarith
      calc 2 * Real.log (R : ℝ) + 2 ≤ 4 * Real.log (X : ℝ) := h2
        _ ≤ 4 * ((X : ℝ) ^ αS / αS) := mul_le_mul_of_nonneg_left h1 (by norm_num)
        _ = (4 / αS) * (X : ℝ) ^ αS := by ring
    have hpow_log : (2 * Real.log (R : ℝ) + 2) ^ (8 * k) ≤ (4 / αS) ^ (8 * k) * (X : ℝ) ^ ((1 : ℝ) / 5) := by
      calc (2 * Real.log (R : ℝ) + 2) ^ (8 * k)
          ≤ ((4 / αS) * (X : ℝ) ^ αS) ^ (8 * k) := pow_le_pow_left₀ (by linarith) hlog_bd _
        _ = (4 / αS) ^ (8 * k) * ((X : ℝ) ^ αS) ^ (8 * k) := mul_pow _ _ _
        _ = (4 / αS) ^ (8 * k) * (X : ℝ) ^ ((1 : ℝ) / 5) := by
            congr 1
            rw [← Real.rpow_natCast ((X : ℝ) ^ αS), ← Real.rpow_mul hX_pos.le]
            congr 1
            dsimp only [αS]
            push_cast; field_simp; ring
    have hR2_le : (R : ℝ) ^ 2 ≤ (X : ℝ) ^ ((2 : ℝ) / 5) := by
      calc (R : ℝ) ^ 2 ≤ ((X : ℝ) ^ ((1 : ℝ) / 5)) ^ (2 : ℕ) := pow_le_pow_left₀ (Nat.cast_nonneg _) hR_le_X5 2
        _ = (X : ℝ) ^ ((2 : ℝ) / 5) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hX_pos.le]; norm_num
    have hKS_le : KS ≤ (X : ℝ) ^ ((2 : ℝ) / 5) := by
      have hX5_r : ((Nat.ceil KS + 2 : ℕ) : ℝ) ^ (3 : ℕ) ≤ (X : ℝ) := by exact_mod_cast hX_ge5
      have h1 : ((Nat.ceil KS + 2 : ℕ) : ℝ) ≤ (X : ℝ) ^ ((1 : ℝ) / 3) := by
        have hpow := Real.rpow_le_rpow (by positivity) hX5_r (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 3)
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)] at hpow
        simpa using hpow
      have h2 : (X : ℝ) ^ ((1 : ℝ) / 3) ≤ (X : ℝ) ^ ((2 : ℝ) / 5) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      have hceil := Nat.le_ceil KS
      push_cast at h1
      linarith
    have hX_split : (X : ℝ) ^ ((2 : ℝ) / 5) * (X : ℝ) ^ ((1 : ℝ) / 5) * (X : ℝ) ^ ((2 : ℝ) / 5) = (X : ℝ) := by
      rw [← Real.rpow_add hX_pos, ← Real.rpow_add hX_pos]
      norm_num
    calc (R : ℝ) ^ 2 * (2 * Real.log (R : ℝ) + 2) ^ (8 * k)
        ≤ (X : ℝ) ^ ((2 : ℝ) / 5) * ((4 / αS) ^ (8 * k) * (X : ℝ) ^ ((1 : ℝ) / 5)) :=
          mul_le_mul hR2_le hpow_log (by positivity) (by positivity)
      _ = (1 / 10 : ℝ) * (KS * ((X : ℝ) ^ ((2 : ℝ) / 5) * (X : ℝ) ^ ((1 : ℝ) / 5))) := by
          dsimp only [KS]; ring
      _ ≤ (1 / 10 : ℝ) * ((X : ℝ) ^ ((2 : ℝ) / 5) * ((X : ℝ) ^ ((2 : ℝ) / 5) * (X : ℝ) ^ ((1 : ℝ) / 5))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hKS_le (by positivity)) (by norm_num)
      _ = (1 / 10 : ℝ) * (X : ℝ) := by
          have : (X : ℝ) ^ ((2 : ℝ) / 5) * ((X : ℝ) ^ ((2 : ℝ) / 5) * (X : ℝ) ^ ((1 : ℝ) / 5)) =
              (X : ℝ) ^ ((2 : ℝ) / 5) * (X : ℝ) ^ ((1 : ℝ) / 5) * (X : ℝ) ^ ((2 : ℝ) / 5) := by ring
          rw [this, hX_split]
      _ ≤ (1 / 10 : ℝ) * (X : ℝ) * ((I2 / 2) * scale) ^ k := by
          calc (1 / 10 : ℝ) * (X : ℝ) = (1 / 10 : ℝ) * (X : ℝ) * 1 := (mul_one _).symm
            _ ≤ (1 / 10 : ℝ) * (X : ℝ) * ((I2 / 2) * scale) ^ k :=
              mul_le_mul_of_nonneg_left hscale_pow (by positivity)
  -- Assemble all conclusions
  refine ⟨X, by dsimp only [X1] at hX_ge1; omega, hR_ge2, hR_lt_X, hU_ge1, hU_le_R,
    hscale_half, hscale_I2, hlog_max, hL_CW, hCW_le, hS1_err, ?_⟩
  intro b' hb' x1 x2
  have hx1_geX : (X : ℝ) ≤ x1 := by
    dsimp only [x1]
    have hnat : X ≤ M * W * X + b' := by
      have : 1 * X ≤ M * W * X := Nat.mul_le_mul_right X hMW_pos
      omega
    exact_mod_cast hnat
  have hx1_ge3 : (3 : ℝ) ≤ x1 := by linarith
  have hx1_le_x2 : x1 ≤ x2 := by
    dsimp only [x1, x2]
    have h12 : 1 * (M * W * X) ≤ 2 * (M * W * X) := Nat.mul_le_mul_right _ (by omega)
    have : M * W * X + b' ≤ 2 * M * W * X + b' := by linarith only [h12]
    exact_mod_cast this
  have hx2_le_3MWX : x2 ≤ 3 * (M * W : ℝ) * (X : ℝ) := by
    dsimp only [x2]
    have hnat : 2 * M * W * X + b' ≤ 3 * (M * W) * X := by
      have h1 : b' ≤ M * W * X := by
        have : 1 * X ≤ M * W * X := Nat.mul_le_mul_right X hMW_pos
        dsimp only [X1] at hX_ge1; omega
      have h2 : 2 * M * W * X + M * W * X = 3 * (M * W) * X := by ring
      omega
    have : ((2 * M * W * X + b' : ℕ) : ℝ) ≤ ((3 * (M * W) * X : ℕ) : ℝ) := Nat.cast_le.mpr hnat
    push_cast at this ⊢; linarith only [this]
  -- Helper: for any x with X <= x <= 3 * M * W * X, M * W * R^2 <= floor(sqrt x / log x ^ B)
  have hQ_bound_fn : ∀ x : ℝ, (X : ℝ) ≤ x → M * W * R ^ 2 ≤ ⌊Real.sqrt x / Real.log x ^ B⌋₊ := by
    intro x hx
    have hx_pos : 0 < x := lt_of_lt_of_le hX_pos hx
    have hlogx_ge1 : 1 ≤ Real.log x := le_trans (by linarith) (Real.log_le_log hX_pos hx)
    have hlogB_le : Real.log x ^ B ≤ KB * x ^ ((1 : ℝ) / 20) := by
      calc Real.log x ^ B ≤ Real.log x ^ Bpos :=
            Real.rpow_le_rpow_of_exponent_le hlogx_ge1 (le_max_left B 0)
        _ ≤ (x ^ αB / αB) ^ Bpos :=
            Real.rpow_le_rpow (by linarith) (log_le_rpow_div hx_pos hαB_pos) (le_max_right B 0)
        _ = (1 / αB) ^ Bpos * (x ^ αB) ^ Bpos := by
            rw [div_eq_mul_inv, mul_comm, Real.mul_rpow (by positivity) (by positivity), one_div]
        _ = KB * x ^ (αB * Bpos) := by rw [← Real.rpow_mul hx_pos.le]
        _ ≤ KB * x ^ ((1 : ℝ) / 20) := by
            refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by linarith) ?_) hKB_pos.le
            dsimp only [αB, Bpos]
            have hBnn : 0 ≤ max B 0 := le_max_right B 0
            rw [one_div_mul_eq_div, div_le_div_iff₀ (by linarith) (by norm_num)]
            linarith
    have hX4_r : ((Nat.ceil (2 * (M * W : ℝ) * KB + 2) + 2 : ℕ) : ℝ) ^ (20 : ℕ) ≤ (X : ℝ) := by
      have h1 : (X4 : ℝ) ≤ (X : ℝ) := Nat.cast_le.mpr hX_ge4
      dsimp only [X4] at h1
      rwa [Nat.cast_pow] at h1
    have hX20_ge : 2 * (M * W : ℝ) * KB + 2 ≤ (X : ℝ) ^ ((1 : ℝ) / 20) := by
      have hpow := Real.rpow_le_rpow (by positivity) hX4_r (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 20)
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)] at hpow
      have h20 : ((20 : ℕ) : ℝ) * ((1 : ℝ) / 20) = 1 := by norm_num
      rw [h20, Real.rpow_one, Nat.cast_add, Nat.cast_ofNat] at hpow
      have hceil := Nat.le_ceil (2 * (M * W : ℝ) * KB + 2)
      linarith only [hpow, hceil]
    have hMWR2_le : ((M * W * R ^ 2 : ℕ) : ℝ) ≤ Real.sqrt x / Real.log x ^ B := by
      have hden_pos : 0 < Real.log x ^ B := Real.rpow_pos_of_pos (by linarith) B
      rw [le_div_iff₀ hden_pos]
      have hR2_le : (R : ℝ) ^ 2 ≤ (X : ℝ) ^ ((2 : ℝ) / 5) := by
        calc (R : ℝ) ^ 2 ≤ ((X : ℝ) ^ ((1 : ℝ) / 5)) ^ (2 : ℕ) := pow_le_pow_left₀ (Nat.cast_nonneg _) hR_le_X5 2
          _ = (X : ℝ) ^ ((2 : ℝ) / 5) := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul hX_pos.le]; norm_num
      have hX_pow_le : (X : ℝ) ^ ((2 : ℝ) / 5) ≤ x ^ ((2 : ℝ) / 5) :=
        Real.rpow_le_rpow hX_pos.le hx (by norm_num)
      have hX20_x : (X : ℝ) ^ ((1 : ℝ) / 20) ≤ x ^ ((1 : ℝ) / 20) :=
        Real.rpow_le_rpow hX_pos.le hx (by norm_num)
      have hsqrt : Real.sqrt x = x ^ ((2 : ℝ) / 5) * x ^ ((1 : ℝ) / 20) * x ^ ((1 : ℝ) / 20) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx_pos, ← Real.rpow_add hx_pos]
        norm_num
      have hMWKB_nn : 0 ≤ (M * W : ℝ) * KB := by positivity
      have hMW_le : (M * W : ℝ) * KB ≤ x ^ ((1 : ℝ) / 20) := by linarith only [hX20_ge, hX20_x, hMWKB_nn]
      have hcast : ((M * W * R ^ 2 : ℕ) : ℝ) = (M * W : ℝ) * (R : ℝ) ^ 2 := by push_cast; ring
      rw [hcast, hsqrt]
      calc (M * W : ℝ) * (R : ℝ) ^ 2 * Real.log x ^ B
          ≤ (M * W : ℝ) * x ^ ((2 : ℝ) / 5) * (KB * x ^ ((1 : ℝ) / 20)) :=
            mul_le_mul (mul_le_mul_of_nonneg_left (le_trans hR2_le hX_pow_le) (by positivity))
              hlogB_le (by positivity) (by positivity)
        _ = x ^ ((2 : ℝ) / 5) * ((M * W : ℝ) * KB) * x ^ ((1 : ℝ) / 20) := by ring
        _ ≤ x ^ ((2 : ℝ) / 5) * x ^ ((1 : ℝ) / 20) * x ^ ((1 : ℝ) / 20) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hMW_le (by positivity)) (by positivity)
    exact (Nat.le_floor_iff (by positivity)).mpr hMWR2_le
  -- Q <= M * W * X + b'
  have hQ_le_fl1 : M * W * R ^ 2 ≤ M * W * X + b' := by
    have hR2_le_X : R ^ 2 ≤ X := by
      have h1 : (R : ℝ) ^ 2 ≤ (X : ℝ) ^ ((2 : ℝ) / 5) := by
        calc (R : ℝ) ^ 2 ≤ ((X : ℝ) ^ ((1 : ℝ) / 5)) ^ (2 : ℕ) := pow_le_pow_left₀ (Nat.cast_nonneg _) hR_le_X5 2
          _ = (X : ℝ) ^ ((2 : ℝ) / 5) := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul hX_pos.le]; norm_num
      have h2 : (X : ℝ) ^ ((2 : ℝ) / 5) ≤ (X : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      rw [Real.rpow_one] at h2
      exact_mod_cast le_trans h1 h2
    have : M * W * R ^ 2 ≤ M * W * X := Nat.mul_le_mul_left (M * W) hR2_le_X
    omega
  -- BV error bound (g)
  have hBV_err :
      (2 * Real.log (R : ℝ) + 2) ^ (6 * k) *
        Real.sqrt ((2 * Real.log (R : ℝ) + 1) ^ (9 * k ^ 2)) *
        (Real.sqrt (5 * C' * x2 ^ 2 * Real.log x2 / Real.log x2 ^ A_BV) +
          Real.sqrt (5 * C' * x1 ^ 2 * Real.log x1 / Real.log x1 ^ A_BV)) ≤
      (1 / 10 : ℝ) * ((W : ℝ) / (Nat.totient W : ℝ)) * (X : ℝ) *
        ((1 / 2 : ℝ) * scale) ^ 2 * ((I2 / 2) * scale) ^ (k - 1) := by
    have hsqrt_single : ∀ x : ℝ, (X : ℝ) ≤ x → x ≤ 3 * (M * W : ℝ) * (X : ℝ) →
        Real.sqrt (5 * C' * x ^ 2 * Real.log x / Real.log x ^ A_BV) ≤
          Real.sqrt (5 * C') * (3 * (M * W : ℝ) * (X : ℝ)) / Real.log (X : ℝ) ^ mBV := by
      intro x hx1 hx2
      have hlogx_ge : Real.log (X : ℝ) ≤ Real.log x := Real.log_le_log hX_pos hx1
      have hlogx_pos : 0 < Real.log x := by linarith
      have hdiv_eq : Real.log x / Real.log x ^ A_BV = 1 / (Real.log x ^ mBV) ^ 2 := by
        dsimp only [A_BV]
        rw [Real.rpow_natCast, pow_succ, mul_comm 2 mBV, pow_mul]
        have hne : Real.log x ≠ 0 := hlogx_pos.ne'
        have hne_m : Real.log x ^ mBV ≠ 0 := pow_ne_zero mBV hne
        field_simp
      have hrew : 5 * C' * x ^ 2 * Real.log x / Real.log x ^ A_BV =
          (5 * C') * (x / Real.log x ^ mBV) ^ 2 := by
        rw [mul_div_assoc, hdiv_eq, div_pow]; ring
      rw [hrew, Real.sqrt_mul (by positivity),
        Real.sqrt_sq (div_nonneg (lt_of_lt_of_le hX_pos hx1).le (pow_nonneg hlogx_pos.le _))]
      have hfrac : x / Real.log x ^ mBV ≤ (3 * (M * W : ℝ) * (X : ℝ)) / Real.log (X : ℝ) ^ mBV := by
        refine div_le_div₀ (by positivity) hx2 (pow_pos (by linarith) _) ?_
        exact pow_le_pow_left₀ (by linarith) hlogx_ge mBV
      calc Real.sqrt (5 * C') * (x / Real.log x ^ mBV)
          ≤ Real.sqrt (5 * C') * ((3 * (M * W : ℝ) * (X : ℝ)) / Real.log (X : ℝ) ^ mBV) :=
            mul_le_mul_of_nonneg_left hfrac (Real.sqrt_nonneg _)
        _ = Real.sqrt (5 * C') * (3 * (M * W : ℝ) * (X : ℝ)) / Real.log (X : ℝ) ^ mBV := by ring
    have hsq1 := hsqrt_single x1 hx1_geX (le_trans hx1_le_x2 hx2_le_3MWX)
    have hsq2 := hsqrt_single x2 (le_trans hx1_geX hx1_le_x2) hx2_le_3MWX
    have hfac1 : (2 * Real.log (R : ℝ) + 2) ^ (6 * k) ≤ (4 : ℝ) ^ (6 * k) * Real.log (X : ℝ) ^ (6 * k) := by
      have h1 : 2 * Real.log (R : ℝ) + 2 ≤ 4 * Real.log (X : ℝ) := by linarith
      calc (2 * Real.log (R : ℝ) + 2) ^ (6 * k)
          ≤ (4 * Real.log (X : ℝ)) ^ (6 * k) := pow_le_pow_left₀ (by linarith) h1 _
        _ = (4 : ℝ) ^ (6 * k) * Real.log (X : ℝ) ^ (6 * k) := mul_pow _ _ _
    have hfac2 : Real.sqrt ((2 * Real.log (R : ℝ) + 1) ^ (9 * k ^ 2)) ≤
        (4 : ℝ) ^ (5 * k ^ 2) * Real.log (X : ℝ) ^ (5 * k ^ 2) := by
      have h1 : 2 * Real.log (R : ℝ) + 1 ≤ 4 * Real.log (X : ℝ) := by linarith
      have h2 : (2 * Real.log (R : ℝ) + 1) ^ (9 * k ^ 2) ≤ (4 * Real.log (X : ℝ)) ^ (10 * k ^ 2) := by
        calc (2 * Real.log (R : ℝ) + 1) ^ (9 * k ^ 2)
            ≤ (4 * Real.log (X : ℝ)) ^ (9 * k ^ 2) := pow_le_pow_left₀ (by linarith) h1 _
          _ ≤ (4 * Real.log (X : ℝ)) ^ (10 * k ^ 2) :=
              pow_le_pow_right₀ (by linarith only [hlogX_ge10]) (Nat.mul_le_mul_right (k ^ 2) (by omega))
      have h3 : (4 * Real.log (X : ℝ)) ^ (10 * k ^ 2) = ((4 * Real.log (X : ℝ)) ^ (5 * k ^ 2)) ^ 2 := by
        rw [← pow_mul]; congr 1; ring
      calc Real.sqrt ((2 * Real.log (R : ℝ) + 1) ^ (9 * k ^ 2))
          ≤ Real.sqrt (((4 * Real.log (X : ℝ)) ^ (5 * k ^ 2)) ^ 2) := Real.sqrt_le_sqrt (h3 ▸ h2)
        _ = (4 * Real.log (X : ℝ)) ^ (5 * k ^ 2) := Real.sqrt_sq (by positivity)
        _ = (4 : ℝ) ^ (5 * k ^ 2) * Real.log (X : ℝ) ^ (5 * k ^ 2) := mul_pow _ _ _
    have hpow_cancel : Real.log (X : ℝ) ^ (6 * k) * Real.log (X : ℝ) ^ (5 * k ^ 2) / Real.log (X : ℝ) ^ mBV ≤
        1 / Real.log (X : ℝ) := by
      have hlogX_pos : 0 < Real.log (X : ℝ) := by linarith
      rw [← pow_add]
      have hmBV_eq : mBV = (6 * k + 5 * k ^ 2) + 10 := by dsimp only [mBV]; ring
      conv_lhs => arg 2; rw [hmBV_eq, pow_add]
      have hne : Real.log (X : ℝ) ^ (6 * k + 5 * k ^ 2) ≠ 0 := pow_ne_zero _ hlogX_pos.ne'
      have h10 : Real.log (X : ℝ) ≤ Real.log (X : ℝ) ^ 10 := by
        calc Real.log (X : ℝ) = Real.log (X : ℝ) ^ 1 := (pow_one _).symm
          _ ≤ Real.log (X : ℝ) ^ 10 := pow_le_pow_right₀ (by linarith) (by omega)
      have hsimp : Real.log (X : ℝ) ^ (6 * k + 5 * k ^ 2) /
          (Real.log (X : ℝ) ^ (6 * k + 5 * k ^ 2) * Real.log (X : ℝ) ^ 10) = 1 / Real.log (X : ℝ) ^ 10 := by
        field_simp
      rw [hsimp]
      exact one_div_le_one_div_of_le hlogX_pos h10
    have hW_ge1 : (1 : ℝ) ≤ (W : ℝ) / (Nat.totient W : ℝ) := by
      rw [one_le_div (Nat.cast_pos.mpr (Nat.totient_pos.mpr hW))]
      exact_mod_cast Nat.totient_le W
    have hrhs_ge : (1 / 10 : ℝ) * (X : ℝ) ≤
        (1 / 10 : ℝ) * ((W : ℝ) / (Nat.totient W : ℝ)) * (X : ℝ) *
          ((1 / 2 : ℝ) * scale) ^ 2 * ((I2 / 2) * scale) ^ (k - 1) := by
      have hsc1 : (1 : ℝ) ≤ ((1 / 2 : ℝ) * scale) ^ 2 := one_le_pow₀ hscale_half
      have hsc2 : (1 : ℝ) ≤ ((I2 / 2) * scale) ^ (k - 1) := one_le_pow₀ hscale_I2
      have hprod : (1 : ℝ) ≤ ((W : ℝ) / (Nat.totient W : ℝ)) * ((1 / 2 : ℝ) * scale) ^ 2 *
          ((I2 / 2) * scale) ^ (k - 1) := by
        calc (1 : ℝ) = 1 * 1 * 1 := by ring
          _ ≤ ((W : ℝ) / (Nat.totient W : ℝ)) * ((1 / 2 : ℝ) * scale) ^ 2 *
              ((I2 / 2) * scale) ^ (k - 1) :=
            mul_le_mul (mul_le_mul hW_ge1 hsc1 (by norm_num) (by positivity)) hsc2 (by norm_num) (by positivity)
      calc (1 / 10 : ℝ) * (X : ℝ)
          = (1 / 10 : ℝ) * (X : ℝ) * 1 := (mul_one _).symm
        _ ≤ (1 / 10 : ℝ) * (X : ℝ) *
            (((W : ℝ) / (Nat.totient W : ℝ)) * ((1 / 2 : ℝ) * scale) ^ 2 *
              ((I2 / 2) * scale) ^ (k - 1)) := mul_le_mul_of_nonneg_left hprod (by positivity)
        _ = _ := by ring
    have hlhs_le :
        (2 * Real.log (R : ℝ) + 2) ^ (6 * k) *
          Real.sqrt ((2 * Real.log (R : ℝ) + 1) ^ (9 * k ^ 2)) *
          (Real.sqrt (5 * C' * x2 ^ 2 * Real.log x2 / Real.log x2 ^ A_BV) +
            Real.sqrt (5 * C' * x1 ^ 2 * Real.log x1 / Real.log x1 ^ A_BV)) ≤
        (1 / 10 : ℝ) * (X : ℝ) := by
      have hsum_sq :
          Real.sqrt (5 * C' * x2 ^ 2 * Real.log x2 / Real.log x2 ^ A_BV) +
            Real.sqrt (5 * C' * x1 ^ 2 * Real.log x1 / Real.log x1 ^ A_BV) ≤
          2 * Real.sqrt (5 * C') * (3 * (M * W : ℝ) * (X : ℝ)) / Real.log (X : ℝ) ^ mBV := by
        have heq : Real.sqrt (5 * C') * (3 * (M * W : ℝ) * (X : ℝ)) / Real.log (X : ℝ) ^ mBV +
            Real.sqrt (5 * C') * (3 * (M * W : ℝ) * (X : ℝ)) / Real.log (X : ℝ) ^ mBV =
            2 * Real.sqrt (5 * C') * (3 * (M * W : ℝ) * (X : ℝ)) / Real.log (X : ℝ) ^ mBV := by ring
        linarith only [hsq1, hsq2, heq]
      calc (2 * Real.log (R : ℝ) + 2) ^ (6 * k) *
            Real.sqrt ((2 * Real.log (R : ℝ) + 1) ^ (9 * k ^ 2)) *
            (Real.sqrt (5 * C' * x2 ^ 2 * Real.log x2 / Real.log x2 ^ A_BV) +
              Real.sqrt (5 * C' * x1 ^ 2 * Real.log x1 / Real.log x1 ^ A_BV))
          ≤ ((4 : ℝ) ^ (6 * k) * Real.log (X : ℝ) ^ (6 * k)) *
            ((4 : ℝ) ^ (5 * k ^ 2) * Real.log (X : ℝ) ^ (5 * k ^ 2)) *
            (2 * Real.sqrt (5 * C') * (3 * (M * W : ℝ) * (X : ℝ)) / Real.log (X : ℝ) ^ mBV) :=
            mul_le_mul (mul_le_mul hfac1 hfac2 (Real.sqrt_nonneg _) (by positivity)) hsum_sq (by positivity) (by positivity)
        _ = (1 / 10 : ℝ) * (X : ℝ) * K_BV *
            (Real.log (X : ℝ) ^ (6 * k) * Real.log (X : ℝ) ^ (5 * k ^ 2) / Real.log (X : ℝ) ^ mBV) := by
            dsimp only [K_BV]; ring
        _ ≤ (1 / 10 : ℝ) * (X : ℝ) * K_BV * (1 / Real.log (X : ℝ)) :=
            mul_le_mul_of_nonneg_left hpow_cancel (by dsimp only [K_BV]; positivity)
        _ = (1 / 10 : ℝ) * (X : ℝ) * (K_BV / Real.log (X : ℝ)) := by ring
        _ ≤ (1 / 10 : ℝ) * (X : ℝ) * 1 := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            rw [div_le_one (by linarith)]
            exact hKBV_le
        _ = (1 / 10 : ℝ) * (X : ℝ) := mul_one _
    exact le_trans hlhs_le hrhs_ge
  exact ⟨hx1_ge3, hQ_bound_fn x1 hx1_geX, hQ_bound_fn x2 (le_trans hx1_geX hx1_le_x2), hQ_le_fl1, hBV_err⟩

end Erdos6MaynardTao

set_option maxHeartbeats 800000 in
theorem maynard_tao_from_bv :
  (∀ A : ℝ, 0 < A → ∃ B C : ℝ, ∀ x : ℝ, 2 ≤ x → ∀ a : ℕ → ℕ, (∀ q, Nat.Coprime (a q) q) →
    ∑ q ∈ Finset.Icc 1 ⌊Real.sqrt x / Real.log x ^ B⌋₊,
      |∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter (fun p => p.Prime ∧ p % q = a q % q),
          Real.log p - x / (Nat.totient q : ℝ)| ≤ C * x / Real.log x ^ A) →
  ∀ r : ℕ, ∃ k : ℕ, ∀ (H : Finset ℕ) (M b : ℕ), k ≤ H.card → 0 < M →
    (∀ p, p.Prime → ∃ x, ∀ a ∈ H, ¬ p ∣ M * x + b + a) →
    ∀ N : ℕ, ∃ x, N < x ∧ r ≤ (H.filter fun a => (M * x + b + a).Prime).card := by
  classical
  intro hBV r
  by_cases hr0 : r = 0
  · subst hr0
    exact ⟨0, fun H M b _ _ _ N => ⟨N + 1, Nat.lt_succ_self N, Nat.zero_le _⟩⟩
  have hr1 : 1 ≤ r := Nat.pos_of_ne_zero hr0
  -- Choose fixed parameters A, T, I2, eps, L, k depending ONLY on r
  let A : ℝ := 30 * (r : ℝ) + 30
  have hA60 : (60 : ℝ) ≤ A := by
    have : (1 : ℝ) ≤ r := by exact_mod_cast hr1
    dsimp only [A]; linarith
  have hA_pos : 0 < A := by linarith
  let T : ℝ := (Real.exp A - 1) / A
  have hT_pos : 0 < T := div_pos (by linarith [Real.add_one_lt_exp hA_pos.ne']) hA_pos
  let I2 : ℝ := (1 - Real.exp (-A)) / A
  have hexp_inv : Real.exp (-A) ≤ 1 / (10 * A) := by
    have h3 := Real.sum_le_exp_of_nonneg hA_pos.le 3
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_one,
      Nat.cast_mul, pow_zero, pow_one, div_one, zero_add] at h3
    have h10A : 10 * A ≤ Real.exp A := by nlinarith
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (by positivity) h10A
  have hI2_low : 9 / (10 * A) ≤ I2 := by
    dsimp only [I2]
    have h1 : 1 - 1 / (10 * A) ≤ 1 - Real.exp (-A) := by linarith
    have h2 : (9 / 10 : ℝ) ≤ 1 - 1 / (10 * A) := by
      have : 1 / (10 * A) ≤ 1 / 10 := one_div_le_one_div_of_le (by norm_num) (by linarith)
      linarith
    have h3 : (9 / 10 : ℝ) / A ≤ (1 - Real.exp (-A)) / A := div_le_div_of_nonneg_right (by linarith) hA_pos.le
    have h4 : (9 / 10 : ℝ) / A = 9 / (10 * A) := by ring
    linarith
  have hI2_high : I2 ≤ 1 / A := by
    dsimp only [I2]
    exact div_le_div_of_nonneg_right (by linarith [Real.exp_pos (-A)]) hA_pos.le
  have hI2_pos : 0 < I2 := lt_of_lt_of_le (by positivity) hI2_low
  let eps : ℝ := I2 / (200 * A)
  have heps_pos : 0 < eps := div_pos hI2_pos (by positivity)
  obtain ⟨L, hL1, hTL_le⟩ : ∃ L : ℕ, 1 ≤ L ∧ T / (L : ℝ) ≤ eps := by
    refine ⟨Nat.ceil (T / eps) + 1, by omega, ?_⟩
    have hL_ge : T / eps ≤ ((Nat.ceil (T / eps) + 1 : ℕ) : ℝ) := by
      push_cast; linarith [Nat.le_ceil (T / eps)]
    rw [div_le_iff₀ (Nat.cast_pos.mpr (by omega : 0 < Nat.ceil (T / eps) + 1)), mul_comm,
      ← div_le_iff₀ heps_pos]
    exact hL_ge
  obtain ⟨k, hk2, hk_ge⟩ : ∃ k : ℕ, 2 ≤ k ∧ 1200 * A * T ≤ (k : ℝ) :=
    ⟨Nat.ceil (1200 * A * T) + 2, by omega, by push_cast; linarith [Nat.le_ceil (1200 * A * T)]⟩
  have hTk : T < (k : ℝ) := by nlinarith
  -- Output k and introduce H, M, b, admissibility, N
  refine ⟨k, fun H M b hHcard hM hadm N => ?_⟩
  -- Pick subset H' of H of exact size k and enumerate it by h : Fin k -> N
  obtain ⟨H', hH'sub, hH'card⟩ := Finset.exists_subset_card_eq hHcard
  let e : Fin k ≃ H' := (Fintype.equivFinOfCardEq (by rw [Fintype.card_coe, hH'card])).symm
  let h : Fin k → ℕ := fun i => (e i).1
  have h_inj : Function.Injective h := fun i j hEq => e.injective (Subtype.ext hEq)
  have hhH : ∀ i, h i ∈ H := fun i => hH'sub (e i).2
  -- Choose fixed D0 depending ONLY on k, M, H', A, T, I2 (NOT on X!)
  let hmax : ℕ := Finset.univ.sup h
  obtain ⟨D0, hMD, hhD, hD_quad, hD_M1, hD_M2, hD_cheb⟩ :
      ∃ D0 : ℕ, M ≤ D0 ∧ (∀ i, h i ≤ D0) ∧ 2 * k ^ 2 + 10 ≤ D0 ∧
        20 * (k : ℝ) ^ 2 * (4 * T / I2) ^ k + 3 ≤ (D0 : ℝ) ∧
        160 * (k : ℝ) ^ 2 * (8 * T / I2) ^ (k - 1) + 4 ≤ (D0 : ℝ) ∧
        30 * (k : ℝ) ^ 2 + 3 ≤ (D0 : ℝ) := by
    let D0_val : ℕ := max M (max hmax (max (2 * k ^ 2 + 10)
      (max (Nat.ceil (20 * (k : ℝ) ^ 2 * (4 * T / I2) ^ k) + 3)
        (max (Nat.ceil (160 * (k : ℝ) ^ 2 * (8 * T / I2) ^ (k - 1)) + 4)
          (30 * k ^ 2 + 3)))))
    refine ⟨D0_val, le_max_left _ _,
      fun i => le_trans (Finset.le_sup (f := h) (Finset.mem_univ i)) (le_trans (le_max_left _ _) (le_max_right _ _)),
      le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _)), ?_, ?_, ?_⟩
    · have h1 : Nat.ceil (20 * (k : ℝ) ^ 2 * (4 * T / I2) ^ k) + 3 ≤ D0_val :=
        le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))
      have h2 : ((Nat.ceil (20 * (k : ℝ) ^ 2 * (4 * T / I2) ^ k) + 3 : ℕ) : ℝ) ≤ (D0_val : ℝ) := Nat.cast_le.mpr h1
      push_cast at h2; linarith [Nat.le_ceil (20 * (k : ℝ) ^ 2 * (4 * T / I2) ^ k)]
    · have h1 : Nat.ceil (160 * (k : ℝ) ^ 2 * (8 * T / I2) ^ (k - 1)) + 4 ≤ D0_val :=
        le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
          (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))))
      have h2 : ((Nat.ceil (160 * (k : ℝ) ^ 2 * (8 * T / I2) ^ (k - 1)) + 4 : ℕ) : ℝ) ≤ (D0_val : ℝ) := Nat.cast_le.mpr h1
      push_cast at h2; linarith [Nat.le_ceil (160 * (k : ℝ) ^ 2 * (8 * T / I2) ^ (k - 1))]
    · have h1 : 30 * k ^ 2 + 3 ≤ D0_val :=
        le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
          (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))))
      exact_mod_cast h1
  -- Fixed primorial W, admissible shift v0, 1D Mertens constant C_W, and BV constants B, C
  let W : ℕ := Erdos6MaynardTao.primorial D0
  have hW_pos : 0 < W := Erdos6MaynardTao.primorial_pos D0
  obtain ⟨v0, hv0⟩ := Erdos6MaynardTao.exists_admissible_shift D0 M b H hadm
  have hcop : ∀ i, Nat.Coprime (M * v0 + b + h i) W := fun i => hv0 (h i) (hhH i)
  obtain ⟨C_W, hCW_nn, hMertens⟩ := Erdos6MaynardTao.mertens_1d hW_pos
  let mBV : ℕ := 5 * k ^ 2 + 6 * k + 10
  let A_BV : ℝ := ((2 * mBV + 1 : ℕ) : ℝ)
  have hABV_pos : 0 < A_BV := by dsimp only [A_BV, mBV]; positivity
  obtain ⟨B, C_raw, hBV_inst⟩ := hBV A_BV hABV_pos
  let C' : ℝ := max C_raw 0
  have hC'_nn : 0 ≤ C' := le_max_right _ _
  have hBV' : ∀ x : ℝ, 2 ≤ x → ∀ a : ℕ → ℕ, (∀ q, Nat.Coprime (a q) q) →
      ∑ q ∈ Finset.Icc 1 ⌊Real.sqrt x / Real.log x ^ B⌋₊,
        |Erdos6MaynardTao.theta x q (a q) - x / (Nat.totient q : ℝ)| ≤ C' * x / Real.log x ^ A_BV := by
    intro x hx a ha
    have h1 := hBV_inst x hx a ha
    have hlog_pos : 0 < Real.log x := Real.log_pos (by linarith)
    have h2 : C_raw * x / Real.log x ^ A_BV ≤ C' * x / Real.log x ^ A_BV :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith))
        (Real.rpow_pos_of_pos hlog_pos A_BV).le
    exact le_trans h1 h2
  -- Choose sufficiently large X
  let Bmax : ℕ := M * v0 + b + hmax
  obtain ⟨X, hNX, hR2, hRX, hU1, hUR, hscale_half, hscale_I2, hlog_max, hL_CW, hCW_le, hS1_err, hBV_all⟩ :=
    Erdos6MaynardTao.exists_large_X_params (Bmax := Bmax) (B := B) (C' := C') (T := T) (C_W := C_W)
      (eps := eps) (I2 := I2) hk2 hM hW_pos hL1 hC'_nn hT_pos hTk hCW_nn heps_pos hI2_pos (N := N)
  let R : ℕ := ⌊(X : ℝ) ^ ((1 : ℝ) / 5)⌋₊
  let U : ℕ := ⌊(R : ℝ) ^ (T / (k : ℝ))⌋₊
  let cW : ℝ := (Nat.totient W : ℝ) / (W : ℝ)
  let scale : ℝ := cW * Real.log (R : ℝ) / (k : ℝ)
  have hcW_pos : 0 < cW := div_pos (Nat.cast_pos.mpr (Nat.totient_pos.mpr hW_pos)) (Nat.cast_pos.mpr hW_pos)
  have hlogR_pos : 0 < Real.log (R : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < R))
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr (by omega)
  have hscale_pos : 0 < scale := by dsimp only [scale]; positivity
  -- Define SU, MU, Z1, Z2 and verify Riemann + Mertens bounds
  let S_U := (Finset.Icc 1 U).filter (fun s => Squarefree s ∧ Nat.Coprime s W)
  let M_U : ℝ := ∑ s ∈ S_U, (1 / (Nat.totient s : ℝ))
  let Z1 : ℝ := ∑ s ∈ S_U, Erdos6MaynardTao.gWeight A k R s / (Nat.totient s : ℝ)
  let Z2 : ℝ := ∑ s ∈ S_U, (Erdos6MaynardTao.gWeight A k R s) ^ 2 / (Nat.totient s : ℝ)
  have hU_pow : (U : ℝ) ≤ (R : ℝ) ^ (T / (k : ℝ)) := Nat.floor_le (by positivity)
  have hZ1_riem := Erdos6MaynardTao.riemann_block_approx (D0 := D0) (k := k) (R := R) (U := U) (L := L)
    hT_pos (by omega) hR2 hL1 hCW_nn rfl hMertens
    (fun t => 1 / (1 + A * t)) (fun t ht => by positivity)
    (fun t ht => by rw [div_le_one (by nlinarith only [hA_pos, ht])]; nlinarith only [hA_pos, ht])
    (fun s t hs hst => div_le_div_of_nonneg_left (by norm_num) (by nlinarith only [hA_pos, hs])
      (by nlinarith only [hA_pos, hst]))
  have hZ2_riem := Erdos6MaynardTao.riemann_block_approx (D0 := D0) (k := k) (R := R) (U := U) (L := L)
    hT_pos (by omega) hR2 hL1 hCW_nn rfl hMertens
    (fun t => 1 / (1 + A * t) ^ 2) (fun t ht => by positivity)
    (fun t ht => by
      have hge1 : 1 ≤ 1 + A * t := by nlinarith only [hA_pos, ht]
      rw [div_le_one (sq_pos_of_pos (by linarith only [hge1]))]; nlinarith only [hge1])
    (fun s t hs hst => div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos (by nlinarith only [hA_pos, hs]))
      (pow_le_pow_left₀ (by nlinarith only [hA_pos, hs]) (by nlinarith only [hA_pos, hst]) 2))
  have hg1_bd := Erdos6MaynardTao.riemann_sum_g1_bounds hA_pos hL1
  have hg2_bd := Erdos6MaynardTao.riemann_sum_g2_bounds hA_pos hL1
  have hZ1_bounds : (1 - 2 * eps) * scale ≤ Z1 ∧ Z1 ≤ (1 + 2 * eps) * scale := by
    have hZ1_eq : Z1 = ∑ s ∈ S_U, (1 / (1 + A * Erdos6MaynardTao.tVal k R s)) / (Nat.totient s : ℝ) := rfl
    rw [hZ1_eq]
    constructor
    · have h1 := hZ1_riem.1
      have h2 := mul_le_mul_of_nonneg_left (le_trans (by linarith only [hTL_le] : 1 - eps ≤ 1 - T / (L : ℝ)) hg1_bd.1) hscale_pos.le
      linarith only [h1, h2, hL_CW]
    · have h1 := hZ1_riem.2
      have h2 := mul_le_mul_of_nonneg_left (le_trans hg1_bd.2 (by linarith only [hTL_le] : 1 + T / (L : ℝ) ≤ 1 + eps)) hscale_pos.le
      linarith only [h1, h2, hL_CW]
  have hZ2_bounds : (I2 - 2 * eps) * scale ≤ Z2 ∧ Z2 ≤ (I2 + 2 * eps) * scale := by
    have hZ2_eq : Z2 = ∑ s ∈ S_U, (1 / (1 + A * Erdos6MaynardTao.tVal k R s) ^ 2) / (Nat.totient s : ℝ) := by
      refine Finset.sum_congr rfl fun s _ => by unfold Erdos6MaynardTao.gWeight; rw [div_pow, one_pow]
    rw [hZ2_eq]
    constructor
    · have h1 := hZ2_riem.1
      have h2 := mul_le_mul_of_nonneg_left (le_trans (by linarith only [hTL_le] : I2 - eps ≤ I2 - T / (L : ℝ)) hg2_bd.1) hscale_pos.le
      linarith only [h1, h2, hL_CW]
    · have h1 := hZ2_riem.2
      have h2 := mul_le_mul_of_nonneg_left (le_trans hg2_bd.2 (by linarith only [hTL_le] : I2 + T / (L : ℝ) ≤ I2 + eps)) hscale_pos.le
      linarith only [h1, h2, hL_CW]
  have hMU_le : M_U ≤ 2 * T * scale := by
    have hY_ge1 : 1 ≤ (R : ℝ) ^ (T / (k : ℝ)) :=
      Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ R)) (by positivity)
    have hM := (abs_le.mp (hMertens ((R : ℝ) ^ (T / (k : ℝ))) hY_ge1)).2
    have hlogY : cW * Real.log ((R : ℝ) ^ (T / (k : ℝ))) = T * scale := by
      rw [Real.log_rpow (Nat.cast_pos.mpr (by omega : 0 < R))]
      dsimp only [scale]; ring
    change M_U - cW * Real.log ((R : ℝ) ^ (T / (k : ℝ))) ≤ C_W at hM
    linarith only [hM, hlogY, hCW_le]
  have hMU_nn : 0 ≤ M_U := Finset.sum_nonneg fun _ _ => by positivity
  -- Simplified numeric bounds on Z1, Z2, mu, delta
  have heps_le_I2 : 2 * eps ≤ I2 / 200 := by
    dsimp only [eps]
    have : 2 * (I2 / (200 * A)) = (I2 / 200) * (2 / A) := by ring
    rw [this]
    have h2A : 2 / A ≤ 1 := by rw [div_le_one hA_pos]; linarith only [hA60]
    exact mul_le_of_le_one_right (by positivity) h2A
  have heps_le_half : 2 * eps ≤ 1 / 10 := by
    have hI2_le1 : I2 ≤ 1 := le_trans hI2_high (by rw [div_le_one hA_pos]; linarith only [hA60])
    linarith only [heps_le_I2, hI2_le1]
  have hZ1_low : (9 / 10 : ℝ) * scale ≤ Z1 :=
    le_trans (mul_le_mul_of_nonneg_right (by linarith only [heps_le_half]) hscale_pos.le) hZ1_bounds.1
  have hZ1_pos : 0 < Z1 := lt_of_lt_of_le (by positivity) hZ1_low
  have hZ2_low : (I2 / 2) * scale ≤ Z2 :=
    le_trans (mul_le_mul_of_nonneg_right (by linarith only [heps_le_I2, hI2_pos]) hscale_pos.le) hZ2_bounds.1
  have hZ2_high : Z2 ≤ (11 / 10 : ℝ) * I2 * scale :=
    le_trans hZ2_bounds.2 (by
      have h1 : I2 + 2 * eps ≤ (11 / 10 : ℝ) * I2 := by linarith only [heps_le_I2, hI2_pos]
      exact mul_le_mul_of_nonneg_right h1 hscale_pos.le)
  have hZ2_pos : 0 < Z2 := lt_of_lt_of_le (by positivity) hZ2_low
  -- Bound 1 - mu >= 1 / (3 * A) and delta >= k / (6 * A)
  let mu : ℝ := (Z1 - Z2) / (A * Z2)
  let delta : ℝ := (k : ℝ) - T - ((k - 1 : ℕ) : ℝ) * mu
  have hmu_nonneg : 0 ≤ mu := by
    dsimp only [mu]
    refine div_nonneg ?_ (mul_nonneg hA_pos.le hZ2_pos.le)
    have hI2_small : (11 / 10 : ℝ) * I2 ≤ 1 / 2 := by
      have : I2 ≤ 1 / 60 := le_trans hI2_high (one_div_le_one_div_of_le (by norm_num) hA60)
      linarith only [this]
    have hZ2_half : Z2 ≤ (1 / 2 : ℝ) * scale :=
      le_trans hZ2_high (mul_le_mul_of_nonneg_right hI2_small hscale_pos.le)
    linarith only [hZ1_low, hZ2_half, hscale_pos]
  have hone_sub_mu : 1 / (3 * A) ≤ 1 - mu := by
    have hnum_eq : 1 - mu = ((A + 1) * Z2 - Z1) / (A * Z2) := by
      dsimp only [mu]; field_simp; ring
    rw [hnum_eq]
    have hAI2 : A * I2 = 1 - Real.exp (-A) := by dsimp only [I2]; field_simp
    have hnum_low : (1 / (2 * A)) * scale ≤ (A + 1) * Z2 - Z1 := by
      have h1 : (A + 1) * ((I2 - 2 * eps) * scale) - (1 + 2 * eps) * scale ≤ (A + 1) * Z2 - Z1 := by
        have hm := mul_le_mul_of_nonneg_left hZ2_bounds.1 (by linarith only [hA_pos] : (0 : ℝ) ≤ A + 1)
        linarith only [hm, hZ1_bounds.2]
      have h2 : (2 * A + 4) * eps ≤ 3 / (200 * A) := by
        have heq : (2 * A + 4) * eps = ((2 * A + 4) / (200 * A)) * I2 := by dsimp only [eps]; ring
        rw [heq]
        have hf : (2 * A + 4) / (200 * A) ≤ 3 / 200 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith only [hA60]
        exact le_trans (mul_le_mul hf hI2_high hI2_pos.le (by norm_num))
          (by rw [mul_one_div]; exact le_of_eq (by ring))
      have h3 : 1 / (2 * A) ≤ (A + 1) * (I2 - 2 * eps) - (1 + 2 * eps) := by
        have heq : (A + 1) * (I2 - 2 * eps) - (1 + 2 * eps) =
            (A * I2 + I2 - 1) - (2 * A + 4) * eps := by ring
        rw [heq, hAI2]
        have hsub : 9 / (10 * A) - 1 / (10 * A) = 8 / (10 * A) := by ring
        have h8 : 8 / (10 * A) ≤ 1 - Real.exp (-A) + I2 - 1 := by linarith only [hexp_inv, hI2_low, hsub]
        have hgap : 1 / (2 * A) + 3 / (200 * A) ≤ 8 / (10 * A) := by
          have : 8 / (10 * A) - (1 / (2 * A) + 3 / (200 * A)) = 57 / (200 * A) := by ring
          linarith only [this, show (0 : ℝ) ≤ 57 / (200 * A) by positivity]
        linarith only [h2, h8, hgap]
      have h4 := mul_le_mul_of_nonneg_right h3 hscale_pos.le
      have heq4 : ((A + 1) * (I2 - 2 * eps) - (1 + 2 * eps)) * scale =
          (A + 1) * ((I2 - 2 * eps) * scale) - (1 + 2 * eps) * scale := by ring
      linarith only [h1, h4, heq4]
    have hden_high : A * Z2 ≤ (11 / 10 : ℝ) * scale := by
      have hAI2_le1 : A * I2 ≤ 1 := by linarith only [hAI2, Real.exp_pos (-A)]
      have h1 : A * Z2 ≤ A * ((11 / 10 : ℝ) * I2 * scale) := mul_le_mul_of_nonneg_left hZ2_high hA_pos.le
      have h2 : A * ((11 / 10 : ℝ) * I2 * scale) = (A * I2) * ((11 / 10 : ℝ) * scale) := by ring
      have h3 : (A * I2) * ((11 / 10 : ℝ) * scale) ≤ 1 * ((11 / 10 : ℝ) * scale) :=
        mul_le_mul_of_nonneg_right hAI2_le1 (by positivity)
      linarith only [h1, h2, h3]
    calc 1 / (3 * A) ≤ ((1 / (2 * A)) * scale) / ((11 / 10 : ℝ) * scale) := by
          have heq : ((1 / (2 * A)) * scale) / ((11 / 10 : ℝ) * scale) = 5 / (11 * A) := by
            field_simp; ring
          rw [heq]
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          linarith only [hA_pos]
      _ ≤ ((A + 1) * Z2 - Z1) / (A * Z2) :=
          div_le_div₀ (le_trans (by positivity) hnum_low) hnum_low (mul_pos hA_pos hZ2_pos) hden_high
  have hdelta_low : (k : ℝ) / (6 * A) ≤ delta := by
    have hk1_cast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
    dsimp only [delta]
    rw [hk1_cast]
    have heq : (k : ℝ) - T - ((k : ℝ) - 1) * mu = (k : ℝ) * (1 - mu) + mu - T := by ring
    rw [heq]
    have h1 : (k : ℝ) / (3 * A) ≤ (k : ℝ) * (1 - mu) := by
      have := mul_le_mul_of_nonneg_left hone_sub_mu hk_pos.le
      linarith only [this, show (k : ℝ) * (1 / (3 * A)) = (k : ℝ) / (3 * A) by ring]
    have h2 : T ≤ (k : ℝ) / (6 * A) := by
      rw [le_div_iff₀ (by positivity)]; linarith only [hk_ge, hA_pos, hT_pos]
    have h3 : (k : ℝ) / (3 * A) - (k : ℝ) / (6 * A) = (k : ℝ) / (6 * A) := by ring
    linarith only [h1, h2, h3, hmu_nonneg]
  have hdelta_pos : 0 < delta := lt_of_lt_of_le (by positivity) hdelta_low
  -- Bound the Chebyshev error <= 1/5
  have hcheb_le : ((k - 1 : ℕ) : ℝ) * (M_U / (A ^ 2 * Z2)) / delta ^ 2 ≤ 1 / 5 := by
    have hZ2_A : (1 / (3 * A)) * scale ≤ Z2 := by
      have h1 : 1 / (3 * A) ≤ I2 / 2 := by
        have h9 : 9 / (20 * A) ≤ I2 / 2 := by
          have : (9 / (10 * A)) / 2 = 9 / (20 * A) := by ring
          linarith only [hI2_low, this]
        have h39 : 1 / (3 * A) ≤ 9 / (20 * A) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith only [hA_pos]
        linarith only [h9, h39]
      exact le_trans (mul_le_mul_of_nonneg_right h1 hscale_pos.le) hZ2_low
    have hMU_div : M_U / (A ^ 2 * Z2) ≤ 6 * T / A := by
      calc M_U / (A ^ 2 * Z2)
          ≤ (2 * T * scale) / (A ^ 2 * ((1 / (3 * A)) * scale)) :=
            div_le_div₀ (by positivity) hMU_le (by positivity)
              (mul_le_mul_of_nonneg_left hZ2_A (sq_nonneg A))
        _ = 6 * T / A := by field_simp; ring
    have hdel2 : ((k : ℝ) / (6 * A)) ^ 2 ≤ delta ^ 2 :=
      pow_le_pow_left₀ (by positivity) hdelta_low 2
    have hk_sub : ((k - 1 : ℕ) : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr (Nat.sub_le k 1)
    calc ((k - 1 : ℕ) : ℝ) * (M_U / (A ^ 2 * Z2)) / delta ^ 2
        ≤ ((k : ℝ) * (6 * T / A)) / ((k : ℝ) / (6 * A)) ^ 2 :=
          div_le_div₀ (by positivity) (mul_le_mul hk_sub hMU_div (by positivity) hk_pos.le)
            (sq_pos_of_pos (by positivity)) hdel2
      _ = 216 * A * T / (k : ℝ) := by field_simp; ring
      _ ≤ 1 / 5 := by rw [div_le_div_iff₀ hk_pos (by norm_num)]; linarith only [hk_ge, hA_pos, hT_pos]
  -- Define L, y, S1, S2 and combine all bounds
  let Lform : Fin k → ℕ → ℕ := fun i n => M * W * n + (M * v0 + b + h i)
  let y : (Fin k → ℕ) → ℝ := Erdos6MaynardTao.yWeight A k D0 R U
  have hy_bd := Erdos6MaynardTao.yWeight_bounds (k := k) (D0 := D0) (U := U) hA_pos hR2
  let weight : ℕ → ℝ := fun n =>
    ∑ d ∈ (Erdos6MaynardTao.validSet k W R).filter (fun d => ∀ i, d i ∣ Lform i n),
      Erdos6MaynardTao.lambdaOfY k W R y d
  let S1 : ℝ := ∑ n ∈ Finset.Ioc X (2 * X), (weight n) ^ 2
  let S2 : ℝ := ∑ idx : Fin k, ∑ n ∈ Finset.Ioc X (2 * X),
    (if (Lform idx n).Prime then Real.log (Lform idx n : ℝ) else 0) * (weight n) ^ 2
  -- Upper bound S1 <= (6/5) * X * Z2^k
  have hS1_upper : S1 ≤ (6 / 5 : ℝ) * (X : ℝ) * Z2 ^ k := by
    have hstep1 := Erdos6MaynardTao.S1_le_mul_M1_add_err (R := R) (X := X) hM hMD (by omega) h h_inj hhD hcop y
      hy_bd.1 hy_bd.2.1
    have hstep2 := Erdos6MaynardTao.M1_le_T1_add_err (R := R) (U := U) hD_quad (by omega) hUR y hy_bd.1 hy_bd.2.1 hy_bd.2.2.1
    have hstep3 := Erdos6MaynardTao.T1_le_Z2_pow (k := k) (D0 := D0) (R := R) (U := U) hA_pos hR2
    have hMU_Z2 : M_U ≤ (4 * T / I2) * Z2 := by
      have h1 : (4 * T / I2) * ((I2 / 2) * scale) = 2 * T * scale := by field_simp; ring
      have h2 := mul_le_mul_of_nonneg_left hZ2_low (by positivity : (0 : ℝ) ≤ 4 * T / I2)
      linarith only [hMU_le, h1, h2]
    have hM1_err : (2 * (k : ℝ) ^ 2 / ((D0 : ℝ) - 2)) * M_U ^ k ≤ (1 / 10 : ℝ) * Z2 ^ k := by
      have hD2_pos : (0 : ℝ) < (D0 : ℝ) - 2 := by
        have : (10 : ℝ) ≤ D0 := by exact_mod_cast (by omega : 10 ≤ D0)
        linarith only [this]
      have hpow : M_U ^ k ≤ (4 * T / I2) ^ k * Z2 ^ k := by
        rw [← mul_pow]; exact pow_le_pow_left₀ hMU_nn hMU_Z2 k
      have hfrac : (2 * (k : ℝ) ^ 2 / ((D0 : ℝ) - 2)) * (4 * T / I2) ^ k ≤ 1 / 10 := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ hD2_pos (by norm_num)]
        linarith only [hD_M1]
      calc (2 * (k : ℝ) ^ 2 / ((D0 : ℝ) - 2)) * M_U ^ k
          ≤ (2 * (k : ℝ) ^ 2 / ((D0 : ℝ) - 2)) * ((4 * T / I2) ^ k * Z2 ^ k) :=
            mul_le_mul_of_nonneg_left hpow (by positivity)
        _ = ((2 * (k : ℝ) ^ 2 / ((D0 : ℝ) - 2)) * (4 * T / I2) ^ k) * Z2 ^ k := by ring
        _ ≤ (1 / 10 : ℝ) * Z2 ^ k := mul_le_mul_of_nonneg_right hfrac (pow_nonneg hZ2_pos.le k)
    have hS1_err' : (R : ℝ) ^ 2 * (2 * Real.log (R : ℝ) + 2) ^ (8 * k) ≤ (1 / 10 : ℝ) * (X : ℝ) * Z2 ^ k :=
      le_trans hS1_err (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hZ2_low k) (by positivity))
    have hM1_le : (∑ d ∈ Erdos6MaynardTao.validSet k W R,
        ∑ e ∈ (Erdos6MaynardTao.validSet k W R).filter (fun e => ∀ i j : Fin k, i ≠ j → Nat.Coprime (d i) (e j)),
          (Erdos6MaynardTao.lambdaOfY k W R y d * Erdos6MaynardTao.lambdaOfY k W R y e) /
            (∏ i : Fin k, (Nat.lcm (d i) (e i) : ℝ))) ≤ (11 / 10 : ℝ) * Z2 ^ k := by
      linarith only [hstep2, hstep3, hM1_err]
    have hX_mul : (X : ℝ) * _ ≤ (X : ℝ) * ((11 / 10 : ℝ) * Z2 ^ k) :=
      mul_le_mul_of_nonneg_left hM1_le (Nat.cast_nonneg X)
    change S1 ≤ _
    linarith only [hstep1, hX_mul, hS1_err']
  -- Lower bound S2(idx) >= (1/2) * (1/cW) * X * Z1^2 * Z2^(k-1) for each idx
  have hS2_each : ∀ idx : Fin k,
      (1 / 2 : ℝ) * ((W : ℝ) / (Nat.totient W : ℝ)) * (X : ℝ) * Z1 ^ 2 * Z2 ^ (k - 1) ≤
      ∑ n ∈ Finset.Ioc X (2 * X),
        (if (Lform idx n).Prime then Real.log (Lform idx n : ℝ) else 0) * (weight n) ^ 2 := by
    intro idx
    have hb'_le : M * v0 + b + h idx ≤ Bmax := by
      dsimp only [Bmax, hmax]
      have := Finset.le_sup (f := h) (Finset.mem_univ idx)
      omega
    obtain ⟨hx1_ge3, hQ_x1, hQ_x2, hQ_fl1, hBV_e⟩ := hBV_all (M * v0 + b + h idx) hb'_le
    have hstep1 := Erdos6MaynardTao.S2_ge_mul_M2_sub_BV_err (R := R) (X := X) hM hMD (by omega) hRX h h_inj hhD hcop
      y hy_bd.1 hy_bd.2.1 idx hC'_nn hBV' hx1_ge3 hQ_x1 hQ_x2 hQ_fl1
    have hstep2 := Erdos6MaynardTao.M2_ge_T2_sub_err (R := R) (U := U) hD_quad (by omega) hUR y
      (Erdos6MaynardTao.gWeight A k R) hy_bd.1
      (fun n => by
        by_cases h0 : n = 0
        · unfold Erdos6MaynardTao.gWeight Erdos6MaynardTao.tVal; simp [h0]
        · exact Erdos6MaynardTao.gWeight_nonneg hA_pos hR2 (Nat.pos_of_ne_zero h0))
      hy_bd.2.2.1 hy_bd.2.2.2 idx
    have hstep3 := Erdos6MaynardTao.T2_ge_chebyshev hA_pos hT_pos hk2 (by omega) hR2 hU1 hU_pow idx hdelta_pos
    -- Bound 3 * k^2 / (D0 - 2) <= 1 / 10
    have hD2_pos : (0 : ℝ) < (D0 : ℝ) - 2 := by
      have : (10 : ℝ) ≤ D0 := by exact_mod_cast (by omega : 10 ≤ D0)
      linarith only [this]
    have hD3_pos : (0 : ℝ) < (D0 : ℝ) - 3 := by
      have : (10 : ℝ) ≤ D0 := by exact_mod_cast (by omega : 10 ≤ D0)
      linarith only [this]
    have h3k_le : 3 * (k : ℝ) ^ 2 / ((D0 : ℝ) - 2) ≤ 1 / 10 := by
      rw [div_le_div_iff₀ hD2_pos (by norm_num)]; linarith only [hD_cheb]
    have hT2_low : (7 / 10 : ℝ) * (Z1 ^ 2 * Z2 ^ (k - 1)) ≤
        ∑ u ∈ (Erdos6MaynardTao.validSet k W R).filter (fun u => u idx = 1),
          (Erdos6MaynardTao.YBar W R y idx u) ^ 2 /
            (∏ i ∈ Finset.univ.erase idx, (Nat.totient (u i) : ℝ)) := by
      have h1 : (7 / 10 : ℝ) ≤ 1 - ((k - 1 : ℕ) : ℝ) * (M_U / (A ^ 2 * Z2)) / delta ^ 2 -
          3 * (k : ℝ) ^ 2 / ((D0 : ℝ) - 2) := by linarith only [hcheb_le, h3k_le]
      have h2 := mul_le_mul_of_nonneg_left h1 (mul_nonneg (sq_nonneg Z1) (pow_nonneg hZ2_pos.le (k - 1)))
      linarith only [h2, hstep3]
    -- Bound M2 error <= (1/10) * Z1^2 * Z2^(k-1)
    have h2MU_Z2 : 2 * M_U ≤ (8 * T / I2) * Z2 := by
      have h1 : (8 * T / I2) * ((I2 / 2) * scale) = 4 * T * scale := by field_simp; ring
      have h2 := mul_le_mul_of_nonneg_left hZ2_low (by positivity : (0 : ℝ) ≤ 8 * T / I2)
      linarith only [hMU_le, h1, h2]
    have hM2_err : (16 * (k : ℝ) ^ 2 / ((D0 : ℝ) - 3)) * Z1 ^ 2 * (2 * M_U) ^ (k - 1) ≤
        (1 / 10 : ℝ) * (Z1 ^ 2 * Z2 ^ (k - 1)) := by
      have hpow : (2 * M_U) ^ (k - 1) ≤ (8 * T / I2) ^ (k - 1) * Z2 ^ (k - 1) := by
        rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith only [hMU_nn]) h2MU_Z2 (k - 1)
      have hfrac : (16 * (k : ℝ) ^ 2 / ((D0 : ℝ) - 3)) * (8 * T / I2) ^ (k - 1) ≤ 1 / 10 := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ hD3_pos (by norm_num)]
        linarith only [hD_M2]
      calc (16 * (k : ℝ) ^ 2 / ((D0 : ℝ) - 3)) * Z1 ^ 2 * (2 * M_U) ^ (k - 1)
          ≤ (16 * (k : ℝ) ^ 2 / ((D0 : ℝ) - 3)) * Z1 ^ 2 * ((8 * T / I2) ^ (k - 1) * Z2 ^ (k - 1)) :=
            mul_le_mul_of_nonneg_left hpow (by positivity)
        _ = ((16 * (k : ℝ) ^ 2 / ((D0 : ℝ) - 3)) * (8 * T / I2) ^ (k - 1)) * (Z1 ^ 2 * Z2 ^ (k - 1)) := by ring
        _ ≤ (1 / 10 : ℝ) * (Z1 ^ 2 * Z2 ^ (k - 1)) :=
            mul_le_mul_of_nonneg_right hfrac (mul_nonneg (sq_nonneg _) (pow_nonneg hZ2_pos.le _))
    have hM2_low : (6 / 10 : ℝ) * (Z1 ^ 2 * Z2 ^ (k - 1)) ≤
        ∑ d ∈ (Erdos6MaynardTao.validSet k W R).filter (fun d => d idx = 1),
          ∑ e ∈ (Erdos6MaynardTao.validSet k W R).filter
            (fun e => e idx = 1 ∧ ∀ i j : Fin k, i ≠ j → Nat.Coprime (d i) (e j)),
            (Erdos6MaynardTao.lambdaOfY k W R y d * Erdos6MaynardTao.lambdaOfY k W R y e) /
              (∏ i : Fin k, (Nat.totient (Nat.lcm (d i) (e i)) : ℝ)) := by
      linarith only [hstep2, hT2_low, hM2_err]
    have hBV_e' :
        (2 * Real.log (R : ℝ) + 2) ^ (6 * k) *
          Real.sqrt ((2 * Real.log (R : ℝ) + 1) ^ (9 * k ^ 2)) *
          (Real.sqrt (5 * C' * ((2 * M * W * X + (M * v0 + b + h idx) : ℕ) : ℝ) ^ 2 *
              Real.log ((2 * M * W * X + (M * v0 + b + h idx) : ℕ) : ℝ) /
              Real.log ((2 * M * W * X + (M * v0 + b + h idx) : ℕ) : ℝ) ^ A_BV) +
            Real.sqrt (5 * C' * ((M * W * X + (M * v0 + b + h idx) : ℕ) : ℝ) ^ 2 *
              Real.log ((M * W * X + (M * v0 + b + h idx) : ℕ) : ℝ) /
              Real.log ((M * W * X + (M * v0 + b + h idx) : ℕ) : ℝ) ^ A_BV)) ≤
        (1 / 10 : ℝ) * ((W : ℝ) / (Nat.totient W : ℝ)) * (X : ℝ) * Z1 ^ 2 * Z2 ^ (k - 1) := by
      refine le_trans hBV_e ?_
      have hsq1 : ((1 / 2 : ℝ) * scale) ^ 2 ≤ Z1 ^ 2 :=
        pow_le_pow_left₀ (by positivity) (by linarith only [hZ1_low, hscale_pos]) 2
      have hpow2 : ((I2 / 2) * scale) ^ (k - 1) ≤ Z2 ^ (k - 1) :=
        pow_le_pow_left₀ (by positivity) hZ2_low (k - 1)
      have hmul := mul_le_mul hsq1 hpow2 (by positivity) (sq_nonneg Z1)
      have hsc := mul_le_mul_of_nonneg_left hmul
        (show (0 : ℝ) ≤ (1 / 10 : ℝ) * ((W : ℝ) / (Nat.totient W : ℝ)) * (X : ℝ) by positivity)
      linarith only [hsc]
    have hmain_mul := mul_le_mul_of_nonneg_left hM2_low
      (show (0 : ℝ) ≤ ((W : ℝ) / (Nat.totient W : ℝ)) * (X : ℝ) by positivity)
    linarith only [hstep1, hmain_mul, hBV_e']
  -- Sum over idx : Fin k and prove strict inequality r * log(2MWX + Bmax) * S1 < S2
  have hS2_lower : (1 / 2 : ℝ) * (k : ℝ) * ((W : ℝ) / (Nat.totient W : ℝ)) * (X : ℝ) * Z1 ^ 2 * Z2 ^ (k - 1) ≤ S2 := by
    calc (1 / 2 : ℝ) * (k : ℝ) * ((W : ℝ) / (Nat.totient W : ℝ)) * (X : ℝ) * Z1 ^ 2 * Z2 ^ (k - 1)
        = ∑ _idx : Fin k, (1 / 2 : ℝ) * ((W : ℝ) / (Nat.totient W : ℝ)) * (X : ℝ) * Z1 ^ 2 * Z2 ^ (k - 1) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
      _ ≤ S2 := Finset.sum_le_sum fun idx _ => hS2_each idx
  let logMax : ℝ := Real.log ((2 * M * W * X + Bmax : ℕ) : ℝ)
  have hlogMax_pos : 0 < logMax := by
    have h2 : (2 : ℝ) ≤ ((2 * M * W * X + Bmax : ℕ) : ℝ) := by
      have : 2 ≤ 2 * M * W * X + Bmax := by
        have hMW1 : 1 ≤ M * W := Nat.mul_pos hM hW_pos
        have hX1 : 1 ≤ X := by omega
        have h1 : 1 ≤ M * W * X := Nat.mul_pos hMW1 hX1
        have h2 : 2 ≤ 2 * (M * W * X) := by omega
        have heq : 2 * (M * W * X) = 2 * M * W * X := by ring
        omega
      exact_mod_cast this
    exact Real.log_pos (by linarith only [h2])
  have hstrict : (r : ℝ) * logMax * S1 < S2 := by
    have hZ2_split : Z2 ^ k = Z2 * Z2 ^ (k - 1) := by
      rw [← pow_succ']; congr 1; omega
    have hS1_nn : 0 ≤ S1 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hX_pos : (0 : ℝ) < X := Nat.cast_pos.mpr (by omega)
    have hZ2k1_pos : 0 < Z2 ^ (k - 1) := pow_pos hZ2_pos (k - 1)
    have hleft : (r : ℝ) * logMax * S1 ≤
        (396 / (50 * A)) * (r : ℝ) * Real.log (R : ℝ) * scale * (X : ℝ) * Z2 ^ (k - 1) := by
      have h1 : (r : ℝ) * logMax * S1 ≤ (r : ℝ) * (6 * Real.log (R : ℝ)) * ((6 / 5 : ℝ) * (X : ℝ) * Z2 ^ k) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hlog_max (Nat.cast_nonneg r)) hS1_upper hS1_nn (by positivity)
      rw [hZ2_split] at h1
      have hZ2_A : Z2 ≤ (11 / (10 * A)) * scale := by
        have h1' : (11 / 10 : ℝ) * I2 ≤ 11 / (10 * A) := by
          have := mul_le_mul_of_nonneg_left hI2_high (by norm_num : (0 : ℝ) ≤ 11 / 10)
          linarith only [this, show (11 / 10 : ℝ) * (1 / A) = 11 / (10 * A) by ring]
        exact le_trans hZ2_high (mul_le_mul_of_nonneg_right h1' hscale_pos.le)
      calc (r : ℝ) * logMax * S1
          ≤ (36 / 5 : ℝ) * (r : ℝ) * Real.log (R : ℝ) * (X : ℝ) * Z2 ^ (k - 1) * Z2 := by linarith only [h1]
        _ ≤ (36 / 5 : ℝ) * (r : ℝ) * Real.log (R : ℝ) * (X : ℝ) * Z2 ^ (k - 1) * ((11 / (10 * A)) * scale) :=
            mul_le_mul_of_nonneg_left hZ2_A (by positivity)
        _ = (396 / (50 * A)) * (r : ℝ) * Real.log (R : ℝ) * scale * (X : ℝ) * Z2 ^ (k - 1) := by ring
    have hright : (81 / 200 : ℝ) * Real.log (R : ℝ) * scale * (X : ℝ) * Z2 ^ (k - 1) ≤ S2 := by
      have hZ1sq : (81 / 100 : ℝ) * scale ^ 2 ≤ Z1 ^ 2 := by
        have := pow_le_pow_left₀ (by positivity) hZ1_low 2
        linarith only [this, show ((9 / 10 : ℝ) * scale) ^ 2 = (81 / 100 : ℝ) * scale ^ 2 by ring]
      have hcancel : (k : ℝ) * ((W : ℝ) / (Nat.totient W : ℝ)) * scale = Real.log (R : ℝ) := by
        dsimp only [scale, cW]
        have hWne : (W : ℝ) ≠ 0 := (Nat.cast_pos.mpr hW_pos).ne'
        have hphi_ne : (Nat.totient W : ℝ) ≠ 0 := (Nat.cast_pos.mpr (Nat.totient_pos.mpr hW_pos)).ne'
        field_simp
      have h1 : (81 / 200 : ℝ) * Real.log (R : ℝ) * scale * (X : ℝ) * Z2 ^ (k - 1) ≤
          (1 / 2 : ℝ) * (k : ℝ) * ((W : ℝ) / (Nat.totient W : ℝ)) * (X : ℝ) * Z1 ^ 2 * Z2 ^ (k - 1) := by
        have h2 := mul_le_mul_of_nonneg_left hZ1sq
          (show (0 : ℝ) ≤ (1 / 2 : ℝ) * (k : ℝ) * ((W : ℝ) / (Nat.totient W : ℝ)) * (X : ℝ) * Z2 ^ (k - 1) by positivity)
        have h3 : (1 / 2 : ℝ) * (k : ℝ) * ((W : ℝ) / (Nat.totient W : ℝ)) * (X : ℝ) * Z2 ^ (k - 1) *
            ((81 / 100 : ℝ) * scale ^ 2) =
            (81 / 200 : ℝ) * ((k : ℝ) * ((W : ℝ) / (Nat.totient W : ℝ)) * scale) * scale * (X : ℝ) * Z2 ^ (k - 1) := by ring
        rw [h3, hcancel] at h2
        linarith only [h2]
      exact le_trans h1 hS2_lower
    have hcoeff_lt : (396 / (50 * A)) * (r : ℝ) < (81 / 200 : ℝ) := by
      have heq : (396 / (50 * A)) * (r : ℝ) = (396 * (r : ℝ)) / (50 * A) := by ring
      rw [heq, div_lt_iff₀ (by positivity)]
      dsimp only [A]; linarith only [hA60]
    have hpos_factor : 0 < Real.log (R : ℝ) * scale * (X : ℝ) * Z2 ^ (k - 1) := by positivity
    have hmid := mul_lt_mul_of_pos_right hcoeff_lt hpos_factor
    linarith only [hleft, hright, hmid]
  -- Extract n in Ioc X (2 * X) with more than r primes among Lform idx n
  have hsum_pos : 0 < ∑ n ∈ Finset.Ioc X (2 * X),
      ((∑ idx : Fin k, if (Lform idx n).Prime then Real.log (Lform idx n : ℝ) else 0) -
        (r : ℝ) * logMax) * (weight n) ^ 2 := by
    have heq : S2 - (r : ℝ) * logMax * S1 = ∑ n ∈ Finset.Ioc X (2 * X),
        ((∑ idx : Fin k, if (Lform idx n).Prime then Real.log (Lform idx n : ℝ) else 0) -
          (r : ℝ) * logMax) * (weight n) ^ 2 := by
      dsimp only [S2, S1]
      rw [Finset.sum_comm, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [← Finset.sum_mul]; ring
    linarith
  have hex_n : ∃ n ∈ Finset.Ioc X (2 * X),
      0 < ((∑ idx : Fin k, if (Lform idx n).Prime then Real.log (Lform idx n : ℝ) else 0) -
        (r : ℝ) * logMax) * (weight n) ^ 2 := by
    by_contra hall
    push Not at hall
    have hle0 : ∑ n ∈ Finset.Ioc X (2 * X),
        ((∑ idx : Fin k, if (Lform idx n).Prime then Real.log (Lform idx n : ℝ) else 0) -
          (r : ℝ) * logMax) * (weight n) ^ 2 ≤ 0 :=
      Finset.sum_nonpos hall
    linarith
  rcases hex_n with ⟨n, hn, hterm_pos⟩
  have hgt_r : (r : ℝ) * logMax <
      ∑ idx : Fin k, if (Lform idx n).Prime then Real.log (Lform idx n : ℝ) else 0 := by
    by_contra hle
    push Not at hle
    have : ((∑ idx : Fin k, if (Lform idx n).Prime then Real.log (Lform idx n : ℝ) else 0) -
        (r : ℝ) * logMax) * (weight n) ^ 2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _)
    linarith
  have hsum_le_card :
      (∑ idx : Fin k, if (Lform idx n).Prime then Real.log (Lform idx n : ℝ) else 0) ≤
      (((Finset.univ : Finset (Fin k)).filter (fun idx => (Lform idx n).Prime)).card : ℝ) * logMax := by
    rw [← Finset.sum_filter]
    calc ∑ idx ∈ Finset.univ.filter (fun idx => (Lform idx n).Prime), Real.log (Lform idx n : ℝ)
        ≤ ∑ _idx ∈ Finset.univ.filter (fun idx => (Lform idx n).Prime), logMax := by
          refine Finset.sum_le_sum fun idx hidx => ?_
          have hp := (Finset.mem_filter.mp hidx).2
          have hle_max : Lform idx n ≤ 2 * M * W * X + Bmax := by
            have hn2X : n ≤ 2 * X := (Finset.mem_Ioc.mp hn).2
            have hhi : h idx ≤ hmax := Finset.le_sup (f := h) (Finset.mem_univ idx)
            dsimp only [Lform, Bmax]
            have : M * W * n ≤ M * W * (2 * X) := Nat.mul_le_mul_left (M * W) hn2X
            linarith
          exact Real.log_le_log (Nat.cast_pos.mpr hp.pos) (Nat.cast_le.mpr hle_max)
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hr_lt_card : r < (Finset.univ.filter (fun idx : Fin k => (Lform idx n).Prime)).card := by
    have h1 : (r : ℝ) * logMax < (((Finset.univ.filter (fun idx : Fin k => (Lform idx n).Prime)).card : ℕ) : ℝ) * logMax :=
      lt_of_lt_of_le hgt_r hsum_le_card
    have h2 : (r : ℝ) < (((Finset.univ.filter (fun idx : Fin k => (Lform idx n).Prime)).card : ℕ) : ℝ) :=
      lt_of_mul_lt_mul_right h1 hlogMax_pos.le
    exact_mod_cast h2
  -- Set x = W * n + v0 and map prime indices into H via h
  refine ⟨W * n + v0, ?_, ?_⟩
  · have hnX : X < n := (Finset.mem_Ioc.mp hn).1
    have h1 : n ≤ W * n := Nat.le_mul_of_pos_left n hW_pos
    omega
  · have hsub : (Finset.univ.filter (fun idx : Fin k => (Lform idx n).Prime)).image h ⊆
        H.filter (fun a => (M * (W * n + v0) + b + a).Prime) := by
      intro a ha
      rcases Finset.mem_image.mp ha with ⟨idx, hidx, rfl⟩
      have hp : (Lform idx n).Prime := (Finset.mem_filter.mp hidx).2
      have heq : M * (W * n + v0) + b + h idx = Lform idx n := by dsimp only [Lform]; ring
      exact Finset.mem_filter.mpr ⟨hhH idx, heq.symm ▸ hp⟩
    calc r ≤ (Finset.univ.filter (fun idx : Fin k => (Lform idx n).Prime)).card := hr_lt_card.le
      _ = ((Finset.univ.filter (fun idx : Fin k => (Lform idx n).Prime)).image h).card :=
          (Finset.card_image_of_injective _ h_inj).symm
      _ ≤ (H.filter (fun a => (M * (W * n + v0) + b + a).Prime)).card := Finset.card_le_card hsub

theorem OMA.solution : OMA.R_Erdos6_erdos_6_variants_increasing_R1.H2 :=
  maynard_tao_from_bv
