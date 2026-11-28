import OMAStatements.S_arxiv_2604_17847
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Tactic.NormNum.Prime
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.ReduceModChar

namespace OMA.R_arxiv_2604_17847_R1

open OMA.S_arxiv_2604_17847

-- It suffices to find a finite cover in the case of a recurring prime-index rank family.
def H1 : Prop :=
  ∀ q r : ℕ, q.Prime → 53 < q → r ∈ S q →
    (∃ e : ℕ, e ∣ r.gcd (pisano q) ∧ ∀ B : ℕ, ∃ l > B, ∃ p > B,
      l.Prime ∧ r.gcd (pisano q) * l ≡ r [MOD pisano q] ∧
      p.Prime ∧ p ≡ 1 [MOD q] ∧ rankOfApparition p = e * l) →
    ∃ (r : ℕ) (W : Finset ℕ), r < pisano q ∧
      ∀ m : ℕ, 0 < m → m ≡ r [MOD pisano q] → q ^ 2 ∣ Nat.fib m ∨
        ∃ p ∈ W, p.Prime ∧ p ≡ 1 [MOD q] ∧ p ∣ Nat.fib m

-- Isolate the exceptional square-divisibility case at the period.
def H2 : Prop :=
  ∀ q : ℕ, q.Prime → 53 < q → q ^ 2 ∣ Nat.fib (pisano q) →
    ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD q] ∧ rankOfApparition p ∣ pisano q

-- The gcd argument follows the proof for OEIS A000032 (project PR 9447).
lemma rank_dvd_index {p n : ℕ} (hn : 0 < n) (hpn : p ∣ Nat.fib n) :
    rankOfApparition p ∣ n := by
  let indices : Set ℕ := {k | 0 < k ∧ p ∣ Nat.fib k}
  have hr : sInf indices ∈ indices := Nat.sInf_mem ⟨n, hn, hpn⟩
  obtain ⟨hrpos, hpr⟩ : 0 < sInf indices ∧ p ∣ Nat.fib (sInf indices) := hr
  have hg : Nat.gcd (sInf indices) n ∈ indices := by
    refine ⟨Nat.gcd_pos_of_pos_left _ hrpos, ?_⟩
    rw [Nat.fib_gcd]
    exact Nat.dvd_gcd hpr hpn
  have heq := le_antisymm (Nat.gcd_le_left n hrpos) (Nat.sInf_le hg)
  change sInf indices ∣ n
  simpa only [heq] using Nat.gcd_dvd_right (sInf indices) n

-- Adapt the totient factorization argument of the Erdős 1003 proof (project PR 6554).
lemma totient_fib_witness {q n : ℕ} (hq : q.Prime) (hd : q ∣ Nat.totient (Nat.fib n)) :
    q ^ 2 ∣ Nat.fib n ∨
      ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD q] ∧ rankOfApparition p ∣ n := by
  by_cases hz : Nat.fib n = 0
  · left
    rw [hz]
    exact dvd_zero _
  have hn : 0 < n := Nat.fib_pos.mp (Nat.pos_of_ne_zero hz)
  rw [Nat.totient_eq_prod_factorization hz, Finsupp.prod, Nat.support_factorization] at hd
  obtain ⟨p, hp, hfactor⟩ := (hq.prime.dvd_finsetProd_iff _).mp hd
  have hpPrime := Nat.prime_of_mem_primeFactors hp
  have hpFib := Nat.dvd_of_mem_primeFactors hp
  obtain ⟨a, ha⟩ := Nat.exists_eq_succ_of_ne_zero
    (hpPrime.factorization_pos_of_dvd hz hpFib).ne'
  rw [ha, Nat.succ_sub_one] at hfactor
  rcases hq.dvd_mul.mp hfactor with hpower | hpred
  · have heq := (Nat.prime_dvd_prime_iff_eq hq hpPrime).mp (hq.dvd_of_dvd_pow hpower)
    subst p
    have hapos : a ≠ 0 := by
      intro he
      simp [he, hq.not_dvd_one] at hpower
    exact Or.inl ((pow_dvd_pow q (by omega : 2 ≤ (Nat.fib n).factorization q)).trans
      (Nat.ordProj_dvd (Nat.fib n) q))
  · exact Or.inr ⟨p, hpPrime, ((Nat.modEq_iff_dvd' hpPrime.one_lt.le).2 hpred).symm,
      rank_dvd_index hn hpFib⟩

-- The product contains precisely the primes dividing L that do not divide a.
lemma coprime_representative {a b L : ℕ} (hab : a.Coprime b) (hb : 0 < b) (hL : 0 < L) :
    ∃ t : ℕ, 0 < t ∧ t ≡ a [MOD b] ∧ L.Coprime t := by
  let primes := L.primeFactors.filter fun p => ¬ p ∣ a
  let k := primes.prod id
  have hk : 0 < k := Finset.prod_pos fun p hp =>
    (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos
  refine ⟨a + k * b, Nat.add_pos_right _ (Nat.mul_pos hk hb), Nat.add_mul_modulus_modEq_iff.mpr rfl, ?_⟩
  apply Nat.coprime_of_dvd
  intro p hp hpL hpt
  by_cases hpa : p ∣ a
  · have hpkb := (Nat.dvd_add_iff_right hpa).mpr hpt
    rcases hp.dvd_mul.mp hpkb with hpk | hpb
    · obtain ⟨s, hs, hps⟩ := (hp.prime.dvd_finsetProd_iff id).mp hpk
      have hsPrime := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hs).1
      have heq := (Nat.prime_dvd_prime_iff_eq hp hsPrime).mp hps
      exact (Finset.mem_filter.mp hs).2 (heq ▸ hpa)
    · exact hp.ne_one (Nat.eq_one_of_dvd_coprimes hab hpa hpb)
  · have hmem : p ∈ primes := Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hp, hpL, hL.ne'⟩, hpa⟩
    have hpk : p ∣ k := Finset.dvd_prod_of_mem id hmem
    exact hpa ((Nat.dvd_add_iff_left (dvd_mul_of_dvd_left hpk b)).mpr hpt)

-- Normalize by the gcd as in the OEIS A070548 proof (project PR 13027).
lemma finite_divisor_representative (D : Finset ℕ) (r P : ℕ) (hP : 0 < P) :
    ∃ m : ℕ, 0 < m ∧ m ≡ r [MOD P] ∧ ∀ d ∈ D, d ∣ m → d ∣ r.gcd P := by
  let positive := D.filter fun d => 0 < d
  let L := positive.prod id
  have hL : 0 < L := Finset.prod_pos fun d hd => (Finset.mem_filter.mp hd).2
  obtain ⟨a, b, hab, ha, hb⟩ := Nat.exists_coprime r P
  have hbpos : 0 < b := by
    by_contra! hz
    have he := Nat.eq_zero_of_le_zero hz
    rw [he, Nat.zero_mul] at hb
    omega
  obtain ⟨t, ht, hmod, hcop⟩ := coprime_representative hab hbpos hL
  have hg := Nat.gcd_pos_of_pos_right r hP
  refine ⟨t * r.gcd P, Nat.mul_pos ht hg, ?_, ?_⟩
  · simpa only [← ha, ← hb] using hmod.mul_right' (r.gcd P)
  · intro d hd hdm
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdm (Nat.mul_pos ht hg)
    have hdL : d ∣ L := Finset.dvd_prod_of_mem id (Finset.mem_filter.mpr ⟨hd, hdpos⟩)
    exact (Nat.Coprime.of_dvd_left hdL hcop).dvd_of_dvd_mul_left hdm

lemma finite_divisor_cover (D : Finset ℕ) {r P : ℕ} (hP : 0 < P)
    (cover : ∀ m : ℕ, 0 < m → m ≡ r [MOD P] → ∃ d ∈ D, d ∣ m) :
    ∃ d ∈ D, d ∣ r.gcd P := by
  obtain ⟨m, hm, hmod, restrict⟩ := finite_divisor_representative D r P hP
  obtain ⟨d, hd, hdm⟩ := cover m hm hmod
  exact ⟨d, hd, restrict d hd hdm⟩

-- A finite pool supplies a single witness already at the gcd of the residue and period.
lemma finite_fib_witness_at_gcd (W : Finset ℕ) {q r P : ℕ} (hP : 0 < P)
    (cover : ∀ m : ℕ, 0 < m → m ≡ r [MOD P] →
      ∃ b ∈ W, q ∣ Nat.totient b ∧ b ∣ Nat.fib m) :
    ∃ b ∈ W, q ∣ Nat.totient b ∧ b ∣ Nat.fib (r.gcd P) := by
  classical
  obtain ⟨m, hm, hmod, restrict⟩ := finite_divisor_representative (W.image rankOfApparition) r P hP
  obtain ⟨b, hb, htot, hbm⟩ := cover m hm hmod
  have halign := restrict (rankOfApparition b) (Finset.mem_image_of_mem _ hb) (rank_dvd_index hm hbm)
  have hrank : 0 < rankOfApparition b ∧ b ∣ Nat.fib (rankOfApparition b) :=
    Nat.sInf_mem (s := {k : ℕ | 0 < k ∧ b ∣ Nat.fib k}) ⟨m, hm, hbm⟩
  exact ⟨b, hb, htot, hrank.2.trans (Nat.fib_dvd _ _ halign)⟩

lemma finite_prime_witness_descent (W : Finset ℕ) {q r P : ℕ} (hq : q.Prime) (hP : 0 < P)
    (cover : ∀ m : ℕ, 0 < m → m ≡ r [MOD P] → q ^ 2 ∣ Nat.fib m ∨
      ∃ p ∈ W, p.Prime ∧ p ≡ 1 [MOD q] ∧ p ∣ Nat.fib m) :
    q ∣ Nat.totient (Nat.fib P) := by
  have square : q ∣ Nat.totient (q ^ 2) := by
    rw [Nat.totient_prime_pow_succ hq 1, pow_one]
    exact dvd_mul_right _ _
  obtain ⟨b, _, hqt, hbg⟩ := finite_fib_witness_at_gcd (insert (q ^ 2) W) hP (q := q) (r := r) (by
    intro m hm hmod
    rcases cover m hm hmod with hs | ⟨p, hpW, hp, hpmod, hpm⟩
    · exact ⟨_, Finset.mem_insert_self _ _, square, hs⟩
    · refine ⟨p, Finset.mem_insert_of_mem hpW, ?_, hpm⟩
      rw [Nat.totient_prime hp]
      exact hpmod.symm.dvd')
  exact hqt.trans (Nat.totient_dvd_of_dvd (hbg.trans (Nat.fib_dvd _ _ (Nat.gcd_dvd_right r P))))

-- Conversely a witness at the period covers the zero residue class.
lemma finite_prime_cover_iff {q P : ℕ} (hq : q.Prime) (hP : 0 < P) :
    (∃ (r : ℕ) (W : Finset ℕ), r < P ∧
      ∀ m : ℕ, 0 < m → m ≡ r [MOD P] → q ^ 2 ∣ Nat.fib m ∨
        ∃ p ∈ W, p.Prime ∧ p ≡ 1 [MOD q] ∧ p ∣ Nat.fib m) ↔
      q ∣ Nat.totient (Nat.fib P) := by
  constructor
  · rintro ⟨r, W, _, cover⟩
    exact finite_prime_witness_descent W hq hP cover
  · intro htot
    rcases totient_fib_witness hq htot with hsquare | ⟨p, hp, hpmod, hrP⟩
    · refine ⟨0, ∅, hP, ?_⟩
      intro m _ hm
      exact Or.inl (hsquare.trans (Nat.fib_dvd _ _ (Nat.modEq_zero_iff_dvd.mp hm)))
    · have hrpos := Nat.pos_of_dvd_of_pos hrP hP
      have hindices := Nat.nonempty_of_pos_sInf (s := {k : ℕ | 0 < k ∧ p ∣ Nat.fib k}) hrpos
      have hrank : 0 < rankOfApparition p ∧ p ∣ Nat.fib (rankOfApparition p) := Nat.sInf_mem hindices
      refine ⟨0, {p}, hP, ?_⟩
      intro m _ hm
      exact Or.inr ⟨p, Finset.mem_singleton_self p, hp, hpmod,
        hrank.2.trans (Nat.fib_dvd _ _ (hrP.trans (Nat.modEq_zero_iff_dvd.mp hm)))⟩

lemma factor_rank_at_prime_index {k g l : ℕ} (hl : l.Prime) (hk : k ∣ g * l) (hkg : ¬ k ∣ g) :
    ∃ e : ℕ, e ∣ g ∧ k = e * l := by
  by_cases h : l ∣ k
  · obtain ⟨e, he⟩ := h
    have hke : k = e * l := he.trans (Nat.mul_comm _ _)
    exact ⟨e, Nat.dvd_of_mul_dvd_mul_right hl.pos (hke ▸ hk), hke⟩
  · exact False.elim (hkg ((hl.coprime_iff_not_dvd.mpr h).symm.dvd_of_dvd_mul_right hk))

lemma witness_totient_at_period {w q P : ℕ} (hP : 0 < P)
    (hrP : rankOfApparition w ∣ P) (hqw : q ∣ Nat.totient w) :
    q ∣ Nat.totient (Nat.fib P) := by
  have hindices := Nat.nonempty_of_pos_sInf (s := {k : ℕ | 0 < k ∧ w ∣ Nat.fib k})
    (Nat.pos_of_dvd_of_pos hrP hP)
  have hr : 0 < rankOfApparition w ∧ w ∣ Nat.fib (rankOfApparition w) := Nat.sInf_mem hindices
  exact hqw.trans (Nat.totient_dvd_of_dvd (hr.2.trans (Nat.fib_dvd _ _ hrP)))

-- At every sufficiently large prime index in the normalized class the square witness drops out.
lemma prime_index_rank {q r l : ℕ} (hq : q.Prime) (hr : r ∈ S q)
    (hbad : ¬ q ∣ Nat.totient (Nat.fib (pisano q))) (hl : l.Prime)
    (hlarge : rankOfApparition (q ^ 2) < l)
    (hmod : r.gcd (pisano q) * l ≡ r [MOD pisano q]) :
    ∃ e : ℕ, e ∣ r.gcd (pisano q) ∧ ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD q] ∧ rankOfApparition p = e * l := by
  let g := r.gcd (pisano q)
  have hP := Nat.zero_lt_of_lt hr.1
  have hg : 0 < g := Nat.gcd_pos_of_pos_right _ hP
  have indexpos := Nat.mul_pos hg hl.pos
  have unaligned (w : ℕ) (hw : q ∣ Nat.totient w) : ¬ rankOfApparition w ∣ g :=
    fun hd => hbad (witness_totient_at_period hP (hd.trans (Nat.gcd_dvd_right _ _)) hw)
  rcases totient_fib_witness hq (hr.2 _ hmod) with hs | ⟨p, hp, hpmod, hrank⟩
  · have hsq : q ∣ Nat.totient (q ^ 2) := by
      rw [Nat.totient_prime_pow_succ hq 1, pow_one]
      exact dvd_mul_right _ _
    have hd := rank_dvd_index indexpos hs
    obtain ⟨e, he, heq⟩ := factor_rank_at_prime_index hl hd (unaligned _ hsq)
    have hepos := Nat.pos_of_dvd_of_pos he hg
    have hle : l ≤ e * l := by simpa using Nat.mul_le_mul_right l hepos
    omega
  · have hqt : q ∣ Nat.totient p := by rw [Nat.totient_prime hp]; exact hpmod.symm.dvd'
    obtain ⟨e, he, heq⟩ := factor_rank_at_prime_index hl hrank (unaligned _ hqt)
    exact ⟨e, he, p, hp, hpmod, heq⟩

-- Normalize before applying Dirichlet's theorem, as in project PR 5789.
lemma normalized_prime_indices {r P : ℕ} (hP : 0 < P) :
    ∀ B : ℕ, ∃ l > B, l.Prime ∧ r.gcd P * l ≡ r [MOD P] := by
  obtain ⟨a, b, hab, ha, hb⟩ := Nat.exists_coprime r P
  have hb0 : b ≠ 0 := by
    intro hz
    rw [hz, Nat.zero_mul] at hb
    omega
  intro B
  obtain ⟨l, hlarge, hl, hmod⟩ := Nat.forall_exists_prime_gt_and_modEq B hb0 hab
  refine ⟨l, hlarge, hl, ?_⟩
  simpa only [Nat.mul_comm (r.gcd P) l, ← ha, ← hb] using hmod.mul_right' (r.gcd P)

-- Select an infinite fiber of the divisor choice, as in project PR 8141.
lemma fixed_rank_family {q r : ℕ} (hq : q.Prime) (hr : r ∈ S q)
    (hbad : ¬ q ∣ Nat.totient (Nat.fib (pisano q))) :
    ∃ e : ℕ, e ∣ r.gcd (pisano q) ∧ ∀ B : ℕ, ∃ l > B, ∃ p > B,
      l.Prime ∧ r.gcd (pisano q) * l ≡ r [MOD pisano q] ∧
      p.Prime ∧ p ≡ 1 [MOD q] ∧ rankOfApparition p = e * l := by
  classical
  let g := r.gcd (pisano q)
  have hg : 0 < g := Nat.gcd_pos_of_pos_right _ (Nat.zero_lt_of_lt hr.1)
  have pick (B : ℕ) : ∃ e : ↥g.divisors, ∃ l > B, ∃ p > B,
      l.Prime ∧ g * l ≡ r [MOD pisano q] ∧ p.Prime ∧ p ≡ 1 [MOD q] ∧
      rankOfApparition p = e.val * l := by
    let cap := (Finset.range (B + 1)).sup rankOfApparition
    obtain ⟨l, hbound, hl, hmod⟩ := normalized_prime_indices (r := r)
      (Nat.zero_lt_of_lt hr.1) (max B (max cap (rankOfApparition (q ^ 2))))
    have hlB : B < l := lt_of_le_of_lt (le_max_left ..) hbound
    have hother := lt_of_le_of_lt (le_max_right ..) hbound
    obtain ⟨e, he, p, hp, hpmod, heq⟩ := prime_index_rank hq hr hbad hl
      (lt_of_le_of_lt (le_max_right ..) hother) hmod
    have hepos := Nat.pos_of_dvd_of_pos he hg
    have hle : l ≤ e * l := by simpa using Nat.mul_le_mul_right l hepos
    have hpB : B < p := by
      by_contra! hsmall
      have hcap : rankOfApparition p ≤ cap := Finset.le_sup (Finset.mem_range_succ_iff.mpr hsmall)
      have := lt_of_le_of_lt (le_max_left ..) hother
      omega
    exact ⟨⟨e, Nat.mem_divisors.mpr ⟨he, hg.ne'⟩⟩, l, hlB, p, hpB, hl, hmod, hp, hpmod, heq⟩
  choose color hcolor using pick
  obtain ⟨v, hv⟩ := Finite.exists_infinite_fiber color
  refine ⟨v.val, (Nat.mem_divisors.mp v.property).1, ?_⟩
  intro B
  obtain ⟨i, hi, hBi⟩ := (Set.infinite_coe_iff.mp hv).exists_gt B
  change color i = v at hi
  obtain ⟨l, hil, p, hip, rest⟩ := hcolor i
  exact ⟨l, hBi.trans hil, p, hBi.trans hip, hi ▸ rest⟩

-- One eligible prime with no possible rank witness excludes the residue.
lemma not_mem_of_missing_rank {q r l : ℕ} (hq : q.Prime)
    (hbad : ¬ q ∣ Nat.totient (Nat.fib (pisano q))) (hl : l.Prime)
    (hlarge : rankOfApparition (q ^ 2) < l)
    (hmod : r.gcd (pisano q) * l ≡ r [MOD pisano q])
    (hmiss : ∀ e : ℕ, e ∣ r.gcd (pisano q) → ∀ p : ℕ, p.Prime → p ≡ 1 [MOD q] →
      rankOfApparition p ≠ e * l) : r ∉ S q := by
  intro hr
  obtain ⟨e, he, p, hp, hc, hrank⟩ := prime_index_rank hq hr hbad hl hlarge hmod
  exact hmiss e he p hp hc hrank

-- Test a period using two consecutive values, as in project PRs 8383 and 9447.
lemma pisano_eq_of_certificate {q P : ℕ} (hP : 0 < P)
    (hstart : Nat.fib P ≡ 0 [MOD q] ∧ Nat.fib (P + 1) ≡ 1 [MOD q])
    (hmin : ∀ k : Fin P, 0 < k.val →
      ¬ (Nat.fib k.val ≡ 0 [MOD q] ∧ Nat.fib (k.val + 1) ≡ 1 [MOD q])) :
    pisano q = P := by
  have hper (n : ℕ) : Nat.fib (n + P) ≡ Nat.fib n [MOD q] := by
    induction n using Nat.twoStepInduction with
    | zero => simpa using hstart.1
    | one => simpa [Nat.add_comm] using hstart.2
    | more n h0 h1 =>
      rw [show n + 2 + P = (n + P) + 2 by omega, Nat.fib_add_two, Nat.fib_add_two]
      simpa only [show n + 1 + P = n + P + 1 by omega] using h0.add h1
  let periods := {k : ℕ | 0 < k ∧ ∀ n : ℕ, Nat.fib (n + k) ≡ Nat.fib n [MOD q]}
  have hmem : P ∈ periods := ⟨hP, hper⟩
  change sInf periods = P
  apply le_antisymm (Nat.sInf_le hmem)
  by_contra! hlt
  obtain ⟨hpos, hperiod⟩ : sInf periods ∈ periods := Nat.sInf_mem ⟨P, hmem⟩
  apply hmin ⟨sInf periods, hlt⟩ hpos
  exact ⟨by simpa using hperiod 0, by simpa [Nat.add_comm] using hperiod 1⟩

lemma prime_mem_of_dvd_product {p : ℕ} (hp : p.Prime) (factors : List ℕ)
    (hpr : ∀ a ∈ factors, Nat.Prime a) (hd : p ∣ factors.prod) : p ∈ factors := by
  induction factors with
  | nil => exact (hp.not_dvd_one hd).elim
  | cons a tail ih =>
    rcases hp.dvd_mul.mp hd with ha | ht
    · exact List.mem_cons.mpr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (hpr a (by simp))).mp ha))
    · exact List.mem_cons_of_mem a (ih (fun b hb => hpr b (List.mem_cons_of_mem _ hb)) ht)

-- An upper multiple with certified prime factors suffices, even when F_n is large.
lemma totient_exception_of_factors {q n k : ℕ} (hq : q.Prime) (hn : 0 < n)
    (safe : List ℕ) (hpr : ∀ a ∈ safe, Nat.Prime a ∧ ¬ a ≡ 1 [MOD q])
    (hsquare : ¬ q ^ 2 ∣ Nat.fib n) (hdiv : Nat.fib n ∣ safe.prod ^ k) :
    ¬ q ∣ Nat.totient (Nat.fib n) := by
  intro htot
  rcases totient_fib_witness hq htot with hs | ⟨p, hp, hmod, hr⟩
  · exact hsquare hs
  · have hpos := Nat.pos_of_dvd_of_pos hr hn
    have hindices := Nat.nonempty_of_pos_sInf (s := {j : ℕ | 0 < j ∧ p ∣ Nat.fib j}) hpos
    have hleast : 0 < rankOfApparition p ∧ p ∣ Nat.fib (rankOfApparition p) := Nat.sInf_mem hindices
    have hd := hp.dvd_of_dvd_pow ((hleast.2.trans (Nat.fib_dvd _ _ hr)).trans hdiv)
    have hm := prime_mem_of_dvd_product hp safe (fun a ha => (hpr a ha).1) hd
    exact (hpr p hm).2 hmod

-- A single totient exception rules out the residue of every divisor of its index.
lemma not_mem_of_divisor_exception {q r n d : ℕ} (hbad : ¬ q ∣ Nat.totient (Nat.fib n))
    (hd : d ∣ n) (hmod : d ≡ r [MOD pisano q]) : r ∉ S q := by
  intro hr
  exact hbad ((hr.2 d hmod).trans (Nat.totient_dvd_of_dvd (Nat.fib_dvd _ _ hd)))

lemma empty_of_exception_table {q P k shifts : ℕ} (hq : q.Prime) (hperiod : pisano q = P)
    (safe : List ℕ) (hpr : ∀ a ∈ safe, Nat.Prime a ∧ ¬ a ≡ 1 [MOD q])
    (table : ∀ r : Fin P, ∃ t : Fin shifts, let n := r.val + t.val * P
      0 < n ∧ ¬ q ^ 2 ∣ Nat.fib n ∧ Nat.fib n ∣ safe.prod ^ k) : S q = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro r hr
  have hlt : r < P := hperiod ▸ hr.1
  obtain ⟨t, hn, hs, hd⟩ := table ⟨r, hlt⟩
  have bad := totient_exception_of_factors hq hn safe hpr hs hd
  have hm : r + t.val * P ≡ r [MOD pisano q] := by
    rw [hperiod]
    exact Nat.add_mul_modulus_modEq_iff.mpr rfl
  exact not_mem_of_divisor_exception bad (dvd_refl _) hm hr

-- At q = 7, the prime 67 is in residue 3 and exceeds the square-witness threshold.
lemma prime_index_exception_seven :
    rankOfApparition (7 ^ 2) < 67 ∧ (67 : ℕ).Prime ∧
      67 ≡ 3 [MOD pisano 7] ∧ ¬ 7 ∣ Nat.totient (Nat.fib 67) := by
  have hP : pisano 7 = 16 := pisano_eq_of_certificate (by decide) (by decide) (by decide)
  have h49 : rankOfApparition (7 ^ 2) ≤ 56 :=
    Nat.sInf_le (s := {k : ℕ | 0 < k ∧ 7 ^ 2 ∣ Nat.fib k}) (m := 56) (by decide +revert)
  refine ⟨by omega, by decide, hP ▸ (by decide), ?_⟩
  apply totient_exception_of_factors (k := 1) (by decide) (by decide) [269, 116849, 1429913]
  · norm_num [List.forall_mem_cons, Nat.ModEq]
  · decide
  · decide

-- Lucas certificates as in project PR 1596, using Mathlib's modular exponentiation tactic.
lemma prime_of_predecessor_factors (p a : ℕ) (factors : List ℕ)
    (hf : factors.prod = p - 1) (hpr : ∀ b ∈ factors, Nat.Prime b)
    (hfull : (a : ZMod p) ^ (p - 1) = 1)
    (htest : ∀ b ∈ factors, (a : ZMod p) ^ ((p - 1) / b) ≠ 1) : p.Prime := by
  apply lucas_primality p (a : ZMod p) hfull
  intro b hb hd
  exact htest b (prime_mem_of_dvd_product hb factors hpr (hf ▸ hd))

-- The same list of certified primes serves every row. Removing primes congruent
-- to one gives the allowed factors for that modulus. Up to three additional
-- periods suffice to find an exception for each residue.
set_option maxRecDepth 4000 in
set_option maxHeartbeats 3000000 in
lemma small_empty_classes {q : ℕ} (hq : q.Prime)
    (hcase : q ∈ ([7, 11, 13, 17, 19, 29, 31, 37, 41, 43, 47] : List ℕ)) : S q = ∅ := by
  have hp0 : Nat.Prime 14736206161 := by
    apply prime_of_predecessor_factors _ 7 [2, 2, 2, 2, 3, 3, 5, 13, 29, 233, 233] (by decide)
    · norm_num [List.forall_mem_cons]
    · reduce_mod_char
    · simp only [List.forall_mem_cons]
      repeat' apply And.intro
      all_goals (reduce_mod_char; decide)
  have hp1 : Nat.Prime 46165371073 := by
    apply prime_of_predecessor_factors _ 7 [2, 2, 2, 2, 2, 2, 3, 2357, 102013] (by decide)
    · norm_num [List.forall_mem_cons]
    · reduce_mod_char
    · simp only [List.forall_mem_cons]
      repeat' apply And.intro
      all_goals (reduce_mod_char; decide)
  have hp2 : Nat.Prime 272602401466814027129 := by
    apply prime_of_predecessor_factors _ 3 [2, 2, 2, 13, 23, 113, 244243, 4129219151] (by decide)
    · norm_num [List.forall_mem_cons]
    · reduce_mod_char
    · simp only [List.forall_mem_cons]
      repeat' apply And.intro
      all_goals (reduce_mod_char; decide)
  have hp3 : Nat.Prime 414988698461 := by
    apply prime_of_predecessor_factors _ 2 [2, 2, 5, 7, 131, 22627519] (by decide)
    · norm_num [List.forall_mem_cons]
    · reduce_mod_char
    · simp only [List.forall_mem_cons]
      repeat' apply And.intro
      all_goals (reduce_mod_char; decide)
  have hp4 : Nat.Prime 5477332620091 := by
    apply prime_of_predecessor_factors _ 12 [2, 3, 5, 131, 2707, 514859] (by decide)
    · norm_num [List.forall_mem_cons]
    · reduce_mod_char
    · simp only [List.forall_mem_cons]
      repeat' apply And.intro
      all_goals (reduce_mod_char; decide)
  have hp5 : Nat.Prime 92180471494753 := by
    apply prime_of_predecessor_factors _ 5 [2, 2, 2, 2, 2, 3, 3, 137, 179, 13051873] (by decide)
    · norm_num [List.forall_mem_cons]
    · reduce_mod_char
    · simp only [List.forall_mem_cons]
      repeat' apply And.intro
      all_goals (reduce_mod_char; decide)
  have hp6 : Nat.Prime 99194853094755497 := by
    apply prime_of_predecessor_factors _ 3 [2, 2, 2, 13, 29, 211, 421, 370248451] (by decide)
    · norm_num [List.forall_mem_cons]
    · reduce_mod_char
    · simp only [List.forall_mem_cons]
      repeat' apply And.intro
      all_goals (reduce_mod_char; decide)
  have hp7 : Nat.Prime 110568632979499 := by
    apply prime_of_predecessor_factors _ 2 [2, 3, 307, 1597, 1699, 22123] (by decide)
    · norm_num [List.forall_mem_cons]
    · reduce_mod_char
    · simp only [List.forall_mem_cons]
      repeat' apply And.intro
      all_goals (reduce_mod_char; decide)
  have hp8 : Nat.Prime 17231203730201189308301 := by
    apply prime_of_predecessor_factors _ 2 [2, 2, 5, 5, 7, 127, 1753, 110568632979499] (by decide)
    · simp only [List.forall_mem_cons, hp7, true_and]
      norm_num
    · reduce_mod_char
    · simp only [List.forall_mem_cons]
      repeat' apply And.intro
      all_goals (reduce_mod_char; decide)
  have hp9 : Nat.Prime 1066340417491710595814572169 := by
    apply prime_of_predecessor_factors _ 3 [2, 2, 2, 11, 89, 131, 199, 521, 2081, 9901, 19801, 24571] (by decide)
    · norm_num [List.forall_mem_cons]
    · reduce_mod_char
    · simp only [List.forall_mem_cons]
      repeat' apply And.intro
      all_goals (reduce_mod_char; decide)
  let primes : List ℕ :=
    [2, 3, 5, 7, 11, 13, 17, 19, 23,
      29, 31, 37, 41, 43, 47, 53, 59, 61,
      67, 71, 73, 79, 83, 89, 97, 101, 107,
      109, 113, 137, 139, 149, 151, 157, 199, 211,
      233, 263, 269, 281, 307, 331, 353, 421, 461,
      521, 557, 661, 677, 701, 797, 829, 859, 881,
      911, 953, 967, 1049, 1087, 1103, 1427, 1597, 1601,
      2161, 2207, 2221, 2269, 2417, 2521, 2789, 3001, 3041,
      3571, 4373, 4481, 4513, 5779, 6673, 9349, 9521, 9901,
      12301, 14503, 18077, 18451, 19441, 19489, 19801, 28657, 39161,
      54833, 59369, 63443, 90481, 103681, 109441, 116849, 135721, 141961,
      474541, 514229, 988681, 1429913, 3010349, 4832521, 6168709, 6376021, 9375829,
      29134601, 35239681, 54018521, 55945741, 86020717, 230686501, 370248451, 433494437, 555003497,
      2710260697, 2971215073, 3415914041, 14736206161, 46165371073, 414988698461, 5477332620091, 92180471494753, 99194853094755497,
      272602401466814027129, 17231203730201189308301, 1066340417491710595814572169]
  have prime_entries : ∀ a ∈ primes, Nat.Prime a := by
    simp only [primes, List.forall_mem_cons, hp0, hp1, hp3, hp4, hp5, hp6, hp2, hp8, hp9, true_and]
    norm_num
  let rows : List (ℕ × ℕ) := [(7, 16), (11, 10), (13, 28), (17, 36), (19, 18), (29, 14), (31, 30), (37, 76), (41, 40), (43, 88), (47, 32)]
  have data : ∀ row ∈ rows, let Q := row.1
      let P := row.2
      let safe := primes.filter (fun a => decide (¬ a ≡ 1 [MOD Q]))
      (0 < P ∧ Nat.fib P ≡ 0 [MOD Q] ∧ Nat.fib (P + 1) ≡ 1 [MOD Q]) ∧
      (∀ j : Fin P, 0 < j.val → ¬ (Nat.fib j.val ≡ 0 [MOD Q] ∧ Nat.fib (j.val + 1) ≡ 1 [MOD Q])) ∧
      ∀ r : Fin P, ∃ t : Fin 4, let n := r.val + t.val * P
        0 < n ∧ ¬ Q ^ 2 ∣ Nat.fib n ∧ Nat.fib n ∣ safe.prod ^ 6 := by decide
  have hrow : q ∈ rows.map Prod.fst := hcase
  obtain ⟨⟨Q, P⟩, hmem, rfl⟩ := List.mem_map.mp hrow
  obtain ⟨⟨hP, h0, h1⟩, hmin, htable⟩ := data _ hmem
  exact empty_of_exception_table hq (pisano_eq_of_certificate hP ⟨h0, h1⟩ hmin) _
    (fun a ha => ⟨prime_entries a (List.mem_filter.mp ha).1, of_decide_eq_true (List.mem_filter.mp ha).2⟩)
    htable

-- A prime factor at the period witnesses the entire zero class, including index zero.
lemma zero_class_of_period_factor {q P p : ℕ} (hperiod : pisano q = P) (hP : 0 < P)
    (hp : p.Prime) (hmod : p ≡ 1 [MOD q]) (hdiv : p ∣ Nat.fib P) : 0 ∈ S q := by
  refine ⟨hperiod ▸ hP, ?_⟩
  intro m hm
  rw [hperiod] at hm
  have hqm : q ∣ Nat.totient p := by rw [Nat.totient_prime hp]; exact hmod.symm.dvd'
  exact hqm.trans (Nat.totient_dvd_of_dvd (hdiv.trans (Nat.fib_dvd _ _ (Nat.modEq_zero_iff_dvd.mp hm))))

lemma aligned_witness_of_checked_period {q P p : ℕ} (hP : 0 < P)
    (hstart : Nat.fib P ≡ 0 [MOD q] ∧ Nat.fib (P + 1) ≡ 1 [MOD q])
    (hmin : ∀ k : Fin P, 0 < k.val →
      ¬ (Nat.fib k.val ≡ 0 [MOD q] ∧ Nat.fib (k.val + 1) ≡ 1 [MOD q]))
    (hp : p.Prime) (hc : p ≡ 1 [MOD q]) (hd : p ∣ Nat.fib P) :
    0 ∈ S q ∧ ∃ w : ℕ, w.Prime ∧ w ≡ 1 [MOD q] ∧ rankOfApparition w ∣ pisano q := by
  have period := pisano_eq_of_certificate hP hstart hmin
  refine ⟨zero_class_of_period_factor period hP hp hc hd, p, hp, hc, ?_⟩
  rw [period]
  exact rank_dvd_index hP hd

lemma small_positive_classes {q : ℕ} (h : q = 3 ∨ q = 5 ∨ q = 23) :
    0 ∈ S q ∧ ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD q] ∧ rankOfApparition p ∣ pisano q := by
  rcases h with rfl | rfl | rfl
  · apply aligned_witness_of_checked_period (P := 8) (p := 7) <;> decide
  · apply aligned_witness_of_checked_period (P := 20) (p := 11) <;> decide
  · apply aligned_witness_of_checked_period (P := 48) (p := 47) <;> decide

-- A fixed divisor works on a whole class exactly when it divides the gcd-index term.
lemma divides_class_iff {b r P : ℕ} :
    (∀ m : ℕ, m ≡ r [MOD P] → b ∣ Nat.fib m) ↔ b ∣ Nat.fib (r.gcd P) := by
  constructor
  · intro h
    have hnext : r + P ≡ r [MOD P] := by simp [Nat.ModEq]
    have hd := Nat.dvd_gcd (h r rfl) (h _ hnext)
    simpa only [← Nat.fib_gcd, Nat.gcd_self_add_right] using hd
  · intro hg m hm
    have hm0 := (hm.of_dvd (Nat.gcd_dvd_right r P)).trans (Nat.gcd_dvd_left r P).modEq_zero_nat
    exact hg.trans (Nat.fib_dvd _ _ (Nat.modEq_zero_iff_dvd.mp hm0))

-- The finite-pool argument in board note 93655 gives a single member of the same pool.
lemma finite_cover_has_uniform_witness (W : Finset ℕ) {q r P : ℕ} (hP : 0 < P)
    (cover : ∀ m : ℕ, 0 < m → m ≡ r [MOD P] →
      ∃ b ∈ W, q ∣ Nat.totient b ∧ b ∣ Nat.fib m) :
    ∃ b ∈ W, q ∣ Nat.totient b ∧ ∀ m : ℕ, m ≡ r [MOD P] → b ∣ Nat.fib m := by
  obtain ⟨b, hb, hq, hg⟩ := finite_fib_witness_at_gcd W hP cover
  exact ⟨b, hb, hq, divides_class_iff.mpr hg⟩

lemma good_residue_of_common_index {q p r d : ℕ} (hr : r < pisano q)
    (hp : p.Prime) (hc : p ≡ 1 [MOD q]) (hd : p ∣ Nat.fib d)
    (hdr : d ∣ r) (hdP : d ∣ pisano q) : r ∈ S q := by
  have hqt : q ∣ Nat.totient p := by rw [Nat.totient_prime hp]; exact hc.symm.dvd'
  have hg := hd.trans (Nat.fib_dvd _ _ (Nat.dvd_gcd hdr hdP))
  exact ⟨hr, fun m hm => hqt.trans (Nat.totient_dvd_of_dvd (divides_class_iff.mpr hg m hm))⟩

lemma good_residues_three : S 3 = {0} := by
  have hP : pisano 3 = 8 := pisano_eq_of_certificate (by decide) (by decide) (by decide)
  ext r
  constructor
  · intro hr
    change r = 0
    by_contra hn
    have limit : r < 8 := hP ▸ hr.1
    let safe : List ℕ := [2, 3, 5, 557, 2417]
    have table : ∀ j : Fin 8, j.val ≠ 0 → ∃ t : Fin 4, let n := j.val + t.val * 8
        0 < n ∧ ¬ 3 ^ 2 ∣ Nat.fib n ∧ Nat.fib n ∣ safe.prod ^ 3 := by decide
    obtain ⟨t, hpos, hs, hd⟩ := table ⟨r, limit⟩ hn
    have hpr : ∀ a ∈ safe, Nat.Prime a ∧ ¬ a ≡ 1 [MOD 3] := by
      norm_num [safe, List.forall_mem_cons, Nat.ModEq]
    have bad := totient_exception_of_factors (by decide : Nat.Prime 3) hpos safe hpr hs hd
    exact bad (hr.2 _ (by rw [hP]; exact Nat.add_mul_modulus_modEq_iff.mpr rfl))
  · rintro rfl
    exact (small_positive_classes (Or.inl rfl)).1

-- The witness 11 covers the two multiples of ten. An exception table leaves
-- residue 15 as the only other candidate modulo the period 20.
lemma good_residue_bounds_five :
    ({0, 10} : Set ℕ) ⊆ S 5 ∧ S 5 ⊆ ({0, 10, 15} : Set ℕ) := by
  have hP : pisano 5 = 20 := pisano_eq_of_certificate (by decide) (by decide) (by decide)
  constructor
  · intro r hr
    change r = 0 ∨ r = 10 at hr
    rcases hr with rfl | rfl
    · exact (small_positive_classes (Or.inr (Or.inl rfl))).1
    · apply good_residue_of_common_index (p := 11) (d := 10) <;> first | decide | (rw [hP]; decide)
  · intro r hr
    change r = 0 ∨ r = 10 ∨ r = 15
    by_contra hn
    let safe : List ℕ := [2, 3, 5, 7, 13, 17, 19, 29, 37, 47, 89, 113, 233, 1597]
    have table : ∀ j : Fin 20, ¬ (j.val = 0 ∨ j.val = 10 ∨ j.val = 15) →
        ∃ t : Fin 4, let n := j.val + t.val * 20
        0 < n ∧ ¬ 5 ^ 2 ∣ Nat.fib n ∧ Nat.fib n ∣ safe.prod ^ 6 := by decide
    have limit : r < 20 := hP ▸ hr.1
    obtain ⟨t, hpos, hs, hd⟩ := table ⟨r, limit⟩ hn
    have hpr : ∀ a ∈ safe, Nat.Prime a ∧ ¬ a ≡ 1 [MOD 5] := by
      norm_num [safe, List.forall_mem_cons, Nat.ModEq]
    have bad := totient_exception_of_factors (by decide : Nat.Prime 5) hpos safe hpr hs hd
    exact bad (hr.2 _ (by rw [hP]; exact Nat.add_mul_modulus_modEq_iff.mpr rfl))

lemma period_fifty_three : pisano 53 = 108 :=
  pisano_eq_of_certificate (by decide) (by decide) (by decide)

-- These are exactly the classes certified by the particular witness 107.
set_option maxRecDepth 3000 in
lemma witness_classes_fifty_three {r : ℕ} (hr : r < pisano 53) :
    (∀ m : ℕ, m ≡ r [MOD pisano 53] → 107 ∣ Nat.fib m) ↔ r ∈ ([0, 36, 72] : List ℕ) := by
  rw [divides_class_iff, period_fifty_three]
  have table : ∀ j : Fin 108, 107 ∣ Nat.fib (j.val.gcd 108) ↔
      j.val ∈ ([0, 36, 72] : List ℕ) := by decide
  exact table ⟨r, period_fifty_three ▸ hr⟩

lemma good_residues_fifty_three {r : ℕ} (h : r ∈ ([0, 36, 72] : List ℕ)) : r ∈ S 53 := by
  have table : ∀ j ∈ ([0, 36, 72] : List ℕ), j < 108 ∧ 36 ∣ j := by decide
  obtain ⟨hr, hd⟩ := table r h
  exact good_residue_of_common_index (p := 107) (d := 36) (period_fifty_three ▸ hr)
    (by decide) (by decide) (by decide) hd (period_fifty_three ▸ (by decide))

lemma converse_fifty_three :
    ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD 53] ∧ rankOfApparition p ∣ pisano 53 := by
  rw [period_fifty_three]
  exact ⟨107, by decide, by decide, rank_dvd_index (by decide) (by decide)⟩

lemma nonempty_through_41 {q : ℕ} (hq : q.Prime) (hodd : q ≠ 2) (hbound : q ≤ 41) :
    (S q).Nonempty ↔ q = 3 ∨ q = 5 ∨ q = 23 := by
  constructor
  · intro hS
    by_contra h
    have classify : ∀ t : Fin 42, t.val.Prime → t.val ≠ 2 →
        ¬ (t.val = 3 ∨ t.val = 5 ∨ t.val = 23) →
        t.val ∈ ([7, 11, 13, 17, 19, 29, 31, 37, 41, 43, 47] : List ℕ) := by decide
    rw [small_empty_classes hq (classify ⟨q, by omega⟩ hq hodd h)] at hS
    exact hS.elim fun _ he => he.elim
  · exact fun h => ⟨0, (small_positive_classes h).1⟩

lemma converse_through_41 {q : ℕ} (hq : q.Prime) (hodd : q ≠ 2) (hbound : q ≤ 41)
    (hS : (S q).Nonempty) :
    ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD q] ∧ rankOfApparition p ∣ pisano q := by
  exact (small_positive_classes ((nonempty_through_41 hq hodd hbound).mp hS)).2

lemma nonempty_through_31 {q : ℕ} (hq : q.Prime) (hodd : q ≠ 2) (hbound : q ≤ 31) :
    (S q).Nonempty ↔ q = 3 ∨ q = 5 ∨ q = 23 :=
  nonempty_through_41 hq hodd (by omega)

lemma converse_through_31 {q : ℕ} (hq : q.Prime) (hodd : q ≠ 2) (hbound : q ≤ 31)
    (hS : (S q).Nonempty) :
    ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD q] ∧ rankOfApparition p ∣ pisano q :=
  converse_through_41 hq hodd (by omega) hS

lemma nonempty_through_53 {q : ℕ} (hq : q.Prime) (hodd : q ≠ 2) (hbound : q ≤ 53) :
    (S q).Nonempty ↔ q = 3 ∨ q = 5 ∨ q = 23 ∨ q = 53 := by
  by_cases low : q ≤ 41
  · rw [nonempty_through_41 hq hodd low]
    omega
  by_cases eq : q = 53
  · subst q
    exact ⟨fun _ => by simp, fun _ => ⟨0, good_residues_fifty_three (by decide)⟩⟩
  have table : ∀ j : Fin 54, j.val.Prime → 41 < j.val → j.val ≠ 53 →
      j.val ∈ ([7, 11, 13, 17, 19, 29, 31, 37, 41, 43, 47] : List ℕ) := by decide
  rw [small_empty_classes hq (table ⟨q, by omega⟩ hq (Nat.lt_of_not_ge low) eq)]
  simp only [Set.not_nonempty_empty, false_iff]
  omega

lemma converse_through_53 {q : ℕ} (hq : q.Prime) (hodd : q ≠ 2) (hbound : q ≤ 53)
    (hS : (S q).Nonempty) :
    ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD q] ∧ rankOfApparition p ∣ pisano q := by
  by_cases low : q ≤ 41
  · exact converse_through_41 hq hodd low hS
  have cases := (nonempty_through_53 hq hodd hbound).mp hS
  have eq : q = 53 := by omega
  exact eq ▸ converse_fifty_three

theorem main : H1 → H2 → type_of% @OMA.S_arxiv_2604_17847.main := by
  intro finiteCover exceptional q hq hodd hS
  by_cases hsmall : q ≤ 53
  · exact converse_through_53 hq hodd hsmall hS
  have hlarge : 53 < q := by omega
  obtain ⟨r, hr⟩ := hS
  have hP : 0 < pisano q := Nat.zero_lt_of_lt hr.1
  have descend : q ∣ Nat.totient (Nat.fib (pisano q)) := by
    by_contra hbad
    exact hbad ((finite_prime_cover_iff hq hP).mp
      (finiteCover q r hq hlarge hr (fixed_rank_family hq hr hbad)))
  rcases totient_fib_witness hq descend with hsquare | hwitness
  · exact exceptional q hq hlarge hsquare
  · exact hwitness

end OMA.R_arxiv_2604_17847_R1
