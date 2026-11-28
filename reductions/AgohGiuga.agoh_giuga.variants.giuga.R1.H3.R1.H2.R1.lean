import OMAReductions.R_AgohGiuga_agoh_giuga_variants_giuga_R1_H3_R1

/-!
For the higher-index branch of the two-factor Giuga reduction, reconstruct the original
squarefree integer. Its reciprocal sum minus the reciprocal of the product is an
integer at least two. The converse uses the two-factor reconstruction of Borwein et al.
The scaled reciprocal bound forces both completion primes above 11600.
The completion conditions then force the gap to be at least 81.
-/

namespace OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R1_H3_R1_H2_R1

open Finset

/-- Exclude index two. -/
def H1 : Prop :=
  ∀ n : ℕ, n.Composite → Odd n → Squarefree n →
    (∀ r ∈ n.primeFactors, (r - 1) ∣ n - 1) →
    (∑ r ∈ n.primeFactors, n / r) ≠ n * 2 + 1

/-- Exclude the indices above two. -/
def H2 : Prop :=
  ∀ n : ℕ, n.Composite → Odd n → Squarefree n →
    (∀ r ∈ n.primeFactors, (r - 1) ∣ n - 1) →
    ∀ k : ℕ, 3 ≤ k → (∑ r ∈ n.primeFactors, n / r) ≠ n * k + 1

section Proof

private theorem numerator_mul_prime {a b : ℕ} (ha : 0 < a) (hb : b.Prime)
    (hnot : b ∉ a.primeFactors) :
    (∑ r ∈ (a * b).primeFactors, a * b / r) =
      b * (∑ r ∈ a.primeFactors, a / r) + a := by
  rw [Nat.primeFactors_mul ha.ne' hb.ne_zero, hb.primeFactors, Finset.union_comm]
  simp only [Finset.singleton_union, Finset.sum_insert hnot, Nat.mul_div_cancel _ hb.pos,
    Finset.mul_sum]
  rw [add_comm]
  congr 1
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [mul_comm a b, Nat.mul_div_assoc b (Nat.dvd_of_mem_primeFactors hr)]

private theorem pair_reconstruction {m p q g d e : ℕ} (hg : 0 < g)
    (hd : m + d = g * p) (he : m + e = g * q) (hprod : d * e + g = m * m) :
    g * (p * q) + 1 = m * p + m * q := by
  apply Nat.eq_of_mul_eq_mul_left hg
  nlinarith only [congrArg₂ (· * ·) hd he, congrArg (m * ·) hd, congrArg (m * ·) he, hprod]

private theorem odd_prime_of_large {p : ℕ} (hp : p.Prime) (hp2 : 2 < p) : Odd p :=
  Nat.odd_iff.mpr ((Nat.Prime.mod_two_eq_one_iff_ne_two hp).mpr (by omega))

private theorem korselt_of_pair {m p q g d e : ℕ} (hm : 0 < m) (hp : p.Prime) (hq : q.Prime)
    (hd : m + d = g * p) (he : m + e = g * q) (hdq : (q - 1) ∣ d)
    (hep : (p - 1) ∣ e) (hgap : g * (p * q) + 1 = m * p + m * q)
    (hold : ∀ r ∈ m.primeFactors, (r - 1) ∣ m * p * q - 1) :
    ∀ r ∈ (m * p * q).primeFactors, (r - 1) ∣ m * p * q - 1 := by
  have hdq' : d * q + 1 = m * p := by
    have := congrArg (· * q) hd
    nlinarith only [this, hgap]
  have hep' : e * p + 1 = m * q := by
    have := congrArg (· * p) he
    nlinarith only [this, hgap]
  intro r hr
  rw [Nat.primeFactors_mul (Nat.mul_pos hm hp.pos).ne' hq.ne_zero, hq.primeFactors,
    Nat.primeFactors_mul hm.ne' hp.ne_zero, hp.primeFactors] at hr
  simp only [Finset.mem_union, Finset.mem_singleton] at hr
  rcases hr with (hr | hr) | hr
  · exact hold r hr
  · subst r
    have h : m * p * q - 1 = (e * p) * p + (p - 1) := by
      rw [mul_right_comm m p q, ← hep', add_mul, one_mul, Nat.add_sub_assoc hp.one_le]
    rw [h]
    exact Nat.dvd_add (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hep p) p) (dvd_refl _)
  · subst r
    have h : m * p * q - 1 = (d * q) * q + (q - 1) := by
      rw [← hdq', add_mul, one_mul, Nat.add_sub_assoc hq.one_le]
    rw [h]
    exact Nat.dvd_add (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hdq q) q) (dvd_refl _)

/-- Reconstruct the index of the full candidate directly from the cofactor numerator. -/
theorem reconstruct {m p q g d e : ℕ} (hm : 1 < m) (hmo : Odd m) (hmf : Squarefree m)
    (hg : g = m - (∑ r ∈ m.primeFactors, m / r) % m)
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (horder : ∀ r ∈ m.primeFactors, r < p)
    (hd : m + d = g * p) (he : m + e = g * q) (hprod : d * e + g = m * m)
    (hdq : (q - 1) ∣ d) (hep : (p - 1) ∣ e)
    (hold : ∀ r ∈ m.primeFactors, (r - 1) ∣ m * p * q - 1) :
    let n := m * p * q
    let D := ∑ r ∈ m.primeFactors, m / r
    n.Composite ∧ Odd n ∧ Squarefree n ∧
      (∀ r ∈ n.primeFactors, (r - 1) ∣ n - 1) ∧
      (∑ r ∈ n.primeFactors, n / r) = n * (D / m + 1) + 1 := by
  let D := ∑ r ∈ m.primeFactors, m / r
  change g = m - D % m at hg
  have hm0 : 0 < m := by omega
  have hmp0 : 0 < m * p := Nat.mul_pos hm0 hp.pos
  have hmod := Nat.mod_lt D hm0
  have hg0 : 0 < g := by omega
  have hD : D + g = m * (D / m + 1) := by
    rw [mul_add, mul_one]
    have := Nat.div_add_mod D m
    omega
  obtain ⟨r, hr⟩ := Nat.exists_prime_and_dvd (show m ≠ 1 by omega)
  have hrM : r ∈ m.primeFactors := Nat.mem_primeFactors.mpr ⟨hr.1, hr.2, hm0.ne'⟩
  have hp2 : 2 < p := hr.1.two_le.trans_lt (horder r hrM)
  have hpn : p ∉ m.primeFactors := fun h => (horder p h).false
  have hqn : q ∉ (m * p).primeFactors := by
    rw [Nat.primeFactors_mul hm0.ne' hp.ne_zero, hp.primeFactors, Finset.mem_union,
      Finset.mem_singleton]
    rintro (h | h)
    · exact (horder q h).not_gt hpq
    · omega
  have hsfp : Squarefree (m * p) :=
    (Nat.squarefree_mul ((hp.coprime_iff_not_dvd.mpr
      (fun h => hpn (Nat.mem_primeFactors.mpr ⟨hp, h, hm0.ne'⟩))).symm)).mpr
      ⟨hmf, hp.squarefree⟩
  have hsfn : Squarefree (m * p * q) :=
    (Nat.squarefree_mul ((hq.coprime_iff_not_dvd.mpr
      (fun h => hqn (Nat.mem_primeFactors.mpr ⟨hq, h, hmp0.ne'⟩))).symm)).mpr
      ⟨hsfp, hq.squarefree⟩
  have hcomp : (m * p * q).Composite := by
    have hn : q < m * p * q := by
      simpa only [one_mul] using Nat.mul_lt_mul_of_pos_right
        (show 1 < m * p by nlinarith only [hm, hp.two_le, hmp0]) hq.pos
    refine ⟨by omega, fun hnP => ?_⟩
    rcases (Nat.dvd_prime hnP).mp (dvd_mul_left q (m * p)) with h | h
    · omega
    · omega
  have hgap := pair_reconstruction hg0 hd he hprod
  refine ⟨hcomp, (hmo.mul (odd_prime_of_large hp hp2)).mul
    (odd_prime_of_large hq (hp2.trans hpq)), hsfn,
    korselt_of_pair hm0 hp hq hd he hdq hep hgap hold, ?_⟩
  rw [numerator_mul_prime hmp0 hq hqn, numerator_mul_prime hm0 hp hpn]
  change q * (p * D + m) + m * p = m * p * q * (D / m + 1) + 1
  nlinarith only [congrArg (· * (p * q)) hD, hgap]

private theorem sufficient_of_indices (h1 : H1) (h2 : H2) :
    OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R1_H3_R1.H2 := by
  intro m hm hmo hmf D hD g hg _ _ d hd0 hdvd e _ hgd hge p q hp hq hpq _
    horder hdq hep hold
  have hgD : g = m - D % m := rfl
  have hgm : g ≤ m := Nat.sub_le _ _
  have hm0 : 0 < m := by omega
  have hgm2 := hgm.trans (Nat.le_mul_of_pos_right m hm0)
  have hde : d * e + g = m * m := by
    have h := Nat.mul_div_cancel' hdvd
    change d * ((m * m - g) / d) = m * m - g at h
    change d * ((m * m - g) / d) + g = m * m
    omega
  have hdp : m + d = g * p := (Nat.mul_div_cancel' hgd).symm
  have heq : m + e = g * q := (Nat.mul_div_cancel' hge).symm
  obtain ⟨hcomp, hodd, hsf, hk, hsum⟩ :=
    reconstruct hm hmo hmf hgD hp hq hpq horder hdp heq hde hdq hep hold
  have hindex : 2 ≤ D / m + 1 := by
    have := Nat.div_pos hD hm0
    omega
  change (∑ r ∈ (m * p * q).primeFactors, m * p * q / r) =
    m * p * q * (D / m + 1) + 1 at hsum
  by_cases hh : D / m + 1 = 2
  · rw [hh] at hsum
    exact h1 _ hcomp hodd hsf hk hsum
  · exact h2 _ hcomp hodd hsf hk (D / m + 1) (by omega) hsum

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
private theorem small_prime_sum :
    (∑ r ∈ (range 11601).filter (fun r => r.minFac = r ∧ 2 < r), (1000000 + r - 1) / r)
      ≤ 1999300 := by
  decide +kernel

private theorem weighted_cofactor {n r : ℕ} (hr : 0 < r) (hd : r ∣ n) :
    1000000 * (n / r) ≤ ((1000000 + r - 1) / r) * n := by
  have hceil : 1000000 ≤ r * ((1000000 + r - 1) / r) := by
    have := Nat.div_add_mod (1000000 + r - 1) r
    have := Nat.mod_lt (1000000 + r - 1) hr
    omega
  calc
    _ ≤ (r * ((1000000 + r - 1) / r)) * (n / r) :=
      Nat.mul_le_mul_right _ hceil
    _ = _ := by rw [mul_comm r, mul_assoc, Nat.mul_div_cancel' hd]

/-- At least two prime factors of an odd candidate of index at least two exceed 11600. -/
theorem second_prime_large {n q k : ℕ} (hn : 0 < n) (hodd : Odd n) (hk : 2 ≤ k)
    (hsum : (∑ r ∈ n.primeFactors, n / r) = n * k + 1)
    (hqm : q ∈ n.primeFactors) :
    ∃ p ∈ n.primeFactors.erase q, 11600 < p := by
  by_contra! h
  let w := fun r : ℕ => (1000000 + r - 1) / r
  let F := (range 11601).filter fun r => r.minFac = r ∧ 2 < r
  have hsmall (r : ℕ) (hr : r ∈ n.primeFactors) (hrle : r ≤ 11600) : r ∈ F := by
    have hp := Nat.prime_of_mem_primeFactors hr
    have hr2 : 2 < r := by
      by_contra! hc
      have heq : r = 2 := le_antisymm hc hp.two_le
      have hd := Nat.dvd_of_mem_primeFactors hr
      rw [heq] at hd
      have := Nat.odd_iff.mp hodd
      omega
    exact mem_filter.mpr ⟨mem_range.mpr (by omega), hp.minFac_eq, hr2⟩
  have hF : n.primeFactors.erase q ⊆ F := fun r hr => hsmall r (mem_of_mem_erase hr) (h r hr)
  have hbound : (∑ r ∈ F, w r) ≤ 1999300 := small_prime_sum
  have hboundn : (∑ r ∈ F, w r * n) ≤ 1999300 * n := by
    rw [← Finset.sum_mul]
    exact Nat.mul_le_mul_right _ hbound
  have hsumw (S : Finset ℕ) (hS : S ⊆ n.primeFactors) :
      1000000 * (∑ r ∈ S, n / r) ≤ ∑ r ∈ S, w r * n := by
    rw [Finset.mul_sum]
    exact sum_le_sum fun r hr =>
      weighted_cofactor (Nat.prime_of_mem_primeFactors (hS hr)).pos
        (Nat.dvd_of_mem_primeFactors (hS hr))
  have hsumlo : 2 * n < ∑ r ∈ n.primeFactors, n / r := by
    rw [hsum, mul_comm n k]
    exact Nat.lt_succ_of_le (Nat.mul_le_mul_right _ hk)
  have hl : 2000000 * n < 1000000 * (∑ r ∈ n.primeFactors, n / r) := by
    calc
      _ = 1000000 * (2 * n) := by ring
      _ < _ := Nat.mul_lt_mul_of_pos_left hsumlo (by decide)
  by_cases hq : q ≤ 11600
  · have hF' : n.primeFactors ⊆ F := by
      intro r hr
      by_cases heq : r = q
      · exact heq ▸ hsmall q hqm hq
      · exact hF (mem_erase.mpr ⟨heq, hr⟩)
    exact hl.not_ge ((hsumw _ Subset.rfl).trans
      ((sum_le_sum_of_subset hF').trans (hboundn.trans (by omega))))
  · have hqw : w q ≤ 87 := by
      dsimp [w]
      exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega))
    have hqterm := (weighted_cofactor (Nat.prime_of_mem_primeFactors hqm).pos
      (Nat.dvd_of_mem_primeFactors hqm)).trans (Nat.mul_le_mul_right n hqw)
    have hh := (hsumw _ (erase_subset _ _)).trans ((sum_le_sum_of_subset hF).trans hboundn)
    rw [← add_sum_erase _ _ hqm, Nat.mul_add] at hl
    omega

/-- The two Korselt divisibilities force a gap of at least 81 if the smaller completion
prime exceeds 11600. -/
theorem large_pair_gap {m p q g d e : ℕ}
    (hm : 1 ≤ m) (hp : p.Prime) (hq : q.Prime) (hpq : p < q) (hqm : q < m)
    (hpLarge : 11600 < p) (hg : 0 < g) (hg4 : g % 4 = 1)
    (hd : m + d = g * p) (he : m + e = g * q)
    (hdq : (q - 1) ∣ d) (hep : (p - 1) ∣ e)
    (hgap : g * (p * q) + 1 = m * p + m * q) :
    81 ≤ g := by
  obtain ⟨a, ha⟩ := hdq
  have hag : a + 2 ≤ g := by
    by_contra! h
    have hprod : (g - 1) * p ≤ (q - 1) * a := by
      rw [mul_comm (g - 1) p]
      exact Nat.mul_le_mul (by omega) (by omega)
    have hpG : (g - 1) * p + p = g * p := by
      calc
        _ = (g - 1 + 1) * p := by rw [Nat.add_mul, one_mul]
        _ = _ := by rw [Nat.sub_add_cancel hg]
    omega
  let t := (p - 1).gcd (q - 1)
  have htp : t ∣ p - 1 := Nat.gcd_dvd_left _ _
  have htq : t ∣ q - 1 := Nat.gcd_dvd_right _ _
  have htd : t ∣ d := htq.trans ⟨a, ha⟩
  have hdq' : d * q + 1 = m * p := by
    have := congrArg (· * q) hd
    nlinarith only [this, hgap]
  have htm : t ∣ m - 1 := by
    have hdmp : t ∣ m * p - 1 := by
      rw [← hdq', Nat.add_sub_cancel]
      exact dvd_mul_of_dvd_left htd _
    have hmul : m * p - 1 = m * (p - 1) + (m - 1) := by
      rw [Nat.mul_sub, mul_one]
      have := Nat.le_mul_of_pos_right m hp.pos
      omega
    rw [hmul] at hdmp
    exact (Nat.dvd_add_right (dvd_mul_of_dvd_right htp m)).mp hdmp
  have htg : t ∣ g - 1 := by
    have hgp : t ∣ g * p - 1 := by
      rw [← hd, show m + d - 1 = (m - 1) + d by omega]
      exact Nat.dvd_add htm htd
    have hmul : g * p - 1 = g * (p - 1) + (g - 1) := by
      rw [Nat.mul_sub, mul_one]
      have := Nat.le_mul_of_pos_right g hp.pos
      omega
    rw [hmul] at hgp
    exact (Nat.dvd_add_right (dvd_mul_of_dvd_right htp g)).mp hgp
  have hratio : e + g * (p - 1) = (g + a) * (q - 1) := by
    nlinarith only [hd, he, ha, congrArg (g * ·) (Nat.sub_add_cancel hp.one_le),
      congrArg (g * ·) (Nat.sub_add_cancel hq.one_le)]
  have hdiv : (p - 1) ∣ (g + a) * (q - 1) :=
    hratio ▸ Nat.dvd_add hep (dvd_mul_of_dvd_right (dvd_refl (p - 1)) g)
  have hfinal : (p - 1) ∣ (g + a) * (g - 1) :=
    (Nat.dvd_mul_gcd_iff_dvd_mul.mpr hdiv).trans (Nat.mul_dvd_mul_left _ htg)
  have hpbound := Nat.le_of_dvd (Nat.mul_pos (by omega) (by omega) :
    0 < (g + a) * (g - 1)) hfinal
  by_contra! hgsmall
  have hg77 : g ≤ 77 := by omega
  have := Nat.mul_le_mul (show g + a ≤ 152 by omega) (show g - 1 ≤ 76 by omega)
  omega

private theorem cofactor_korselt {a r : ℕ} (ha : 0 < a) (hr : 1 ≤ r)
    (h : (r - 1) ∣ a * r - 1) : (r - 1) ∣ a - 1 := by
  have hsplit : a * r - 1 = a * (r - 1) + (a - 1) := by
    rw [Nat.mul_sub, mul_one]
    have := Nat.le_mul_of_pos_right a (by omega : 0 < r)
    omega
  rw [hsplit] at h
  exact (Nat.dvd_add_right (dvd_mul_of_dvd_right (dvd_refl (r - 1)) a)).mp h

private theorem next_gap {D m p q k : ℕ} (hm : 0 < m) (hp : 2 ≤ p) (hpq : p < q)
    (hsum : D * (p * q) + m * p + m * q = m * (p * q) * k + 1) :
    let g := m - D % m
    g * (p * q) + 1 = m * p + m * q := by
  have hpq0 : 0 < p * q := Nat.mul_pos (by omega) (by omega)
  have hDle : D ≤ m * k := by
    by_contra! h
    have hprod := Nat.mul_le_mul_right (p * q) (show m * k + 1 ≤ D by omega)
    rw [add_mul, one_mul, mul_right_comm m k (p * q)] at hprod
    have := Nat.le_mul_of_pos_left q hm
    omega
  let t := m * k - D
  have htD : D + t = m * k := Nat.add_sub_of_le hDle
  have htadd : t * (p * q) + 1 = m * p + m * q := by
    rw [mul_right_comm m (p * q) k, ← htD, add_mul] at hsum
    omega
  have ht : 0 < t := by
    by_contra! h
    have h0 : t = 0 := by omega
    rw [h0, zero_mul, zero_add] at htadd
    have := Nat.le_mul_of_pos_left q hm
    omega
  have hlt : p + q < p * q := by
    have := Nat.mul_le_mul_right q hp
    omega
  have htm : t < m := by
    by_contra! h
    have hh := Nat.mul_le_mul_right (p * q) h
    have hh' := Nat.mul_lt_mul_of_pos_left hlt hm
    rw [Nat.mul_add] at hh'
    omega
  have hmod : (D % m + t) % m = 0 := by
    rw [Nat.mod_add_mod, htD, Nat.mul_mod_right]
  have hrem := Nat.mod_lt D hm
  have hsumge : m ≤ D % m + t := by
    by_contra! h
    rw [Nat.mod_eq_of_lt h] at hmod
    omega
  rw [Nat.mod_eq_sub_mod hsumge, Nat.mod_eq_of_lt (by omega)] at hmod
  have heq : m - D % m = t := by omega
  exact heq ▸ htadd

private theorem at_least_two_factors {n : ℕ} (hc : n.Composite) (hsf : Squarefree n) :
    2 ≤ n.primeFactors.card := by
  have hprod := Nat.prod_primeFactors_of_squarefree hsf
  have hn := hc.1
  by_contra! h
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (show n.primeFactors.card ≤ 1 by omega) with h0 | h1
  · rw [Finset.card_eq_zero.mp h0, Finset.prod_empty] at hprod
    omega
  · obtain ⟨p, hp⟩ := Finset.card_eq_one.mp h1
    have hmem : p ∈ n.primeFactors := by rw [hp]; simp
    have hprime := Nat.prime_of_mem_primeFactors hmem
    rw [hp, Finset.prod_singleton] at hprod
    exact hc.2 (hprod ▸ hprime)

private theorem high_index_gives_completion {n k : ℕ} (hc : n.Composite) (hno : Odd n)
    (hsf : Squarefree n) (hK : ∀ r ∈ n.primeFactors, (r - 1) ∣ n - 1)
    (hk : 2 ≤ k) (hsum : (∑ r ∈ n.primeFactors, n / r) = n * k + 1) :
    ¬ OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R1_H3_R1.H2 := by
  intro htarget
  have hn0 : 0 < n := Nat.pos_of_ne_zero hsf.ne_zero
  let P := n.primeFactors
  have hP : 2 ≤ P.card := at_least_two_factors hc hsf
  let q := P.max' (Finset.card_pos.mp (by omega))
  have hqM : q ∈ P := Finset.max'_mem _ _
  have hPe : (P.erase q).Nonempty := Finset.card_pos.mp (by rw [Finset.card_erase_of_mem hqM]; omega)
  let p := (P.erase q).max' hPe
  have hpE : p ∈ P.erase q := Finset.max'_mem _ _
  have hpM : p ∈ P := mem_of_mem_erase hpE
  have hpq : p < q :=
    lt_of_le_of_ne (Finset.le_max' _ _ hpM) (Finset.mem_erase.mp hpE).1
  have hp : p.Prime := Nat.prime_of_mem_primeFactors hpM
  have hq : q.Prime := Nat.prime_of_mem_primeFactors hqM
  have hpLarge : 11600 < p := by
    obtain ⟨r, hr, hrLarge⟩ := second_prime_large hn0 hno hk hsum hqM
    exact hrLarge.trans_le (Finset.le_max' _ _ hr)
  let T := (P.erase q).erase p
  let m := ∏ r ∈ T, r
  have hmF : m.primeFactors = T := Nat.primeFactors_prod fun r hr =>
    Nat.prime_of_mem_primeFactors (mem_of_mem_erase (mem_of_mem_erase hr))
  have hnEq : n = m * p * q := by
    calc
      n = ∏ r ∈ P, r := (Nat.prod_primeFactors_of_squarefree hsf).symm
      _ = (∏ r ∈ P.erase q, r) * q := (Finset.prod_erase_mul _ _ hqM).symm
      _ = m * p * q := congrArg (· * q) (Finset.prod_erase_mul _ _ hpE).symm
  have hsq : Squarefree (m * p * q) := hnEq ▸ hsf
  have hmf : Squarefree m := hsq.of_mul_left.of_mul_left
  have hm0 : 0 < m := Nat.pos_of_ne_zero hmf.ne_zero
  have hmo : Odd m := (Nat.odd_mul.mp (Nat.odd_mul.mp (hnEq ▸ hno : Odd (m * p * q))).1).1
  have hpn : p ∉ m.primeFactors := by rw [hmF]; exact notMem_erase p _
  have hqn : q ∉ (m * p).primeFactors := by
    rw [Nat.primeFactors_mul hm0.ne' hp.ne_zero, hp.primeFactors, mem_union, mem_singleton, hmF]
    rintro (hr | hr)
    · exact (mem_erase.mp (mem_of_mem_erase hr)).1 rfl
    · omega
  let D := ∑ r ∈ m.primeFactors, m / r
  have hsum' := hsum
  rw [hnEq, numerator_mul_prime (Nat.mul_pos hm0 hp.pos) hq hqn,
    numerator_mul_prime hm0 hp hpn] at hsum'
  change q * (p * D + m) + m * p = m * p * q * k + 1 at hsum'
  have hD : m ≤ D := by
    by_contra! h
    have hlt : p + q < p * q := by have := Nat.mul_le_mul_right q hp.two_le; omega
    have hle := Nat.mul_le_mul_right (p * q) (show D + 1 ≤ m by omega)
    have hh := Nat.mul_lt_mul_of_pos_left hlt hm0
    have h2 := Nat.mul_le_mul_left (m * p * q) hk
    nlinarith only [hle, hh, h2, hsum']
  have hm : 1 < m := by
    by_contra! h
    have hm1 : m = 1 := by omega
    have hD0 : D = 0 := by simp [D, hm1]
    omega
  let g := m - D % m
  have hg : 0 < g := by
    have := Nat.mod_lt D hm0
    dsimp [g]
    omega
  have hgap : g * (p * q) + 1 = m * p + m * q :=
    next_gap (k := k) hm0 hp.two_le hpq (by nlinarith only [hsum'])
  have hkp : (p - 1) ∣ m * q - 1 := cofactor_korselt (Nat.mul_pos hm0 hq.pos) hp.one_le
    (by simpa only [hnEq, mul_right_comm m p q] using hK p hpM)
  have hkq : (q - 1) ∣ m * p - 1 := cofactor_korselt (Nat.mul_pos hm0 hp.pos) hq.one_le
    (by simpa only [hnEq] using hK q hqM)
  obtain ⟨d, e, hd0, hde, hprod, hdp, heq, hdq, hep⟩ :=
    OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R1_H3_R1.pair_divisors hm0 hg hp hq hpq hgap hkp hkq
  have hqm : q < m := by
    have hdq' : d * q + 1 = m * p := by
      have := congrArg (· * q) hdp
      nlinarith only [this, hgap]
    by_contra! h
    have hle := Nat.le_of_dvd hd0 hdq
    have hpd : p ≤ d := by omega
    have hpq' := Nat.mul_le_mul_right q hpd
    have hmq := Nat.mul_le_mul_right p h
    rw [mul_comm q p] at hmq
    omega
  have hp2 : 2 ∣ p - 1 := by
    have := Nat.odd_iff.mp (odd_prime_of_large hp (by omega))
    omega
  have hq2 : 2 ∣ q - 1 := by
    have := Nat.odd_iff.mp (odd_prime_of_large hq (by omega))
    omega
  have h4 : 4 ∣ d * e := mul_dvd_mul (hq2.trans hdq) (hp2.trans hep)
  have hm4 : (m * m) % 4 = 1 := by
    obtain ⟨a, ha⟩ := hmo
    rw [ha, show (2 * a + 1) * (2 * a + 1) = 4 * (a * a + a) + 1 by ring]
    omega
  have hgm : g ≤ m := Nat.sub_le _ _
  have hgm2 := hgm.trans (Nat.le_mul_of_pos_right m hm0)
  have hprod' : d * e + g = m * m := by omega
  have hg4 : g % 4 = 1 := by omega
  have hgMin := large_pair_gap hm.le hp hq hpq hqm hpLarge hg hg4 hdp heq hdq hep hgap
  have hgCop : g.Coprime m := by
    have hgcd := Nat.gcd_dvd_left g m
    have hmc := Nat.gcd_dvd_right g m
    have hh := Nat.dvd_add (dvd_mul_of_dvd_left hmc p) (dvd_mul_of_dvd_left hmc q)
    rw [← hgap] at hh
    exact Nat.dvd_one.mp ((Nat.dvd_add_right (dvd_mul_of_dvd_left hgcd (p * q))).mp hh)
  have hdvd : d ∣ m * m - g := ⟨e, hprod.symm⟩
  have heEq : (m * m - g) / d = e := by rw [← hprod, Nat.mul_div_cancel_left e hd0]
  have hp' : (m + d) / g = p := by rw [hdp, Nat.mul_div_cancel_left p hg]
  have hq' : (m + e) / g = q := by rw [heq, Nat.mul_div_cancel_left q hg]
  have hOrder (r : ℕ) (hr : r ∈ m.primeFactors) : r < p := by
    rw [hmF] at hr
    exact lt_of_le_of_ne (Finset.le_max' _ _ (mem_of_mem_erase hr)) (mem_erase.mp hr).1
  have hOld (r : ℕ) (hr : r ∈ m.primeFactors) : (r - 1) ∣ m * p * q - 1 := by
    rw [hmF] at hr
    rw [← hnEq]
    exact hK r (mem_of_mem_erase (mem_of_mem_erase hr))
  have hcheck := htarget m hm hmo hmf hD (show 13 ≤ g by omega) hg4 hgCop d hd0 hdvd
  change d < (m * m - g) / d → _ at hcheck
  dsimp only at hcheck
  rw [heEq, hp', hq'] at hcheck
  exact hcheck hde ⟨p, hdp⟩ ⟨q, heq⟩ hp hq hpq hqm hOrder hdq hep hOld

/-- The remaining step is exactly the exclusion of odd Carmichael numbers of Giuga index at least two. -/
theorem criterion_equiv :
    (H1 ∧ H2) ↔ OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R1_H3_R1.H2 := by
  constructor
  · rintro ⟨h1, h2⟩
    exact sufficient_of_indices h1 h2
  · intro h
    constructor
    · intro n hc hno hsf hK hsum
      exact high_index_gives_completion hc hno hsf hK (by decide : 2 ≤ 2) hsum h
    · intro n hc hno hsf hK k hk hsum
      exact high_index_gives_completion hc hno hsf hK (by omega) hsum h

theorem main : H1 → H2 → OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R1_H3_R1.H2 :=
  fun h1 h2 => criterion_equiv.mp ⟨h1, h2⟩

end Proof

end OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R1_H3_R1_H2_R1
