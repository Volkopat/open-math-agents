import OMAReductions.R_AgohGiuga_agoh_giuga_variants_giuga_R3_H2_R1

namespace OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R3_H2_R1_H2_R1

open OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R3 (weight_mul_prime)

/-- The reciprocal mass of pairwise compatible odd primes forces a large
cardinality. The common multiple is a denominator for the reciprocal sum. -/
def H1 : Prop :=
  ∀ S : Finset ℕ, (∀ r ∈ S, r.Prime ∧ Odd r) →
    (∀ r ∈ S, ∀ s ∈ S, ¬ (r ∣ s - 1)) →
    ∀ n : ℕ, 0 < n → (∀ r ∈ S, r ∣ n) →
      2 * n < ∑ r ∈ S, n / r → 887038347 ≤ S.card

/-- The remaining exclusion for cofactors with at least 887038345 prime factors. -/
def H2 : Prop :=
  ∀ h x y : ℕ, 1 < h → Odd h → Squarefree h →
    887038347 ≤ h.primeFactors.card + 2 →
    let L := ∑ r ∈ h.primeFactors, h / r
    let A := h - L % h
    let p := (x + h) / A
    let q := (y + h) / A
    h ≤ L → 0 < x → x < y → x < h → x * y + A = h ^ 2 → h < 2 * A ^ 3 →
    A ∣ x + h → A ∣ y + h →
    p.Prime → q.Prime → (∀ r ∈ h.primeFactors, r < p) →
    p - 1 ∣ y → q - 1 ∣ x →
    ¬ (h.primeFactors.lcm (fun r => r - 1) ∣ h * p * q - 1)

private theorem primeFactors_append {m p : ℕ} (hm : 0 < m) (hp : p.Prime) :
    (m * p).primeFactors = insert p m.primeFactors := by
  rw [Nat.primeFactors_mul hm.ne' hp.ne_zero, hp.primeFactors, Finset.union_comm,
    Finset.singleton_union]

private theorem predecessor_dvd_of_product {n p m y : ℕ} (hp : 1 < p)
    (h₁ : n = p * m) (h₂ : p * y + 1 = m) (hd : p - 1 ∣ y) :
    p - 1 ∣ n - 1 := by
  obtain ⟨v, hv⟩ := hd
  have hlin : n = (p - 1) * (p * p * v) + p := by
    rw [h₁, ← h₂, hv]
    ring
  have hfactor : (p - 1) * (p * p * v + 1) = (p - 1) * (p * p * v) + (p - 1) := by
    ring
  exact ⟨p * p * v + 1, by omega⟩

private theorem reconstruction {h A p q x y : ℕ} (hA : 0 < A)
    (hx : A * p = x + h) (hy : A * q = y + h) (hxy : x * y + A = h ^ 2) :
    A * p * q + 1 = h * p + h * q := by
  have hprod : (x + h) * (y + h) = A * (A * p * q) := by
    rw [← hx, ← hy]
    ring
  have hcross : (x + h) * h + (y + h) * h = A * (h * p + h * q) := by
    rw [← hx, ← hy]
    ring
  apply Nat.eq_of_mul_eq_mul_left hA
  nlinarith only [hprod, hcross, hxy]

theorem main : H1 → H2 → OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R3_H2_R1.H2 := by
  classical
  intro hmass hlarge h x y hh hhOdd hhSq
  let L := ∑ r ∈ h.primeFactors, h / r
  let A := h - L % h
  let p := (x + h) / A
  let q := (y + h) / A
  change h ≤ L → 0 < x → x < y → x < h → x * y + A = h ^ 2 → h < 2 * A ^ 3 →
    A ∣ x + h → A ∣ y + h → p.Prime → q.Prime → (∀ r ∈ h.primeFactors, r < p) →
    p - 1 ∣ y → q - 1 ∣ x → ¬ (h.primeFactors.lcm (fun r => r - 1) ∣ h * p * q - 1)
  intro hL hx0 hxy hxlt hfact hbound hxD hyD hp hq hold hpd hqd hlcm
  have hh0 : 0 < h := by omega
  have hrem : L % h < h := Nat.mod_lt _ hh0
  have hA : 0 < A := by dsimp only [A]; omega
  have hx : A * p = x + h := by
    simpa only [p, mul_comm] using Nat.div_mul_cancel hxD
  have hy : A * q = y + h := by
    simpa only [q, mul_comm] using Nat.div_mul_cancel hyD
  have hpq : p < q := by
    apply Nat.lt_of_mul_lt_mul_left (a := A)
    rw [hx, hy]
    omega
  have hpNot : p ∉ h.primeFactors := fun hr => (lt_irrefl p) (hold p hr)
  have hqNot : q ∉ (h * p).primeFactors := by
    rw [primeFactors_append hh0 hp, Finset.mem_insert]
    rintro (he | he)
    · omega
    · exact (not_lt_of_ge hpq.le) (hold q he)
  have hcp : h.Coprime p := (hp.coprime_iff_not_dvd.mpr
    (fun hd => hpNot (Nat.mem_primeFactors.mpr ⟨hp, hd, hh0.ne'⟩))).symm
  have hhp : 0 < h * p := Nat.mul_pos hh0 hp.pos
  have hcq : (h * p).Coprime q := (hq.coprime_iff_not_dvd.mpr
    (fun hd => hqNot (Nat.mem_primeFactors.mpr ⟨hq, hd, hhp.ne'⟩))).symm
  obtain ⟨r, hr⟩ := Nat.nonempty_primeFactors.mpr hh
  have hrp := hold r hr
  have hr2 := (Nat.prime_of_mem_primeFactors hr).two_le
  have hpOdd : Odd p := hp.odd_of_ne_two (by omega)
  have hqOdd : Odd q := hq.odd_of_ne_two (by omega)
  let n := h * p * q
  have hn0 : 0 < n := Nat.mul_pos hhp hq.pos
  have hnOdd : Odd n := (hhOdd.mul hpOdd).mul hqOdd
  have hprime (s : ℕ) (hs : s ∈ n.primeFactors) : s.Prime ∧ Odd s := by
    have hsP := Nat.prime_of_mem_primeFactors hs
    exact ⟨hsP, hsP.odd_of_ne_two (fun he =>
      hnOdd.not_two_dvd_nat (he ▸ Nat.dvd_of_mem_primeFactors hs))⟩
  have hrec := reconstruction hA hx hy hfact
  have hpy : p * y + 1 = h * q := by
    have h : p * (y + h) = A * p * q := by rw [← hy]; ring
    nlinarith only [h, hrec]
  have hqx : q * x + 1 = h * p := by
    have h : q * (x + h) = A * p * q := by rw [← hx]; ring
    nlinarith only [h, hrec]
  have hpPred : p - 1 ∣ n - 1 :=
    predecessor_dvd_of_product hp.one_lt (by dsimp only [n]; ring) hpy hpd
  have hqPred : q - 1 ∣ n - 1 :=
    predecessor_dvd_of_product hq.one_lt (by dsimp only [n]; ring) hqx hqd
  have hnFactors : n.primeFactors = insert q (insert p h.primeFactors) := by
    change (h * p * q).primeFactors = _
    rw [primeFactors_append hhp hq, primeFactors_append hh0 hp]
  have hpred (s : ℕ) (hs : s ∈ n.primeFactors) : s - 1 ∣ n - 1 := by
    rw [hnFactors, Finset.mem_insert, Finset.mem_insert] at hs
    rcases hs with he | he | he
    · exact he.symm ▸ hqPred
    · exact he.symm ▸ hpPred
    · exact Finset.lcm_dvd_iff.mp hlcm s he
  have hcompatible (s : ℕ) (hs : s ∈ n.primeFactors)
      (t : ℕ) (ht : t ∈ n.primeFactors) : ¬ (s ∣ t - 1) := by
    intro hst
    have hd : s ∣ n - 1 := hst.trans (hpred t ht)
    have hdn : s ∣ n := Nat.dvd_of_mem_primeFactors hs
    have he : 1 + (n - 1) = n := by omega
    have hsum : s ∣ 1 + (n - 1) := by rw [he]; exact hdn
    exact (hprime s hs).1.not_dvd_one ((Nat.dvd_add_left hd).mp hsum)
  have hLdiv : 1 ≤ L / h := (Nat.le_div_iff_mul_le hh0).mpr (by simpa using hL)
  have hLA : 2 * h ≤ L + A := by
    have ha : L % h + A = h := by dsimp only [A]; omega
    have he := Nat.mod_add_div L h
    have hm := Nat.mul_le_mul_left h hLdiv
    omega
  have hweight : (∑ r ∈ n.primeFactors, n / r) = q * (p * L + h) + h * p := by
    change (∑ r ∈ (h * p * q).primeFactors, h * p * q / r) = _
    rw [weight_mul_prime hhp hq hcq, weight_mul_prime hh0 hp hcp]
  have hindex : 2 * n < ∑ r ∈ n.primeFactors, n / r := by
    have he : q * (p * L + h) + h * p = (L + A) * (p * q) + 1 := by
      calc
        _ = L * (p * q) + (h * p + h * q) := by ring
        _ = _ := by rw [← hrec]; ring
    calc
      2 * n = (2 * h) * (p * q) := by dsimp only [n]; ring
      _ ≤ (L + A) * (p * q) := Nat.mul_le_mul_right _ hLA
      _ < _ := by rw [hweight, he]; omega
  have hcard := hmass n.primeFactors hprime hcompatible n hn0
    (fun _ hs => Nat.dvd_of_mem_primeFactors hs) hindex
  have hqInsert : q ∉ insert p h.primeFactors := by rwa [← primeFactors_append hh0 hp]
  rw [hnFactors, Finset.card_insert_of_notMem hqInsert, Finset.card_insert_of_notMem hpNot] at hcard
  exact hlarge h x y hh hhOdd hhSq hcard hL hx0 hxy hxlt hfact hbound hxD hyD hp hq hold
    hpd hqd hlcm

end OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R3_H2_R1_H2_R1
