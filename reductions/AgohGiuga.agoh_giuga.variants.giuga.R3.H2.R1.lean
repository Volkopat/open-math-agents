import OMAReductions.R_AgohGiuga_agoh_giuga_variants_giuga_R3
import Mathlib

/-!
Recover the two largest primes from a factorization attached to the remaining
cofactor. The two cases distinguish reciprocal-sum index one from higher index.
-/

namespace OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R3_H2_R1

open OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R3 (weight_mul_prime)

private theorem reconstruct_pair {h p q A x y : ℕ}
    (hx : A * p = x + h) (hy : A * q = y + h)
    (he : A * p * q + 1 = h * p + h * q) : x * y + A = h ^ 2 := by
  have hproduct : (x + h) * (y + h) = A * (A * p * q) := by rw [← hx, ← hy]; ring
  have hcross : (x + h) * h + (y + h) * h = A * (h * p + h * q) := by
    rw [← hx, ← hy]
    ring
  have hscale : A * (A * p * q) + A = A * (h * p + h * q) := by
    simpa only [mul_add, mul_one] using congrArg (A * ·) he
  nlinarith

private theorem recover_residue {h L A : ℕ} (ha : 0 < A) (hah : A < h)
    (hd : h ∣ L + A) : A = h - L % h := by
  have hrem := Nat.mod_lt L (show 0 < h by omega)
  have hmod : (L % h + A) % h = 0 := by
    rw [Nat.mod_add_mod]
    exact Nat.mod_eq_zero_of_dvd hd
  obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero hmod
  have hk1 : k = 1 := by
    by_contra! hk1
    have hk0 : k ≠ 0 := by
      intro hz
      simp [hz] at hk
      omega
    have hmul : h * 2 ≤ h * k := Nat.mul_le_mul_left _ (by omega)
    omega
  simp [hk1] at hk
  omega

private theorem predecessor_dvd_factor {h p q y : ℕ} (hp : p.Prime)
    (hy : p * y + 1 = h * q) (hd : p - 1 ∣ h * p * q - 1) : p - 1 ∣ y := by
  have hm : h * p * q - 1 = p * (p * y) + (p - 1) := by
    rw [show h * p * q = p * (h * q) by ring, ← hy, mul_add, mul_one]
    have := hp.one_le
    omega
  rw [hm] at hd
  have hmul := (Nat.dvd_add_left (dvd_refl (p - 1))).mp hd
  have hcop : (p - 1).Coprime p := by
    conv_rhs => rw [← Nat.sub_add_cancel hp.one_le]
    exact Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)
  exact hcop.dvd_of_dvd_mul_left (hcop.dvd_of_dvd_mul_left hmul)

private theorem cofactor_bound {h p q A x y : ℕ} (hh : 0 < h) (hp : 1 < p)
    (hpq : p < q) (ha : 0 < A) (hx0 : 0 < x)
    (hx : A * p = x + h) (hy : A * q = y + h) (hrec : q * x + 1 = h * p)
    (hdY : p - 1 ∣ y) (hdX : q - 1 ∣ x) : h < 2 * A ^ 3 := by
  let s := p - 1
  let t := q - 1
  have hs : s + 1 = p := Nat.sub_add_cancel (by omega)
  have ht : t + 1 = q := Nat.sub_add_cancel (by omega)
  have hpt : p ≤ t := by omega
  have hpx : p ≤ x := hpt.trans (Nat.le_of_dvd hx0 hdX)
  have hxlt : x < A * p := by rw [hx]; omega
  have hA1 : 1 < A := by
    by_contra! hn
    have : A = 1 := by omega
    rw [this, one_mul] at hxlt
    omega
  obtain ⟨v, hv⟩ := hdX
  change x = t * v at hv
  have hvp : v * p ≤ x := by
    rw [hv, mul_comm t v]
    exact Nat.mul_le_mul_left v hpt
  have hvA : v < A := Nat.lt_of_mul_lt_mul_right (hvp.trans_lt hxlt)
  have hLinear : (A + v) * t = y + A * s := by
    have h₁ : A * (s + 1) = t * v + h := by rw [hs, hx, hv]
    have h₂ : A * (t + 1) = y + h := by rw [ht, hy]
    nlinarith
  have hGap : v * (t * (q + 1)) = (A - 1) + (h + A) * s := by
    have h₁ : v * (t * (q + 1)) = q * x + x := by rw [hv]; ring
    have h₂ : h * p = h * s + h := by rw [← hs, mul_add, mul_one]
    have h₃ : A * p = A * s + A := by rw [← hs, mul_add, mul_one]
    have h₄ : A - 1 + 1 = A := Nat.sub_add_cancel (by omega)
    nlinarith
  have hDiv : s ∣ (A + v) * t := hLinear.symm ▸ dvd_add hdY (dvd_mul_left s A)
  have hDiv' : s ∣ (A + v) * (v * (t * (q + 1))) := by
    rw [show (A + v) * (v * (t * (q + 1))) = ((A + v) * t) * (v * (q + 1)) by ring]
    exact dvd_mul_of_dvd_left hDiv _
  rw [hGap, mul_add] at hDiv'
  have hTerm : s ∣ (A + v) * ((h + A) * s) := dvd_mul_left s (h + A) |>.mul_left _
  have hPred : s ∣ (A + v) * (A - 1) := (Nat.dvd_add_left hTerm).mp hDiv'
  have hPredBound : s ≤ (A + v) * (A - 1) :=
    Nat.le_of_dvd (Nat.mul_pos (by omega) (by omega)) hPred
  have hlt : (A + v) * (A - 1) < (2 * A) * A :=
    (Nat.mul_lt_mul_of_pos_right (by omega : A + v < 2 * A) (show 0 < A - 1 by omega)).trans_le
      (Nat.mul_le_mul_left _ (by omega))
  have hpBound : p ≤ 2 * A ^ 2 := by
    rw [pow_two, ← mul_assoc]
    omega
  calc
    h < A * p := by rw [hx]; omega
    _ ≤ A * (2 * A ^ 2) := Nat.mul_le_mul_left _ hpBound
    _ = 2 * A ^ 3 := by ring

/-- Exclude factor pairs with reciprocal-sum index one. -/
def H1 : Prop :=
  ∀ h x y : ℕ, 1 < h → Odd h → Squarefree h →
    let L := ∑ r ∈ h.primeFactors, h / r
    let A := h - L % h
    let p := (x + h) / A
    let q := (y + h) / A
    L < h → 0 < x → x < y → x < h → x * y + A = h ^ 2 → h < 2 * A ^ 3 →
    A ∣ x + h → A ∣ y + h →
    p.Prime → q.Prime → (∀ r ∈ h.primeFactors, r < p) →
    p - 1 ∣ y → q - 1 ∣ x →
    ¬ (h.primeFactors.lcm (fun r => r - 1) ∣ h * p * q - 1)

/-- Exclude factor pairs with reciprocal-sum index at least two. -/
def H2 : Prop :=
  ∀ h x y : ℕ, 1 < h → Odd h → Squarefree h →
    let L := ∑ r ∈ h.primeFactors, h / r
    let A := h - L % h
    let p := (x + h) / A
    let q := (y + h) / A
    h ≤ L → 0 < x → x < y → x < h → x * y + A = h ^ 2 → h < 2 * A ^ 3 →
    A ∣ x + h → A ∣ y + h →
    p.Prime → q.Prime → (∀ r ∈ h.primeFactors, r < p) →
    p - 1 ∣ y → q - 1 ∣ x →
    ¬ (h.primeFactors.lcm (fun r => r - 1) ∣ h * p * q - 1)

theorem main : H1 → H2 → OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R3.H2 := by
  intro hSmall hLarge m hm hmOdd hmSq
  let D := ∑ r ∈ m.primeFactors, m / r
  let g := m - D % m
  let q := (m - 1) / g
  change q.Prime → (∀ r ∈ m.primeFactors, r < q) → q * g = m - 1 →
    q - 1 ∣ g → ¬ (m.primeFactors.lcm (fun r => r - 1) ∣ m * q - 1)
  intro hq hqMax hqg hqKorselt hM
  have hm0 : 0 < m := by omega
  have hg : 0 < g := by
    dsimp [g]
    have := Nat.mod_lt D hm0
    omega
  have hnon := Nat.nonempty_primeFactors.mpr hm
  let p := m.primeFactors.max' hnon
  have hpMem : p ∈ m.primeFactors := Finset.max'_mem _ _
  have hp : p.Prime := Nat.prime_of_mem_primeFactors hpMem
  have hpq := hqMax p hpMem
  let h := m / p
  have hmprod : h * p = m := Nat.div_mul_cancel (Nat.dvd_of_mem_primeFactors hpMem)
  have hh0 : 0 < h :=
    Nat.div_pos (Nat.le_of_dvd hm0 (Nat.dvd_of_mem_primeFactors hpMem)) hp.pos
  have hsq : Squarefree (h * p) := hmprod ▸ hmSq
  rw [Nat.squarefree_mul_iff] at hsq
  have hhOdd : Odd h := (Nat.odd_mul.mp (hmprod ▸ hmOdd)).1
  have hSub : h.primeFactors ⊆ m.primeFactors := by
    rw [← hmprod, Nat.primeFactors_mul hh0.ne' hp.ne_zero]
    exact Finset.subset_union_left
  have hOld : ∀ r ∈ h.primeFactors, r < p := by
    intro r hr
    apply lt_of_le_of_ne (Finset.le_max' _ _ (hSub hr))
    intro heq
    change r = p at heq
    have hrp : p ∈ h.primeFactors := heq ▸ hr
    exact (hp.coprime_iff_not_dvd.mp hsq.1.symm) (Nat.dvd_of_mem_primeFactors hrp)
  let L := ∑ r ∈ h.primeFactors, h / r
  have hD : D = p * L + h := by
    dsimp [D, L]
    rw [← hmprod, weight_mul_prime hh0 hp hsq.1]
  have hDg : D + g = m * (D / m + 1) := by
    have hrem : D % m + g = m := Nat.add_sub_of_le (Nat.mod_lt D hm0).le
    rw [mul_add, mul_one]
    have := Nat.mod_add_div D m
    omega
  have hpDg : p ∣ D + g := by
    refine ⟨h * (D / m + 1), ?_⟩
    calc
      D + g = m * (D / m + 1) := hDg
      _ = (h * p) * (D / m + 1) := congrArg (· * (D / m + 1)) hmprod.symm
      _ = p * (h * (D / m + 1)) := by ring
  have hpHg : p ∣ h + g := (Nat.dvd_add_right (dvd_mul_right p L)).mp
    (by simpa only [hD, add_assoc] using hpDg)
  obtain ⟨A, hA⟩ := hpHg
  have hA0 : 0 < A := by
    by_contra! hn
    have : A = 0 := by omega
    simp [this] at hA
    omega
  have hprod : A * p * q + 1 = h * p + h * q := by
    have hqg' : q * g + 1 = h * p := by rw [hmprod]; omega
    calc
      A * p * q + 1 = (h + g) * q + 1 := by rw [hA, mul_comm A p]
      _ = h * p + h * q := by rw [add_mul, mul_comm g q]; omega
  have hpqSum : p + q ≤ p * q := by
    have := Nat.mul_le_mul_right q hp.two_le
    omega
  have hAh : A < h := by
    apply Nat.lt_of_mul_lt_mul_right (a := p * q)
    calc
      A * (p * q) < h * (p + q) := by rw [← mul_assoc, mul_add, ← hprod]; omega
      _ ≤ h * (p * q) := Nat.mul_le_mul_left h hpqSum
  have hLA : h ∣ L + A := by
    use D / m + 1
    apply Nat.eq_of_mul_eq_mul_left hp.pos
    calc
      p * (L + A) = D + g := by rw [mul_add, ← hA, hD, add_assoc]
      _ = m * (D / m + 1) := hDg
      _ = (h * p) * (D / m + 1) := congrArg (· * (D / m + 1)) hmprod.symm
      _ = p * (h * (D / m + 1)) := by ring
  have hResid : A = h - L % h := recover_residue hA0 hAh hLA
  let y := A * q - h
  have hx : A * p = g + h := by simpa only [mul_comm, add_comm] using hA.symm
  have hAq : h < A * q := by
    apply Nat.lt_of_mul_lt_mul_left (a := p)
    have hHq : 1 < h * q :=
      hq.one_lt.trans_le (by simpa using Nat.mul_le_mul_right q (show 1 ≤ h by omega))
    rw [mul_comm p h, show p * (A * q) = A * p * q by ring]
    omega
  have hy : A * q = y + h := (Nat.sub_add_cancel hAq.le).symm
  have hgy : g < y := by
    have hlt := Nat.mul_lt_mul_of_pos_left hpq hA0
    omega
  have hFact : g * y + A = h ^ 2 := reconstruct_pair hx hy hprod
  have hgh : g < h := by
    by_contra! hle
    have hmul : h * h ≤ g * y := Nat.mul_le_mul hle (hle.trans hgy.le)
    rw [pow_two] at hFact
    omega
  have hRecP : (g + h) / A = p := by rw [← hx, Nat.mul_div_cancel_left _ hA0]
  have hRecQ : (y + h) / A = q := by rw [← hy, Nat.mul_div_cancel_left _ hA0]
  have hpKorselt : p - 1 ∣ y := by
    apply predecessor_dvd_factor hp (q := q) (h := h)
    · have hrewrite : p * (y + h) = A * p * q := by rw [← hy]; ring
      rw [mul_add, mul_comm p h] at hrewrite
      omega
    · rw [hmprod]
      exact (Finset.lcm_dvd_iff.mp hM) p hpMem
  have hhBound : h < 2 * A ^ 3 := by
    apply cofactor_bound hh0 hp.one_lt hpq hA0 hg hx hy _ hpKorselt hqKorselt
    rw [hmprod]
    omega
  have hCheck :
      let B := h - L % h
      let P := (g + h) / B
      let Q := (y + h) / B
      P.Prime → Q.Prime → (∀ r ∈ h.primeFactors, r < P) →
        P - 1 ∣ y → Q - 1 ∣ g →
        ¬ (h.primeFactors.lcm (fun r => r - 1) ∣ h * P * Q - 1) := by
    have hxDvd : A ∣ g + h := ⟨p, hx.symm⟩
    have hyDvd : A ∣ y + h := ⟨q, hy.symm⟩
    by_cases hL : L < h
    · exact hSmall h g y (by omega) hhOdd hsq.2.1 hL hg hgy hgh
        (hResid ▸ hFact) (hResid ▸ hhBound) (hResid ▸ hxDvd) (hResid ▸ hyDvd)
    · exact hLarge h g y (by omega) hhOdd hsq.2.1 (by omega) hg hgy hgh
        (hResid ▸ hFact) (hResid ▸ hhBound) (hResid ▸ hxDvd) (hResid ▸ hyDvd)
  dsimp only at hCheck
  rw [← hResid, hRecP, hRecQ] at hCheck
  apply hCheck hp hq hOld hpKorselt hqKorselt
  rw [hmprod, Finset.lcm_dvd_iff]
  exact fun r hr => (Finset.lcm_dvd_iff.mp hM) r (hSub hr)

end OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R3_H2_R1
