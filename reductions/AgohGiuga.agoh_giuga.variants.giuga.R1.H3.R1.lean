import OMAReductions.R_AgohGiuga_agoh_giuga_variants_giuga_R1

/-!
Use the two-factor reconstruction of Borwein, Borwein, Borwein and
Girgensohn, Giuga's Conjecture on Primality, Theorem 3, with the
additional Korselt conditions on both reconstructed factors.
https://carmamaths.org/resources/db90/pdfs/db90-109.00.pdf

The local-to-global numerator argument and the one-factor sum identity
are adapted from Pixelstorm44's merged reduction R3.
-/

namespace OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R1_H3_R1

/-- The cofactor's reciprocal sum is below one. -/
def H1 : Prop :=
  ∀ m : ℕ, 1 < m → Odd m → Squarefree m →
    let D := ∑ r ∈ m.primeFactors, m / r
    D < m →
    let g := m - D
    13 ≤ g → g % 4 = 1 → g.Coprime m →
    ∀ d : ℕ, 0 < d → d ∣ m * m - g →
      let e := (m * m - g) / d
      d < e → g ∣ m + d → g ∣ m + e →
      let p := (m + d) / g
      let q := (m + e) / g
      p.Prime → q.Prime → p < q → q < m →
      (∀ r ∈ m.primeFactors, r < p) →
      (q - 1) ∣ d → (p - 1) ∣ e →
      (∀ r ∈ m.primeFactors, (r - 1) ∣ (m * p * q - 1)) → False

/-- The cofactor's reciprocal sum is at least one. -/
def H2 : Prop :=
  ∀ m : ℕ, 1 < m → Odd m → Squarefree m →
    let D := ∑ r ∈ m.primeFactors, m / r
    m ≤ D →
    let g := m - D % m
    13 ≤ g → g % 4 = 1 → g.Coprime m →
    ∀ d : ℕ, 0 < d → d ∣ m * m - g →
      let e := (m * m - g) / d
      d < e → g ∣ m + d → g ∣ m + e →
      let p := (m + d) / g
      let q := (m + e) / g
      p.Prime → q.Prime → p < q → q < m →
      (∀ r ∈ m.primeFactors, r < p) →
      (q - 1) ∣ d → (p - 1) ∣ e →
      (∀ r ∈ m.primeFactors, (r - 1) ∣ (m * p * q - 1)) → False

section Proof

private theorem two_factors {n : ℕ} (hn : n.Composite) (hf : Squarefree n) :
    2 ≤ n.primeFactors.card := by
  have hprod := Nat.prod_primeFactors_of_squarefree hf
  by_contra! h
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (show n.primeFactors.card ≤ 1 by omega) with h0 | h1
  · rw [Finset.card_eq_zero.mp h0, Finset.prod_empty] at hprod
    exact hn.1.not_gt (by omega)
  · obtain ⟨p, hp⟩ := Finset.card_eq_one.mp h1
    have hmem : p ∈ n.primeFactors := by rw [hp]; simp
    have hp' := Nat.prime_of_mem_primeFactors hmem
    rw [hp, Finset.prod_singleton] at hprod
    exact hn.2 (hprod ▸ hp')

private theorem divide_other_cofactor {n p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (hpn : p ∣ n) (hqn : q ∣ n) : p ∣ n / q := by
  obtain ⟨a, ha⟩ := ((Nat.coprime_primes hp hq).mpr hpq).mul_dvd_of_dvd_of_dvd hpn hqn
  refine ⟨a, ?_⟩
  rw [ha, mul_comm p q, mul_assoc, Nat.mul_div_cancel_left _ hq.pos]

private theorem numerator {n : ℕ} (hn : n.Composite) (hf : Squarefree n)
    (hG : ∀ p ∈ n.primeFactors, p ∣ n / p - 1) :
    ∃ k : ℕ, (∑ p ∈ n.primeFactors, n / p) = n * k + 1 := by
  let S := ∑ p ∈ n.primeFactors, n / p
  have h1 : ∀ p ∈ n.primeFactors, 1 ≤ n / p := fun p hp =>
    Nat.div_pos (Nat.le_of_dvd (by have := hn.1; omega) (Nat.dvd_of_mem_primeFactors hp))
      (Nat.prime_of_mem_primeFactors hp).pos
  have hS : n.primeFactors.card ≤ S := by simpa [S] using Finset.sum_le_sum h1
  have hS2 := (two_factors hn hf).trans hS
  have hN : n ∣ S - 1 := by
    rw [← Nat.prod_primeFactors_of_squarefree hf, Nat.prod_primeFactors_dvd_iff (by omega)]
    intro p hp
    have hp' := Nat.prime_of_mem_primeFactors hp
    have hpn := Nat.dvd_of_mem_primeFactors hp
    refine Nat.mem_primeFactors.mpr ⟨hp', ?_, by omega⟩
    have hsplit : S = n / p + ∑ q ∈ n.primeFactors.erase p, n / q :=
      (Finset.add_sum_erase _ _ hp).symm
    rw [show S - 1 = (n / p - 1) + ∑ q ∈ n.primeFactors.erase p, n / q by
      have := h1 p hp
      omega]
    apply Nat.dvd_add (hG p hp)
    apply Finset.dvd_sum
    intro q hq
    obtain ⟨hqne, hq⟩ := Finset.mem_erase.mp hq
    exact divide_other_cofactor hp' (Nat.prime_of_mem_primeFactors hq) hqne.symm hpn
      (Nat.dvd_of_mem_primeFactors hq)
  obtain ⟨k, hk⟩ := hN
  exact ⟨k, by change S = n * k + 1; omega⟩

private theorem numerator_mul_prime {m q : ℕ} (hm : 0 < m) (hq : q.Prime)
    (hc : m.Coprime q) :
    (∑ r ∈ (m * q).primeFactors, m * q / r) = q * (∑ r ∈ m.primeFactors, m / r) + m := by
  have hnot : q ∉ m.primeFactors := fun h =>
    (hq.coprime_iff_not_dvd.mp hc.symm) (Nat.dvd_of_mem_primeFactors h)
  rw [Nat.primeFactors_mul hm.ne' hq.ne_zero, hq.primeFactors, Finset.union_comm]
  simp only [Finset.singleton_union, Finset.sum_insert hnot, Nat.mul_div_cancel _ hq.pos,
    Finset.mul_sum]
  rw [add_comm]
  congr 1
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [mul_comm m q, Nat.mul_div_assoc q (Nat.dvd_of_mem_primeFactors hr)]

private theorem pred_coprime (p : ℕ) (hp : 1 ≤ p) : (p - 1).Coprime p := by
  conv_rhs => rw [← Nat.sub_add_cancel hp]
  exact Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)

private theorem korselt_cofactor {n p : ℕ} (hp : p.Prime) (hd : p ∣ n) (hn : 0 < n)
    (hk : (p - 1) ∣ (n - 1)) : (p - 1) ∣ (n / p - 1) := by
  have hdiv : 1 ≤ n / p := Nat.div_pos (Nat.le_of_dvd hn hd) hp.pos
  have hid : n - 1 = p * (n / p - 1) + (p - 1) := by
    rw [Nat.mul_sub, mul_one, Nat.mul_div_cancel' hd]
    have hle := Nat.le_of_dvd hn hd
    have := hp.one_le
    omega
  rw [hid] at hk
  exact (pred_coprime p hp.one_le).dvd_of_dvd_mul_left
    ((Nat.dvd_add_left (dvd_refl (p - 1))).mp hk)

private theorem gap_of_multiple {m D t : ℕ} (ht : 0 < t) (htm : t < m) (hd : m ∣ D + t) :
    m - D % m = t := by
  have hmod : (D % m + t) % m = 0 := by
    rw [Nat.mod_add_mod, Nat.mod_eq_zero_of_dvd hd]
  have hD := Nat.mod_lt D (by omega : 0 < m)
  by_cases hsmall : D % m + t < m
  · rw [Nat.mod_eq_of_lt hsmall] at hmod
    omega
  · rw [Nat.mod_eq_sub_mod (by omega : m ≤ D % m + t), Nat.mod_eq_of_lt (by omega)] at hmod
    omega

private theorem pair_gap {m p q D k : ℕ} (hm : 0 < m) (hp : 2 ≤ p) (hpq : p < q)
    (he : D * (p * q) + (m * p + m * q) = (m * k) * (p * q) + 1) :
    let g := m - D % m
    0 < g ∧ g < m ∧ g * (p * q) + 1 = m * p + m * q := by
  have hp0 : 0 < p := by omega
  have hq0 : 0 < q := by omega
  have hmp := Nat.le_mul_of_pos_left p hm
  have hmq := Nat.le_mul_of_pos_left q hm
  have hD : D ≤ m * k := by
    by_contra! h
    have hn := Nat.mul_lt_mul_of_pos_right h (Nat.mul_pos hp0 hq0)
    omega
  let t := m * k - D
  have htadd : D + t = m * k := by dsimp [t]; omega
  have hsum : t * (p * q) + 1 = m * p + m * q := by
    rw [← htadd, add_mul] at he
    omega
  have ht : 0 < t := by
    by_contra! h
    simp [Nat.eq_zero_of_le_zero h] at hsum
    omega
  have hlt : p + q < p * q := by
    have := Nat.mul_le_mul_right q hp
    omega
  have htm : t < m := by
    by_contra! h
    have hb := Nat.mul_le_mul_right (p * q) h
    have ha := Nat.mul_lt_mul_of_pos_left hlt hm
    rw [mul_add] at ha
    omega
  rw [gap_of_multiple ht htm ⟨k, htadd⟩]
  exact ⟨ht, htm, hsum⟩

/-- The only possible completion primes are obtained from a factor pair of
`m * m - g`, with the extra divisibilities in the conclusion. -/
theorem pair_divisors {m p q g : ℕ} (hm : 0 < m) (hg : 0 < g)
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (h : g * (p * q) + 1 = m * p + m * q)
    (hkp : (p - 1) ∣ (m * q - 1)) (hkq : (q - 1) ∣ (m * p - 1)) :
    ∃ d e : ℕ, 0 < d ∧ d < e ∧ d * e = m * m - g ∧
      m + d = g * p ∧ m + e = g * q ∧ (q - 1) ∣ d ∧ (p - 1) ∣ e := by
  have hmp := Nat.le_mul_of_pos_left p hm
  have hmq := Nat.le_mul_of_pos_left q hm
  have hp2 := hp.two_le
  have hq2 := hq.two_le
  have hup : m < g * p := by
    by_contra! hb
    have hh := Nat.mul_le_mul_right q hb
    rw [mul_assoc] at hh
    omega
  have huq : m < g * q := hup.trans
    (Nat.mul_lt_mul_of_pos_left hpq hg)
  let d := g * p - m
  let e := g * q - m
  have hd : m + d = g * p := by dsimp [d]; omega
  have he : m + e = g * q := by dsimp [e]; omega
  have hde : d < e := by
    have hh := Nat.mul_lt_mul_of_pos_left hpq hg
    omega
  have hdq : d * q = m * p - 1 := by
    have hh := congrArg (· * q) hd
    rw [add_mul, mul_assoc] at hh
    omega
  have hep : e * p = m * q - 1 := by
    have hh := congrArg (· * p) he
    rw [add_mul, mul_assoc, mul_comm q p] at hh
    omega
  have hprod : d * e + g = m * m := by
    nlinarith only [congrArg (· * g) h, congrArg (· * m) hd, congrArg (· * m) he,
      congrArg₂ (· * ·) hd he]
  refine ⟨d, e, by dsimp [d]; omega, hde, by omega, hd, he, ?_, ?_⟩
  · rw [← hdq, mul_comm] at hkq
    exact (pred_coprime q hq.one_le).dvd_of_dvd_mul_left hkq
  · rw [← hep, mul_comm] at hkp
    exact (pred_coprime p hp.one_le).dvd_of_dvd_mul_left hkp

/-- An additional divisibility filter from the two Korselt conditions. -/
private theorem completion_pred_dvd {m p q g d e a : ℕ}
    (hm : 1 ≤ m) (hg : 1 ≤ g) (hp : p.Prime) (hq : q.Prime)
    (hd : m + d = g * p) (he : m + e = g * q)
    (ha : d = (q - 1) * a) (heK : (p - 1) ∣ e)
    (hkp : (p - 1) ∣ (m * q - 1)) :
    (p - 1) ∣ (g + a) * (g - 1) := by
  let t := (p - 1).gcd (q - 1)
  have htp : t ∣ p - 1 := Nat.gcd_dvd_left _ _
  have htq : t ∣ q - 1 := Nat.gcd_dvd_right _ _
  have htm : t ∣ m - 1 := by
    have hEq : m * q - 1 = m * (q - 1) + (m - 1) := by
      rw [Nat.mul_sub, mul_one]
      have := Nat.le_mul_of_pos_right m hq.pos
      omega
    have hh := htp.trans hkp
    rw [hEq] at hh
    exact (Nat.dvd_add_right (dvd_mul_of_dvd_right htq m)).mp hh
  have htg : t ∣ g - 1 := by
    have hh : t ∣ g * p - 1 := by
      rw [← hd, show m + d - 1 = (m - 1) + d by omega]
      exact Nat.dvd_add htm (htq.trans ⟨a, ha⟩)
    have hEq : g * p - 1 = g * (p - 1) + (g - 1) := by
      rw [Nat.mul_sub, mul_one]
      have := Nat.le_mul_of_pos_right g hp.pos
      omega
    rw [hEq] at hh
    exact (Nat.dvd_add_right (dvd_mul_of_dvd_right htp g)).mp hh
  obtain ⟨b, hb⟩ := heK
  rw [ha] at hd
  rw [hb] at he
  have hRatio : (g + a) * (q - 1) = (p - 1) * (g + b) := by
    nlinarith only [hd, he,
      congrArg (g * ·) (Nat.sub_add_cancel hp.one_le),
      congrArg (g * ·) (Nat.sub_add_cancel hq.one_le)]
  have hdiv := Nat.dvd_mul_gcd_iff_dvd_mul.mpr
    (show (p - 1) ∣ (g + a) * (q - 1) from ⟨g + b, hRatio⟩)
  exact hdiv.trans (Nat.mul_dvd_mul_left _ htg)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem small_gap_table : ∀ g : Fin 10, g.val = 5 ∨ g.val = 9 →
    ∀ a : Fin 8, 0 < a.val → a.val + 2 ≤ g.val →
    ∀ p : Fin 130, 3 ≤ p.val → (p.val - 1) ∣ (g.val + a.val) * (g.val - 1) →
      p.val.Prime → a.val ∣ g.val * p.val * p.val - 1 →
      let f := fun q : ℕ => a.val * ((q - 1) * (p.val + q)) + 1
      let v := g.val * p.val * p.val
      ([3, 4, 5, 6, 8, 9, 13, 16, 23, 28, 34, 39, 43, 57, 104, 105, 150] : List ℕ).any
        (fun b => decide (f b ≤ v ∧ v < f (b + 1) ∧ (f b < v ∨ b = 9))) = true := by
  decide

/-- A bounded kernel-checked exclusion of the first three possible gaps. -/
private theorem gap_ge_thirteen {m p q g d e : ℕ} (hg : 0 < g) (hg4 : g % 4 = 1)
    (hp : p.Prime) (hq : q.Prime) (hp3 : 3 ≤ p) (hpq : p < q) (hqm : q < m)
    (hd0 : 0 < d) (hd : m + d = g * p) (he : m + e = g * q)
    (hdK : (q - 1) ∣ d) (heK : (p - 1) ∣ e)
    (hkp : (p - 1) ∣ (m * q - 1))
    (hgap : g * (p * q) + 1 = m * p + m * q) : 13 ≤ g := by
  by_contra! hsmall
  have hg1 : 1 < g := by
    by_contra! h
    have heq : g = 1 := by omega
    rw [heq, one_mul] at hd
    omega
  have hcases : g = 5 ∨ g = 9 := by omega
  have hg9 : g ≤ 9 := by omega
  obtain ⟨a, ha⟩ := hdK
  have ha0 : 0 < a := by
    by_contra! h
    simp [Nat.eq_zero_of_le_zero h] at ha
    omega
  have hag : a + 2 ≤ g := by
    by_contra! h
    have hle := Nat.mul_le_mul_left (q - 1) (show g - 1 ≤ a by omega)
    have hle' : (g - 1) * p ≤ (q - 1) * (g - 1) := by
      rw [mul_comm (q - 1) (g - 1)]
      exact Nat.mul_le_mul_left _ (by omega)
    have hh : (g - 1) * p + p = g * p := by
      rw [Nat.sub_mul, one_mul]
      have := Nat.le_mul_of_pos_left p hg
      omega
    omega
  have hpdiv := completion_pred_dvd (by omega) hg hp hq hd he ha heK hkp
  have hpbound := Nat.le_of_dvd (Nat.mul_pos (by omega) (by omega) :
    0 < (g + a) * (g - 1)) hpdiv
  have hp129 : p ≤ 129 := by
    have hle := Nat.mul_le_mul (show g + a ≤ 16 by omega) (show g - 1 ≤ 8 by omega)
    omega
  have hPoly : a * ((q - 1) * (p + q)) + 1 = g * p * p := by
    have hh := congrArg (· * (p + q)) hd
    rw [ha] at hh
    nlinarith only [hh, hgap]
  have hquot : g * p * p - 1 = a * ((q - 1) * (p + q)) := by omega
  let f := fun j : ℕ => a * ((j - 1) * (p + j)) + 1
  let v := g * p * p
  have hfq : f q = v := hPoly
  obtain ⟨b, _, hdec⟩ := List.any_eq_true.mp
    (small_gap_table ⟨g, by omega⟩ hcases ⟨a, by omega⟩ ha0 hag
      ⟨p, by omega⟩ hp3 hpdiv hp ⟨_, hquot⟩)
  have hb : f b ≤ v ∧ v < f (b + 1) ∧ (f b < v ∨ b = 9) := of_decide_eq_true hdec
  have hqle : q ≤ b := by
    by_contra! h
    have hm : f (b + 1) ≤ f q := by
      dsimp [f]
      exact Nat.add_le_add_right (Nat.mul_le_mul_left a
        (Nat.mul_le_mul (Nat.sub_le_sub_right h 1) (Nat.add_le_add_left h p))) 1
    omega
  have hble : b ≤ q := by
    by_contra! h
    have hlt : f q < f b := by
      dsimp [f]
      apply Nat.add_lt_add_right
      apply Nat.mul_lt_mul_of_pos_left _ ha0
      calc
        (q - 1) * (p + q) ≤ (q - 1) * (p + b) :=
          Nat.mul_le_mul_left _ (Nat.add_le_add_left h.le p)
        _ < (b - 1) * (p + b) := Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
    omega
  have heq := Nat.le_antisymm hqle hble
  rcases hb.2.2 with hh | hh
  · rw [← heq, hfq] at hh
    exact (lt_irrefl v) hh
  · rw [heq, hh] at hq
    exact (by decide : ¬ Nat.Prime 9) hq

theorem main : H1 → H2 → OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R1.H3 := by
  intro hUnit hHigher n hn hf hK hG
  have hn0 : 0 < n := by have := hn.1; omega
  let P := n.primeFactors
  have hP : 2 ≤ P.card := two_factors hn hf
  let q := P.max' (Finset.card_pos.mp (by omega))
  have hqM : q ∈ P := Finset.max'_mem _ _
  have hPq : (P.erase q).Nonempty := Finset.card_pos.mp (by rw [Finset.card_erase_of_mem hqM]; omega)
  let p := (P.erase q).max' hPq
  have hpE : p ∈ P.erase q := Finset.max'_mem _ _
  have hpM : p ∈ P := (Finset.mem_erase.mp hpE).2
  have hpq : p < q :=
    lt_of_le_of_ne (Finset.le_max' _ _ hpM) (Finset.mem_erase.mp hpE).1
  have hp : p.Prime := Nat.prime_of_mem_primeFactors hpM
  have hq : q.Prime := Nat.prime_of_mem_primeFactors hqM
  let T := (P.erase q).erase p
  let m := ∏ r ∈ T, r
  have hmF : m.primeFactors = T := Nat.primeFactors_prod fun r hr =>
    Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hr))
  have hnEq : n = m * p * q := by
    calc
      n = ∏ r ∈ P, r := (Nat.prod_primeFactors_of_squarefree hf).symm
      _ = (∏ r ∈ P.erase q, r) * q := (Finset.prod_erase_mul _ _ hqM).symm
      _ = m * p * q := congrArg (· * q) (Finset.prod_erase_mul _ _ hpE).symm
  have hsf : Squarefree (m * p * q) := hnEq ▸ hf
  have hsfp : Squarefree (m * p) := hsf.of_mul_left
  have hmf : Squarefree m := hsfp.of_mul_left
  have hm0 : 0 < m := Nat.pos_of_ne_zero hmf.ne_zero
  have hmp := Nat.le_mul_of_pos_left p hm0
  have hp2 := hp.two_le
  have hq2 := hq.two_le
  have hqdiv : n / q = m * p := by rw [hnEq, Nat.mul_div_cancel _ hq.pos]
  have hpdiv : n / p = m * q := by rw [hnEq, mul_right_comm m p q, Nat.mul_div_cancel _ hp.pos]
  have hkp := korselt_cofactor hp (Nat.dvd_of_mem_primeFactors hpM) hn0 (hK p hpM)
  have hkq := korselt_cofactor hq (Nat.dvd_of_mem_primeFactors hqM) hn0 (hK q hqM)
  rw [hpdiv] at hkp
  rw [hqdiv] at hkq
  have hGq : q ∣ m * p - 1 := hqdiv ▸ hG q hqM
  have hqlt : q < m := by
    have hh := (pred_coprime q hq.one_le).mul_dvd_of_dvd_of_dvd hkq hGq
    have hb : q * (q - 1) ≤ m * p - 1 := by
      simpa only [mul_comm q (q - 1)] using Nat.le_of_dvd (by omega : 0 < m * p - 1) hh
    by_contra! ha
    have ha' : m * p ≤ p * q := by
      simpa only [mul_comm q p] using Nat.mul_le_mul_right p ha
    have hb' : p * q ≤ q * (q - 1) := by
      simpa only [mul_comm q p] using Nat.mul_le_mul_left q (show p ≤ q - 1 by omega)
    omega
  have hqodd : q % 2 = 1 := (Nat.Prime.mod_two_eq_one_iff_ne_two hq).2 (by omega)
  have h2 : 2 ∣ n - 1 := (show 2 ∣ q - 1 by omega).trans (hK q hqM)
  have hOdd : Odd (m * p * q) := hnEq ▸ (show Odd n from ⟨(n - 1) / 2, by omega⟩)
  have hOddMP := Nat.odd_mul.mp hOdd
  have hmo : Odd m := (Nat.odd_mul.mp hOddMP.1).1
  have hpo : p % 2 = 1 := Nat.odd_iff.mp (Nat.odd_mul.mp hOddMP.1).2
  obtain ⟨k, hk⟩ := numerator hn hf hG
  rw [hnEq, numerator_mul_prime (Nat.mul_pos hm0 hp.pos) hq (Nat.coprime_of_squarefree_mul hsf),
    numerator_mul_prime hm0 hp (Nat.coprime_of_squarefree_mul hsfp)] at hk
  let D := ∑ r ∈ m.primeFactors, m / r
  let g := m - D % m
  have hgap : 0 < g ∧ g < m ∧ g * (p * q) + 1 = m * p + m * q :=
    pair_gap hm0 hp2 hpq (D := D) (k := k) (by dsimp [D]; nlinarith only [hk])
  obtain ⟨d, e, hd, hde, hprod, hpEq, hqEq, hdK, heK⟩ :=
    pair_divisors hm0 hgap.1 hp hq hpq hgap.2.2 hkp hkq
  have hd2 : 2 ∣ d := (show 2 ∣ q - 1 by omega).trans hdK
  have he2 : 2 ∣ e := (show 2 ∣ p - 1 by omega).trans heK
  have hde4 : 4 ∣ d * e := mul_dvd_mul hd2 he2
  have hm4 : (m * m) % 4 = 1 := by
    obtain ⟨a, ha⟩ := hmo
    rw [ha, show (2 * a + 1) * (2 * a + 1) = 4 * (a * a + a) + 1 by ring]
    omega
  have hg4 : g % 4 = 1 := by
    have hgm := hgap.2.1.le.trans (Nat.le_mul_of_pos_left m hm0)
    omega
  have hgCop : g.Coprime m := by
    have hgcd := Nat.gcd_dvd_left g m
    have hmc := Nat.gcd_dvd_right g m
    have hh := Nat.dvd_add (dvd_mul_of_dvd_left hmc p) (dvd_mul_of_dvd_left hmc q)
    rw [← hgap.2.2] at hh
    exact Nat.dvd_one.mp ((Nat.dvd_add_right (dvd_mul_of_dvd_left hgcd (p * q))).mp hh)
  have hgMin := gap_ge_thirteen hgap.1 hg4 hp hq (by omega) hpq hqlt
    hd hpEq hqEq hdK heK hkp hgap.2.2
  have hdvd : d ∣ m * m - g := ⟨e, hprod.symm⟩
  have heEq : (m * m - g) / d = e := by rw [← hprod, Nat.mul_div_cancel_left e hd]
  have hp' : (m + d) / g = p := by rw [hpEq, Nat.mul_div_cancel_left p hgap.1]
  have hq' : (m + e) / g = q := by rw [hqEq, Nat.mul_div_cancel_left q hgap.1]
  have hOrder (r : ℕ) (hr : r ∈ m.primeFactors) : r < p := by
    rw [hmF] at hr
    exact lt_of_le_of_ne (Finset.le_max' _ _ (Finset.mem_of_mem_erase hr))
      (Finset.mem_erase.mp hr).1
  have hOld (r : ℕ) (hr : r ∈ m.primeFactors) : (r - 1) ∣ (m * p * q - 1) := by
    rw [hmF] at hr
    rw [← hnEq]
    exact hK r (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hr))
  have hdCheck : g ∣ m + d := ⟨p, hpEq⟩
  have heCheck : g ∣ m + e := ⟨q, hqEq⟩
  by_cases hD : D < m
  · have hgEq : m - D = g := by dsimp [g]; rw [Nat.mod_eq_of_lt hD]
    have hh := hUnit m (by omega) hmo hmf hD
    change 13 ≤ m - D → (m - D) % 4 = 1 → (m - D).Coprime m → ∀ d : ℕ, _ at hh
    rw [hgEq] at hh
    have hc := hh hgMin hg4 hgCop d hd hdvd
    dsimp only at hc
    rw [heEq, hp', hq'] at hc
    exact hc hde hdCheck heCheck hp hq hpq hqlt hOrder hdK heK hOld
  · have hc := hHigher m (by omega) hmo hmf (show m ≤ D by omega) hgMin hg4 hgCop d hd hdvd
    change d < (m * m - g) / d → _ at hc
    dsimp only at hc
    rw [heEq, hp', hq'] at hc
    exact hc hde hdCheck heCheck hp hq hpq hqlt hOrder hdK heK hOld

end Proof

end OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R1_H3_R1
