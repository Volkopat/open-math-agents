import OMAReductions.R_Erdos1052_erdos_1052_R2

/-! Separate the external contributions to the repeated odd core in Erdős 1052. -/


namespace OMA.UnitaryCoreAudit

open scoped BigOperators

private theorem product_ratios {s : Finset ℕ} {f : ℕ → ℕ}
    (hf : ∀ i ∈ s, 0 < f i) :
    (∏ i ∈ s, (1 + (1 : ℚ) / f i)) =
    (∏ i ∈ s, (f i + 1 : ℕ) : ℕ) / ((∏ i ∈ s, f i : ℕ) : ℚ) := by
  push_cast
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  have hi0 : (f i : ℚ) ≠ 0 := by exact_mod_cast (hf i hi).ne'
  field_simp

private theorem one_add_pow_upper {x : ℚ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (k : ℕ) :
    (1 + x) ^ k ≤ 1 + ((2 : ℚ) ^ k - 1) * x := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hC : 0 ≤ (2 : ℚ) ^ k - 1 := by
      exact sub_nonneg.mpr (one_le_pow₀ (by norm_num) (n := k))
    rw [pow_succ, pow_succ (2 : ℚ)]
    refine (mul_le_mul_of_nonneg_right ih (by positivity)).trans ?_
    nlinarith [mul_nonneg hC (mul_nonneg hx0 (sub_nonneg.mpr hx1))]

private theorem exists_small_component {s : Finset ℕ} {f : ℕ → ℕ} {D m k : ℕ}
    (hs : s.Nonempty) (hf : ∀ i ∈ s, 0 < f i) (hk : s.card ≤ k)
    (hm : 0 < m) (hmD : m ≤ D)
    (hdiv : (∏ i ∈ s, f i) ∣ m * ∏ i ∈ s, (f i + 1)) :
    ∃ i ∈ s, f i ≤ D * 2 ^ k := by
  classical
  by_contra! hlarge
  let T := D * 2 ^ k
  let x : ℚ := 1 / ((T : ℚ) + 1)
  have hT : (T : ℚ) + 1 > 0 := by positivity
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 := by
    dsimp [x]
    rw [div_le_iff₀ hT]
    have : (0 : ℚ) ≤ T := by positivity
    linarith
  have hup : ∀ i ∈ s, (1 + (1 : ℚ) / f i) ≤ 1 + x := by
    intro i hi
    have h : T + 1 ≤ f i := by have := hlarge i hi; omega
    have hq : (T : ℚ) + 1 ≤ f i := by exact_mod_cast h
    exact add_le_add_right (one_div_le_one_div_of_le hT hq) 1
  have hprod := Finset.prod_le_prod
    (fun i _ => show 0 ≤ (1 + (1 : ℚ) / f i) by positivity) hup
  rw [Finset.prod_const] at hprod
  have hcard : (1 + x) ^ s.card ≤ (1 + x) ^ k :=
    pow_le_pow_right₀ (by linarith) hk
  have hlo : (1 : ℚ) < ∏ i ∈ s, (1 + (1 : ℚ) / f i) := by
    obtain ⟨i, hi⟩ := hs
    have hfi : (0 : ℚ) < f i := by exact_mod_cast hf i hi
    have hfactor : (1 : ℚ) < 1 + (1 : ℚ) / f i := by
      have : 0 < (1 : ℚ) / f i := by positivity
      linarith
    rw [← Finset.mul_prod_erase s (fun j => 1 + (1 : ℚ) / f j) hi]
    have hrest : (1 : ℚ) ≤ ∏ j ∈ s.erase i, (1 + (1 : ℚ) / f j) :=
      Finset.one_le_prod fun j _ => by
        have : 0 ≤ (1 : ℚ) / f j := by positivity
        linarith
    exact hfactor.trans_le (le_mul_of_one_le_right (by positivity) hrest)
  obtain ⟨w, hw⟩ := hdiv
  have hP : 0 < ∏ i ∈ s, f i := Finset.prod_pos hf
  have hwQ : (m : ℚ) * (∏ i ∈ s, (1 + (1 : ℚ) / f i)) = w := by
    rw [product_ratios hf, ← mul_div_assoc]
    have hPq : (0 : ℚ) < ((∏ i ∈ s, f i : ℕ) : ℚ) := by exact_mod_cast hP
    apply (div_eq_iff hPq.ne').mpr
    exact_mod_cast hw.trans (mul_comm _ _)
  have hmQ : (0 : ℚ) < m := by exact_mod_cast hm
  have hlower : m < w := by
    exact_mod_cast (show (m : ℚ) < w by
      rw [← hwQ]
      exact lt_mul_of_one_lt_right hmQ hlo)
  have hupper : (w : ℚ) < (m : ℚ) + 1 := by
    rw [← hwQ]
    apply lt_of_le_of_lt (mul_le_mul_of_nonneg_left
      (hprod.trans (hcard.trans (one_add_pow_upper hx0 hx1 k))) hmQ.le)
    have hdQ : (m : ℚ) ≤ D := by exact_mod_cast hmD
    have hTd : (T : ℚ) = (D : ℚ) * (2 : ℚ) ^ k := by dsimp [T]; push_cast; rfl
    have hpow : (0 : ℚ) ≤ (2 : ℚ) ^ k := by positivity
    have hh : (m : ℚ) * ((2 : ℚ) ^ k - 1) < (T : ℚ) + 1 := by
      rw [hTd]
      nlinarith [mul_nonneg (sub_nonneg.mpr hdQ) hpow]
    dsimp [x]
    rw [mul_one_div, mul_add, mul_one, ← mul_div_assoc, add_lt_add_iff_left, div_lt_iff₀ hT]
    simpa using hh
  have : w < m + 1 := by exact_mod_cast hupper
  omega

/-- Bounded external factors and a bounded number of components bound their product. -/
private theorem bounded_of_card (k : ℕ) :
    ∀ D : ℕ, ∃ B : ℕ, ∀ (s : Finset ℕ) (f : ℕ → ℕ) (m : ℕ),
      s.card ≤ k → (∀ i ∈ s, 0 < f i) → 0 < m → m ≤ D →
      (∏ i ∈ s, f i) ∣ m * ∏ i ∈ s, (f i + 1) → ∏ i ∈ s, f i ≤ B := by
  induction k with
  | zero =>
    intro D
    refine ⟨1, fun s f m hk _ _ _ _ => ?_⟩
    simp [Finset.card_eq_zero.mp (Nat.le_zero.mp hk)]
  | succ k ih =>
    intro D
    let T := D * 2 ^ (k + 1)
    obtain ⟨B, hB⟩ := ih (D * (T + 1))
    refine ⟨max 1 (T * B), fun s f m hk hf hm hmD hdiv => ?_⟩
    by_cases hs : s.Nonempty
    · obtain ⟨i, hi, hsmall⟩ := exists_small_component hs hf hk hm hmD hdiv
      have hc : (s.erase i).card ≤ k := by
        have := Finset.card_erase_add_one hi
        omega
      have hdiv' : (∏ j ∈ s.erase i, f j) ∣
          (m * (f i + 1)) * ∏ j ∈ s.erase i, (f j + 1) := by
        rw [mul_assoc m, Finset.mul_prod_erase s (fun j => f j + 1) hi]
        exact (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.erase_subset i s)).trans hdiv
      have ht : f i ≤ T := hsmall
      have hrest := hB (s.erase i) f (m * (f i + 1)) hc
        (fun j hj => hf j (Finset.mem_of_mem_erase hj)) (by positivity)
        (Nat.mul_le_mul hmD (Nat.add_le_add_right ht 1)) hdiv'
      rw [← Finset.mul_prod_erase s f hi]
      exact (Nat.mul_le_mul ht hrest).trans (le_max_right _ _)
    · rw [Finset.not_nonempty_iff_eq_empty.mp hs, Finset.prod_empty]
      exact le_max_left _ _

private theorem card_le_external {s : Finset ℕ} {f : ℕ → ℕ} {m : ℕ}
    (hf : ∀ i ∈ s, Odd (f i) ∧ 3 ≤ f i) (hm : 0 < m)
    (hdiv : (∏ i ∈ s, f i) ∣ m * ∏ i ∈ s, (f i + 1)) :
    s.card ≤ 2 * m := by
  classical
  let P := ∏ i ∈ s, f i
  let Q := ∏ i ∈ s, (f i + 1)
  let k := s.card
  have hP : 0 < P := Finset.prod_pos fun i hi => by have := (hf i hi).2; omega
  have hQ : 0 < Q := Finset.prod_pos fun _ _ => by omega
  have hodd : Odd P := by
    dsimp [P]
    exact Finset.prod_induction f Odd (fun a b => Odd.mul) odd_one (fun i hi => (hf i hi).1)
  have hcop : P.Coprime (2 ^ k) := by
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_two_right]
    exact hodd
  have htwo : 2 ^ k ∣ Q := by
    dsimp [k, Q]
    rw [← Finset.prod_const]
    exact Finset.prod_dvd_prod_of_dvd _ _ fun i hi => by
      have h := (hf i hi).1
      exact (h.add_odd odd_one).two_dvd
  have hboth := hcop.mul_dvd_of_dvd_of_dvd hdiv (dvd_mul_of_dvd_right htwo m)
  have hle := Nat.le_of_dvd (Nat.mul_pos hm hQ) hboth
  have hr : ∏ i ∈ s, (1 + (1 : ℚ) / f i) ≤ (4 / 3 : ℚ) ^ k := by
    dsimp [k]
    rw [← Finset.prod_const]
    apply Finset.prod_le_prod (fun _ _ => by positivity)
    intro i hi
    have h3 : (3 : ℚ) ≤ f i := by exact_mod_cast (hf i hi).2
    have hrec := one_div_le_one_div_of_le (by norm_num : (0 : ℚ) < 3) h3
    linarith
  have hpq : (0 : ℚ) < P := by exact_mod_cast hP
  have hmq : (0 : ℚ) ≤ m := by positivity
  have hscale : (2 : ℚ) ^ k ≤ (m : ℚ) * (4 / 3 : ℚ) ^ k := calc
    _ ≤ (m : ℚ) * (Q : ℚ) / (P : ℚ) := by
      apply (le_div_iff₀ hpq).mpr
      exact_mod_cast (mul_comm P (2 ^ k)) ▸ hle
    _ = (m : ℚ) * ∏ i ∈ s, (1 + (1 : ℚ) / f i) := by
      rw [product_ratios (fun i hi => by have := (hf i hi).2; omega), mul_div_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_left hr hmq
  have hkbound : (3 / 2 : ℚ) ^ k ≤ m := by
    have hh := (div_le_iff₀ (by positivity : 0 < (4 / 3 : ℚ) ^ k)).mpr hscale
    rw [← div_pow] at hh
    norm_num at hh
    exact hh
  have hbern := one_add_mul_le_pow (a := (1 / 2 : ℚ)) (by norm_num) k
  norm_num at hbern
  have hrk : (k : ℚ) ≤ 2 * (m : ℚ) := by linarith
  exact_mod_cast hrk

/-- An odd product of components has bounded size if its successor product supplies everything
except a bounded positive external factor. -/
theorem bounded_of_external (D : ℕ) :
    ∃ B : ℕ, ∀ (s : Finset ℕ) (f : ℕ → ℕ) (m : ℕ),
      (∀ i ∈ s, Odd (f i) ∧ 3 ≤ f i) → 0 < m → m ≤ D →
      (∏ i ∈ s, f i) ∣ m * ∏ i ∈ s, (f i + 1) → ∏ i ∈ s, f i ≤ B := by
  obtain ⟨B, hB⟩ := bounded_of_card (2 * D) D
  refine ⟨B, fun s f m hf hm hmD hd => hB s f m ?_ ?_ hm hmD hd⟩
  · exact (card_le_external hf hm hd).trans (Nat.mul_le_mul_left 2 hmD)
  · intro i hi
    have := (hf i hi).2
    omega

end OMA.UnitaryCoreAudit

namespace OMA.R_Erdos1052_erdos_1052_R2_H1_R1

open scoped BigOperators
open OMA.R_Erdos1052_erdos_1052_R2

private def simple (n : ℕ) : Finset ℕ :=
  n.primeFactors.filter (fun p => p ≠ 2 ∧ n.factorization p = 1)

private def repeated (n : ℕ) : Finset ℕ :=
  n.primeFactors.filter (fun p => p ≠ 2 ∧ n.factorization p ≠ 1)

private def core (n : ℕ) : ℕ :=
  ∏ p ∈ repeated n, p ^ n.factorization p

private def repeatShifts (n : ℕ) : ℕ :=
  ∏ p ∈ repeated n, (p ^ n.factorization p + 1)

private def simpleShifts (n : ℕ) : ℕ :=
  ∏ p ∈ simple n, (p + 1)

private def seed (n : ℕ) : ℕ := 2 ^ n.factorization 2 + 1

private theorem components {n : ℕ} {p : ℕ} (hp : p ∈ repeated n) :
    Odd (p ^ n.factorization p) ∧ 3 ≤ p ^ n.factorization p := by
  obtain ⟨hp, h2, h1⟩ := Finset.mem_filter.mp hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hpos := hprime.factorization_pos_of_dvd
    (Nat.mem_primeFactors.mp hp).2.2 (Nat.dvd_of_mem_primeFactors hp)
  have h3 : 3 ≤ p := by have := hprime.two_le; omega
  refine ⟨(hprime.odd_of_ne_two h2).pow, h3.trans ?_⟩
  exact Nat.le_pow (by omega)

private theorem core_dvd_product {n : ℕ} (hn : Erdos1052.IsUnitaryPerfect n) :
    core n ∣ seed n * (simpleShifts n * repeatShifts n) := by
  let T := n.primeFactors.erase 2
  let f := fun p : ℕ => p ^ n.factorization p + 1
  have hT : T = simple n ∪ repeated n := by
    ext p
    simp only [T, simple, repeated, Finset.mem_erase, Finset.mem_union, Finset.mem_filter]
    tauto
  have hd : Disjoint (simple n) (repeated n) := by
    refine Finset.disjoint_left.mpr fun p hp hq => ?_
    exact (Finset.mem_filter.mp hq).2.2 (Finset.mem_filter.mp hp).2.2
  have hs : ∏ p ∈ (simple n), f p = simpleShifts n := by
    apply Finset.prod_congr rfl
    intro p hp
    simp [f, (Finset.mem_filter.mp hp).2.2]
  have hprod : ∏ p ∈ T, f p = simpleShifts n * repeatShifts n := by
    rw [hT, Finset.prod_union hd, hs]
    rfl
  have hcore : core n ∣ n := calc
    core n ∣ ∏ p ∈ n.primeFactors, p ^ n.factorization p :=
      Finset.prod_dvd_prod_of_subset (repeated n) n.primeFactors _ (Finset.filter_subset _ _)
    _ ∣ n := (prod_primeFactors_pow_self hn.2.ne').dvd
  obtain ⟨hpos, hsum⟩ := sum_udiv_of_isUnitaryPerfect hn
  rw [sum_udiv_eq_prod hpos.ne'] at hsum
  have hb : core n ∣ ∏ p ∈ n.primeFactors, f p := by
    have hb : core n ∣ 2 * n := dvd_mul_of_dvd_right hcore 2
    simpa only [f, add_comm _ 1, hsum] using hb
  rw [← hprod]
  by_cases hTwo : 2 ∈ n.primeFactors
  · rw [show seed n = f 2 from rfl, Finset.mul_prod_erase n.primeFactors f hTwo]
    exact hb
  · have hTeq : T = n.primeFactors := Finset.erase_eq_of_notMem hTwo
    rw [hTeq]
    exact dvd_mul_of_dvd_right hb _

/-- Uniformly bound the contribution of the seed to the repeated odd core. -/
def H1 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    let S := n.primeFactors.filter (fun p => p ≠ 2 ∧ n.factorization p = 1)
    let R := n.primeFactors.filter (fun p => p ≠ 2 ∧ n.factorization p ≠ 1)
    let c := ∏ p ∈ R, p ^ n.factorization p
    4 ≤ S.card → Nat.gcd c (2 ^ n.factorization 2 + 1) ≤ A

/-- Uniformly bound the contribution of all simple-prime shifts to that core. -/
def H2 : Prop :=
  ∃ B : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    let S := n.primeFactors.filter (fun p => p ≠ 2 ∧ n.factorization p = 1)
    let R := n.primeFactors.filter (fun p => p ≠ 2 ∧ n.factorization p ≠ 1)
    let c := ∏ p ∈ R, p ^ n.factorization p
    4 ≤ S.card → Nat.gcd c (∏ p ∈ S, (p + 1)) ≤ B

theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R2.H1 := by
  intro hSeed hSimple
  obtain ⟨A, hA⟩ := hSeed
  obtain ⟨B, hB⟩ := hSimple
  obtain ⟨M, hM⟩ := OMA.UnitaryCoreAudit.bounded_of_external (A * B)
  refine ⟨M, fun n hn hcount => ?_⟩
  let E := Nat.gcd (core n) (seed n) * Nat.gcd (core n) (simpleShifts n)
  have hc : 0 < core n := Finset.prod_pos fun p hp => by have := (components hp).2; omega
  have hE0 : 0 < E := Nat.mul_pos (Nat.gcd_pos_of_pos_left _ hc) (Nat.gcd_pos_of_pos_left _ hc)
  have hEle : E ≤ A * B := Nat.mul_le_mul (hA n hn hcount) (hB n hn hcount)
  have hd : core n ∣ E * repeatShifts n := by
    have dh := core_dvd_product hn
    rw [← mul_assoc] at dh
    have hg := dvd_gcd_mul_of_dvd_mul dh
    exact hg.trans (mul_dvd_mul (gcd_mul_dvd_mul_gcd _ _ _) dvd_rfl)
  exact hM (repeated n) (fun p => p ^ n.factorization p) E (fun _ => components)
    hE0 hEle hd

end OMA.R_Erdos1052_erdos_1052_R2_H1_R1
