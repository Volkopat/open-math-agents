import OMAReductions.R_AgohGiuga_agoh_giuga_variants_giuga_R2_H2_R1_H1_R1

/-! Reciprocal-sum bounds and a congruence for the prime factors other than five. -/

open scoped BigOperators

namespace OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R2_H2_R1_H1_R1_H2_R1

open OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R2_H2_R1

private theorem reciprocal_bound (s T : Finset ℕ) (B K t : ℕ)
    (hs : ∀ p ∈ s, 0 < p) (hsmall : ∀ p ∈ s, p < B → p ∈ T)
    (hlarge : K ≤ B * t) :
    (K : ℚ) * (∑ p ∈ s, 1 / (p : ℚ)) ≤
      (s.card : ℚ) * t + (↑(∑ p ∈ T, ((K + p - 1) / p - t)) : ℚ) := by
  let extra (p : ℕ) := (K + p - 1) / p - t
  let weight (p : ℕ) : ℚ := t + if p ∈ T then (extra p : ℚ) else 0
  have hweight (p : ℕ) (hp : p ∈ s) : (K : ℚ) * (1 / (p : ℚ)) ≤ weight p := by
    have hpQ : (0 : ℚ) < p := by exact_mod_cast hs p hp
    rw [mul_one_div]
    apply (div_le_iff₀ hpQ).2
    by_cases h : p < B
    · have hceil : K ≤ p * ((K + p - 1) / p) := by
        have hm := Nat.mod_lt (K + p - 1) (hs p hp)
        have hd := Nat.div_add_mod (K + p - 1) p
        omega
      have hstep : K ≤ (t + extra p) * p := by
        rw [mul_comm (t + extra p) p]
        exact hceil.trans (Nat.mul_le_mul_left _ (by dsimp [extra]; omega))
      simp only [weight, if_pos (hsmall p hp h)]
      exact_mod_cast hstep
    · have hstep : K ≤ t * p := by
        rw [mul_comm t p]
        exact hlarge.trans (Nat.mul_le_mul_right t (by omega))
      have hbase : (K : ℚ) ≤ (t : ℚ) * p := by exact_mod_cast hstep
      apply hbase.trans
      apply mul_le_mul_of_nonneg_right _ hpQ.le
      dsimp [weight]
      split_ifs
      · exact le_add_of_nonneg_right (Nat.cast_nonneg _)
      · simp
  calc
    _ = ∑ p ∈ s, (K : ℚ) * (1 / (p : ℚ)) := Finset.mul_sum ..
    _ ≤ ∑ p ∈ s, weight p := Finset.sum_le_sum hweight
    _ = (s.card : ℚ) * t + (↑(∑ p ∈ s.filter (· ∈ T), extra p) : ℚ) := by
      simp only [weight, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
        Finset.sum_filter, Nat.cast_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro p _
      split_ifs <;> simp
    _ ≤ _ := by
      apply add_le_add_right
      change (↑(∑ p ∈ s.filter (· ∈ T), extra p) : ℚ) ≤ ↑(∑ p ∈ T, extra p)
      exact_mod_cast (Finset.sum_le_sum_of_subset (f := extra) (s := s.filter (· ∈ T))
        (t := T) (fun _ hp => (Finset.mem_filter.mp hp).2))

private theorem prime_in_wheel (w : List ℕ) (hw : ∀ d ∈ w, Nat.Prime d)
    {p : ℕ} (hp : p.Prime) : p ∈ w ∨ p.Coprime w.prod := by
  induction w with
  | nil => simp
  | cons d w ih =>
    by_cases h : p = d
    · exact Or.inl (by simp [h])
    · rcases ih (fun q hq => hw q (List.mem_cons.mpr (Or.inr hq))) with hm | hc
      · exact Or.inl (List.mem_cons.mpr (Or.inr hm))
      · have hd : d.Prime := hw d List.mem_cons_self
        have hcop : p.Coprime d := hp.coprime_iff_not_dvd.mpr
          (fun hdvd => h ((Nat.prime_dvd_prime_iff_eq hp hd).mp hdvd))
        exact Or.inr (hcop.mul_right hc)

private theorem erase_five_residues {n p : ℕ}
    (hres : ∀ q ∈ n.primeFactors, 5 ≤ q ∧ q % 5 ≠ 1)
    (hp : p ∈ n.primeFactors.erase 5) : p % 5 = 2 ∨ p % 5 = 3 ∨ p % 5 = 4 := by
  have ⟨hne, hmem⟩ := Finset.mem_erase.mp hp
  have hzero : p % 5 ≠ 0 := by
    intro hz
    exact hne ((Nat.prime_dvd_prime_iff_eq Nat.prime_five (Nat.prime_of_mem_primeFactors hmem)).mp
      (Nat.dvd_of_mod_eq_zero hz)).symm
  have hnotone := (hres p hmem).2
  omega

/-- The reciprocals of the factors other than five determine the next base-five digit. -/
private theorem prime_residues_mod_onehundredtwentyfive {n : ℕ} (hn : n ≠ 0) (h5 : 5 ∣ n)
    (hn5 : n % 25 = 5) (hres : ∀ p ∈ n.primeFactors, 5 ≤ p ∧ p % 5 ≠ 1)
    (hsum : ∑ p ∈ n.primeFactors, (1 / (p : ℚ)) - 1 / (n : ℚ) = 1) :
    let s := n.primeFactors.erase 5
    let a := (s.filter (fun p => p % 5 = 2)).card
    let b := (s.filter (fun p => p % 5 = 3)).card
    let c := (s.filter (fun p => p % 5 = 4)).card
    n + 25 * (3*a + 2*b + 4*c) ≡ 30 [MOD 125] := by
  intro s a b c
  let w (p : ℕ) := 3 * (if p % 5 = 2 then 1 else 0) +
    2 * (if p % 5 = 3 then 1 else 0) + 4 * (if p % 5 = 4 then 1 else 0)
  have hw : (∑ p ∈ s, w p) = 3*a + 2*b + 4*c := by
    simp only [w, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_boole, Nat.cast_id, a, b, c]
  have h5mem : 5 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_five, h5, hn⟩
  have hn25 : n ≡ 5 [MOD 25] := hn5
  have hterm (p : ℕ) (hp : p ∈ s) : n / p ≡ 5 * w p [MOD 25] := by
    have ⟨hne, hmem⟩ := Finset.mem_erase.mp hp
    have hcop5 : Nat.Coprime 5 p := Nat.prime_five.coprime_iff_not_dvd.mpr (by
      intro hd
      exact hne ((Nat.prime_dvd_prime_iff_eq Nat.prime_five (Nat.prime_of_mem_primeFactors hmem)).mp hd).symm)
    have hcop : Nat.Coprime 25 p := hcop5.mul_left hcop5
    apply Nat.ModEq.cancel_left_of_coprime hcop
    have hinv : p * w p ≡ 1 [MOD 5] := by
      rcases erase_five_residues hres hp with h | h | h <;>
        rw [Nat.ModEq, Nat.mul_mod] <;> norm_num [w, h]
    have hscaled := hinv.mul_left' 5
    rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_primeFactors hmem)]
    exact hn25.trans (by simpa only [mul_one, mul_left_comm] using hscaled.symm)
  have hterms := Nat.ModEq.sum hterm
  rw [← Finset.mul_sum, hw] at hterms
  have hclear : n / 5 + 5 * (3*a + 2*b + 4*c) ≡ n + 1 [MOD 25] := by
    apply (hterms.symm.add_left (n / 5)).trans
    rw [add_comm, Finset.sum_erase_add _ _ h5mem, sum_div_eq_add_one hn hsum]
  have hscale := hclear.mul_left' 5
  have hscale' : n + 25 * (3*a + 2*b + 4*c) ≡ 5*(n+1) [MOD 125] := by
    rw [mul_add, Nat.mul_div_cancel' h5, ← mul_assoc] at hscale
    exact hscale
  have hend := (hn25.mul_left' 5).add_right 5
  exact hscale'.trans (by simpa only [mul_add, mul_one] using hend)

set_option maxRecDepth 15000 in
set_option maxHeartbeats 10000000 in
/-- Exact integer certificate for the excess reciprocal weights below the cutoff. -/
private theorem residue_four_certificate :
    let wheelPrimes : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]
    (∑ p ∈ (Finset.Ico 5 10000).filter (fun p =>
        p % 5 = 4 ∧ (p ∈ wheelPrimes ∨ p.Coprime wheelPrimes.prod)),
      ((100000000 + p - 1) / p - 10000)) ≤ 26090000 := by
  intro wheelPrimes
  rw [Finset.sum_filter]
  let weight (p : ℕ) : ℕ :=
    if p % 5 = 4 ∧ (p ∈ wheelPrimes ∨ p.Coprime wheelPrimes.prod) then
      (100000000 + p - 1) / p - 10000 else 0
  change (∑ p ∈ Finset.Ico 5 10000, weight p) ≤ 26090000
  have h1000 : (∑ p ∈ Finset.Ico 5 1000, weight p) = 21534869 := by
    dsimp only [weight, wheelPrimes]
    decide +kernel
  have h2000 : (∑ p ∈ Finset.Ico 1000 2000, weight p) = 2131912 := by
    dsimp only [weight, wheelPrimes]
    decide +kernel
  have h3000 : (∑ p ∈ Finset.Ico 2000 3000, weight p) = 942915 := by
    dsimp only [weight, wheelPrimes]
    decide +kernel
  have h4000 : (∑ p ∈ Finset.Ico 3000 4000, weight p) = 592905 := by
    dsimp only [weight, wheelPrimes]
    decide +kernel
  have h5000 : (∑ p ∈ Finset.Ico 4000 5000, weight p) = 347505 := by
    dsimp only [weight, wheelPrimes]
    decide +kernel
  have h6000 : (∑ p ∈ Finset.Ico 5000 6000, weight p) = 224375 := by
    dsimp only [weight, wheelPrimes]
    decide +kernel
  have h7000 : (∑ p ∈ Finset.Ico 6000 7000, weight p) = 150044 := by
    dsimp only [weight, wheelPrimes]
    decide +kernel
  have h8000 : (∑ p ∈ Finset.Ico 7000 8000, weight p) = 98970 := by
    dsimp only [weight, wheelPrimes]
    decide +kernel
  have h9000 : (∑ p ∈ Finset.Ico 8000 9000, weight p) = 51747 := by
    dsimp only [weight, wheelPrimes]
    decide +kernel
  have h10000 : (∑ p ∈ Finset.Ico 9000 10000, weight p) = 13832 := by
    dsimp only [weight, wheelPrimes]
    decide +kernel
  rw [
    ← Finset.sum_Ico_consecutive weight (m := 5) (n := 9000) (k := 10000) (by decide) (by decide),
    ← Finset.sum_Ico_consecutive weight (m := 5) (n := 8000) (k := 9000) (by decide) (by decide),
    ← Finset.sum_Ico_consecutive weight (m := 5) (n := 7000) (k := 8000) (by decide) (by decide),
    ← Finset.sum_Ico_consecutive weight (m := 5) (n := 6000) (k := 7000) (by decide) (by decide),
    ← Finset.sum_Ico_consecutive weight (m := 5) (n := 5000) (k := 6000) (by decide) (by decide),
    ← Finset.sum_Ico_consecutive weight (m := 5) (n := 4000) (k := 5000) (by decide) (by decide),
    ← Finset.sum_Ico_consecutive weight (m := 5) (n := 3000) (k := 4000) (by decide) (by decide),
    ← Finset.sum_Ico_consecutive weight (m := 5) (n := 2000) (k := 3000) (by decide) (by decide),
    ← Finset.sum_Ico_consecutive weight (m := 5) (n := 1000) (k := 2000) (by decide) (by decide)]
  rw [h1000, h2000, h3000, h4000, h5000, h6000, h7000, h8000, h9000, h10000]
  decide

private theorem residue_four_card_bound (s : Finset ℕ)
    (hprime : ∀ p ∈ s, p.Prime ∧ 5 ≤ p ∧ p % 5 = 4)
    (hs : (598 : ℚ) / 1000 < ∑ p ∈ s, (1 / (p : ℚ))) : 3372 ≤ s.card := by
  let wheelPrimes : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43,
    47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]
  let T := (Finset.Ico 5 10000).filter (fun p =>
    p % 5 = 4 ∧ (p ∈ wheelPrimes ∨ p.Coprime wheelPrimes.prod))
  have hw : ∀ d ∈ wheelPrimes, Nat.Prime d := by dsimp [wheelPrimes]; decide
  have hsmall (p : ℕ) (hp : p ∈ s) (hb : p < 10000) : p ∈ T := by
    have ⟨hpprime, hge, hmod⟩ := hprime p hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hge, hb⟩,
      hmod, prime_in_wheel wheelPrimes hw hpprime⟩
  have hbound := reciprocal_bound s T 10000 100000000 10000
    (fun _ hp => (hprime _ hp).1.pos) hsmall (by decide)
  have hcert : (∑ p ∈ T, ((100000000 + p - 1) / p - 10000)) ≤ 26090000 :=
    residue_four_certificate
  have hcertQ : (↑(∑ p ∈ T, ((100000000 + p - 1) / p - 10000)) : ℚ) ≤ 26090000 := by
    exact_mod_cast hcert
  have hstrict := mul_lt_mul_of_pos_left hs (show (0 : ℚ) < 100000000 by norm_num)
  have hcardQ : (3371 : ℚ) < s.card := by linarith
  exact Nat.succ_le_of_lt (by exact_mod_cast hcardQ)

private theorem two_reciprocals_bound {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hp5 : 5 ≤ p) (hq5 : 5 ≤ q) (hne : p ≠ q)
    (hmod : p % 5 = 2 ∨ p % 5 = 3) (heq : p % 5 = q % 5) :
    1 / (p : ℚ) + 1 / (q : ℚ) ≤ 1 / 7 + 1 / 17 := by
  have hpodd := Nat.odd_iff.mp (hp.odd_of_ne_two (by omega))
  have hqodd := Nat.odd_iff.mp (hq.odd_of_ne_two (by omega))
  have pair_le {a b : ℕ} (ha : 7 ≤ a) (hb : 17 ≤ b) :
      1/(a:ℚ) + 1/(b:ℚ) ≤ 1/7 + 1/17 :=
    add_le_add (one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast ha))
      (one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hb))
  by_cases hp7 : p = 7
  · exact pair_le (by omega) (by omega)
  by_cases hq7 : q = 7
  · rw [add_comm (1/(p:ℚ))]
    exact pair_le (by omega) (by omega)
  have hp13 : 13 ≤ p := by omega
  have hq13 : 13 ≤ q := by omega
  have hpbound : 1 / (p : ℚ) ≤ 1 / 13 :=
    one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hp13)
  have hqbound : 1 / (q : ℚ) ≤ 1 / 13 :=
    one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hq13)
  linarith

private theorem card_four_of_two_exceptions {n : ℕ} (hn : n ≠ 0) (h5 : 5 ∣ n)
    (hres : ∀ p ∈ n.primeFactors, 5 ≤ p ∧ p % 5 ≠ 1)
    (hs : ∑ p ∈ n.primeFactors, (1 / (p : ℚ)) - 1 / (n : ℚ) = 1) :
    let s := n.primeFactors.erase 5
    let a := (s.filter (fun p => p % 5 = 2)).card
    let b := (s.filter (fun p => p % 5 = 3)).card
    let c := (s.filter (fun p => p % 5 = 4)).card
    a + b = 2 → (a + 3*b) % 4 = 2 → 3372 ≤ c ∧ n.primeFactors.card = c + 3 := by
  intro s a b c hab habmod
  let E := s.filter (fun p => p % 5 = 2 ∨ p % 5 = 3)
  let C := s.filter (fun p => p % 5 = 4)
  have hE : E.card = 2 := by
    dsimp only [E]
    rw [Finset.filter_or, Finset.card_union_of_disjoint]
    · exact hab
    · refine Finset.disjoint_left.mpr fun p hp hq => ?_
      have hp' := (Finset.mem_filter.mp hp).2
      have hq' := (Finset.mem_filter.mp hq).2
      omega
  have habzero : a = 0 ∨ b = 0 := by omega
  have hallSame (p q : ℕ) (hp : p ∈ E) (hq : q ∈ E) : p % 5 = q % 5 := by
    have ⟨hp', hpm⟩ := Finset.mem_filter.mp hp
    have ⟨hq', hqm⟩ := Finset.mem_filter.mp hq
    rcases habzero with ha | hb
    · have hno (r : ℕ) (hr : r ∈ s) : r % 5 ≠ 2 := by
        intro h
        have hh : 0 < a := Finset.card_pos.mpr ⟨r, Finset.mem_filter.mpr ⟨hr, h⟩⟩
        omega
      have hpnot := hno p hp'
      have hqnot := hno q hq'
      omega
    · have hno (r : ℕ) (hr : r ∈ s) : r % 5 ≠ 3 := by
        intro h
        have hh : 0 < b := Finset.card_pos.mpr ⟨r, Finset.mem_filter.mpr ⟨hr, h⟩⟩
        omega
      have hpnot := hno p hp'
      have hqnot := hno q hq'
      omega
  have hprimes (p : ℕ) (hp : p ∈ s) : p.Prime ∧ 5 ≤ p := by
    have hmem := Finset.mem_of_mem_erase hp
    exact ⟨Nat.prime_of_mem_primeFactors hmem, (hres p hmem).1⟩
  have hEbound : (∑ p ∈ E, (1 / (p : ℚ))) ≤ 1/7 + 1/17 := by
    obtain ⟨p,q,hne,hpair⟩ := Finset.card_eq_two.mp hE
    have hp : p ∈ E := by rw [hpair]; simp
    have hq : q ∈ E := by rw [hpair]; simp
    have hp' := hprimes p (Finset.mem_filter.mp hp).1
    have hq' := hprimes q (Finset.mem_filter.mp hq).1
    rw [hpair, Finset.sum_insert (by simpa using hne), Finset.sum_singleton]
    exact two_reciprocals_bound hp'.1 hq'.1 hp'.2 hq'.2 hne (Finset.mem_filter.mp hp).2 (hallSame p q hp hq)
  have hsplit : E ∪ C = s := by
    apply Finset.Subset.antisymm
    · intro p hp
      rcases Finset.mem_union.mp hp with h | h <;> exact (Finset.mem_filter.mp h).1
    · intro p hp
      rcases erase_five_residues hres hp with h | h | h
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp, Or.inl h⟩)
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp, Or.inr h⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp, h⟩)
  have hdis : Disjoint E C := by
    refine Finset.disjoint_left.mpr fun p hp hq => ?_
    have hp' := (Finset.mem_filter.mp hp).2
    have hq' := (Finset.mem_filter.mp hq).2
    rcases hp' with h | h <;> omega
  have h5mem : 5 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_five,h5,hn⟩
  have hsum_cut : (∑ p ∈ E, (1 / (p : ℚ))) + (∑ p ∈ C, (1 / (p : ℚ))) + 1/5 =
      ∑ p ∈ n.primeFactors, (1 / (p : ℚ)) := by
    rw [← Finset.sum_union hdis, hsplit]
    exact Finset.sum_erase_add _ _ h5mem
  have hpos : 0 < 1 / (n : ℚ) := by positivity
  have hCs : (598 : ℚ) / 1000 < ∑ p ∈ C, (1 / (p : ℚ)) := by linarith
  have hC (p : ℕ) (hp : p ∈ C) : p.Prime ∧ 5 ≤ p ∧ p % 5 = 4 := by
    have ⟨hmem, hmod⟩ := Finset.mem_filter.mp hp
    have hprime := hprimes p hmem
    exact ⟨hprime.1, hprime.2, hmod⟩
  refine ⟨residue_four_card_bound C hC hCs, ?_⟩
  have hunion := Finset.card_union_of_disjoint hdis
  rw [hsplit, hE] at hunion
  have herase : s.card + 1 = n.primeFactors.card := Finset.card_erase_add_one h5mem
  change n.primeFactors.card = C.card + 3
  omega

/-- Exactly two factors other than five lie in the classes two and three. -/
def H1 : Prop :=
  ∀ n : ℕ, n.Composite → Squarefree n → Odd n → ¬ (3 ∣ n) → 5 ∣ n →
    n % 600 = 505 → n.primeFactors.card % 8 = 2 → 3378 ≤ n.primeFactors.card →
    4 ∣ (n.primeFactors.filter (fun p => p % 4 = 3)).card →
    (n.primeFactors.filter (fun p => p % 4 = 1)).card % 4 = 2 →
    (∀ p ∈ n.primeFactors, 5 ≤ p ∧ p % 5 ≠ 1) →
    (∀ p ∈ n.primeFactors, p * (p - 1) ∣ (n / p - 1)) →
    (∀ p ∈ n.primeFactors, ∀ q ∈ n.primeFactors, ¬ (p ∣ (q - 1))) →
    (∑ p ∈ n.primeFactors, (1 / (p : ℚ)) - 1 / (n : ℚ) = 1) →
    (let s := n.primeFactors.erase 5
     let a := (s.filter (fun p => p % 5 = 2)).card
     let b := (s.filter (fun p => p % 5 = 3)).card
     let c := (s.filter (fun p => p % 5 = 4)).card
     a + b = 2 ∧ (a + 3*b) % 4 = 2 ∧ c % 2 = 1 ∧ 3372 ≤ c ∧
       (n + 25 * (3*a + 2*b + 4*c) ≡ 30 [MOD 125])) → False

/-- At least four factors other than five lie in the classes two and three. -/
def H2 : Prop :=
  ∀ n : ℕ, n.Composite → Squarefree n → Odd n → ¬ (3 ∣ n) → 5 ∣ n →
    n % 600 = 505 → n.primeFactors.card % 8 = 2 → 66 ≤ n.primeFactors.card →
    4 ∣ (n.primeFactors.filter (fun p => p % 4 = 3)).card →
    (n.primeFactors.filter (fun p => p % 4 = 1)).card % 4 = 2 →
    (∀ p ∈ n.primeFactors, 5 ≤ p ∧ p % 5 ≠ 1) →
    (∀ p ∈ n.primeFactors, p * (p - 1) ∣ (n / p - 1)) →
    (∀ p ∈ n.primeFactors, ∀ q ∈ n.primeFactors, ¬ (p ∣ (q - 1))) →
    (∑ p ∈ n.primeFactors, (1 / (p : ℚ)) - 1 / (n : ℚ) = 1) →
    (let s := n.primeFactors.erase 5
     let a := (s.filter (fun p => p % 5 = 2)).card
     let b := (s.filter (fun p => p % 5 = 3)).card
     let c := (s.filter (fun p => p % 5 = 4)).card
     4 ≤ a + b ∧ (a + 3*b) % 4 = 2 ∧ c % 2 = 1 ∧
       (n + 25 * (3*a + 2*b + 4*c) ≡ 30 [MOD 125])) → False

theorem main : H1 → H2 → OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R2_H2_R1_H1_R1.H2 := by
  intro htwo hmany n hcomp hsq hodd hnot3 h5 hn600 hcard hlarge hr3 hr1 hres hstrong hnorm hsum hcounts
  let s := n.primeFactors.erase 5
  let a := (s.filter (fun p => p % 5 = 2)).card
  let b := (s.filter (fun p => p % 5 = 3)).card
  let c := (s.filter (fun p => p % 5 = 4)).card
  change c % 2 = 1 ∧ (a + 3*b) % 4 = 2 ∧ 2 ≤ a + b at hcounts
  obtain ⟨hc, habmod, hablower⟩ := hcounts
  have hn25 : n % 25 = 5 := by omega
  have hmod : n + 25 * (3*a + 2*b + 4*c) ≡ 30 [MOD 125] :=
    prime_residues_mod_onehundredtwentyfive hsq.ne_zero h5 hn25 hres hsum
  by_cases hab : a + b = 2
  · obtain ⟨hbound, hsumcard⟩ : 3372 ≤ c ∧ n.primeFactors.card = c + 3 :=
      card_four_of_two_exceptions hsq.ne_zero h5 hres hsum hab habmod
    have hlarge' : 3378 ≤ n.primeFactors.card := by omega
    exact htwo n hcomp hsq hodd hnot3 h5 hn600 hcard hlarge' hr3 hr1 hres hstrong hnorm hsum
      ⟨hab, habmod, hc, hbound, hmod⟩
  · have habfour : 4 ≤ a + b := by omega
    exact hmany n hcomp hsq hodd hnot3 h5 hn600 hcard hlarge hr3 hr1 hres hstrong hnorm hsum
      ⟨habfour, habmod, hc, hmod⟩

end OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R2_H2_R1_H1_R1_H2_R1
