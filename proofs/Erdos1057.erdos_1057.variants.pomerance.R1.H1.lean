import OMAReductions.R_Erdos1057_erdos_1057_variants_pomerance_R1
import Mathlib

-- Step H1 of the reduction Erdos1057.erdos_1057.variants.pomerance.R1: the sharp upper bound
-- C(x) <= x / L(x)^(1 - eps) for the number of Carmichael numbers up to x, where
-- L(x) = exp (log x * log log log x / log log x). Pomerance, Selfridge and Wagstaff,
-- The pseudoprimes to 25 * 10^9, Math. Comp. 35 (1980), Theorem 6.
-- Credit: @chris01-dev
--
-- The elementary counting lemmas (Korselt congruences, the large prime divisor class, the
-- divisor just above a cutoff, the Rankin product and the prime reciprocal sum) are taken from
-- the merged proof of Erdos1057.erdos_1057.variants.upper_bound in this repository, which
-- obtains the bound with the constant 1/2000. The sharp constant needs a different split:
-- the cutoff is x^(1 - delta) instead of the square root, the divisor d above the cutoff is
-- weighted by 1 + x / (d * lambda d) for every exponent, the divisors with a fixed small
-- exponent m are summed with weight 1 / d by the Rankin method, and the exponents are summed
-- with the harmonic weight 1 / m.

namespace CarmichaelCount

open Filter Finset Real
open scoped Topology

private theorem carmichael_composite {n : ℕ} (hn : IsCarmichael n) : ¬n.Prime ∧ 1 < n :=
  (hn 1 (by decide) (Nat.coprime_one_right n)).2

/-- The exponent of the group of units modulo a Carmichael number divides its predecessor. -/
private theorem carmichael_exponent_dvd {n : ℕ} (hn : IsCarmichael n) :
    ArithmeticFunction.carmichael n ∣ n - 1 := by
  have hn1 := (carmichael_composite hn).2
  have : NeZero n := ⟨by omega⟩
  rw [ArithmeticFunction.carmichael_eq_exponent']
  apply Monoid.exponent_dvd_of_forall_pow_eq_one
  intro a
  let b : ℕ := (a : ZMod n).val + n
  have hb : 1 ≤ b := by unfold b; omega
  have hcast : (b : ZMod n) = a := by simp [b]
  have hc : n.Coprime b := ((ZMod.isUnit_iff_coprime b n).1 (hcast ▸ a.isUnit)).symm
  have hp := (Nat.probablePrime_iff_modEq n hb).1 (hn b hb hc).1
  apply Units.ext
  simpa [hcast] using (ZMod.natCast_eq_natCast_iff _ _ _).2 hp

private theorem carmichael_prime {p : ℕ} (hp : p.Prime) :
    ArithmeticFunction.carmichael p = p - 1 := by
  by_cases h2 : p = 2
  · subst p
    simpa using ArithmeticFunction.carmichael_two_pow_of_le_two (n := 1) (by decide)
  · simpa [Nat.totient_prime hp] using ArithmeticFunction.carmichael_pow_of_prime_ne_two 1 hp h2

private theorem prime_sub_one_dvd {n p : ℕ} (hn : IsCarmichael n) (hp : p.Prime)
    (hpn : p ∣ n) : p - 1 ∣ n - 1 := by
  rw [← carmichael_prime hp]
  exact (ArithmeticFunction.carmichael_dvd hpn).trans (carmichael_exponent_dvd hn)

private theorem coprime_pred {n : ℕ} (hn : 1 ≤ n) : n.Coprime (n - 1) := by
  apply Nat.coprime_of_dvd
  intro p hp hpn hpp
  apply hp.not_dvd_one
  have hb := Nat.dvd_sub hpn hpp
  rwa [show n - (n - 1) = 1 by omega] at hb

private theorem carmichael_squarefree {n : ℕ} (hn : IsCarmichael n) : Squarefree n := by
  refine Nat.squarefree_iff_prime_squarefree.2 fun p hp hpp => ?_
  have hp' : p ∣ ArithmeticFunction.carmichael (p ^ 2) := by
    by_cases h : p = 2
    · subst p
      rw [ArithmeticFunction.carmichael_two_pow_of_le_two (by decide)]
      decide
    · rw [ArithmeticFunction.carmichael_pow_of_prime_ne_two _ hp h, Nat.totient_prime_pow hp (by decide : 0 < 2)]
      simp
  have hpn : p ∣ n := (dvd_mul_right p p).trans hpp
  have hdiv : p ^ 2 ∣ n := by simpa [pow_two] using hpp
  have hppred := hp'.trans ((ArithmeticFunction.carmichael_dvd hdiv).trans (carmichael_exponent_dvd hn))
  exact hp.not_dvd_one <| (coprime_pred (by have := (carmichael_composite hn).2; omega) :
    n.Coprime (n - 1)).gcd_eq_one ▸ Nat.dvd_gcd hpn hppred

/-- The least divisor above the cutoff is at most the cutoff times the largest prime factor. -/
private theorem exists_large_divisor {n : ℕ} {a b : ℝ} (ha : 1 ≤ a)
    (hn : a < n) (hsmall : ∀ p : ℕ, p.Prime → p ∣ n → (p : ℝ) ≤ b) :
    ∃ d : ℕ, d ∣ n ∧ a < d ∧ (d : ℝ) ≤ a * b := by
  classical
  let h : ∃ d : ℕ, a < d ∧ d ∣ n := ⟨n, hn, dvd_rfl⟩
  let d := Nat.find h
  obtain ⟨had, hdn⟩ : a < (d : ℝ) ∧ d ∣ n := Nat.find_spec h
  have hd : 1 < d := by exact_mod_cast ha.trans_lt had
  obtain ⟨p, hp, c, hc⟩ := Nat.exists_prime_and_dvd (show d ≠ 1 by omega)
  have hcpos : 0 < c := by
    by_contra! hzero
    have : c = 0 := by omega
    simp [this] at hc
    omega
  have hcd : c < d := by rw [hc]; simpa using (Nat.mul_lt_mul_of_pos_right hp.one_lt hcpos)
  have hcn : c ∣ n := (show c ∣ d by rw [hc]; exact dvd_mul_left ..).trans hdn
  have hca : (c : ℝ) ≤ a := by
    by_contra! hnca
    exact (Nat.find_min h hcd) ⟨hnca, hcn⟩
  have hpb := hsmall p hp ((show p ∣ d from ⟨c, hc⟩).trans hdn)
  refine ⟨d, hdn, had, ?_⟩
  rw [hc, Nat.cast_mul, mul_comm]
  exact mul_le_mul hca hpb (by positivity) (by linarith)

private theorem carmichael_from_prime {n p : ℕ} (hn : IsCarmichael n)
    (hp : p.Prime) (hpn : p ∣ n) : ∃ j : ℕ, 0 < j ∧ n = p * (1 + (p - 1) * j) := by
  obtain ⟨k, hk⟩ := hpn
  have hn' := carmichael_composite hn
  have hk' : 1 < k := by
    by_contra! hsmall
    interval_cases k
    · simp_all
    · simp_all
  have heq : n - 1 = (k - 1) + (p - 1) * k := by
    have hp' : p - 1 + 1 = p := Nat.sub_add_cancel hp.one_lt.le
    have hk'' : k - 1 + 1 = k := Nat.sub_add_cancel hk'.le
    calc
      n - 1 = ((p - 1 + 1) * k) - 1 := by rw [hp', hk]
      _ = _ := by rw [Nat.add_mul, one_mul]; omega
  have hj : p - 1 ∣ k - 1 := by
    have h := Nat.dvd_sub (prime_sub_one_dvd hn hp ⟨k, hk⟩) (dvd_mul_right (p - 1) k)
    rwa [heq, Nat.add_sub_cancel] at h
  obtain ⟨j, hj⟩ := hj
  have hj' : 0 < j := Nat.pos_of_ne_zero (by intro h; simp [h] at hj; omega)
  refine ⟨j, hj', ?_⟩
  rw [hk]
  congr 1
  omega

private noncomputable def carms (N : ℕ) : Finset ℕ := by
  classical
  exact (Icc 1 N).filter IsCarmichael

private theorem mem_carms {n N : ℕ} : n ∈ carms N ↔ IsCarmichael n ∧ n ≤ N := by
  classical
  simp only [carms, mem_filter, mem_Icc]
  constructor
  · tauto
  · rintro ⟨h, hN⟩
    exact ⟨⟨(carmichael_composite h).2.le, hN⟩, h⟩

private theorem count_eq_card {x : ℝ} (hx : 0 ≤ x) :
    Erdos1057.carmichaelCounting x = ((carms ⌊x⌋₊).card : ℝ) := by
  have heq : {n : ℕ | IsCarmichael n ∧ (n : ℝ) ≤ x} = (carms ⌊x⌋₊ : Set ℕ) := by
    ext n
    simp [mem_carms, Nat.le_floor_iff hx]
  unfold Erdos1057.carmichaelCounting
  rw [heq, Set.ncard_coe_finset]

/-- For a fixed divisor, the possible Carmichael numbers occupy one residue class modulo the divisor times its Carmichael exponent. -/
private theorem card_fiber_carmichael_le {N d : ℕ} :
    (((carms N).filter fun n => d ∣ n).card : ℝ) ≤
      1 + (N : ℝ) / (d * ArithmeticFunction.carmichael d) := by
  classical
  let lambdaD := ArithmeticFunction.carmichael d
  let m := d * lambdaD
  let S := (carms N).filter fun n => d ∣ n
  have hcard : S.card ≤ N / m + 1 := by
    rw [← Finset.card_range (N / m + 1)]
    refine Finset.card_le_card_of_injOn (fun k : ℕ => k / m) ?_ ?_
    · intro n hn
      exact mem_range.2 (Nat.lt_succ_of_le (Nat.div_le_div_right (mem_carms.mp (mem_filter.mp hn).1).2))
    · intro a ha b hb heq
      obtain ⟨ha, hda⟩ := mem_filter.mp ha
      obtain ⟨hb, hdb⟩ := mem_filter.mp hb
      have hac := (mem_carms.mp ha).1
      have hbc := (mem_carms.mp hb).1
      have hLambdaeq (n : ℕ) (hn : IsCarmichael n) (hdn : d ∣ n) : 1 ≡ n [MOD lambdaD] :=
        (Nat.modEq_iff_dvd' (carmichael_composite hn).2.le).2
          ((ArithmeticFunction.carmichael_dvd hdn).trans (carmichael_exponent_dvd hn))
      have hcop : d.Coprime lambdaD := (coprime_pred (carmichael_composite hac).2.le).coprime_dvd_left hda
        |>.coprime_dvd_right ((ArithmeticFunction.carmichael_dvd hda).trans (carmichael_exponent_dvd hac))
      have habd : a ≡ b [MOD d] := (Nat.modEq_zero_iff_dvd.mpr hda).trans (Nat.modEq_zero_iff_dvd.mpr hdb).symm
      have hab : a ≡ b [MOD m] := (Nat.modEq_and_modEq_iff_modEq_mul hcop).1
        ⟨habd, (hLambdaeq _ hac hda).symm.trans (hLambdaeq _ hbc hdb)⟩
      change a % m = b % m at hab
      have h₁ := Nat.mod_add_div a m
      have h₂ := Nat.mod_add_div b m
      change a / m = b / m at heq
      rw [hab, heq] at h₁
      omega
  have hcast : (S.card : ℝ) ≤ (N / m : ℕ) + (1 : ℝ) := by exact_mod_cast hcard
  calc
    (S.card : ℝ) ≤ (N / m : ℕ) + (1 : ℝ) := hcast
    _ ≤ 1 + (N : ℝ) / m := by
      have h : ((N / m : ℕ) : ℝ) ≤ (N : ℝ) / m := Nat.cast_div_le
      linarith
    _ = _ := by simp [m, lambdaD]

private theorem card_biUnion_real_le {α β : Type*} [DecidableEq β] (S : Finset α)
    (F : α → Finset β) (u : α → ℝ) (hf : ∀ a ∈ S, ((F a).card : ℝ) ≤ u a) :
    ((S.biUnion F).card : ℝ) ≤ ∑ a ∈ S, u a := by
  calc
    _ ≤ ((∑ a ∈ S, (F a).card : ℕ) : ℝ) := by exact_mod_cast Finset.card_biUnion_le
    _ = ∑ a ∈ S, ((F a).card : ℝ) := by push_cast; rfl
    _ ≤ _ := sum_le_sum hf

private theorem reciprocal_telescope {B : ℕ} (hB : 0 < B) (N : ℕ) :
    ∑ q ∈ Ico B N, 1 / (((q : ℝ) + 1) * q) ≤ 1 / (B : ℝ) := by
  have hsum (M : ℕ) (hM : B ≤ M) :
      ∑ q ∈ Ico B M, 1 / (((q : ℝ) + 1) * q) = 1 / (B : ℝ) - 1 / (M : ℝ) := by
    induction M, hM using Nat.le_induction with
    | base => simp
    | succ m hm ih =>
      rw [sum_Ico_succ_top hm, ih, Nat.cast_succ]
      have ha : (0 : ℝ) < m := by exact_mod_cast (hB.trans_le hm)
      field_simp; ring
  by_cases h : B ≤ N
  · rw [hsum N h]
    exact sub_le_self _ (by positivity)
  · simp [Finset.Ico_eq_empty_of_le (by omega : N ≤ B)]

private noncomputable def carmsLarge (N B : ℕ) : Finset ℕ := by
  classical
  exact (carms N).filter fun n => ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ B < p

/-- The cofactor of a prime divisor is one plus a positive multiple of the prime minus one. -/
private theorem card_large_le {N B : ℕ} (hB : 0 < B) :
    ((carmsLarge N B).card : ℝ) ≤ (N : ℝ) / B := by
  classical
  let F := fun q : ℕ => (Icc 1 (N / ((q + 1) * q))).image
    (fun j => (q + 1) * (1 + q * j))
  have hcover : carmsLarge N B ⊆ (Ico B N).biUnion F := by
    intro n hn
    obtain ⟨hn, p, hp, hpn, hBp⟩ := mem_filter.mp hn
    obtain ⟨hn, hnN⟩ := mem_carms.mp hn
    obtain ⟨j, hj, heq⟩ := carmichael_from_prime hn hp hpn
    let q := p - 1
    have he : q + 1 = p := Nat.sub_add_cancel hp.one_lt.le
    have hpN := (Nat.le_of_dvd (by have := (carmichael_composite hn).2; omega) hpn).trans hnN
    refine mem_biUnion.mpr ⟨q, mem_Ico.mpr ⟨by omega, by omega⟩, mem_image.mpr ?_⟩
    refine ⟨j, mem_Icc.mpr ⟨hj, ?_⟩, by simpa only [he] using heq.symm⟩
    apply (Nat.le_div_iff_mul_le (show 0 < (q + 1) * q from Nat.mul_pos (by omega) (by omega))).2
    calc
      j * ((q + 1) * q) = (q + 1) * (q * j) := by ring
      _ ≤ (q + 1) * (1 + q * j) := by gcongr; omega
      _ = n := by simpa only [he] using heq.symm
      _ ≤ N := hnN
  calc
    _ ≤ (((Ico B N).biUnion F).card : ℝ) := by exact_mod_cast Finset.card_le_card hcover
    _ ≤ ∑ q ∈ Ico B N, (N : ℝ) * (1 / (((q : ℝ) + 1) * q)) := by
      apply card_biUnion_real_le
      intro q hq
      have hcard : (F q).card ≤ N / ((q + 1) * q) := by
        simpa [F, Nat.card_Icc] using (Finset.card_image_le (s := Icc 1 (N / ((q + 1) * q)))
          (f := fun j => (q + 1) * (1 + q * j)))
      calc
        _ ≤ ((N / ((q + 1) * q) : ℕ) : ℝ) := by exact_mod_cast hcard
        _ ≤ (N : ℝ) / (((q : ℝ) + 1) * q) := by
          simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using
            (Nat.cast_div_le (α := ℝ) (m := N) (n := (q + 1) * q))
        _ = _ := by ring
    _ ≤ _ := by
      rw [← Finset.mul_sum, div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left (reciprocal_telescope hB N) (Nat.cast_nonneg N)

private theorem carmichael_pos {d : ℕ} (hd : 0 < d) :
    0 < ArithmeticFunction.carmichael d := by
  have : NeZero d := ⟨hd.ne'⟩
  rw [ArithmeticFunction.carmichael_eq_exponent']
  exact Nat.pos_of_ne_zero Monoid.exponent_ne_zero_of_finite

private noncomputable def midDivs (a L : ℝ) : Finset ℕ := by
  classical
  exact (Icc 1 ⌊a * L⌋₊).filter fun d => a < (d : ℝ)

private noncomputable def lowDivs (a L : ℝ) (m : ℕ) : Finset ℕ := by
  classical
  exact (midDivs a L).filter fun d => Squarefree d ∧ ArithmeticFunction.carmichael d = m

private theorem Icc_one_floor_card_le {x : ℝ} (hx : 0 ≤ x) :
    ((Icc 1 ⌊x⌋₊).card : ℝ) ≤ x := by
  simpa [Nat.card_Icc] using (Nat.floor_le hx)

private theorem midDivs_card_le {a L : ℝ} (ha : 0 ≤ a * L) :
    ((midDivs a L).card : ℝ) ≤ a * L := by
  classical
  apply le_trans _ (Icc_one_floor_card_le ha)
  exact_mod_cast Finset.card_filter_le ..


open Filter Finset Real ArithmeticFunction
open scoped Topology ArithmeticFunction.zeta

private theorem sum_rpow_squarefree_le_prod {D P : Finset ℕ} (s : ℝ)
    (hD : ∀ d ∈ D, Squarefree d ∧ d.primeFactors ⊆ P) :
    ∑ d ∈ D, (d : ℝ) ^ s ≤ ∏ p ∈ P, (1 + (p : ℝ) ^ s) := by
  classical
  rw [Finset.prod_one_add]
  let D' := D.image Nat.primeFactors
  have hsub : D' ⊆ P.powerset := by
    intro A hA
    obtain ⟨d, hd, rfl⟩ := mem_image.mp hA
    exact mem_powerset.mpr (hD d hd).2
  have hinj : Set.InjOn Nat.primeFactors (D : Set ℕ) := by
    intro a ha b hb heq
    rw [← Nat.prod_primeFactors_of_squarefree (hD a ha).1, heq,
      Nat.prod_primeFactors_of_squarefree (hD b hb).1]
  calc
    _ = ∑ A ∈ D', ∏ p ∈ A, (p : ℝ) ^ s := by
      rw [Finset.sum_image hinj]
      refine sum_congr rfl fun d hd => ?_
      rw [Real.finsetProd_rpow _ _ (fun p _ => Nat.cast_nonneg p), ← Nat.cast_prod,
        Nat.prod_primeFactors_of_squarefree (hD d hd).1]
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity

private theorem prod_one_add_rpow_le_sum {P : Finset ℕ} {s : ℝ}
    (hp : ∀ p ∈ P, p.Prime) :
    ∏ p ∈ P, (1 + (p : ℝ) ^ s) ≤ ∑ n ∈ Icc 1 (∏ p ∈ P, p), (n : ℝ) ^ s := by
  classical
  let f := fun A : Finset ℕ => ∏ p ∈ A, p
  let S := P.powerset.image f
  have hf (A : Finset ℕ) (hA : A ⊆ P) : (f A).primeFactors = A :=
    Nat.primeFactors_prod fun p hp' => hp p (hA hp')
  have hinj : Set.InjOn f (P.powerset : Set (Finset ℕ)) := by
    intro A hA B hB heq
    rw [← hf A (mem_powerset.mp hA), heq, hf B (mem_powerset.mp hB)]
  have hsub : S ⊆ Icc 1 (∏ p ∈ P, p) := by
    intro n hn
    obtain ⟨A, hA, rfl⟩ := mem_image.mp hn
    have hA' := mem_powerset.mp hA
    refine mem_Icc.mpr ⟨?_, Nat.le_of_dvd ?_ (Finset.prod_dvd_prod_of_subset _ _ _ hA')⟩
    · exact Finset.prod_pos fun p hp' => (hp p (hA' hp')).pos
    · exact Finset.prod_pos fun p hp' => (hp p hp').pos
  rw [Finset.prod_one_add]
  calc
    _ = ∑ n ∈ S, (n : ℝ) ^ s := by
      rw [Finset.sum_image hinj]
      refine sum_congr rfl fun A hA => ?_
      rw [Real.finsetProd_rpow _ _ (fun p _ => Nat.cast_nonneg p), ← Nat.cast_prod]
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity

private theorem sum_Icc_rpow_le {N : ℕ} {s : ℝ} (hN : 1 ≤ N) (hs : 1 < s) :
    ∑ n ∈ Icc 1 N, (n : ℝ) ^ (-s) ≤ 1 + 1 / (s - 1) := by
  let f : ℝ → ℝ := fun x => x ^ (-s)
  have hanti : AntitoneOn f (Set.Icc (1 : ℝ) (N : ℝ)) := by
    intro a ha b hb hab
    exact Real.rpow_le_rpow_of_nonpos (by linarith [ha.1]) hab (by linarith)
  have h := AntitoneOn.sum_le_integral_Ico hN (by simpa only [Nat.cast_one] using hanti)
  have hsum : (∑ n ∈ Icc 1 N, f n) = 1 + ∑ n ∈ Ico 1 N, f (n + 1) := by
    have hset : Icc 1 N = insert 1 ((Ico 1 N).image fun n => n + 1) := by
      ext n
      simp only [mem_Icc, mem_insert, mem_image, mem_Ico]
      constructor
      · intro hn
        by_cases he : n = 1
        · exact Or.inl he
        · exact Or.inr ⟨n - 1, by omega, by omega⟩
      · rintro (rfl | ⟨a, ha, rfl⟩) <;> omega
    rw [hset, sum_insert, sum_image (by intro a _ b _ he; simp only at he; omega)]
    · simp [f]
    · simp
  have hint : (∫ x in (1 : ℝ)..(N : ℝ), f x) ≤ 1 / (s - 1) := by
    have hi : (0 : ℝ) ∉ Set.uIcc (1 : ℝ) (N : ℝ) := by
      rw [Set.uIcc_of_le (by exact_mod_cast hN)]
      simp
    change (∫ x in (1 : ℝ)..(N : ℝ), x ^ (-s)) ≤ _
    rw [integral_rpow (r := -s) (Or.inr ⟨by linarith, hi⟩), Real.one_rpow]
    rw [show -s + 1 = -(s - 1) by ring, div_neg, ← neg_div, neg_sub]
    exact div_le_div_of_nonneg_right (sub_le_self _ (by positivity))
      (by linarith)
  rw [show (∑ n ∈ Icc 1 N, (n : ℝ) ^ (-s)) = ∑ n ∈ Icc 1 N, f n from rfl, hsum]
  push_cast at h
  exact add_le_add_right (h.trans hint) 1

private theorem half_le_log_one_add {x : ℝ} (hx : 0 ≤ x) (h₁ : x ≤ 1) :
    x / 2 ≤ Real.log (1 + x) := by
  have h₀ : 0 < 1 + x := by linarith
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr h₀)
  rw [Real.log_inv] at h
  have h' : x / (1 + x) ≤ Real.log (1 + x) := by
    have he : (1 + x)⁻¹ - 1 = -(x / (1 + x)) := by field_simp; ring
    rw [he] at h
    linarith
  exact (div_le_div_of_nonneg_left hx h₀ (by linarith)).trans h'

private theorem sum_prime_rpow_le {P : Finset ℕ} {s : ℝ}
    (hp : ∀ p ∈ P, p.Prime) (hs : 1 < s) :
    ∑ p ∈ P, (p : ℝ) ^ (-s) ≤ 2 * Real.log (1 + 1 / (s - 1)) := by
  have h1 : 1 ≤ ∏ p ∈ P, p := Finset.prod_pos fun p h => (hp p h).pos
  have hprod := (prod_one_add_rpow_le_sum (s := -s) hp).trans (sum_Icc_rpow_le h1 hs)
  have hpos (p : ℕ) : 0 < 1 + (p : ℝ) ^ (-s) := by positivity
  have hp0 : 0 < ∏ p ∈ P, (1 + (p : ℝ) ^ (-s)) := Finset.prod_pos fun p _ => hpos p
  have hlog := Real.log_le_log hp0 hprod
  rw [Real.log_prod (fun p _ => (hpos p).ne')] at hlog
  have hcomp := Finset.sum_le_sum (s := P) fun p h =>
    half_le_log_one_add (x := (p : ℝ) ^ (-s)) (by positivity)
      (Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast (hp p h).one_lt.le) (by linarith))
  simp_rw [div_eq_mul_inv, ← Finset.sum_mul] at hcomp
  linarith


/-- A finite Euler product gives the prime reciprocal bound needed for the split. -/
private theorem prime_reciprocal_bound {T : ℝ} (hT : 1 < T) :
    ∑ p ∈ Nat.primesLE ⌊T⌋₊, (p : ℝ)⁻¹ ≤
      (2 * Real.exp 1) * Real.log (1 + Real.log T) := by
  let u := Real.log T
  have hu : 0 < u := Real.log_pos hT
  let σ := 1 + 1 / u
  have hσ : 1 < σ := lt_add_of_pos_right _ (one_div_pos.mpr hu)
  have hp (p : ℕ) (h : p ∈ Nat.primesLE ⌊T⌋₊) : p.Prime := (Nat.mem_primesLE.mp h).2
  have hb := sum_prime_rpow_le (s := σ) hp hσ
  have heq : 1 / (σ - 1) = u := by simp [σ]
  rw [heq] at hb
  have hcomp : ∀ p ∈ Nat.primesLE ⌊T⌋₊, (p : ℝ)⁻¹ ≤ Real.exp 1 * (p : ℝ) ^ (-σ) := by
    intro p h
    have hpp : 0 < (p : ℝ) := by exact_mod_cast (hp p h).pos
    have hle : (p : ℝ) ≤ T := (Nat.le_floor_iff (by linarith : 0 ≤ T)).mp (Nat.mem_primesLE.mp h).1
    have hlog := Real.log_le_log hpp hle
    have hdiv : Real.log p / u ≤ 1 := (div_le_iff₀ hu).2 (by simpa [u] using hlog)
    rw [← Real.rpow_neg_one, Real.rpow_def_of_pos hpp, Real.rpow_def_of_pos hpp,
      ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    dsimp [σ]
    linarith [show Real.log p * (1 / u) ≤ 1 by simpa [div_eq_mul_inv, one_mul] using hdiv]
  calc
    _ ≤ ∑ p ∈ Nat.primesLE ⌊T⌋₊, Real.exp 1 * (p : ℝ) ^ (-σ) := sum_le_sum hcomp
    _ ≤ _ := by rw [← Finset.mul_sum]; nlinarith [Real.exp_pos 1]

/-- Bound the divisor sum by geometric series over the prime powers in the factorization. -/
private theorem divisor_rpow_sum_le {m : ℕ} (hm : m ≠ 0) {s : ℝ} (hs : 1 / 2 ≤ s) :
    ∑ d ∈ m.divisors, (d : ℝ) ^ (-s) ≤
      Real.exp (4 * ∑ p ∈ m.primeFactors, (p : ℝ) ^ (-s)) := by
  let w : ArithmeticFunction ℝ := ⟨fun n => (n : ℝ) ^ (-s), by simp [Real.zero_rpow,
    show -s ≠ 0 by linarith]⟩
  have hw : w.IsMultiplicative := by
    constructor
    · simp [w]
    · intro a b _
      change ((↑(a * b) : ℝ) ^ (-s)) = _
      rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg a) (Nat.cast_nonneg b)]
      rfl
  let g := (↑ζ : ArithmeticFunction ℝ) * w
  have hg : g.IsMultiplicative := (ArithmeticFunction.isMultiplicative_zeta.natCast).mul hw
  have hprod := ArithmeticFunction.IsMultiplicative.multiplicative_factorization g hg hm
  rw [Nat.prod_factorization_eq_prod_primeFactors] at hprod
  change ((↑ζ : ArithmeticFunction ℝ) * w) m = _ at hprod
  rw [ArithmeticFunction.coe_zeta_mul_apply] at hprod
  change (∑ d ∈ m.divisors, (d : ℝ) ^ (-s)) = _ at hprod
  rw [hprod, Finset.mul_sum, Real.exp_sum]
  refine Finset.prod_le_prod (fun p hp => ?_) (fun p hp => ?_)
  · change 0 ≤ ((↑ζ : ArithmeticFunction ℝ) * w) (p ^ m.factorization p)
    rw [ArithmeticFunction.coe_zeta_mul_apply]
    exact sum_nonneg (fun d _ => Real.rpow_nonneg (Nat.cast_nonneg d) _)
  · have hpp := Nat.prime_of_mem_primeFactors hp
    let v : ℝ := (p : ℝ) ^ (-s)
    have hv : 0 ≤ v := Real.rpow_nonneg (Nat.cast_nonneg p) _
    have hv34 : v ≤ 3 / 4 := by
      have hTwoP : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
      have h₁ : v ≤ (2 : ℝ) ^ (-(1 / 2) : ℝ) :=
        (Real.rpow_le_rpow_of_nonpos zero_lt_two hTwoP (by linarith)).trans
          (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith))
      refine h₁.trans ?_
      rw [Real.rpow_neg zero_le_two, ← Real.sqrt_eq_rpow]
      have hpos : 0 < Real.sqrt 2 := by positivity
      rw [← one_div, div_le_iff₀ hpos]
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    have hv1 : v < 1 := by linarith
    have hvsum : (∑ j ∈ range (m.factorization p + 1), v ^ j) ≤ (1 - v)⁻¹ := by
      have hsumm := summable_geometric_of_lt_one hv hv1
      rw [← tsum_geometric_of_lt_one hv hv1]
      exact hsumm.sum_le_tsum _ (fun _ _ => by positivity)
    have hgeom : (1 - v)⁻¹ ≤ 1 + 4 * v := by
      rw [← one_div, div_le_iff₀ (by linarith : 0 < 1 - v)]
      nlinarith [mul_nonneg hv (show 0 ≤ 3 - 4 * v by linarith)]
    change ((↑ζ : ArithmeticFunction ℝ) * w) (p ^ m.factorization p) ≤ _
    rw [ArithmeticFunction.coe_zeta_mul_apply, Nat.sum_divisors_prime_pow hpp]
    have he : (∑ i ∈ range (m.factorization p + 1), w (p ^ i)) =
        ∑ i ∈ range (m.factorization p + 1), v ^ i := by
      refine sum_congr rfl fun i _ => ?_
      change ((↑(p ^ i) : ℝ) ^ (-s)) = _
      rw [Nat.cast_pow, ← Real.rpow_natCast (p : ℝ) i,
        ← Real.rpow_mul (Nat.cast_nonneg p), mul_comm, Real.rpow_mul_natCast (Nat.cast_nonneg p)]
    rw [he]
    exact hvsum.trans (hgeom.trans (by simpa only [add_comm] using Real.add_one_le_exp (4 * v)))

private noncomputable def allowedPrimes (m : ℕ) : Finset ℕ :=
  (m.divisors.image (fun d : ℕ => d + 1)).filter Nat.Prime

private theorem sum_allowedPrimes_le {m : ℕ} {s : ℝ} (hs : 0 ≤ s) :
    ∑ p ∈ allowedPrimes m, (p : ℝ) ^ (-s) ≤ ∑ d ∈ m.divisors, (d : ℝ) ^ (-s) := by
  calc
    _ ≤ ∑ p ∈ m.divisors.image (fun d : ℕ => d + 1), (p : ℝ) ^ (-s) :=
      sum_le_sum_of_subset_of_nonneg (filter_subset (s := m.divisors.image (fun d : ℕ => d + 1)) Nat.Prime) fun _ _ _ => by positivity
    _ = ∑ d ∈ m.divisors, ((d + 1 : ℕ) : ℝ) ^ (-s) :=
      sum_image (fun _ _ _ _ h => by omega)
    _ ≤ _ := sum_le_sum fun d hd => Real.rpow_le_rpow_of_nonpos
      (by exact_mod_cast Nat.pos_of_mem_divisors hd) (by exact_mod_cast Nat.le_succ d) (by linarith)

private theorem primeFactors_card_log_le {m : ℕ} (hm : 0 < m) :
    (m.primeFactors.card : ℝ) * Real.log 2 ≤ Real.log m := by
  have hprod : 2 ^ m.primeFactors.card ≤ m := by
    calc
      _ = ∏ _p ∈ m.primeFactors, (2 : ℕ) := by simp
      _ ≤ ∏ p ∈ m.primeFactors, p := Finset.prod_le_prod' fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
      _ ≤ m := Nat.le_of_dvd hm (Nat.prod_primeFactors_dvd m)
  have hx : (2 : ℝ) ^ m.primeFactors.card ≤ m := by exact_mod_cast hprod
  have h := Real.log_le_log (by positivity : 0 < (2 : ℝ) ^ m.primeFactors.card) hx
  simpa only [Real.log_pow, mul_comm (Real.log 2)] using h

/-- Split the prime divisors at the cutoff and bound the large-prime part by their number. -/
private theorem sum_primeFactors_rpow_le {m : ℕ} {T s : ℝ}
    (hT : 1 < T) (hs : 0 ≤ s) (hs1 : s ≤ 1) (hc : (m.primeFactors.card : ℝ) ≤ T) :
    ∑ p ∈ m.primeFactors, (p : ℝ) ^ (-s) ≤
      ((2 * Real.exp 1) * Real.log (1 + Real.log T) + 1) * Real.exp ((1 - s) * Real.log T) := by
  classical
  let P := m.primeFactors
  let E := Real.exp ((1 - s) * Real.log T)
  have hE : 0 ≤ E := Real.exp_nonneg _
  let small := P.filter (fun p : ℕ => (p : ℝ) ≤ T)
  let large := P.filter (fun p : ℕ => ¬(p : ℝ) ≤ T)
  have hT0 : 0 < T := by linarith
  have hsmall : ∑ p ∈ small, (p : ℝ) ^ (-s) ≤
      ((2 * Real.exp 1) * Real.log (1 + Real.log T)) * E := by
    have hsub : small ⊆ Nat.primesLE ⌊T⌋₊ := by
      intro p hp
      obtain ⟨hp, hpT⟩ := mem_filter.mp hp
      exact Nat.mem_primesLE.mpr ⟨(Nat.le_floor_iff hT0.le).mpr hpT, Nat.prime_of_mem_primeFactors hp⟩
    have hterm (p : ℕ) (hp : p ∈ small) : (p : ℝ) ^ (-s) ≤ (p : ℝ)⁻¹ * E := by
      obtain ⟨hp, hpT⟩ := mem_filter.mp hp
      have hpp : (0 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
      have he : (p : ℝ) ^ (-s) = ((p : ℝ) ^ (-1 : ℝ)) * ((p : ℝ) ^ (1 - s)) := by
        rw [← Real.rpow_add hpp]
        congr 1
        ring
      rw [he, Real.rpow_neg_one]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have he' : T ^ (1 - s) = E := by
        rw [Real.rpow_def_of_pos hT0]
        simp only [E, mul_comm (Real.log T)]
      rw [← he']
      exact Real.rpow_le_rpow hpp.le hpT (by linarith)
    calc
      _ ≤ ∑ p ∈ small, (p : ℝ)⁻¹ * E := sum_le_sum hterm
      _ = (∑ p ∈ small, (p : ℝ)⁻¹) * E := by rw [Finset.sum_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        ((sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)).trans
          (prime_reciprocal_bound hT)) hE
  have hlarge : ∑ p ∈ large, (p : ℝ) ^ (-s) ≤ E := by
    have hcard : (large.card : ℝ) ≤ (P.card : ℝ) := by
      exact_mod_cast Finset.card_filter_le (s := P) ..
    have hc' : (large.card : ℝ) ≤ T := hcard.trans hc
    calc
      _ ≤ ∑ _p ∈ large, T ^ (-s) := sum_le_sum fun p hp =>
        Real.rpow_le_rpow_of_nonpos hT0 (le_of_not_ge (mem_filter.mp hp).2) (by linarith)
      _ = (large.card : ℝ) * T ^ (-s) := by simp [nsmul_eq_mul]
      _ ≤ T * T ^ (-s) := mul_le_mul_of_nonneg_right hc' (by positivity)
      _ = E := by
        calc
          T * T ^ (-s) = T ^ (1 : ℝ) * T ^ (-s) := by rw [Real.rpow_one]
          _ = _ := by rw [← Real.rpow_add hT0, Real.rpow_def_of_pos hT0]; dsimp [E]; congr 1; ring
  have hsplit : ∑ p ∈ small, (p : ℝ) ^ (-s) + ∑ p ∈ large, (p : ℝ) ^ (-s) =
      ∑ p ∈ P, (p : ℝ) ^ (-s) := Finset.sum_filter_add_sum_filter_not P _ _
  rw [← hsplit, add_mul, one_mul]
  exact add_le_add hsmall hlarge


/-- Rankin sum over squarefree integers supported on the primes allowed by a fixed exponent. -/
private theorem sum_rankin {D : Finset ℕ} {m : ℕ} {s : ℝ}
    (hm : m ≠ 0) (hs : 1 / 2 ≤ s)
    (hD : ∀ d ∈ D, Squarefree d ∧ d.primeFactors ⊆ allowedPrimes m) :
    ∑ d ∈ D, (d : ℝ) ^ (-s) ≤
      Real.exp (Real.exp (4 * ∑ p ∈ m.primeFactors, (p : ℝ) ^ (-s))) :=
  (sum_rpow_squarefree_le_prod (-s) hD).trans
    ((Real.prod_one_add_le_exp_sum _ fun p => by positivity).trans
      (Real.exp_le_exp.mpr ((sum_allowedPrimes_le (show 0 ≤ s by linarith)).trans
        (divisor_rpow_sum_le hm hs))))

/-- The Rankin sum over the squarefree divisors in the middle range with Carmichael exponent m. -/
private theorem lowDivs_rankin {a L s : ℝ} (hs : 1 / 2 ≤ s) (m : ℕ) (hm : 0 < m) :
    ∑ d ∈ lowDivs a L m, (d : ℝ) ^ (-s) ≤
      Real.exp (Real.exp (4 * ∑ p ∈ m.primeFactors, (p : ℝ) ^ (-s))) := by
  classical
  apply sum_rankin hm.ne' hs
  intro d hd
  obtain ⟨hd, hsqd, hLambda⟩ := mem_filter.mp hd
  refine ⟨hsqd, ?_⟩
  intro p hp
  obtain ⟨hp, hpd, _⟩ := Nat.mem_primeFactors.mp hp
  have hdiv : p - 1 ∣ m := by
    rw [← hLambda, ← carmichael_prime hp]
    exact ArithmeticFunction.carmichael_dvd hpd
  exact mem_filter.mpr ⟨mem_image.mpr ⟨p - 1, Nat.mem_divisors.mpr ⟨hdiv, hm.ne'⟩,
    Nat.sub_add_cancel hp.one_lt.le⟩, hp⟩

private theorem sum_inv_Icc_le {y : ℝ} (hy : 1 ≤ y) :
    ∑ m ∈ Icc 1 ⌊y⌋₊, ((m : ℝ))⁻¹ ≤ 1 + Real.log y := by
  have h := harmonic_floor_le_one_add_log y hy
  rw [harmonic_eq_sum_Icc] at h
  push_cast at h
  exact h

/-- Count three classes: small numbers, numbers with a large prime divisor, and numbers with a
squarefree divisor d just above the cutoff, the last class weighted by 1 + x / (d * lambda d). -/
private theorem finite_bound_sharp {x a L s K : ℝ} (hx : 1 ≤ x) (ha : 1 ≤ a) (hL : 1 ≤ L)
    (hs1 : s ≤ 1) (hK : 0 ≤ K)
    (hD : ∀ m : ℕ, 0 < m → (m : ℝ) ≤ L ^ 3 →
      ∑ d ∈ lowDivs a L m, (d : ℝ) ^ (-s) ≤ K) :
    Erdos1057.carmichaelCounting x ≤
      a + 2 * x / L + a * L + x / L ^ 2 + x * (a ^ (s - 1) * K * (1 + 3 * Real.log L)) := by
  classical
  let N := ⌊x⌋₊
  let B := ⌊L⌋₊
  have hX : 0 ≤ x := by linarith
  have hN : (N : ℝ) ≤ x := Nat.floor_le hX
  have ha0 : 0 < a := by linarith
  have hL0 : 0 < L := by linarith
  have hB1 : 1 ≤ B := Nat.floor_pos.mpr hL
  have hB1' : (1 : ℝ) ≤ B := by exact_mod_cast hB1
  have hLB : L / 2 ≤ B := by
    have h := Nat.lt_floor_add_one L
    change L < (B : ℝ) + 1 at h
    linarith
  have hAL : 0 ≤ a * L := by positivity
  have hL3 : 1 ≤ L ^ 3 := one_le_pow₀ hL
  let F := fun d => (carms N).filter fun n => d ∣ n
  let S₀ := Icc 1 ⌊a⌋₊
  let S₁ := carmsLarge N B
  let sq := (midDivs a L).filter fun d => Squarefree d
  let S₂ := sq.biUnion F
  have hcover : carms N ⊆ (S₀ ∪ S₁) ∪ S₂ := by
    intro n hn
    obtain ⟨hcarm, _⟩ := mem_carms.mp hn
    by_cases hnle : (n : ℝ) ≤ a
    · exact mem_union.mpr (Or.inl (mem_union.mpr (Or.inl (mem_Icc.mpr
        ⟨(carmichael_composite hcarm).2.le, (Nat.le_floor_iff ha0.le).mpr hnle⟩))))
    by_cases hlarge : n ∈ S₁
    · exact mem_union.mpr (Or.inl (mem_union.mpr (Or.inr hlarge)))
    have hsmall (p : ℕ) (hp : p.Prime) (hpn : p ∣ n) : (p : ℝ) ≤ L := by
      apply (Nat.le_floor_iff hL0.le).mp
      by_contra! hBp
      exact hlarge (mem_filter.mpr ⟨hn, p, hp, hpn, hBp⟩)
    obtain ⟨d, hdn, had, hdL⟩ := exists_large_divisor ha (lt_of_not_ge hnle) hsmall
    have hdpos : 0 < d := by exact_mod_cast (show (0 : ℝ) < d from ha0.trans had)
    have hmid : d ∈ midDivs a L := mem_filter.mpr
      ⟨mem_Icc.mpr ⟨hdpos, (Nat.le_floor_iff hAL).mpr hdL⟩, had⟩
    have hF : n ∈ F d := mem_filter.mpr ⟨hn, hdn⟩
    exact mem_union.mpr (Or.inr (mem_biUnion.mpr
      ⟨d, mem_filter.mpr ⟨hmid, (carmichael_squarefree hcarm).squarefree_of_dvd hdn⟩, hF⟩))
  have h₀ : (S₀.card : ℝ) ≤ a := Icc_one_floor_card_le ha0.le
  have h₁ : (S₁.card : ℝ) ≤ 2 * x / L := by
    apply (card_large_le hB1).trans
    have : (0 : ℝ) < (B : ℝ) := by linarith
    calc
      (N : ℝ) / B ≤ x / B := div_le_div_of_nonneg_right hN this.le
      _ ≤ x / (L / 2) := div_le_div_of_nonneg_left hX (by positivity) hLB
      _ = _ := by ring
  -- facts about the divisors in the middle range
  have hsq_gt (d : ℕ) (hd : d ∈ sq) : a < (d : ℝ) := (mem_filter.mp (mem_filter.mp hd).1).2
  have hsq_pos (d : ℕ) (hd : d ∈ sq) : 0 < d := by
    exact_mod_cast (show (0 : ℝ) < d from ha0.trans (hsq_gt d hd))
  have hlam_pos (d : ℕ) (hd : d ∈ sq) : (0 : ℝ) < (ArithmeticFunction.carmichael d : ℝ) := by
    exact_mod_cast carmichael_pos (hsq_pos d hd)
  have hsq_card : (sq.card : ℝ) ≤ a * L := by
    apply le_trans _ (midDivs_card_le hAL)
    exact_mod_cast Finset.card_filter_le ..
  let g := fun d : ℕ => 1 / ((d : ℝ) * (ArithmeticFunction.carmichael d : ℝ))
  have hg0 (d : ℕ) : 0 ≤ g d := by
    change 0 ≤ 1 / ((d : ℝ) * (ArithmeticFunction.carmichael d : ℝ))
    positivity
  have hS2 : (S₂.card : ℝ) ≤ ∑ d ∈ sq, (1 + x * g d) := by
    apply card_biUnion_real_le
    intro d hd
    apply (card_fiber_carmichael_le (N := N) (d := d)).trans
    have hle : (N : ℝ) / ((d : ℝ) * ArithmeticFunction.carmichael d) ≤ x * g d := by
      change _ ≤ x * (1 / ((d : ℝ) * (ArithmeticFunction.carmichael d : ℝ)))
      rw [mul_one_div]
      exact div_le_div_of_nonneg_right hN (by positivity)
    linarith
  -- large exponents
  let hi := sq.filter fun d => L ^ 3 ≤ (ArithmeticFunction.carmichael d : ℝ)
  let lo := sq.filter fun d => ¬ L ^ 3 ≤ (ArithmeticFunction.carmichael d : ℝ)
  have hhi : ∑ d ∈ hi, g d ≤ 1 / L ^ 2 := by
    have hterm (d : ℕ) (hd : d ∈ hi) : g d ≤ 1 / (a * L ^ 3) := by
      obtain ⟨hdsq, hC⟩ := mem_filter.mp hd
      change 1 / ((d : ℝ) * (ArithmeticFunction.carmichael d : ℝ)) ≤ _
      apply div_le_div_of_nonneg_left zero_le_one (by positivity)
      exact mul_le_mul (hsq_gt d hdsq).le hC (by positivity) (by positivity)
    have hcard : (hi.card : ℝ) ≤ a * L := by
      apply le_trans _ hsq_card
      exact_mod_cast Finset.card_filter_le ..
    calc
      _ ≤ ∑ _d ∈ hi, 1 / (a * L ^ 3) := sum_le_sum hterm
      _ = (hi.card : ℝ) * (1 / (a * L ^ 3)) := by simp only [sum_const, nsmul_eq_mul]
      _ ≤ (a * L) * (1 / (a * L ^ 3)) := mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = _ := by field_simp
  -- small exponents, grouped by the exponent
  let M := ⌊L ^ 3⌋₊
  have hmaps : ∀ d ∈ lo, ArithmeticFunction.carmichael d ∈ Icc 1 M := by
    intro d hd
    obtain ⟨hdsq, hC⟩ := mem_filter.mp hd
    exact mem_Icc.mpr ⟨carmichael_pos (hsq_pos d hdsq),
      (Nat.le_floor_iff (by positivity)).mpr (le_of_not_ge hC)⟩
  have hA0 : 0 ≤ a ^ (s - 1) := Real.rpow_nonneg ha0.le _
  have hfib (m : ℕ) (hm : m ∈ Icc 1 M) :
      ∑ d ∈ lo.filter (fun d => ArithmeticFunction.carmichael d = m), g d ≤
        (a ^ (s - 1) * K) * ((m : ℝ))⁻¹ := by
    have hm1 : 0 < m := (mem_Icc.mp hm).1
    have hmL : (m : ℝ) ≤ L ^ 3 := (Nat.le_floor_iff (by positivity)).mp (mem_Icc.mp hm).2
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
    have hsub : lo.filter (fun d => ArithmeticFunction.carmichael d = m) ⊆ lowDivs a L m := by
      intro d hd
      obtain ⟨hdlo, hlam⟩ := mem_filter.mp hd
      obtain ⟨hdsq, _⟩ := mem_filter.mp hdlo
      obtain ⟨hdmid, hsqf⟩ := mem_filter.mp hdsq
      exact mem_filter.mpr ⟨hdmid, hsqf, hlam⟩
    have hterm (d : ℕ) (hd : d ∈ lo.filter (fun d => ArithmeticFunction.carmichael d = m)) :
        g d ≤ (a ^ (s - 1) * ((m : ℝ))⁻¹) * (d : ℝ) ^ (-s) := by
      obtain ⟨hdlo, hlam⟩ := mem_filter.mp hd
      obtain ⟨hdsq, _⟩ := mem_filter.mp hdlo
      have had := hsq_gt d hdsq
      have hd0 : (0 : ℝ) < d := ha0.trans had
      change 1 / ((d : ℝ) * (ArithmeticFunction.carmichael d : ℝ)) ≤ _
      rw [hlam]
      have hpow : (d : ℝ) ^ (s - 1) ≤ a ^ (s - 1) :=
        Real.rpow_le_rpow_of_nonpos ha0 had.le (by linarith)
      have hinv : ((d : ℝ))⁻¹ = (d : ℝ) ^ (s - 1) * (d : ℝ) ^ (-s) := by
        rw [← Real.rpow_add hd0, show s - 1 + -s = -1 by ring, Real.rpow_neg_one]
      calc
        1 / ((d : ℝ) * (m : ℝ)) = ((d : ℝ))⁻¹ * ((m : ℝ))⁻¹ := by
          rw [one_div, mul_inv]
        _ = (d : ℝ) ^ (s - 1) * (d : ℝ) ^ (-s) * ((m : ℝ))⁻¹ := by rw [hinv]
        _ ≤ a ^ (s - 1) * (d : ℝ) ^ (-s) * ((m : ℝ))⁻¹ := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hd0.le _)
        _ = _ := by ring
    calc
      _ ≤ ∑ d ∈ lo.filter (fun d => ArithmeticFunction.carmichael d = m),
          (a ^ (s - 1) * ((m : ℝ))⁻¹) * (d : ℝ) ^ (-s) := sum_le_sum hterm
      _ ≤ ∑ d ∈ lowDivs a L m, (a ^ (s - 1) * ((m : ℝ))⁻¹) * (d : ℝ) ^ (-s) :=
        sum_le_sum_of_subset_of_nonneg hsub fun d _ _ =>
          mul_nonneg (mul_nonneg hA0 (by positivity)) (Real.rpow_nonneg (Nat.cast_nonneg d) _)
      _ = (a ^ (s - 1) * ((m : ℝ))⁻¹) * ∑ d ∈ lowDivs a L m, (d : ℝ) ^ (-s) := by
        rw [Finset.mul_sum]
      _ ≤ (a ^ (s - 1) * ((m : ℝ))⁻¹) * K :=
        mul_le_mul_of_nonneg_left (hD m hm1 hmL) (mul_nonneg hA0 (by positivity))
      _ = _ := by ring
  have hlo : ∑ d ∈ lo, g d ≤ a ^ (s - 1) * K * (1 + 3 * Real.log L) := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps g]
    calc
      _ ≤ ∑ m ∈ Icc 1 M, (a ^ (s - 1) * K) * ((m : ℝ))⁻¹ := sum_le_sum hfib
      _ = (a ^ (s - 1) * K) * ∑ m ∈ Icc 1 M, ((m : ℝ))⁻¹ := by rw [Finset.mul_sum]
      _ ≤ (a ^ (s - 1) * K) * (1 + Real.log (L ^ 3)) :=
        mul_le_mul_of_nonneg_left (sum_inv_Icc_le hL3) (mul_nonneg hA0 hK)
      _ = _ := by
        rw [Real.log_pow]
        push_cast
        ring
  have hsplit : ∑ d ∈ hi, g d + ∑ d ∈ lo, g d = ∑ d ∈ sq, g d :=
    Finset.sum_filter_add_sum_filter_not sq _ _
  have h₂ : (S₂.card : ℝ) ≤
      a * L + x * (1 / L ^ 2 + a ^ (s - 1) * K * (1 + 3 * Real.log L)) := by
    calc
      _ ≤ ∑ d ∈ sq, (1 + x * g d) := hS2
      _ = (sq.card : ℝ) + x * ∑ d ∈ sq, g d := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
        simp
      _ ≤ a * L + x * (1 / L ^ 2 + a ^ (s - 1) * K * (1 + 3 * Real.log L)) := by
        rw [← hsplit]
        exact add_le_add hsq_card (mul_le_mul_of_nonneg_left (add_le_add hhi hlo) hX)
  have hcast : ((carms N).card : ℝ) ≤ (S₀.card : ℝ) + S₁.card + S₂.card := by
    have hncard : (carms N).card ≤ S₀.card + S₁.card + S₂.card := calc
      _ ≤ ((S₀ ∪ S₁) ∪ S₂).card := Finset.card_le_card hcover
      _ ≤ (S₀ ∪ S₁).card + S₂.card := Finset.card_union_le (S₀ ∪ S₁) S₂
      _ ≤ _ := Nat.add_le_add_right (Finset.card_union_le S₀ S₁) _
    exact_mod_cast hncard
  rw [count_eq_card hX]
  change ((carms N).card : ℝ) ≤ _
  calc
    _ ≤ (S₀.card : ℝ) + S₁.card + S₂.card := hcast
    _ ≤ a + 2 * x / L + (a * L + x * (1 / L ^ 2 + a ^ (s - 1) * K * (1 + 3 * Real.log L))) :=
      add_le_add (add_le_add h₀ h₁) h₂
    _ = _ := by ring

private theorem eventually_log_le_rpow {r : ℝ} (hr : 0 < r) :
    ∀ᶠ u in atTop, Real.log u ≤ u ^ r := by
  filter_upwards [(isLittleO_log_rpow_atTop hr).bound one_pos,
    eventually_ge_atTop (0 : ℝ)] with u hu hu0
  have hpow : 0 ≤ u ^ r := Real.rpow_nonneg hu0 _
  change ‖Real.log u‖ ≤ 1 * ‖u ^ r‖ at hu
  exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs, abs_of_nonneg hpow] using hu)

private theorem eventually_log_le_mul {c : ℝ} (hc : 0 < c) :
    ∀ᶠ u : ℝ in atTop, Real.log u ≤ c * u := by
  filter_upwards [Real.isLittleO_log_id_atTop.bound hc, eventually_ge_atTop (0 : ℝ)] with u hu hu0
  change ‖Real.log u‖ ≤ c * ‖u‖ at hu
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hu0] at hu
  exact (le_abs_self _).trans hu

/-- The eventual inequalities between the iterated logarithms used by the final count. -/
private theorem params {δ : ℝ} (hδ : 0 < δ) : ∀ᶠ t : ℝ in atTop,
    1 < t ∧ 1 ≤ Real.log t ∧ 1 ≤ Real.log (Real.log t) ∧
    Real.log (Real.log t) ≤ δ / 4 * Real.log t ∧
    6 / δ ^ 2 ≤ t * Real.log (Real.log t) / Real.log t ∧
    4 * ((2 * Real.exp 1) * Real.log (1 + Real.log t) + 1) *
        Real.exp ((1 - δ) * Real.log (Real.log t)) ≤
      Real.log t + Real.log (Real.log (Real.log t)) - Real.log (Real.log t) + Real.log δ := by
  have hd2 : 0 < δ / 2 := by linarith
  let C := 4 * Real.exp 1 + 1
  have hC : 0 < C := by positivity
  have e1 := Real.tendsto_log_atTop.eventually_ge_atTop 1
  have e2 := (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 1
  have e3 := Real.tendsto_log_atTop.eventually (eventually_log_le_mul (show 0 < δ / 4 by linarith))
  have e4 := eventually_log_le_mul (show 0 < δ ^ 2 / 6 by positivity)
  have e5 := Real.tendsto_log_atTop.eventually (eventually_log_le_rpow hd2)
  have e6 := ((tendsto_rpow_atTop hd2).comp Real.tendsto_log_atTop).eventually_ge_atTop (8 * C)
  have e7 := Real.tendsto_log_atTop.eventually
    (eventually_log_le_mul (show (0 : ℝ) < 1 / 4 by norm_num))
  have e8 := Real.tendsto_log_atTop.eventually_ge_atTop (-4 * Real.log δ)
  filter_upwards [eventually_gt_atTop (1 : ℝ), e1, e2, e3, e4, e5, e6, e7, e8] with
    t ht hu1 hv1 hvu htu hvr hur hv4 hld
  simp only [Function.comp_apply] at hv1 hur
  set u := Real.log t with hu
  set v := Real.log u with hv
  have ht0 : 0 < t := by linarith
  have hu0 : 0 < u := by linarith
  have hv0 : 0 < v := by linarith
  refine ⟨ht, hu1, hv1, hvu, ?_, ?_⟩
  · rw [le_div_iff₀ hu0]
    have h6 : 6 / δ ^ 2 * u ≤ t := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      have := mul_le_mul_of_nonneg_left htu (show (0 : ℝ) ≤ 6 by norm_num)
      have hδ2 : 0 < δ ^ 2 := by positivity
      calc 6 * u ≤ 6 * (δ ^ 2 / 6 * t) := this
        _ = t * δ ^ 2 := by ring
    calc 6 / δ ^ 2 * u ≤ t := h6
      _ = t * 1 := by ring
      _ ≤ t * v := mul_le_mul_of_nonneg_left hv1 ht0.le
  · have hr1 : 1 ≤ u ^ (δ / 2) := Real.one_le_rpow hu1 hd2.le
    have hlog2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    have hlog : Real.log (1 + u) ≤ 2 * u ^ (δ / 2) := by
      calc
        Real.log (1 + u) ≤ Real.log (2 * u) := Real.log_le_log (by positivity) (by linarith)
        _ = Real.log 2 + v := by rw [Real.log_mul (by norm_num) hu0.ne']
        _ ≤ _ := by linarith
    have hExp : Real.exp ((1 - δ) * v) = u ^ (1 - δ) := by
      rw [Real.rpow_def_of_pos hu0, mul_comm]
    have hK : (2 * Real.exp 1) * Real.log (1 + u) + 1 ≤ C * u ^ (δ / 2) := by
      have h := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 2 * Real.exp 1 by positivity)
      change _ ≤ (4 * Real.exp 1 + 1) * u ^ (δ / 2)
      linarith
    have hpow : u ^ (δ / 2) * u ^ (1 - δ) = u ^ (1 - δ / 2) := by
      rw [← Real.rpow_add hu0]
      congr 1
      ring
    have hup : (8 * C) * u ^ (1 - δ / 2) ≤ u := by
      calc
        _ ≤ u ^ (δ / 2) * u ^ (1 - δ / 2) := mul_le_mul_of_nonneg_right hur (by positivity)
        _ = u := by
          rw [← Real.rpow_add hu0, show δ / 2 + (1 - δ / 2) = 1 by ring, Real.rpow_one]
    have hlhs : 4 * ((2 * Real.exp 1) * Real.log (1 + u) + 1) * Real.exp ((1 - δ) * v) ≤
        u / 2 := by
      rw [hExp]
      have h1 : ((2 * Real.exp 1) * Real.log (1 + u) + 1) * u ^ (1 - δ) ≤
          C * u ^ (1 - δ / 2) := by
        calc
          _ ≤ (C * u ^ (δ / 2)) * u ^ (1 - δ) := mul_le_mul_of_nonneg_right hK (by positivity)
          _ = _ := by rw [mul_assoc, hpow]
      nlinarith
    have hlv : 0 ≤ Real.log v := Real.log_nonneg hv1
    linarith

set_option maxHeartbeats 1000000 in
/-- The count for one large x, with every eventual inequality as a hypothesis. -/
private theorem final_bound {δ x t u v : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 5) (hx : 1 < x)
    (ht : Real.log x = t) (hu : Real.log t = u) (hv : Real.log u = v)
    (ht1 : 1 < t) (hu1 : 1 ≤ u) (hv1 : 1 ≤ v) (hvu : v ≤ δ / 4 * u)
    (hW : 6 / δ ^ 2 ≤ t * v / u)
    (hE : 4 * ((2 * Real.exp 1) * Real.log (1 + u) + 1) * Real.exp ((1 - δ) * v) ≤
      u + Real.log v - v + Real.log δ) :
    Erdos1057.carmichaelCounting x ≤ x * Real.exp (-(1 - 5 * δ) * (t * v / u)) := by
  have hx0 : 0 < x := by linarith
  have ht0 : 0 < t := by linarith
  have hu0 : 0 < u := by linarith
  have hv0 : 0 < v := by linarith
  set W := t * v / u with hWdef
  have hxe : x = Real.exp t := by rw [← ht, Real.exp_log hx0]
  have hW0 : 0 < W := by positivity
  have hδ2 : 0 < δ ^ 2 := by positivity
  have hW6 : 6 ≤ δ ^ 2 * W := by
    have := (div_le_iff₀ hδ2).mp hW
    linarith
  have hvu' : v / u ≤ δ / 4 := (div_le_iff₀ hu0).mpr hvu
  have hWt : W ≤ δ / 4 * t := by
    have : W = t * (v / u) := by rw [hWdef]; ring
    rw [this]
    linarith [mul_le_mul_of_nonneg_left hvu' ht0.le]
  -- parameters
  let a := Real.exp ((1 - δ) * t)
  let ell := (1 - δ) * W
  let L := Real.exp ell
  let s := 1 - (1 - δ) * (v / u)
  let K := Real.exp (δ * W)
  have hell0 : 0 ≤ ell := mul_nonneg (by linarith) hW0.le
  have hellW : ell ≤ W := by
    change (1 - δ) * W ≤ W
    linarith [mul_nonneg hδ.le hW0.le]
  have ha : 1 ≤ a := Real.one_le_exp (mul_nonneg (by linarith) ht0.le)
  have hL : 1 ≤ L := Real.one_le_exp hell0
  have hsub : 0 ≤ (1 - δ) * (v / u) := mul_nonneg (by linarith) (by positivity)
  have hsub' : (1 - δ) * (v / u) ≤ 1 / 2 := by
    have h1 : (1 - δ) * (v / u) ≤ 1 * (v / u) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    linarith
  have hs : 1 / 2 ≤ s := by change 1 / 2 ≤ 1 - (1 - δ) * (v / u); linarith
  have hs1 : s ≤ 1 := by change 1 - (1 - δ) * (v / u) ≤ 1; linarith
  have hK0 : 0 ≤ K := (Real.exp_pos _).le
  have hlogtwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := half_le_log_one_add (x := 1) (by norm_num) (by norm_num)
    norm_num at h ⊢
    exact h
  have hD : ∀ m : ℕ, 0 < m → (m : ℝ) ≤ L ^ 3 →
      ∑ d ∈ lowDivs a L m, (d : ℝ) ^ (-s) ≤ K := by
    intro m hm hmL
    refine (lowDivs_rankin hs m hm).trans (Real.exp_le_exp.mpr ?_)
    have hmc : (m.primeFactors.card : ℝ) ≤ t := by
      apply le_of_mul_le_mul_right _ (by linarith : 0 < Real.log 2)
      calc
        (m.primeFactors.card : ℝ) * Real.log 2 ≤ Real.log m := primeFactors_card_log_le hm
        _ ≤ Real.log (L ^ 3) := Real.log_le_log (by exact_mod_cast hm) hmL
        _ = 3 * ell := by
          change Real.log ((Real.exp ell) ^ 3) = 3 * ell
          rw [Real.log_pow, Real.log_exp]; norm_num
        _ ≤ t * Real.log 2 := by
          linarith [mul_le_mul_of_nonneg_left hlogtwo ht0.le,
            mul_le_mul_of_nonneg_right hδ1 ht0.le]
    have hbound := sum_primeFactors_rpow_le (m := m) (T := t) (s := s) ht1 (by linarith) hs1 hmc
    rw [hu] at hbound
    have hexp : (1 - s) * u = (1 - δ) * v := by
      change (1 - (1 - (1 - δ) * (v / u))) * u = (1 - δ) * v
      field_simp
      ring
    rw [hexp] at hbound
    have h4 : 4 * ∑ p ∈ m.primeFactors, (p : ℝ) ^ (-s) ≤
        u + Real.log v - v + Real.log δ := by
      refine le_trans ?_ hE
      linarith
    calc
      Real.exp (4 * ∑ p ∈ m.primeFactors, (p : ℝ) ^ (-s)) ≤
          Real.exp (u + Real.log v - v + Real.log δ) := Real.exp_le_exp.mpr h4
      _ = δ * W := by
        have e1 : Real.exp u = t := by rw [← hu, Real.exp_log ht0]
        have e2 : Real.exp v = u := by rw [← hv, Real.exp_log hu0]
        rw [Real.exp_add, Real.exp_sub, Real.exp_add, Real.exp_log hv0, Real.exp_log hδ, e1, e2,
          hWdef]
        ring
  have hfb := finite_bound_sharp (x := x) (a := a) (L := L) (s := s) (K := K) hx.le ha hL hs1 hK0 hD
  -- rewrite every term as x times an exponential
  have hP : ∀ y : ℝ, Real.exp (t + y) = x * Real.exp y := by
    intro y
    rw [Real.exp_add, ← hxe]
  let Q := Real.exp (-(1 - 4 * δ) * W)
  have hQ0 : 0 < Q := Real.exp_pos _
  have hT0 : a ≤ x * Q := by
    change Real.exp ((1 - δ) * t) ≤ x * Real.exp (-(1 - 4 * δ) * W)
    rw [← hP]
    apply Real.exp_le_exp.mpr
    linarith [mul_nonneg hδ.le hW0.le, mul_nonneg hδ.le ht0.le]
  have hT1 : 2 * x / L ≤ 2 * (x * Q) := by
    have : 2 * x / L = 2 * (x * Real.exp (-ell)) := by
      change 2 * x / Real.exp ell = _
      rw [Real.exp_neg]
      field_simp
    rw [this]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply mul_le_mul_of_nonneg_left _ hx0.le
    apply Real.exp_le_exp.mpr
    change -((1 - δ) * W) ≤ -(1 - 4 * δ) * W
    linarith [mul_nonneg hδ.le hW0.le]
  have hT2 : a * L ≤ x * Q := by
    change Real.exp ((1 - δ) * t) * Real.exp ell ≤ x * Real.exp (-(1 - 4 * δ) * W)
    rw [← Real.exp_add, ← hP]
    apply Real.exp_le_exp.mpr
    change (1 - δ) * t + (1 - δ) * W ≤ t + -(1 - 4 * δ) * W
    linarith [mul_nonneg hδ.le hW0.le, mul_nonneg hδ.le ht0.le]
  have hT3 : x / L ^ 2 ≤ x * Q := by
    have : x / L ^ 2 = x * Real.exp (-(2 * ell)) := by
      change x / (Real.exp ell) ^ 2 = _
      rw [Real.exp_neg, ← Real.exp_nat_mul]
      push_cast
      field_simp
    rw [this]
    apply mul_le_mul_of_nonneg_left _ hx0.le
    apply Real.exp_le_exp.mpr
    change -(2 * ((1 - δ) * W)) ≤ -(1 - 4 * δ) * W
    linarith [mul_nonneg hδ.le hW0.le]
  have hquad : 1 + 3 * W ≤ Real.exp (δ * W) := by
    have h := Real.quadratic_le_exp_of_nonneg (show 0 ≤ δ * W by positivity)
    have h3 : 3 * W ≤ δ * W + (δ * W) ^ 2 / 2 := by
      have : (δ * W) ^ 2 / 2 = (δ ^ 2 * W) * W / 2 := by ring
      rw [this]
      linarith [mul_le_mul_of_nonneg_right hW6 hW0.le, mul_pos hδ hW0]
    linarith
  have hT4 : a ^ (s - 1) * K * (1 + 3 * Real.log L) ≤ Q := by
    have ha_pow : a ^ (s - 1) = Real.exp (-((1 - δ) ^ 2 * W)) := by
      change (Real.exp ((1 - δ) * t)) ^ (1 - (1 - δ) * (v / u) - 1) = _
      rw [← Real.exp_mul]
      congr 1
      rw [hWdef]
      field_simp
      ring
    have hlogL : Real.log L = ell := Real.log_exp ell
    rw [ha_pow, hlogL]
    have h13 : 1 + 3 * ell ≤ Real.exp (δ * W) := by
      refine le_trans ?_ hquad
      linarith
    calc
      Real.exp (-((1 - δ) ^ 2 * W)) * K * (1 + 3 * ell) ≤
          Real.exp (-((1 - δ) ^ 2 * W)) * K * Real.exp (δ * W) :=
        mul_le_mul_of_nonneg_left h13 (by positivity)
      _ = Real.exp (-((1 - δ) ^ 2 * W) + δ * W + δ * W) := by
        change Real.exp (-((1 - δ) ^ 2 * W)) * Real.exp (δ * W) * Real.exp (δ * W) = _
        rw [← Real.exp_add, ← Real.exp_add]
      _ ≤ Q := by
        apply Real.exp_le_exp.mpr
        linarith [mul_nonneg (sq_nonneg δ) hW0.le]
  have h6 : 6 ≤ Real.exp (δ * W) := by
    have h := Real.add_one_le_exp (δ * W)
    have h5 : 30 ≤ δ * W := by
      linarith [mul_le_mul_of_nonneg_right hδ1 (mul_pos hδ hW0).le]
    linarith
  have hfinal : 6 * (x * Q) ≤ x * Real.exp (-(1 - 5 * δ) * W) := by
    have : x * Real.exp (-(1 - 5 * δ) * W) = Real.exp (δ * W) * (x * Q) := by
      change _ = Real.exp (δ * W) * (x * Real.exp (-(1 - 4 * δ) * W))
      rw [mul_left_comm, ← Real.exp_add]
      congr 2
      ring
    rw [this]
    exact mul_le_mul_of_nonneg_right h6 (by positivity)
  have hT4' : x * (a ^ (s - 1) * K * (1 + 3 * Real.log L)) ≤ x * Q :=
    mul_le_mul_of_nonneg_left hT4 hx0.le
  linarith

end CarmichaelCount

open Filter Real

/-- The sharp upper bound of Pomerance, Selfridge and Wagstaff for the number of Carmichael
numbers: C(x) is at most x / L(x)^(1 - eps) for every eps > 0 and every large x. -/
theorem OMA.solution : OMA.R_Erdos1057_erdos_1057_variants_pomerance_R1.H1 := by
  intro ε hε
  have hδ : 0 < min ε 1 / 5 := by positivity
  have hδ1 : min ε 1 / 5 ≤ 1 / 5 := by
    have := min_le_right ε 1
    linarith
  have hδε : 5 * (min ε 1 / 5) ≤ ε := by
    have := min_le_left ε 1
    linarith
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually (CarmichaelCount.params hδ)] with x hx h
  obtain ⟨ht1, hu1, hv1, hvu, hW, hE⟩ := h
  have hb := CarmichaelCount.final_bound hδ hδ1 hx rfl rfl rfl ht1 hu1 hv1 hvu hW hE
  refine hb.trans ?_
  have hx0 : 0 < x := by linarith
  have hW0 : 0 ≤ Real.log x * Real.log (Real.log (Real.log x)) / Real.log (Real.log x) := by
    have : (0 : ℝ) < Real.log x := by linarith
    positivity
  apply mul_le_mul_of_nonneg_left _ hx0.le
  apply Real.exp_le_exp.mpr
  linarith [mul_nonneg (sub_nonneg.mpr hδε) hW0]
