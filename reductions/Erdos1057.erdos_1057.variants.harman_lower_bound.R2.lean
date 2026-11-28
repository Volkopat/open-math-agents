import FormalConjectures.ErdosProblems.«1057»
import Mathlib

-- Reduction Erdos1057.erdos_1057.variants.harman_lower_bound.R2 of Erdős Problem 1057 — harman lower bound
-- Credit: @mijuny
-- Builds on the AGP formalization patterns of @Dugongue (CRT + Davenport setup),
-- @ZedingZhang (Korselt sufficiency and Proposition 1.2 subset counting), and
-- @PanPapag (dyadic exponent interpolation).
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Harman's lower bound for Carmichael numbers via finite-group zero-sum and dyadic reservoirs

This reduction formalizes the complete algebraic, combinatorial, and dyadic-interpolation
architecture of the Alford–Granville–Pomerance / Harman / Lichtman construction inside `main`,
isolating two clean, orthogonal hypotheses:

* `H1` (combinatorial group theory, van Emde Boas–Kruyswijk 1969 / Meshulam 1990): in any finite
  commutative group `G` of exponent `e`, a sequence of length at least `e * (1 + log (|G| / e))`
  has a nonempty subsequence of product `1`.
* `H2` (analytic prime reservoir at dyadic scales `2 ^ m`, Harman 2008 / Lichtman 2022): for all
  sufficiently large `m`, there exist coprime `k, L > 0`, bound `b > 0`, threshold `n`, target
  subset size `t` (`n + 2 ≤ t ≤ |P|`, `b ^ t ≤ 2 ^ m`), and a reservoir `P` of primes `p ≤ b`
  not dividing `k * L` with `k ∣ p - 1 ∣ k * L`, such that `n + 1` exceeds the Davenport threshold
  of `(ZMod L)ˣ` and `2 ^ (0.3389 * m) * C(|P|, n) ≤ C(|P|, t)`.
-/

namespace OMA.R_Erdos1057_erdos_1057_variants_harman_lower_bound_R2

open Finset Filter Real
open scoped Classical Topology

/-- The van Emde Boas–Kruyswijk–Meshulam product-one bound in finite commutative groups. -/
def H1 : Prop :=
  ∀ (G : Type) [CommGroup G] [Finite G] (T : Finset ℕ) (g : ℕ → G),
    (Monoid.exponent G : ℝ) * (1 + Real.log ((Nat.card G : ℝ) / (Monoid.exponent G : ℝ)))
      ≤ (T.card : ℝ) →
    ∃ I ⊆ T, I.Nonempty ∧ ∏ i ∈ I, g i = 1

/-- Quantitative smooth-shifted-prime reservoir at dyadic scales `2 ^ m`. -/
def H2 : Prop :=
  ∀ᶠ m : ℕ in atTop, ∃ (k L b n t : ℕ) (P : Finset ℕ),
    0 < L ∧ 0 < b ∧ Nat.Coprime k L ∧
    n + 2 ≤ t ∧ t ≤ P.card ∧ ((b ^ t : ℕ) : ℝ) ≤ (2 : ℝ) ^ m ∧
    (∀ p ∈ P, p.Prime ∧ p ≤ b ∧ ¬ p ∣ k * L ∧ k ∣ p - 1 ∧ p - 1 ∣ k * L) ∧
    (Monoid.exponent (ZMod L)ˣ : ℝ) *
      (1 + Real.log ((Nat.card (ZMod L)ˣ : ℝ) / (Monoid.exponent (ZMod L)ˣ : ℝ))) ≤ (n + 1 : ℝ) ∧
    (2 : ℝ) ^ ((m : ℝ) * 0.3389) * (P.card.choose n : ℝ) ≤ (P.card.choose t : ℝ)

lemma support_mem {I : Finset ℕ} (prime : ∀ q ∈ I, q.Prime) {p : ℕ}
    (hp : p.Prime) (dvd : p ∣ ∏ q ∈ I, q) : p ∈ I := by
  obtain ⟨q, hq, pq⟩ := (Prime.dvd_finsetProd_iff hp.prime (fun q => q)).mp dvd
  rwa [(Nat.prime_dvd_prime_iff_eq hp (prime q hq)).mp pq]

lemma products_injective {S T : Finset ℕ}
    (hs : ∀ p ∈ S, p.Prime) (ht : ∀ p ∈ T, p.Prime)
    (same : (∏ p ∈ S, p) = ∏ p ∈ T, p) : S = T := by
  ext p
  constructor
  · intro hp
    exact support_mem ht (hs p hp) (same ▸ Finset.dvd_prod_of_mem (fun q => q) hp)
  · intro hp
    exact support_mem hs (ht p hp) (same.symm ▸ Finset.dvd_prod_of_mem (fun q => q) hp)

lemma product_carmichael {S : Finset ℕ} {M : ℕ} (two : 1 < S.card)
    (prime : ∀ p ∈ S, p.Prime) (divides : ∀ p ∈ S, p - 1 ∣ M)
    (oneMod : (∏ p ∈ S, p) ≡ 1 [MOD M]) : IsCarmichael (∏ p ∈ S, p) := by
  let N := ∏ p ∈ S, p
  have pos : 0 < N := Finset.prod_pos (fun p hp => (prime p hp).pos)
  obtain ⟨p, hp, q, hq, ne⟩ := Finset.one_lt_card.mp two
  have dp : p ∣ N := Finset.dvd_prod_of_mem _ hp
  have dq : q ∣ N := Finset.dvd_prod_of_mem _ hq
  have big : 1 < N := (prime p hp).one_lt.trans_le (Nat.le_of_dvd pos dp)
  have composite : ¬ N.Prime := by
    intro hn
    exact ne (((Nat.prime_dvd_prime_iff_eq (prime p hp) hn).mp dp).trans
      ((Nat.prime_dvd_prime_iff_eq (prime q hq) hn).mp dq).symm)
  have modDvd : M ∣ N - 1 := (Nat.modEq_iff_dvd' (show 1 ≤ N by omega)).mp oneMod.symm
  intro b hb cop
  refine ⟨?_, composite, big⟩
  unfold Nat.ProbablePrime
  apply Finset.prod_primes_dvd _ (fun r hr => (prime r hr).prime)
  intro r hr
  haveI : Fact r.Prime := ⟨prime r hr⟩
  have dr : r ∣ N := Finset.dvd_prod_of_mem _ hr
  have nz : (b : ZMod r) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro h
    exact (prime r hr).not_dvd_one (cop.gcd_eq_one ▸ Nat.dvd_gcd dr h)
  obtain ⟨j, hj⟩ := (divides r hr).trans modDvd
  change r ∣ b ^ (N - 1) - 1
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.one_le_pow _ _ hb), Nat.cast_pow,
    hj, pow_mul, ZMod.pow_card_sub_one_eq_one nz, one_pow, Nat.cast_one, sub_self]

lemma decompose_subset {A P : Finset ℕ} {M n t : ℕ} (sub : A ⊆ P)
    (size : A.card = t) (hnt : n ≤ t)
    (extract : ∀ S ⊆ P, n < S.card → ∃ I ⊆ S, I.Nonempty ∧ (∏ p ∈ I, p) ≡ 1 [MOD M]) :
    ∃ I D : Finset ℕ, I ⊆ P ∧ t - n ≤ I.card ∧ I.card ≤ t ∧
      (∏ p ∈ I, p) ≡ 1 [MOD M] ∧ D ⊆ P ∧ D.card = n ∧ I ∪ D = A := by
  classical
  let F := A.powerset.filter (fun I => (∏ p ∈ I, p) ≡ 1 [MOD M])
  have empty : ∅ ∈ F := by
    refine mem_filter.mpr ⟨mem_powerset.mpr (empty_subset A), ?_⟩
    simpa only [prod_empty] using (show 1 ≡ 1 [MOD M] from rfl)
  obtain ⟨I, hi, hmax⟩ := exists_max_image F card ⟨∅, empty⟩
  obtain ⟨subA, one⟩ := mem_filter.mp hi
  have ia := mem_powerset.mp subA
  have small : (A \ I).card ≤ n := by
    by_contra! large
    obtain ⟨J, hj, hjpos, oneJ⟩ := extract (A \ I) (sdiff_subset.trans sub) large
    have dis : Disjoint I J := disjoint_left.mpr (fun x hx hxj =>
      (mem_sdiff.mp (hj hxj)).2 hx)
    have together : I ∪ J ∈ F := by
      refine mem_filter.mpr ⟨mem_powerset.mpr
        (union_subset ia (hj.trans sdiff_subset)), ?_⟩
      rw [prod_union dis]
      simpa only [one_mul] using one.mul oneJ
    have bigger := hmax (I ∪ J) together
    rw [card_union_of_disjoint dis] at bigger
    have nonzero := card_pos.mpr hjpos
    omega
  obtain ⟨D, rest, da, dsize⟩ := exists_subsuperset_card_eq
    (show A \ I ⊆ A from sdiff_subset) small (by omega)
  have ilo := card_sdiff_of_subset ia
  have ihi := card_le_card ia
  refine ⟨I, D, ia.trans sub, by omega, by omega, one, da.trans sub, dsize, ?_⟩
  apply Subset.antisymm (union_subset ia da)
  intro a ha
  by_cases h : a ∈ I
  · exact mem_union.mpr (Or.inl h)
  · exact mem_union.mpr (Or.inr (rest (mem_sdiff.mpr ⟨ha, h⟩)))

lemma subset_count (P : Finset ℕ) (M n t : ℕ) (hnt : n ≤ t)
    (extract : ∀ S ⊆ P, n < S.card → ∃ I ⊆ S, I.Nonempty ∧ (∏ p ∈ I, p) ≡ 1 [MOD M]) :
    P.card.choose t ≤
      (P.powerset.filter (fun I => t - n ≤ I.card ∧ I.card ≤ t ∧
        (∏ p ∈ I, p) ≡ 1 [MOD M])).card * P.card.choose n := by
  classical
  let G := P.powerset.filter (fun I => t - n ≤ I.card ∧ I.card ≤ t ∧
    (∏ p ∈ I, p) ≡ 1 [MOD M])
  let pairs := G ×ˢ P.powersetCard n
  let join (z : Finset ℕ × Finset ℕ) := z.1 ∪ z.2
  have cover : P.powersetCard t ⊆ pairs.image join := by
    intro A ha
    obtain ⟨sub, size⟩ := mem_powersetCard.mp ha
    obtain ⟨I, D, ip, lo, hi, one, dp, dsize, un⟩ := decompose_subset sub size hnt extract
    refine mem_image.mpr ⟨(I, D), mem_product.mpr ⟨?_, ?_⟩, un⟩
    · exact mem_filter.mpr ⟨mem_powerset.mpr ip, lo, hi, one⟩
    · exact mem_powersetCard.mpr ⟨dp, dsize⟩
  have bound := (card_le_card cover).trans (card_image_le (s := pairs) (f := join))
  simpa only [pairs, card_product, card_powersetCard, G] using bound

lemma extract_mod_mul (h1 : H1) {k L n : ℕ} (hL : 0 < L) (hkL : Nat.Coprime k L)
    {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime ∧ p ≤ b ∧ ¬ p ∣ k * L ∧ k ∣ p - 1 ∧ p - 1 ∣ k * L)
    (hdav : (Monoid.exponent (ZMod L)ˣ : ℝ) *
      (1 + Real.log ((Nat.card (ZMod L)ˣ : ℝ) / (Monoid.exponent (ZMod L)ˣ : ℝ))) ≤ (n + 1 : ℝ)) :
    ∀ S ⊆ P, n < S.card → ∃ I ⊆ S, I.Nonempty ∧ (∏ p ∈ I, p) ≡ 1 [MOD k * L] := by
  classical
  haveI : NeZero L := ⟨by omega⟩
  intro S hSP hScard
  have hcop : ∀ p ∈ S, Nat.Coprime p L := by
    intro p hp
    obtain ⟨hpp, -, hndvd, -⟩ := hP p (hSP hp)
    exact Nat.Coprime.coprime_dvd_right (Dvd.intro_left k rfl)
      ((Nat.Prime.coprime_iff_not_dvd hpp).2 hndvd)
  let g : ℕ → (ZMod L)ˣ := fun p =>
    if h : Nat.Coprime p L then ZMod.unitOfCoprime p h else 1
  have hcard : (Monoid.exponent (ZMod L)ˣ : ℝ) *
      (1 + Real.log ((Nat.card (ZMod L)ˣ : ℝ) / (Monoid.exponent (ZMod L)ˣ : ℝ))) ≤ (S.card : ℝ) :=
    hdav.trans (by exact_mod_cast (show n + 1 ≤ S.card by omega))
  obtain ⟨I, hIS, hIne, hprod⟩ := h1 (ZMod L)ˣ S g hcard
  have hnL : (∏ q ∈ I, q) ≡ 1 [MOD L] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    have hunit : ((∏ q ∈ I, g q : (ZMod L)ˣ) : ZMod L) = 1 := by rw [hprod]; rfl
    rw [Units.coe_prod] at hunit
    rw [Nat.cast_prod, Nat.cast_one, ← hunit]
    refine Finset.prod_congr rfl fun q hq => ?_
    simp only [g, dif_pos (hcop q (hIS hq)), ZMod.coe_unitOfCoprime]
  have hnk : (∏ q ∈ I, q) ≡ 1 [MOD k] := by
    rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_prod, Nat.cast_one]
    refine Finset.prod_eq_one fun q hq => ?_
    obtain ⟨hqp, -, -, hkq, -⟩ := hP q (hSP (hIS hq))
    have h1q : 1 ≤ q := hqp.one_lt.le
    have hz : ((q - 1 : ℕ) : ZMod k) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hkq
    rw [Nat.cast_sub h1q, Nat.cast_one, sub_eq_zero] at hz
    exact hz
  exact ⟨I, hIS, hIne, (Nat.modEq_and_modEq_iff_modEq_mul hkL).1 ⟨hnk, hnL⟩⟩

lemma carmichaelCounting_mono : Monotone Erdos1057.carmichaelCounting := by
  intro x y hxy
  unfold Erdos1057.carmichaelCounting
  have hsub : {n : ℕ | IsCarmichael n ∧ (n : ℝ) ≤ x} ⊆
      {n : ℕ | IsCarmichael n ∧ (n : ℝ) ≤ y} :=
    fun n hn => ⟨hn.1, hn.2.trans hxy⟩
  have hfin : {n : ℕ | IsCarmichael n ∧ (n : ℝ) ≤ y}.Finite :=
    (Set.finite_Iic ⌊y⌋₊).subset (fun n hn => Nat.le_floor hn.2)
  exact_mod_cast Set.ncard_le_ncard hsub hfin

lemma harman_of_dyadic {C : ℝ → ℝ} (mono : Monotone C)
    (h : ∀ᶠ m : ℕ in atTop, (2 : ℝ) ^ ((m : ℝ) * 0.3389) ≤ C ((2 : ℝ) ^ m)) :
    ∀ᶠ x : ℝ in atTop, x ^ (0.33336704 : ℝ) < C x := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 h
  let K := max N 100
  filter_upwards [eventually_ge_atTop ((2 : ℝ) ^ K)] with x hx
  obtain ⟨m, hlo, hhi⟩ := exists_nat_pow_near
    ((one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)).trans hx) (by norm_num : (1 : ℝ) < 2)
  have hK : K ≤ m := by
    by_contra! hlt
    exact (not_lt_of_ge hx) (hhi.trans_le (pow_le_pow_right₀ (by norm_num) hlt))
  have hm : (100 : ℝ) ≤ m := by exact_mod_cast (le_max_right N 100).trans hK
  calc
    x ^ (0.33336704 : ℝ) < ((2 : ℝ) ^ (m + 1)) ^ (0.33336704 : ℝ) :=
      Real.rpow_lt_rpow ((by positivity : 0 ≤ (2 : ℝ) ^ K).trans hx) hhi (by norm_num)
    _ = (2 : ℝ) ^ (((m : ℝ) + 1) * 0.33336704) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      push_cast
      rfl
    _ ≤ (2 : ℝ) ^ ((m : ℝ) * 0.3389) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ ≤ C ((2 : ℝ) ^ m) := hN m ((le_max_left N 100).trans hK)
    _ ≤ C x := mono hlo

lemma dyadic_bound (h1 : H1) (h2 : H2) :
    ∀ᶠ m : ℕ in atTop, (2 : ℝ) ^ ((m : ℝ) * 0.3389) ≤ Erdos1057.carmichaelCounting ((2 : ℝ) ^ m) := by
  classical
  filter_upwards [h2] with m hm
  obtain ⟨k, L, b, n, t, P, hL, hb, hkL, hnt, htP, cap, hP, hdav, ratio⟩ := hm
  let M := k * L
  have reserve := extract_mod_mul h1 hL hkL hP hdav
  let G := P.powerset.filter (fun I => t - n ≤ I.card ∧ I.card ≤ t ∧
    (∏ p ∈ I, p) ≡ 1 [MOD M])
  let val (I : Finset ℕ) := ∏ p ∈ I, p
  have info {I : Finset ℕ} (hi : I ∈ G) :
      I ⊆ P ∧ t - n ≤ I.card ∧ I.card ≤ t ∧ val I ≡ 1 [MOD M] := by
    obtain ⟨sub, h⟩ := Finset.mem_filter.mp hi
    exact ⟨Finset.mem_powerset.mp sub, h⟩
  have inj : Set.InjOn val (↑G : Set (Finset ℕ)) := by
    intro I hi J hj eqn
    exact products_injective (fun p hp => (hP p ((info hi).1 hp)).1)
      (fun p hp => (hP p ((info hj).1 hp)).1) eqn
  have inRange : (↑(G.image val) : Set ℕ) ⊆ {q : ℕ | IsCarmichael q ∧ (q : ℝ) ≤ (2 : ℝ) ^ m} := by
    intro q hq
    obtain ⟨I, hi, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨sub, lo, high, one⟩ := info hi
    refine ⟨product_carmichael (by omega) (fun p hp => (hP p (sub hp)).1)
      (fun p hp => (hP p (sub hp)).2.2.2.2) one, ?_⟩
    have lim : val I ≤ b ^ t := calc
      val I ≤ ∏ _p ∈ I, b := Finset.prod_le_prod' (fun p hp => (hP p (sub hp)).2.1)
      _ = b ^ I.card := by simp
      _ ≤ b ^ t := Nat.pow_le_pow_right hb high
    exact (show (val I : ℝ) ≤ (b ^ t : ℕ) by exact_mod_cast lim).trans cap
  have fin : {q : ℕ | IsCarmichael q ∧ (q : ℝ) ≤ (2 : ℝ) ^ m}.Finite :=
    (Set.finite_Iic ⌊(2 : ℝ) ^ m⌋₊).subset (fun q hq => Nat.le_floor hq.2)
  have cardBound := Set.ncard_le_ncard inRange fin
  rw [Set.ncard_coe_finset, Finset.card_image_of_injOn inj] at cardBound
  have comb : P.card.choose t ≤ G.card * P.card.choose n :=
    subset_count P M n t (by omega) reserve
  have cpos : (0 : ℝ) < (P.card.choose n : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega : n ≤ P.card)
  have hle : (2 : ℝ) ^ ((m : ℝ) * 0.3389) * (P.card.choose n : ℝ) ≤
      (G.card : ℝ) * (P.card.choose n : ℝ) :=
    ratio.trans (by exact_mod_cast comb)
  have many : (2 : ℝ) ^ ((m : ℝ) * 0.3389) ≤ (G.card : ℝ) :=
    le_of_mul_le_mul_right hle cpos
  exact many.trans (by unfold Erdos1057.carmichaelCounting; exact_mod_cast cardBound)

theorem main : H1 → H2 → type_of% @Erdos1057.erdos_1057.variants.harman_lower_bound := by
  intro h1 h2
  exact harman_of_dyadic carmichaelCounting_mono (dyadic_bound h1 h2)

end OMA.R_Erdos1057_erdos_1057_variants_harman_lower_bound_R2
