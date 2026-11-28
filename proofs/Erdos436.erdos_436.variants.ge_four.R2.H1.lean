import OMAReductions.R_Erdos436_erdos_436_variants_ge_four_R2
import Mathlib

/-!
# Proof of `Erdos436.erdos_436.variants.ge_four.R2.H1`

For an odd prime `q` and natural `M`, let `K` be the splitting field over `ℚ` of
`(X^q - 1) ∏_{r odd prime ≤ M} (X^q - r)` and `L` be the splitting field of
`(X^q - 1) (X^q - 2) ∏_{r odd prime ≤ M} (X^q - r)`.
Using Galois inertia groups we prove that `2` is unramified in `K` (hence `[K : ℚ] < [L : ℚ]`)
and only finitely many primes ramify in `K` and `L`. Using Mathlib's Dirichlet class number
formula for `NumberField.dedekindZeta` and the real Euler product, we show that infinitely
many primes `p` split completely in `K` but not in `L`; every sufficiently large such prime
makes all odd primes `r ≤ M` `q`-th power residues while `2` is a `q`-th power nonresidue.
-/

open scoped BigOperators nonZeroDivisors
open Filter Topology Polynomial Ideal NumberField

namespace Erdos436H1

noncomputable section

/- Section 1: Elementary real log inequality and fiberwise tsum for nonnegative reals -/

private lemma log_one_sub_bounds {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    x ≤ -Real.log (1 - x) ∧ -Real.log (1 - x) ≤ x + x ^ 2 := by
  have h1x : 0 < 1 - x := by linarith
  constructor
  · have h := Real.log_le_sub_one_of_pos h1x
    linarith
  · let f : ℝ → ℝ := fun t => Real.log (1 - t) + t + t ^ 2
    have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) x,
        HasDerivAt f (-(1 - t)⁻¹ + 1 + 2 * t) t := by
      intro t ht
      have hpos : 0 < 1 - t := by linarith [ht.2, hx1]
      have h1 : HasDerivAt (fun u : ℝ => 1 - u) (-1) t := by
        simpa using (hasDerivAt_const t (1 : ℝ)).fun_sub (hasDerivAt_id t)
      have hlog : HasDerivAt (fun u : ℝ => Real.log (1 - u)) (-1 / (1 - t)) t :=
        h1.log hpos.ne'
      have hpow : HasDerivAt (fun u : ℝ => u ^ 2) (2 * t) t := by
        simpa using hasDerivAt_pow 2 t
      have hsum : HasDerivAt f (-1 / (1 - t) + 1 + 2 * t) t :=
        (hlog.fun_add (hasDerivAt_id t)).fun_add hpow
      convert hsum using 1
      field_simp [hpos.ne']
    have hmono : MonotoneOn f (Set.Icc 0 x) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc 0 x)
      · exact fun t ht => (hderiv t ht).continuousAt.continuousWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        exact (hderiv t (Set.Ioo_subset_Icc_self ht)).differentiableAt.differentiableWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        rw [(hderiv t (Set.Ioo_subset_Icc_self ht)).deriv]
        have hpos : 0 < 1 - t := by linarith [ht.2, hx1]
        have ht0 : 0 ≤ t := ht.1.le
        have ht1 : t ≤ 1 / 2 := le_trans ht.2.le hx1
        have hnum : 0 ≤ t * (1 - 2 * t) := mul_nonneg ht0 (by linarith)
        have heq : -(1 - t)⁻¹ + 1 + 2 * t = t * (1 - 2 * t) / (1 - t) := by
          field_simp [hpos.ne']
          ring
        rw [heq]
        exact div_nonneg hnum hpos.le
    have h0x : f 0 ≤ f x := hmono ⟨le_rfl, hx0⟩ ⟨hx0, le_rfl⟩ hx0
    simp only [f, sub_zero, Real.log_one, add_zero, zero_pow (by norm_num : 2 ≠ 0)] at h0x
    linarith

private lemma tsum_fiberwise_nonneg {β γ : Type*} {f : β → ℝ} (hf : Summable f)
    (hnn : ∀ b, 0 ≤ f b) (g : β → γ) :
    ∑' c : γ, ∑' b : {b : β // g b = c}, f b.1 = ∑' b : β, f b := by
  have hfib_sum : ∀ c : γ, Summable (fun b : {b : β // g b = c} => f b.1) :=
    fun c => hf.subtype _
  have hfib_nn : ∀ c : γ, 0 ≤ ∑' b : {b : β // g b = c}, f b.1 :=
    fun c => tsum_nonneg (fun b => hnn b.1)
  have h1 : ENNReal.ofReal (∑' b : β, f b) =
      ∑' c : γ, ENNReal.ofReal (∑' b : {b : β // g b = c}, f b.1) := by
    rw [ENNReal.ofReal_tsum_of_nonneg hnn hf, ← ENNReal.tsum_fiberwise (fun b => ENNReal.ofReal (f b)) g]
    refine tsum_congr (fun c => ?_)
    exact (ENNReal.ofReal_tsum_of_nonneg (fun b : {x : β // g x = c} => hnn b.1) (hfib_sum c)).symm
  have hne_top : (∑' c : γ, ENNReal.ofReal (∑' b : {b : β // g b = c}, f b.1)) ≠ ⊤ := by
    rw [← h1]
    exact ENNReal.ofReal_ne_top
  have htoReal : (∑' c : γ, ENNReal.ofReal (∑' b : {b : β // g b = c}, f b.1)).toReal =
      ∑' c : γ, ∑' b : {b : β // g b = c}, f b.1 := by
    rw [ENNReal.tsum_toReal_eq (fun c => ENNReal.ofReal_ne_top)]
    exact tsum_congr (fun c => ENNReal.toReal_ofReal (hfib_nn c))
  rw [← htoReal, ← h1, ENNReal.toReal_ofReal (tsum_nonneg hnn)]

private lemma natCard_le_of_inj {α β : Type*} [Finite β] {f : α → β} (hf : Function.Injective f) :
    Nat.card α ≤ Nat.card β := by
  have : Finite α := Finite.of_injective f hf
  classical
  let _ := Fintype.ofFinite α
  let _ := Fintype.ofFinite β
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact Fintype.card_le_of_injective f hf

/- Section 2: Real Dedekind zeta function and Euler product for a Galois number field -/

private def realDedekindZeta (F : Type*) [Field F] [NumberField F] (s : ℝ) : ℝ :=
  ∑' I : (Ideal (𝓞 F))⁰, ((Ideal.absNorm (I : Ideal (𝓞 F)) : ℝ) ^ s)⁻¹

private lemma exists_card_absNorm_le_bound (F : Type*) [Field F] [NumberField F] :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      (Nat.card {I : (Ideal (𝓞 F))⁰ // Ideal.absNorm (I : Ideal (𝓞 F)) ≤ n} : ℝ) ≤ C * n := by
  have ht := NumberField.Ideal.tendsto_norm_le_div_atTop₀ F
  set L := (2 ^ NumberField.InfinitePlace.nrRealPlaces F *
    (2 * Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces F *
    NumberField.Units.regulator F * NumberField.classNumber F) /
    (NumberField.Units.torsionOrder F * Real.sqrt |NumberField.discr F|)
  have hev : ∀ᶠ s : ℝ in atTop,
      (Nat.card {I : (Ideal (𝓞 F))⁰ // (Ideal.absNorm (I : Ideal (𝓞 F)) : ℝ) ≤ s} : ℝ) / s ≤
        L + 1 :=
    ((tendsto_order.mp ht).2 (L + 1) (by linarith)).mono fun _ h => h.le
  rw [Filter.eventually_atTop] at hev
  obtain ⟨M₀, hM₀⟩ := hev
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge (max M₀ 1)
  let C : ℝ := max (max (L + 1) 1)
    (Nat.card {I : (Ideal (𝓞 F))⁰ // Ideal.absNorm (I : Ideal (𝓞 F)) ≤ N₀} : ℝ)
  refine ⟨C, lt_of_lt_of_le (by positivity : (0 : ℝ) < 1)
    (le_trans (le_max_right _ _) (le_max_left _ _)), fun n => ?_⟩
  rcases eq_or_ne n 0 with rfl | hn0
  · have : IsEmpty {I : (Ideal (𝓞 F))⁰ // Ideal.absNorm (I : Ideal (𝓞 F)) = 0} :=
      ⟨fun ⟨I, hI⟩ => Ideal.absNorm_ne_zero_of_nonZeroDivisors I hI⟩
    simp
  · by_cases hle : n ≤ N₀
    · have : Finite {I : (Ideal (𝓞 F))⁰ // Ideal.absNorm (I : Ideal (𝓞 F)) ≤ N₀} :=
        Ideal.finite_setOfPred_absNorm_le₀ N₀
      have hcard_le :
          Nat.card {I : (Ideal (𝓞 F))⁰ // Ideal.absNorm (I : Ideal (𝓞 F)) ≤ n} ≤
          Nat.card {I : (Ideal (𝓞 F))⁰ // Ideal.absNorm (I : Ideal (𝓞 F)) ≤ N₀} := by
        apply natCard_le_of_inj (f := fun x : {I : (Ideal (𝓞 F))⁰ // Ideal.absNorm (I : Ideal (𝓞 F)) ≤ n} =>
          (⟨x.1, le_trans x.2 hle⟩ : {I : (Ideal (𝓞 F))⁰ // Ideal.absNorm (I : Ideal (𝓞 F)) ≤ N₀}))
        intro x y hxy
        exact Subtype.ext (Subtype.mk.inj hxy)
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn0)
      have hC0 : 0 ≤ C := le_trans (by norm_num) (le_trans (le_max_right _ _) (le_max_left _ _))
      calc (Nat.card {I : (Ideal (𝓞 F))⁰ // Ideal.absNorm (I : Ideal (𝓞 F)) ≤ n} : ℝ)
          ≤ (Nat.card {I : (Ideal (𝓞 F))⁰ // Ideal.absNorm (I : Ideal (𝓞 F)) ≤ N₀} : ℝ) := by
            exact_mod_cast hcard_le
        _ ≤ C := le_max_right _ _
        _ = C * 1 := (mul_one C).symm
        _ ≤ C * n := mul_le_mul_of_nonneg_left hn1 hC0
    · push Not at hle
      have hn_ge : M₀ ≤ (n : ℝ) := le_trans (le_max_left _ _) (le_trans hN₀ (by exact_mod_cast hle.le))
      have hbd := hM₀ (n : ℝ) hn_ge
      have hn_pos : (0 : ℝ) < n := by exact_mod_cast (Nat.pos_of_ne_zero hn0)
      rw [div_le_iff₀ hn_pos] at hbd
      have hcast :
          Nat.card {I : (Ideal (𝓞 F))⁰ // Ideal.absNorm (I : Ideal (𝓞 F)) ≤ n} =
          Nat.card {I : (Ideal (𝓞 F))⁰ // (Ideal.absNorm (I : Ideal (𝓞 F)) : ℝ) ≤ (n : ℝ)} :=
        Nat.card_congr (Equiv.subtypeEquivRight fun _ => by exact_mod_cast Iff.rfl)
      rw [hcast]
      exact hbd.trans (mul_le_mul_of_nonneg_right
        (le_trans (le_max_left _ _) (le_max_left _ _)) hn_pos.le)

private lemma summable_realDedekindZeta (F : Type*) [Field F] [NumberField F]
    {s : ℝ} (hs : 1 < s) :
    Summable (fun I : (Ideal (𝓞 F))⁰ => ((Ideal.absNorm (I : Ideal (𝓞 F)) : ℝ) ^ s)⁻¹) := by
  classical
  obtain ⟨C, hCpos, hC⟩ := exists_card_absNorm_le_bound F
  apply summable_of_sum_le (fun I => by positivity) (c := (2 * C) / (1 - (2 : ℝ) ^ (1 - s)))
  intro u
  let M := u.sup (fun I => Ideal.absNorm (I : Ideal (𝓞 F)))
  have hbound : ∑ I ∈ u, ((Ideal.absNorm (I : Ideal (𝓞 F)) : ℝ) ^ s)⁻¹ ≤
      ∑ k ∈ Finset.range (Nat.log 2 M + 1),
        (2 * C) * ((2 : ℝ) ^ (1 - s)) ^ k := by
    let blk : ℕ → Finset (Ideal (𝓞 F))⁰ := fun k =>
      u.filter (fun I => Nat.log 2 (Ideal.absNorm (I : Ideal (𝓞 F))) = k)
    have hpart : u = (Finset.range (Nat.log 2 M + 1)).biUnion blk := by
      ext I
      simp only [Finset.mem_biUnion, Finset.mem_range, blk, Finset.mem_filter]
      constructor
      · intro hI
        refine ⟨Nat.log 2 (Ideal.absNorm (I : Ideal (𝓞 F))), ?_, hI, rfl⟩
        have hle : Ideal.absNorm (I : Ideal (𝓞 F)) ≤ M :=
          Finset.le_sup (f := fun J : (Ideal (𝓞 F))⁰ => Ideal.absNorm (J : Ideal (𝓞 F))) hI
        exact Nat.lt_succ_of_le (Nat.log_mono_right hle)
      · rintro ⟨_, _, hI, _⟩; exact hI
    have hdisj : Set.PairwiseDisjoint (Finset.range (Nat.log 2 M + 1) : Set ℕ) blk := by
      intro i _ j _ hij
      change Disjoint (blk i) (blk j)
      rw [Finset.disjoint_left]
      intro I hi hj
      simp only [blk, Finset.mem_filter] at hi hj
      exact hij (hi.2.symm.trans hj.2)
    rw [hpart, Finset.sum_biUnion hdisj]
    apply Finset.sum_le_sum
    intro k _
    have hcard : ((blk k).card : ℝ) ≤ C * ((2 ^ (k + 1) : ℕ) : ℝ) := by
      have : Finite {I : (Ideal (𝓞 F))⁰ // Ideal.absNorm (I : Ideal (𝓞 F)) ≤ 2 ^ (k + 1)} :=
        Ideal.finite_setOfPred_absNorm_le₀ (2 ^ (k + 1))
      have hle_card : (blk k).card ≤
          Nat.card {I : (Ideal (𝓞 F))⁰ // Ideal.absNorm (I : Ideal (𝓞 F)) ≤ 2 ^ (k + 1)} := by
        rw [← Fintype.card_coe, ← Nat.card_eq_fintype_card]
        apply natCard_le_of_inj
          (f := fun x : ↥(blk k) =>
            (⟨x.1, by
              have hx := (Finset.mem_filter.mp x.2).2
              have hlt := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2)
                (Ideal.absNorm (x.1 : Ideal (𝓞 F)))
              rw [hx] at hlt
              exact hlt.le⟩ : {I : (Ideal (𝓞 F))⁰ // Ideal.absNorm (I : Ideal (𝓞 F)) ≤ 2 ^ (k + 1)}))
        intro x y hxy
        exact Subtype.ext (Subtype.mk.inj hxy)
      exact (Nat.cast_le.mpr hle_card).trans (hC (2 ^ (k + 1)))
    have hterm : ∀ I ∈ blk k,
        ((Ideal.absNorm (I : Ideal (𝓞 F)) : ℝ) ^ s)⁻¹ ≤ ((2 ^ k : ℝ) ^ s)⁻¹ := by
      intro I hI
      have hlog : Nat.log 2 (Ideal.absNorm (I : Ideal (𝓞 F))) = k := (Finset.mem_filter.mp hI).2
      have hpow : 2 ^ k ≤ Ideal.absNorm (I : Ideal (𝓞 F)) := by
        rw [← hlog]
        exact Nat.pow_log_le_self 2 (Ideal.absNorm_ne_zero_of_nonZeroDivisors I)
      have hpowR : (2 : ℝ) ^ k ≤ (Ideal.absNorm (I : Ideal (𝓞 F)) : ℝ) := by exact_mod_cast hpow
      apply inv_anti₀ (by positivity)
      exact Real.rpow_le_rpow (by positivity) hpowR (by linarith)
    calc ∑ I ∈ blk k, ((Ideal.absNorm (I : Ideal (𝓞 F)) : ℝ) ^ s)⁻¹
        ≤ ∑ _I ∈ blk k, ((2 ^ k : ℝ) ^ s)⁻¹ := Finset.sum_le_sum hterm
      _ = ((blk k).card : ℝ) * ((2 ^ k : ℝ) ^ s)⁻¹ := by simp
      _ ≤ (C * ((2 ^ (k + 1) : ℕ) : ℝ)) * ((2 ^ k : ℝ) ^ s)⁻¹ :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = (2 * C) * ((2 : ℝ) ^ (1 - s)) ^ k := by
          push_cast
          rw [pow_succ, ← Real.rpow_natCast (2 : ℝ) k]
          rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 2)]
          rw [← Real.rpow_natCast ((2 : ℝ) ^ (1 - s)) k, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 2)]
          rw [← Real.rpow_neg (by positivity : (0 : ℝ) ≤ 2)]
          have h1 : (2 : ℝ) ^ (k : ℝ) * (2 : ℝ) ^ (-((k : ℝ) * s)) = (2 : ℝ) ^ ((1 - s) * (k : ℝ)) := by
            rw [← Real.rpow_add (by positivity : (0 : ℝ) < 2)]
            congr 1; ring
          calc C * ((2 : ℝ) ^ (k : ℝ) * 2) * (2 : ℝ) ^ (-((k : ℝ) * s))
              = 2 * C * ((2 : ℝ) ^ (k : ℝ) * (2 : ℝ) ^ (-((k : ℝ) * s))) := by ring
            _ = 2 * C * (2 : ℝ) ^ ((1 - s) * (k : ℝ)) := by rw [h1]
  refine hbound.trans ?_
  rw [← Finset.mul_sum]
  have hr_nonneg : (0 : ℝ) ≤ (2 : ℝ) ^ (1 - s) := by positivity
  have hr_lt_one : (2 : ℝ) ^ (1 - s) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hgeo := (summable_geometric_of_lt_one hr_nonneg hr_lt_one).sum_le_tsum
    (Finset.range (Nat.log 2 M + 1)) (fun k _ => pow_nonneg hr_nonneg k)
  rw [tsum_geometric_of_lt_one hr_nonneg hr_lt_one] at hgeo
  calc (2 * C) * ∑ k ∈ Finset.range (Nat.log 2 M + 1), ((2 : ℝ) ^ (1 - s)) ^ k
      ≤ (2 * C) * (1 - (2 : ℝ) ^ (1 - s))⁻¹ := mul_le_mul_of_nonneg_left hgeo (by positivity)
    _ = (2 * C) / (1 - (2 : ℝ) ^ (1 - s)) := by rw [div_eq_mul_inv]

private lemma dedekindZeta_eq_realDedekindZeta (F : Type*) [Field F] [NumberField F]
    {s : ℝ} (hs : 1 < s) :
    NumberField.dedekindZeta F (s : ℂ) = (realDedekindZeta F s : ℂ) := by
  have hsum : Summable (fun I : (Ideal (𝓞 F))⁰ => ((Ideal.absNorm (I : Ideal (𝓞 F)) : ℝ) ^ s)⁻¹) :=
    summable_realDedekindZeta F hs
  have hfiber :
      ∑' n : ℕ, ∑' I : {I : (Ideal (𝓞 F))⁰ // Ideal.absNorm (I : Ideal (𝓞 F)) = n},
        ((Ideal.absNorm (I.1 : Ideal (𝓞 F)) : ℝ) ^ s)⁻¹ = realDedekindZeta F s :=
    tsum_fiberwise_nonneg hsum (fun _ => by positivity)
      (fun I : (Ideal (𝓞 F))⁰ => Ideal.absNorm (I : Ideal (𝓞 F)))
  have hterm_eq : ∀ n : ℕ,
      ((∑' I : {I : (Ideal (𝓞 F))⁰ // Ideal.absNorm (I : Ideal (𝓞 F)) = n},
        ((Ideal.absNorm (I.1 : Ideal (𝓞 F)) : ℝ) ^ s)⁻¹ : ℝ) : ℂ) =
      LSeries.term (fun k : ℕ => (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = k} : ℂ)) (s : ℂ) n := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn0
    · have : IsEmpty {I : (Ideal (𝓞 F))⁰ // Ideal.absNorm (I : Ideal (𝓞 F)) = 0} := by
        refine ⟨fun ⟨I, hI⟩ => Ideal.absNorm_ne_zero_of_nonZeroDivisors I hI⟩
      simp [LSeries.term]
    · have : Finite {I : Ideal (𝓞 F) // Ideal.absNorm I = n} :=
        Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 F) n
      have : Finite {I : (Ideal (𝓞 F))⁰ // Ideal.absNorm (I : Ideal (𝓞 F)) = n} :=
        Finite.of_injective
          (fun x : {I : (Ideal (𝓞 F))⁰ // Ideal.absNorm (I : Ideal (𝓞 F)) = n} =>
            (⟨x.1.1, x.2⟩ : {I : Ideal (𝓞 F) // Ideal.absNorm I = n}))
          (fun x y h => Subtype.ext (Subtype.ext (Subtype.mk.inj h)))
      have heq_card :
          Nat.card {I : (Ideal (𝓞 F))⁰ // Ideal.absNorm (I : Ideal (𝓞 F)) = n} =
          Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} := by
        apply Nat.card_congr
        refine
          { toFun := fun x => ⟨x.1.1, x.2⟩
            invFun := fun x => ⟨⟨x.1, Ideal.absNorm_ne_zero_iff_mem_nonZeroDivisors.mp (by omega)⟩, x.2⟩
            left_inv := fun x => by ext; rfl
            right_inv := fun x => by ext; rfl }
      rw [LSeries.term_of_ne_zero hn0]
      have hts : ∑' I : {I : (Ideal (𝓞 F))⁰ // Ideal.absNorm (I : Ideal (𝓞 F)) = n},
          ((Ideal.absNorm (I.1 : Ideal (𝓞 F)) : ℝ) ^ s)⁻¹ =
          (Nat.card {I : (Ideal (𝓞 F))⁰ // Ideal.absNorm (I : Ideal (𝓞 F)) = n} : ℝ) / (n : ℝ) ^ s := by
        have : ∀ I : {I : (Ideal (𝓞 F))⁰ // Ideal.absNorm (I : Ideal (𝓞 F)) = n},
            ((Ideal.absNorm (I.1 : Ideal (𝓞 F)) : ℝ) ^ s)⁻¹ = ((n : ℝ) ^ s)⁻¹ := by
          intro I; rw [I.2]
        simp_rw [this, tsum_const, nsmul_eq_mul, div_eq_mul_inv]
      rw [hts, heq_card]
      push_cast
      rw [Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_natCast]
  rw [NumberField.dedekindZeta, LSeries, ← hfiber, Complex.ofReal_tsum]
  apply tsum_congr
  intro n
  exact (hterm_eq n).symm

private lemma realDedekindZeta_pos (F : Type*) [Field F] [NumberField F]
    {s : ℝ} (hs : 1 < s) : 0 < realDedekindZeta F s := by
  have hsum := summable_realDedekindZeta F hs
  let top0 : (Ideal (𝓞 F))⁰ := ⟨⊤, by rw [mem_nonZeroDivisors_iff_ne_zero]; exact top_ne_bot⟩
  have h1 : (1 : ℝ) ≤ realDedekindZeta F s := by
    have hle := hsum.le_tsum top0 (fun _ _ => by positivity)
    unfold realDedekindZeta
    simpa [top0, Ideal.absNorm_top] using hle
  linarith

/- Section 3: Prime ideal factorization and real Euler product -/

private lemma absNorm_prime_ge_two {F : Type*} [Field F] [NumberField F]
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    2 ≤ Ideal.absNorm P.asIdeal := by
  have : P.asIdeal.IsMaximal := P.isMaximal
  obtain ⟨p, n, hn, _, hp, hnorm⟩ := Ideal.exists_prime_and_absNorm_eq_pow P.asIdeal
  rw [hnorm]
  calc 2 ≤ p := hp.two_le
    _ = p ^ 1 := (pow_one p).symm
    _ ≤ p ^ n := Nat.pow_le_pow_right hp.pos hn

private lemma multiset_prod_eq_prod_toFinset_count {α : Type*} [CommMonoid α] [DecidableEq α]
    (m : Multiset α) : m.prod = ∏ x ∈ m.toFinset, x ^ m.count x := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.prod_cons, ih]
    by_cases ha : a ∈ s.toFinset
    · have hto : (a ::ₘ s).toFinset = s.toFinset := by
        ext x; simp only [Multiset.mem_toFinset, Multiset.mem_cons]
        exact ⟨fun h => h.elim (fun hx => hx ▸ Multiset.mem_toFinset.mp ha) id, Or.inr⟩
      rw [hto, ← Finset.mul_prod_erase _ _ ha, ← Finset.mul_prod_erase s.toFinset _ ha]
      rw [Multiset.count_cons_self, pow_succ', mul_assoc]
      congr 1; congr 1
      apply Finset.prod_congr rfl
      intro x hx
      have hxa : x ≠ a := (Finset.mem_erase.mp hx).1
      rw [Multiset.count_cons_of_ne hxa]
    · have hto : (a ::ₘ s).toFinset = insert a s.toFinset := by
        ext x; simp [Multiset.mem_toFinset]
      rw [hto, Finset.prod_insert ha, Multiset.count_cons_self]
      have h0 : s.count a = 0 := Multiset.count_eq_zero.mpr (by simpa [Multiset.mem_toFinset] using ha)
      rw [h0, zero_add, pow_one]
      congr 1
      apply Finset.prod_congr rfl
      intro x hx
      have hxa : x ≠ a := fun h => ha (h ▸ hx)
      rw [Multiset.count_cons_of_ne hxa]

private lemma normalizedFactors_finset_prod_pow {F : Type*} [Field F] [NumberField F]
    [DecidableEq (IsDedekindDomain.HeightOneSpectrum (𝓞 F))]
    (T : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
    (g : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → ℕ)
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    (UniqueFactorizationMonoid.normalizedFactors
      (∏ Q ∈ T, Q.asIdeal ^ g Q)).count P.asIdeal = if P ∈ T then g P else 0 := by
  induction T using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, UniqueFactorizationMonoid.normalizedFactors_one]
    simp
  | @insert a S ha ih =>
    rw [Finset.prod_insert ha]
    have ha_ne : a.asIdeal ^ g a ≠ ⊥ := pow_ne_zero _ a.ne_bot
    have hS_ne : (∏ Q ∈ S, Q.asIdeal ^ g Q) ≠ ⊥ :=
      Finset.prod_ne_zero_iff.mpr (fun Q _ => pow_ne_zero _ Q.ne_bot)
    have hmul : UniqueFactorizationMonoid.normalizedFactors (a.asIdeal ^ g a * ∏ Q ∈ S, Q.asIdeal ^ g Q) =
        UniqueFactorizationMonoid.normalizedFactors (a.asIdeal ^ g a) +
        UniqueFactorizationMonoid.normalizedFactors (∏ Q ∈ S, Q.asIdeal ^ g Q) :=
      UniqueFactorizationMonoid.normalizedFactors_mul ha_ne hS_ne
    rw [hmul, Multiset.count_add, ih, UniqueFactorizationMonoid.normalizedFactors_pow,
      Multiset.count_nsmul]
    have haprime : Prime a.asIdeal := Ideal.prime_of_isPrime a.ne_bot a.isPrime
    have hnf : UniqueFactorizationMonoid.normalizedFactors a.asIdeal = {a.asIdeal} := by
      simpa using UniqueFactorizationMonoid.normalizedFactors_irreducible haprime.irreducible
    rw [hnf, Multiset.count_singleton]
    by_cases hPa : P = a
    · subst hPa
      simp [ha]
    · have hne : P.asIdeal ≠ a.asIdeal := fun h => hPa (by cases P; cases a; simp_all)
      simp [hne, hPa]

private lemma ideal_unique_factorization_equiv (F : Type*) [Field F] [NumberField F] :
    ∃ e : (Ideal (𝓞 F))⁰ ≃ (IsDedekindDomain.HeightOneSpectrum (𝓞 F) →₀ ℕ),
      ∀ I : (Ideal (𝓞 F))⁰,
        Ideal.absNorm (I : Ideal (𝓞 F)) =
          (e I).prod (fun P k => (Ideal.absNorm P.asIdeal) ^ k) := by
  classical
  let toF : (Ideal (𝓞 F))⁰ → (IsDedekindDomain.HeightOneSpectrum (𝓞 F) →₀ ℕ) := fun I =>
    Finsupp.onFinset
      ((UniqueFactorizationMonoid.normalizedFactors I.1).toFinset.attach.image
        (fun x : {J : Ideal (𝓞 F) // J ∈ (UniqueFactorizationMonoid.normalizedFactors I.1).toFinset} =>
          let hP : Prime x.1 := UniqueFactorizationMonoid.prime_of_normalized_factor x.1
            (Multiset.mem_toFinset.mp x.2)
          ({ asIdeal := x.1
             isPrime := Ideal.isPrime_of_prime hP
             ne_bot := hP.ne_zero } : IsDedekindDomain.HeightOneSpectrum (𝓞 F))))
      (fun P => (UniqueFactorizationMonoid.normalizedFactors I.1).count P.asIdeal)
      (fun P hP => by
        have hmem : P.asIdeal ∈ UniqueFactorizationMonoid.normalizedFactors I.1 :=
          Multiset.count_pos.mp (Nat.pos_of_ne_zero hP)
        rw [Finset.mem_image]
        refine ⟨⟨P.asIdeal, Multiset.mem_toFinset.mpr hmem⟩, Finset.mem_attach _ _, ?_⟩
        cases P; rfl)
  let invF : (IsDedekindDomain.HeightOneSpectrum (𝓞 F) →₀ ℕ) → (Ideal (𝓞 F))⁰ := fun f =>
    ⟨f.prod (fun P k => P.asIdeal ^ k), by
      rw [mem_nonZeroDivisors_iff_ne_zero]
      change f.prod (fun P k => P.asIdeal ^ k) ≠ ⊥
      rw [Finsupp.prod]
      intro hbot
      obtain ⟨P, _, hP⟩ := Finset.prod_eq_zero_iff.mp hbot
      exact pow_ne_zero _ P.ne_bot hP⟩
  have hto_apply : ∀ I P, toF I P = (UniqueFactorizationMonoid.normalizedFactors I.1).count P.asIdeal :=
    fun _ _ => rfl
  have hleft : Function.LeftInverse invF toF := by
    intro I
    apply Subtype.ext
    change (toF I).prod (fun P k => P.asIdeal ^ k) = I.1
    have hI0 : I.1 ≠ ⊥ := by
      have := I.2; rwa [mem_nonZeroDivisors_iff_ne_zero] at this
    rw [← Ideal.prod_normalizedFactors_eq_self hI0]
    rw [Finsupp.prod, multiset_prod_eq_prod_toFinset_count]
    symm
    apply Finset.prod_bij (fun (J : Ideal (𝓞 F)) (hJ : J ∈ (UniqueFactorizationMonoid.normalizedFactors I.1).toFinset) =>
      let hP := UniqueFactorizationMonoid.prime_of_normalized_factor J (Multiset.mem_toFinset.mp hJ)
      ({ asIdeal := J, isPrime := Ideal.isPrime_of_prime hP, ne_bot := hP.ne_zero } :
        IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
    · intro J hJ
      rw [Finsupp.mem_support_iff, hto_apply]
      exact (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hJ)).ne'
    · intro J₁ _ J₂ _ h
      exact congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal h
    · intro P hP
      rw [Finsupp.mem_support_iff, hto_apply] at hP
      refine ⟨P.asIdeal, Multiset.mem_toFinset.mpr (Multiset.count_pos.mp (Nat.pos_of_ne_zero hP)), ?_⟩
      cases P; rfl
    · intro J hJ; rfl
  have hright : Function.RightInverse invF toF := by
    intro f
    ext P
    rw [hto_apply]
    change (UniqueFactorizationMonoid.normalizedFactors
      (∏ Q ∈ f.support, Q.asIdeal ^ f Q)).count P.asIdeal = f P
    rw [normalizedFactors_finset_prod_pow]
    by_cases hP : P ∈ f.support
    · simp [hP]
    · simp [hP, Finsupp.notMem_support_iff.mp hP]
  refine ⟨⟨toF, invF, hleft, hright⟩, fun I => ?_⟩
  have hEq : (invF (toF I)).1 = I.1 := congrArg Subtype.val (hleft I)
  rw [← hEq]
  change Ideal.absNorm ((toF I).prod (fun P k => P.asIdeal ^ k)) = _
  rw [Finsupp.prod, Finsupp.prod, map_prod]
  apply Finset.prod_congr rfl
  intro P _
  rw [map_pow]
  rfl

private def insertEquivOption {α : Type*} [DecidableEq α] {a : α} {S : Finset α} (ha : a ∉ S) :
    ↥(insert a S) ≃ Option ↥S where
  toFun x := if h : x.1 = a then none else some ⟨x.1, (Finset.mem_insert.mp x.2).resolve_left h⟩
  invFun
    | none => ⟨a, Finset.mem_insert_self a S⟩
    | some y => ⟨y.1, Finset.mem_insert_of_mem y.2⟩
  left_inv x := by
    dsimp; split_ifs with h
    · exact Subtype.ext h.symm
    · rfl
  right_inv
    | none => by simp
    | some y => by
      have hne : y.1 ≠ a := fun h => ha (h ▸ y.2)
      simp [hne]

private lemma prod_insert_subtype {α M : Type*} [DecidableEq α] [CommMonoid M]
    {a : α} {S : Finset α} (ha : a ∉ S) (f : ↥(insert a S) → M) :
    (∏ P : ↥(insert a S), f P) =
      f ⟨a, Finset.mem_insert_self a S⟩ *
        ∏ P : ↥S, f ⟨P.1, Finset.mem_insert_of_mem P.2⟩ := by
  rw [Fintype.prod_equiv (insertEquivOption ha) f
    (fun o => match o with
      | none => f ⟨a, Finset.mem_insert_self a S⟩
      | some y => f ⟨y.1, Finset.mem_insert_of_mem y.2⟩)
    (fun x => by
      dsimp [insertEquivOption]
      split_ifs with h
      · have hx : (⟨a, Finset.mem_insert_self a S⟩ : ↥(insert a S)) = x := Subtype.ext h.symm
        rw [hx]
      · rfl)]
  exact Fintype.prod_option _

private lemma summable_prod_of_nonneg {α β : Type*} {f : α → ℝ} {g : β → ℝ}
    (hf : Summable f) (hg : Summable g) (hf0 : ∀ a, 0 ≤ f a) (hg0 : ∀ b, 0 ≤ g b) :
    Summable (fun p : α × β => f p.1 * g p.2) := by
  classical
  refine summable_of_sum_le (f := fun p : α × β => f p.1 * g p.2)
    (fun p => mul_nonneg (hf0 p.1) (hg0 p.2)) (c := (∑' a, f a) * (∑' b, g b)) fun u => ?_
  have hsub : u ⊆ (u.image Prod.fst) ×ˢ (u.image Prod.snd) := fun p hp =>
    Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hp, Finset.mem_image_of_mem _ hp⟩
  calc ∑ p ∈ u, f p.1 * g p.2
      ≤ ∑ p ∈ (u.image Prod.fst) ×ˢ (u.image Prod.snd), f p.1 * g p.2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => mul_nonneg (hf0 p.1) (hg0 p.2))
    _ = (∑ a ∈ u.image Prod.fst, f a) * (∑ b ∈ u.image Prod.snd, g b) := by
        rw [Finset.sum_product, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a _; rw [Finset.mul_sum]
    _ ≤ (∑' a, f a) * (∑' b, g b) :=
        mul_le_mul (hf.sum_le_tsum _ (fun a _ => hf0 a)) (hg.sum_le_tsum _ (fun b _ => hg0 b))
          (Finset.sum_nonneg (fun b _ => hg0 b)) (tsum_nonneg hf0)

private lemma tsum_comp_le_of_inj {α β : Type*} {f : β → ℝ} (hf : Summable f)
    (hf0 : ∀ b, 0 ≤ f b) {i : α → β} (hi : Function.Injective i) :
    ∑' a : α, f (i a) ≤ ∑' b : β, f b := by
  classical
  have hcomp : Summable (fun a : α => f (i a)) := hf.comp_injective hi
  apply hcomp.tsum_le_of_sum_le
  intro u
  rw [← Finset.sum_image (fun a _ b _ h => hi h)]
  exact hf.sum_le_tsum (u.image i) (fun b _ => hf0 b)

private lemma summable_finite_euler_prod (F : Type*) [Field F] [NumberField F]
    {s : ℝ} (hs : 1 < s) (T : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) :
    Summable (fun g : ↥T → ℕ => ∏ P : T, (((Ideal.absNorm P.1.asIdeal : ℝ) ^ s)⁻¹) ^ (g P)) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    exact Summable.of_finite
  | @insert a T ha ih =>
    have ha_ge : (2 : ℝ) ≤ Ideal.absNorm a.asIdeal := by exact_mod_cast absNorm_prime_ge_two a
    have hr0 : (0 : ℝ) ≤ ((Ideal.absNorm a.asIdeal : ℝ) ^ s)⁻¹ := by positivity
    have hr1 : ((Ideal.absNorm a.asIdeal : ℝ) ^ s)⁻¹ < 1 :=
      inv_lt_one_of_one_lt₀ (Real.one_lt_rpow (by linarith) (by linarith))
    have hsum1 : Summable (fun n : ℕ => ‖(((Ideal.absNorm a.asIdeal : ℝ) ^ s)⁻¹) ^ n‖) := by
      simpa only [Real.norm_of_nonneg (pow_nonneg hr0 _)] using summable_geometric_of_lt_one hr0 hr1
    have hsum2 : Summable (fun g : ↥T → ℕ =>
        ‖∏ P : T, (((Ideal.absNorm P.1.asIdeal : ℝ) ^ s)⁻¹) ^ (g P)‖) := by
      refine ih.congr (fun g => ?_)
      exact (Real.norm_of_nonneg (Finset.prod_nonneg (fun _ _ => by positivity))).symm
    have hprod := summable_mul_of_summable_norm hsum1 hsum2
    let e : (↥(insert a T) → ℕ) ≃ (ℕ × (↥T → ℕ)) :=
      { toFun := fun g => (g ⟨a, Finset.mem_insert_self a T⟩,
          fun P => g ⟨P.1, Finset.mem_insert_of_mem P.2⟩)
        invFun := fun ⟨n, g'⟩ P =>
          if h : P.1 = a then n else g' ⟨P.1, (Finset.mem_insert.mp P.2).resolve_left h⟩
        left_inv := fun g => by
          funext P; dsimp; split_ifs with h
          · have hP : (⟨a, Finset.mem_insert_self a T⟩ : ↥(insert a T)) = P := Subtype.ext h.symm
            rw [hP]
          · rfl
        right_inv := fun ⟨n, g'⟩ => by
          apply Prod.ext
          · simp
          · funext P
            have : P.1 ≠ a := fun h => ha (h ▸ P.2)
            simp [this] }
    refine (hprod.comp_injective e.injective).congr fun g => ?_
    exact (prod_insert_subtype ha
      (fun P : ↥(insert a T) => (((Ideal.absNorm P.1.asIdeal : ℝ) ^ s)⁻¹) ^ (g P))).symm

private lemma finite_euler_prod_eq_tsum (F : Type*) [Field F] [NumberField F]
    {s : ℝ} (hs : 1 < s) (T : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) :
    ∏ P ∈ T, (1 - ((Ideal.absNorm P.asIdeal : ℝ) ^ s)⁻¹)⁻¹ =
      ∑' g : ↥T → ℕ, ∏ P : T, (((Ideal.absNorm P.1.asIdeal : ℝ) ^ s)⁻¹) ^ (g P) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    simp
  | @insert a T ha ih =>
    rw [Finset.prod_insert ha, ih]
    have ha_ge : (2 : ℝ) ≤ Ideal.absNorm a.asIdeal := by exact_mod_cast absNorm_prime_ge_two a
    have hr0 : (0 : ℝ) ≤ ((Ideal.absNorm a.asIdeal : ℝ) ^ s)⁻¹ := by positivity
    have hr1 : ((Ideal.absNorm a.asIdeal : ℝ) ^ s)⁻¹ < 1 :=
      inv_lt_one_of_one_lt₀ (Real.one_lt_rpow (by linarith) (by linarith))
    rw [← tsum_geometric_of_lt_one hr0 hr1]
    have hsum1 : Summable (fun n : ℕ => ‖(((Ideal.absNorm a.asIdeal : ℝ) ^ s)⁻¹) ^ n‖) := by
      simpa only [Real.norm_of_nonneg (pow_nonneg hr0 _)] using summable_geometric_of_lt_one hr0 hr1
    have hsum2 : Summable (fun g : ↥T → ℕ =>
        ‖∏ P : T, (((Ideal.absNorm P.1.asIdeal : ℝ) ^ s)⁻¹) ^ (g P)‖) := by
      refine (summable_finite_euler_prod F hs T).congr (fun g => ?_)
      exact (Real.norm_of_nonneg (Finset.prod_nonneg (fun _ _ => by positivity))).symm
    rw [tsum_mul_tsum_of_summable_norm hsum1 hsum2]
    let e : (ℕ × (↥T → ℕ)) ≃ (↥(insert a T) → ℕ) :=
      { toFun := fun ⟨n, g'⟩ P =>
          if h : P.1 = a then n else g' ⟨P.1, (Finset.mem_insert.mp P.2).resolve_left h⟩
        invFun := fun g => (g ⟨a, Finset.mem_insert_self a T⟩,
          fun P => g ⟨P.1, Finset.mem_insert_of_mem P.2⟩)
        left_inv := fun ⟨n, g'⟩ => by
          apply Prod.ext
          · simp
          · funext P
            have : P.1 ≠ a := fun h => ha (h ▸ P.2)
            simp [this]
        right_inv := fun g => by
          funext P; dsimp; split_ifs with h
          · have hP : (⟨a, Finset.mem_insert_self a T⟩ : ↥(insert a T)) = P := Subtype.ext h.symm
            rw [hP]
          · rfl }
    rw [← e.tsum_eq]
    apply tsum_congr
    rintro ⟨n, g'⟩
    rw [prod_insert_subtype ha
      (fun P : ↥(insert a T) => (((Ideal.absNorm P.1.asIdeal : ℝ) ^ s)⁻¹) ^ (e (n, g') P))]
    congr 1
    · simp [e]
    · apply Finset.prod_congr rfl
      intro P _
      have hne : P.1 ≠ a := fun h => ha (h ▸ P.2)
      simp [e, hne]

private lemma log_realDedekindZeta_eq_tsum (F : Type*) [Field F] [NumberField F]
    {s : ℝ} (hs : 1 < s) :
    Summable (fun P : IsDedekindDomain.HeightOneSpectrum (𝓞 F) =>
      -Real.log (1 - ((Ideal.absNorm P.asIdeal : ℝ) ^ s)⁻¹)) ∧
    Real.log (realDedekindZeta F s) =
      ∑' P : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
        -Real.log (1 - ((Ideal.absNorm P.asIdeal : ℝ) ^ s)⁻¹) := by
  classical
  obtain ⟨e, he⟩ := ideal_unique_factorization_equiv F
  have hZsum := summable_realDedekindZeta F hs
  have hZpos := realDedekindZeta_pos F hs
  have hterm_pos : ∀ P : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
      0 < 1 - ((Ideal.absNorm P.asIdeal : ℝ) ^ s)⁻¹ := by
    intro P
    have h2 : (2 : ℝ) ≤ Ideal.absNorm P.asIdeal := by exact_mod_cast absNorm_prime_ge_two P
    have hpow : (1 : ℝ) < (Ideal.absNorm P.asIdeal : ℝ) ^ s :=
      Real.one_lt_rpow (by linarith) (by linarith)
    have hlt : ((Ideal.absNorm P.asIdeal : ℝ) ^ s)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hpow
    linarith
  have hlog_nonneg : ∀ P : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
      0 ≤ -Real.log (1 - ((Ideal.absNorm P.asIdeal : ℝ) ^ s)⁻¹) := by
    intro P
    have hle : 1 - ((Ideal.absNorm P.asIdeal : ℝ) ^ s)⁻¹ ≤ 1 := by
      have : (0 : ℝ) ≤ ((Ideal.absNorm P.asIdeal : ℝ) ^ s)⁻¹ := by positivity
      linarith
    linarith [Real.log_nonpos (hterm_pos P).le hle]
  have hfin_le : ∀ T : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)),
      ∏ P ∈ T, (1 - ((Ideal.absNorm P.asIdeal : ℝ) ^ s)⁻¹)⁻¹ ≤ realDedekindZeta F s := by
    intro T
    rw [finite_euler_prod_eq_tsum F hs T]
    let mkFinsupp : (↥T → ℕ) → (IsDedekindDomain.HeightOneSpectrum (𝓞 F) →₀ ℕ) := fun g =>
      Finsupp.onFinset T (fun P => if h : P ∈ T then g ⟨P, h⟩ else 0)
        (fun P hP => by by_contra h; simp [h] at hP)
    let ι : (↥T → ℕ) → (Ideal (𝓞 F))⁰ := fun g => e.symm (mkFinsupp g)
    have hι_inj : Function.Injective ι := by
      intro g₁ g₂ h
      have h' := e.symm.injective h
      funext P
      have := congrArg (fun f => f P.1) h'
      simpa [mkFinsupp, P.2] using this
    have hι_val : ∀ g : ↥T → ℕ,
        ((Ideal.absNorm ((ι g) : Ideal (𝓞 F)) : ℝ) ^ s)⁻¹ =
          ∏ P : T, (((Ideal.absNorm P.1.asIdeal : ℝ) ^ s)⁻¹) ^ (g P) := by
      intro g
      rw [he (ι g), Equiv.apply_symm_apply, Finsupp.prod]
      have hsupp : (mkFinsupp g).support ⊆ T := by
        intro P hP
        by_contra h
        simp [mkFinsupp, Finsupp.mem_support_iff, h] at hP
      have hprod_eq : ∏ P ∈ (mkFinsupp g).support, Ideal.absNorm P.asIdeal ^ (mkFinsupp g P) =
          ∏ P ∈ T, Ideal.absNorm P.asIdeal ^ (mkFinsupp g P) := by
        apply Finset.prod_subset hsupp
        intro P _ hnot
        rw [Finsupp.notMem_support_iff.mp hnot, pow_zero]
      rw [hprod_eq, Nat.cast_prod, ← Real.finsetProd_rpow T _ (fun _ _ => by positivity),
        ← Finset.prod_inv_distrib, ← Finset.prod_coe_sort T]
      apply Finset.prod_congr rfl
      intro P _
      have hval : mkFinsupp g P.1 = g P := by simp [mkFinsupp, P.2]
      rw [hval, Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity), mul_comm,
        Real.rpow_mul (by positivity), Real.rpow_natCast, inv_pow]
    have hcomp_le := tsum_comp_le_of_inj hZsum (fun _ => by positivity) hι_inj
    unfold realDedekindZeta
    simpa only [hι_val] using hcomp_le
  have hsum_le : ∀ T : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)),
      ∑ P ∈ T, -Real.log (1 - ((Ideal.absNorm P.asIdeal : ℝ) ^ s)⁻¹) ≤
        Real.log (realDedekindZeta F s) := by
    intro T
    have hprod_pos : 0 < ∏ P ∈ T, (1 - ((Ideal.absNorm P.asIdeal : ℝ) ^ s)⁻¹)⁻¹ :=
      Finset.prod_pos (fun P _ => inv_pos.mpr (hterm_pos P))
    have hle := Real.log_le_log hprod_pos (hfin_le T)
    rw [Real.log_prod (fun P _ => (inv_pos.mpr (hterm_pos P)).ne')] at hle
    simpa only [Real.log_inv] using hle
  have hPsum : Summable (fun P : IsDedekindDomain.HeightOneSpectrum (𝓞 F) =>
      -Real.log (1 - ((Ideal.absNorm P.asIdeal : ℝ) ^ s)⁻¹)) :=
    summable_of_sum_le hlog_nonneg hsum_le
  refine ⟨hPsum, le_antisymm ?_ (hPsum.tsum_le_of_sum_le hsum_le)⟩
  rw [Real.log_le_iff_le_exp hZpos]
  apply hZsum.tsum_le_of_sum_le
  intro U
  let T : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)) := U.biUnion (fun I => (e I).support)
  have hU_le : ∑ I ∈ U, ((Ideal.absNorm (I : Ideal (𝓞 F)) : ℝ) ^ s)⁻¹ ≤
      ∏ P ∈ T, (1 - ((Ideal.absNorm P.asIdeal : ℝ) ^ s)⁻¹)⁻¹ := by
    rw [finite_euler_prod_eq_tsum F hs T]
    let κ : (Ideal (𝓞 F))⁰ → (↥T → ℕ) := fun I P => e I P.1
    have hκ_inj : Set.InjOn κ U := by
      intro I₁ hI₁ I₂ hI₂ heq
      apply e.injective
      ext P
      by_cases hP : P ∈ T
      · exact congrFun heq ⟨P, hP⟩
      · have h1 : P ∉ (e I₁).support := fun h => hP (Finset.mem_biUnion.mpr ⟨I₁, hI₁, h⟩)
        have h2 : P ∉ (e I₂).support := fun h => hP (Finset.mem_biUnion.mpr ⟨I₂, hI₂, h⟩)
        rw [Finsupp.notMem_support_iff.mp h1, Finsupp.notMem_support_iff.mp h2]
    have hκ_val : ∀ I ∈ U,
        ((Ideal.absNorm (I : Ideal (𝓞 F)) : ℝ) ^ s)⁻¹ =
          ∏ P : T, (((Ideal.absNorm P.1.asIdeal : ℝ) ^ s)⁻¹) ^ (κ I P) := by
      intro I hI
      rw [he I, Finsupp.prod]
      have hsub : (e I).support ⊆ T := fun P hP => Finset.mem_biUnion.mpr ⟨I, hI, hP⟩
      have hprod_eq : ∏ P ∈ (e I).support, Ideal.absNorm P.asIdeal ^ (e I P) =
          ∏ P ∈ T, Ideal.absNorm P.asIdeal ^ (e I P) := by
        apply Finset.prod_subset hsub
        intro P _ hnot
        rw [Finsupp.notMem_support_iff.mp hnot, pow_zero]
      rw [hprod_eq, Nat.cast_prod, ← Real.finsetProd_rpow T _ (fun _ _ => by positivity),
        ← Finset.prod_inv_distrib, ← Finset.prod_coe_sort T]
      apply Finset.prod_congr rfl
      intro P _
      rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity), mul_comm,
        Real.rpow_mul (by positivity), Real.rpow_natCast, inv_pow]
    have hsum_g := summable_finite_euler_prod F hs T
    have himg : ∑ g ∈ U.image κ, ∏ P : T, (((Ideal.absNorm P.1.asIdeal : ℝ) ^ s)⁻¹) ^ (g P) =
        ∑ I ∈ U, ∏ P : T, (((Ideal.absNorm P.1.asIdeal : ℝ) ^ s)⁻¹) ^ (κ I P) :=
      Finset.sum_image (fun x hx y hy h => hκ_inj hx hy h)
    calc ∑ I ∈ U, ((Ideal.absNorm (I : Ideal (𝓞 F)) : ℝ) ^ s)⁻¹
        = ∑ I ∈ U, ∏ P : T, (((Ideal.absNorm P.1.asIdeal : ℝ) ^ s)⁻¹) ^ (κ I P) :=
          Finset.sum_congr rfl hκ_val
      _ = ∑ g ∈ U.image κ, ∏ P : T, (((Ideal.absNorm P.1.asIdeal : ℝ) ^ s)⁻¹) ^ (g P) :=
          himg.symm
      _ ≤ ∑' g : ↥T → ℕ, ∏ P : T, (((Ideal.absNorm P.1.asIdeal : ℝ) ^ s)⁻¹) ^ (g P) :=
          hsum_g.sum_le_tsum (U.image κ) (fun _ _ => by positivity)
  refine hU_le.trans ?_
  have hprod_eq_exp : ∏ P ∈ T, (1 - ((Ideal.absNorm P.asIdeal : ℝ) ^ s)⁻¹)⁻¹ =
      Real.exp (∑ P ∈ T, -Real.log (1 - ((Ideal.absNorm P.asIdeal : ℝ) ^ s)⁻¹)) := by
    rw [Real.exp_sum]
    apply Finset.prod_congr rfl
    intro P _
    rw [Real.exp_neg, Real.exp_log (hterm_pos P)]
  rw [hprod_eq_exp]
  exact Real.exp_le_exp.mpr (hPsum.sum_le_tsum T (fun P _ => hlog_nonneg P))

/- Section 4: Splitting completely in a Galois number field and Dirichlet series asymptotic -/

private def SplitsCompletely (F : Type*) [Field F] [NumberField F] (p : ℕ) : Prop :=
  p.Prime ∧ (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 F)).ncard = Module.finrank ℚ F

private lemma galois_fundamental_identity (F : Type*) [Field F] [NumberField F] [IsGalois ℚ F]
    (p : ℕ) [hp : Fact p.Prime] :
    (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 F)).ncard *
      (Ideal.ramificationIdxIn (Ideal.span {(p : ℤ)}) (𝓞 F) *
        Ideal.inertiaDegIn (Ideal.span {(p : ℤ)}) (𝓞 F)) = Module.finrank ℚ F := by
  let _ : MulSemiringAction (F ≃ₐ[ℚ] F) (𝓞 F) := IsIntegralClosure.MulSemiringAction ℤ ℚ F (𝓞 F)
  have : IsGaloisGroup (F ≃ₐ[ℚ] F) ℤ (𝓞 F) :=
    IsGaloisGroup.of_isFractionRing (F ≃ₐ[ℚ] F) ℤ (𝓞 F) ℚ F
  have : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Int.ideal_span_isMaximal_of_prime p).isPrime
  have h := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    (Ideal.span {(p : ℤ)}) (𝓞 F) (F ≃ₐ[ℚ] F)
  rwa [IsGalois.card_aut_eq_finrank ℚ F] at h

private lemma inertiaDeg_eq_inertiaDegIn_galois (F : Type*) [Field F] [NumberField F] [IsGalois ℚ F]
    (p : ℕ) [Fact p.Prime] (P : Ideal (𝓞 F)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})] :
    P.inertiaDeg ℤ = Ideal.inertiaDegIn (Ideal.span {(p : ℤ)}) (𝓞 F) := by
  let _ : MulSemiringAction (F ≃ₐ[ℚ] F) (𝓞 F) := IsIntegralClosure.MulSemiringAction ℤ ℚ F (𝓞 F)
  have : IsGaloisGroup (F ≃ₐ[ℚ] F) ℤ (𝓞 F) :=
    IsGaloisGroup.of_isFractionRing (F ≃ₐ[ℚ] F) ℤ (𝓞 F) ℚ F
  have : (Ideal.span {(p : ℤ)}).IsPrime := (Int.ideal_span_isMaximal_of_prime p).isPrime
  exact (Ideal.inertiaDegIn_eq_inertiaDeg (Ideal.span {(p : ℤ)}) P (F ≃ₐ[ℚ] F)).symm

private lemma prime_ideal_liesOver_natPrime {F : Type*} [Field F] [NumberField F]
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    ∃! p : ℕ, p.Prime ∧ P.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := by
  have : P.asIdeal.IsMaximal := P.isMaximal
  obtain ⟨p, _, _, hpP, hp, _⟩ := Ideal.exists_prime_and_absNorm_eq_pow P.asIdeal
  have : Fact p.Prime := ⟨hp⟩
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime p
  have hunder : P.asIdeal.under ℤ = Ideal.span {(p : ℤ)} := by
    have hle : Ideal.span {(p : ℤ)} ≤ P.asIdeal.under ℤ := by
      rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_under]
      simpa using hpP
    have hne : P.asIdeal.under ℤ ≠ ⊤ := Ideal.IsPrime.ne_top inferInstance
    exact (hmax.eq_of_le hne hle).symm
  refine ⟨p, ⟨hp, ⟨hunder.symm⟩⟩, ?_⟩
  rintro q ⟨hq, hqover⟩
  have hqeq : Ideal.span {(q : ℤ)} = Ideal.span {(p : ℤ)} :=
    hqover.over.trans hunder
  have hdvd : (p : ℤ) ∣ (q : ℤ) :=
    Ideal.span_singleton_le_span_singleton.mp hqeq.le
  have hdvdN : p ∣ q := Int.natCast_dvd_natCast.mp hdvd
  exact ((Nat.prime_dvd_prime_iff_eq hp hq).mp hdvdN).symm

private def basePrime {F : Type*} [Field F] [NumberField F]
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) : ℕ :=
  (prime_ideal_liesOver_natPrime P).choose

private lemma basePrime_spec {F : Type*} [Field F] [NumberField F]
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    (basePrime P).Prime ∧ P.asIdeal.LiesOver (Ideal.span {(basePrime P : ℤ)}) :=
  (prime_ideal_liesOver_natPrime P).choose_spec.1

private lemma basePrime_eq {F : Type*} [Field F] [NumberField F]
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) {p : ℕ} (hp : p.Prime)
    (hlo : P.asIdeal.LiesOver (Ideal.span {(p : ℤ)})) : basePrime P = p :=
  ((prime_ideal_liesOver_natPrime P).choose_spec.2 p ⟨hp, hlo⟩).symm

private lemma liesOver_basePrime_eq {F : Type*} [Field F] [NumberField F]
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) {p : ℕ} (h : basePrime P = p) :
    P.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := by
  subst h
  exact (basePrime_spec P).2

private lemma prime_ideal_ne_bot_of_liesOver_natPrime {F : Type*} [Field F] [NumberField F]
    {p : ℕ} (hp : p.Prime) {Q : Ideal (𝓞 F)} (hQ : Q.LiesOver (Ideal.span {(p : ℤ)})) :
    Q ≠ ⊥ := by
  intro hbot
  have h1 : (p : ℤ) ∈ Q.under ℤ := by
    rw [← hQ.over]; exact Ideal.subset_span rfl
  rw [hbot, Ideal.mem_under, Ideal.mem_bot, map_natCast, Nat.cast_eq_zero] at h1
  exact hp.ne_zero h1

private def fiber_basePrime_equiv_primesOver (F : Type*) [Field F] [NumberField F]
    (p : ℕ) (hp : p.Prime) :
    {P : IsDedekindDomain.HeightOneSpectrum (𝓞 F) // basePrime P = p} ≃
      Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 F) :=
  { toFun := fun P => ⟨P.1.asIdeal, P.1.isPrime, liesOver_basePrime_eq P.1 P.2⟩
    invFun := fun Q =>
      ⟨{ asIdeal := Q.1
         isPrime := Q.2.1
         ne_bot := prime_ideal_ne_bot_of_liesOver_natPrime hp Q.2.2 },
       basePrime_eq _ hp Q.2.2⟩
    left_inv := fun P => by ext; rfl
    right_inv := fun Q => by ext; rfl }

private lemma fiber_basePrime_card (F : Type*) [Field F] [NumberField F]
    (p : ℕ) (hp : p.Prime) :
    Nat.card {P : IsDedekindDomain.HeightOneSpectrum (𝓞 F) // basePrime P = p} =
      (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 F)).ncard := by
  rw [← Nat.card_coe_set_eq]
  exact Nat.card_congr (fiber_basePrime_equiv_primesOver F p hp)

private lemma summable_prime_rpow_inv (F : Type*) [Field F] [NumberField F]
    {s : ℝ} (hs : 1 < s) :
    Summable (fun P : IsDedekindDomain.HeightOneSpectrum (𝓞 F) =>
      ((Ideal.absNorm P.asIdeal : ℝ) ^ s)⁻¹) := by
  classical
  have hZs := summable_realDedekindZeta F hs
  let ι : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → (Ideal (𝓞 F))⁰ :=
    fun P => ⟨P.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr P.ne_bot⟩
  have hι : Function.Injective ι := fun P₁ P₂ h =>
    IsDedekindDomain.HeightOneSpectrum.ext (Subtype.mk.inj h)
  refine summable_of_sum_le
    (f := fun P : IsDedekindDomain.HeightOneSpectrum (𝓞 F) => ((Ideal.absNorm P.asIdeal : ℝ) ^ s)⁻¹)
    (fun _ => by positivity) (c := realDedekindZeta F s) fun u => ?_
  have himg : ∑ I ∈ u.image ι, ((Ideal.absNorm (I : Ideal (𝓞 F)) : ℝ) ^ s)⁻¹ =
      ∑ P ∈ u, ((Ideal.absNorm P.asIdeal : ℝ) ^ s)⁻¹ :=
    Finset.sum_image (fun _ _ _ _ h => hι h)
  rw [← himg]
  exact hZs.sum_le_tsum (u.image ι) (fun _ _ => by positivity)

private lemma splitsCompletely_of_eq {F : Type*} [Field F] [NumberField F]
    {p q : ℕ} (h : p = q) (hp : SplitsCompletely F p) : SplitsCompletely F q :=
  h ▸ hp

private lemma split_primes_tsum_eq (F : Type*) [Field F] [NumberField F] [IsGalois ℚ F]
    {s : ℝ} (hs : 1 < s) :
    ∑' P : ({P : IsDedekindDomain.HeightOneSpectrum (𝓞 F) | SplitsCompletely F (basePrime P)} : Set _),
      ((Ideal.absNorm P.1.asIdeal : ℝ) ^ s)⁻¹ =
      (Module.finrank ℚ F : ℝ) *
        (∑' p : {p : ℕ // SplitsCompletely F p}, ((p.1 : ℝ) ^ s)⁻¹) := by
  set SplitP : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :=
    {P | SplitsCompletely F (basePrime P)}
  have hP_s_sum := summable_prime_rpow_inv F hs
  have hsum_sp : Summable (fun P : SplitP => ((Ideal.absNorm P.1.asIdeal : ℝ) ^ s)⁻¹) :=
    hP_s_sum.subtype SplitP
  have hfib := tsum_fiberwise_nonneg hsum_sp (fun _ => by positivity)
    (fun P : SplitP => (⟨basePrime P.1, P.2⟩ : {p : ℕ // SplitsCompletely F p}))
  rw [← hfib, ← tsum_mul_left]
  apply tsum_congr
  rintro ⟨p, hp⟩
  have : Fact p.Prime := ⟨hp.1⟩
  have hfund := galois_fundamental_identity F p
  rw [hp.2] at hfund
  have hd_pos : 0 < Module.finrank ℚ F := Module.finrank_pos
  have hf1 : Ideal.inertiaDegIn (Ideal.span {(p : ℤ)}) (𝓞 F) = 1 :=
    Nat.eq_one_of_mul_eq_one_left (by nlinarith :
      Ideal.ramificationIdxIn _ _ * Ideal.inertiaDegIn _ _ = 1)
  have hnorm_p : ∀ P : {P : SplitP // (⟨basePrime P.1, P.2⟩ : {q : ℕ // SplitsCompletely F q}) = ⟨p, hp⟩},
      Ideal.absNorm P.1.1.asIdeal = p := by
    intro P
    have hbp : basePrime P.1.1 = p := congrArg Subtype.val P.2
    have : P.1.1.asIdeal.IsPrime := P.1.1.isPrime
    have : P.1.1.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := liesOver_basePrime_eq P.1.1 hbp
    have hfP : P.1.1.asIdeal.inertiaDeg ℤ = 1 := by
      rw [inertiaDeg_eq_inertiaDegIn_galois F p P.1.1.asIdeal, hf1]
    rw [← Ideal.pow_inertiaDeg p P.1.1.asIdeal, hfP, pow_one]
  have hequiv : {P : SplitP // (⟨basePrime P.1, P.2⟩ : {q : ℕ // SplitsCompletely F q}) = ⟨p, hp⟩} ≃
      {P : IsDedekindDomain.HeightOneSpectrum (𝓞 F) // basePrime P = p} :=
    { toFun := fun P => ⟨P.1.1, congrArg Subtype.val P.2⟩
      invFun := fun P => ⟨⟨P.1, splitsCompletely_of_eq P.2.symm hp⟩, Subtype.ext P.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have : Finite {P : IsDedekindDomain.HeightOneSpectrum (𝓞 F) // basePrime P = p} :=
    Finite.of_equiv _ (fiber_basePrime_equiv_primesOver F p hp.1).symm
  have : Finite {P : SplitP // (⟨basePrime P.1, P.2⟩ : {q : ℕ // SplitsCompletely F q}) = ⟨p, hp⟩} :=
    Finite.of_equiv _ hequiv.symm
  have hcard_p : Nat.card {P : SplitP // (⟨basePrime P.1, P.2⟩ : {q : ℕ // SplitsCompletely F q}) = ⟨p, hp⟩} =
      Module.finrank ℚ F := by
    rw [Nat.card_congr hequiv, fiber_basePrime_card F p hp.1, hp.2]
  simp_rw [hnorm_p, tsum_const, nsmul_eq_mul, hcard_p]

private lemma nonsplit_primes_tsum_le (F : Type*) [Field F] [NumberField F] [IsGalois ℚ F]
    (hram : {p : ℕ | p.Prime ∧
      Ideal.ramificationIdxIn (Ideal.span {(p : ℤ)}) (𝓞 F) ≠ 1}.Finite)
    {s : ℝ} (hs : 1 < s) :
    ∑' P : (({P : IsDedekindDomain.HeightOneSpectrum (𝓞 F) | SplitsCompletely F (basePrime P)}ᶜ : Set _)),
      ((Ideal.absNorm P.1.asIdeal : ℝ) ^ s)⁻¹ ≤
      (Module.finrank ℚ F : ℝ) * (hram.toFinset.card : ℝ) +
      (Module.finrank ℚ F : ℝ) * ∑' n : ℕ, ((n : ℝ) ^ (2 : ℝ))⁻¹ := by
  classical
  set d := Module.finrank ℚ F
  have hd_pos : 0 < d := Module.finrank_pos
  set SplitP : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :=
    {P | SplitsCompletely F (basePrime P)}
  have hP_s_sum := summable_prime_rpow_inv F hs
  have hsum_c : Summable (fun P : (SplitPᶜ : Set _) => ((Ideal.absNorm P.1.asIdeal : ℝ) ^ s)⁻¹) :=
    hP_s_sum.subtype _
  have hfib := tsum_fiberwise_nonneg hsum_c (fun _ => by positivity) (fun P : (SplitPᶜ : Set _) => basePrime P.1)
  rw [← hfib]
  have hsq_sum_nat : Summable (fun n : ℕ => ((n : ℝ) ^ (2 : ℝ))⁻¹) := by
    simp only [Real.rpow_two]
    exact Real.summable_nat_pow_inv.mpr (by norm_num : 1 < 2)
  have hfiber_bound : ∀ p : ℕ,
      (∑' P : {P : (SplitPᶜ : Set _) // basePrime P.1 = p},
        ((Ideal.absNorm P.1.1.asIdeal : ℝ) ^ s)⁻¹) ≤
        (if p ∈ hram.toFinset then (d : ℝ) else 0) + (d : ℝ) * ((p : ℝ) ^ (2 : ℝ))⁻¹ := by
    intro p
    by_cases hp : p.Prime
    · have : Fact p.Prime := ⟨hp⟩
      have hfund := galois_fundamental_identity F p
      have : Finite {P : IsDedekindDomain.HeightOneSpectrum (𝓞 F) // basePrime P = p} :=
        Finite.of_equiv _ (fiber_basePrime_equiv_primesOver F p hp).symm
      have hinj_sub : Function.Injective
          (fun P : {P : (SplitPᶜ : Set _) // basePrime P.1 = p} =>
            (⟨P.1.1, P.2⟩ : {P : IsDedekindDomain.HeightOneSpectrum (𝓞 F) // basePrime P = p})) :=
        fun _ _ h => Subtype.ext (Subtype.ext (Subtype.mk.inj h))
      have : Finite {P : (SplitPᶜ : Set _) // basePrime P.1 = p} :=
        Finite.of_injective _ hinj_sub
      have hcard_le_d : Nat.card {P : (SplitPᶜ : Set _) // basePrime P.1 = p} ≤ d := by
        have hle1 : Nat.card {P : (SplitPᶜ : Set _) // basePrime P.1 = p} ≤
            Nat.card {P : IsDedekindDomain.HeightOneSpectrum (𝓞 F) // basePrime P = p} :=
          natCard_le_of_inj hinj_sub
        rw [fiber_basePrime_card F p hp] at hle1
        have hpos_ef : 1 ≤ Ideal.ramificationIdxIn (Ideal.span {(p : ℤ)}) (𝓞 F) *
            Ideal.inertiaDegIn (Ideal.span {(p : ℤ)}) (𝓞 F) := by
          by_contra h0
          have : Ideal.ramificationIdxIn (Ideal.span {(p : ℤ)}) (𝓞 F) *
              Ideal.inertiaDegIn (Ideal.span {(p : ℤ)}) (𝓞 F) = 0 := by omega
          rw [this, mul_zero] at hfund
          omega
        nlinarith
      by_cases hR : p ∈ hram.toFinset
      · simp only [hR, ↓reduceIte]
        have hle1 : ∀ P : {P : (SplitPᶜ : Set _) // basePrime P.1 = p},
            ((Ideal.absNorm P.1.1.asIdeal : ℝ) ^ s)⁻¹ ≤ 1 := by
          intro P
          have h2 : (2 : ℝ) ≤ Ideal.absNorm P.1.1.asIdeal := by exact_mod_cast absNorm_prime_ge_two P.1.1
          exact inv_le_one_of_one_le₀ (Real.one_le_rpow (by linarith) (by linarith))
        have hts_le : ∑' P : {P : (SplitPᶜ : Set _) // basePrime P.1 = p},
            ((Ideal.absNorm P.1.1.asIdeal : ℝ) ^ s)⁻¹ ≤
            (Nat.card {P : (SplitPᶜ : Set _) // basePrime P.1 = p} : ℝ) := by
          calc ∑' P : {P : (SplitPᶜ : Set _) // basePrime P.1 = p},
                ((Ideal.absNorm P.1.1.asIdeal : ℝ) ^ s)⁻¹
              ≤ ∑' _P : {P : (SplitPᶜ : Set _) // basePrime P.1 = p}, (1 : ℝ) :=
                Summable.tsum_le_tsum hle1 Summable.of_finite Summable.of_finite
            _ = (Nat.card {P : (SplitPᶜ : Set _) // basePrime P.1 = p} : ℝ) := by simp
        have hcardR : (Nat.card {P : (SplitPᶜ : Set _) // basePrime P.1 = p} : ℝ) ≤ d := by
          exact_mod_cast hcard_le_d
        linarith [show (0 : ℝ) ≤ (d : ℝ) * ((p : ℝ) ^ (2 : ℝ))⁻¹ by positivity]
      · simp only [hR, ↓reduceIte, zero_add]
        have he1 : Ideal.ramificationIdxIn (Ideal.span {(p : ℤ)}) (𝓞 F) = 1 := by
          by_contra hne
          exact hR (hram.mem_toFinset.mpr ⟨hp, hne⟩)
        have hle_p2 : ∀ P : {P : (SplitPᶜ : Set _) // basePrime P.1 = p},
            ((Ideal.absNorm P.1.1.asIdeal : ℝ) ^ s)⁻¹ ≤ ((p : ℝ) ^ (2 : ℝ))⁻¹ := by
          intro P
          have hnot_split : ¬ SplitsCompletely F p := by
            have := P.1.2; rwa [Set.mem_compl_iff, Set.mem_ofPred_eq, P.2] at this
          have hncard_ne : (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 F)).ncard ≠ d :=
            fun h => hnot_split ⟨hp, h⟩
          rw [he1, one_mul] at hfund
          have hf2 : 2 ≤ Ideal.inertiaDegIn (Ideal.span {(p : ℤ)}) (𝓞 F) := by
            by_contra hlt
            push Not at hlt
            have hf0 : Ideal.inertiaDegIn (Ideal.span {(p : ℤ)}) (𝓞 F) ≠ 0 := by
              intro h0; rw [h0, mul_zero] at hfund; omega
            have hf1 : Ideal.inertiaDegIn (Ideal.span {(p : ℤ)}) (𝓞 F) = 1 := by omega
            rw [hf1, mul_one] at hfund
            exact hncard_ne hfund
          have : P.1.1.asIdeal.IsPrime := P.1.1.isPrime
          have : P.1.1.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := liesOver_basePrime_eq P.1.1 P.2
          have hfP : 2 ≤ P.1.1.asIdeal.inertiaDeg ℤ := by
            rw [inertiaDeg_eq_inertiaDegIn_galois F p P.1.1.asIdeal]
            exact hf2
          have hnorm_ge : p ^ 2 ≤ Ideal.absNorm P.1.1.asIdeal := by
            rw [← Ideal.pow_inertiaDeg p P.1.1.asIdeal]
            exact Nat.pow_le_pow_right hp.pos hfP
          have hnorm_geR : (p : ℝ) ^ (2 : ℝ) ≤ (Ideal.absNorm P.1.1.asIdeal : ℝ) := by
            rw [Real.rpow_two]
            exact_mod_cast hnorm_ge
          have hp_pos : (0 : ℝ) < (p : ℝ) ^ (2 : ℝ) := by
            have : (0 : ℝ) < p := by exact_mod_cast hp.pos
            positivity
          apply inv_anti₀ hp_pos
          calc (p : ℝ) ^ (2 : ℝ) ≤ (Ideal.absNorm P.1.1.asIdeal : ℝ) := hnorm_geR
            _ = (Ideal.absNorm P.1.1.asIdeal : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
            _ ≤ (Ideal.absNorm P.1.1.asIdeal : ℝ) ^ s := by
                have h2 : (2 : ℝ) ≤ Ideal.absNorm P.1.1.asIdeal := by exact_mod_cast absNorm_prime_ge_two P.1.1
                exact Real.rpow_le_rpow_of_exponent_le (by linarith) hs.le
        calc ∑' P : {P : (SplitPᶜ : Set _) // basePrime P.1 = p},
              ((Ideal.absNorm P.1.1.asIdeal : ℝ) ^ s)⁻¹
            ≤ ∑' _P : {P : (SplitPᶜ : Set _) // basePrime P.1 = p}, ((p : ℝ) ^ (2 : ℝ))⁻¹ :=
              Summable.tsum_le_tsum hle_p2 Summable.of_finite Summable.of_finite
          _ = (Nat.card {P : (SplitPᶜ : Set _) // basePrime P.1 = p} : ℝ) * ((p : ℝ) ^ (2 : ℝ))⁻¹ := by
              simp
          _ ≤ (d : ℝ) * ((p : ℝ) ^ (2 : ℝ))⁻¹ :=
              mul_le_mul_of_nonneg_right (by exact_mod_cast hcard_le_d) (by positivity)
    · have : IsEmpty {P : (SplitPᶜ : Set _) // basePrime P.1 = p} :=
        ⟨fun P => hp (P.2 ▸ (basePrime_spec P.1.1).1)⟩
      simp only [tsum_empty]
      have h1 : 0 ≤ (if p ∈ hram.toFinset then (d : ℝ) else 0) := by split_ifs <;> positivity
      have h2 : 0 ≤ (d : ℝ) * ((p : ℝ) ^ (2 : ℝ))⁻¹ := by positivity
      linarith
  have hsum_ind : Summable (fun p : ℕ => if p ∈ hram.toFinset then (d : ℝ) else 0) := by
    apply summable_of_ne_finset_zero (s := hram.toFinset)
    intro p hp; simp [hp]
  have hsum_rhs : Summable (fun p : ℕ =>
      (if p ∈ hram.toFinset then (d : ℝ) else 0) + (d : ℝ) * ((p : ℝ) ^ (2 : ℝ))⁻¹) :=
    hsum_ind.add (hsq_sum_nat.mul_left (d : ℝ))
  have hsum_lhs : Summable (fun p : ℕ =>
      ∑' P : {P : (SplitPᶜ : Set _) // basePrime P.1 = p},
        ((Ideal.absNorm P.1.1.asIdeal : ℝ) ^ s)⁻¹) :=
    Summable.of_nonneg_of_le (fun _ => tsum_nonneg (fun _ => by positivity)) hfiber_bound hsum_rhs
  calc ∑' p : ℕ, ∑' P : {P : (SplitPᶜ : Set _) // basePrime P.1 = p},
          ((Ideal.absNorm P.1.1.asIdeal : ℝ) ^ s)⁻¹
      ≤ ∑' p : ℕ, ((if p ∈ hram.toFinset then (d : ℝ) else 0) +
          (d : ℝ) * ((p : ℝ) ^ (2 : ℝ))⁻¹) :=
        hsum_lhs.tsum_le_tsum hfiber_bound hsum_rhs
    _ = (∑' p : ℕ, if p ∈ hram.toFinset then (d : ℝ) else 0) +
          ∑' p : ℕ, (d : ℝ) * ((p : ℝ) ^ (2 : ℝ))⁻¹ :=
        hsum_ind.tsum_add (hsq_sum_nat.mul_left (d : ℝ))
    _ = (d : ℝ) * (hram.toFinset.card : ℝ) + (d : ℝ) * ∑' n : ℕ, ((n : ℝ) ^ (2 : ℝ))⁻¹ := by
        congr 1
        · rw [tsum_eq_sum (s := hram.toFinset) (fun p hp => by simp [hp])]
          simp only [Finset.sum_ite_mem, Finset.inter_self, Finset.sum_const, nsmul_eq_mul]
          ring
        · rw [tsum_mul_left]

private lemma prime_zeta_sum_asymptotic (F : Type*) [Field F] [NumberField F] [IsGalois ℚ F]
    (hram : {p : ℕ | p.Prime ∧
      Ideal.ramificationIdxIn (Ideal.span {(p : ℤ)}) (𝓞 F) ≠ 1}.Finite) :
    ∃ C : ℝ, ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ),
      |(Module.finrank ℚ F : ℝ) *
        (∑' p : {p : ℕ // SplitsCompletely F p}, ((p.1 : ℝ) ^ s)⁻¹) -
        (-Real.log (s - 1))| ≤ C := by
  classical
  set d := Module.finrank ℚ F
  have hP_sq_sum : Summable (fun P : IsDedekindDomain.HeightOneSpectrum (𝓞 F) =>
      ((Ideal.absNorm P.asIdeal : ℝ) ^ (2 : ℝ))⁻¹) :=
    summable_prime_rpow_inv F (s := 2) (by norm_num)
  set C1 : ℝ := ∑' P : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
      ((Ideal.absNorm P.asIdeal : ℝ) ^ (2 : ℝ))⁻¹
  set C2 : ℝ := (d : ℝ) * (hram.toFinset.card : ℝ)
  set C3 : ℝ := (d : ℝ) * ∑' n : ℕ, ((n : ℝ) ^ (2 : ℝ))⁻¹
  have hdiff_bound : ∀ s : ℝ, 1 < s →
      |Real.log (realDedekindZeta F s) -
        (d : ℝ) * (∑' p : {p : ℕ // SplitsCompletely F p}, ((p.1 : ℝ) ^ s)⁻¹)| ≤
        C1 + C2 + C3 := by
    intro s hs
    obtain ⟨hlogSum, hlogEq⟩ := log_realDedekindZeta_eq_tsum F hs
    have hP_s_sum := summable_prime_rpow_inv F hs
    have h1 : |Real.log (realDedekindZeta F s) -
        ∑' P : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
          ((Ideal.absNorm P.asIdeal : ℝ) ^ s)⁻¹| ≤ C1 := by
      rw [hlogEq, ← hlogSum.tsum_sub hP_s_sum]
      have hnn : ∀ P : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
          0 ≤ -Real.log (1 - ((Ideal.absNorm P.asIdeal : ℝ) ^ s)⁻¹) -
            ((Ideal.absNorm P.asIdeal : ℝ) ^ s)⁻¹ ∧
          -Real.log (1 - ((Ideal.absNorm P.asIdeal : ℝ) ^ s)⁻¹) -
            ((Ideal.absNorm P.asIdeal : ℝ) ^ s)⁻¹ ≤
            ((Ideal.absNorm P.asIdeal : ℝ) ^ (2 : ℝ))⁻¹ := by
        intro P
        have h2 : (2 : ℝ) ≤ Ideal.absNorm P.asIdeal := by exact_mod_cast absNorm_prime_ge_two P
        have hle : ((Ideal.absNorm P.asIdeal : ℝ) ^ s)⁻¹ ≤ 1 / 2 := by
          rw [one_div]
          apply inv_anti₀ (by norm_num)
          calc (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := (Real.rpow_one 2).symm
            _ ≤ (2 : ℝ) ^ s := Real.rpow_le_rpow_of_exponent_le (by norm_num) hs.le
            _ ≤ (Ideal.absNorm P.asIdeal : ℝ) ^ s := Real.rpow_le_rpow (by norm_num) h2 (by linarith)
        have hbd := log_one_sub_bounds (by positivity) hle
        refine ⟨by linarith [hbd.1], ?_⟩
        have hsq : (((Ideal.absNorm P.asIdeal : ℝ) ^ s)⁻¹) ^ 2 ≤
            ((Ideal.absNorm P.asIdeal : ℝ) ^ (2 : ℝ))⁻¹ := by
          rw [inv_pow, ← Real.rpow_natCast ((Ideal.absNorm P.asIdeal : ℝ) ^ s) 2,
            ← Real.rpow_mul (by positivity)]
          apply inv_anti₀ (by positivity)
          exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by push_cast; linarith)
        linarith [hbd.2]
      rw [abs_of_nonneg (tsum_nonneg (fun P => (hnn P).1))]
      exact (hlogSum.sub hP_s_sum).tsum_le_tsum (fun P => (hnn P).2) hP_sq_sum
    let SplitP : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :=
      {P | SplitsCompletely F (basePrime P)}
    have hadd := hP_s_sum.tsum_subtype_add_tsum_subtype_compl SplitP
    rw [split_primes_tsum_eq F hs] at hadd
    have h2 : |∑' P : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
        ((Ideal.absNorm P.asIdeal : ℝ) ^ s)⁻¹ -
        (d : ℝ) * (∑' p : {p : ℕ // SplitsCompletely F p}, ((p.1 : ℝ) ^ s)⁻¹)| ≤ C2 + C3 := by
      have heq : ∑' P : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
          ((Ideal.absNorm P.asIdeal : ℝ) ^ s)⁻¹ -
          (d : ℝ) * (∑' p : {p : ℕ // SplitsCompletely F p}, ((p.1 : ℝ) ^ s)⁻¹) =
          ∑' P : (SplitPᶜ : Set _), ((Ideal.absNorm P.1.asIdeal : ℝ) ^ s)⁻¹ := by
        linarith
      rw [heq, abs_of_nonneg (tsum_nonneg (fun _ => by positivity))]
      exact nonsplit_primes_tsum_le F hram hs
    calc |Real.log (realDedekindZeta F s) -
            (d : ℝ) * (∑' p : {p : ℕ // SplitsCompletely F p}, ((p.1 : ℝ) ^ s)⁻¹)|
        = |(Real.log (realDedekindZeta F s) -
            ∑' P : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
              ((Ideal.absNorm P.asIdeal : ℝ) ^ s)⁻¹) +
          (∑' P : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
            ((Ideal.absNorm P.asIdeal : ℝ) ^ s)⁻¹ -
            (d : ℝ) * (∑' p : {p : ℕ // SplitsCompletely F p}, ((p.1 : ℝ) ^ s)⁻¹))| := by ring_nf
      _ ≤ |Real.log (realDedekindZeta F s) -
            ∑' P : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
              ((Ideal.absNorm P.asIdeal : ℝ) ^ s)⁻¹| +
          |∑' P : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
            ((Ideal.absNorm P.asIdeal : ℝ) ^ s)⁻¹ -
            (d : ℝ) * (∑' p : {p : ℕ // SplitsCompletely F p}, ((p.1 : ℝ) ^ s)⁻¹)| := abs_add_le _ _
      _ ≤ C1 + (C2 + C3) := add_le_add h1 h2
      _ = C1 + C2 + C3 := by ring
  have hres_pos : 0 < NumberField.dedekindZeta_residue F := NumberField.dedekindZeta_residue_pos F
  have ht_c := NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT F
  have ht_re : Tendsto (fun s : ℝ => (s - 1) * realDedekindZeta F s)
      (𝓝[>] (1 : ℝ)) (𝓝 (NumberField.dedekindZeta_residue F)) := by
    have ht_re0 := (Complex.continuous_re.tendsto _).comp ht_c
    simp only [Function.comp_def, Complex.ofReal_re] at ht_re0
    refine ht_re0.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [dedekindZeta_eq_realDedekindZeta F hs]
    norm_cast
  have ht_log : Tendsto (fun s : ℝ => Real.log ((s - 1) * realDedekindZeta F s))
      (𝓝[>] (1 : ℝ)) (𝓝 (Real.log (NumberField.dedekindZeta_residue F))) :=
    (Real.continuousAt_log hres_pos.ne').tendsto.comp ht_re
  have hev_log : ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ),
      |Real.log ((s - 1) * realDedekindZeta F s) -
        Real.log (NumberField.dedekindZeta_residue F)| ≤ 1 := by
    have := Metric.tendsto_nhds.mp ht_log 1 zero_lt_one
    filter_upwards [this] with s hs
    exact (Real.dist_eq _ _ ▸ hs).le
  refine ⟨C1 + C2 + C3 + |Real.log (NumberField.dedekindZeta_residue F)| + 1, ?_⟩
  filter_upwards [self_mem_nhdsWithin, hev_log] with s hs hlog1
  have hs0 : 0 < s - 1 := sub_pos.mpr hs
  have hZpos : 0 < realDedekindZeta F s := realDedekindZeta_pos F hs
  have hlog_mul : Real.log ((s - 1) * realDedekindZeta F s) =
      Real.log (s - 1) + Real.log (realDedekindZeta F s) :=
    Real.log_mul hs0.ne' hZpos.ne'
  have hdb := hdiff_bound s hs
  rw [hlog_mul] at hlog1
  have hstep1 : |Real.log (realDedekindZeta F s) - (-Real.log (s - 1))| ≤
      |Real.log (NumberField.dedekindZeta_residue F)| + 1 := by
    have heq : Real.log (realDedekindZeta F s) - (-Real.log (s - 1)) =
        (Real.log (s - 1) + Real.log (realDedekindZeta F s) -
          Real.log (NumberField.dedekindZeta_residue F)) +
        Real.log (NumberField.dedekindZeta_residue F) := by ring
    rw [heq]
    linarith [abs_add_le (Real.log (s - 1) + Real.log (realDedekindZeta F s) -
        Real.log (NumberField.dedekindZeta_residue F))
      (Real.log (NumberField.dedekindZeta_residue F))]
  have htri : |(d : ℝ) * (∑' p : {p : ℕ // SplitsCompletely F p}, ((p.1 : ℝ) ^ s)⁻¹) -
      (-Real.log (s - 1))| ≤
      |Real.log (realDedekindZeta F s) -
        (d : ℝ) * (∑' p : {p : ℕ // SplitsCompletely F p}, ((p.1 : ℝ) ^ s)⁻¹)| +
      |Real.log (realDedekindZeta F s) - (-Real.log (s - 1))| := by
    have heq : (d : ℝ) * (∑' p : {p : ℕ // SplitsCompletely F p}, ((p.1 : ℝ) ^ s)⁻¹) -
        (-Real.log (s - 1)) =
        -(Real.log (realDedekindZeta F s) -
          (d : ℝ) * (∑' p : {p : ℕ // SplitsCompletely F p}, ((p.1 : ℝ) ^ s)⁻¹)) +
        (Real.log (realDedekindZeta F s) - (-Real.log (s - 1))) := by ring
    rw [heq]
    have hab := abs_add_le
      (-(Real.log (realDedekindZeta F s) -
        (d : ℝ) * (∑' p : {p : ℕ // SplitsCompletely F p}, ((p.1 : ℝ) ^ s)⁻¹)))
      (Real.log (realDedekindZeta F s) - (-Real.log (s - 1)))
    rw [abs_neg] at hab
    exact hab
  linarith

/- Section 5: Bauer gap theorem -/

private lemma infinite_splitsCompletely_diff
    (K L : Type*) [Field K] [NumberField K] [IsGalois ℚ K]
    [Field L] [NumberField L] [IsGalois ℚ L]
    (hramK : {p : ℕ | p.Prime ∧ Ideal.ramificationIdxIn (Ideal.span {(p : ℤ)}) (𝓞 K) ≠ 1}.Finite)
    (hramL : {p : ℕ | p.Prime ∧ Ideal.ramificationIdxIn (Ideal.span {(p : ℤ)}) (𝓞 L) ≠ 1}.Finite)
    (hlt : Module.finrank ℚ K < Module.finrank ℚ L) :
    {p : ℕ | SplitsCompletely K p ∧ ¬ SplitsCompletely L p}.Infinite := by
  classical
  by_contra hfin
  rw [Set.not_infinite] at hfin
  obtain ⟨CK, hK⟩ := prime_zeta_sum_asymptotic K hramK
  obtain ⟨CL, hL⟩ := prime_zeta_sum_asymptotic L hramL
  have hdK_pos : (0 : ℝ) < (Module.finrank ℚ K : ℝ) :=
    Nat.cast_pos.mpr (Module.finrank_pos (R := ℚ) (M := K))
  have hdL_pos : (0 : ℝ) < (Module.finrank ℚ L : ℝ) :=
    Nat.cast_pos.mpr (Module.finrank_pos (R := ℚ) (M := L))
  have hltR : (Module.finrank ℚ K : ℝ) < (Module.finrank ℚ L : ℝ) :=
    Nat.cast_lt.mpr hlt
  set dK : ℝ := (Module.finrank ℚ K : ℝ)
  set dL : ℝ := (Module.finrank ℚ L : ℝ)
  have hgap : 0 < dK⁻¹ - dL⁻¹ := sub_pos.mpr (inv_strictAnti₀ hdK_pos hltR)
  have ht_inf : Tendsto (fun s : ℝ => -Real.log (s - 1)) (𝓝[>] (1 : ℝ)) atTop := by
    have hsub : Tendsto (fun s : ℝ => s - 1) (𝓝[>] (1 : ℝ)) (𝓝[>] (0 : ℝ)) := by
      have h1 : Tendsto (fun s : ℝ => s - 1) (𝓝[>] (1 : ℝ)) (𝓝 (1 - 1 : ℝ)) :=
        ((continuous_id.sub continuous_const).tendsto 1).mono_left nhdsWithin_le_nhds
      rw [sub_self] at h1
      exact tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ h1
        (eventually_nhdsWithin_of_forall fun s hs => sub_pos.mpr (Set.mem_Ioi.mp hs))
    have hlog := Real.tendsto_log_nhdsGT_zero.comp hsub
    exact tendsto_neg_atBot_atTop.comp hlog
  set B : ℝ := (hfin.toFinset.card : ℝ) + CK / dK + CL / dL + 1
  have hev_big : ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ), B / (dK⁻¹ - dL⁻¹) < -Real.log (s - 1) :=
    ((tendsto_atTop.mp ht_inf) (B / (dK⁻¹ - dL⁻¹) + 1)).mono fun s hs => by linarith
  have hev_gt1 : ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ), (1 : ℝ) < s := self_mem_nhdsWithin
  have hev_all := hK.and (hL.and (hev_gt1.and hev_big))
  obtain ⟨s, hsK, hsL, hs1, hsbig⟩ := hev_all.exists
  have hsum_nat : Summable (fun n : ℕ => ((n : ℝ) ^ s)⁻¹) :=
    Real.summable_nat_rpow_inv.mpr hs1
  have hdiff_le :
      (∑' p : {p : ℕ // SplitsCompletely K p}, ((p.1 : ℝ) ^ s)⁻¹) -
      (∑' p : {p : ℕ // SplitsCompletely L p}, ((p.1 : ℝ) ^ s)⁻¹) ≤
      (hfin.toFinset.card : ℝ) := by
    let indK (n : ℕ) : ℝ := if SplitsCompletely K n then ((n : ℝ) ^ s)⁻¹ else 0
    let indL (n : ℕ) : ℝ := if SplitsCompletely L n then ((n : ℝ) ^ s)⁻¹ else 0
    let indD (n : ℕ) : ℝ := if n ∈ hfin.toFinset then (1 : ℝ) else 0
    have hindK_sum : Summable indK :=
      Summable.of_nonneg_of_le (fun n => by dsimp [indK]; split_ifs <;> positivity)
        (fun n => by
          dsimp [indK]; split_ifs
          · exact le_rfl
          · positivity) hsum_nat
    have hindL_sum : Summable indL :=
      Summable.of_nonneg_of_le (fun n => by dsimp [indL]; split_ifs <;> positivity)
        (fun n => by
          dsimp [indL]; split_ifs
          · exact le_rfl
          · positivity) hsum_nat
    have hindD_sum : Summable indD := by
      apply summable_of_ne_finset_zero (s := hfin.toFinset)
      intro n hn
      exact if_neg hn
    have hpt : ∀ n : ℕ, indK n ≤ indL n + indD n := by
      intro n
      by_cases hKn : SplitsCompletely K n
      · by_cases hLn : SplitsCompletely L n
        · simp only [indK, indL, indD, hKn, hLn, ↓reduceIte]
          have : 0 ≤ (if n ∈ hfin.toFinset then (1 : ℝ) else 0) := by split_ifs <;> positivity
          linarith
        · have hnD : n ∈ hfin.toFinset := hfin.mem_toFinset.mpr ⟨hKn, hLn⟩
          simp only [indK, indL, indD, hKn, hLn, hnD, ↓reduceIte, zero_add]
          have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hKn.1.two_le
          exact inv_le_one_of_one_le₀ (Real.one_le_rpow (by linarith) (by linarith))
      · simp only [indK, hKn, ↓reduceIte]
        have h1 : 0 ≤ indL n := by dsimp [indL]; split_ifs <;> positivity
        have h2 : 0 ≤ indD n := by dsimp [indD]; split_ifs <;> positivity
        linarith
    have hts_le := hindK_sum.tsum_le_tsum hpt (hindL_sum.add hindD_sum)
    rw [hindL_sum.tsum_add hindD_sum] at hts_le
    have hEqK : ∑' n : ℕ, indK n = ∑' p : {p : ℕ // SplitsCompletely K p}, ((p.1 : ℝ) ^ s)⁻¹ := by
      change ∑' n : ℕ, indK n = ∑' p : ↑{p : ℕ | SplitsCompletely K p}, ((p.1 : ℝ) ^ s)⁻¹
      rw [tsum_subtype {p : ℕ | SplitsCompletely K p} (fun n : ℕ => ((n : ℝ) ^ s)⁻¹)]
      apply tsum_congr
      intro n
      simp [indK, Set.indicator]
    have hEqL : ∑' n : ℕ, indL n = ∑' p : {p : ℕ // SplitsCompletely L p}, ((p.1 : ℝ) ^ s)⁻¹ := by
      change ∑' n : ℕ, indL n = ∑' p : ↑{p : ℕ | SplitsCompletely L p}, ((p.1 : ℝ) ^ s)⁻¹
      rw [tsum_subtype {p : ℕ | SplitsCompletely L p} (fun n : ℕ => ((n : ℝ) ^ s)⁻¹)]
      apply tsum_congr
      intro n
      simp [indL, Set.indicator]
    have hEqD : ∑' n : ℕ, indD n = (hfin.toFinset.card : ℝ) := by
      rw [tsum_eq_sum (s := hfin.toFinset) (fun n hn => if_neg hn)]
      simp only [Finset.sum_ite_mem, Finset.inter_self, Finset.sum_const, nsmul_eq_mul, mul_one]
    linarith
  have hK_low : (-Real.log (s - 1) - CK) / dK ≤
      ∑' p : {p : ℕ // SplitsCompletely K p}, ((p.1 : ℝ) ^ s)⁻¹ := by
    rw [div_le_iff₀ hdK_pos]
    linarith [(abs_le.mp hsK).1]
  have hL_high : ∑' p : {p : ℕ // SplitsCompletely L p}, ((p.1 : ℝ) ^ s)⁻¹ ≤
      (-Real.log (s - 1) + CL) / dL := by
    rw [le_div_iff₀ hdL_pos]
    linarith [(abs_le.mp hsL).2]
  have hcomb : (dK⁻¹ - dL⁻¹) * (-Real.log (s - 1)) ≤ (hfin.toFinset.card : ℝ) + CK / dK + CL / dL := by
    have h1 : (-Real.log (s - 1) - CK) / dK - (-Real.log (s - 1) + CL) / dL ≤
        (hfin.toFinset.card : ℝ) := by linarith
    have h2 : (-Real.log (s - 1) - CK) / dK - (-Real.log (s - 1) + CL) / dL =
        (dK⁻¹ - dL⁻¹) * (-Real.log (s - 1)) - CK / dK - CL / dL := by ring
    linarith
  have hbig : B < (dK⁻¹ - dL⁻¹) * (-Real.log (s - 1)) := by
    rwa [div_lt_iff₀ hgap, mul_comm] at hsbig
  linarith

/- Section 6: Kummer splitting fields and unramifiedness via inertia group -/

private def kummerPoly (q : ℕ) (C : Finset ℕ) : ℚ[X] :=
  (X ^ q - 1) * ∏ c ∈ C, (X ^ q - Polynomial.C (c : ℚ))

private lemma kummerPoly_monic (q : ℕ) (hq : 0 < q) (C : Finset ℕ) :
    (kummerPoly q C).Monic := by
  unfold kummerPoly
  apply Polynomial.Monic.mul
  · exact Polynomial.monic_X_pow_sub_C 1 hq.ne'
  · exact Polynomial.monic_prod_of_monic C _ (fun c _ => Polynomial.monic_X_pow_sub_C (c : ℚ) hq.ne')

private lemma kummerPoly_ne_zero (q : ℕ) (hq : 0 < q) (C : Finset ℕ) :
    kummerPoly q C ≠ 0 :=
  (kummerPoly_monic q hq C).ne_zero

private lemma root_of_kummerPoly_pow_eq {q : ℕ} {C : Finset ℕ}
    {F : Type*} [Field F] [Algebra ℚ F] {α : F}
    (hα : Polynomial.aeval α (kummerPoly q C) = 0) :
    α ^ q = 1 ∨ ∃ c ∈ C, α ^ q = (c : F) := by
  simp only [kummerPoly, map_mul, map_sub, map_pow, aeval_X, map_one, map_prod, aeval_C,
    mul_eq_zero, Finset.prod_eq_zero_iff] at hα
  rcases hα with h1 | ⟨c, hc, h2⟩
  · left; exact sub_eq_zero.mp h1
  · right; refine ⟨c, hc, ?_⟩
    have h2' : α ^ q = algebraMap ℚ F (c : ℚ) := sub_eq_zero.mp h2
    simpa using h2'

private lemma integral_of_pow_eq_nat {F : Type*} [Field F] [NumberField F]
    {q c : ℕ} (hq : 0 < q) {α : F} (hα : α ^ q = (c : F)) :
    IsIntegral ℤ α := by
  refine ⟨Polynomial.X ^ q - Polynomial.C (c : ℤ),
    Polynomial.monic_X_pow_sub_C (c : ℤ) hq.ne', ?_⟩
  simp [hα]

private lemma prime_root_of_unity_sub_one_dvd_q {R : Type*} [CommRing R] [IsDomain R]
    {q : ℕ} {z : R} (hzq : z ^ q = 1) (hz1 : z ≠ 1) :
    (z - 1) ∣ (q : R) := by
  have hgeom : (z - 1) * ∑ j ∈ Finset.range q, z ^ j = 0 := by
    have h1 : (z - 1) * ∑ j ∈ Finset.range q, z ^ j = -((∑ j ∈ Finset.range q, z ^ j) * (1 - z)) := by
      ring
    rw [h1, geom_sum_mul_neg, hzq, sub_self, neg_zero]
  have hsum0 : ∑ j ∈ Finset.range q, z ^ j = 0 :=
    (mul_eq_zero.mp hgeom).resolve_left (sub_ne_zero.mpr hz1)
  have hq_eq : (q : R) = ∑ j ∈ Finset.range q, (1 - z ^ j) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
      hsum0, sub_zero]
  rw [hq_eq]
  apply Finset.dvd_sum
  intro j _
  have hfact : 1 - z ^ j = (∑ i ∈ Finset.range j, z ^ i) * (1 - z) :=
    (geom_sum_mul_neg z j).symm
  rw [hfact]
  exact ⟨-(∑ i ∈ Finset.range j, z ^ i), by ring⟩

private lemma finite_residueField_span_prime (p : ℕ) [Fact p.Prime] :
    Finite (Ideal.span {(p : ℤ)}).ResidueField := by
  have : (Ideal.span {(p : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime p
  have : (Ideal.span {(p : ℤ)}).IsPrime := (Int.ideal_span_isMaximal_of_prime p).isPrime
  let _ : Field (ℤ ⧸ Ideal.span {(p : ℤ)}) := Ideal.Quotient.field (Ideal.span {(p : ℤ)})
  have : Finite (ℤ ⧸ Ideal.span {(p : ℤ)}) :=
    Finite.of_equiv (ZMod p) (Int.quotientSpanNatEquivZMod p).symm.toEquiv
  have hsurj : Function.Surjective (algebraMap (ℤ ⧸ Ideal.span {(p : ℤ)}) (Ideal.span {(p : ℤ)}).ResidueField) := by
    intro x
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (ℤ ⧸ Ideal.span {(p : ℤ)}) x
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    refine ⟨a / b, ?_⟩
    rw [map_div₀]
  exact Finite.of_surjective _ hsurj

private lemma kummerSplittingField_unramified
    (q : ℕ) (hq : q.Prime) (C : Finset ℕ) (p : ℕ) [hp : Fact p.Prime]
    (hpq : ¬ p ∣ q) (hpC : ∀ c ∈ C, ¬ p ∣ c) :
    Ideal.ramificationIdxIn (Ideal.span {(p : ℤ)})
      (𝓞 (kummerPoly q C).SplittingField) = 1 := by
  set P := kummerPoly q C
  set F := P.SplittingField
  have : NumberField F := ⟨⟩
  have : Normal ℚ F := Polynomial.SplittingField.instNormal P
  have : IsGalois ℚ F := ⟨⟩
  have : Polynomial.IsSplittingField ℚ F P := Polynomial.IsSplittingField.splittingField P
  have : IsGaloisGroup (F ≃ₐ[ℚ] F) ℤ (𝓞 F) :=
    IsGaloisGroup.of_isFractionRing (F ≃ₐ[ℚ] F) ℤ (𝓞 F) ℚ F
  have : (Ideal.span {(p : ℤ)}).IsPrime := (Int.ideal_span_isMaximal_of_prime p).isPrime
  have : (Ideal.span {(p : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime p
  have : Finite (Ideal.span {(p : ℤ)}).ResidueField := finite_residueField_span_prime p
  have : PerfectField (Ideal.span {(p : ℤ)}).ResidueField := inferInstance
  obtain ⟨⟨Q, hQprime, hQover⟩⟩ :=
    (inferInstance : Nonempty (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 F)))
  have : Q.IsPrime := hQprime
  have : Q.LiesOver (Ideal.span {(p : ℤ)}) := hQover
  rw [← Ideal.card_inertia_eq_ramificationIdxIn (G := F ≃ₐ[ℚ] F) (Ideal.span {(p : ℤ)}) Q]
  have htriv : ∀ σ : Q.inertia (F ≃ₐ[ℚ] F), σ = 1 := by
    rintro ⟨σ, hσ⟩
    apply Subtype.ext
    change σ = 1
    have hadj : Algebra.adjoin ℚ (P.rootSet F) = ⊤ :=
      Polynomial.IsSplittingField.adjoin_rootSet F P
    have hfix : ∀ α ∈ P.rootSet F, σ α = α := by
      intro α hα
      have hroot : Polynomial.aeval α P = 0 := by
        rwa [Polynomial.mem_rootSet_of_ne (kummerPoly_ne_zero q hq.pos C)] at hα
      have hpow : ∃ c : ℕ, ¬ p ∣ c ∧ α ^ q = (c : F) := by
        rcases root_of_kummerPoly_pow_eq hroot with h1 | ⟨c, hc, h2⟩
        · exact ⟨1, fun h => hp.out.not_dvd_one h, by simpa using h1⟩
        · exact ⟨c, hpC c hc, h2⟩
      obtain ⟨c, hpc, hαq⟩ := hpow
      have hint : IsIntegral ℤ α := integral_of_pow_eq_nat hq.pos hαq
      let a : 𝓞 F := ⟨α, hint⟩
      have haq : a ^ q = (c : 𝓞 F) := by
        apply Subtype.ext
        change α ^ q = (c : F)
        exact hαq
      by_contra hne
      have hα0 : α ≠ 0 := by
        intro h0
        rw [h0, zero_pow hq.ne_zero] at hαq
        have hc0 : c = 0 := by exact_mod_cast hαq.symm
        exact hpc (hc0 ▸ dvd_zero p)
      let zF : F := σ α / α
      have hzFq : zF ^ q = 1 := by
        rw [div_pow, ← map_pow, hαq, map_natCast, div_self]
        exact Nat.cast_ne_zero.mpr (fun hc0 => hpc (hc0 ▸ dvd_zero p))
      have hzF1 : zF ≠ 1 := by
        intro h1
        exact hne (by rwa [div_eq_one_iff_eq hα0] at h1)
      have hzint : IsIntegral ℤ zF :=
        integral_of_pow_eq_nat (c := 1) hq.pos (by rw [Nat.cast_one]; exact hzFq)
      let z : 𝓞 F := ⟨zF, hzint⟩
      have hzq : z ^ q = 1 := by apply Subtype.ext; change zF ^ q = 1; exact hzFq
      have hz1 : z ≠ 1 := fun h => hzF1 (congrArg Subtype.val h)
      have hσa_eq : σ • a = z * a := by
        apply Subtype.ext
        exact (div_mul_cancel₀ (σ α) hα0).symm
      have hmem : σ • a - a ∈ Q := hσ a
      rw [hσa_eq] at hmem
      have hprod_mem : (z - 1) * a ∈ Q := by
        convert hmem using 1; ring
      rcases hQprime.mem_or_mem hprod_mem with hzQ | haQ
      · have hqQ : (q : 𝓞 F) ∈ Q := by
          obtain ⟨t, ht⟩ := prime_root_of_unity_sub_one_dvd_q hzq hz1
          rw [ht]
          exact Q.mul_mem_right t hzQ
        have hq_under : (q : ℤ) ∈ Q.under ℤ := by
          rw [Ideal.mem_under]; simpa using hqQ
        rw [← hQover.over, Ideal.mem_span_singleton] at hq_under
        exact hpq (Int.natCast_dvd_natCast.mp hq_under)
      · have hcQ : (c : 𝓞 F) ∈ Q := by
          rw [← haq]
          exact Q.pow_mem_of_mem haQ q hq.pos
        have hc_under : (c : ℤ) ∈ Q.under ℤ := by
          rw [Ideal.mem_under]; simpa using hcQ
        rw [← hQover.over, Ideal.mem_span_singleton] at hc_under
        exact hpc (Int.natCast_dvd_natCast.mp hc_under)
    apply AlgEquiv.ext
    intro x
    have hx : x ∈ Algebra.adjoin ℚ (P.rootSet F) := by rw [hadj]; trivial
    have heq : (σ : F →ₐ[ℚ] F) x = (AlgHom.id ℚ F) x := by
      refine Algebra.adjoin_induction (p := fun y _ => σ y = y) ?_ ?_ ?_ ?_ hx
      · exact fun y hy => hfix y hy
      · exact fun r => σ.commutes r
      · intro u v _ _ hu hv; rw [map_add, hu, hv]
      · intro u v _ _ hu hv; rw [map_mul, hu, hv]
    simpa using heq
  have : Unique (Q.inertia (F ≃ₐ[ℚ] F)) :=
    { default := 1, uniq := htriv }
  exact Nat.card_unique

private lemma kummerSplittingField_finite_ramified
    (q : ℕ) (hq : q.Prime) (C : Finset ℕ) (hCpos : ∀ c ∈ C, 0 < c) :
    {p : ℕ | p.Prime ∧ Ideal.ramificationIdxIn (Ideal.span {(p : ℤ)})
      (𝓞 (kummerPoly q C).SplittingField) ≠ 1}.Finite := by
  let B : ℕ := max q (C.sup id)
  apply (Set.finite_le_nat B).subset
  rintro p ⟨hp, hram⟩
  have : Fact p.Prime := ⟨hp⟩
  change p ≤ B
  by_contra hgt
  have hgt' : B < p := lt_of_not_ge hgt
  have hpq : ¬ p ∣ q := fun h => by
    have := Nat.le_of_dvd hq.pos h
    have : q ≤ B := le_max_left _ _
    omega
  have hpC : ∀ c ∈ C, ¬ p ∣ c := fun c hc h => by
    have h1 := Nat.le_of_dvd (hCpos c hc) h
    have h2 : c ≤ C.sup id := Finset.le_sup (f := id) hc
    have h3 : C.sup id ≤ B := le_max_right _ _
    omega
  exact hram (kummerSplittingField_unramified q hq C p hpq hpC)

/- Section 7: Degree separation finrank ℚ K < finrank ℚ L -/

private lemma exists_root_X_pow_sub_C_of_splits {L : Type*} [Field L] [Algebra ℚ L]
    {q c : ℕ} (hq : 0 < q) (hsplits : ((X ^ q - Polynomial.C (c : ℚ)).map (algebraMap ℚ L)).Splits) :
    ∃ α : L, α ^ q = (c : L) := by
  have hmon : (X ^ q - Polynomial.C (c : ℚ)).Monic :=
    Polynomial.monic_X_pow_sub_C (c : ℚ) hq.ne'
  have hmonL : ((X ^ q - Polynomial.C (c : ℚ)).map (algebraMap ℚ L)).Monic :=
    hmon.map (algebraMap ℚ L)
  have hcard : ((X ^ q - Polynomial.C (c : ℚ)).map (algebraMap ℚ L)).roots.card = q := by
    rw [hsplits.natDegree_eq_card_roots.symm,
      Polynomial.natDegree_map_eq_of_injective (algebraMap ℚ L).injective,
      Polynomial.natDegree_X_pow_sub_C]
  obtain ⟨α, hα⟩ := Multiset.card_pos_iff_exists_mem.mp (by rw [hcard]; exact hq)
  have hroot := (Polynomial.mem_roots hmonL.ne_zero).mp hα
  refine ⟨α, ?_⟩
  simp only [Polynomial.IsRoot, Polynomial.eval_map, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow,
    Polynomial.eval₂_C, sub_eq_zero] at hroot
  simpa using hroot

private lemma finrank_kummer_lt (q : ℕ) (hq : q.Prime) (hq2 : 2 < q) (M : ℕ) :
    let CK : Finset ℕ := (Finset.Icc 3 M).filter Nat.Prime
    let CL : Finset ℕ := insert 2 CK
    Module.finrank ℚ (kummerPoly q CK).SplittingField <
      Module.finrank ℚ (kummerPoly q CL).SplittingField := by
  intro CK CL
  set PK := kummerPoly q CK
  set PL := kummerPoly q CL
  set K := PK.SplittingField
  set L := PL.SplittingField
  have : NumberField K := ⟨⟩
  have : NumberField L := ⟨⟩
  have : Polynomial.IsSplittingField ℚ K PK := Polynomial.IsSplittingField.splittingField PK
  have h2not : 2 ∉ CK := by simp [CK]
  have hPL_eq : PL = PK * (X ^ q - Polynomial.C (2 : ℚ)) := by
    simp only [PL, PK, kummerPoly, CL, Finset.prod_insert h2not]
    push_cast
    ring
  have hPL_splits : (PL.map (algebraMap ℚ L)).Splits := Polynomial.SplittingField.splits PL
  have hPL_map_ne : PL.map (algebraMap ℚ L) ≠ 0 :=
    ((kummerPoly_monic q hq.pos CL).map (algebraMap ℚ L)).ne_zero
  have hdvd_PK : PK ∣ PL := by rw [hPL_eq]; exact dvd_mul_right _ _
  have hdvd_X2 : (X ^ q - Polynomial.C (2 : ℚ)) ∣ PL := by rw [hPL_eq]; exact dvd_mul_left _ _
  have hPK_splits_L : (PK.map (algebraMap ℚ L)).Splits :=
    hPL_splits.of_dvd hPL_map_ne (Polynomial.map_dvd (algebraMap ℚ L) hdvd_PK)
  let ι : K →ₐ[ℚ] L := Polynomial.IsSplittingField.lift K PK hPK_splits_L
  have hle : Module.finrank ℚ K ≤ Module.finrank ℚ L :=
    LinearMap.finrank_le_finrank_of_injective (f := ι.toLinearMap) ι.injective
  refine lt_of_le_of_ne hle ?_
  intro heq
  have hsurj : Function.Surjective ι :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := ι.toLinearMap) heq).mp ι.injective
  have hX2_splits : ((X ^ q - Polynomial.C (2 : ℚ)).map (algebraMap ℚ L)).Splits :=
    hPL_splits.of_dvd hPL_map_ne (Polynomial.map_dvd (algebraMap ℚ L) hdvd_X2)
  obtain ⟨αL, hαL⟩ := exists_root_X_pow_sub_C_of_splits hq.pos hX2_splits
  obtain ⟨αK, hαK_eq⟩ := hsurj αL
  have hαKq : αK ^ q = (2 : K) := by
    apply ι.injective
    calc ι (αK ^ q) = (ι αK) ^ q := map_pow ι αK q
      _ = αL ^ q := by rw [hαK_eq]
      _ = ((2 : ℕ) : L) := hαL
      _ = ι (2 : K) := by rw [map_ofNat, Nat.cast_ofNat]
  have hint : IsIntegral ℤ αK :=
    integral_of_pow_eq_nat (c := 2) hq.pos (by rw [Nat.cast_ofNat]; exact hαKq)
  let a : 𝓞 K := ⟨αK, hint⟩
  have haq : a ^ q = (2 : 𝓞 K) := by
    apply Subtype.ext; change αK ^ q = (2 : K); exact hαKq
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2q : ¬ 2 ∣ q := by
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).mp h
    omega
  have h2CK : ∀ c ∈ CK, ¬ 2 ∣ c := by
    intro c hc h
    simp only [CK, Finset.mem_filter, Finset.mem_Icc] at hc
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hc.2).mp h
    omega
  have hunram : Ideal.ramificationIdxIn (Ideal.span {(2 : ℤ)}) (𝓞 K) = 1 :=
    kummerSplittingField_unramified q hq CK 2 h2q h2CK
  have : (Ideal.span {(2 : ℤ)}).IsPrime := (Int.ideal_span_isMaximal_of_prime 2).isPrime
  obtain ⟨⟨P, hPprime, hPover⟩⟩ :=
    (inferInstance : Nonempty (Ideal.primesOver (Ideal.span {(2 : ℤ)}) (𝓞 K)))
  have : P.IsPrime := hPprime
  have : P.LiesOver (Ideal.span {(2 : ℤ)}) := hPover
  have : Normal ℚ K := Polynomial.SplittingField.instNormal PK
  have : IsGalois ℚ K := ⟨⟩
  have : IsGaloisGroup (K ≃ₐ[ℚ] K) ℤ (𝓞 K) :=
    IsGaloisGroup.of_isFractionRing (K ≃ₐ[ℚ] K) ℤ (𝓞 K) ℚ K
  have he1 : Ideal.ramificationIdx P ℤ = 1 := by
    rw [← Ideal.ramificationIdxIn_eq_ramificationIdx (Ideal.span {(2 : ℤ)}) P (K ≃ₐ[ℚ] K), hunram]
  have h2mem : (2 : 𝓞 K) ∈ P := by
    have h2u : (2 : ℤ) ∈ P.under ℤ := by
      rw [← hPover.over]; exact Ideal.subset_span rfl
    simpa [Ideal.mem_under] using h2u
  have ha_mem : a ∈ P := by
    rw [← haq] at h2mem
    exact hPprime.mem_of_pow_mem q h2mem
  have hPdvd : P ^ q ∣ Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {(2 : ℤ)}) := by
    rw [Ideal.map_span, Set.image_singleton, map_ofNat]
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem, ← haq]
    exact Ideal.pow_mem_pow ha_mem q
  have hmap_ne : Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {(2 : ℤ)}) ≠ ⊥ := by
    rw [Ideal.map_span, Set.image_singleton, map_ofNat]
    simp
  have hq_le_e : q ≤ Ideal.ramificationIdx P ℤ := by
    rw [Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count (Ideal.span {(2 : ℤ)}) P hmap_ne]
    obtain ⟨J, hJ⟩ := hPdvd
    have hPq_ne : P ^ q ≠ ⊥ := pow_ne_zero q (prime_ideal_ne_bot_of_liesOver_natPrime Nat.prime_two hPover)
    have hJ_ne : J ≠ ⊥ := fun h0 => hmap_ne (by rw [hJ, h0, Ideal.mul_bot])
    rw [hJ, UniqueFactorizationMonoid.normalizedFactors_mul hPq_ne hJ_ne, Multiset.count_add,
      UniqueFactorizationMonoid.normalizedFactors_pow, Multiset.count_nsmul]
    have hPprime' : Prime P := Ideal.prime_of_isPrime
      (prime_ideal_ne_bot_of_liesOver_natPrime Nat.prime_two hPover) hPprime
    have hnf : UniqueFactorizationMonoid.normalizedFactors P = {P} := by
      simpa using UniqueFactorizationMonoid.normalizedFactors_irreducible hPprime'.irreducible
    rw [hnf, Multiset.count_singleton_self, mul_one]
    omega
  omega

/- Section 8: Denominator clearing and translating SplitsCompletely to power residues -/

private lemma exists_denom_clearing_roots (q : ℕ) (hq : q.Prime) (C : Finset ℕ) :
    let F := (kummerPoly q C).SplittingField
    ∃ N₀ : ℕ, 0 < N₀ ∧
      ∀ y : 𝓞 F, ((N₀ : 𝓞 F) * y) ∈
        Algebra.adjoin ℤ {a : 𝓞 F | Polynomial.aeval (a : F) (kummerPoly q C) = 0} := by
  classical
  set P := kummerPoly q C
  set F := P.SplittingField
  have : NumberField F := ⟨⟩
  have : Polynomial.IsSplittingField ℚ F P := Polynomial.IsSplittingField.splittingField P
  let S : Set (𝓞 F) := {a : 𝓞 F | Polynomial.aeval (a : F) P = 0}
  let R : Subalgebra ℤ (𝓞 F) := Algebra.adjoin ℤ S
  have hclear_elem : ∀ x : F, ∃ d : ℕ, 0 < d ∧ ∃ r : 𝓞 F, r ∈ R ∧ (r : F) = (d : F) * x := by
    intro x
    have hx : x ∈ Algebra.adjoin ℚ (P.rootSet F) := by
      rw [Polynomial.IsSplittingField.adjoin_rootSet F P]; trivial
    refine Algebra.adjoin_induction
      (p := fun y _ => ∃ d : ℕ, 0 < d ∧ ∃ r : 𝓞 F, r ∈ R ∧ (r : F) = (d : F) * y)
      ?_ ?_ ?_ ?_ hx
    · intro y hy
      have hroot : Polynomial.aeval y P = 0 := by
        rwa [Polynomial.mem_rootSet_of_ne (kummerPoly_ne_zero q hq.pos C)] at hy
      have hint : IsIntegral ℤ y := by
        rcases root_of_kummerPoly_pow_eq hroot with h1 | ⟨c, _, h2⟩
        · exact integral_of_pow_eq_nat (c := 1) hq.pos (by rw [Nat.cast_one]; exact h1)
        · exact integral_of_pow_eq_nat hq.pos h2
      let a : 𝓞 F := ⟨y, hint⟩
      refine ⟨1, Nat.one_pos, a, Algebra.subset_adjoin hroot, ?_⟩
      change y = ((1 : ℕ) : F) * y
      simp
    · intro qval
      refine ⟨qval.den, qval.pos, (qval.num : 𝓞 F), R.intCast_mem qval.num, ?_⟩
      have hqeq : (qval.num : ℚ) = (qval.den : ℚ) * qval := by
        rw [mul_comm, Rat.mul_den_eq_num]
      have hqF : algebraMap ℚ F (qval.num : ℚ) = algebraMap ℚ F ((qval.den : ℚ) * qval) :=
        congrArg (algebraMap ℚ F) hqeq
      rw [map_mul, map_intCast, map_natCast] at hqF
      simpa using hqF
    · rintro u v _ _ ⟨d₁, hd₁, r₁, hr₁, h₁⟩ ⟨d₂, hd₂, r₂, hr₂, h₂⟩
      refine ⟨d₁ * d₂, Nat.mul_pos hd₁ hd₂, (d₂ : 𝓞 F) * r₁ + (d₁ : 𝓞 F) * r₂,
        R.add_mem (R.mul_mem (R.natCast_mem d₂) hr₁) (R.mul_mem (R.natCast_mem d₁) hr₂), ?_⟩
      change algebraMap (𝓞 F) F ((d₂ : 𝓞 F) * r₁ + (d₁ : 𝓞 F) * r₂) = (d₁ * d₂ : ℕ) * (u + v)
      rw [map_add, map_mul, map_mul, map_natCast, map_natCast, Nat.cast_mul]
      change (d₂ : F) * (r₁ : F) + (d₁ : F) * (r₂ : F) = (d₁ : F) * (d₂ : F) * (u + v)
      rw [h₁, h₂]
      ring
    · rintro u v _ _ ⟨d₁, hd₁, r₁, hr₁, h₁⟩ ⟨d₂, hd₂, r₂, hr₂, h₂⟩
      refine ⟨d₁ * d₂, Nat.mul_pos hd₁ hd₂, r₁ * r₂, R.mul_mem hr₁ hr₂, ?_⟩
      change algebraMap (𝓞 F) F (r₁ * r₂) = (d₁ * d₂ : ℕ) * (u * v)
      rw [map_mul, Nat.cast_mul]
      change (r₁ : F) * (r₂ : F) = (d₁ : F) * (d₂ : F) * (u * v)
      rw [h₁, h₂]
      ring
  let b := NumberField.RingOfIntegers.basis F
  choose d hd_pos r hr_mem hr_eq using fun i => hclear_elem (b i : F)
  let N₀ : ℕ := ∏ i, d i
  have hN₀_pos : 0 < N₀ := Finset.prod_pos (fun i _ => hd_pos i)
  refine ⟨N₀, hN₀_pos, fun y => ?_⟩
  have hy : y = ∑ i, (b.repr y i) • b i := (b.sum_repr y).symm
  rw [hy, Finset.mul_sum]
  apply R.sum_mem
  intro i _
  have hdvd : d i ∣ N₀ := Finset.dvd_prod_of_mem d (Finset.mem_univ i)
  obtain ⟨k, hk⟩ := hdvd
  have hmul : (N₀ : 𝓞 F) * ((b.repr y i) • b i) = ((b.repr y i : 𝓞 F) * (k : 𝓞 F)) * r i := by
    apply Subtype.ext
    change algebraMap (𝓞 F) F ((N₀ : 𝓞 F) * ((b.repr y i) • b i)) =
      algebraMap (𝓞 F) F (((b.repr y i : 𝓞 F) * (k : 𝓞 F)) * r i)
    rw [map_mul, map_natCast, map_zsmul, map_mul, map_mul, map_intCast, map_natCast, zsmul_eq_mul]
    change (N₀ : F) * ((b.repr y i : F) * (b i : F)) =
      ((b.repr y i : F) * (k : F)) * (r i : F)
    rw [hr_eq i, hk, Nat.cast_mul]
    ring
  rw [hmul]
  exact R.mul_mem (R.mul_mem (R.intCast_mem _) (R.natCast_mem _)) (hr_mem i)

private lemma exists_nontrivial_qth_root_in_splitting (q : ℕ) (hq : q.Prime) (C : Finset ℕ) :
    ∃ ζ : 𝓞 (kummerPoly q C).SplittingField, ζ ^ q = 1 ∧ ζ ≠ 1 := by
  classical
  set P := kummerPoly q C
  set F := P.SplittingField
  have : NumberField F := ⟨⟩
  have hP_splits : (P.map (algebraMap ℚ F)).Splits := Polynomial.SplittingField.splits P
  have hP_map_ne : P.map (algebraMap ℚ F) ≠ 0 :=
    ((kummerPoly_monic q hq.pos C).map (algebraMap ℚ F)).ne_zero
  have hsplits : ((X ^ q - (1 : ℚ[X])).map (algebraMap ℚ F)).Splits := by
    apply hP_splits.of_dvd hP_map_ne
    unfold P kummerPoly
    rw [Polynomial.map_mul]
    exact dvd_mul_right _ _
  have hsep : (X ^ q - (1 : ℚ[X])).Separable := by
    simpa using Polynomial.separable_X_pow_sub_C (1 : ℚ) (by exact_mod_cast hq.ne_zero) one_ne_zero
  have hsepF : ((X ^ q - (1 : ℚ[X])).map (algebraMap ℚ F)).Separable := hsep.map
  have hnodup : ((X ^ q - (1 : ℚ[X])).map (algebraMap ℚ F)).roots.Nodup :=
    Polynomial.nodup_roots hsepF
  have hcard : ((X ^ q - (1 : ℚ[X])).map (algebraMap ℚ F)).roots.card = q := by
    rw [hsplits.natDegree_eq_card_roots.symm,
      Polynomial.natDegree_map_eq_of_injective (algebraMap ℚ F).injective]
    simpa using (Polynomial.natDegree_X_pow_sub_C (n := q) (r := (1 : ℚ)))
  have hex : ∃ z ∈ ((X ^ q - (1 : ℚ[X])).map (algebraMap ℚ F)).roots, z ≠ 1 := by
    by_contra hall
    push Not at hall
    have hle : ((X ^ q - (1 : ℚ[X])).map (algebraMap ℚ F)).roots.card ≤ 1 := by
      rw [← Multiset.toFinset_card_of_nodup hnodup]
      have hsub : ((X ^ q - (1 : ℚ[X])).map (algebraMap ℚ F)).roots.toFinset ⊆ {1} := by
        intro z hz
        simp [hall z (Multiset.mem_toFinset.mp hz)]
      exact (Finset.card_le_card hsub).trans (by simp)
    have := hq.two_le
    omega
  obtain ⟨z, hz_mem, hz1⟩ := hex
  have hzq : z ^ q = 1 := by
    have hne : ((X ^ q - (1 : ℚ[X])).map (algebraMap ℚ F)) ≠ 0 := by
      have hmon : (X ^ q - (1 : ℚ[X])).Monic := by
        simpa using Polynomial.monic_X_pow_sub_C (1 : ℚ) hq.ne_zero
      exact (hmon.map (algebraMap ℚ F)).ne_zero
    have hev := (Polynomial.mem_roots hne).mp hz_mem
    simp only [Polynomial.IsRoot, Polynomial.eval_map, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow,
      Polynomial.eval₂_one, sub_eq_zero] at hev
    exact hev
  have hint : IsIntegral ℤ z :=
    integral_of_pow_eq_nat (c := 1) hq.pos (by rw [Nat.cast_one]; exact hzq)
  refine ⟨⟨z, hint⟩, ?_, ?_⟩
  · apply Subtype.ext; change z ^ q = 1; exact hzq
  · intro h; exact hz1 (congrArg Subtype.val h)

private def zmodToQuotRingHom {F : Type*} [Field F] [NumberField F]
    (p : ℕ) (P : Ideal (𝓞 F)) [hPover : P.LiesOver (Ideal.span {(p : ℤ)})] :
    ZMod p →+* 𝓞 F ⧸ P :=
  (Ideal.Quotient.lift (Ideal.span {(p : ℤ)}) (Int.castRingHom (𝓞 F ⧸ P)) fun a ha => by
    have haP : (a : 𝓞 F) ∈ P := by
      have hau : a ∈ P.under ℤ := by rwa [← hPover.over]
      simpa [Ideal.mem_under] using hau
    change Ideal.Quotient.mk P (a : 𝓞 F) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr haP).comp
    (Int.quotientSpanNatEquivZMod p).symm.toRingHom

private lemma zmodToQuotRingHom_intCast {F : Type*} [Field F] [NumberField F]
    (p : ℕ) (P : Ideal (𝓞 F)) [P.LiesOver (Ideal.span {(p : ℤ)})] (k : ℤ) :
    zmodToQuotRingHom p P (k : ZMod p) = Ideal.Quotient.mk P (k : 𝓞 F) := by
  rw [map_intCast, map_intCast]

private lemma zmodToQuotRingHom_natCast {F : Type*} [Field F] [NumberField F]
    (p : ℕ) (P : Ideal (𝓞 F)) [P.LiesOver (Ideal.span {(p : ℤ)})] (k : ℕ) :
    zmodToQuotRingHom p P (k : ZMod p) = Ideal.Quotient.mk P (k : 𝓞 F) := by
  rw [map_natCast, map_natCast]

private lemma quot_iso_zmod_of_splitsCompletely
    (F : Type*) [Field F] [NumberField F] [IsGalois ℚ F]
    (p : ℕ) (hp : SplitsCompletely F p)
    (P : Ideal (𝓞 F)) [hPprime : P.IsPrime] [hPover : P.LiesOver (Ideal.span {(p : ℤ)})] :
    ∃ φ : ZMod p ≃+* 𝓞 F ⧸ P,
      ∀ k : ℕ, φ (k : ZMod p) = Ideal.Quotient.mk P (k : 𝓞 F) := by
  have : Fact p.Prime := ⟨hp.1⟩
  have : (Ideal.span {(p : ℤ)}).IsPrime := (Int.ideal_span_isMaximal_of_prime p).isPrime
  have : P.IsMaximal := hPprime.isMaximal (prime_ideal_ne_bot_of_liesOver_natPrime hp.1 hPover)
  let _ : Field (𝓞 F ⧸ P) := Ideal.Quotient.field P
  have hfund := galois_fundamental_identity F p
  rw [hp.2] at hfund
  have hd_pos : 0 < Module.finrank ℚ F := Module.finrank_pos
  have hf1 : Ideal.inertiaDegIn (Ideal.span {(p : ℤ)}) (𝓞 F) = 1 :=
    Nat.eq_one_of_mul_eq_one_left (by nlinarith :
      Ideal.ramificationIdxIn _ _ * Ideal.inertiaDegIn _ _ = 1)
  have hfP : P.inertiaDeg ℤ = 1 := by
    rw [inertiaDeg_eq_inertiaDegIn_galois F p P, hf1]
  have hcardQ : Nat.card (𝓞 F ⧸ P) = p := by
    have h1 := Ideal.pow_inertiaDeg p P
    rw [hfP, pow_one, Ideal.absNorm_apply, Submodule.cardQuot] at h1
    exact h1.symm
  let ψ : ZMod p →+* 𝓞 F ⧸ P := zmodToQuotRingHom p P
  have hψ_nat : ∀ k : ℕ, ψ (k : ZMod p) = Ideal.Quotient.mk P (k : 𝓞 F) :=
    zmodToQuotRingHom_natCast p P
  have hψ_inj : Function.Injective ψ := ψ.injective
  have : Finite (𝓞 F ⧸ P) := Nat.finite_of_card_ne_zero (by rw [hcardQ]; exact hp.1.ne_zero)
  let _ := Fintype.ofFinite (𝓞 F ⧸ P)
  have hψ_bij : Function.Bijective ψ :=
    (Fintype.bijective_iff_injective_and_card ψ).mpr ⟨hψ_inj, by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcardQ, Nat.card_zmod]⟩
  exact ⟨RingEquiv.ofBijective ψ hψ_bij, hψ_nat⟩

private lemma root_pow_in_range_of_field_hom
    {p q : ℕ} [Fact p.Prime] (hq : q.Prime)
    {E : Type*} [Field E] (ψ : ZMod p →+* E)
    {z₀ x : ZMod p} (hz₀q : z₀ ^ q = 1) (hz₀1 : z₀ ≠ 1) (hxne : x ≠ 0)
    {w : E} (hw : w ^ q = ψ (x ^ q)) :
    w ∈ Set.range ψ := by
  classical
  let f : E[X] := Polynomial.X ^ q - Polynomial.C (ψ (x ^ q))
  have hf_ne : f ≠ 0 := (Polynomial.monic_X_pow_sub_C _ hq.ne_zero).ne_zero
  let g : Fin q → E := fun j => ψ (z₀ ^ (j : ℕ) * x)
  have hz₀_ne : z₀ ≠ 0 := by
    intro h0
    rw [h0, zero_pow hq.ne_zero] at hz₀q
    exact zero_ne_one hz₀q
  have hpow_ne_one : ∀ d : ℕ, 0 < d → d < q → z₀ ^ d ≠ 1 := by
    intro d hd0 hdq hzd
    have : Fact q.Prime := ⟨hq⟩
    have : Fact (1 < q) := ⟨hq.one_lt⟩
    have hd_ne : (d : ZMod q) ≠ 0 := by
      intro h0
      have hdvd : q ∣ d := (ZMod.natCast_eq_zero_iff d q).mp h0
      exact Nat.not_dvd_of_pos_of_lt hd0 hdq hdvd
    let k : ℕ := ((d : ZMod q)⁻¹).val
    have hk : (d * k) % q = 1 := by
      have h1 : ((d * k : ℕ) : ZMod q) = 1 := by
        rw [Nat.cast_mul, ZMod.natCast_zmod_val, mul_inv_cancel₀ hd_ne]
      have h2 : ((d * k : ℕ) : ZMod q).val = (1 : ZMod q).val := congrArg ZMod.val h1
      rw [ZMod.val_natCast, ZMod.val_one] at h2
      exact h2
    have hdiv : d * k = q * (d * k / q) + 1 := by
      have := Nat.div_add_mod (d * k) q
      omega
    have hz1 : z₀ = 1 := by
      calc z₀ = z₀ ^ 1 := (pow_one z₀).symm
        _ = (z₀ ^ q) ^ (d * k / q) * z₀ ^ 1 := by rw [hz₀q, one_pow, one_mul]
        _ = z₀ ^ (q * (d * k / q) + 1) := by rw [pow_add, pow_mul]
        _ = z₀ ^ (d * k) := by rw [← hdiv]
        _ = (z₀ ^ d) ^ k := pow_mul z₀ d k
        _ = 1 := by rw [hzd, one_pow]
    exact hz₀1 hz1
  have hg_inj : Function.Injective g := by
    intro i j hij
    have h1 : z₀ ^ (i : ℕ) * x = z₀ ^ (j : ℕ) * x := ψ.injective hij
    have h2 : z₀ ^ (i : ℕ) = z₀ ^ (j : ℕ) := mul_right_cancel₀ hxne h1
    rcases lt_trichotomy (i : ℕ) (j : ℕ) with hlt | heq | hgt
    · exfalso
      have hdiff : z₀ ^ ((j : ℕ) - (i : ℕ)) = 1 := by
        apply mul_left_cancel₀ (pow_ne_zero (i : ℕ) hz₀_ne)
        rw [← pow_add, Nat.add_sub_cancel' hlt.le, mul_one, h2]
      exact hpow_ne_one ((j : ℕ) - (i : ℕ)) (by omega) (by omega) hdiff
    · exact Fin.ext heq
    · exfalso
      have hdiff : z₀ ^ ((i : ℕ) - (j : ℕ)) = 1 := by
        apply mul_left_cancel₀ (pow_ne_zero (j : ℕ) hz₀_ne)
        rw [← pow_add, Nat.add_sub_cancel' hgt.le, mul_one, h2.symm]
      exact hpow_ne_one ((i : ℕ) - (j : ℕ)) (by omega) (by omega) hdiff
  have hg_root : ∀ j : Fin q, f.IsRoot (g j) := by
    intro j
    simp only [f, g, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero]
    rw [← map_pow, mul_pow, ← pow_mul, mul_comm (j : ℕ) q, pow_mul, hz₀q, one_pow, one_mul]
  let Rfin : Finset E := Finset.univ.image g
  have hRcard : Rfin.card = q := by
    rw [Finset.card_image_of_injective _ hg_inj, Finset.card_fin]
  have hRsub : Rfin ⊆ f.roots.toFinset := by
    intro u hu
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hu
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hf_ne).mpr (hg_root j))
  have hroot_w : w ∈ f.roots.toFinset := by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hf_ne]
    simp only [f, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero]
    exact hw
  have hcard_roots : f.roots.toFinset.card ≤ q := by
    calc f.roots.toFinset.card ≤ f.roots.card := Multiset.toFinset_card_le _
      _ ≤ f.natDegree := Polynomial.card_roots' f
      _ = q := Polynomial.natDegree_X_pow_sub_C
  have hReq : Rfin = f.roots.toFinset :=
    Finset.eq_of_subset_of_card_le hRsub (by omega)
  rw [← hReq] at hroot_w
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hroot_w
  exact ⟨z₀ ^ (j : ℕ) * x, hj⟩

end

end Erdos436H1

theorem OMA.solution : OMA.R_Erdos436_erdos_436_variants_ge_four_R2.H1 := by
  classical
  intro q hq hq2 M
  let CK : Finset ℕ := (Finset.Icc 3 M).filter Nat.Prime
  let CL : Finset ℕ := insert 2 CK
  set PK := Erdos436H1.kummerPoly q CK
  set PL := Erdos436H1.kummerPoly q CL
  set K := PK.SplittingField
  set L := PL.SplittingField
  have : NumberField K := ⟨⟩
  have : NumberField L := ⟨⟩
  have : Normal ℚ K := Polynomial.SplittingField.instNormal PK
  have : Normal ℚ L := Polynomial.SplittingField.instNormal PL
  have : IsGalois ℚ K := ⟨⟩
  have : IsGalois ℚ L := ⟨⟩
  have hCK_pos : ∀ c ∈ CK, 0 < c := fun c hc => (Finset.mem_filter.mp hc).2.pos
  have hCL_pos : ∀ c ∈ CL, 0 < c := by
    intro c hc
    rcases Finset.mem_insert.mp hc with rfl | hc'
    · norm_num
    · exact hCK_pos c hc'
  have hramK := Erdos436H1.kummerSplittingField_finite_ramified q hq CK hCK_pos
  have hramL := Erdos436H1.kummerSplittingField_finite_ramified q hq CL hCL_pos
  have hlt := Erdos436H1.finrank_kummer_lt q hq hq2 M
  have hinf := Erdos436H1.infinite_splitsCompletely_diff K L hramK hramL hlt
  obtain ⟨N₀, hN₀_pos, hN₀⟩ := Erdos436H1.exists_denom_clearing_roots q hq CL
  let B : ℕ := max (max (max M q) 2) N₀
  have hinf_big : ({p : ℕ | Erdos436H1.SplitsCompletely K p ∧
      ¬ Erdos436H1.SplitsCompletely L p} \ {p : ℕ | p ≤ B}).Infinite :=
    hinf.sdiff (Set.finite_le_nat B)
  refine hinf_big.mono ?_
  rintro p ⟨⟨hpK, hpnotL⟩, hpbig⟩
  simp only [Set.mem_ofPred_eq, not_le] at hpbig
  have hp : p.Prime := hpK.1
  have : Fact p.Prime := ⟨hp⟩
  have hp_gt_M : M < p := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _))) hpbig
  have hp_gt_q : q < p := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))) hpbig
  have hp_gt_2 : 2 < p := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hpbig
  have hp_gt_N₀ : N₀ < p := lt_of_le_of_lt (le_max_right _ _) hpbig
  have : (Ideal.span {(p : ℤ)}).IsPrime := (Int.ideal_span_isMaximal_of_prime p).isPrime
  obtain ⟨⟨P, hPprime, hPover⟩⟩ :=
    (inferInstance : Nonempty (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 K)))
  have : P.IsPrime := hPprime
  have : P.LiesOver (Ideal.span {(p : ℤ)}) := hPover
  obtain ⟨φ, hφ_nat⟩ := Erdos436H1.quot_iso_zmod_of_splitsCompletely K p hpK P
  have hres_CK : ∀ r : ℕ, r.Prime → 2 < r → r ≤ M → Erdos436.IsPowerResidue q p r := by
    intro r hr hr2 hrM
    have hrCK : r ∈ CK := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hrM⟩, hr⟩
    have hr_ne : (r : ZMod p) ≠ 0 := by
      intro h0
      have hdvd : p ∣ r := (ZMod.natCast_eq_zero_iff r p).mp h0
      have := Nat.le_of_dvd hr.pos hdvd
      omega
    have hPK_splits : (PK.map (algebraMap ℚ K)).Splits := Polynomial.SplittingField.splits PK
    have hPK_map_ne : PK.map (algebraMap ℚ K) ≠ 0 :=
      ((Erdos436H1.kummerPoly_monic q hq.pos CK).map (algebraMap ℚ K)).ne_zero
    have hfac : (Polynomial.X ^ q - Polynomial.C (r : ℚ)) ∣ PK :=
      dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ hrCK) _
    have hsplits : ((Polynomial.X ^ q - Polynomial.C (r : ℚ)).map (algebraMap ℚ K)).Splits :=
      hPK_splits.of_dvd hPK_map_ne (Polynomial.map_dvd (algebraMap ℚ K) hfac)
    obtain ⟨β, hβq⟩ := Erdos436H1.exists_root_X_pow_sub_C_of_splits hq.pos hsplits
    let b : 𝓞 K := ⟨β, Erdos436H1.integral_of_pow_eq_nat hq.pos hβq⟩
    have hbq : b ^ q = (r : 𝓞 K) := by apply Subtype.ext; change β ^ q = (r : K); exact hβq
    refine ⟨hr_ne, φ.symm (Ideal.Quotient.mk P b), ?_⟩
    apply φ.injective
    rw [map_pow, φ.apply_symm_apply, hφ_nat r, ← map_pow, hbq]
  refine ⟨hp, ?_, hres_CK⟩
  intro h2res
  obtain ⟨ζ, hζq, hζ1⟩ := Erdos436H1.exists_nontrivial_qth_root_in_splitting q hq CK
  let z₀ : ZMod p := φ.symm (Ideal.Quotient.mk P ζ)
  have hz₀q : z₀ ^ q = 1 := by
    apply φ.injective
    rw [map_pow, φ.apply_symm_apply, map_one, ← map_pow, hζq, map_one]
  have hz₀1 : z₀ ≠ 1 := by
    intro h1
    have hmem : ζ - 1 ∈ P := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, sub_eq_zero]
      have := congrArg φ h1
      simpa [z₀] using this
    obtain ⟨t, ht⟩ := Erdos436H1.prime_root_of_unity_sub_one_dvd_q hζq hζ1
    have hqP : (q : 𝓞 K) ∈ P := by rw [ht]; exact P.mul_mem_right t hmem
    have hqu : (q : ℤ) ∈ P.under ℤ := by rw [Ideal.mem_under]; simpa using hqP
    rw [← hPover.over, Ideal.mem_span_singleton] at hqu
    have hdvd : p ∣ q := Int.natCast_dvd_natCast.mp hqu
    have := Nat.le_of_dvd hq.pos hdvd
    omega
  have hroot_zmod : ∀ c : ℕ, c = 1 ∨ c ∈ CL →
      ∃ x : ZMod p, x ≠ 0 ∧ x ^ q = (c : ZMod p) := by
    intro c hc
    rcases hc with rfl | hcCL
    · exact ⟨1, one_ne_zero, by simp⟩
    · rcases Finset.mem_insert.mp hcCL with rfl | hcCK
      · obtain ⟨h2ne, x, hx⟩ := h2res
        refine ⟨x, ?_, hx⟩
        intro hx0; rw [hx0, zero_pow hq.ne_zero] at hx; exact h2ne hx.symm
      · have hc' := Finset.mem_filter.mp hcCK
        have hcIcc := Finset.mem_Icc.mp hc'.1
        obtain ⟨hne, x, hx⟩ := hres_CK c hc'.2 (by omega) hcIcc.2
        refine ⟨x, ?_, hx⟩
        intro hx0; rw [hx0, zero_pow hq.ne_zero] at hx; exact hne hx.symm
  obtain ⟨⟨Q, hQprime, hQover⟩⟩ :=
    (inferInstance : Nonempty (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 L)))
  have : Q.IsPrime := hQprime
  have : Q.LiesOver (Ideal.span {(p : ℤ)}) := hQover
  have : Q.IsMaximal := hQprime.isMaximal (Erdos436H1.prime_ideal_ne_bot_of_liesOver_natPrime hp hQover)
  let _ : Field (𝓞 L ⧸ Q) := Ideal.Quotient.field Q
  let ψ : ZMod p →+* 𝓞 L ⧸ Q := Erdos436H1.zmodToQuotRingHom p Q
  have hψ_nat : ∀ k : ℕ, ψ (k : ZMod p) = Ideal.Quotient.mk Q (k : 𝓞 L) :=
    Erdos436H1.zmodToQuotRingHom_natCast p Q
  have hψ_int : ∀ k : ℤ, ψ (k : ZMod p) = Ideal.Quotient.mk Q (k : 𝓞 L) :=
    Erdos436H1.zmodToQuotRingHom_intCast p Q
  have hroots_in_range : ∀ a : 𝓞 L, Polynomial.aeval (a : L) PL = 0 →
      Ideal.Quotient.mk Q a ∈ Set.range ψ := by
    intro a ha
    have hc : ∃ c : ℕ, (c = 1 ∨ c ∈ CL) ∧ a ^ q = (c : 𝓞 L) := by
      rcases Erdos436H1.root_of_kummerPoly_pow_eq ha with h1 | ⟨c, hc, h2⟩
      · exact ⟨1, Or.inl rfl, by apply Subtype.ext; change (a : L) ^ q = 1; exact h1⟩
      · exact ⟨c, Or.inr hc, by apply Subtype.ext; change (a : L) ^ q = (c : L); exact h2⟩
    obtain ⟨c, hc, haq⟩ := hc
    obtain ⟨x, hxne, hxq⟩ := hroot_zmod c hc
    refine Erdos436H1.root_pow_in_range_of_field_hom hq ψ hz₀q hz₀1 hxne ?_
    rw [← map_pow, haq, hxq, hψ_nat c]
  have hψ_surj : Function.Surjective ψ := by
    intro w
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective w
    have hmem : (N₀ : 𝓞 L) * y ∈ Algebra.adjoin ℤ {a : 𝓞 L | Polynomial.aeval (a : L) PL = 0} :=
      hN₀ y
    have hNy_in : Ideal.Quotient.mk Q ((N₀ : 𝓞 L) * y) ∈ Set.range ψ := by
      refine Algebra.adjoin_induction
        (p := fun z _ => Ideal.Quotient.mk Q z ∈ Set.range ψ) ?_ ?_ ?_ ?_ hmem
      · exact fun a ha => hroots_in_range a ha
      · intro k; exact ⟨(k : ZMod p), hψ_int k⟩
      · rintro u v _ _ ⟨ru, hru⟩ ⟨rv, hrv⟩
        exact ⟨ru + rv, by rw [map_add, hru, hrv, map_add]⟩
      · rintro u v _ _ ⟨ru, hru⟩ ⟨rv, hrv⟩
        exact ⟨ru * rv, by rw [map_mul, hru, hrv, map_mul]⟩
    obtain ⟨r, hr⟩ := hNy_in
    have hN₀_ne : (N₀ : ZMod p) ≠ 0 := by
      intro h0
      have hdvd : p ∣ N₀ := (ZMod.natCast_eq_zero_iff N₀ p).mp h0
      have := Nat.le_of_dvd hN₀_pos hdvd
      omega
    refine ⟨(N₀ : ZMod p)⁻¹ * r, ?_⟩
    have hmul : ψ (N₀ : ZMod p) * Ideal.Quotient.mk Q y = ψ r := by
      rw [hψ_nat N₀, ← map_mul]; exact hr.symm
    have hψN₀ : ψ (N₀ : ZMod p) ≠ 0 := fun h0 => hN₀_ne (ψ.injective (by simpa using h0))
    rw [map_mul, map_inv₀, ← hmul, ← mul_assoc, inv_mul_cancel₀ hψN₀, one_mul]
  have hcardQ : Nat.card (𝓞 L ⧸ Q) = p := by
    have hbij : Function.Bijective ψ := ⟨ψ.injective, hψ_surj⟩
    rw [← Nat.card_congr (Equiv.ofBijective ψ hbij), Nat.card_zmod]
  have hfQ : Q.inertiaDeg ℤ = 1 := by
    have h1 := Ideal.pow_inertiaDeg p Q
    rw [Ideal.absNorm_apply, Submodule.cardQuot] at h1
    change p ^ Q.inertiaDeg ℤ = Nat.card (𝓞 L ⧸ Q) at h1
    rw [hcardQ] at h1
    have h2 : p ^ Q.inertiaDeg ℤ = p ^ 1 := by simpa using h1
    exact Nat.pow_right_injective hp.two_le h2
  have hpq : ¬ p ∣ q := fun h => by have := Nat.le_of_dvd hq.pos h; omega
  have hpCL : ∀ c ∈ CL, ¬ p ∣ c := by
    intro c hc h
    have hc_le : c ≤ max M 2 := by
      rcases Finset.mem_insert.mp hc with rfl | hcCK
      · exact le_max_right _ _
      · exact le_trans (Finset.mem_Icc.mp (Finset.mem_filter.mp hcCK).1).2 (le_max_left _ _)
    have := Nat.le_of_dvd (hCL_pos c hc) h
    omega
  have heL : Ideal.ramificationIdxIn (Ideal.span {(p : ℤ)}) (𝓞 L) = 1 :=
    Erdos436H1.kummerSplittingField_unramified q hq CL p hpq hpCL
  have hfL : Ideal.inertiaDegIn (Ideal.span {(p : ℤ)}) (𝓞 L) = 1 := by
    rw [← Erdos436H1.inertiaDeg_eq_inertiaDegIn_galois L p Q, hfQ]
  have hfundL := Erdos436H1.galois_fundamental_identity L p
  rw [heL, hfL, mul_one, mul_one] at hfundL
  exact hpnotL ⟨hp, hfundL⟩
