import OMAReductions.R_SmallCohenMacaulayModules_exists_isBalancedBigCohenMacaulay_R1
import Mathlib

/-!
# Equal-Characteristic Balanced Big Cohen-Macaulay Modules: Complete Local Domain Reduction

We reduce `OMA.R_SmallCohenMacaulayModules_exists_isBalancedBigCohenMacaulay_R1.H1` (Hochster 1975,
equal-characteristic balanced big Cohen-Macaulay modules for Noetherian local domains of dimension
at least 2) to two strictly stronger theorems on **complete** Noetherian local domains:

1. `H1`: Equal characteristic `p > 0` (`p.Prime`, `CharP B p`) for complete Noetherian local
   domains `B : Type` of Krull dimension at least 2 (Hochster 1975, Theorem 4.2 / Frobenius).
2. `H2`: Equal characteristic `0` (`CharZero B`, `CharZero (ResidueField B)`) for complete
   Noetherian local domains `B : Type` of Krull dimension at least 2 (Hochster 1975, Theorem 5.1 /
   Artin approximation and reduction to positive characteristic).

In `main`, we prove completely from scratch in Lean 4:
- Noetherianity of the `I`-adic completion `AdicCompletion I R` of any Noetherian ring `R` via a
  surjective ring homomorphism from `MvPowerSeries s R` constructed by telescoping homogeneous
  lifts of Cauchy approximations.
- Preservation of Krull dimension under completion `ringKrullDim (AdicCompletion m A) = ringKrullDim A`,
  combining Going Down for the flat local map `A ->+* AdicCompletion m A` with Krull's height
  theorem on a system of parameters.
- Passage to a full-dimensional minimal prime quotient `B = AdicCompletion m A / P`, proving that
  `B` is a complete Noetherian local domain of the same Krull dimension via exactness of adic
  completion and Hausdorffness.
- Equal-characteristic dichotomy (`p.Prime` with `CharP B p` vs `CharZero B` and
  `CharZero (ResidueField B)` via injectivity of the induced map on residue fields).
- Pullback of balanced big Cohen-Macaulay modules along SOP-preserving local ring homomorphisms.
-/

namespace OMA.R_SmallCohenMacaulayModules_exists_isBalancedBigCohenMacaulay_R1_H1_R1

open IsLocalRing Module
open scoped Pointwise

/-- Equal-characteristic `p > 0` existence of balanced big Cohen-Macaulay modules for complete
Noetherian local domains of Krull dimension at least 2 (Hochster 1975, Theorem 4.2). -/
def H1 : Prop :=
  ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [IsLocalRing B] [IsDomain B]
    [IsAdicComplete (maximalIdeal B) B] (p : ℕ),
    p.Prime → CharP B p → (2 : WithBot ℕ∞) ≤ ringKrullDim B →
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module B W), IsBalancedBigCohenMacaulay B W

/-- Equal-characteristic `0` existence of balanced big Cohen-Macaulay modules for complete
Noetherian local domains of Krull dimension at least 2 (Hochster 1975, Theorem 5.1). -/
def H2 : Prop :=
  ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [IsLocalRing B] [IsDomain B]
    [IsAdicComplete (maximalIdeal B) B],
    CharZero B → CharZero (ResidueField B) → (2 : WithBot ℕ∞) ≤ ringKrullDim B →
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module B W), IsBalancedBigCohenMacaulay B W

section Helpers

/- Section 1: Noetherianity of adic completion via surjection from MvPowerSeries -/

private lemma exists_homogeneous_aeval {R : Type*} [CommRing R]
    (s : Finset R) {I : Ideal R} (hI : Ideal.span (s : Set R) = I) :
    ∀ (n : ℕ) {a : R}, a ∈ I ^ n →
      ∃ P : MvPolynomial s R,
        (∀ m : s →₀ ℕ, MvPolynomial.coeff m P ≠ 0 → Finsupp.degree m = n) ∧
        MvPolynomial.aeval (Subtype.val : s → R) P = a := by
  classical
  intro n
  induction n with
  | zero =>
    intro a _
    refine ⟨MvPolynomial.C a, ?_, by simp⟩
    intro m hm
    have hm0 : m = 0 := by
      by_contra hne
      apply hm
      rw [MvPolynomial.coeff_C, if_neg (Ne.symm hne)]
    subst hm0
    simp
  | succ n ih =>
    intro a ha
    rw [pow_succ] at ha
    let S : Submodule R R :=
      { carrier := {x : R | ∃ P : MvPolynomial s R,
          (∀ m : s →₀ ℕ, MvPolynomial.coeff m P ≠ 0 → Finsupp.degree m = n + 1) ∧
          MvPolynomial.aeval (Subtype.val : s → R) P = x}
        add_mem' := by
          rintro x y ⟨Px, hPx, rfl⟩ ⟨Py, hPy, rfl⟩
          refine ⟨Px + Py, ?_, map_add _ _ _⟩
          intro m hm
          rw [MvPolynomial.coeff_add] at hm
          by_cases hx : MvPolynomial.coeff m Px = 0
          · rw [hx, zero_add] at hm
            exact hPy m hm
          · exact hPx m hx
        zero_mem' := ⟨0, fun m hm => absurd (by simp) hm, map_zero _⟩
        smul_mem' := by
          rintro r x ⟨Px, hPx, rfl⟩
          refine ⟨MvPolynomial.C r * Px, ?_, by simp [smul_eq_mul]⟩
          intro m hm
          rw [MvPolynomial.coeff_C_mul] at hm
          exact hPx m (right_ne_zero_of_mul hm) }
    change a ∈ S
    refine Submodule.mul_induction_on ha ?_ (fun _ _ hx hy => S.add_mem hx hy)
    intro x hx y hy
    obtain ⟨Px, hPx, rfl⟩ := ih hx
    rw [← hI] at hy
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
    · intro b hb
      refine ⟨Px * MvPolynomial.X ⟨b, hb⟩, ?_, by simp⟩
      intro m hm
      rw [MvPolynomial.coeff_mul_X'] at hm
      split_ifs at hm with hle
      · have hdeg := hPx (m - Finsupp.single ⟨b, hb⟩ 1) hm
        have hle' : Finsupp.single ⟨b, hb⟩ 1 ≤ m :=
          Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hle))
        have hadd : (m - Finsupp.single ⟨b, hb⟩ 1) + Finsupp.single ⟨b, hb⟩ 1 = m :=
          tsub_add_cancel_of_le hle'
        rw [← hadd, map_add, hdeg, Finsupp.degree_single]
      · exact absurd rfl hm
    · rw [mul_zero]; exact S.zero_mem
    · intro u v _ _ hu hv; rw [mul_add]; exact S.add_mem hu hv
    · intro r u _ hu; rw [smul_eq_mul, mul_left_comm]; exact S.smul_mem r hu

private lemma isNoetherianRing_adicCompletion (R : Type*) [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) : IsNoetherianRing (AdicCompletion I R) := by
  classical
  obtain ⟨s, hs⟩ := IsNoetherian.noetherian I
  let e : MvPolynomial s R →ₐ[R] R := MvPolynomial.aeval (Subtype.val : s → R)
  have hJ_le : MvPolynomial.idealOfVars s R ≤ I.comap e.toRingHom := by
    rw [MvPolynomial.idealOfVars, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    change e (MvPolynomial.X i) ∈ I
    rw [← hs]
    exact Ideal.subset_span (by simp [e])
  have hJ_pow : ∀ n : ℕ, MvPolynomial.idealOfVars s R ^ n ≤ (I ^ n).comap e.toRingHom := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, pow_succ, ← Ideal.map_le_iff_le_comap, Ideal.map_mul]
      exact Ideal.mul_mono (Ideal.map_le_iff_le_comap.mpr ih) (Ideal.map_le_iff_le_comap.mpr hJ_le)
  let q : ∀ n : ℕ, MvPolynomial s R ⧸ MvPolynomial.idealOfVars s R ^ n →+* R ⧸ I ^ n :=
    fun n => Ideal.quotientMap (I ^ n) e.toRingHom (hJ_pow n)
  let f : ∀ n : ℕ, MvPowerSeries s R →+* R ⧸ I ^ n :=
    fun n => (q n).comp (MvPowerSeries.truncTotalAlgHom s R n).toRingHom
  have hf : ∀ {m n : ℕ} (hle : m ≤ n), (Ideal.Quotient.factorPow I hle).comp (f n) = f m := by
    intro m n hle
    ext p
    change Ideal.Quotient.mk (I ^ m) (e (p.truncTotal n)) =
      Ideal.Quotient.mk (I ^ m) (e (p.truncTotal m))
    rw [Ideal.Quotient.eq, ← map_sub]
    exact hJ_pow m (MvPowerSeries.truncTotal_sub_truncTotal_mem_pow_idealOfVars hle le_rfl p)
  let Φ : MvPowerSeries s R →+* AdicCompletion I R := AdicCompletion.liftRingHom I f hf
  have hΦ_surj : Function.Surjective Φ := by
    intro x
    let y : ℕ → R := fun k => match k with
      | 0 => 0
      | k + 1 => Quotient.out (AdicCompletion.evalₐ I (k + 1) x)
    have hy_mk : ∀ k : ℕ, Ideal.Quotient.mk (I ^ k) (y k) = AdicCompletion.evalₐ I k x := by
      intro k
      cases k with
      | zero =>
        have hsub : Subsingleton (R ⧸ I ^ 0) :=
          Ideal.Quotient.subsingleton_iff.mpr (by simp)
        exact Subsingleton.elim _ _
      | succ k =>
        exact Quotient.out_eq (AdicCompletion.evalₐ I (k + 1) x)
    have hy_diff : ∀ k : ℕ, y (k + 1) - y k ∈ I ^ k := by
      intro k
      rw [← Ideal.Quotient.eq, hy_mk k]
      have hcompat :
          Ideal.Quotient.factorPow I (Nat.le_succ k) (AdicCompletion.evalₐ I (k + 1) x) =
            AdicCompletion.evalₐ I k x := by
        obtain ⟨r, hr⟩ := Submodule.Quotient.mk_surjective _ (x.val (k + 1))
        have hr' : x.val k = Submodule.Quotient.mk r := by
          rw [← x.property (Nat.le_succ k), ← hr]
          rfl
        have h1 : AdicCompletion.evalₐ I (k + 1) x = Ideal.Quotient.mk (I ^ (k + 1)) r := by
          rw [← AdicCompletion.factor_eval_eq_evalₐ I x (le_of_eq (Ideal.mul_top _))]
          change Ideal.Quotient.factor (le_of_eq (Ideal.mul_top _)) (x.val (k + 1)) = _
          rw [← hr]
          rfl
        have h2 : AdicCompletion.evalₐ I k x = Ideal.Quotient.mk (I ^ k) r := by
          rw [← AdicCompletion.factor_eval_eq_evalₐ I x (le_of_eq (Ideal.mul_top _))]
          change Ideal.Quotient.factor (le_of_eq (Ideal.mul_top _)) (x.val k) = _
          rw [hr']
          rfl
        rw [h1, h2]
        rfl
      rw [← hcompat, ← hy_mk (k + 1)]
      rfl
    have hP_ex : ∀ k : ℕ, ∃ P : MvPolynomial s R,
        (∀ m : s →₀ ℕ, MvPolynomial.coeff m P ≠ 0 → Finsupp.degree m = k) ∧
        e P = y (k + 1) - y k :=
      fun k => exists_homogeneous_aeval s hs k (hy_diff k)
    let P : ℕ → MvPolynomial s R := fun k => (hP_ex k).choose
    have hP_deg : ∀ (k : ℕ) (m : s →₀ ℕ), MvPolynomial.coeff m (P k) ≠ 0 → Finsupp.degree m = k :=
      fun k => (hP_ex k).choose_spec.1
    have hP_eval : ∀ k : ℕ, e (P k) = y (k + 1) - y k :=
      fun k => (hP_ex k).choose_spec.2
    let p : MvPowerSeries s R := fun m => MvPolynomial.coeff m (P (Finsupp.degree m))
    refine ⟨p, AdicCompletion.ext_evalₐ fun n => ?_⟩
    rw [AdicCompletion.evalₐ_liftRingHom]
    change Ideal.Quotient.mk (I ^ n) (e (p.truncTotal n)) = AdicCompletion.evalₐ I n x
    have htrunc : p.truncTotal n = ∑ k ∈ Finset.range n, P k := by
      ext m
      rw [MvPolynomial.coeff_sum]
      by_cases hm : Finsupp.degree m < n
      · rw [MvPowerSeries.coeff_truncTotal p hm]
        rw [Finset.sum_eq_single (Finsupp.degree m)]
        · rfl
        · intro k _ hk
          by_contra hne
          exact hk (hP_deg k m hne).symm
        · intro hnot
          exact absurd (Finset.mem_range.mpr hm) hnot
      · have hzero : MvPolynomial.coeff m (p.truncTotal n) = 0 :=
          MvPowerSeries.coeff_truncTotal_eq_zero p (not_lt.mp hm)
        rw [hzero]
        symm
        refine Finset.sum_eq_zero fun k hk => ?_
        by_contra hne
        have hdeg := hP_deg k m hne
        exact hm (hdeg ▸ Finset.mem_range.mp hk)
    rw [htrunc, map_sum]
    have htel : ∑ k ∈ Finset.range n, e (P k) = y n := by
      have hsum : ∑ k ∈ Finset.range n, e (P k) = ∑ k ∈ Finset.range n, (y (k + 1) - y k) :=
        Finset.sum_congr rfl fun k _ => hP_eval k
      rw [hsum, Finset.sum_range_sub y n]
      simp [y]
    rw [htel, hy_mk n]
  exact isNoetherianRing_of_surjective (MvPowerSeries s R) (AdicCompletion I R) Φ hΦ_surj

/- Section 2: Krull dimension preservation under completion and minimal prime quotient -/

private lemma ringKrullDim_eq_nat_of_local_noetherian
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    ∃ d : ℕ, ringKrullDim R = (d : WithBot ℕ∞) := by
  have hnbot : ringKrullDim R ≠ ⊥ := ringKrullDim_ne_bot
  have hntop : ringKrullDim R ≠ ⊤ := ringKrullDim_ne_top
  cases h : ringKrullDim R with
  | bot => exact absurd h hnbot
  | coe x =>
    cases x with
    | top => exact absurd h hntop
    | coe d => exact ⟨d, rfl⟩

private lemma exists_ltSeries_of_krullDim_eq_nat
    {α : Type*} [Preorder α] {n : ℕ} (h : Order.krullDim α = (n : WithBot ℕ∞)) :
    ∃ l : LTSeries α, l.length = n := by
  have hne : Nonempty α := by
    by_contra hmt
    rw [not_nonempty_iff] at hmt
    rw [Order.krullDim_eq_bot] at h
    exact WithBot.bot_ne_coe h
  rw [Order.krullDim_eq_iSup_length] at h
  have h' : (⨆ l : LTSeries α, (l.length : ℕ∞)) = (n : ℕ∞) := WithBot.coe_injective h
  by_contra hno
  have hle : ∀ l : LTSeries α, l.length < n := by
    intro l
    have h1 : (l.length : ℕ∞) ≤ (n : ℕ∞) :=
      h' ▸ le_iSup (fun p : LTSeries α => (p.length : ℕ∞)) l
    have h2 : l.length ≤ n := Nat.cast_le.mp h1
    exact lt_of_le_of_ne h2 (fun heq => hno ⟨l, heq⟩)
  cases n with
  | zero =>
    obtain ⟨a⟩ := hne
    exact Nat.not_lt_zero _ (hle (RelSeries.singleton _ a))
  | succ m =>
    have hsup : (⨆ l : LTSeries α, (l.length : ℕ∞)) ≤ (m : ℕ∞) :=
      iSup_le fun l => Nat.cast_le.mpr (Nat.lt_succ_iff.mp (hle l))
    rw [h'] at hsup
    exact Nat.not_succ_le_self m (Nat.cast_le.mp hsup)

private lemma ringKrullDim_adicCompletion_eq (A : Type*) [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] :
    ringKrullDim (AdicCompletion (maximalIdeal A) A) = ringKrullDim A := by
  classical
  let Â := AdicCompletion (maximalIdeal A) A
  have : IsNoetherianRing Â := isNoetherianRing_adicCompletion A (maximalIdeal A)
  have : Algebra.HasGoingDown A Â := Algebra.HasGoingDown.of_flat
  let ι : A →+* Â := algebraMap A Â
  obtain ⟨d, hd⟩ := ringKrullDim_eq_nat_of_local_noetherian A
  apply le_antisymm
  · rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := Â),
      ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := A)]
    apply WithBot.coe_le_coe.mpr
    obtain ⟨s, hs_min, hs_card⟩ :=
      Ideal.exists_finset_card_eq_height_of_isNoetherianRing (maximalIdeal A)
    have hrad : (Ideal.span (s : Set A)).radical = maximalIdeal A := by
      apply le_antisymm
      · exact (Ideal.radical_mono hs_min.1.2).trans (IsLocalRing.maximalIdeal.isMaximal A).isPrime.radical.le
      · rw [Ideal.radical_eq_sInf]
        refine le_sInf fun P hP => ?_
        have : P.IsPrime := hP.2
        obtain ⟨Q, hQmin, hQP⟩ := Ideal.exists_minimalPrimes_le hP.1
        have hQmax : Q ≤ maximalIdeal A := IsLocalRing.le_maximalIdeal hQmin.1.1.ne_top
        have hQeq : Q = maximalIdeal A := by
          have := hs_min.2 ⟨hQmin.1.1, hQmin.1.2⟩ hQmax
          exact le_antisymm hQmax this
        exact hQeq ▸ hQP
    let s' : Finset Â := s.image ι
    have hrad' : (Ideal.span (s' : Set Â)).radical = maximalIdeal Â := by
      have hmap_span : Ideal.span (s' : Set Â) = (Ideal.span (s : Set A)).map ι := by
        rw [Ideal.map_span, Finset.coe_image]
      apply le_antisymm
      · rw [hmap_span]
        have hle : (Ideal.span (s : Set A)).map ι ≤ maximalIdeal Â := by
          rw [AdicCompletion.maximalIdeal_eq_map]
          exact Ideal.map_mono hs_min.1.2
        exact (Ideal.radical_mono hle).trans (IsLocalRing.maximalIdeal.isMaximal Â).isPrime.radical.le
      · rw [AdicCompletion.maximalIdeal_eq_map, Ideal.map_le_iff_le_comap]
        intro a ha
        rw [← hrad, Ideal.mem_radical_iff] at ha
        obtain ⟨n, hn⟩ := ha
        rw [Ideal.mem_comap, Ideal.mem_radical_iff, hmap_span]
        refine ⟨n, ?_⟩
        rw [← map_pow]
        exact Ideal.mem_map_of_mem ι hn
    have hmin' : maximalIdeal Â ∈ (Ideal.span (s' : Set Â)).minimalPrimes := by
      refine ⟨⟨(IsLocalRing.maximalIdeal.isMaximal Â).isPrime, ?_⟩, ?_⟩
      · exact hrad' ▸ Ideal.le_radical
      · intro Q hQ _
        have hQrad : (Ideal.span (s' : Set Â)).radical ≤ Q :=
          hQ.1.radical_le_iff.mpr hQ.2
        exact hrad' ▸ hQrad
    calc (maximalIdeal Â).height
        ≤ s'.card := Ideal.height_le_card_of_mem_minimalPrimes_span_finset hmin'
      _ ≤ s.card := Nat.cast_le.mpr Finset.card_image_le
      _ = (maximalIdeal A).height := hs_card
  · rw [hd]
    obtain ⟨l, hl⟩ := exists_ltSeries_of_krullDim_eq_nat hd
    have hlast : (l (Fin.last l.length)).asIdeal = maximalIdeal A := by
      have hle : (l (Fin.last l.length)).asIdeal ≤ maximalIdeal A :=
        IsLocalRing.le_maximalIdeal (l (Fin.last l.length)).isPrime.ne_top
      by_contra hne
      have hlt : (l (Fin.last l.length)) <
          ⟨maximalIdeal A, (IsLocalRing.maximalIdeal.isMaximal A).isPrime⟩ :=
        lt_of_le_of_ne hle (fun h => hne (congrArg PrimeSpectrum.asIdeal h))
      let l' : LTSeries (PrimeSpectrum A) :=
        l.snoc ⟨maximalIdeal A, (IsLocalRing.maximalIdeal.isMaximal A).isPrime⟩ hlt
      have hlen : (l'.length : WithBot ℕ∞) ≤ ringKrullDim A := by
        rw [ringKrullDim, Order.krullDim_eq_iSup_length]
        exact WithBot.coe_le_coe.mpr (le_iSup (fun p : LTSeries (PrimeSpectrum A) => (p.length : ℕ∞)) l')
      rw [hd] at hlen
      have hnat : l'.length ≤ d := Nat.cast_le.mp (WithBot.coe_le_coe.mp hlen)
      have hlen_eq : l'.length = l.length + 1 := RelSeries.snoc_length l _ hlt
      omega
    have hlift : ∀ (k : ℕ) (hk : k ≤ l.length),
        ∃ f : (i : Fin (k + 1)) → PrimeSpectrum Â,
          (∀ i : Fin k, f i.castSucc < f i.succ) ∧
          ∀ i : Fin (k + 1), (f i).asIdeal.comap ι =
            (l ⟨l.length - k + i.1, by have := i.2; omega⟩).asIdeal := by
      intro k hk
      induction k with
      | zero =>
        refine ⟨fun _ => ⟨maximalIdeal Â, (IsLocalRing.maximalIdeal.isMaximal Â).isPrime⟩,
          fun i => Fin.elim0 i, ?_⟩
        intro i
        have hidx : (⟨l.length - 0 + i.1, by have := i.2; omega⟩ : Fin (l.length + 1)) =
            Fin.last l.length := by
          ext; simp
        rw [hidx, hlast]
        exact IsLocalRing.maximalIdeal_comap ι
      | succ k ih =>
        obtain ⟨f, hstrict, hover⟩ := ih (Nat.le_of_succ_le hk)
        let Q0 : Ideal Â := (f 0).asIdeal
        have : Q0.IsPrime := (f 0).isPrime
        have hQ0_under : Q0.under A = (l ⟨l.length - k, by omega⟩).asIdeal := hover 0
        have hlt_p : (l ⟨l.length - (k + 1), by omega⟩).asIdeal < Q0.under A := by
          rw [hQ0_under]
          exact l.strictMono (show (⟨l.length - (k + 1), by omega⟩ : Fin (l.length + 1)) <
            ⟨l.length - k, by omega⟩ by simp [Fin.lt_def]; omega)
        obtain ⟨Qprev, hQprev_le, hQprev_prime, hQprev_over⟩ :=
          Algebra.HasGoingDown.exists_ideal_le_liesOver_of_lt
            (p := (l ⟨l.length - (k + 1), by omega⟩).asIdeal) (Q := Q0) hlt_p
        have hQprev_lt : Qprev < Q0 := by
          refine lt_of_le_of_ne hQprev_le fun heq => ne_of_lt hlt_p ?_
          have h1 : Qprev.comap ι = (l ⟨l.length - (k + 1), by omega⟩).asIdeal :=
            hQprev_over.over.symm
          change (l ⟨l.length - (k + 1), by omega⟩).asIdeal = Q0.comap ι
          rw [← h1, heq]
        refine ⟨Fin.cons ⟨Qprev, hQprev_prime⟩ f, ?_, ?_⟩
        · intro i
          refine Fin.cases ?_ ?_ i
          · exact hQprev_lt
          · intro j
            exact hstrict j
        · intro i
          refine Fin.cases ?_ ?_ i
          · exact hQprev_over.over.symm
          · intro j
            have hidx : (⟨l.length - (k + 1) + j.succ.1, by have := j.2; omega⟩ :
                Fin (l.length + 1)) = ⟨l.length - k + j.1, by have := j.2; omega⟩ := by
              ext; simp; omega
            rw [Fin.cons_succ, hover j, hidx]
    obtain ⟨f, hstrict, _⟩ := hlift l.length le_rfl
    let l' : LTSeries (PrimeSpectrum Â) :=
      { length := l.length
        toFun := f
        step := hstrict }
    rw [ringKrullDim, Order.krullDim_eq_iSup_length]
    apply WithBot.coe_le_coe.mpr
    calc (d : ℕ∞) = (l'.length : ℕ∞) := by simp [l', hl]
      _ ≤ ⨆ p : LTSeries (PrimeSpectrum Â), (p.length : ℕ∞) :=
          le_iSup (fun p : LTSeries (PrimeSpectrum Â) => (p.length : ℕ∞)) l'

private lemma exists_prime_quotient_same_dim
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    ∃ (P : Ideal R) (_ : P.IsPrime), ringKrullDim (R ⧸ P) = ringKrullDim R := by
  obtain ⟨d, hd⟩ := ringKrullDim_eq_nat_of_local_noetherian R
  obtain ⟨l, hl⟩ := exists_ltSeries_of_krullDim_eq_nat hd
  let P : Ideal R := (l 0).asIdeal
  have hP : P.IsPrime := (l 0).isPrime
  refine ⟨P, hP, le_antisymm (ringKrullDim_quotient_le P) ?_⟩
  let q : R →+* R ⧸ P := Ideal.Quotient.mk P
  have hker : RingHom.ker q = P := Ideal.mk_ker
  have hge : ∀ i : Fin (l.length + 1), P ≤ (l i).asIdeal := fun i =>
    l.monotone (Fin.zero_le i)
  let lQ : LTSeries (PrimeSpectrum (R ⧸ P)) :=
    { length := l.length
      toFun := fun i =>
        ⟨(l i).asIdeal.map q,
          Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [hker]; exact hge i)⟩
      step := fun i => by
        change (l i.castSucc).asIdeal.map q < (l i.succ).asIdeal.map q
        have hlt : (l i.castSucc).asIdeal < (l i.succ).asIdeal := l.step i
        refine lt_of_le_of_ne (Ideal.map_mono (le_of_lt hlt)) fun heq => ne_of_lt hlt ?_
        have h1 : ((l i.castSucc).asIdeal.map q).comap q = (l i.castSucc).asIdeal := by
          rw [Ideal.comap_map_of_surjective q Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
            hker, sup_eq_left.mpr (hge i.castSucc)]
        have h2 : ((l i.succ).asIdeal.map q).comap q = (l i.succ).asIdeal := by
          rw [Ideal.comap_map_of_surjective q Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
            hker, sup_eq_left.mpr (hge i.succ)]
        rw [← h1, ← h2, heq] }
  rw [hd, ringKrullDim, Order.krullDim_eq_iSup_length]
  apply WithBot.coe_le_coe.mpr
  calc (d : ℕ∞) = (lQ.length : ℕ∞) := by simp [lQ, hl]
    _ ≤ ⨆ p : LTSeries (PrimeSpectrum (R ⧸ P)), (p.length : ℕ∞) :=
        le_iSup (fun p : LTSeries (PrimeSpectrum (R ⧸ P)) => (p.length : ℕ∞)) lQ

/- Section 3: Completeness of quotients and local homomorphism pullback -/

private lemma maximalIdeal_quotient_eq_map (R : Type*) [CommRing R] [IsLocalRing R]
    (P : Ideal R) [P.IsPrime] [IsLocalRing (R ⧸ P)] :
    maximalIdeal (R ⧸ P) = (maximalIdeal R).map (Ideal.Quotient.mk P) := by
  have hle : RingHom.ker (Ideal.Quotient.mk P) ≤ maximalIdeal R := by
    rw [Ideal.mk_ker]
    exact IsLocalRing.le_maximalIdeal Ideal.IsPrime.ne_top'
  have hmax : ((maximalIdeal R).map (Ideal.Quotient.mk P)).IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective hle
  exact (IsLocalRing.eq_maximalIdeal hmax).symm

private lemma isAdicComplete_quotient (R : Type*) [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R]
    (P : Ideal R) [P.IsPrime] [IsLocalRing (R ⧸ P)] :
    IsAdicComplete (maximalIdeal (R ⧸ P)) (R ⧸ P) := by
  have hmax : maximalIdeal (R ⧸ P) = (maximalIdeal R).map (algebraMap R (R ⧸ P)) :=
    maximalIdeal_quotient_eq_map R P
  rw [hmax, IsAdicComplete.map_algebraMap_iff, ← AdicCompletion.of_bijective_iff]
  refine ⟨?_, ?_⟩
  · rw [AdicCompletion.of_injective_iff]
    have hH : IsHausdorff (maximalIdeal (R ⧸ P)) (R ⧸ P) := inferInstance
    rw [hmax, IsHausdorff.map_algebraMap_iff] at hH
    exact hH
  · intro y
    have hmap_surj : Function.Surjective
        (AdicCompletion.map (maximalIdeal R) (Algebra.linearMap R (R ⧸ P))) :=
      AdicCompletion.map_surjective (maximalIdeal R) Ideal.Quotient.mk_surjective
    obtain ⟨z, rfl⟩ := hmap_surj y
    obtain ⟨r, rfl⟩ := (AdicCompletion.of_bijective (maximalIdeal R) R).2 z
    refine ⟨Ideal.Quotient.mk P r, ?_⟩
    exact (AdicCompletion.map_of (maximalIdeal R) (Algebra.linearMap R (R ⧸ P)) r).symm

private lemma isLocalHom_quotientMk (R : Type*) [CommRing R] [IsLocalRing R]
    (P : Ideal R) [P.IsPrime] [IsLocalRing (R ⧸ P)] :
    IsLocalHom (Ideal.Quotient.mk P) := by
  apply ((IsLocalRing.local_hom_TFAE (Ideal.Quotient.mk P)).out 0 2).mpr
  rw [maximalIdeal_quotient_eq_map R P]

private lemma balancedBigCM_of_localHom
    (A B : Type) [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    (φ : A →+* B) [IsLocalHom φ]
    (hdim : ringKrullDim B = ringKrullDim A)
    (hmax : (maximalIdeal A).map φ = maximalIdeal B)
    (W : Type) [AddCommGroup W] [Module B W]
    (hW : IsBalancedBigCohenMacaulay B W) :
    ∃ (W' : Type) (_ : AddCommGroup W') (_ : Module A W'), IsBalancedBigCohenMacaulay A W' := by
  let _ : Module A W := Module.compHom W φ
  have hsmul_eq : ∀ (a : A) (w : W), a • w = φ a • w := fun _ _ => rfl
  have hmap_max : ∀ a ∈ maximalIdeal A, φ a ∈ maximalIdeal B := by
    intro a ha
    rw [← hmax]
    exact Ideal.mem_map_of_mem φ ha
  have hsmul_top : maximalIdeal A • (⊤ : Submodule A W) ≠ ⊤ := by
    intro htop
    apply hW.smul_top_ne_top
    rw [eq_top_iff]
    intro w _
    have hw : w ∈ maximalIdeal A • (⊤ : Submodule A W) := by rw [htop]; trivial
    refine Submodule.smul_induction_on hw ?_ ?_
    · intro a ha x _
      exact Submodule.smul_mem_smul (hmap_max a ha) trivial
    · intro x y hx hy
      exact Submodule.add_mem _ hx hy
  have hreg : ∀ rs : List A, IsSystemOfParameters A rs → RingTheory.Sequence.IsRegular W rs := by
    intro rs hrs
    have hrs' : IsSystemOfParameters B (rs.map φ) := by
      refine ⟨?_, ?_⟩
      · simp [hrs.length_eq, hdim]
      · apply le_antisymm
        · have hle : Ideal.ofList (rs.map φ) ≤ maximalIdeal B := by
            rw [← Ideal.map_ofList, Ideal.map_le_iff_le_comap]
            intro a ha
            exact hmap_max a (hrs.radical_eq ▸ Ideal.le_radical ha)
          exact (Ideal.radical_mono hle).trans
            (IsLocalRing.maximalIdeal.isMaximal B).isPrime.radical.le
        · rw [← hmax, Ideal.map_le_iff_le_comap]
          intro a ha
          rw [← hrs.radical_eq, Ideal.mem_radical_iff] at ha
          obtain ⟨n, hn⟩ := ha
          rw [Ideal.mem_comap, Ideal.mem_radical_iff, ← Ideal.map_ofList]
          refine ⟨n, ?_⟩
          rw [← map_pow]
          exact Ideal.mem_map_of_mem φ hn
    have hreg' : RingTheory.Sequence.IsRegular W (rs.map φ) := hW.isRegular (rs.map φ) hrs'
    exact ((AddEquiv.refl W).isRegular_congr
      (List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr fun a _ w => hsmul_eq a w))).mpr hreg'
  exact ⟨W, inferInstance, inferInstance, ⟨hsmul_top, hreg⟩⟩

end Helpers

theorem main : H1 → H2 →
    OMA.R_SmallCohenMacaulayModules_exists_isBalancedBigCohenMacaulay_R1.H1 := by
  intro h1 h2 A _ _ _ _ hdimA hcharA
  let Â : Type := AdicCompletion (maximalIdeal A) A
  have : IsNoetherianRing Â := isNoetherianRing_adicCompletion A (maximalIdeal A)
  have hdimÂ : ringKrullDim Â = ringKrullDim A := ringKrullDim_adicCompletion_eq A
  obtain ⟨P, hP, hdimP⟩ := exists_prime_quotient_same_dim Â
  let B : Type := Â ⧸ P
  have : IsLocalRing B :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
  have : IsAdicComplete (maximalIdeal B) B := isAdicComplete_quotient Â P
  have : IsLocalHom (Ideal.Quotient.mk P) := isLocalHom_quotientMk Â P
  let φ : A →+* B := (Ideal.Quotient.mk P).comp (algebraMap A Â)
  have : IsLocalHom φ := RingHom.isLocalHom_comp (Ideal.Quotient.mk P) (algebraMap A Â)
  have hdimB : ringKrullDim B = ringKrullDim A := hdimP.trans hdimÂ
  have hdimB2 : (2 : WithBot ℕ∞) ≤ ringKrullDim B := hdimB.symm ▸ hdimA
  have hmax_map : (maximalIdeal A).map φ = maximalIdeal B := by
    change (maximalIdeal A).map ((Ideal.Quotient.mk P).comp (algebraMap A Â)) = maximalIdeal B
    rw [← Ideal.map_map, ← AdicCompletion.maximalIdeal_eq_map, ← maximalIdeal_quotient_eq_map Â P]
  have hW_B : ∃ (W : Type) (_ : AddCommGroup W) (_ : Module B W),
      IsBalancedBigCohenMacaulay B W := by
    rcases CharP.char_is_prime_or_zero A (ringChar A) with hp | h0
    · have hcharB : CharP B (ringChar A) := by
        have hzero : ((ringChar A : ℕ) : B) = 0 := by
          rw [← map_natCast φ, CharP.cast_eq_zero A (ringChar A), map_zero]
        have hdvd : ringChar B ∣ ringChar A := ringChar.dvd hzero
        rcases (Nat.dvd_prime hp).mp hdvd with h1_eq | hp_eq
        · have h10 : ((1 : ℕ) : B) = 0 := (ringChar.spec B 1).mpr (h1_eq ▸ dvd_rfl)
          simp at h10
        · rw [← hp_eq]
          exact ringChar.charP B
      exact h1 B (ringChar A) hp hcharB hdimB2
    · have hresA0 : ringChar (ResidueField A) = 0 := hcharA.symm.trans h0
      have : CharP (ResidueField A) 0 := hresA0 ▸ ringChar.charP (ResidueField A)
      have hCZ_resA : CharZero (ResidueField A) := CharP.charP_to_charZero (ResidueField A)
      have hres_inj : Function.Injective (IsLocalRing.ResidueField.map φ) :=
        RingHom.injective (IsLocalRing.ResidueField.map φ)
      have hCZ_resB : CharZero (ResidueField B) := by
        refine ⟨fun m n hmn => ?_⟩
        apply Nat.cast_injective (R := ResidueField A)
        apply hres_inj
        simpa using hmn
      have hCZ_B : CharZero B := by
        refine ⟨fun m n hmn => ?_⟩
        apply Nat.cast_injective (R := ResidueField B)
        have := congrArg (IsLocalRing.residue B) hmn
        simpa using this
      exact h2 B hCZ_B hCZ_resB hdimB2
  obtain ⟨W, _, _, hW⟩ := hW_B
  exact balancedBigCM_of_localHom A B φ hdimB hmax_map W hW

end OMA.R_SmallCohenMacaulayModules_exists_isBalancedBigCohenMacaulay_R1_H1_R1
