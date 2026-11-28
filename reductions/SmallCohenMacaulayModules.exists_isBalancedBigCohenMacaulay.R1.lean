import FormalConjectures.Wikipedia.SmallCohenMacaulayModules
import Mathlib

/-!
Existence of Balanced Big Cohen-Macaulay Modules (Hochster 1975, André 2018): Reduction

This file reduces the existence of a balanced big Cohen-Macaulay module over an arbitrary
Noetherian local ring `R` in an arbitrary universe `u` to two canonical `Type 0` theorems:

1. `H1`: Equal-characteristic existence (Hochster 1975): every Noetherian local domain `A : Type`
   of Krull dimension at least 2 with `ringChar A = ringChar (ResidueField A)` has a balanced
   big Cohen-Macaulay module `W : Type`.
2. `H2`: Mixed-characteristic existence (André 2018): every Noetherian local domain `A : Type`
   of Krull dimension at least 2 with `ringChar A ≠ ringChar (ResidueField A)` has a balanced
   big Cohen-Macaulay module `W : Type`.

In `main`, we prove directly in Lean:
- Full-dimensional prime quotient reduction: passing from any Noetherian local ring `R : Type u`
  to a Noetherian local domain `D = R ⧸ P` with `ringKrullDim D = ringKrullDim R` and pulling
  back any balanced big Cohen-Macaulay `D`-module to `R`.
- Direct proof of the `ringKrullDim D ≤ 1` base case (fields and 1-dimensional local domains)
  taking `W = D`.
- Countable faithfully flat local subring descent (`exists_countable_flat_subring`) preserving
  Krull dimension, maximal ideal generators, and any prescribed countable family of systems of
  parameters, landing in a `Type 0` Noetherian local domain `A`.
- Hochster's universal balanced modification colimit `W = (AllGen →₀ D) ⧸ RelAll : Type u` for
  every Noetherian local domain `D : Type u` of dimension `≥ 2`: every system of parameters of
  `D` is weakly regular on `W` by construction, while `maximalIdeal D • ⊤ ≠ ⊤` follows by
  extracting the countable relation ancestry of any hypothetical collapse `1 ∈ m_D • W`,
  descending to `A : Type 0`, invoking `H1` or `H2` for a balanced big Cohen-Macaulay `A`-module
  `W₀ : Type 0`, and recursively constructing evaluation maps `Gen n → W₀` killing every
  descended stage relation and sending the base generator to `w₀ ∉ m_A • W₀`.
-/

namespace OMA.R_SmallCohenMacaulayModules_exists_isBalancedBigCohenMacaulay_R1

open IsLocalRing Module
open scoped Pointwise

universe u

/-- Equal-characteristic existence of balanced big Cohen-Macaulay modules (Hochster 1975):
every Noetherian local domain of Krull dimension at least 2 with
`ringChar A = ringChar (ResidueField A)` has a balanced big Cohen-Macaulay module. -/
def H1 : Prop :=
  ∀ (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A],
    (2 : WithBot ℕ∞) ≤ ringKrullDim A →
    ringChar A = ringChar (ResidueField A) →
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module A W), IsBalancedBigCohenMacaulay A W

/-- Mixed-characteristic existence of balanced big Cohen-Macaulay modules (André 2018):
every Noetherian local domain of Krull dimension at least 2 with
`ringChar A ≠ ringChar (ResidueField A)` has a balanced big Cohen-Macaulay module. -/
def H2 : Prop :=
  ∀ (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A],
    (2 : WithBot ℕ∞) ≤ ringKrullDim A →
    ringChar A ≠ ringChar (ResidueField A) →
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module A W), IsBalancedBigCohenMacaulay A W

section

/- Section 1: Krull dimension helpers, prime quotient reduction, and dim <= 1 base case -/

private lemma ringKrullDim_eq_nat_of_local_noetherian
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
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
    have : m + 1 ≤ m := Nat.cast_le.mp hsup
    omega

private lemma exists_prime_quotient_same_dim
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    ∃ P : Ideal R, P.IsPrime ∧ ringKrullDim (R ⧸ P) = ringKrullDim R := by
  obtain ⟨d, hd⟩ := ringKrullDim_eq_nat_of_local_noetherian R
  obtain ⟨l, hl⟩ := exists_ltSeries_of_krullDim_eq_nat hd
  let P : Ideal R := (l ⟨0, Nat.zero_lt_succ _⟩).asIdeal
  have hP : P.IsPrime := (l ⟨0, Nat.zero_lt_succ _⟩).isPrime
  refine ⟨P, hP, le_antisymm (ringKrullDim_quotient_le P) ?_⟩
  let q : R →+* R ⧸ P := Ideal.Quotient.mk P
  have hker : Ideal.comap q ⊥ = P := by
    ext x
    exact Ideal.Quotient.eq_zero_iff_mem
  have hge : ∀ i : Fin (l.length + 1), P ≤ (l i).asIdeal := fun i =>
    l.monotone (Fin.zero_le i)
  have hprime_map : ∀ i : Fin (l.length + 1), ((l i).asIdeal.map q).IsPrime := fun i =>
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by
      rw [Ideal.mk_ker]
      exact hge i)
  let lQ : LTSeries (PrimeSpectrum (R ⧸ P)) := {
    length := l.length
    toFun := fun i => ⟨(l i).asIdeal.map q, hprime_map i⟩
    step := fun i => by
      change (l i.castSucc).asIdeal.map q < (l i.succ).asIdeal.map q
      have hlt : (l i.castSucc).asIdeal < (l i.succ).asIdeal := l.step i
      refine lt_of_le_of_ne (Ideal.map_mono (le_of_lt hlt)) fun heq => ne_of_lt hlt ?_
      have h1 : ((l i.castSucc).asIdeal.map q).comap q = (l i.castSucc).asIdeal := by
        rw [Ideal.comap_map_of_surjective q Ideal.Quotient.mk_surjective, hker,
          sup_eq_left.mpr (hge i.castSucc)]
      have h2 : ((l i.succ).asIdeal.map q).comap q = (l i.succ).asIdeal := by
        rw [Ideal.comap_map_of_surjective q Ideal.Quotient.mk_surjective, hker,
          sup_eq_left.mpr (hge i.succ)]
      rw [← h1, ← h2, heq]
  }
  rw [hd, ringKrullDim, Order.krullDim_eq_iSup_length]
  apply WithBot.coe_le_coe.mpr
  calc (d : ℕ∞) = (lQ.length : ℕ∞) := by simp [lQ, hl]
    _ ≤ ⨆ p : LTSeries (PrimeSpectrum (R ⧸ P)), (p.length : ℕ∞) :=
        le_iSup (fun p : LTSeries (PrimeSpectrum (R ⧸ P)) => (p.length : ℕ∞)) lQ

private lemma balancedBigCM_of_quotient
    (R : Type u) [CommRing R] [IsLocalRing R]
    (P : Ideal R) [P.IsPrime] [IsLocalRing (R ⧸ P)]
    (hdim : ringKrullDim (R ⧸ P) = ringKrullDim R)
    (W : Type u) [AddCommGroup W] [Module (R ⧸ P) W]
    (hW : IsBalancedBigCohenMacaulay (R ⧸ P) W) :
    ∃ (W' : Type u) (_ : AddCommGroup W') (_ : Module R W'), IsBalancedBigCohenMacaulay R W' := by
  let q : R →+* R ⧸ P := Ideal.Quotient.mk P
  let _ : Module R W := Module.compHom W q
  have hsmul_eq : ∀ (r : R) (w : W), r • w = q r • w := fun _ _ => rfl
  have hmap_max : ∀ r ∈ maximalIdeal R, q r ∈ maximalIdeal (R ⧸ P) := by
    intro r hr
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hr ⊢
    intro hu
    obtain ⟨y, hy⟩ := hu.exists_right_inv
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hdiff : r * s - 1 ∈ P := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, map_one, hy, sub_self]
    have hmem : r * s - 1 ∈ maximalIdeal R :=
      IsLocalRing.le_maximalIdeal Ideal.IsPrime.ne_top' hdiff
    have h1 : (1 : R) ∈ maximalIdeal R := by
      have h2 := Ideal.sub_mem (maximalIdeal R) (Ideal.mul_mem_right s (maximalIdeal R) hr) hmem
      have h3 : r * s - (r * s - 1) = 1 := by ring
      rwa [h3] at h2
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)
  have hsmul_top : maximalIdeal R • (⊤ : Submodule R W) ≠ ⊤ := by
    intro htop
    apply hW.smul_top_ne_top
    rw [eq_top_iff]
    intro w _
    have hw : w ∈ maximalIdeal R • (⊤ : Submodule R W) := by rw [htop]; trivial
    refine Submodule.smul_induction_on hw ?_ ?_
    · intro r hr x _
      exact Submodule.smul_mem_smul (hmap_max r hr) trivial
    · intro x y hx hy
      exact Submodule.add_mem _ hx hy
  have hreg : ∀ rs : List R, IsSystemOfParameters R rs → RingTheory.Sequence.IsRegular W rs := by
    intro rs hrs
    have hrs' : IsSystemOfParameters (R ⧸ P) (rs.map q) := by
      refine ⟨?_, ?_⟩
      · simp [hrs.length_eq, hdim]
      · apply le_antisymm
        · intro y hy
          obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hy
          have hle : Ideal.ofList (rs.map q) ≤ maximalIdeal (R ⧸ P) := by
            rw [← Ideal.map_ofList, Ideal.map_le_iff_le_comap]
            intro r hr
            exact hmap_max r (hrs.radical_eq ▸ Ideal.le_radical hr)
          exact (IsLocalRing.maximalIdeal.isMaximal (R ⧸ P)).isPrime.mem_of_pow_mem n (hle hn)
        · intro y hy
          obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
          have hx : x ∈ maximalIdeal R := by
            rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hy ⊢
            intro hu
            exact hy (hu.map q)
          rw [← hrs.radical_eq, Ideal.mem_radical_iff] at hx
          obtain ⟨n, hn⟩ := hx
          rw [Ideal.mem_radical_iff]
          refine ⟨n, ?_⟩
          rw [← map_pow, ← Ideal.map_ofList]
          exact Ideal.mem_map_of_mem q hn
    have hreg' : RingTheory.Sequence.IsRegular W (rs.map q) := hW.isRegular (rs.map q) hrs'
    exact ((AddEquiv.refl W).isRegular_congr
      (List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr fun r _ w => hsmul_eq r w))).mpr hreg'
  exact ⟨W, inferInstance, inferInstance, ⟨hsmul_top, hreg⟩⟩

private lemma exists_balanced_of_domain_dim_le_one
    (D : Type u) [CommRing D] [IsLocalRing D] [IsNoetherianRing D] [IsDomain D]
    (hdim : ringKrullDim D ≤ 1) :
    ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module D W), IsBalancedBigCohenMacaulay D W := by
  refine ⟨D, inferInstance, inferInstance, ?_, ?_⟩
  · intro htop
    have h1 : (1 : D) ∈ maximalIdeal D • (⊤ : Submodule D D) := by rw [htop]; trivial
    have hle : maximalIdeal D • (⊤ : Submodule D D) ≤ maximalIdeal D := by
      rw [Submodule.smul_le]
      intro r hr x _
      exact Ideal.mul_mem_right x (maximalIdeal D) hr
    exact (IsLocalRing.maximalIdeal.isMaximal D).ne_top
      (Ideal.eq_top_of_isUnit_mem _ (hle h1) isUnit_one)
  · intro rs hrs
    have hlen : rs.length ≤ 1 := by
      have h1 : ((rs.length : ℕ) : WithBot ℕ∞) ≤ 1 := hrs.length_eq.le.trans hdim
      have h2 : ((rs.length : ℕ) : ℕ∞) ≤ ((1 : ℕ) : ℕ∞) := WithBot.coe_le_coe.mp h1
      exact ENat.natCast_le_natCast.mp h2
    cases rs with
    | nil => exact RingTheory.Sequence.IsRegular.nil D D
    | cons x tl =>
      cases tl with
      | nil =>
        have hxne : x ≠ 0 := by
          intro hx0
          have hrad : (Ideal.ofList [x]).radical = ⊥ := by
            rw [hx0, Ideal.ofList_singleton, Ideal.span_singleton_eq_bot.mpr rfl]
            ext a
            simp only [Ideal.mem_radical_iff, Ideal.mem_bot]
            exact ⟨fun ⟨n, hn⟩ => eq_zero_of_pow_eq_zero hn, fun ha => ⟨1, by simp [ha]⟩⟩
          have hmax0 : maximalIdeal D = ⊥ := hrs.radical_eq.symm.trans hrad
          have hdim0 : ringKrullDim D ≤ 0 := by
            rw [ringKrullDim, Order.krullDim_eq_iSup_length]
            apply WithBot.coe_le_coe.mpr
            apply iSup_le
            intro l
            cases hll : l.length with
            | zero => exact le_rfl
            | succ m =>
              exfalso
              have hlt : (l ⟨0, by omega⟩).asIdeal < (l ⟨1, by omega⟩).asIdeal :=
                l.strictMono (by show (⟨0, _⟩ : Fin (l.length + 1)) < ⟨1, _⟩; exact Nat.zero_lt_one)
              have h1 : (l ⟨1, by omega⟩).asIdeal ≤ ⊥ :=
                hmax0 ▸ IsLocalRing.le_maximalIdeal (l ⟨1, by omega⟩).isPrime.ne_top
              exact not_lt_of_ge (h1.trans bot_le) (lt_of_le_of_lt bot_le hlt)
          have hbad : ((1 : ℕ) : WithBot ℕ∞) ≤ 0 := by
            have heq : (([x] : List D).length : WithBot ℕ∞) = ringKrullDim D := hrs.length_eq
            simpa using heq.le.trans hdim0
          have hbad' : ((1 : ℕ) : ℕ∞) ≤ ((0 : ℕ) : ℕ∞) := WithBot.coe_le_coe.mp hbad
          exact absurd (ENat.natCast_le_natCast.mp hbad') (by omega)
        refine ⟨⟨fun i hi => ?_⟩, ?_⟩
        · have hi0 : i = 0 := by simp at hi; omega
          subst hi0
          have hbot : (Ideal.ofList (List.take 0 [x]) • (⊤ : Submodule D D)) = ⊥ := by
            simp
          let e : (D ⧸ (Ideal.ofList (List.take 0 [x]) • (⊤ : Submodule D D))) ≃ₗ[D] D :=
            Submodule.quotEquivOfEqBot _ hbot
          have hregx : IsSMulRegular D x := fun a b hab => mul_left_cancel₀ hxne hab
          exact (e.symm.isSMulRegular_congr x).mp hregx
        · intro htop
          have h1 : (1 : D) ∈ Ideal.ofList [x] • (⊤ : Submodule D D) := by
            rw [← htop]; trivial
          have hle : Ideal.ofList [x] • (⊤ : Submodule D D) ≤ maximalIdeal D := by
            rw [Submodule.smul_le]
            intro r hr y _
            have hrm : r ∈ maximalIdeal D := hrs.radical_eq ▸ Ideal.le_radical hr
            exact Ideal.mul_mem_right y (maximalIdeal D) hrm
          exact (IsLocalRing.maximalIdeal.isMaximal D).ne_top
            (Ideal.eq_top_of_isUnit_mem _ (hle h1) isUnit_one)
      | cons y tl' =>
        simp at hlen

private lemma mem_ofList_smul_top_iff
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (s : List R) (x : M) :
    x ∈ Ideal.ofList s • (⊤ : Submodule R M) ↔
      ∃ v : Fin s.length → M, x = ∑ j : Fin s.length, s[j] • v j := by
  induction s generalizing x with
  | nil =>
    rw [Ideal.ofList_nil, Submodule.bot_smul, Submodule.mem_bot]
    simp only [List.length_nil, Finset.univ_eq_empty, Finset.sum_empty]
    exact ⟨fun h => ⟨Fin.elim0, h⟩, fun ⟨_, h⟩ => h⟩
  | cons r t ih =>
    rw [Ideal.ofList_cons_smul, Submodule.mem_sup]
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      obtain ⟨u, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists a r (⊤ : Submodule R M)).mp ha
      obtain ⟨v, rfl⟩ := (ih b).mp hb
      refine ⟨Fin.cons (α := fun _ => M) u v, ?_⟩
      have hsum : ∑ j : Fin (r :: t).length, (r :: t)[j] • Fin.cons (α := fun _ => M) u v j =
          r • u + ∑ j : Fin t.length, t[j] • v j := by
        simpa [Fin.cons_zero, Fin.cons_succ] using
          Fin.sum_univ_succ (fun j : Fin (t.length + 1) =>
            (r :: t)[j] • Fin.cons (α := fun _ => M) u v j)
      exact hsum.symm
    · rintro ⟨v, rfl⟩
      have hsum : ∑ j : Fin (r :: t).length, (r :: t)[j] • v j =
          r • v 0 + ∑ j : Fin t.length, t[j] • v j.succ :=
        Fin.sum_univ_succ (fun j : Fin (t.length + 1) => (r :: t)[j] • v j)
      rw [hsum]
      refine ⟨r • v 0, Submodule.smul_mem_pointwise_smul (v 0) r ⊤ trivial,
        ∑ j : Fin t.length, t[j] • v j.succ, (ih _).mpr ⟨fun j => v j.succ, rfl⟩, rfl⟩

/- Section 2: Countable faithfully flat local subring descent into opaque Type 0 -/

private lemma countable_subring_closure {R : Type u} [CommRing R] {s : Set R} (hs : s.Countable) :
    (Subring.closure s : Set R).Countable := by
  let step : Set R → Set R := fun t =>
    t ∪ ((fun p : R × R => p.1 + p.2) '' (t ×ˢ t)) ∪
      ((fun p : R × R => p.1 * p.2) '' (t ×ˢ t)) ∪
      ((fun x : R => -x) '' t)
  let L : ℕ → Set R := Nat.rec (s ∪ {0, 1}) (fun _ t => step t)
  have hL_count : ∀ n, (L n).Countable := by
    intro n
    induction n with
    | zero => exact hs.union ((Set.countable_singleton 0).union (Set.countable_singleton 1))
    | succ n ih =>
      exact ((ih.union ((ih.prod ih).image _)).union ((ih.prod ih).image _)).union (ih.image _)
  have hL_step : ∀ n, L n ⊆ L (n + 1) := fun n x hx => Or.inl (Or.inl (Or.inl hx))
  have hL_mono : Monotone L := monotone_nat_of_le_succ hL_step
  let U : Set R := ⋃ n : ℕ, L n
  let B : Subring R := {
    carrier := U
    zero_mem' := Set.mem_iUnion.mpr ⟨0, Or.inr (Or.inl rfl)⟩
    one_mem' := Set.mem_iUnion.mpr ⟨0, Or.inr (Or.inr rfl)⟩
    add_mem' := fun {a b} ha hb => by
      obtain ⟨m, hm⟩ := Set.mem_iUnion.mp ha
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hb
      refine Set.mem_iUnion.mpr ⟨max m n + 1, Or.inl (Or.inl (Or.inr ?_))⟩
      exact ⟨(a, b), ⟨hL_mono (le_max_left m n) hm, hL_mono (le_max_right m n) hn⟩, rfl⟩
    mul_mem' := fun {a b} ha hb => by
      obtain ⟨m, hm⟩ := Set.mem_iUnion.mp ha
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hb
      refine Set.mem_iUnion.mpr ⟨max m n + 1, Or.inl (Or.inr ?_)⟩
      exact ⟨(a, b), ⟨hL_mono (le_max_left m n) hm, hL_mono (le_max_right m n) hn⟩, rfl⟩
    neg_mem' := fun {a} ha => by
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp ha
      exact Set.mem_iUnion.mpr ⟨n + 1, Or.inr ⟨a, hn, rfl⟩⟩
  }
  have hsub : (Subring.closure s : Set R) ⊆ U := by
    change Subring.closure s ≤ B
    rw [Subring.closure_le]
    intro x hx
    exact Set.mem_iUnion.mpr ⟨0, Or.inl hx⟩
  exact (Set.countable_iUnion hL_count).mono hsub

private lemma exists_countable_flat_subring
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (S₀ : Set R) (hS₀_count : S₀.Countable) :
    ∃ (R₀ : Subring R), Countable R₀ ∧ S₀ ⊆ (R₀ : Set R) ∧
      IsLocalHom (algebraMap R₀ R) ∧ IsLocalRing R₀ ∧
      Module.Flat R₀ R ∧ IsNoetherianRing R₀ := by
  classical
  let syzGen : ∀ (n : ℕ) (f : Fin n → R), Finset (Fin n → R) := fun n f =>
    let φ : (Fin n → R) →ₗ[R] R := {
      toFun := fun v => ∑ i : Fin n, f i * v i
      map_add' := fun v w => by simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun r v => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => by ring
    }
    (IsNoetherian.noetherian (LinearMap.ker φ)).choose
  have hsyzGen : ∀ (n : ℕ) (f : Fin n → R),
      Submodule.span R (syzGen n f : Set (Fin n → R)) =
      LinearMap.ker ({
        toFun := fun v : Fin n → R => ∑ i : Fin n, f i * v i
        map_add' := fun v w => by simp [mul_add, Finset.sum_add_distrib]
        map_smul' := fun r v => by
          simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => by ring
      } : (Fin n → R) →ₗ[R] R) := fun n f =>
    (IsNoetherian.noetherian _).choose_spec
  let stepSet : Subring R → Set R := fun B =>
    (B : Set R) ∪
    Set.range (fun u : { b : B // IsUnit (b : R) } => ((u.2.unit⁻¹ : Rˣ) : R)) ∪
    ⋃ (q : Σ n : ℕ, Fin n → B), ⋃ (v : syzGen q.1 (fun i => (q.2 i : R))),
      Set.range (v.1 : Fin q.1 → R)
  have hstep_count : ∀ B : Subring R, (B : Set R).Countable → (stepSet B).Countable := by
    intro B hB
    have _ : Countable B := hB.to_subtype
    have h1 : (Set.range (fun u : { b : B // IsUnit (b : R) } => ((u.2.unit⁻¹ : Rˣ) : R))).Countable :=
      Set.countable_range _
    have h2 : (⋃ (q : Σ n : ℕ, Fin n → B), ⋃ (v : syzGen q.1 (fun i => (q.2 i : R))),
        Set.range (v.1 : Fin q.1 → R)).Countable := by
      refine Set.countable_iUnion fun q => ?_
      refine Set.countable_iUnion fun v => ?_
      exact Set.countable_range _
    exact (hB.union h1).union h2
  let T : ℕ → Subring R := Nat.rec (Subring.closure S₀) (fun _ B => Subring.closure (stepSet B))
  have hT_count : ∀ k, (SetLike.coe (T k)).Countable := by
    intro k
    induction k with
    | zero => exact countable_subring_closure hS₀_count
    | succ k ih => exact countable_subring_closure (hstep_count (T k) ih)
  have hT_step : ∀ k, T k ≤ T (k + 1) := by
    intro k x hx
    exact Subring.subset_closure (Or.inl (Or.inl (show x ∈ SetLike.coe (T k) from hx)))
  have hT_mono : Monotone T := monotone_nat_of_le_succ hT_step
  let R₀ : Subring R := ⨆ k : ℕ, T k
  have hR₀_mem : ∀ x : R, x ∈ R₀ ↔ ∃ k : ℕ, x ∈ T k := fun x =>
    Subring.mem_iSup_of_directed hT_mono.directed_le
  have hR₀_count : (R₀ : Set R).Countable := by
    have heq : (R₀ : Set R) = ⋃ k : ℕ, SetLike.coe (T k) := by
      ext x; simp only [SetLike.mem_coe, Set.mem_iUnion, hR₀_mem]
    rw [heq]
    exact Set.countable_iUnion hT_count
  have hcnt : Countable R₀ := hR₀_count.to_subtype
  have hS₀_sub : S₀ ⊆ (R₀ : Set R) := fun x hx =>
    (hR₀_mem x).mpr ⟨0, Subring.subset_closure hx⟩
  have hlocalHom₀ : IsLocalHom (algebraMap R₀ R) := by
    constructor
    intro b hb
    obtain ⟨k, hk⟩ := (hR₀_mem b.1).mp b.2
    have hinv_mem : ((hb.unit⁻¹ : Rˣ) : R) ∈ T (k + 1) :=
      Subring.subset_closure (Or.inl (Or.inr ⟨⟨⟨b.1, hk⟩, hb⟩, rfl⟩))
    have hinvR₀ : ((hb.unit⁻¹ : Rˣ) : R) ∈ R₀ := (hR₀_mem _).mpr ⟨k + 1, hinv_mem⟩
    refine isUnit_iff_exists_inv.mpr ⟨⟨((hb.unit⁻¹ : Rˣ) : R), hinvR₀⟩, ?_⟩
    ext
    exact hb.unit.mul_inv
  have hloc₀ : IsLocalRing R₀ := (algebraMap R₀ R).domain_isLocalRing
  have hflat₀ : Module.Flat R₀ R := by
    apply Module.Flat.of_forall_isTrivialRelation
    intro l f x hrel
    have hex_k : ∃ k : ℕ, ∀ i : Fin l, (f i : R) ∈ T k := by
      have : ∀ i : Fin l, ∃ k : ℕ, (f i : R) ∈ T k := fun i => (hR₀_mem _).mp (f i).2
      choose fk hfk using this
      refine ⟨Finset.univ.sup fk, fun i => hT_mono (Finset.le_sup (Finset.mem_univ i)) (hfk i)⟩
    obtain ⟨k, hk⟩ := hex_k
    let f_k : Fin l → T k := fun i => ⟨(f i : R), hk i⟩
    let G := syzGen l (fun i => (f_k i : R))
    have hx_mem : x ∈ Submodule.span R (G : Set (Fin l → R)) := by
      rw [hsyzGen l (fun i => (f_k i : R)), LinearMap.mem_ker]
      exact hrel
    rw [Finsupp.mem_span_iff_linearCombination] at hx_mem
    obtain ⟨c, hc⟩ := hx_mem
    let m : ℕ := G.card
    let eG : Fin m ≃ G := (Fintype.equivFinOfCardEq (Fintype.card_coe G)).symm
    have hmem_coord : ∀ (j : Fin m) (i : Fin l), (eG j).1 i ∈ R₀ := fun j i => by
      have h1 : (eG j).1 i ∈ T (k + 1) := by
        apply Subring.subset_closure
        right
        refine Set.mem_iUnion.mpr ⟨⟨l, f_k⟩, ?_⟩
        refine Set.mem_iUnion.mpr ⟨eG j, ?_⟩
        exact ⟨i, rfl⟩
      exact (hR₀_mem _).mpr ⟨k + 1, h1⟩
    refine ⟨m, fun i j => ⟨(eG j).1 i, hmem_coord j i⟩, fun j => c (eG j), ?_, ?_⟩
    · intro i
      have hci := congrFun hc.symm i
      rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype] at hci
      · rw [hci]
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        calc ∑ g : G, c g * g.1 i
            = ∑ j : Fin m, c (eG j) * (eG j).1 i := (Equiv.sum_comp eG (fun g : G => c g * g.1 i)).symm
          _ = ∑ j : Fin m, (⟨(eG j).1 i, hmem_coord j i⟩ : R₀) • c (eG j) := by
              refine Finset.sum_congr rfl fun j _ => ?_
              change c (eG j) * (eG j).1 i = (eG j).1 i * c (eG j)
              ring
      · intro _; exact zero_smul R _
    · intro j
      apply Subtype.ext
      have hkerj : (eG j).1 ∈ Submodule.span R (G : Set (Fin l → R)) :=
        Submodule.subset_span (eG j).2
      rw [hsyzGen l (fun i => (f_k i : R)), LinearMap.mem_ker] at hkerj
      simpa [f_k] using hkerj
  have hff₀ : Module.FaithfullyFlat R₀ R := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hnoeth₀ : IsNoetherianRing R₀ := by
    rw [IsNoetherianRing, ← monotone_stabilizes_iff_noetherian]
    intro f
    let g : ℕ →o Submodule R R := {
      toFun := fun n => Ideal.map (algebraMap R₀ R) (f n)
      monotone' := fun _ _ h => Ideal.map_mono (f.monotone h)
    }
    obtain ⟨N, hN⟩ := monotone_stabilizes_iff_noetherian.mpr (inferInstance : IsNoetherian R R) g
    refine ⟨N, fun n hn => ?_⟩
    exact Ideal.map_injective_of_faithfullyFlat (A := R₀) (B := R) (hN n hn)
  exact ⟨R₀, hcnt, hS₀_sub, hlocalHom₀, hloc₀, hflat₀, hnoeth₀⟩

private lemma transport_type0_sops
    (D : Type u) [CommRing D] [IsLocalRing D]
    (R₀ : Subring D) [IsLocalRing R₀] [IsNoetherianRing R₀] [IsDomain R₀]
    [IsLocalHom (algebraMap R₀ D)]
    (d : ℕ) (hdim₀ : ringKrullDim R₀ = (d : WithBot ℕ∞))
    (Sops₀ : Set (List D))
    (toR₀ : D → R₀) (htoR₀_eq : ∀ {x : D} (hx : x ∈ R₀), toR₀ x = ⟨x, hx⟩)
    (hsop_R₀ : ∀ rs ∈ Sops₀, IsSystemOfParameters R₀ (rs.map toR₀))
    (A : Type) [CommRing A] (eA : A ≃+* R₀) :
    ∃ (_ : IsLocalRing A) (_ : IsNoetherianRing A) (_ : IsDomain A) (toA : D → A),
      ringKrullDim A = (d : WithBot ℕ∞) ∧
      toA 0 = 0 ∧ toA 1 = 1 ∧
      (∀ {x y : D}, x ∈ R₀ → y ∈ R₀ → toA (x + y) = toA x + toA y) ∧
      (∀ {x y : D}, x ∈ R₀ → y ∈ R₀ → toA (x * y) = toA x * toA y) ∧
      (∀ {x : D}, x ∈ R₀ → toA (-x) = -toA x) ∧
      (∀ {x : D}, x ∈ R₀ → x ∈ maximalIdeal D → toA x ∈ maximalIdeal A) ∧
      (∀ rs ∈ Sops₀, IsSystemOfParameters A (rs.map toA)) := by
  have hlocal_eA : IsLocalHom eA.toRingHom := ⟨fun x hx => by
    have h1 : IsUnit (eA.symm (eA x)) := hx.map eA.symm.toRingHom
    rwa [eA.symm_apply_apply] at h1⟩
  have hlocA : IsLocalRing A := eA.toRingHom.domain_isLocalRing
  have hnoethA : IsNoetherianRing A := isNoetherianRing_of_ringEquiv R₀ eA.symm
  have hdomA : IsDomain A := Function.Injective.isDomain eA.toRingHom eA.injective
  let toA : D → A := fun x => eA.symm (toR₀ x)
  have hdimA : ringKrullDim A = (d : WithBot ℕ∞) := by
    rw [ringKrullDim_eq_of_ringEquiv eA, hdim₀]
  have htoA_zero : toA 0 = 0 := by
    change eA.symm (toR₀ 0) = 0
    rw [htoR₀_eq R₀.zero_mem]
    exact map_zero eA.symm
  have htoA_one : toA 1 = 1 := by
    change eA.symm (toR₀ 1) = 1
    rw [htoR₀_eq R₀.one_mem]
    exact map_one eA.symm
  have htoA_add : ∀ {x y : D}, x ∈ R₀ → y ∈ R₀ → toA (x + y) = toA x + toA y := by
    intro x y hx hy
    change eA.symm (toR₀ (x + y)) = eA.symm (toR₀ x) + eA.symm (toR₀ y)
    rw [htoR₀_eq (R₀.add_mem hx hy), htoR₀_eq hx, htoR₀_eq hy, ← map_add]
    rfl
  have htoA_mul : ∀ {x y : D}, x ∈ R₀ → y ∈ R₀ → toA (x * y) = toA x * toA y := by
    intro x y hx hy
    change eA.symm (toR₀ (x * y)) = eA.symm (toR₀ x) * eA.symm (toR₀ y)
    rw [htoR₀_eq (R₀.mul_mem hx hy), htoR₀_eq hx, htoR₀_eq hy, ← map_mul]
    rfl
  have htoA_neg : ∀ {x : D}, x ∈ R₀ → toA (-x) = -toA x := by
    intro x hx
    change eA.symm (toR₀ (-x)) = -eA.symm (toR₀ x)
    rw [htoR₀_eq (R₀.neg_mem hx), htoR₀_eq hx, ← map_neg]
    rfl
  have htoA_max : ∀ {x : D}, x ∈ R₀ → x ∈ maximalIdeal D → toA x ∈ maximalIdeal A := by
    intro x hx hxm
    change eA.symm (toR₀ x) ∈ maximalIdeal A
    rw [htoR₀_eq hx]
    have hmR₀ : (⟨x, hx⟩ : R₀) ∈ maximalIdeal R₀ := by
      rw [← IsLocalRing.maximalIdeal_comap (algebraMap R₀ D)]
      exact hxm
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hmR₀ ⊢
    intro hu
    have h2 : IsUnit (eA (eA.symm ⟨x, hx⟩)) := hu.map eA.toRingHom
    rw [eA.apply_symm_apply] at h2
    exact hmR₀ h2
  have htoA_sop : ∀ rs ∈ Sops₀, IsSystemOfParameters A (rs.map toA) := by
    intro rs hrs
    have hR₀sop := hsop_R₀ rs hrs
    have hmap : rs.map toA = (rs.map toR₀).map eA.symm.toRingHom := by
      rw [List.map_map]; rfl
    rw [hmap]
    refine ⟨?_, ?_⟩
    · rw [List.length_map, hR₀sop.length_eq, hdim₀, hdimA]
    · apply le_antisymm
      · intro y hy
        obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hy
        have hle : Ideal.ofList ((rs.map toR₀).map eA.symm.toRingHom) ≤ maximalIdeal A := by
          rw [← Ideal.map_ofList, Ideal.map_le_iff_le_comap]
          intro z hz
          have hzm : z ∈ maximalIdeal R₀ := hR₀sop.radical_eq ▸ Ideal.le_radical hz
          rw [Ideal.mem_comap]
          rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hzm ⊢
          intro hu
          have h2 : IsUnit (eA (eA.symm z)) := hu.map eA.toRingHom
          rw [eA.apply_symm_apply] at h2
          exact hzm h2
        exact (IsLocalRing.maximalIdeal.isMaximal A).isPrime.mem_of_pow_mem n (hle hn)
      · intro y hy
        have hym : eA y ∈ maximalIdeal R₀ := by
          rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hy ⊢
          intro hu
          have h2 : IsUnit (eA.symm (eA y)) := hu.map eA.symm.toRingHom
          rw [eA.symm_apply_apply] at h2
          exact hy h2
        rw [← hR₀sop.radical_eq, Ideal.mem_radical_iff] at hym
        obtain ⟨k, hk⟩ := hym
        rw [Ideal.mem_radical_iff]
        refine ⟨k, ?_⟩
        rw [← Ideal.map_ofList]
        have heq : y ^ k = eA.symm ((eA y) ^ k) := by rw [map_pow, eA.symm_apply_apply]
        rw [heq]
        exact Ideal.mem_map_of_mem eA.symm.toRingHom hk
  exact ⟨hlocA, hnoethA, hdomA, toA, hdimA, htoA_zero, htoA_one,
    htoA_add, htoA_mul, htoA_neg, htoA_max, htoA_sop⟩

private lemma exists_type0_local_domain_with_sops
    (D : Type u) [CommRing D] [IsLocalRing D] [IsNoetherianRing D] [IsDomain D]
    (d : ℕ) (hd : ringKrullDim D = (d : WithBot ℕ∞))
    (E₀ : Set D) (hE₀ : E₀.Countable)
    (Sops₀ : Set (List D)) (hSops₀ : Sops₀.Countable)
    (hSops₀_valid : ∀ rs ∈ Sops₀, IsSystemOfParameters D rs) :
    ∃ (A : Type) (_ : CommRing A) (_ : IsLocalRing A) (_ : IsNoetherianRing A) (_ : IsDomain A)
      (R₀ : Subring D) (toA : D → A),
      E₀ ⊆ (R₀ : Set D) ∧
      (∀ rs ∈ Sops₀, ∀ r ∈ rs, r ∈ R₀) ∧
      ringKrullDim A = (d : WithBot ℕ∞) ∧
      toA 0 = 0 ∧ toA 1 = 1 ∧
      (∀ {x y : D}, x ∈ R₀ → y ∈ R₀ → toA (x + y) = toA x + toA y) ∧
      (∀ {x y : D}, x ∈ R₀ → y ∈ R₀ → toA (x * y) = toA x * toA y) ∧
      (∀ {x : D}, x ∈ R₀ → toA (-x) = -toA x) ∧
      (∀ {x : D}, x ∈ R₀ → x ∈ maximalIdeal D → toA x ∈ maximalIdeal A) ∧
      (∀ rs ∈ Sops₀, IsSystemOfParameters A (rs.map toA)) := by
  classical
  obtain ⟨gMax, hgMax_span⟩ := IsNoetherian.noetherian (maximalIdeal D)
  obtain ⟨cD, hcD_len⟩ := exists_ltSeries_of_krullDim_eq_nat hd
  have hwD_ex : ∀ i : Fin d, ∃ w : D,
      w ∈ (cD ⟨i.1 + 1, by omega⟩).asIdeal ∧ w ∉ (cD ⟨i.1, by omega⟩).asIdeal := fun i => by
    have hlt : (cD ⟨i.1, by omega⟩).asIdeal < (cD ⟨i.1 + 1, by omega⟩).asIdeal :=
      cD.strictMono (by show (⟨i.1, _⟩ : Fin (cD.length + 1)) < ⟨i.1 + 1, _⟩; exact Nat.lt_succ_self _)
    exact SetLike.exists_of_lt hlt
  choose wD hwD_mem hwD_nmem using hwD_ex
  have hrad_ex : ∀ (p : Sops₀) (g : gMax),
      ∃ (n : ℕ) (c : Fin p.1.length → D), (g.1 : D) ^ n = ∑ j : Fin p.1.length, c j * p.1[j] := by
    intro p g
    have hgmem : g.1 ∈ maximalIdeal D := by rw [← hgMax_span]; exact Ideal.subset_span g.2
    have hrad : g.1 ∈ (Ideal.ofList p.1).radical := (hSops₀_valid p.1 p.2).radical_eq.symm ▸ hgmem
    obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hrad
    have hn' : (g.1 : D) ^ n ∈ Ideal.ofList p.1 • (⊤ : Submodule D D) := by
      simpa using hn
    obtain ⟨c, hc⟩ := (mem_ofList_smul_top_iff p.1 ((g.1 : D) ^ n)).mp hn'
    refine ⟨n, c, ?_⟩
    simpa [smul_eq_mul, mul_comm] using hc
  choose radExp radCoeff hradEq using hrad_ex
  have _ : Countable Sops₀ := hSops₀.to_subtype
  let sopElems : Set D := ⋃ p : Sops₀, Set.range (fun j : Fin p.1.length => p.1[j])
  have hsopElems_count : sopElems.Countable :=
    Set.countable_iUnion fun _ => Set.countable_range _
  let radCoeffs : Set D := ⋃ p : Sops₀, ⋃ g : gMax, Set.range (radCoeff p g)
  have hradCoeffs_count : radCoeffs.Countable :=
    Set.countable_iUnion fun _ => Set.countable_iUnion fun _ => Set.countable_range _
  let S₀ : Set D := E₀ ∪ (gMax : Set D) ∪ Set.range wD ∪ sopElems ∪ radCoeffs
  have hS₀_count : S₀.Countable :=
    (((hE₀.union gMax.countable_toSet).union (Set.countable_range wD)).union hsopElems_count).union
      hradCoeffs_count
  obtain ⟨R₀, hcnt, hS₀_sub, hlocalHom₀, hloc₀, hflat₀, hnoeth₀⟩ :=
    exists_countable_flat_subring D S₀ hS₀_count
  have hff₀ : Module.FaithfullyFlat R₀ D := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hdom₀ : IsDomain R₀ := Function.Injective.isDomain (algebraMap R₀ D) Subtype.val_injective
  have hE₀_sub : E₀ ⊆ (R₀ : Set D) := fun x hx =>
    hS₀_sub (Or.inl (Or.inl (Or.inl (Or.inl hx))))
  have hgMax_in : ∀ x ∈ gMax, x ∈ R₀ := fun x hx =>
    hS₀_sub (Or.inl (Or.inl (Or.inl (Or.inr hx))))
  have hwD_in : ∀ i : Fin d, wD i ∈ R₀ := fun i =>
    hS₀_sub (Or.inl (Or.inl (Or.inr ⟨i, rfl⟩)))
  have hsop_in : ∀ rs ∈ Sops₀, ∀ r ∈ rs, r ∈ R₀ := by
    intro rs hrs r hr
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hr
    exact hS₀_sub (Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨⟨rs, hrs⟩, ⟨⟨j, hj⟩, rfl⟩⟩)))
  have hradCoeff_in : ∀ (p : Sops₀) (g : gMax) (j : Fin p.1.length), radCoeff p g j ∈ R₀ :=
    fun p g j =>
      hS₀_sub (Or.inr (Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨g, ⟨j, rfl⟩⟩⟩))
  have hdim_ge : (d : WithBot ℕ∞) ≤ ringKrullDim R₀ := by
    let cR₀ : LTSeries (PrimeSpectrum R₀) := {
      length := d
      toFun := fun i => PrimeSpectrum.comap (algebraMap R₀ D) (cD ⟨i.1, by omega⟩)
      step := fun i => by
        change (cD ⟨i.1, by omega⟩).asIdeal.comap (algebraMap R₀ D) <
          (cD ⟨i.1 + 1, by omega⟩).asIdeal.comap (algebraMap R₀ D)
        refine lt_of_le_of_ne (Ideal.comap_mono (cD.monotone (by
          show (⟨i.1, _⟩ : Fin (cD.length + 1)) ≤ ⟨i.1 + 1, _⟩; exact Nat.le_succ _))) ?_
        intro heq
        have h1 : (⟨wD i, hwD_in i⟩ : R₀) ∈
            (cD ⟨i.1 + 1, by omega⟩).asIdeal.comap (algebraMap R₀ D) := hwD_mem i
        rw [← heq] at h1
        exact hwD_nmem i h1
    }
    rw [ringKrullDim, Order.krullDim_eq_iSup_length]
    exact WithBot.coe_le_coe.mpr
      (le_iSup (fun l : LTSeries (PrimeSpectrum R₀) => (l.length : ℕ∞)) cR₀)
  have hdim_le : ringKrullDim R₀ ≤ (d : WithBot ℕ∞) := by
    rw [← hd, ringKrullDim, ringKrullDim, Order.krullDim_eq_iSup_length,
      Order.krullDim_eq_iSup_length]
    apply WithBot.coe_le_coe.mpr
    apply iSup_le
    intro l
    obtain ⟨Q, hQp, hQlo⟩ :=
      Ideal.exists_isPrime_liesOver_of_faithfullyFlat (B := D) l.last.asIdeal
    obtain ⟨L, hLlen, _, _⟩ := Ideal.exists_ltSeries_of_hasGoingDown l Q
    calc (l.length : ℕ∞) = (L.length : ℕ∞) := by rw [hLlen]
      _ ≤ ⨆ p : LTSeries (PrimeSpectrum D), (p.length : ℕ∞) :=
          le_iSup (fun p : LTSeries (PrimeSpectrum D) => (p.length : ℕ∞)) L
  have hdim₀ : ringKrullDim R₀ = (d : WithBot ℕ∞) := le_antisymm hdim_le hdim_ge
  let gMax₀ : Finset R₀ := gMax.attach.image (fun x => ⟨x.1, hgMax_in x.1 x.2⟩)
  have hmax_map : (maximalIdeal R₀).map (algebraMap R₀ D) = maximalIdeal D := by
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      exact le_of_eq (IsLocalRing.maximalIdeal_comap (algebraMap R₀ D)).symm
    · rw [← hgMax_span, Ideal.span_le]
      intro y hy
      have hy0 : (⟨y, hgMax_in y hy⟩ : R₀) ∈ maximalIdeal R₀ := by
        rw [← IsLocalRing.maximalIdeal_comap (algebraMap R₀ D)]
        change y ∈ maximalIdeal D
        rw [← hgMax_span]
        exact Ideal.subset_span hy
      exact Ideal.mem_map_of_mem (algebraMap R₀ D) hy0
  have hmax₀_span : Ideal.span (gMax₀ : Set R₀) = maximalIdeal R₀ := by
    apply Ideal.map_injective_of_faithfullyFlat (A := R₀) (B := D)
    rw [hmax_map, Ideal.map_span, ← hgMax_span]
    congr 1
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [Finset.mem_coe, Finset.mem_image] at hx
      obtain ⟨⟨z, hz⟩, _, rfl⟩ := hx
      exact hz
    · intro hy
      exact ⟨⟨y, hgMax_in y hy⟩,
        Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨⟨y, hy⟩, Finset.mem_attach _ _, rfl⟩), rfl⟩
  let toR₀ : D → R₀ := fun x => if hx : x ∈ R₀ then ⟨x, hx⟩ else 0
  have htoR₀_eq : ∀ {x : D} (hx : x ∈ R₀), toR₀ x = ⟨x, hx⟩ := by
    intro x hx
    dsimp only [toR₀]
    split_ifs
    rfl
  have hsop_R₀ : ∀ rs ∈ Sops₀, IsSystemOfParameters R₀ (rs.map toR₀) := by
    intro rs hrs
    refine ⟨?_, ?_⟩
    · rw [List.length_map, hdim₀, ← hd, (hSops₀_valid rs hrs).length_eq]
    · apply le_antisymm
      · intro y hy
        obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hy
        have hle : Ideal.ofList (rs.map toR₀) ≤ maximalIdeal R₀ := by
          rw [Ideal.span_le]
          intro z hz
          rcases List.mem_map.mp hz with ⟨r, hr, rfl⟩
          rw [htoR₀_eq (hsop_in rs hrs r hr), ← IsLocalRing.maximalIdeal_comap (algebraMap R₀ D)]
          exact (hSops₀_valid rs hrs).mem_maximalIdeal hr
        exact (IsLocalRing.maximalIdeal.isMaximal R₀).isPrime.mem_of_pow_mem n (hle hn)
      · rw [← hmax₀_span, Ideal.span_le]
        intro z hz
        rw [Finset.mem_coe, Finset.mem_image] at hz
        obtain ⟨⟨g, hg⟩, _, rfl⟩ := hz
        let p : Sops₀ := ⟨rs, hrs⟩
        let g' : gMax := ⟨g, hg⟩
        change (⟨g, hgMax_in g hg⟩ : R₀) ∈ (Ideal.ofList (rs.map toR₀)).radical
        rw [Ideal.mem_radical_iff]
        refine ⟨radExp p g', ?_⟩
        have heq_sub : (⟨g, hgMax_in g hg⟩ : R₀) ^ radExp p g' =
            ∑ j : Fin rs.length,
              (⟨radCoeff p g' j, hradCoeff_in p g' j⟩ : R₀) * toR₀ rs[j] := by
          apply Subtype.ext
          rw [SubmonoidClass.coe_pow, AddSubmonoidClass.coe_finsetSum]
          have hsum : ∑ j : Fin rs.length,
              (((⟨radCoeff p g' j, hradCoeff_in p g' j⟩ : R₀) * toR₀ rs[j] : R₀) : D) =
              ∑ j : Fin rs.length, radCoeff p g' j * rs[j] := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [htoR₀_eq (hsop_in rs hrs rs[j] (List.getElem_mem j.2))]
            rfl
          rw [hsum]
          exact hradEq p g'
        rw [heq_sub]
        refine Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ?_)
        exact List.mem_map.mpr ⟨rs[j], List.getElem_mem j.2, rfl⟩
  obtain ⟨hlocA, hnoethA, hdomA, toA, hdimA, htoA_zero, htoA_one,
      htoA_add, htoA_mul, htoA_neg, htoA_max, htoA_sop⟩ :=
    transport_type0_sops D R₀ d hdim₀ Sops₀ toR₀ htoR₀_eq hsop_R₀
      (Shrink.{0} R₀) (Shrink.ringEquiv.{0} R₀)
  exact ⟨Shrink.{0} R₀, inferInstance, hlocA, hnoethA, hdomA, R₀, toA,
    hE₀_sub, hsop_in, hdimA, htoA_zero, htoA_one, htoA_add, htoA_mul, htoA_neg, htoA_max, htoA_sop⟩

/- Section 3a: Opaque tower colimit giving IsBalancedBigCohenMacaulay -/

private lemma build_balanced_from_opaque_tower
    (D : Type u) [CommRing D] [IsLocalRing D]
    (Gen : ℕ → Type u)
    (Rel : ∀ n : ℕ, Submodule D (Gen n →₀ D))
    (baseGen : Gen 0)
    (stepInl : ∀ n : ℕ, Gen n → Gen (n + 1))
    (hRel_mono : ∀ (n : ℕ) {r : Gen n →₀ D}, r ∈ Rel n →
      Finsupp.lmapDomain D D (stepInl n) r ∈ Rel (n + 1))
    (hmod : ∀ (n : ℕ) (rs : List D), IsSystemOfParameters D rs →
      ∀ (k : ℕ) (hk : k < rs.length) (w : Gen n →₀ D) (v : Fin k → (Gen n →₀ D)),
      rs[k] • w - ∑ j : Fin k, (rs[j.1]'(Nat.lt_trans j.2 hk)) • v j ∈ Rel n →
      ∃ u : Fin k → Gen (n + 1),
        Finsupp.lmapDomain D D (stepInl n) w -
          ∑ j : Fin k, (rs[j.1]'(Nat.lt_trans j.2 hk)) • Finsupp.single (u j) 1 ∈ Rel (n + 1))
    (hno_collapse : ∀ (N : ℕ) (g0N : Gen N),
      (Nat.rec (motive := fun k => Gen k) baseGen (fun k g => stepInl k g) N = g0N) →
      ∀ (r : ℕ) (a : Fin r → D) (z : Fin r → (Gen N →₀ D)),
      (∀ s, a s ∈ maximalIdeal D) →
      Finsupp.single g0N (1 : D) - ∑ s : Fin r, a s • z s ∉ Rel N) :
    ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module D W), IsBalancedBigCohenMacaulay D W := by
  classical
  let emb : ∀ n : ℕ, (Gen n →₀ D) →ₗ[D] (Gen (n + 1) →₀ D) := fun n =>
    Finsupp.lmapDomain D D (stepInl n)
  let shiftGen : ∀ {m N : ℕ}, m ≤ N → Gen m → Gen N := by
    intro m N
    induction N generalizing m with
    | zero =>
      intro h g
      exact (Nat.eq_zero_of_le_zero h) ▸ g
    | succ N ih =>
      intro h g
      exact if hm : m ≤ N then stepInl N (ih hm g) else (show m = N + 1 by omega) ▸ g
  have hshiftGen_refl : ∀ (N : ℕ) (g : Gen N), shiftGen (le_refl N) g = g := by
    intro N g
    cases N with
    | zero => rfl
    | succ N =>
      change (if hm : N + 1 ≤ N then _ else _) = g
      split_ifs
      · omega
      · rfl
  have hshiftGen_succ_right : ∀ {m N : ℕ} (h : m ≤ N) (g : Gen m),
      shiftGen (Nat.le_succ_of_le h) g = stepInl N (shiftGen h g) := by
    intro m N h g
    change (if hm : m ≤ N then _ else _) = stepInl N (shiftGen h g)
    split_ifs
    rfl
  have hshiftGen_succ_left : ∀ {m N : ℕ} (h : m + 1 ≤ N) (g : Gen m),
      shiftGen h (stepInl m g) = shiftGen (Nat.le_of_succ_le h) g := by
    intro m N
    induction N with
    | zero => intro h; omega
    | succ N ih =>
      intro h g
      by_cases hm : m + 1 ≤ N
      · rw [hshiftGen_succ_right hm (stepInl m g),
          hshiftGen_succ_right (Nat.le_of_succ_le hm) g, ih hm g]
      · have hmeq : m = N := by omega
        subst hmeq
        rw [hshiftGen_refl (m + 1) (stepInl m g),
          hshiftGen_succ_right (le_refl m) g, hshiftGen_refl m g]
  have hshiftGen_base : ∀ (N : ℕ),
      Nat.rec (motive := fun k => Gen k) baseGen (fun k g => stepInl k g) N =
        shiftGen (Nat.zero_le N) baseGen := by
    intro N
    induction N with
    | zero => rfl
    | succ N ih =>
      rw [hshiftGen_succ_right (Nat.zero_le N) baseGen]
      exact congrArg (stepInl N) ih
  let shiftVec : ∀ {m N : ℕ}, m ≤ N → (Gen m →₀ D) →ₗ[D] (Gen N →₀ D) := fun h =>
    Finsupp.lmapDomain D D (shiftGen h)
  have hshiftVec_refl : ∀ (N : ℕ) (x : Gen N →₀ D), shiftVec (le_refl N) x = x := by
    intro N x
    change Finsupp.mapDomain (shiftGen (le_refl N)) x = x
    have hfun : (shiftGen (le_refl N) : Gen N → Gen N) = id := funext (hshiftGen_refl N)
    rw [hfun, Finsupp.mapDomain_id]
  have hshiftVec_succ_right : ∀ {m N : ℕ} (h : m ≤ N) (x : Gen m →₀ D),
      shiftVec (Nat.le_succ_of_le h) x = emb N (shiftVec h x) := by
    intro m N h x
    change Finsupp.mapDomain (shiftGen (Nat.le_succ_of_le h)) x =
      Finsupp.mapDomain (stepInl N) (Finsupp.mapDomain (shiftGen h) x)
    rw [← Finsupp.mapDomain_comp]
    congr 1
    exact funext (hshiftGen_succ_right h)
  have hshiftVec_rel : ∀ {m N : ℕ} (h : m ≤ N) {r : Gen m →₀ D}, r ∈ Rel m → shiftVec h r ∈ Rel N := by
    intro m N
    induction N with
    | zero =>
      intro h r hr
      have hm0 : m = 0 := Nat.eq_zero_of_le_zero h
      subst hm0
      rw [hshiftVec_refl 0 r]
      exact hr
    | succ N ih =>
      intro h r hr
      by_cases hm : m ≤ N
      · rw [hshiftVec_succ_right hm r]
        exact hRel_mono N (ih hm hr)
      · have hmeq : m = N + 1 := by omega
        subst hmeq
        rw [hshiftVec_refl (N + 1) r]
        exact hr
  let AllGen : Type u := Σ n : ℕ, Gen n
  let incAll : ∀ n : ℕ, (Gen n →₀ D) →ₗ[D] (AllGen →₀ D) := fun n =>
    Finsupp.lmapDomain D D (fun g : Gen n => (⟨n, g⟩ : AllGen))
  let idRelSet : Set (AllGen →₀ D) :=
    Set.range (fun p : Σ n : ℕ, Gen n =>
      Finsupp.single (⟨p.1, p.2⟩ : AllGen) (1 : D) -
        Finsupp.single (⟨p.1 + 1, stepInl p.1 p.2⟩ : AllGen) (1 : D))
  let stageRelSet : Set (AllGen →₀ D) :=
    Set.range (fun p : Σ n : ℕ, Rel n => incAll p.1 p.2.1)
  let RelAll : Submodule D (AllGen →₀ D) :=
    Submodule.span D (idRelSet ∪ stageRelSet)
  let W : Type u := (AllGen →₀ D) ⧸ RelAll
  let toW : ∀ n : ℕ, (Gen n →₀ D) →ₗ[D] W := fun n => RelAll.mkQ.comp (incAll n)
  have htoW_single_succ : ∀ (n : ℕ) (g : Gen n) (c : D),
      toW (n + 1) (Finsupp.single (stepInl n g) c) = toW n (Finsupp.single g c) := by
    intro n g c
    symm
    change RelAll.mkQ (Finsupp.mapDomain (fun x => (⟨n, x⟩ : AllGen)) (Finsupp.single g c)) =
      RelAll.mkQ (Finsupp.mapDomain (fun x => (⟨n + 1, x⟩ : AllGen)) (Finsupp.single (stepInl n g) c))
    rw [Finsupp.mapDomain_single, Finsupp.mapDomain_single, Submodule.mkQ_apply,
      Submodule.mkQ_apply, Submodule.Quotient.eq]
    have h1 : Finsupp.single (⟨n, g⟩ : AllGen) c - Finsupp.single (⟨n + 1, stepInl n g⟩ : AllGen) c =
        c • (Finsupp.single (⟨n, g⟩ : AllGen) (1 : D) -
          Finsupp.single (⟨n + 1, stepInl n g⟩ : AllGen) (1 : D)) := by
      rw [smul_sub, Finsupp.smul_single, Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [h1]
    exact RelAll.smul_mem c (Submodule.subset_span (Or.inl ⟨⟨n, g⟩, rfl⟩))
  have htoW_emb : ∀ (n : ℕ) (x : Gen n →₀ D), toW (n + 1) (emb n x) = toW n x := by
    intro n x
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add x₁ x₂ h₁ h₂ => rw [map_add, map_add, map_add, h₁, h₂]
    | single g c =>
      have hemb : emb n (Finsupp.single g c) = Finsupp.single (stepInl n g) c :=
        Finsupp.mapDomain_single
      rw [hemb]
      exact htoW_single_succ n g c
  have htoW_shift : ∀ {m N : ℕ} (h : m ≤ N) (x : Gen m →₀ D),
      toW N (shiftVec h x) = toW m x := by
    intro m N
    induction N with
    | zero =>
      intro h x
      have hm0 : m = 0 := Nat.eq_zero_of_le_zero h
      subst hm0
      rw [hshiftVec_refl 0 x]
    | succ N ih =>
      intro h x
      by_cases hm : m ≤ N
      · rw [hshiftVec_succ_right hm x, htoW_emb N, ih hm x]
      · have hmeq : m = N + 1 := by omega
        subst hmeq
        rw [hshiftVec_refl (N + 1) x]
  have htoW_rel : ∀ (n : ℕ) {r : Gen n →₀ D}, r ∈ Rel n → toW n r = 0 := by
    intro n r hr
    change RelAll.mkQ (incAll n r) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Submodule.subset_span (Or.inr ⟨⟨n, ⟨r, hr⟩⟩, rfl⟩)
  have hlift_W : ∀ w : W, ∃ (n : ℕ) (x : Gen n →₀ D), toW n x = w := by
    intro w
    induction w using Submodule.Quotient.induction_on with
    | _ z =>
      let N : ℕ := z.support.sup Sigma.fst
      have hle : ∀ p ∈ z.support, p.1 ≤ N := fun p hp => Finset.le_sup hp
      refine ⟨N, ∑ p ∈ z.support.attach,
        Finsupp.single (shiftGen (hle p.1 p.2) p.1.2) (z p.1), ?_⟩
      rw [map_sum]
      have hterm : ∀ p ∈ z.support.attach,
          toW N (Finsupp.single (shiftGen (hle p.1 p.2) p.1.2) (z p.1)) =
            RelAll.mkQ (Finsupp.single p.1 (z p.1)) := by
        intro p _
        have h1 : Finsupp.single (shiftGen (hle p.1 p.2) p.1.2) (z p.1) =
            shiftVec (hle p.1 p.2) (Finsupp.single p.1.2 (z p.1)) :=
          Finsupp.mapDomain_single.symm
        rw [h1, htoW_shift (hle p.1 p.2)]
        change RelAll.mkQ (Finsupp.mapDomain (fun g => (⟨p.1.1, g⟩ : AllGen))
          (Finsupp.single p.1.2 (z p.1))) = _
        rw [Finsupp.mapDomain_single]
      rw [Finset.sum_congr rfl hterm, ← map_sum]
      change RelAll.mkQ _ = RelAll.mkQ z
      congr 1
      have hsum : ∑ p ∈ z.support.attach, Finsupp.single p.1 (z p.1) = z := by
        rw [Finset.sum_attach z.support (fun p => Finsupp.single p (z p))]
        exact Finsupp.sum_single z
      exact hsum
  have hker_toW : ∀ (n : ℕ) (x : Gen n →₀ D), toW n x = 0 →
      ∃ (N : ℕ) (h : n ≤ N), shiftVec h x ∈ Rel N := by
    intro n x hx
    have hmem : incAll n x ∈ RelAll := (Submodule.Quotient.mk_eq_zero RelAll).mp hx
    dsimp only [RelAll] at hmem
    rw [Submodule.span_union, Submodule.mem_sup] at hmem
    obtain ⟨u₁, hu₁, u₂, hu₂, hu_eq⟩ := hmem
    obtain ⟨c₁, hc₁⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hu₁
    obtain ⟨c₂, hc₂⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hu₂
    let N : ℕ := max n (max (c₁.support.sup (fun p => p.1 + 1)) (c₂.support.sup (fun p => p.1)))
    have hnN : n ≤ N := le_max_left _ _
    refine ⟨N, hnN, ?_⟩
    let collapse : (AllGen →₀ D) →ₗ[D] ((Gen N →₀ D) ⧸ Rel N) :=
      Finsupp.lsum D fun p : AllGen =>
        if hp : p.1 ≤ N then (Rel N).mkQ.comp (Finsupp.lsingle (shiftGen hp p.2)) else 0
    have hcoll_single : ∀ (m : ℕ) (hm : m ≤ N) (g : Gen m) (a : D),
        collapse (Finsupp.single (⟨m, g⟩ : AllGen) a) =
          (Rel N).mkQ (Finsupp.single (shiftGen hm g) a) := by
      intro m hm g a
      change (Finsupp.lsum D _ (Finsupp.single (⟨m, g⟩ : AllGen) a)) = _
      rw [Finsupp.lsum_single]
      split_ifs with h
      · rfl
      · exact absurd hm h
    have hcoll_inc : ∀ (m : ℕ) (hm : m ≤ N) (v : Gen m →₀ D),
        collapse (incAll m v) = (Rel N).mkQ (shiftVec hm v) := by
      intro m hm v
      induction v using Finsupp.induction_linear with
      | zero => simp
      | add v₁ v₂ h₁ h₂ => rw [map_add, map_add, map_add, map_add, h₁, h₂]
      | single g a =>
        have hinc : incAll m (Finsupp.single g a) = Finsupp.single (⟨m, g⟩ : AllGen) a :=
          Finsupp.mapDomain_single
        have hsh : shiftVec hm (Finsupp.single g a) = Finsupp.single (shiftGen hm g) a :=
          Finsupp.mapDomain_single
        rw [hinc, hsh, hcoll_single m hm g a]
    have hcoll_u₁ : collapse u₁ = 0 := by
      rw [← hc₁]
      change collapse (∑ p ∈ c₁.support, c₁ p •
        (Finsupp.single (⟨p.1, p.2⟩ : AllGen) (1 : D) -
          Finsupp.single (⟨p.1 + 1, stepInl p.1 p.2⟩ : AllGen) (1 : D))) = 0
      rw [map_sum]
      refine Finset.sum_eq_zero fun p hp => ?_
      rw [map_smul, map_sub]
      have hp1 : p.1 + 1 ≤ N :=
        (Finset.le_sup (f := fun q : Σ k : ℕ, Gen k => q.1 + 1) hp).trans
          ((le_max_left _ _).trans (le_max_right _ _))
      have hp0 : p.1 ≤ N := Nat.le_of_succ_le hp1
      rw [hcoll_single p.1 hp0 p.2 1, hcoll_single (p.1 + 1) hp1 (stepInl p.1 p.2) 1,
        hshiftGen_succ_left hp1 p.2, sub_self, smul_zero]
    have hcoll_u₂ : collapse u₂ = 0 := by
      rw [← hc₂]
      change collapse (∑ p ∈ c₂.support, c₂ p • incAll p.1 p.2.1) = 0
      rw [map_sum]
      refine Finset.sum_eq_zero fun p hp => ?_
      rw [map_smul]
      have hp0 : p.1 ≤ N :=
        (Finset.le_sup (f := fun q : Σ k : ℕ, Rel k => q.1) hp).trans
          ((le_max_right _ _).trans (le_max_right _ _))
      rw [hcoll_inc p.1 hp0 p.2.1]
      have h0 : (Rel N).mkQ (shiftVec hp0 p.2.1) = 0 :=
        (Submodule.Quotient.mk_eq_zero (Rel N)).mpr (hshiftVec_rel hp0 p.2.2)
      rw [h0, smul_zero]
    have hcoll_x : collapse (incAll n x) = 0 := by
      rw [← hu_eq, map_add, hcoll_u₁, hcoll_u₂, add_zero]
    rw [hcoll_inc n hnN x] at hcoll_x
    exact (Submodule.Quotient.mk_eq_zero (Rel N)).mp hcoll_x
  have hweak_reg : ∀ rs : List D, IsSystemOfParameters D rs →
      RingTheory.Sequence.IsWeaklyRegular W rs := by
    intro rs hrs
    refine ⟨fun k hk => ?_⟩
    intro q₁ q₂ hq
    induction q₁ using Submodule.Quotient.induction_on with
    | _ w₁ =>
      induction q₂ using Submodule.Quotient.induction_on with
      | _ w₂ =>
        rw [Submodule.Quotient.eq]
        have hsub_mem : rs[k] • (w₁ - w₂) ∈ Ideal.ofList (rs.take k) • (⊤ : Submodule D W) := by
          rw [smul_sub]
          have hq' : Submodule.Quotient.mk (p := Ideal.ofList (rs.take k) • (⊤ : Submodule D W))
              (rs[k] • w₁) =
              Submodule.Quotient.mk (p := Ideal.ofList (rs.take k) • (⊤ : Submodule D W))
              (rs[k] • w₂) := hq
          exact (Submodule.Quotient.eq _).mp hq'
        obtain ⟨vW, hvW⟩ := (mem_ofList_smul_top_iff (rs.take k) (rs[k] • (w₁ - w₂))).mp hsub_mem
        obtain ⟨n₀, x₀, hx₀⟩ := hlift_W (w₁ - w₂)
        have hv_ex : ∀ j : Fin (rs.take k).length, ∃ (nj : ℕ) (vj : Gen nj →₀ D),
            toW nj vj = vW j := fun j => hlift_W (vW j)
        choose nv xv hxv using hv_ex
        let m₀ : ℕ := max n₀ (Finset.univ.sup nv)
        have hn₀m : n₀ ≤ m₀ := le_max_left _ _
        have hnvm : ∀ j : Fin (rs.take k).length, nv j ≤ m₀ := fun j =>
          (Finset.le_sup (Finset.mem_univ j)).trans (le_max_right _ _)
        have htake_len : (rs.take k).length = k := List.length_take_of_le (le_of_lt hk)
        let wM : Gen m₀ →₀ D := shiftVec hn₀m x₀
        let vM : Fin k → (Gen m₀ →₀ D) := fun j =>
          shiftVec (hnvm ⟨j.1, by omega⟩) (xv ⟨j.1, by omega⟩)
        have hwM_eq : toW m₀ wM = w₁ - w₂ := by rw [htoW_shift hn₀m x₀, hx₀]
        have hvM_eq : ∀ j : Fin k, toW m₀ (vM j) = vW ⟨j.1, by omega⟩ := fun j => by
          rw [htoW_shift (hnvm ⟨j.1, by omega⟩), hxv ⟨j.1, by omega⟩]
        have hrelW : toW m₀ (rs[k] • wM -
            ∑ j : Fin k, (rs[j.1]'(Nat.lt_trans j.2 hk)) • vM j) = 0 := by
          rw [map_sub, map_smul, map_sum, hwM_eq]
          have hsumW : ∑ j : Fin k, toW m₀ ((rs[j.1]'(Nat.lt_trans j.2 hk)) • vM j) =
              ∑ j : Fin (rs.take k).length, (rs.take k)[j] • vW j := by
            let eFin : Fin k ≃ Fin (rs.take k).length := finCongr htake_len.symm
            rw [← Equiv.sum_comp eFin.symm]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [map_smul, hvM_eq]
            simp [eFin, List.getElem_take]
          rw [hsumW, ← hvW, sub_self]
        obtain ⟨N, hm₀N, hrelN⟩ := hker_toW m₀ _ hrelW
        let wN : Gen N →₀ D := shiftVec hm₀N wM
        let vN : Fin k → (Gen N →₀ D) := fun j => shiftVec hm₀N (vM j)
        have hrelN' : rs[k] • wN -
            ∑ j : Fin k, (rs[j.1]'(Nat.lt_trans j.2 hk)) • vN j ∈ Rel N := by
          have heq : shiftVec hm₀N (rs[k] • wM -
              ∑ j : Fin k, (rs[j.1]'(Nat.lt_trans j.2 hk)) • vM j) =
              rs[k] • wN - ∑ j : Fin k, (rs[j.1]'(Nat.lt_trans j.2 hk)) • vN j := by
            rw [map_sub, map_smul, map_sum]
            congr 1
            refine Finset.sum_congr rfl fun j _ => map_smul _ _ _
          rwa [← heq]
        obtain ⟨u, hu⟩ := hmod N rs hrs k hk wN vN hrelN'
        have huW : toW (N + 1) (emb N wN -
            ∑ j : Fin k, (rs[j.1]'(Nat.lt_trans j.2 hk)) • Finsupp.single (u j) 1) = 0 :=
          htoW_rel (N + 1) hu
        rw [map_sub, map_sum, htoW_emb N wN, htoW_shift hm₀N wM, hwM_eq] at huW
        have hsumU : ∑ j : Fin k, toW (N + 1) ((rs[j.1]'(Nat.lt_trans j.2 hk)) •
            Finsupp.single (u j) 1) =
            ∑ j : Fin k, (rs[j.1]'(Nat.lt_trans j.2 hk)) •
              toW (N + 1) (Finsupp.single (u j) 1) :=
          Finset.sum_congr rfl fun j _ => map_smul _ _ _
        rw [hsumU] at huW
        have hw_eq : w₁ - w₂ = ∑ j : Fin k,
            (rs[j.1]'(Nat.lt_trans j.2 hk)) • toW (N + 1) (Finsupp.single (u j) 1) :=
          sub_eq_zero.mp huW
        rw [mem_ofList_smul_top_iff]
        refine ⟨fun j => toW (N + 1) (Finsupp.single (u ⟨j.1, by omega⟩) 1), ?_⟩
        rw [hw_eq]
        let eFin : Fin k ≃ Fin (rs.take k).length := finCongr htake_len.symm
        rw [← Equiv.sum_comp eFin.symm]
        refine Finset.sum_congr rfl fun j _ => ?_
        have hj : eFin.symm j = ⟨j.1, by omega⟩ := rfl
        rw [hj]
        simp [List.getElem_take]
  have hsmul_W_ne_top : maximalIdeal D • (⊤ : Submodule D W) ≠ ⊤ := by
    intro htop
    have h1mem : toW 0 (Finsupp.single baseGen (1 : D)) ∈
        maximalIdeal D • (⊤ : Submodule D W) := by
      rw [htop]; trivial
    have h1sum : ∃ (r : ℕ) (a : Fin r → D) (v : Fin r → W),
        (∀ s : Fin r, a s ∈ maximalIdeal D) ∧
          toW 0 (Finsupp.single baseGen (1 : D)) = ∑ s : Fin r, a s • v s := by
      refine Submodule.smul_induction_on h1mem ?_ ?_
      · intro a ha v _
        exact ⟨1, fun _ => a, fun _ => v, fun _ => ha, by simp⟩
      · rintro x y ⟨r₁, a₁, v₁, ha₁, hx⟩ ⟨r₂, a₂, v₂, ha₂, hy⟩
        refine ⟨r₁ + r₂, Fin.append a₁ a₂, Fin.append v₁ v₂, fun s => ?_, ?_⟩
        · refine Fin.addCases (fun i => ?_) (fun j => ?_) s
          · simpa [Fin.append_left] using ha₁ i
          · simpa [Fin.append_right] using ha₂ j
        · rw [hx, hy, Fin.sum_univ_add]
          congr 1
          · refine Finset.sum_congr rfl fun i _ => by simp [Fin.append_left]
          · refine Finset.sum_congr rfl fun j _ => by simp [Fin.append_right]
    obtain ⟨r, a, vW, ha_max, h1eq⟩ := h1sum
    have hv_ex : ∀ s : Fin r, ∃ (ns : ℕ) (vs : Gen ns →₀ D), toW ns vs = vW s :=
      fun s => hlift_W (vW s)
    choose nv zv hzv using hv_ex
    let n₀ : ℕ := Finset.univ.sup nv
    have hnv_le : ∀ s : Fin r, nv s ≤ n₀ := fun s => Finset.le_sup (Finset.mem_univ s)
    let e₀ : Gen n₀ →₀ D := shiftVec (Nat.zero_le n₀) (Finsupp.single baseGen (1 : D))
    let z₀ : Fin r → (Gen n₀ →₀ D) := fun s => shiftVec (hnv_le s) (zv s)
    have hzeroW : toW n₀ (e₀ - ∑ s : Fin r, a s • z₀ s) = 0 := by
      rw [map_sub, map_sum, htoW_shift (Nat.zero_le n₀)]
      have hsum : ∑ s : Fin r, toW n₀ (a s • z₀ s) = ∑ s : Fin r, a s • vW s := by
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [map_smul, htoW_shift (hnv_le s), hzv s]
      rw [hsum, ← h1eq, sub_self]
    obtain ⟨N, hn₀N, hrelN⟩ := hker_toW n₀ _ hzeroW
    let eN : Gen N →₀ D := shiftVec hn₀N e₀
    let zN : Fin r → (Gen N →₀ D) := fun s => shiftVec hn₀N (z₀ s)
    have hcontra : eN - ∑ s : Fin r, a s • zN s ∈ Rel N := by
      have heq : shiftVec hn₀N (e₀ - ∑ s : Fin r, a s • z₀ s) =
          eN - ∑ s : Fin r, a s • zN s := by
        rw [map_sub, map_sum]
        congr 1
        refine Finset.sum_congr rfl fun s _ => map_smul _ _ _
      rwa [← heq]
    have heN_single : eN = Finsupp.single (shiftGen (Nat.zero_le N) baseGen) (1 : D) := by
      change shiftVec hn₀N (shiftVec (Nat.zero_le n₀) (Finsupp.single baseGen 1)) = _
      have h1 : shiftVec (Nat.zero_le n₀) (Finsupp.single baseGen (1 : D)) =
          Finsupp.single (shiftGen (Nat.zero_le n₀) baseGen) 1 := Finsupp.mapDomain_single
      rw [h1]
      have h2 : shiftVec hn₀N (Finsupp.single (shiftGen (Nat.zero_le n₀) baseGen) (1 : D)) =
          Finsupp.single (shiftGen hn₀N (shiftGen (Nat.zero_le n₀) baseGen)) 1 :=
        Finsupp.mapDomain_single
      rw [h2]
      congr 1
      have hshiftGen_trans : ∀ {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) (g : Gen a),
          shiftGen hbc (shiftGen hab g) = shiftGen (hab.trans hbc) g := by
        intro a b c
        induction c with
        | zero =>
          intro hab hbc g
          have hb0 : b = 0 := Nat.eq_zero_of_le_zero hbc
          subst hb0
          have ha0 : a = 0 := Nat.eq_zero_of_le_zero hab
          subst ha0
          rw [hshiftGen_refl 0, hshiftGen_refl 0]
        | succ k ih =>
          intro hab hbc g
          by_cases hbk : b ≤ k
          · rw [hshiftGen_succ_right hbk, hshiftGen_succ_right (hab.trans hbk), ih hab hbk g]
          · have hbe : b = k + 1 := by omega
            subst hbe
            rw [hshiftGen_refl (k + 1)]
      exact hshiftGen_trans (Nat.zero_le n₀) hn₀N baseGen
    rw [heN_single] at hcontra
    exact hno_collapse N (shiftGen (Nat.zero_le N) baseGen) (hshiftGen_base N) r a zN ha_max hcontra
  refine ⟨W, inferInstance, inferInstance, hsmul_W_ne_top, fun rs hrs => ⟨hweak_reg rs hrs, ?_⟩⟩
  intro htop
  apply hsmul_W_ne_top
  rw [eq_top_iff]
  have hle : Ideal.ofList rs ≤ maximalIdeal D := by
    rw [Ideal.span_le]
    intro r hr
    exact hrs.mem_maximalIdeal hr
  exact htop.le.trans (Submodule.smul_mono hle le_rfl)

/- Section 3b: Opaque non-collapse proof via countable relation ancestry and Type 0 descent -/

private lemma no_collapse_from_opaque_tower
    (hType0 : ∀ (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A],
      (2 : WithBot ℕ∞) ≤ ringKrullDim A →
      ∃ (W : Type) (_ : AddCommGroup W) (_ : Module A W), IsBalancedBigCohenMacaulay A W)
    (D : Type u) [CommRing D] [IsLocalRing D] [IsNoetherianRing D] [IsDomain D]
    (d : ℕ) (hd : ringKrullDim D = (d : WithBot ℕ∞)) (hd2 : 2 ≤ d)
    (Gen : ℕ → Type u)
    (Rel : ∀ n : ℕ, Submodule D (Gen n →₀ D))
    (baseGen : Gen 0)
    (hRel0 : Rel 0 = ⊥)
    (Idx : ℕ → Type u)
    (idxRs : ∀ n, Idx n → List D)
    (idxSop : ∀ n (ι : Idx n), IsSystemOfParameters D (idxRs n ι))
    (idxK : ∀ n (ι : Idx n), Fin (idxRs n ι).length)
    (idxW : ∀ n, Idx n → (Gen n →₀ D))
    (idxV : ∀ n (ι : Idx n), Fin (idxK n ι).1 → (Gen n →₀ D))
    (idxHrel : ∀ n (ι : Idx n),
      (idxRs n ι)[idxK n ι] • idxW n ι -
        ∑ j : Fin (idxK n ι).1,
          ((idxRs n ι)[j.1]'(Nat.lt_trans j.2 (idxK n ι).2)) • idxV n ι j ∈ Rel n)
    (stepInl : ∀ n : ℕ, Gen n → Gen (n + 1))
    (stepInr : ∀ n (ι : Idx n), Fin (idxK n ι).1 → Gen (n + 1))
    (hstepInl_inj : ∀ n : ℕ, Function.Injective (stepInl n))
    (hrecGen : ∀ (n : ℕ) {α : Type} (f₁ : Gen n → α)
      (f₂ : ∀ ι : Idx n, Fin (idxK n ι).1 → α),
      ∃ ψ : Gen (n + 1) → α,
        (∀ g, ψ (stepInl n g) = f₁ g) ∧ (∀ ι j, ψ (stepInr n ι j) = f₂ ι j))
    (hRel_succ : ∀ n : ℕ,
      Rel (n + 1) =
        Submodule.map (Finsupp.lmapDomain D D (stepInl n)) (Rel n) ⊔
          Submodule.span D (Set.range (fun ι : Idx n =>
            Finsupp.lmapDomain D D (stepInl n) (idxW n ι) -
              ∑ j : Fin (idxK n ι).1,
                ((idxRs n ι)[j.1]'(Nat.lt_trans j.2 (idxK n ι).2)) •
                  Finsupp.single (stepInr n ι j) 1)))
    (N : ℕ) (g0N : Gen N)
    (hg0N : Nat.rec (motive := fun k => Gen k) baseGen (fun k g => stepInl k g) N = g0N)
    (r : ℕ) (a : Fin r → D) (zN : Fin r → (Gen N →₀ D))
    (ha_max : ∀ s, a s ∈ maximalIdeal D)
    (hcontra : Finsupp.single g0N (1 : D) - ∑ s : Fin r, a s • zN s ∈ Rel N) :
    False := by
  classical
  let emb : ∀ n : ℕ, (Gen n →₀ D) →ₗ[D] (Gen (n + 1) →₀ D) := fun n =>
    Finsupp.lmapDomain D D (stepInl n)
  let newRel : ∀ (n : ℕ) (ι : Idx n), Gen (n + 1) →₀ D := fun n ι =>
    emb n (idxW n ι) -
      ∑ j : Fin (idxK n ι).1,
        ((idxRs n ι)[j.1]'(Nat.lt_trans j.2 (idxK n ι).2)) • Finsupp.single (stepInr n ι j) 1
  let coeffSet : ∀ {G : Type u}, (G →₀ D) → Set D := fun x =>
    (x : _ → D) '' (x.support : Set _)
  have hcoeff_count : ∀ {G : Type u} (x : G →₀ D), (coeffSet x).Countable := fun x =>
    x.support.countable_toSet.image _
  have hrel_decomp : ∀ (n : ℕ) (x : Gen (n + 1) →₀ D), x ∈ Rel (n + 1) →
      ∃ (y : Gen n →₀ D) (_ : y ∈ Rel n) (c : Idx n →₀ D),
        emb n y + ∑ ι ∈ c.support, c ι • newRel n ι = x := by
    intro n x hx
    rw [hRel_succ n, Submodule.mem_sup] at hx
    obtain ⟨u, hu, v, hv, huv⟩ := hx
    obtain ⟨y, hy, rfl⟩ := hu
    obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hv
    refine ⟨y, hy, c, ?_⟩
    rw [← huv, ← hc]
    rfl
  let ancRel : ∀ (n : ℕ) (x : Gen n →₀ D), x ∈ Rel n → Set D × Set (List D) :=
    Nat.rec (motive := fun n => ∀ (x : Gen n →₀ D), x ∈ Rel n → Set D × Set (List D))
      (fun _ _ => (∅, ∅))
      (fun n ih x hx =>
        let hex := hrel_decomp n x hx
        let y := hex.choose
        let hy := hex.choose_spec.choose
        let c := hex.choose_spec.choose_spec.choose
        let ancY := ih y hy
        let ancC1 : Set D :=
          ⋃ ι : c.support,
            (Set.range (fun j : Fin (idxRs n ι.1).length => (idxRs n ι.1)[j]) ∪
              coeffSet (idxW n ι.1) ∪
              (⋃ j : Fin (idxK n ι.1).1, coeffSet (idxV n ι.1 j)) ∪
              (ih _ (idxHrel n ι.1)).1)
        let ancC2 : Set (List D) :=
          ⋃ ι : c.support, ({idxRs n ι.1} ∪ (ih _ (idxHrel n ι.1)).2)
        (ancY.1 ∪ coeffSet y ∪ coeffSet c ∪ ancC1, ancY.2 ∪ ancC2))
  have hancRel_props : ∀ (n : ℕ) (x : Gen n →₀ D) (hx : x ∈ Rel n),
      (ancRel n x hx).1.Countable ∧ (ancRel n x hx).2.Countable ∧
        ∀ rs ∈ (ancRel n x hx).2, IsSystemOfParameters D rs := by
    intro n
    induction n with
    | zero =>
      intro x hx
      exact ⟨Set.countable_empty, Set.countable_empty, fun _ h => False.elim h⟩
    | succ n ih =>
      intro x hx
      let hex := hrel_decomp n x hx
      let y := hex.choose
      let hy := hex.choose_spec.choose
      let c := hex.choose_spec.choose_spec.choose
      have hyP := ih y hy
      have hιP : ∀ ι : c.support, (ancRel n _ (idxHrel n ι.1)).1.Countable ∧
          (ancRel n _ (idxHrel n ι.1)).2.Countable ∧
          ∀ rs ∈ (ancRel n _ (idxHrel n ι.1)).2, IsSystemOfParameters D rs :=
        fun ι => ih _ (idxHrel n ι.1)
      refine ⟨?_, ?_, ?_⟩
      · refine ((hyP.1.union (hcoeff_count y)).union (hcoeff_count c)).union ?_
        refine Set.countable_iUnion fun ι => ?_
        refine (((Set.countable_range _).union (hcoeff_count _)).union ?_).union (hιP ι).1
        exact Set.countable_iUnion fun j => hcoeff_count _
      · refine hyP.2.1.union ?_
        refine Set.countable_iUnion fun ι => ?_
        exact (Set.countable_singleton _).union (hιP ι).2.1
      · intro rs hrs
        rcases hrs with hrs | hrs
        · exact hyP.2.2 rs hrs
        · obtain ⟨ι, hι⟩ := Set.mem_iUnion.mp hrs
          rcases hι with rfl | hι
          · exact idxSop n ι.1
          · exact (hιP ι).2.2 rs hι
  let E₀ : Set D :=
    Set.range a ∪ (⋃ s : Fin r, coeffSet (zN s)) ∪ (ancRel N _ hcontra).1
  let Sops₀ : Set (List D) := (ancRel N _ hcontra).2
  have hancP := hancRel_props N _ hcontra
  have hE₀_count : E₀.Countable :=
    ((Set.countable_range a).union (Set.countable_iUnion fun s => hcoeff_count (zN s))).union
      hancP.1
  obtain ⟨A, _, _, _, _, R₀, toA, hE₀_sub, hsop_in, hdimA,
      htoA_zero, htoA_one, htoA_add, htoA_mul, htoA_neg, htoA_max, htoA_sop⟩ :=
    exists_type0_local_domain_with_sops D d hd E₀ hE₀_count Sops₀ hancP.2.1 hancP.2.2
  have hdimA2 : (2 : WithBot ℕ∞) ≤ ringKrullDim A := by
    rw [hdimA]
    exact WithBot.coe_le_coe.mpr (ENat.natCast_le_natCast.mpr hd2)
  obtain ⟨W₀, _, _, hW₀⟩ := hType0 A hdimA2
  have hw₀_ex : ∃ w₀ : W₀, w₀ ∉ maximalIdeal A • (⊤ : Submodule A W₀) := by
    by_contra hall
    push Not at hall
    exact hW₀.smul_top_ne_top (eq_top_iff.mpr fun w _ => hall w)
  obtain ⟨w₀, hw₀⟩ := hw₀_ex
  let VecInR₀ : ∀ {G : Type u}, (G →₀ D) → Prop := fun x => ∀ g, x g ∈ R₀
  have hVecInR₀_of_coeff : ∀ {G : Type u} (x : G →₀ D), coeffSet x ⊆ (R₀ : Set D) → VecInR₀ x := by
    intro G x hx g
    by_cases hg : g ∈ x.support
    · exact hx ⟨g, hg, rfl⟩
    · rw [Finsupp.notMem_support_iff.mp hg]
      exact R₀.zero_mem
  have hVecInR₀_add : ∀ {G : Type u} {x y : G →₀ D}, VecInR₀ x → VecInR₀ y → VecInR₀ (x + y) :=
    fun hx hy g => R₀.add_mem (hx g) (hy g)
  have hVecInR₀_smul : ∀ {G : Type u} {c : D} {x : G →₀ D}, c ∈ R₀ → VecInR₀ x → VecInR₀ (c • x) :=
    fun hc hx g => R₀.mul_mem hc (hx g)
  have hVecInR₀_sub : ∀ {G : Type u} {x y : G →₀ D}, VecInR₀ x → VecInR₀ y → VecInR₀ (x - y) :=
    fun hx hy g => R₀.sub_mem (hx g) (hy g)
  have hVecInR₀_sum : ∀ {G : Type u} {ι : Type} (s : Finset ι) (f : ι → (G →₀ D)),
      (∀ i ∈ s, VecInR₀ (f i)) → VecInR₀ (∑ i ∈ s, f i) := by
    intro G ι s f hf
    induction s using Finset.induction_on with
    | empty => intro g; simp [R₀.zero_mem]
    | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact hVecInR₀_add (hf a (Finset.mem_insert_self a s))
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))
  have hVecInR₀_sum_u : ∀ {G : Type u} {ι : Type u} (s : Finset ι) (f : ι → (G →₀ D)),
      (∀ i ∈ s, VecInR₀ (f i)) → VecInR₀ (∑ i ∈ s, f i) := by
    intro G ι s f hf
    induction s using Finset.induction_on with
    | empty => intro g; simp [R₀.zero_mem]
    | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact hVecInR₀_add (hf a (Finset.mem_insert_self a s))
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))
  have hVecInR₀_single : ∀ {G : Type u} (g : G) {c : D}, c ∈ R₀ → VecInR₀ (Finsupp.single g c) := by
    intro G g c hc g'
    by_cases h : g = g'
    · subst h; simpa using hc
    · rw [Finsupp.single_eq_of_ne (Ne.symm h)]; exact R₀.zero_mem
  have hVecInR₀_emb : ∀ (n : ℕ) {x : Gen n →₀ D}, VecInR₀ x → VecInR₀ (emb n x) := by
    intro n x hx g
    by_cases hg : ∃ g' : Gen n, stepInl n g' = g
    · obtain ⟨g', rfl⟩ := hg
      change Finsupp.mapDomain (stepInl n) x (stepInl n g') ∈ R₀
      rw [Finsupp.mapDomain_apply (hstepInl_inj n)]
      exact hx g'
    · have h0 : emb n x g = 0 := by
        change Finsupp.mapDomain (stepInl n) x g = 0
        exact Finsupp.mapDomain_of_notMem_range x g hg
      rw [h0]
      exact R₀.zero_mem
  let eval : ∀ {G : Type u}, (G → W₀) → (G →₀ D) → W₀ := fun ψ x =>
    x.sum fun g c => toA c • ψ g
  have heval_zero : ∀ {G : Type u} (ψ : G → W₀), eval ψ 0 = 0 := fun _ => Finsupp.sum_zero_index
  have heval_single : ∀ {G : Type u} (ψ : G → W₀) (g : G) (c : D),
      eval ψ (Finsupp.single g c) = toA c • ψ g := fun ψ g c => by
    dsimp only [eval]
    exact Finsupp.sum_single_index (by rw [htoA_zero, zero_smul])
  have heval_add : ∀ {G : Type u} (ψ : G → W₀) {x y : G →₀ D},
      VecInR₀ x → VecInR₀ y → eval ψ (x + y) = eval ψ x + eval ψ y := by
    intro G ψ x y hx hy
    dsimp only [eval]
    let s : Finset G := x.support ∪ y.support
    have hxy : (x + y).support ⊆ s := Finsupp.support_add
    rw [Finsupp.sum_of_support_subset (x + y) hxy _ (fun g _ => by rw [htoA_zero, zero_smul]),
      Finsupp.sum_of_support_subset x Finset.subset_union_left _
        (fun g _ => by rw [htoA_zero, zero_smul]),
      Finsupp.sum_of_support_subset y Finset.subset_union_right _
        (fun g _ => by rw [htoA_zero, zero_smul]),
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Finsupp.add_apply, htoA_add (hx g) (hy g), add_smul]
  have heval_smul : ∀ {G : Type u} (ψ : G → W₀) {c : D} {x : G →₀ D},
      c ∈ R₀ → VecInR₀ x → eval ψ (c • x) = toA c • eval ψ x := by
    intro G ψ c x hc hx
    dsimp only [eval]
    rw [Finsupp.sum_of_support_subset (c • x) Finsupp.support_smul _
      (fun g _ => by rw [htoA_zero, zero_smul])]
    change ∑ g ∈ x.support, toA (c * x g) • ψ g = toA c • ∑ g ∈ x.support, toA (x g) • ψ g
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [htoA_mul hc (hx g), mul_smul]
  have heval_neg : ∀ {G : Type u} (ψ : G → W₀) {x : G →₀ D},
      VecInR₀ x → eval ψ (-x) = -eval ψ x := by
    intro G ψ x hx
    have h1 : -x = (-1 : D) • x := by ext g; simp
    rw [h1, heval_smul ψ (R₀.neg_mem R₀.one_mem) hx, htoA_neg R₀.one_mem, htoA_one, neg_one_smul]
  have heval_sub : ∀ {G : Type u} (ψ : G → W₀) {x y : G →₀ D},
      VecInR₀ x → VecInR₀ y → eval ψ (x - y) = eval ψ x - eval ψ y := by
    intro G ψ x y hx hy
    rw [sub_eq_add_neg, heval_add ψ hx (fun g => R₀.neg_mem (hy g)), heval_neg ψ hy,
      sub_eq_add_neg]
  have heval_sum : ∀ {G : Type u} {ι : Type} (ψ : G → W₀) (s : Finset ι) (f : ι → (G →₀ D)),
      (∀ i ∈ s, VecInR₀ (f i)) → eval ψ (∑ i ∈ s, f i) = ∑ i ∈ s, eval ψ (f i) := by
    intro G ι ψ s f hf
    induction s using Finset.induction_on with
    | empty => simp [heval_zero]
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        heval_add ψ (hf a (Finset.mem_insert_self a s))
          (hVecInR₀_sum s f fun i hi => hf i (Finset.mem_insert_of_mem hi)),
        ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]
  have heval_sum_u : ∀ {G : Type u} {ι : Type u} (ψ : G → W₀) (s : Finset ι) (f : ι → (G →₀ D)),
      (∀ i ∈ s, VecInR₀ (f i)) → eval ψ (∑ i ∈ s, f i) = ∑ i ∈ s, eval ψ (f i) := by
    intro G ι ψ s f hf
    induction s using Finset.induction_on with
    | empty => simp [heval_zero]
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        heval_add ψ (hf a (Finset.mem_insert_self a s))
          (hVecInR₀_sum_u s f fun i hi => hf i (Finset.mem_insert_of_mem hi)),
        ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]
  let GoodIdx : ∀ (n : ℕ), Idx n → Prop := fun n ι =>
    idxRs n ι ∈ Sops₀ ∧ VecInR₀ (idxW n ι) ∧ (∀ j, VecInR₀ (idxV n ι j)) ∧
      (ancRel n _ (idxHrel n ι)).1 ⊆ (R₀ : Set D) ∧ (ancRel n _ (idxHrel n ι)).2 ⊆ Sops₀
  have hψ_ex : ∀ n : ℕ, ∃ ψ : Gen n → W₀,
      ψ (Nat.rec (motive := fun k => Gen k) baseGen (fun k g => stepInl k g) n) = w₀ ∧
      ∀ (x : Gen n →₀ D) (hx : x ∈ Rel n),
        (ancRel n x hx).1 ⊆ (R₀ : Set D) → (ancRel n x hx).2 ⊆ Sops₀ → eval ψ x = 0 := by
    intro n
    induction n with
    | zero =>
      refine ⟨fun _ => w₀, rfl, fun x hx _ _ => ?_⟩
      rw [hRel0] at hx
      have hx0 : x = 0 := hx
      rw [hx0, heval_zero]
    | succ n ih =>
      obtain ⟨ψn, hψn0, hψn⟩ := ih
      have hsol : ∀ (ι : Idx n), GoodIdx n ι →
          ∃ u : Fin (idxK n ι).1 → W₀,
            eval ψn (idxW n ι) =
              ∑ j : Fin (idxK n ι).1,
                toA ((idxRs n ι)[j.1]'(Nat.lt_trans j.2 (idxK n ι).2)) • u j := by
        intro ι hι
        rcases hι with ⟨hrs_mem, hw_in, hv_in, hanc1, hanc2⟩
        have hrel_eval : eval ψn ((idxRs n ι)[idxK n ι] • idxW n ι -
            ∑ j : Fin (idxK n ι).1,
              ((idxRs n ι)[j.1]'(Nat.lt_trans j.2 (idxK n ι).2)) • idxV n ι j) = 0 :=
          hψn _ (idxHrel n ι) hanc1 hanc2
        have hrk_in : (idxRs n ι)[idxK n ι] ∈ R₀ :=
          hsop_in (idxRs n ι) hrs_mem (idxRs n ι)[idxK n ι] (List.getElem_mem (idxK n ι).2)
        have hr_in : ∀ (idx : ℕ) (hidx : idx < (idxRs n ι).length), (idxRs n ι)[idx] ∈ R₀ :=
          fun idx hidx => hsop_in (idxRs n ι) hrs_mem (idxRs n ι)[idx] (List.getElem_mem hidx)
        rw [heval_sub ψn (hVecInR₀_smul hrk_in hw_in)
              (hVecInR₀_sum _ _ fun j _ => hVecInR₀_smul (hr_in j.1 _) (hv_in j)),
            heval_smul ψn hrk_in hw_in,
            heval_sum ψn _ _ fun j _ => hVecInR₀_smul (hr_in j.1 _) (hv_in j)] at hrel_eval
        have hsum_eq : ∑ j : Fin (idxK n ι).1,
            eval ψn (((idxRs n ι)[j.1]'(Nat.lt_trans j.2 (idxK n ι).2)) • idxV n ι j) =
            ∑ j : Fin (idxK n ι).1,
              toA ((idxRs n ι)[j.1]'(Nat.lt_trans j.2 (idxK n ι).2)) • eval ψn (idxV n ι j) :=
          Finset.sum_congr rfl fun j _ => heval_smul ψn (hr_in j.1 _) (hv_in j)
        rw [hsum_eq] at hrel_eval
        have hsmul_eq : toA (idxRs n ι)[idxK n ι] • eval ψn (idxW n ι) =
            ∑ j : Fin (idxK n ι).1,
              toA ((idxRs n ι)[j.1]'(Nat.lt_trans j.2 (idxK n ι).2)) • eval ψn (idxV n ι j) :=
          sub_eq_zero.mp hrel_eval
        let rsA : List A := (idxRs n ι).map toA
        have hrsA : IsSystemOfParameters A rsA := htoA_sop (idxRs n ι) hrs_mem
        have hregA : RingTheory.Sequence.IsRegular W₀ rsA := hW₀.isRegular rsA hrsA
        have hkA : (idxK n ι).1 < rsA.length := by simp [rsA, (idxK n ι).2]
        have htake_len : (rsA.take (idxK n ι).1).length = (idxK n ι).1 :=
          List.length_take_of_le (le_of_lt hkA)
        have hmem_prev : rsA[(idxK n ι).1] • eval ψn (idxW n ι) ∈
            Ideal.ofList (rsA.take (idxK n ι).1) • (⊤ : Submodule A W₀) := by
          rw [mem_ofList_smul_top_iff]
          refine ⟨fun j => eval ψn (idxV n ι ⟨j.1, by omega⟩), ?_⟩
          have hlhs : rsA[(idxK n ι).1] = toA (idxRs n ι)[idxK n ι] := by simp [rsA]
          rw [hlhs, hsmul_eq]
          let eFin : Fin (idxK n ι).1 ≃ Fin (rsA.take (idxK n ι).1).length :=
            finCongr htake_len.symm
          rw [← Equiv.sum_comp eFin.symm]
          refine Finset.sum_congr rfl fun j _ => ?_
          have hj : eFin.symm j = ⟨j.1, by omega⟩ := rfl
          rw [hj]
          simp [rsA, List.getElem_take]
        have hsmul_reg : IsSMulRegular
            (W₀ ⧸ (Ideal.ofList (rsA.take (idxK n ι).1) • (⊤ : Submodule A W₀)))
            rsA[(idxK n ι).1] := hregA.regular_mod_prev (idxK n ι).1 hkA
        have hquot0 : Submodule.Quotient.mk
            (p := Ideal.ofList (rsA.take (idxK n ι).1) • (⊤ : Submodule A W₀))
            (eval ψn (idxW n ι)) = 0 := by
          apply hsmul_reg
          dsimp only
          rw [smul_zero, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
          exact hmem_prev
        have hmem_w : eval ψn (idxW n ι) ∈
            Ideal.ofList (rsA.take (idxK n ι).1) • (⊤ : Submodule A W₀) :=
          (Submodule.Quotient.mk_eq_zero _).mp hquot0
        obtain ⟨u, hu⟩ := (mem_ofList_smul_top_iff (rsA.take (idxK n ι).1) _).mp hmem_w
        refine ⟨fun j => u ⟨j.1, by omega⟩, ?_⟩
        rw [hu]
        let eFin : Fin (idxK n ι).1 ≃ Fin (rsA.take (idxK n ι).1).length :=
          finCongr htake_len.symm
        rw [← Equiv.sum_comp eFin.symm]
        refine Finset.sum_congr rfl fun j _ => ?_
        have hj : eFin.symm j = ⟨j.1, by omega⟩ := rfl
        rw [hj]
        simp [rsA, List.getElem_take]
      obtain ⟨ψnext, hψ_inl, hψ_inr⟩ := hrecGen n ψn
        (fun ι j => if hι : GoodIdx n ι then (hsol ι hι).choose j else 0)
      have heval_emb : ∀ (v : Gen n →₀ D), eval ψnext (emb n v) = eval ψn v := by
        intro v
        dsimp only [eval]
        have hsupp : (emb n v).support = v.support.image (stepInl n) := by
          ext g
          by_cases hg : ∃ g' : Gen n, stepInl n g' = g
          · obtain ⟨g', rfl⟩ := hg
            simp only [Finsupp.mem_support_iff, Finset.mem_image]
            constructor
            · intro hne
              refine ⟨g', ?_, rfl⟩
              change Finsupp.mapDomain (stepInl n) v (stepInl n g') ≠ 0 at hne
              rwa [Finsupp.mapDomain_apply (hstepInl_inj n)] at hne
            · rintro ⟨g'', hg'', heq⟩
              have hg_eq : g'' = g' := hstepInl_inj n heq
              subst hg_eq
              change Finsupp.mapDomain (stepInl n) v (stepInl n g'') ≠ 0
              rwa [Finsupp.mapDomain_apply (hstepInl_inj n)]
          · simp only [Finsupp.mem_support_iff, Finset.mem_image]
            constructor
            · intro hne
              exfalso
              exact hne (Finsupp.mapDomain_of_notMem_range v g hg)
            · rintro ⟨g', _, rfl⟩
              exact absurd ⟨g', rfl⟩ hg
        change ∑ g ∈ (emb n v).support, toA (emb n v g) • ψnext g =
          ∑ g ∈ v.support, toA (v g) • ψn g
        rw [hsupp, Finset.sum_image (fun _ _ _ _ h => hstepInl_inj n h)]
        refine Finset.sum_congr rfl fun g _ => ?_
        change toA (Finsupp.mapDomain (stepInl n) v (stepInl n g)) • ψnext (stepInl n g) =
          toA (v g) • ψn g
        rw [Finsupp.mapDomain_apply (hstepInl_inj n), hψ_inl g]
      refine ⟨ψnext, ?_, ?_⟩
      · exact (hψ_inl _).trans hψn0
      · intro x hx hanc1 hanc2
        let hex := hrel_decomp n x hx
        let y := hex.choose
        let hy := hex.choose_spec.choose
        let c := hex.choose_spec.choose_spec.choose
        have hdecomp : emb n y + ∑ ι ∈ c.support, c ι • newRel n ι = x :=
          hex.choose_spec.choose_spec.choose_spec
        have hy_anc1 : (ancRel n y hy).1 ⊆ (R₀ : Set D) := fun r hr =>
          hanc1 (Or.inl (Or.inl (Or.inl hr)))
        have hy_anc2 : (ancRel n y hy).2 ⊆ Sops₀ := fun rs hrs => hanc2 (Or.inl hrs)
        have hy_vec : VecInR₀ y := hVecInR₀_of_coeff y fun r hr =>
          hanc1 (Or.inl (Or.inl (Or.inr hr)))
        have hc_in : ∀ ι ∈ c.support, c ι ∈ R₀ := fun ι hι =>
          hanc1 (Or.inl (Or.inr ⟨ι, hι, rfl⟩))
        have hι_good : ∀ ι ∈ c.support, GoodIdx n ι := by
          intro ι hι
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · exact hanc2 (Or.inr (Set.mem_iUnion.mpr ⟨⟨ι, hι⟩, Or.inl rfl⟩))
          · exact hVecInR₀_of_coeff (idxW n ι) fun r hr =>
              hanc1 (Or.inr (Set.mem_iUnion.mpr ⟨⟨ι, hι⟩, Or.inl (Or.inl (Or.inr hr))⟩))
          · intro j
            exact hVecInR₀_of_coeff (idxV n ι j) fun r hr =>
              hanc1 (Or.inr (Set.mem_iUnion.mpr
                ⟨⟨ι, hι⟩, Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨j, hr⟩))⟩))
          · intro r hr
            exact hanc1 (Or.inr (Set.mem_iUnion.mpr ⟨⟨ι, hι⟩, Or.inr hr⟩))
          · intro rs hrs
            exact hanc2 (Or.inr (Set.mem_iUnion.mpr ⟨⟨ι, hι⟩, Or.inr hrs⟩))
        have hnew_vec : ∀ ι ∈ c.support, VecInR₀ (newRel n ι) := by
          intro ι hι
          have hgi := hι_good ι hι
          refine hVecInR₀_sub (hVecInR₀_emb n hgi.2.1) (hVecInR₀_sum _ _ fun j _ => ?_)
          exact hVecInR₀_smul (hsop_in (idxRs n ι) hgi.1 _ (List.getElem_mem _))
            (hVecInR₀_single _ R₀.one_mem)
        have hnew_eval : ∀ ι ∈ c.support, eval ψnext (newRel n ι) = 0 := by
          intro ι hι
          have hgi := hι_good ι hι
          have hr_in : ∀ j : Fin (idxK n ι).1,
              ((idxRs n ι)[j.1]'(Nat.lt_trans j.2 (idxK n ι).2)) ∈ R₀ :=
            fun j => hsop_in (idxRs n ι) hgi.1 _ (List.getElem_mem _)
          change eval ψnext (emb n (idxW n ι) -
            ∑ j : Fin (idxK n ι).1,
              ((idxRs n ι)[j.1]'(Nat.lt_trans j.2 (idxK n ι).2)) •
                Finsupp.single (stepInr n ι j) 1) = 0
          rw [heval_sub ψnext (hVecInR₀_emb n hgi.2.1)
                (hVecInR₀_sum _ _ fun j _ =>
                  hVecInR₀_smul (hr_in j) (hVecInR₀_single _ R₀.one_mem)),
              heval_emb,
              heval_sum ψnext _ _ fun j _ =>
                hVecInR₀_smul (hr_in j) (hVecInR₀_single _ R₀.one_mem)]
          have hsum0 : ∑ j : Fin (idxK n ι).1,
              eval ψnext (((idxRs n ι)[j.1]'(Nat.lt_trans j.2 (idxK n ι).2)) •
                Finsupp.single (stepInr n ι j) 1) =
              ∑ j : Fin (idxK n ι).1,
                toA ((idxRs n ι)[j.1]'(Nat.lt_trans j.2 (idxK n ι).2)) •
                  (hsol ι hgi).choose j := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [heval_smul ψnext (hr_in j) (hVecInR₀_single _ R₀.one_mem),
              heval_single, htoA_one, one_smul, hψ_inr ι j]
            split_ifs
            rfl
          rw [hsum0, ← (hsol ι hgi).choose_spec, sub_self]
        rw [← hdecomp, heval_add ψnext (hVecInR₀_emb n hy_vec)
              (hVecInR₀_sum_u _ _ fun ι hι => hVecInR₀_smul (hc_in ι hι) (hnew_vec ι hι)),
            heval_emb, hψn y hy hy_anc1 hy_anc2, zero_add,
            heval_sum_u ψnext _ _ fun ι hι => hVecInR₀_smul (hc_in ι hι) (hnew_vec ι hι)]
        refine Finset.sum_eq_zero fun ι hι => ?_
        rw [heval_smul ψnext (hc_in ι hι) (hnew_vec ι hι), hnew_eval ι hι, smul_zero]
  obtain ⟨ψN, hψN0, hψN⟩ := hψ_ex N
  have heN_vec : VecInR₀ (Finsupp.single g0N (1 : D)) := hVecInR₀_single g0N R₀.one_mem
  have ha_in : ∀ s : Fin r, a s ∈ R₀ := fun s =>
    hE₀_sub (Or.inl (Or.inl ⟨s, rfl⟩))
  have hzN_vec : ∀ s : Fin r, VecInR₀ (zN s) := fun s =>
    hVecInR₀_of_coeff (zN s) fun x hx =>
      hE₀_sub (Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨s, hx⟩)))
  have hcontra_eval : eval ψN (Finsupp.single g0N (1 : D) - ∑ s : Fin r, a s • zN s) = 0 :=
    hψN _ hcontra (fun x hx => hE₀_sub (Or.inr hx)) (fun _ hx => hx)
  rw [heval_sub ψN heN_vec
        (hVecInR₀_sum _ _ fun s _ => hVecInR₀_smul (ha_in s) (hzN_vec s)),
      heval_single, htoA_one, one_smul, ← hg0N, hψN0,
      heval_sum ψN _ _ fun s _ => hVecInR₀_smul (ha_in s) (hzN_vec s)] at hcontra_eval
  have hw₀_eq : w₀ = ∑ s : Fin r, toA (a s) • eval ψN (zN s) := by
    have hsum : ∑ s : Fin r, eval ψN (a s • zN s) =
        ∑ s : Fin r, toA (a s) • eval ψN (zN s) :=
      Finset.sum_congr rfl fun s _ => heval_smul ψN (ha_in s) (hzN_vec s)
    rw [hsum] at hcontra_eval
    exact sub_eq_zero.mp hcontra_eval
  apply hw₀
  rw [hw₀_eq]
  refine Submodule.sum_mem _ fun s _ => ?_
  exact Submodule.smul_mem_smul (htoA_max (ha_in s) (ha_max s)) trivial

/- Section 3c: Instantiating the universal modification tower -/

private lemma exists_balanced_of_domain_dim_ge_two
    (hType0 : ∀ (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A],
      (2 : WithBot ℕ∞) ≤ ringKrullDim A →
      ∃ (W : Type) (_ : AddCommGroup W) (_ : Module A W), IsBalancedBigCohenMacaulay A W)
    (D : Type u) [CommRing D] [IsLocalRing D] [IsNoetherianRing D] [IsDomain D]
    (d : ℕ) (hd : ringKrullDim D = (d : WithBot ℕ∞)) (hd2 : 2 ≤ d) :
    ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module D W), IsBalancedBigCohenMacaulay D W := by
  let RawIdx : Type u → Type u := fun G =>
    Σ (rs : { rs : List D // IsSystemOfParameters D rs }) (k : Fin rs.1.length),
      (G →₀ D) × (Fin k.1 → (G →₀ D))
  let IdxOf : ∀ (G : Type u), Submodule D (G →₀ D) → Type u := fun G R =>
    { p : RawIdx G //
        p.1.1[p.2.1] • p.2.2.1 -
          ∑ j : Fin p.2.1.1, (p.1.1[j.1]'(Nat.lt_trans j.2 p.2.1.2)) • p.2.2.2 j ∈ R }
  let newRelOf : ∀ (G : Type u) (R : Submodule D (G →₀ D)) (ι : IdxOf G R),
      (G ⊕ (Σ ι' : IdxOf G R, Fin ι'.1.2.1.1)) →₀ D := fun G R ι =>
    Finsupp.lmapDomain D D Sum.inl ι.1.2.2.1 -
      ∑ j : Fin ι.1.2.1.1,
        (ι.1.1.1[j.1]'(Nat.lt_trans j.2 ι.1.2.1.2)) • Finsupp.single (Sum.inr ⟨ι, j⟩) 1
  let stepStage : (Σ G : Type u, Submodule D (G →₀ D)) →
      (Σ G : Type u, Submodule D (G →₀ D)) := fun s =>
    ⟨s.1 ⊕ (Σ ι : IdxOf s.1 s.2, Fin ι.1.2.1.1),
      Submodule.map (Finsupp.lmapDomain D D Sum.inl) s.2 ⊔
        Submodule.span D (Set.range (newRelOf s.1 s.2))⟩
  let stage : ℕ → (Σ G : Type u, Submodule D (G →₀ D)) :=
    Nat.rec ⟨PUnit.{u + 1}, ⊥⟩ (fun _ s => stepStage s)
  let Gen : ℕ → Type u := fun n => (stage n).1
  let Rel : ∀ n : ℕ, Submodule D (Gen n →₀ D) := fun n => (stage n).2
  let Idx : ℕ → Type u := fun n => IdxOf (Gen n) (Rel n)
  let stepInl : ∀ n : ℕ, Gen n → Gen (n + 1) := fun _ => Sum.inl
  let stepInr : ∀ n (ι : Idx n), Fin ι.1.2.1.1 → Gen (n + 1) := fun _ ι j => Sum.inr ⟨ι, j⟩
  refine build_balanced_from_opaque_tower D Gen Rel PUnit.unit stepInl
    (fun n r hr => Submodule.mem_sup_left ⟨r, hr, rfl⟩)
    (fun n rs hrs k hk w v hrel =>
      let ι : Idx n := ⟨⟨⟨rs, hrs⟩, ⟨k, hk⟩, (w, v)⟩, hrel⟩
      ⟨fun j => stepInr n ι j, Submodule.mem_sup_right (Submodule.subset_span ⟨ι, rfl⟩)⟩)
    (fun N g0N hg0N r a zN ha_max hcontra =>
      no_collapse_from_opaque_tower hType0 D d hd hd2 Gen Rel PUnit.unit rfl
        Idx (fun _ ι => ι.1.1.1) (fun _ ι => ι.1.1.2) (fun _ ι => ι.1.2.1)
        (fun _ ι => ι.1.2.2.1) (fun _ ι => ι.1.2.2.2) (fun _ ι => ι.2)
        stepInl stepInr (fun _ => Sum.inl_injective)
        (fun _ {_} f₁ f₂ => ⟨fun g => Sum.elim f₁ (fun p => f₂ p.1 p.2) g,
          fun _ => rfl, fun _ _ => rfl⟩)
        (fun _ => rfl)
        N g0N hg0N r a zN ha_max hcontra)

end

theorem main : H1 → H2 → type_of% @SmallCohenMacaulayModules.exists_isBalancedBigCohenMacaulay := by
  intro h1 h2 R _ _ _
  obtain ⟨P, hP, hdimP⟩ := exists_prime_quotient_same_dim R
  have _ : IsLocalRing (R ⧸ P) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
  obtain ⟨d, hd⟩ := ringKrullDim_eq_nat_of_local_noetherian (R ⧸ P)
  have hType0 : ∀ (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A],
      (2 : WithBot ℕ∞) ≤ ringKrullDim A →
      ∃ (W : Type) (_ : AddCommGroup W) (_ : Module A W), IsBalancedBigCohenMacaulay A W := by
    intro A _ _ _ _ hdimA
    by_cases hchar : ringChar A = ringChar (ResidueField A)
    · exact h1 A hdimA hchar
    · exact h2 A hdimA hchar
  have hdomW : ∃ (W : Type _) (_ : AddCommGroup W) (_ : Module (R ⧸ P) W),
      IsBalancedBigCohenMacaulay (R ⧸ P) W := by
    by_cases hd1 : d ≤ 1
    · have hdim1 : ringKrullDim (R ⧸ P) ≤ 1 := by
        rw [hd]
        exact WithBot.coe_le_coe.mpr (ENat.natCast_le_natCast.mpr hd1)
      exact exists_balanced_of_domain_dim_le_one (R ⧸ P) hdim1
    · exact exists_balanced_of_domain_dim_ge_two hType0 (R ⧸ P) d hd (by omega)
  obtain ⟨W, _, _, hW⟩ := hdomW
  exact balancedBigCM_of_quotient R P hdimP W hW

end OMA.R_SmallCohenMacaulayModules_exists_isBalancedBigCohenMacaulay_R1
