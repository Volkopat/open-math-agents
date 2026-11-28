import FormalConjectures.ErdosProblems.«951»

/-! Alternative reduction of Erdős 951. Credit: @studer.

Erdős recorded the ordinary integer case in “A survey of problems in
combinatorial number theory” (1980), p. 102. The rank argument
below also handles nonintegral generators whose logarithms lie in the rational
span of the ordinary prime logs at a given cutoff. If only finitely many
ordinary primes are missing from the Beurling integers, their product gives
a full progression in that semigroup. H1 is an arithmetic rigidity question
for such a semigroup. H2 isolates the surviving case. -/

open Finset Filter
open scoped Nat.Prime

namespace OMA.R_Erdos951_erdos_951_R2

private theorem log_indicator (a : ℕ → ℝ) (ha : ∀ i, 0 < a i) (s : Finset ℕ)
    (f : ℕ → ℕ) :
    Real.log (beurlingInteger a (Finsupp.indicator s (fun i _ => f i))) =
      ∑ i ∈ s, (f i : ℝ) * Real.log (a i) := by
  rw [beurlingInteger, Finsupp.prod_of_support_subset _ (Finsupp.support_indicator_subset _ _)
    _ (fun _ _ => pow_zero _), Real.log_prod (fun i _ => pow_ne_zero _ (ha i).ne')]
  apply sum_congr rfl
  intro i hi
  rw [Finsupp.indicator_of_mem hi, Real.log_pow]

/-- An integer relation among the logs would identify two Beurling integers
with distinct nonnegative exponent vectors. Clearing denominators then
gives the same independence over the rationals. -/
private theorem logs_independent (a : ℕ → ℝ) (ha : ∀ i, 0 < a i) (sep : Erdos951.Erdos951Prop a) :
    LinearIndependent ℚ (fun i => Real.log (a i)) := by
  classical
  apply (LinearIndependent.iff_fractionRing ℤ ℚ).mp
  apply linearIndependent_iff'.mpr
  intro s g rel i hi
  let pos (j : ℕ) := (g j).toNat
  let neg (j : ℕ) := (-g j).toNat
  have split (j : ℕ) : (g j : ℝ) = (pos j : ℝ) - (neg j : ℝ) := by
    exact_mod_cast (show g j = (pos j : ℤ) - (neg j : ℤ) by dsimp [pos,neg]; omega)
  have logs :
      Real.log (beurlingInteger a (Finsupp.indicator s (fun j _ => pos j))) =
      Real.log (beurlingInteger a (Finsupp.indicator s (fun j _ => neg j))) := by
    rw [log_indicator a ha, log_indicator a ha, ← sub_eq_zero, ← sum_sub_distrib]
    simpa only [zsmul_eq_mul,split,sub_mul] using rel
  have bp (v : ℕ →₀ ℕ) : 0 < beurlingInteger a v :=
    Finset.prod_pos (fun j _ => pow_pos (ha j) (v j))
  have equal := Real.log_injOn_pos (bp _) (bp _) logs
  have expEq : Finsupp.indicator s (fun j _ => pos j) =
      Finsupp.indicator s (fun j _ => neg j) := by
    by_contra hne
    have impossible := sep _ _ hne
    rw [equal, sub_self, abs_zero] at impossible
    linarith
  have at_i := DFunLike.congr_fun expEq i
  simp only [Finsupp.indicator_of_mem hi] at at_i
  dsimp [pos,neg] at at_i
  omega

private theorem supported_finset_card (a : ℕ → ℝ) (ha : ∀ i, 0 < a i)
    (sep : Erdos951.Erdos951Prop a) (S : Finset ℕ) (P : Finset ℕ)
    (supported : ∀ i ∈ S, Real.log (a i) ∈
      Submodule.span ℚ (↑(P.image (fun p : ℕ => Real.log (p:ℝ))) : Set ℝ)) :
    S.card ≤ P.card := by
  classical
  let L := Submodule.span ℚ (↑(P.image (fun p : ℕ => Real.log (p:ℝ))) : Set ℝ)
  let v (i : S) : L := ⟨Real.log (a i), supported i i.property⟩
  have hli : LinearIndependent ℚ v := by
    apply LinearIndependent.of_comp (f := L.subtype)
    exact (logs_independent a ha sep).comp Subtype.val Subtype.val_injective
  calc
    S.card = Fintype.card S := (Fintype.card_coe _).symm
    _ ≤ Module.finrank ℚ L := hli.fintype_card_le_finrank
    _ ≤ (P.image (fun p : ℕ => Real.log (p:ℝ))).card := finrank_span_finset_le_card ..
    _ ≤ P.card := card_image_le


/-- This applies to any set of indices without an a priori finiteness or height condition. -/
private theorem supported_set_card (a : ℕ → ℝ) (ha : ∀ i, 0 < a i)
    (sep : Erdos951.Erdos951Prop a) (S : Set ℕ) (P : Finset ℕ)
    (supported : ∀ i ∈ S, Real.log (a i) ∈
      Submodule.span ℚ (↑(P.image (fun p : ℕ => Real.log (p:ℝ))) : Set ℝ)) :
    S.Finite ∧ S.ncard ≤ P.card := by
  classical
  have bound (T : Set ℕ) (hT : T.Finite) (hsub : T ⊆ S) : T.ncard ≤ P.card := by
    rw [Set.ncard_eq_toFinset_card _ hT]
    exact supported_finset_card a ha sep hT.toFinset P fun i hi =>
      supported i (hsub (hT.mem_toFinset.mp hi))
  have hS : S.Finite := by
    by_contra hinf
    obtain ⟨T,hTS,hT,hcard⟩ := Set.Infinite.exists_subset_ncard_eq hinf (P.card+1)
    have := bound T hT hTS
    omega
  exact ⟨hS,bound S hS (fun _ hi => hi)⟩

/-- Prime factorization puts the log of an ordinary smooth integer in the
rational span of the logs of its allowed prime factors. -/
private theorem log_nat_mem (P : Finset ℕ) (u : ℕ) (hu : u ≠ 0) (hs : u.primeFactors ⊆ P) :
    Real.log (u:ℝ) ∈ Submodule.span ℚ (↑(P.image (fun p : ℕ => Real.log (p:ℝ))) : Set ℝ) := by
  classical
  have eq : (u:ℝ) = ∏ p ∈ u.primeFactors, (p:ℝ)^u.factorization p := by
    exact_mod_cast Nat.prod_primeFactors_pow_factorization hu
  rw [eq, Real.log_prod (fun p hp => pow_ne_zero _ (by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero))]
  apply Submodule.sum_mem
  intro p hp
  rw [Real.log_pow]
  have hm := (Submodule.span ℚ (↑(P.image (fun p : ℕ => Real.log (p:ℝ))) : Set ℝ)).smul_mem
    (u.factorization p : ℚ) (Submodule.subset_span (Finset.mem_image_of_mem _ (hs hp)))
  simpa [Rat.smul_def] using hm


/-- Multiplicative closure and prime factorization supply the progression
with modulus the product of the missing primes (including the empty product). -/
private theorem progression_of_finite_missing (S : Submonoid ℝ)
    (hfin : {p : ℕ | p.Prime ∧ (p:ℝ) ∉ S}.Finite) :
    ∃ d : ℕ, 0 < d ∧ ∀ k : ℕ, 1 + (d:ℝ) * (k:ℝ) ∈ S := by
  classical
  let T := hfin.toFinset
  let d := ∏ p ∈ T, p
  refine ⟨d, Finset.prod_pos (fun p hp => (hfin.mem_toFinset.mp hp).1.pos), ?_⟩
  intro k
  let m := 1+d*k
  have hm : m ≠ 0 := by dsimp [m]; omega
  have eqm : (m:ℝ) = ∏ p ∈ m.primeFactors, (p:ℝ)^m.factorization p := by
    exact_mod_cast Nat.prod_primeFactors_pow_factorization hm
  change ((1:ℝ) + (d:ℝ)*k) ∈ S
  rw [show ((1:ℝ) + (d:ℝ)*k) = (m:ℝ) by dsimp [m]; push_cast; rfl, eqm]
  refine S.prod_mem fun p hp => S.pow_mem ?_ _
  by_contra hn
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hT : p ∈ T := hfin.mem_toFinset.mpr ⟨hprime, hn⟩
  have hpd : p ∣ d := Finset.dvd_prod_of_mem id hT
  have hpm := Nat.dvd_of_mem_primeFactors hp
  have hpk : p ∣ d*k := dvd_mul_of_dvd_left hpd k
  exact hprime.not_dvd_one ((Nat.dvd_add_left hpk).mp hpm)

/-- Progression rigidity for a separated multiplicative submonoid. -/
def H1 : Prop :=
  ∀ S : Submonoid ℝ, (∀ x ∈ S, 0 < x) →
    (∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x - y|) →
    ∀ d : ℕ, 0 < d → (∀ k : ℕ, 1 + (d : ℝ) * (k : ℝ) ∈ S) →
    ∀ x ∈ S, ∃ n : ℕ, x = (n : ℝ)

/-- The remaining cutoffs have an index outside the small-prime log span;
the generated semigroup also omits infinitely many ordinary primes. -/
def H2 : Prop :=
  ∀ a : ℕ → ℝ, 1 < a 0 → StrictMono a → Erdos951.Erdos951Prop a →
    {p : ℕ | p.Prime ∧ (p:ℝ) ∉ BeurlingIntegers a}.Infinite →
    ∀ᶠ x : ℝ in atTop, (∃ i, a i ≤ x ∧ Real.log (a i) ∉
      Submodule.span ℚ (↑((Nat.primesLE ⌊x⌋₊).image (fun p : ℕ => Real.log (p:ℝ))) : Set ℝ)) →
      {i : ℕ | a i ≤ x}.ncard ≤ π ⌊x⌋₊

theorem main : H1 → H2 → type_of% @Erdos951.erdos_951 := by
  classical
  intro h1 h2 a hfirst hmono hsep
  have hpos (i : ℕ) : 0 < a i := (zero_lt_one.trans hfirst).trans_le (hmono.monotone (Nat.zero_le i))
  have count (x : ℝ) (h : ∀ i, a i ≤ x → Real.log (a i) ∈
      Submodule.span ℚ (↑((Nat.primesLE ⌊x⌋₊).image (fun p : ℕ => Real.log (p:ℝ))) : Set ℝ)) :
      {i : ℕ | a i ≤ x}.ncard ≤ π ⌊x⌋₊ := by
    rw [← Nat.primesLE_card_eq_primeCounting]
    exact (supported_set_card a hpos hsep _ _ h).2
  by_cases hinf : {p : ℕ | p.Prime ∧ (p:ℝ) ∉ BeurlingIntegers a}.Infinite
  · filter_upwards [h2 a hfirst hmono hsep hinf] with x hx
    by_cases hex : ∃ i, a i ≤ x ∧ Real.log (a i) ∉
        Submodule.span ℚ (↑((Nat.primesLE ⌊x⌋₊).image (fun p : ℕ => Real.log (p:ℝ))) : Set ℝ)
    · exact hx hex
    · exact count x fun i hi => by_contra fun hn => hex ⟨i, hi, hn⟩
  let S : Submonoid ℝ :=
    { carrier := BeurlingIntegers a
      one_mem' := ⟨0, by simp⟩
      mul_mem' := mul_mem_beurling }
  obtain ⟨d,hd,hprog⟩ := progression_of_finite_missing S (Set.not_infinite.mp hinf)
  have spos : ∀ x ∈ S, 0 < x := by
    rintro _ ⟨v,rfl⟩
    exact Finset.prod_pos (fun i _ => pow_pos (hpos i) (v i))
  have ssep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x-y| := by
    rintro _ ⟨v,rfl⟩ _ ⟨w,rfl⟩ hn
    exact hsep v w (fun eq => hn (congrArg _ eq))
  have integer := h1 S spos ssep d hd hprog
  apply Filter.Eventually.of_forall
  intro x
  apply count x
  intro i hi
  obtain ⟨n,hn⟩ := integer (a i) (generator_mem_beurling a i)
  have hnpos : 0 < n := by exact_mod_cast hn ▸ hpos i
  rw [hn]
  apply log_nat_mem _ _ hnpos.ne'
  intro p hp
  apply Nat.mem_primesLE.mpr
  refine ⟨Nat.le_floor ?_, Nat.prime_of_mem_primeFactors hp⟩
  exact (Nat.cast_le.mpr (Nat.le_of_mem_primeFactors hp)).trans (hn ▸ hi)

end OMA.R_Erdos951_erdos_951_R2
