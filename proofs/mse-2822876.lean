import OMAStatements.S_mse_2822876

/-! The existing finite prime-avoidance argument, with the polynomial conversion
handled directly by the total-degree characterization of units. -/
open UniqueFactorizationMonoid

theorem common_divisor_of_pairwise {R : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] (I : Ideal R)
    (hpair : ∀ a ∈ I, ∀ b ∈ I,
      ∃ d : R, d ≠ 0 ∧ ¬IsUnit d ∧ d ∣ a ∧ d ∣ b) :
    ∃ d : R, d ≠ 0 ∧ ¬IsUnit d ∧ ∀ a ∈ I, d ∣ a := by
  classical
  by_cases hz : ∀ a ∈ I, a = 0
  · obtain ⟨d, hd0, hdu, _, _⟩ := hpair 0 I.zero_mem 0 I.zero_mem
    refine ⟨d, hd0, hdu, ?_⟩
    intro a ha
    rw [hz a ha]
    exact dvd_zero d
  · push Not at hz
    obtain ⟨a, ha, ha0⟩ := hz
    let : StrongNormalizationMonoid R := UniqueFactorizationMonoid.strongNormalizationMonoid
    let S : Finset R := (normalizedFactors a).toFinset
    have hprime : ∀ p ∈ S, Prime p := by
      intro p hp
      have hp' : p ∈ normalizedFactors a := Multiset.mem_toFinset.mp hp
      exact prime_of_normalized_factor p hp'
    have hcover : (I : Set R) ⊆
        ⋃ p ∈ (↑S : Set R), (Ideal.span ({p} : Set R) : Set R) := by
      intro b hb
      obtain ⟨d, hd0, hdu, hda, hdb⟩ := hpair a ha b hb
      obtain ⟨p, hp, hpd⟩ := WfDvdMonoid.exists_irreducible_factor hdu hd0
      obtain ⟨q, hq, hpq⟩ := exists_mem_normalizedFactors_of_dvd ha0 hp (hpd.trans hda)
      refine Set.mem_iUnion.mpr ⟨q, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
      · exact Multiset.mem_toFinset.mpr hq
      · exact Ideal.mem_span_singleton.mpr
          (hpq.dvd_iff_dvd_left.mp (hpd.trans hdb))
    obtain ⟨p, hp, hI⟩ :=
      (Ideal.subset_union_prime (s := S) (f := fun p => Ideal.span ({p} : Set R)) 0 0
        (fun p hp _ _ => Ideal.isPrime_span_singleton_of_prime (hprime p hp))).mp hcover
    refine ⟨p, (hprime p hp).ne_zero, (hprime p hp).not_isUnit, ?_⟩
    intro b hb
    exact Ideal.mem_span_singleton.mp (hI hb)

private lemma positive_degree {K σ : Type*} [Field K] (p : MvPolynomial σ K) :
    0 < p.totalDegree ↔ p ≠ 0 ∧ ¬IsUnit p := by
  by_cases h : p.totalDegree = 0
  · rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp h]
    simp [isUnit_iff_ne_zero]
  · have hp : p ≠ 0 := by rintro rfl; simp at h
    simp [Nat.pos_iff_ne_zero, h, hp, MvPolynomial.isUnit_iff_totalDegree_of_isReduced]

theorem OMA.solution : type_of% @OMA.S_mse_2822876.main := by
  intro n I hpair
  have h := common_divisor_of_pairwise I (by
    simpa only [positive_degree, and_assoc] using hpair)
  simpa only [positive_degree, and_assoc] using h
