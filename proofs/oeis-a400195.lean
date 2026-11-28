import OMAStatements.S_oeis_a400195

-- Problem: A400195: Maximum number of odd terms in a 2-dense sublist of divisors of n.
-- Upstream: formal-conjectures statements/oeis-a400195.lean:0 (declaration OMA.S_oeis_a400195.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: write e for the 2-adic valuation of n, so A001511(n) = e + 1. In a 2-dense
-- sublist from x to y, an even term 2z has z in the sublist (z < x would give 2z < x by the
-- left maximality), and a term z with 2z dividing n has 2z in the sublist (2z > y would give
-- 2y < 2z by the right maximality). Hence the terms of the sublist are exactly the numbers
-- 2^i * d with d an odd term and i <= e, all distinct, so each sublist has e + 1 times as many
-- terms as odd terms, and the two maxima differ by the factor e + 1.

open OMA.S_oeis_a400195 in
theorem OMA.solution : type_of% @OMA.S_oeis_a400195.main := by
  intro n hn
  have hn0 : n ≠ 0 := by omega
  obtain ⟨e, he⟩ : ∃ e, e = padicValNat 2 n := ⟨_, rfl⟩
  have hdvd_iff : ∀ k : ℕ, 2 ^ k ∣ n ↔ k ≤ e := by
    intro k
    rw [he]
    exact padicValNat_dvd_iff_le hn0
  have hval : ∀ i d : ℕ, Odd d → padicValNat 2 (2 ^ i * d) = i := by
    intro i d hd
    have hd0 : d ≠ 0 := by
      rintro rfl
      obtain ⟨k, hk⟩ := hd
      omega
    have hnd : ¬ 2 ∣ d := by
      rintro ⟨c, hc⟩
      obtain ⟨k, hk⟩ := hd
      omega
    rw [padicValNat.mul (p := 2) (pow_ne_zero i (by norm_num : (2 : ℕ) ≠ 0)) hd0,
      padicValNat.prime_pow (p := 2), padicValNat.eq_zero_of_not_dvd hnd, Nat.add_zero]
  have hblock : ∀ x y : ℕ, IsDense n x y →
      (terms n x y).card = (e + 1) * ((terms n x y).filter Odd).card := by
    intro x y hD
    obtain ⟨_, _, _, _, hleft, hright⟩ := hD
    have hmem : ∀ z, z ∈ terms n x y ↔ z ∣ n ∧ x ≤ z ∧ z ≤ y := by
      intro z
      unfold terms
      rw [Finset.mem_filter, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨h1, _⟩, h2, h3⟩
        exact ⟨h1, h2, h3⟩
      · rintro ⟨h1, h2, h3⟩
        exact ⟨⟨h1, hn0⟩, h2, h3⟩
    have hhalf : ∀ z, 2 * z ∈ terms n x y → z ∈ terms n x y := by
      intro z hz
      obtain ⟨h1, h2, h3⟩ := (hmem (2 * z)).mp hz
      have hzd : z ∣ n := Nat.dvd_trans (dvd_mul_left z 2) h1
      refine (hmem z).mpr ⟨hzd, ?_, by omega⟩
      by_contra hc
      have h4 := hleft z (Nat.mem_divisors.mpr ⟨hzd, hn0⟩) (by omega)
      omega
    have hdouble : ∀ z, z ∈ terms n x y → 2 * z ∣ n → 2 * z ∈ terms n x y := by
      intro z hz h2z
      obtain ⟨_, h2, h3⟩ := (hmem z).mp hz
      refine (hmem (2 * z)).mpr ⟨h2z, by omega, ?_⟩
      by_contra hc
      have h4 := hright (2 * z) (Nat.mem_divisors.mpr ⟨h2z, hn0⟩) (by omega)
      omega
    have hhalfs : ∀ k m : ℕ, 2 ^ k * m ∈ terms n x y → m ∈ terms n x y := by
      intro k
      induction k with
      | zero =>
        intro m h
        simpa using h
      | succ k ih =>
        intro m h
        apply ih
        apply hhalf
        rw [show 2 * (2 ^ k * m) = 2 ^ (k + 1) * m by ring]
        exact h
    have hdoubles : ∀ d, d ∈ (terms n x y).filter Odd → ∀ i : ℕ, i ≤ e →
        2 ^ i * d ∈ terms n x y := by
      intro d hd i
      obtain ⟨hdB, hdo⟩ := Finset.mem_filter.mp hd
      have hdn : d ∣ n := ((hmem d).mp hdB).1
      have hcop : Nat.Coprime (2 ^ e) d :=
        Nat.Coprime.pow_left e (Nat.coprime_two_left.mpr hdo)
      have hed : 2 ^ e * d ∣ n :=
        Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop ((hdvd_iff e).mpr le_rfl) hdn
      induction i with
      | zero =>
        intro _
        simpa using hdB
      | succ i ih =>
        intro hi
        have h1 := ih (by omega)
        rw [show 2 ^ (i + 1) * d = 2 * (2 ^ i * d) by ring]
        apply hdouble _ h1
        rw [show 2 * (2 ^ i * d) = 2 ^ (i + 1) * d by ring]
        exact Nat.dvd_trans (mul_dvd_mul_right (Nat.pow_dvd_pow 2 hi) d) hed
    have himage : terms n x y =
        (((terms n x y).filter Odd) ×ˢ Finset.range (e + 1)).image
          (fun q : ℕ × ℕ => 2 ^ q.2 * q.1) := by
      ext z
      rw [Finset.mem_image]
      constructor
      · intro hz
        have hz0 : z ≠ 0 := by
          have hzn := ((hmem z).mp hz).1
          rintro rfl
          exact hn0 (Nat.eq_zero_of_zero_dvd hzn)
        obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hz0
        refine ⟨(m, k), ?_, rfl⟩
        rw [Finset.mem_product, Finset.mem_filter, Finset.mem_range]
        refine ⟨⟨hhalfs k m hz, hm⟩, ?_⟩
        have hk : 2 ^ k ∣ n := Nat.dvd_trans (dvd_mul_right (2 ^ k) m) ((hmem _).mp hz).1
        have hke := (hdvd_iff k).mp hk
        show k < e + 1
        omega
      · rintro ⟨⟨d, i⟩, hq, rfl⟩
        rw [Finset.mem_product, Finset.mem_range] at hq
        exact hdoubles d hq.1 i (Nat.le_of_lt_succ hq.2)
    have hinj : Set.InjOn (fun q : ℕ × ℕ => 2 ^ q.2 * q.1)
        (((terms n x y).filter Odd) ×ˢ Finset.range (e + 1) : Finset (ℕ × ℕ)) := by
      rintro ⟨d, i⟩ hq ⟨d', j⟩ hq' heq
      have hq1 := Finset.mem_product.mp (Finset.mem_coe.mp hq)
      have hq2 := Finset.mem_product.mp (Finset.mem_coe.mp hq')
      have hod : Odd d := (Finset.mem_filter.mp hq1.1).2
      have hod' : Odd d' := (Finset.mem_filter.mp hq2.1).2
      have heq' : 2 ^ i * d = 2 ^ j * d' := heq
      have hij : i = j := by
        have h1 := hval i d hod
        have h2 := hval j d' hod'
        rw [heq'] at h1
        omega
      subst hij
      have hpos : 0 < 2 ^ i := by positivity
      have hdd : d = d' := Nat.eq_of_mul_eq_mul_left hpos heq'
      rw [hdd]
    have hc := congrArg Finset.card himage
    rw [hc, Finset.card_image_of_injOn hinj, Finset.card_product, Finset.card_range]
    ring
  have ha : a001511 n = e + 1 := by
    unfold a001511
    rw [padicValNat.mul (p := 2) (by norm_num : (2 : ℕ) ≠ 0) hn0, padicValNat_self (p := 2), he]
    omega
  have hDL : ∀ q ∈ denseLists n, IsDense n q.1 q.2 := by
    intro q hq
    unfold denseLists at hq
    exact (Finset.mem_filter.mp hq).2
  have hsup : a400194 n = (e + 1) * a n := by
    unfold a400194 a
    apply le_antisymm
    · apply Finset.sup_le
      intro q hq
      have hD : IsDense n q.1 q.2 := hDL q hq
      show (terms n q.1 q.2).card ≤ _
      rw [hblock q.1 q.2 hD]
      exact Nat.mul_le_mul_left (e + 1)
        (Finset.le_sup (f := fun p : ℕ × ℕ => ((terms n p.1 p.2).filter Odd).card) hq)
    · rcases Finset.eq_empty_or_nonempty (denseLists n) with h | h
      · rw [h]
        simp
      · obtain ⟨q, hq, hqe⟩ := Finset.exists_mem_eq_sup _ h
          (fun p : ℕ × ℕ => ((terms n p.1 p.2).filter Odd).card)
        rw [hqe]
        have hD : IsDense n q.1 q.2 := hDL q hq
        show (e + 1) * ((terms n q.1 q.2).filter Odd).card ≤ _
        rw [← hblock q.1 q.2 hD]
        exact Finset.le_sup (f := fun p : ℕ × ℕ => (terms n p.1 p.2).card) hq
  have hpos : (0 : ℚ) < ((e + 1 : ℕ) : ℚ) := by positivity
  rw [hsup, ha, Nat.cast_mul, mul_div_cancel_left₀ _ hpos.ne']
