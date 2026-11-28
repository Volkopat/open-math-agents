import OMAStatements.S_mo_215301

/-! STATUS: NEW
For every positive integer there is a finite set of distinct positive unit
fractions with that total and no proper positive integer subsum.
Source: https://mathoverflow.net/questions/215301
The poser's example handles total two. Adam Przeździecki's construction in
MO 209958 permits repetitions. Here a single denominator joins an initial
segment of odd primes. The connecting denominator has a precursor in
pallab1234’s construction. B. M. Stewart’s binary remainder method
(1954) fills the remaining fraction while preserving coprimality.
Credit: @Mapika. -/

open Finset

namespace Egypt

private abbrev mass (S : Finset ℕ) : ℚ := ∑ k ∈ S, 1 / (k : ℚ)

private lemma den_unit {k : ℕ} (hk : 0 < k) : (1 / (k : ℚ)).den = k := by
  rw [one_div, Rat.den_inv_of_ne_zero (by exact_mod_cast hk.ne')]
  simp

private lemma clean_sum {p : ℕ} (hp : p.Prime) (S : Finset ℕ)
    (hs : ∀ k ∈ S, 0 < k ∧ ¬p ∣ k) : ¬p ∣ (mass S).den := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa [mass] using hp.not_dvd_one
  | @insert k S hk ih =>
    rw [mass, sum_insert hk]
    intro h
    rcases hp.dvd_mul.mp (h.trans (Rat.add_den_dvd _ _)) with h | h
    · rw [den_unit (hs k (mem_insert_self ..)).1] at h
      exact (hs k (mem_insert_self ..)).2 h
    · exact ih (fun j hj => hs j (mem_insert_of_mem hj)) h

private lemma marker {p : ℕ} (hp : p.Prime) {S : Finset ℕ} (hm : p ∈ S)
    (hs : ∀ k ∈ S, k ≠ p → 0 < k ∧ ¬p ∣ k) : p ∣ (mass S).den := by
  classical
  by_contra h
  have hc := clean_sum hp (S.erase p) (fun k hk => hs k (mem_erase.mp hk).2 (mem_erase.mp hk).1)
  have he : 1 / (p : ℚ) = mass S - mass (S.erase p) := by
    have := Finset.add_sum_erase S (fun k : ℕ => 1/(k:ℚ)) hm
    unfold mass
    linarith
  have hd := Rat.sub_den_dvd (mass S) (mass (S.erase p))
  rw [← he, den_unit hp.pos] at hd
  exact (hp.dvd_mul.mp hd).elim h hc

private def oddPrimes (N : ℕ) := (range N).filter (fun p => p.Prime ∧ 2 < p)

private lemma primes_step (N : ℕ) :
    mass (oddPrimes (N+1)) = mass (oddPrimes N) + (if N.Prime ∧ 2 < N then 1/(N:ℚ) else 0) := by
  classical
  simp [oddPrimes, mass, Finset.sum_filter, Finset.sum_range_succ]

private lemma long_primes (n : ℕ) : ∃ N, (n:ℚ)-1 < mass (oddPrimes N) := by
  classical
  by_contra! h
  apply not_summable_one_div_on_primes
  apply summable_of_sum_range_le (c := (n:ℝ)+1) (fun i => Set.indicator_nonneg (fun _ _ => by positivity) _)
  intro N
  have hreal : (∑ p ∈ oddPrimes N, 1/(p:ℝ)) ≤ (n:ℝ)-1 := by
    have hh := h N
    unfold mass at hh
    have hr := (Rat.cast_le (K := ℝ)).mpr hh
    push_cast at hr
    exact hr
  have he : ∀ i : ℕ, Set.indicator {p : ℕ | p.Prime} (fun p => (1:ℝ)/p) i =
      (if i.Prime ∧ 2 < i then 1/(i:ℝ) else 0) +
      (if i = 2 then 1/(2:ℝ) else 0) := by
    intro i
    by_cases hp : i.Prime
    · by_cases h2 : i = 2
      · subst i; norm_num [Set.indicator]
      · have hh : 2 < i := lt_of_le_of_ne hp.two_le (Ne.symm h2)
        simp [Set.indicator, hp, hh, h2]
    · have h2 : i ≠ 2 := fun e => hp (e ▸ Nat.prime_two)
      simp [Set.indicator, hp, h2]
  simp_rw [he, sum_add_distrib]
  simp only [oddPrimes, sum_filter] at hreal
  have hsmall : (∑ x ∈ range N, if x = 2 then 1/(2:ℝ) else 0) ≤ 1 := by
    simp only [sum_ite_eq', Finset.mem_range]
    split <;> norm_num
  linarith

private lemma prime_block (n : ℕ) (hn : 0 < n) :
    ∃ U : Finset ℕ, (∀ p ∈ U, p.Prime ∧ 2 < p) ∧
      (n:ℚ)-1 < mass U ∧ mass U < n := by
  classical
  let N := Nat.find (long_primes n)
  have hx : (n:ℚ)-1 < mass (oddPrimes N) := Nat.find_spec (long_primes n)
  refine ⟨oddPrimes N, fun _ h => (mem_filter.mp h).2, hx, ?_⟩
  cases hN : N with
  | zero =>
    simpa [oddPrimes, mass] using (show (0:ℚ)<n by exact_mod_cast hn)
  | succ k =>
    have hk : ¬ (n:ℚ)-1 < mass (oddPrimes k) :=
      Nat.find_min (long_primes n) (show k < N by omega)
    rw [primes_step]
    split_ifs with hp
    · have : (1:ℚ)/(k:ℚ) < 1 := (div_lt_one (by exact_mod_cast hp.1.pos)).mpr (by exact_mod_cast hp.1.one_lt)
      linarith
    · linarith

private def bits (M n : ℕ) : Finset ℕ :=
  n.bitIndices.toFinset.image (fun i => M / 2^i)

private lemma bit_le {n i : ℕ} (hi : i ∈ n.bitIndices.toFinset) : 2^i ≤ n := by
  simpa using (Finset.single_le_sum (fun j (_ : j ∈ n.bitIndices.toFinset) =>
    Nat.zero_le (2^j)) hi)

private lemma bits_spec (M n : ℕ) (hM : 0 < M)
    (hd : ∀ i ∈ n.bitIndices.toFinset, 2^i ∣ M) :
    mass (bits M n) = n / (M:ℚ) ∧
      ∀ k ∈ bits M n, 0 < k ∧ k ∣ M ∧ k ≤ M ∧ M ≤ k*n := by
  have he i hi := Nat.div_mul_cancel (hd i hi)
  constructor
  · unfold mass bits
    rw [sum_image]
    · calc
        _ = ∑ i ∈ n.bitIndices.toFinset, (2^i : ℚ) / M := by
          apply sum_congr rfl
          intro i hi
          rw [Rat.natCast_div _ _ (hd i hi)]
          push_cast
          field_simp
        _ = _ := by rw [← Finset.sum_div]; norm_cast; simp
    · intro i hi j hj hij
      have hpos : 0 < M / 2^i := Nat.div_pos (Nat.le_of_dvd hM (hd i hi)) (by positivity)
      have hx := he j hj
      change M / 2^i = M / 2^j at hij
      rw [← hij] at hx
      have heq := Nat.eq_of_mul_eq_mul_left hpos ((he i hi).trans hx.symm)
      exact (Nat.pow_right_injective (by decide : 2 ≤ 2)) heq
  · intro k hk
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
    have hpos := Nat.div_pos (Nat.le_of_dvd hM (hd i hi)) (show 0 < 2^i by positivity)
    exact ⟨hpos, ⟨2^i, (he i hi).symm⟩, Nat.div_le_self ..,
      (he i hi).symm.le.trans (Nat.mul_le_mul_left _ (bit_le hi))⟩

private lemma fill (q b : ℕ) (hb : b < q) :
    ∃ F : Finset ℕ, mass F = b/(q:ℚ) ∧
      ∀ k ∈ F, 0 < k ∧ k ∣ q * 2^q := by
  let D := 2^q
  have hD : q < D := Nat.lt_two_pow_self
  have hq : 0 < q := by omega
  have hDp : 0 < D := by omega
  let u := b*D/q
  let v := b*D%q
  have hu : u < D := (Nat.div_lt_iff_lt_mul hq).mpr (by nlinarith)
  have hv : v < q := Nat.mod_lt _ hq
  have heq : v+q*u=b*D := Nat.mod_add_div .. 
  have hd {j i : ℕ} (hj : j < D) (hi : i ∈ j.bitIndices.toFinset) : 2^i ∣ D := by
    have hh := (bit_le hi).trans hj.le
    exact pow_dvd_pow _ ((Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hh)
  obtain ⟨hs, hs'⟩ := bits_spec D u hDp (fun _ hi => hd hu hi)
  obtain ⟨ht, ht'⟩ := bits_spec (q*D) v (Nat.mul_pos hq hDp)
    (fun _ hi => (hd (hv.trans hD) hi).trans (dvd_mul_left D q))
  have hdis : Disjoint (bits D u) (bits (q*D) v) := by
    apply Finset.disjoint_left.mpr
    intro k h₁ h₂
    obtain ⟨hk, _, _, hx⟩ := ht' k h₂
    have hy := (hs' k h₁).2.2.1
    nlinarith [Nat.mul_le_mul_left v hy, Nat.mul_lt_mul_of_pos_right hv hDp]
  refine ⟨bits D u ∪ bits (q*D) v, ?_, ?_⟩
  · rw [mass, sum_union hdis]
    change mass (bits D u) + mass (bits (q*D) v) = _
    rw [hs, ht]
    push_cast
    have hrat : (v:ℚ)+q*u=b*D := by exact_mod_cast heq
    field_simp
    linarith
  · intro k hk
    rcases Finset.mem_union.mp hk with h | h
    · exact ⟨(hs' k h).1, (hs' k h).2.1.trans (dvd_mul_left D q)⟩
    · exact ⟨(ht' k h).1, (ht' k h).2.1⟩

private lemma completion (r : ℚ) (hr : 0 < r) (hr' : r < 1) :
    ∃ (z : ℕ) (F : Finset ℕ), r.den < z ∧ r.den ∣ z ∧
      1/(z:ℚ) + mass F = r ∧
      ∀ k ∈ F, 0 < k ∧ ∀ p : ℕ, p.Prime → 2 < p → p ∣ r.den → ¬p ∣ k := by
  let d := r.den
  let a := r.num.natAbs
  have hd : 0 < d := r.den_pos
  have ha : (a:ℚ) = r.num := by
    have hsign : 0 ≤ r.num := Rat.num_nonneg.mpr hr.le
    have e : (a:ℤ) = r.num := Int.natAbs_of_nonneg hsign
    exact_mod_cast e
  have hrval : (a:ℚ) / d = r := by rw [ha]; exact Rat.num_div_den r
  have hdQ : 0 < (d:ℚ) := by exact_mod_cast hd
  have hlt : a < d := by
    exact_mod_cast (div_lt_one hdQ).mp (hrval.trans_lt hr')
  have ha0 : 0 < a := by
    by_contra! hz
    have h0 : a=0 := by omega
    simp [h0] at hrval
    linarith
  obtain ⟨j, _, hj⟩ := Nat.exists_mul_mod_eq_one_of_coprime r.reduced (show 1 < d by omega)
  let q := j + 2*d
  have hq : 1 < q := by dsimp [q]; omega
  have hmod : a*q%d=1 := by
    change a*j%d=1 at hj
    simpa [q, Nat.mul_add, ← Nat.mul_assoc, Nat.add_mul_mod_self_left] using hj
  let b := a*q/d
  have hcalc : 1+d*b=a*q := by
    have e := Nat.mod_add_div (a*q) d
    rwa [hmod] at e
  have hb : b<q := (Nat.div_lt_iff_lt_mul hd).mpr (by nlinarith)
  obtain ⟨F, hF, hF'⟩ := fill q b hb
  refine ⟨d*q, F, ?_, dvd_mul_right .., ?_, ?_⟩
  · change d < d*q
    nlinarith
  · rw [hF, ← hrval]
    push_cast
    have he : (1:ℚ)+d*b=a*q := by exact_mod_cast hcalc
    have hqQ : (q:ℚ) ≠ 0 := by positivity
    field_simp
    linarith
  · intro k h
    refine ⟨(hF' k h).1, ?_⟩
    intro p hp hp2 hpd hpk
    rcases hp.dvd_mul.mp (hpk.trans (hF' k h).2) with hpq | hp2'
    · have he : p ∣ 1+d*b := hcalc ▸ dvd_mul_of_dvd_right hpq a
      exact hp.not_dvd_one ((Nat.dvd_add_iff_left (dvd_mul_of_dvd_left hpd b)).mpr he)
    · have := Nat.le_of_dvd (by decide : 0<2) (hp.dvd_of_dvd_pow hp2')
      omega

private lemma build (n : ℕ) (hn : 0 < n) :
    ∃ S : Finset ℕ, (∀ k ∈ S, 0 < k) ∧ mass S = n ∧
      ∀ T ⊂ S, ∀ m : ℕ, 0 < m → mass T ≠ m := by
  classical
  obtain ⟨U, hU, hlow, hhigh⟩ := prime_block n hn
  let r := (n:ℚ) - mass U
  have hr : 0 < r := sub_pos.mpr hhigh
  have hr' : r < 1 := by dsimp [r]; linarith
  have hpden : ∀ p ∈ U, p ∣ r.den := by
    intro p hp
    have hd := marker (hU p hp).1 hp (fun k hk hne =>
      ⟨(hU k hk).1.pos, fun h => hne ((Nat.prime_dvd_prime_iff_eq (hU p hp).1 (hU k hk).1).mp h).symm⟩)
    have e : mass U = n-r := by dsimp [r]; ring
    rw [e] at hd
    simpa using hd.trans (Rat.sub_den_dvd (n:ℚ) r)
  obtain ⟨z, F, hz, hdz, hsum, hF⟩ := completion r hr hr'
  have hz0 : 0 < z := lt_trans r.den_pos hz
  have hfclean {p k} (hp : p ∈ U) (hk : k ∈ F) : ¬p ∣ k :=
    (hF k hk).2 p (hU p hp).1 (hU p hp).2 (hpden p hp)
  have hdis : Disjoint U F :=
    by
    apply Finset.disjoint_left.mpr
    intro k hp hk
    exact hfclean hp hk (dvd_refl _)
  have hpos : ∀ k ∈ U ∪ F, 0 < k := by
    intro k hk
    rcases mem_union.mp hk with h | h
    · exact (hU k h).1.pos
    · exact (hF k h).1
  have hUn : U.Nonempty := by
    by_contra! h
    rw [h] at hlow
    simp [mass] at hlow
    have h1 : (1:ℚ) ≤ n := by exact_mod_cast hn
    linarith
  obtain ⟨p₀, hp₀⟩ := hUn
  have hznot : z ∉ U ∪ F := by
    intro h
    rcases mem_union.mp h with hu | hf
    · exact (not_le.mpr hz) (Nat.le_of_dvd r.den_pos (hpden z hu))
    · exact hfclean hp₀ hf ((hpden p₀ hp₀).trans hdz)
  let S := insert z (U ∪ F)
  have hSpos : ∀ k ∈ S, 0 < k := by
    intro k hk
    rcases mem_insert.mp hk with rfl | h
    · exact hz0
    · exact hpos k h
  have hS : mass S = n := by
    change mass (insert z (U ∪ F)) = _
    rw [mass, sum_insert hznot, sum_union hdis]
    change 1/(z:ℚ) + (mass U + mass F) = n
    dsimp [r] at hsum
    linarith
  have hsmall : mass F < 1 := by
    have : (0:ℚ) < 1 / z := by positivity
    linarith
  have no_omit (T : Finset ℕ) (ht : T ⊆ U ∪ F) (hT : T.Nonempty)
      (j : ℤ) (he : mass T = j) : False := by
    have hsub : T ⊆ F := by
      intro p hpt
      rcases mem_union.mp (ht hpt) with hp | hf
      · exfalso
        have hd := marker (hU p hp).1 hpt (fun k hk hne => by
          refine ⟨hpos k (ht hk), ?_⟩
          rcases mem_union.mp (ht hk) with h | h
          · exact fun h' => hne ((Nat.prime_dvd_prime_iff_eq (hU p hp).1 (hU k h).1).mp h').symm
          · exact hfclean hp h)
        rw [he, Rat.den_intCast] at hd
        exact (hU p hp).1.not_dvd_one hd
      · exact hf
    have hle : mass T ≤ mass F :=
      sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by positivity)
    have hpoz : 0 < mass T :=
      Finset.sum_pos (fun i hi => by exact one_div_pos.mpr (by exact_mod_cast hpos i (ht hi))) hT
    have h1 : (j:ℚ) < 1 := he ▸ hle.trans_lt hsmall
    have h2 : 0 < (j:ℚ) := he ▸ hpoz
    have : j < 1 := by exact_mod_cast h1
    have : 0 < j := by exact_mod_cast h2
    omega
  refine ⟨S,hSpos,hS,?_⟩
  intro T hT m hm he
  by_cases hzt : z ∈ T
  · let C := S \ T
    have hc : C.Nonempty := Finset.sdiff_nonempty.mpr (not_subset_of_ssubset hT)
    have hcsub : C ⊆ U ∪ F := by
      intro k hk
      rcases mem_sdiff.mp hk with ⟨hkS,hkT⟩
      rcases mem_insert.mp hkS with rfl | h
      · exact (hkT hzt).elim
      · exact h
    apply no_omit C hcsub hc ((n:ℤ)-m)
    have hparts := Finset.sum_sdiff hT.subset (f := fun k : ℕ => 1 / (k:ℚ))
    change mass C + mass T = mass S at hparts
    push_cast
    linarith
  · have hts : T ⊆ U ∪ F := by
      intro k hk
      rcases mem_insert.mp (hT.subset hk) with rfl | h
      · exact (hzt hk).elim
      · exact h
    have htne : T.Nonempty := by
      apply Finset.nonempty_iff_ne_empty.mpr
      intro h0
      have he0 : (0:ℚ) = m := by simpa [h0, mass] using he
      exact (Nat.cast_pos.mpr hm : (0:ℚ) < m).ne he0
    exact no_omit T hts htne m (by exact_mod_cast he)

end Egypt

theorem OMA.solution : type_of% @OMA.S_mo_215301.main := Egypt.build
