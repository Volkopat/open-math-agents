import FormalConjectures.Paper.PartitionParity

/-!
A finite counting version of Zheng's square - root bound (Appendix A of
Ono and Swaminathan, arXiv:2509.09553). Only the order of growth is needed.
We count squarefree discriminants by discarding large square factors and
bound the total number of reduced forms by encoding their coefficients.
For every real x ≥ 10¹² the resulting conditional bound is
√x ≤ 768000000 times the number of odd partition values through x.

The parity input is the catalogue theorem PartitionParity.ono_swaminathan.odd_bound.
The class - number comparison follows from PartitionParity.classNumber_eq_ncard_reducedForms.
Credit: @yuka30240
-/

namespace OMA.R_PartitionParity_zheng_odd_R2

open Finset Nat Filter Asymptotics Polynomial
open scoped BigOperators

/-- A large square factor has few multiples. Summing the elementary bound
`1 / m² ≤ 1 / (m-1) - 1 / m` makes the tail uniform in its length. -/
private lemma square_tail (N K : ℕ) :
    ((∑ i ∈ range K, N / (49 + i) ^ 2 : ℕ) : ℝ) ≤
      N / 48 - N / (48 + (K : ℝ)) := by
  induction K with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, Nat.cast_add, Nat.cast_succ]
    have hd : ((N / (49 + k) ^ 2 : ℕ) : ℝ) ≤ N / (49 + (k : ℝ)) ^ 2 := by
      apply (le_div_iff₀ (by positivity)).2
      exact_mod_cast Nat.div_mul_le_self N ((49 + k) ^ 2)
    have he : (N : ℝ) / (49 + k) ^ 2 ≤ N / (48 + k) - N / (49 + k) := by
      field_simp
      nlinarith [show 0 ≤ (N : ℝ) * (49 + k) by positivity]
    rw [show (48 + ((k : ℝ) + 1)) = 49 + k by ring]
    linarith

private lemma disc_mod {m D : ℕ} (h : (m ^ 2 * D) % 24 = 23) : D % 24 = 23 := by
  have tab : ∀ a b : Fin 24, (a.val ^ 2 * b.val) % 24 = 23 → b.val = 23 := by decide
  apply tab ⟨m % 24, Nat.mod_lt _ (by decide)⟩ ⟨D % 24, Nat.mod_lt _ (by decide)⟩
  simpa [Nat.mul_mod, Nat.pow_mod] using h

/-- Among the squarefree parts of the integers `24j+23`, the first 48
possible square multipliers account for at least half the indices. -/
private lemma disc_count (J : ℕ) :
    J ≤ 96 * ((range (24 * J + 1)).filter (fun D => D % 24 = 23 ∧ Squarefree D)).card := by
  classical
  let N := 24 * J
  let A := (range (N + 1)).filter (fun D => D % 24 = 23 ∧ Squarefree D)
  let S := (range J).image (fun j => 24 * j + 23)
  let small := A.biUnion (fun D => (Icc 1 48).image (fun m : ℕ => m ^ 2 * D))
  let large := (range N).biUnion (fun i =>
    (Icc 1 (N / (49 + i) ^ 2)).image (fun D : ℕ => (49 + i) ^ 2 * D))
  have cover : S ⊆ small ∪ large := by
    intro n hn
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hn
    have hj' := mem_range.mp hj
    have hn' : 24 * j + 23 ≤ N := by dsimp [N]; omega
    obtain ⟨D, m, hD, hm, he, hsq⟩ := Nat.sq_mul_squarefree_of_pos
      (show 0 < 24 * j + 23 by omega)
    have hpow : 1 ≤ m ^ 2 := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ hm.ne')
    have hDle : D ≤ N := by nlinarith only [he, hn', Nat.mul_le_mul_right D hpow]
    have hmod : D % 24 = 23 := disc_mod (by rw [he]; omega)
    by_cases hc : m ≤ 48
    · exact mem_union_left _ (mem_biUnion.mpr ⟨D,
        mem_filter.mpr ⟨mem_range.mpr (by omega), hmod, hsq⟩,
        mem_image.mpr ⟨m, mem_Icc.mpr ⟨hm, hc⟩, he⟩⟩)
    · have hml : m ≤ N := by
        nlinarith only [he, hn', Nat.mul_le_mul_left (m ^ 2) hD, Nat.mul_le_mul_left m hm]
      have e : 49 + (m - 49) = m := by omega
      apply mem_union_right _ (mem_biUnion.mpr ⟨m - 49, mem_range.mpr (by omega), ?_⟩)
      rw [e]
      exact mem_image.mpr ⟨D, mem_Icc.mpr ⟨hD, (Nat.le_div_iff_mul_le (by positivity)).2
        (by simpa [Nat.mul_comm] using he.le.trans hn')⟩, he⟩
  have hsmall : small.card ≤ A.card * 48 := by
    apply card_biUnion_le_card_mul
    intro D _
    exact card_image_le.trans (by simp)
  have hlarge : large.card ≤ ∑ i ∈ range N, N / (49 + i) ^ 2 := by
    refine card_biUnion_le.trans (sum_le_sum fun i _ => ?_)
    exact card_image_le.trans (by simp)
  have hS : S.card = J := by
    rw [show S = _ from rfl, Finset.card_image_of_injective _ (by intro x y h; dsimp at h; omega),
      card_range]
  have total := (card_le_card cover).trans (card_union_le _ _)
  have htail := square_tail N N
  have hhalf : 2 * (∑ i ∈ range N, N / (49 + i) ^ 2) ≤ J := by
    have hnon : 0 ≤ (N : ℝ) / (48 + N) := by positivity
    dsimp [N] at htail hnon ⊢
    simp only [Nat.cast_mul, Nat.cast_ofNat] at htail hnon
    exact_mod_cast (by linarith : 2 * ((∑ i ∈ range (24 * J), 24 * J / (49 + i) ^ 2 : ℕ) : ℝ) ≤ J)
  change J ≤ 96 * A.card
  omega

/-- All reduced forms with discriminant between `-24t²` and `-1` fit in a
rectangle with at most `305t³` lattice points. The second coordinate stores
both `c` and `b+a` in radix `2a+1`. -/
private lemma form_total (t : ℕ) (ht : 0 < t) (A : Finset ℕ)
    (hA : ∀ D ∈ A, 0 < D ∧ D ≤ 24 * t ^ 2) :
    (∑ D ∈ A, {p : ℤ × ℤ × ℤ | PartitionParity.IsReducedForm D p.1 p.2.1 p.2.2}.ncard)
      ≤ 305 * t ^ 3 := by
  classical
  let B := Icc (1 : ℤ) (5 * t) ×ˢ Icc (0 : ℤ) (60 * (t : ℤ) ^ 2)
  let decode (u : ℤ × ℤ) : ℤ × ℤ × ℤ :=
    (u.1, u.2 % (2 * u.1 + 1) - u.1, u.2 / (2 * u.1 + 1))
  let disc (u : ℤ × ℤ) : ℕ :=
    (4 * u.1 * (decode u).2.2 - (decode u).2.1 ^ 2).toNat
  have cover (D : ℕ) (hD : D ∈ A) :
      {p : ℤ × ℤ × ℤ | PartitionParity.IsReducedForm D p.1 p.2.1 p.2.2} ⊆
        ((B.filter (fun u => disc u = D)).image decode : Set (ℤ × ℤ × ℤ)) := by
    rintro ⟨a, b, c⟩ ⟨he, hba, hac, _, _⟩
    dsimp only at he hba hac
    obtain ⟨hpos, hle⟩ := hA D hD
    have hp : (0 : ℤ) < D := by exact_mod_cast hpos
    have hle' : (D : ℤ) ≤ 24 * (t : ℤ) ^ 2 := by exact_mod_cast hle
    have ⟨hneg, hplus⟩ := abs_le.mp hba
    have ha : 0 < a := by
      by_contra! hz
      have : a = 0 := by omega
      have : b = 0 := by omega
      nlinarith
    have hb2 : b ^ 2 ≤ a ^ 2 := by
      nlinarith [mul_nonneg (show 0 ≤ a - b by omega)
        (show 0 ≤ a + b by omega)]
    have haa : a ^ 2 ≤ a * c := by nlinarith [mul_nonneg ha.le (sub_nonneg.mpr hac)]
    have hat : a ≤ 5 * (t : ℤ) := by
      by_contra! h
      nlinarith [mul_self_le_mul_self (show 0 ≤ 5 * (t : ℤ) by positivity) h.le]
    let q := b + a + (2 * a + 1) * c
    have hr : 0 ≤ b + a := by omega
    have hr' : b + a < 2 * a + 1 := by omega
    have hc : 0 < c := by omega
    have hq : 0 ≤ q := by dsimp [q]; positivity
    have hq' : q ≤ 60 * (t : ℤ) ^ 2 := by
      dsimp [q]
      nlinarith [mul_nonneg (show 0 ≤ a - 1 by omega) hc.le,
        mul_nonneg ha.le (show 0 ≤ c - 1 by omega)]
    have hu : (a, q) ∈ B := mem_product.mpr ⟨mem_Icc.mpr ⟨by omega, hat⟩, mem_Icc.mpr ⟨hq, hq'⟩⟩
    have hd : decode (a, q) = (a, b, c) := by
      dsimp [decode, q]
      simp [Int.add_mul_ediv_left _ _ (show 2 * a + 1 ≠ 0 by omega),
        Int.emod_eq_of_lt hr hr', Int.ediv_eq_zero_of_lt hr hr']
    apply mem_image.mpr ⟨(a, q), mem_filter.mpr ⟨hu, ?_⟩, hd⟩
    change (4 * a * (decode (a, q)).2.2 - (decode (a, q)).2.1 ^ 2).toNat = D
    rw [hd]
    dsimp
    rw [show 4 * a * c - b ^ 2 = (D : ℤ) by linarith]
    simp
  calc
    _ ≤ ∑ D ∈ A, (B.filter (fun u => disc u = D)).card := by
      apply sum_le_sum
      intro D hD
      exact (Set.ncard_le_ncard (cover D hD) (Finset.finite_toSet _)).trans
        (by rw [Set.ncard_coe_finset]; exact card_image_le)
    _ = _ := sum_card_fiberwise_eq_card_filter B A disc
    _ ≤ B.card := card_filter_le _ _
    _ ≤ _ := by
      simp [B, Int.card_Icc]
      zify
      rw [Int.toNat_of_nonneg (by positivity), Int.toNat_of_nonneg (by positivity)]
      nlinarith [show (1 : ℤ) ≤ t by exact_mod_cast ht,
        mul_nonneg (show 0 ≤ (t : ℤ) ^ 2 - 1 by nlinarith [show (1 : ℤ) ≤ t by exact_mod_cast ht])
          (show 0 ≤ (t : ℤ) by positivity)]

/-- Discard discriminants whose number of forms exceeds 60000 times the scale. -/
private lemma good_discs (t : ℕ) (ht : 0 < t) :
    ∃ G : Finset ℕ, t ^ 2 ≤ 192 * G.card ∧ ∀ D ∈ G,
      D ≤ 24 * t ^ 2 ∧ D % 24 = 23 ∧ Squarefree D ∧
      {p : ℤ × ℤ × ℤ | PartitionParity.IsReducedForm D p.1 p.2.1 p.2.2}.ncard ≤ 60000 * t := by
  classical
  let A := (range (24 * t ^ 2 + 1)).filter (fun D => D % 24 = 23 ∧ Squarefree D)
  let forms := fun D => {p : ℤ × ℤ × ℤ | PartitionParity.IsReducedForm D p.1 p.2.1 p.2.2}.ncard
  let G := A.filter (fun D => forms D ≤ 60000 * t)
  have hA (D : ℕ) (h : D ∈ A) : 0 < D ∧ D ≤ 24 * t ^ 2 := by
    obtain ⟨h₁, h₂, _⟩ := mem_filter.mp h
    simp only [mem_range] at h₁
    omega
  have hbad : (A \ G).card * (60000 * t) ≤ 305 * t ^ 3 := calc
    _ = ∑ _ ∈ A \ G, 60000 * t := by simp
    _ ≤ ∑ D ∈ A \ G, forms D := by
      apply sum_le_sum
      intro D h
      obtain ⟨ha, hg⟩ := mem_sdiff.mp h
      exact Nat.le_of_lt (lt_of_not_ge fun hle => hg (mem_filter.mpr ⟨ha, hle⟩))
    _ ≤ ∑ D ∈ A, forms D := sum_le_sum_of_subset_of_nonneg sdiff_subset (by intros; omega)
    _ ≤ _ := form_total t ht A hA
  have hbad' : 192 * (A \ G).card ≤ t ^ 2 := by
    apply Nat.le_of_mul_le_mul_right (c := 305 * t) ?_ (by positivity)
    nlinarith only [hbad, Nat.zero_le ((A \ G).card * t)]
  refine ⟨G, ?_, ?_⟩
  · have hcount : t ^ 2 ≤ 96 * A.card := disc_count _
    have hsplit : (A \ G).card + G.card = A.card := card_sdiff_add_card_eq_card (filter_subset _ _)
    omega
  · intro D h
    obtain ⟨ha, hf⟩ := mem_filter.mp h
    obtain ⟨_, hm, hsq⟩ := mem_filter.mp ha
    exact ⟨(hA D ha).2, hm, hsq, hf⟩

/-- The odd witness in Theorem 1 of Ono and Swaminathan. -/
def H1 : Prop := ∀ (D : ℕ) (hD : 1 < D), Squarefree D → D % 24 = 23 →
  haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
    ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by omega))⟩
  ∃ m : ℕ, m.Coprime 6 ∧
    m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
    Odd (partitionNumber ((D * m ^ 2 + 1) / 24))

/-- The upper bound direction of the reduced-form interpretation of the class number. -/
def H2 : Prop := ∀ (D : ℕ) (hD : 1 < D), Squarefree D → D % 24 = 23 →
  haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
    ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by omega))⟩
  NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) ≤
    {p : ℤ × ℤ × ℤ | PartitionParity.IsReducedForm D p.1 p.2.1 p.2.2}.ncard

section

private lemma index_eq {m D : ℕ} (hm : m.Coprime 6) (hD : D % 24 = 23) :
    24 * ((D * m ^ 2 + 1) / 24) = D * m ^ 2 + 1 := by
  have tab : ∀ a : Fin 24, (a.val % 6).Coprime 6 → a.val ^ 2 % 24 = 1 := by decide
  have h6 : (m % 24 % 6).Coprime 6 := by
    rw [Nat.mod_mod_of_dvd _ (by decide : 6 ∣ 24)]
    exact (ZMod.coprime_mod_iff_coprime _ _).mpr hm
  have h1 := tab ⟨m % 24, Nat.mod_lt _ (by decide)⟩ h6
  have h1' : m ^ 2 % 24 = 1 := by simpa [Nat.pow_mod] using h1
  apply Nat.mul_div_cancel'
  apply Nat.dvd_of_mod_eq_zero
  rw [Nat.add_mod, Nat.mul_mod, hD, h1']

/-- The parity of each prime valuation recovers the squarefree discriminant. -/
private lemma disc_unique {D E m k : ℕ} (hd : Squarefree D) (he : Squarefree E)
    (hm : m ≠ 0) (hk : k ≠ 0) (h : D * m ^ 2 = E * k ^ 2) : D = E := by
  apply Nat.factorization_inj hd.ne_zero he.ne_zero
  ext p
  have hf := congrArg (fun n : ℕ => n.factorization p) h
  simp only [Nat.factorization_mul hd.ne_zero (pow_ne_zero _ hm),
    Nat.factorization_mul he.ne_zero (pow_ne_zero _ hk), Nat.factorization_pow,
    Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at hf
  have hd1 := (Nat.squarefree_iff_factorization_le_one hd.ne_zero).mp hd p
  have he1 := (Nat.squarefree_iff_factorization_le_one he.ne_zero).mp he p
  omega

/-- Distinct good discriminants give distinct odd indices below the cutoff. -/
private lemma finite_bound (hp : H1) (hc : H2) (t : ℕ) (ht : 0 < t) (x : ℝ)
    (hx : ((1000000 * t ^ 2 : ℕ) : ℝ) ^ 2 ≤ x) :
    t ^ 2 ≤ 192 * {n : ℕ | (n : ℝ) ≤ x ∧ Odd (partitionNumber n)}.ncard := by
  classical
  obtain ⟨G, hsize, hG⟩ := good_discs t ht
  have witnesses (D : ℕ) (h : D ∈ G) : ∃ m : ℕ, m ≠ 0 ∧ m ≤ 1000000 * t ∧
      24 * ((D * m ^ 2 + 1) / 24) = D * m ^ 2 + 1 ∧ Odd (partitionNumber ((D * m ^ 2 + 1) / 24)) := by
    obtain ⟨_, hmod, hsq, hforms⟩ := hG D h
    have hD : 1 < D := by omega
    obtain ⟨m, hm, hle, ho⟩ := hp D hD hsq hmod
    have hclass := hc D hD hsq hmod
    have hm0 : m ≠ 0 := by rintro rfl; norm_num at hm
    exact ⟨m, hm0, by omega, index_eq hm hmod, ho⟩
  choose! m hm using witnesses
  let idx := fun D => (D * (m D) ^ 2 + 1) / 24
  let T := {n : ℕ | (n : ℝ) ≤ x ∧ Odd (partitionNumber n)}
  have hcard : G.card ≤ T.ncard := by
    rw [← Set.ncard_coe_finset]
    refine Set.ncard_le_ncard_of_injOn idx ?_ ?_ ?_
    · intro D h
      obtain ⟨_, hmt, he, ho⟩ := hm D h
      have hDt := (hG D h).1
      have hprod := Nat.mul_le_mul hDt (Nat.pow_le_pow_left hmt 2)
      have hi : idx D ≤ (1000000 * t ^ 2) ^ 2 := by
        dsimp [idx]
        nlinarith only [he, hprod]
      exact ⟨(by exact_mod_cast hi : (idx D : ℝ) ≤ ((1000000 * t ^ 2 : ℕ) : ℝ) ^ 2).trans hx, ho⟩
    · intro D hD E hE hij
      apply disc_unique (hG D hD).2.2.1 (hG E hE).2.2.1 (hm D hD).1 (hm E hE).1
      have he := (hm E hE).2.2.1
      have hd := (hm D hD).2.2.1
      change idx D = idx E at hij
      change 24 * idx D = _ at hd
      change 24 * idx E = _ at he
      omega
    · exact (Set.finite_le_nat ⌊x⌋₊).subset fun n (hn : n ∈ T) => Nat.le_floor hn.1
  exact hsize.trans (Nat.mul_le_mul_left _ hcard)

/-- An explicit, unoptimized bound at every real cutoff past the threshold. -/
lemma sqrt_le_odd_count (hp : H1) (hc : H2) {x : ℝ} (hx : 1000000000000 ≤ x) :
    Real.sqrt x ≤ 768000000 * ({n : ℕ | (n : ℝ) ≤ x ∧ Odd (partitionNumber n)}.ncard : ℝ) := by
  have hx0 : 0 ≤ x := by linarith
  let y := Real.sqrt (Real.sqrt x / 1000000)
  have hy0 : 0 ≤ y := Real.sqrt_nonneg _
  have hy : y ^ 2 = Real.sqrt x / 1000000 := Real.sq_sqrt (by positivity)
  have hroot : (1000000 : ℝ) ≤ Real.sqrt x := by
    exact (Real.le_sqrt (by norm_num) hx0).2 (by linarith)
  have hy1 : 1 ≤ y := by nlinarith
  let t := ⌊y⌋₊
  have ht : 0 < t := Nat.floor_pos.mpr hy1
  have hty : (t : ℝ) ≤ y := Nat.floor_le hy0
  have hyt : y ≤ 2 * (t : ℝ) := by
    have h1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
    linarith [Nat.lt_floor_add_one y]
  have hscale : 1000000 * (t : ℝ) ^ 2 ≤ Real.sqrt x := by
    nlinarith [sq_le_sq' (by linarith : -y ≤ (t : ℝ)) hty]
  have hcap : ((1000000 * t ^ 2 : ℕ) : ℝ) ^ 2 ≤ x := by
    push_cast
    have hl : -Real.sqrt x ≤ 1000000 * (t : ℝ) ^ 2 := by
      linarith [Real.sqrt_nonneg x, sq_nonneg (t : ℝ)]
    nlinarith [sq_le_sq' hl hscale, Real.sq_sqrt hx0]
  have hb := finite_bound hp hc t ht x hcap
  have hb' : (t : ℝ) ^ 2 ≤ 192 * ({n : ℕ | (n : ℝ) ≤ x ∧ Odd (partitionNumber n)}.ncard : ℝ) := by
    exact_mod_cast hb
  nlinarith [sq_le_sq' (by linarith [show (0 : ℝ) ≤ t by positivity] : -(2 * (t : ℝ)) ≤ y) hyt]

end

theorem main : H1 → H2 → type_of% @PartitionParity.zheng.odd := by
  intro hp hc
  apply IsBigO.of_bound 768000000
  filter_upwards [eventually_ge_atTop (1000000000000 : ℝ)] with x hx
  simpa only [Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.norm_natCast] using
    sqrt_le_odd_count hp hc hx

end OMA.R_PartitionParity_zheng_odd_R2
