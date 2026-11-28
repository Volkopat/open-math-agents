import FormalConjectures.ErdosProblems.«325»

-- Reduction Erdos325.erdos_325.variants.weaker.R1 of Erdős Problem 325 (weaker form)
-- Credit: @LordMike
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Sums of three `k`-th powers: the large exponents are known

The target asks for `f_{k,3}(x) ≫ x^(3/k - ε)` for every `k ≥ 3`, where `f_{k,3}(x)` counts the
`n ≤ x` that are sums of three `k`-th powers.

* `H1` (open core): the target for the finitely many exponents `3 ≤ k < 26`. It is a special
  case of the target.
* `H2` (known, deep): paucity of non-trivial solutions of
  `a^k + b^k + c^k = d^k + e^k + f^k` in positive integers at most `B`, for `k ≥ 26`. Here a
  solution is trivial if `(d, e, f)` is a permutation of `(a, b, c)`. This is P. Salberger,
  *Counting rational points on hypersurfaces of low dimension*, Ann. Sci. École Norm. Sup. 38
  (2005), 93-115, Corollary 4.6 and Remark 4.7. For `k ≥ 33` it is the theorem of T. D. Browning
  and D. R. Heath-Brown, *Equal sums of three powers*, Invent. Math. 157 (2004), 553-573.

`main` handles `k ≥ 26` as in the corollary of Browning and Heath-Brown. There are at most
`27 B^3` trivial solutions, so `H2` bounds the number of all solutions by `O(B^3)`. By the
Cauchy-Schwarz inequality the `B^3` triples in `[1, B]^3` then have `≫ B^3` distinct sums, all
at most `3 B^k`. Taking `B = ⌊x^(1/k) / 3⌋` gives `f_{k,3}(x) ≫ x^(3/k)`.
-/

namespace OMA.R_Erdos325_erdos_325_variants_weaker_R1

open Asymptotics Filter Finset

/-- The target for the exponents `3 ≤ k < 26`. -/
def H1 : Prop :=
  ∀ ε > (0 : ℝ), ∀ k : ℕ, 3 ≤ k → k < 26 →
    (fun x : ℕ => (x : ℝ) ^ ((3 / k : ℝ) - ε)) =O[atTop]
      (fun x => (Erdos325.cardIsSumThreePowerBelow k x : ℝ))

/-- Salberger (2005), after Browning and Heath-Brown (2004): for `k ≥ 26` the equation
`a^k + b^k + c^k = d^k + e^k + f^k` has `O(B^(3 - δ))` solutions in positive integers at most `B`
in which `(d, e, f)` is not a permutation of `(a, b, c)`. -/
def H2 : Prop :=
  ∀ k : ℕ, 26 ≤ k → ∃ δ > (0 : ℝ), ∃ C : ℝ, ∀ B : ℕ,
    ((((Finset.Icc 1 B ×ˢ Finset.Icc 1 B ×ˢ Finset.Icc 1 B) ×ˢ
        (Finset.Icc 1 B ×ˢ Finset.Icc 1 B ×ˢ Finset.Icc 1 B)).filter
      fun p : (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ) =>
        p.1.1 ^ k + p.1.2.1 ^ k + p.1.2.2 ^ k = p.2.1 ^ k + p.2.2.1 ^ k + p.2.2.2 ^ k ∧
          ¬ [p.2.1, p.2.2.1, p.2.2.2].Perm [p.1.1, p.1.2.1, p.1.2.2]).card : ℝ) ≤
      C * (B : ℝ) ^ (3 - δ)

/-- Cauchy-Schwarz: a map on a finite set has few values only if it has many collisions. -/
lemma card_sq_le_card_image_mul {α : Type*} [DecidableEq α] (S : Finset α) (f : α → ℕ) :
    S.card ^ 2 ≤ (S.image f).card * ((S ×ˢ S).filter (fun p => f p.1 = f p.2)).card := by
  have h1 : S.card = ∑ n ∈ S.image f, (S.filter (fun a => f a = n)).card :=
    card_eq_sum_card_fiberwise (fun a ha => mem_coe.2 (mem_image_of_mem f (mem_coe.1 ha)))
  have h2 : ((S ×ˢ S).filter (fun p => f p.1 = f p.2)).card
      = ∑ n ∈ S.image f, (S.filter (fun a => f a = n)).card ^ 2 := by
    rw [card_eq_sum_card_fiberwise (f := fun p : α × α => f p.1) (t := S.image f)]
    · refine sum_congr rfl fun n _ => ?_
      rw [sq, ← card_product]
      congr 1
      ext ⟨a, b⟩
      simp only [mem_filter, mem_product]
      constructor
      · rintro ⟨⟨⟨ha, hb⟩, hab⟩, hn⟩
        exact ⟨⟨ha, hn⟩, hb, hab.symm.trans hn⟩
      · rintro ⟨⟨ha, hna⟩, hb, hnb⟩
        exact ⟨⟨⟨ha, hb⟩, hna.trans hnb.symm⟩, hna⟩
    · intro p hp
      have hp' := (mem_filter.1 (mem_coe.1 hp)).1
      exact mem_coe.2 (mem_image_of_mem f (mem_product.1 hp').1)
  rw [h2]
  calc S.card ^ 2 = (∑ n ∈ S.image f, (S.filter (fun a => f a = n)).card) ^ 2 := by rw [← h1]
    _ ≤ (S.image f).card * ∑ n ∈ S.image f, (S.filter (fun a => f a = n)).card ^ 2 := by
        simpa using sq_sum_le_card_mul_sum_sq (s := S.image f)
          (f := fun n => (S.filter (fun a => f a = n)).card)

/-- There are `B^3` triples in `[1, B]^3`. -/
lemma card_cube (B : ℕ) : (Icc 1 B ×ˢ Icc 1 B ×ˢ Icc 1 B).card = B ^ 3 := by
  simp only [card_product, Nat.card_Icc, Nat.add_sub_cancel]
  ring

/-- At most `27 B^3` pairs of triples in `[1, B]^3` are permutations of each other. -/
lemma card_perm_le (B : ℕ) :
    (((Icc 1 B ×ˢ Icc 1 B ×ˢ Icc 1 B) ×ˢ (Icc 1 B ×ˢ Icc 1 B ×ˢ Icc 1 B)).filter
      fun p : (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ) =>
        [p.2.1, p.2.2.1, p.2.2.2].Perm [p.1.1, p.1.2.1, p.1.2.2]).card ≤ 27 * B ^ 3 := by
  let g : ℕ × ℕ × ℕ → Finset ((ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)) := fun t =>
    ({t} : Finset (ℕ × ℕ × ℕ)) ×ˢ
      (({t.1, t.2.1, t.2.2} : Finset ℕ) ×ˢ ({t.1, t.2.1, t.2.2} : Finset ℕ) ×ˢ
        ({t.1, t.2.1, t.2.2} : Finset ℕ))
  have hsub : (((Icc 1 B ×ˢ Icc 1 B ×ˢ Icc 1 B) ×ˢ (Icc 1 B ×ˢ Icc 1 B ×ˢ Icc 1 B)).filter
      fun p : (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ) =>
        [p.2.1, p.2.2.1, p.2.2.2].Perm [p.1.1, p.1.2.1, p.1.2.2]) ⊆
      (Icc 1 B ×ˢ Icc 1 B ×ˢ Icc 1 B).biUnion g := by
    rintro ⟨⟨a, b, c⟩, ⟨d, e, f⟩⟩ hp
    obtain ⟨hmem, hperm⟩ := mem_filter.1 hp
    have hd : d = a ∨ d = b ∨ d = c := by
      simpa using hperm.subset (List.mem_cons_self (a := d) (l := [e, f]))
    have he : e = a ∨ e = b ∨ e = c := by
      simpa using hperm.subset (show e ∈ [d, e, f] by simp)
    have hf : f = a ∨ f = b ∨ f = c := by
      simpa using hperm.subset (show f ∈ [d, e, f] by simp)
    refine mem_biUnion.2 ⟨(a, b, c), (mem_product.1 hmem).1, ?_⟩
    simp only [g, mem_product, mem_singleton, mem_insert, true_and]
    exact ⟨hd, he, hf⟩
  have hg : ∀ t ∈ Icc 1 B ×ˢ Icc 1 B ×ˢ Icc 1 B, (g t).card ≤ 27 := by
    intro t _
    have h3 : ({t.1, t.2.1, t.2.2} : Finset ℕ).card ≤ 3 := card_le_three
    simp only [g, card_product, card_singleton, one_mul]
    calc _ ≤ 3 * (3 * 3) := Nat.mul_le_mul h3 (Nat.mul_le_mul h3 h3)
      _ = 27 := by norm_num
  calc _ ≤ ((Icc 1 B ×ˢ Icc 1 B ×ˢ Icc 1 B).biUnion g).card := card_le_card hsub
    _ ≤ ∑ t ∈ Icc 1 B ×ˢ Icc 1 B ×ˢ Icc 1 B, (g t).card := card_biUnion_le
    _ ≤ ∑ _t ∈ Icc 1 B ×ˢ Icc 1 B ×ˢ Icc 1 B, 27 := sum_le_sum hg
    _ = 27 * B ^ 3 := by rw [sum_const, card_cube, smul_eq_mul, mul_comm]

/-- From the paucity bound: the triples in `[1, B]^3` have `≫ B^3` distinct sums of `k`-th
powers. -/
lemma cube_le_card_image (k : ℕ) (δ C : ℝ) (hδ : 0 < δ)
    (hC : ∀ B : ℕ,
      ((((Icc 1 B ×ˢ Icc 1 B ×ˢ Icc 1 B) ×ˢ (Icc 1 B ×ˢ Icc 1 B ×ˢ Icc 1 B)).filter
        fun p : (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ) =>
          p.1.1 ^ k + p.1.2.1 ^ k + p.1.2.2 ^ k = p.2.1 ^ k + p.2.2.1 ^ k + p.2.2.2 ^ k ∧
            ¬ [p.2.1, p.2.2.1, p.2.2.2].Perm [p.1.1, p.1.2.1, p.1.2.2]).card : ℝ) ≤
        C * (B : ℝ) ^ (3 - δ))
    (B : ℕ) (hB : 1 ≤ B) :
    (B : ℝ) ^ 3 ≤ (max C 0 + 27) *
      (((Icc 1 B ×ˢ Icc 1 B ×ˢ Icc 1 B).image
        fun t : ℕ × ℕ × ℕ => t.1 ^ k + t.2.1 ^ k + t.2.2 ^ k).card : ℝ) := by
  have hCS := card_sq_le_card_image_mul (Icc 1 B ×ˢ Icc 1 B ×ˢ Icc 1 B)
    (fun t : ℕ × ℕ × ℕ => t.1 ^ k + t.2.1 ^ k + t.2.2 ^ k)
  rw [card_cube] at hCS
  have hE : (((Icc 1 B ×ˢ Icc 1 B ×ˢ Icc 1 B) ×ˢ (Icc 1 B ×ˢ Icc 1 B ×ˢ Icc 1 B)).filter
      (fun p : (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ) =>
        p.1.1 ^ k + p.1.2.1 ^ k + p.1.2.2 ^ k = p.2.1 ^ k + p.2.2.1 ^ k + p.2.2.2 ^ k)).card ≤
      (((Icc 1 B ×ˢ Icc 1 B ×ˢ Icc 1 B) ×ˢ (Icc 1 B ×ˢ Icc 1 B ×ˢ Icc 1 B)).filter
        fun p : (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ) =>
          p.1.1 ^ k + p.1.2.1 ^ k + p.1.2.2 ^ k = p.2.1 ^ k + p.2.2.1 ^ k + p.2.2.2 ^ k ∧
            ¬ [p.2.1, p.2.2.1, p.2.2.2].Perm [p.1.1, p.1.2.1, p.1.2.2]).card +
      (((Icc 1 B ×ˢ Icc 1 B ×ˢ Icc 1 B) ×ˢ (Icc 1 B ×ˢ Icc 1 B ×ˢ Icc 1 B)).filter
        fun p : (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ) =>
          [p.2.1, p.2.2.1, p.2.2.2].Perm [p.1.1, p.1.2.1, p.1.2.2]).card := by
    refine (card_le_card ?_).trans (card_union_le _ _)
    intro p hp
    obtain ⟨hm, he⟩ := mem_filter.1 hp
    by_cases hperm : [p.2.1, p.2.2.1, p.2.2.2].Perm [p.1.1, p.1.2.1, p.1.2.2]
    · exact mem_union_right _ (mem_filter.2 ⟨hm, hperm⟩)
    · exact mem_union_left _ (mem_filter.2 ⟨hm, he, hperm⟩)
  have hT := card_perm_le B
  have hN := hC B
  have hBpos : (0 : ℝ) < (B : ℝ) ^ 3 := by positivity
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hpow : (B : ℝ) ^ (3 - δ) ≤ (B : ℝ) ^ 3 := by
    have h := Real.rpow_le_rpow_of_exponent_le hB1 (by push_cast; linarith : 3 - δ ≤ ((3 : ℕ) : ℝ))
    rwa [Real.rpow_natCast] at h
  have hpow0 : (0 : ℝ) ≤ (B : ℝ) ^ (3 - δ) := by positivity
  have hN' : C * (B : ℝ) ^ (3 - δ) ≤ max C 0 * (B : ℝ) ^ 3 :=
    (mul_le_mul_of_nonneg_right (le_max_left C 0) hpow0).trans
      (mul_le_mul_of_nonneg_left hpow (le_max_right C 0))
  have hEr : ((((Icc 1 B ×ˢ Icc 1 B ×ˢ Icc 1 B) ×ˢ (Icc 1 B ×ˢ Icc 1 B ×ˢ Icc 1 B)).filter
      (fun p : (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ) =>
        p.1.1 ^ k + p.1.2.1 ^ k + p.1.2.2 ^ k
          = p.2.1 ^ k + p.2.2.1 ^ k + p.2.2.2 ^ k)).card : ℝ) ≤
      (max C 0 + 27) * (B : ℝ) ^ 3 := by
    have hE' := (Nat.cast_le (α := ℝ)).2 (hE.trans (Nat.add_le_add_left hT _))
    push_cast at hE'
    linarith
  have hCS' := (Nat.cast_le (α := ℝ)).2 hCS
  push_cast at hCS'
  have hI : (0 : ℝ) ≤ (((Icc 1 B ×ˢ Icc 1 B ×ˢ Icc 1 B).image
      fun t : ℕ × ℕ × ℕ => t.1 ^ k + t.2.1 ^ k + t.2.2 ^ k).card : ℝ) := Nat.cast_nonneg _
  have hfin : (B : ℝ) ^ 3 * (B : ℝ) ^ 3 ≤ ((max C 0 + 27) *
      (((Icc 1 B ×ˢ Icc 1 B ×ˢ Icc 1 B).image
        fun t : ℕ × ℕ × ℕ => t.1 ^ k + t.2.1 ^ k + t.2.2 ^ k).card : ℝ)) * (B : ℝ) ^ 3 := by
    have := mul_le_mul_of_nonneg_left hEr hI
    nlinarith [this, hCS']
  exact le_of_mul_le_mul_right hfin hBpos

/-- The sums of three `k`-th powers of integers in `[1, B]` are counted by the target. -/
lemma card_image_le (k B x : ℕ) (h : 3 * B ^ k ≤ x) :
    ((Icc 1 B ×ˢ Icc 1 B ×ˢ Icc 1 B).image
      fun t : ℕ × ℕ × ℕ => t.1 ^ k + t.2.1 ^ k + t.2.2 ^ k).card ≤
      Erdos325.cardIsSumThreePowerBelow k x := by
  unfold Erdos325.cardIsSumThreePowerBelow
  rw [← Set.ncard_coe_finset]
  refine Set.ncard_le_ncard ?_ ((Set.finite_Iic x).subset fun n hn => hn.1)
  intro n hn
  obtain ⟨⟨a, b, c⟩, ht, rfl⟩ := mem_image.1 (mem_coe.1 hn)
  simp only [mem_product, mem_Icc] at ht
  obtain ⟨⟨-, ha⟩, ⟨-, hb⟩, -, hc⟩ := ht
  refine ⟨?_, a, b, c, rfl⟩
  have ha' := Nat.pow_le_pow_left ha k
  have hb' := Nat.pow_le_pow_left hb k
  have hc' := Nat.pow_le_pow_left hc k
  show a ^ k + b ^ k + c ^ k ≤ x
  omega

/-- The choice `B = ⌊x^(1/k) / 3⌋`. -/
lemma exists_B (k : ℕ) (hk : 1 ≤ k) (x : ℕ) (hx : 6 ^ k ≤ x) :
    ∃ B : ℕ, 1 ≤ B ∧ 3 * B ^ k ≤ x ∧ (x : ℝ) ^ (3 / k : ℝ) ≤ 216 * (B : ℝ) ^ 3 := by
  have hk0 : k ≠ 0 := by omega
  have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg x
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = (x : ℝ) ^ ((k : ℝ)⁻¹) := ⟨_, rfl⟩
  have hyk : y ^ k = x := by rw [hy]; exact Real.rpow_inv_natCast_pow hx0 hk0
  have hy0 : 0 ≤ y := by rw [hy]; exact Real.rpow_nonneg hx0 _
  have hy6 : 6 ≤ y := by
    have h6 : ((6 : ℝ) ^ k) ^ ((k : ℝ)⁻¹) = 6 := Real.pow_rpow_inv_natCast (by norm_num) hk0
    rw [hy, ← h6]
    exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hx) (by positivity)
  have hfl : (⌊y / 3⌋₊ : ℝ) ≤ y / 3 := Nat.floor_le (by positivity)
  have hlt : y / 3 < ⌊y / 3⌋₊ + 1 := Nat.lt_floor_add_one _
  have hB1 : 1 ≤ ⌊y / 3⌋₊ := Nat.le_floor (by push_cast; linarith)
  have hB1' : (1 : ℝ) ≤ ⌊y / 3⌋₊ := by exact_mod_cast hB1
  refine ⟨⌊y / 3⌋₊, hB1, ?_, ?_⟩
  · have h1 : (3 * (⌊y / 3⌋₊ : ℝ)) ^ k ≤ y ^ k :=
      pow_le_pow_left₀ (by positivity) (by linarith) k
    have h2 : 3 * (⌊y / 3⌋₊ : ℝ) ^ k ≤ (3 * (⌊y / 3⌋₊ : ℝ)) ^ k := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right (le_self_pow₀ (by norm_num) hk0) (by positivity)
    have h3 : 3 * (⌊y / 3⌋₊ : ℝ) ^ k ≤ x := (h2.trans h1).trans hyk.le
    exact_mod_cast h3
  · have hxy : (x : ℝ) ^ (3 / k : ℝ) = y ^ 3 := by
      rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hx0]
      congr 1
      push_cast
      ring
    rw [hxy]
    calc y ^ 3 ≤ (6 * (⌊y / 3⌋₊ : ℝ)) ^ 3 := pow_le_pow_left₀ hy0 (by linarith) 3
      _ = 216 * (⌊y / 3⌋₊ : ℝ) ^ 3 := by ring

/-- From `H2`: for `k ≥ 26` a positive proportion of `x^(3/k)` integers up to `x` are sums of
three `k`-th powers. -/
lemma large_k (h2 : H2) (k : ℕ) (hk : 26 ≤ k) :
    (fun x : ℕ => (x : ℝ) ^ (3 / k : ℝ)) =O[atTop]
      (fun x => (Erdos325.cardIsSumThreePowerBelow k x : ℝ)) := by
  obtain ⟨δ, hδ, C, hC⟩ := h2 k hk
  refine IsBigO.of_bound (216 * (max C 0 + 27)) ?_
  filter_upwards [eventually_ge_atTop (6 ^ k)] with x hx
  obtain ⟨B, hB1, hBx, hxB⟩ := exists_B k (by omega) x hx
  have h1 := cube_le_card_image k δ C hδ hC B hB1
  have h3 : (((Icc 1 B ×ˢ Icc 1 B ×ˢ Icc 1 B).image
      fun t : ℕ × ℕ × ℕ => t.1 ^ k + t.2.1 ^ k + t.2.2 ^ k).card : ℝ) ≤
      (Erdos325.cardIsSumThreePowerBelow k x : ℝ) := by
    exact_mod_cast card_image_le k B x hBx
  have hc : 0 ≤ max C 0 + 27 := add_nonneg (le_max_right _ _) (by norm_num)
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  calc (x : ℝ) ^ (3 / k : ℝ) ≤ 216 * (B : ℝ) ^ 3 := hxB
    _ ≤ 216 * ((max C 0 + 27) * (Erdos325.cardIsSumThreePowerBelow k x : ℝ)) :=
        mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_left h3 hc)) (by norm_num)
    _ = 216 * (max C 0 + 27) * (Erdos325.cardIsSumThreePowerBelow k x : ℝ) := by ring

theorem main : H1 → H2 → type_of% @Erdos325.erdos_325.variants.weaker := by
  intro h1 h2 ε hε k hk
  by_cases hk26 : k < 26
  · exact h1 ε hε k hk hk26
  · refine IsBigO.trans (IsBigO.of_bound 1 ?_) (large_k h2 k (not_lt.mp hk26))
    filter_upwards [eventually_ge_atTop 1] with x hx
    have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity), one_mul]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)

end OMA.R_Erdos325_erdos_325_variants_weaker_R1
