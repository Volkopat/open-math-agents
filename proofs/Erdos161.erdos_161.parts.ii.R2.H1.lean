import OMAReductions.R_Erdos161_erdos_161_parts_ii_R2

-- Step Erdos161.erdos_161.parts.ii.R2.H1: hypothesis H1 of reduction Erdos161.erdos_161.parts.ii.R2
-- Credit: @<handle>
-- H1 := ∀ t : ℕ, 3 ≤ t → ∀ γ : ℝ, 1 / 4 ≤ γ → γ < 1 / 2 →     (fun n : ℕ ↦ ((sInf {m : ℕ | ∃ c : Finset (Fin n) → Bool, ∀ X : Finset (Fin n), m ≤ X.card →         ∀ b : Bool, let count := ((X.powersetCard t).filter (fun e ↦ c e = b)).card         0 < count ∧ γ * (X.card.choose t : ℝ) ≤ count} : ℕ) : ℝ)) =O[atTop]     (fun n : ℕ ↦ ((sInf {m : ℕ | ∃ c : Finset (Fin n) → Bool, ∀ X : Finset (Fin n), m ≤ X.card →         ∀ b : Bool, let count := ((X.powersetCard t).filter (fun e ↦ c e = b)).card         0 < count ∧ (1 / 4 : ℝ) * (X.card.choose t : ℝ) ≤ count} : ℕ) : ℝ))

open Filter Asymptotics Finset
open scoped BigOperators Function

private def HasBalancedColoring (n t : ℕ) (α : ℝ) (m : ℕ) : Prop :=
  ∃ c : Finset (Fin n) → Bool, ∀ X : Finset (Fin n), m ≤ X.card →
    ∀ b : Bool, let count := ((X.powersetCard t).filter (fun e ↦ c e = b)).card
      0 < count ∧ α * (X.card.choose t : ℝ) ≤ (count : ℝ)

private lemma threshold_feasible (n t : ℕ) (α : ℝ) :
    HasBalancedColoring n t α (Hypergraph.balancedColoringThreshold n t α) := by
  change sInf {m | HasBalancedColoring n t α m} ∈ {m | HasBalancedColoring n t α m}
  apply Nat.sInf_mem
  refine ⟨n + 1, fun _ ↦ false, fun X hX ↦ ?_⟩
  have hcard : X.card ≤ n := by simpa using Finset.card_le_univ X
  omega

private lemma threshold_le_of_feasible {n t m : ℕ} {α : ℝ}
    (h : HasBalancedColoring n t α m) : Hypergraph.balancedColoringThreshold n t α ≤ m :=
  Nat.sInf_le (s := {k | HasBalancedColoring n t α k}) h

private noncomputable abbrev threshold (t : ℕ) (density : ℝ) (n : ℕ) : ℝ :=
  Hypergraph.balancedColoringThreshold n t density

private lemma threshold_pos_of_pos_uniformity (n d : ℕ) (α : ℝ) :
    0 < Hypergraph.balancedColoringThreshold n (d + 1) α := by
  by_contra! h
  obtain ⟨col, hcol⟩ := threshold_feasible n (d + 1) α
  have hempty : (∅ : Finset (Fin n)).powersetCard (d + 1) = ∅ :=
    powersetCard_eq_empty.mpr (by simp)
  have hpos := (hcol ∅ (by simpa using h) false).1
  simp [hempty] at hpos

private noncomputable abbrev logScale (d : ℕ) (n : ℕ) : ℝ :=
  Real.log n ^ ((d : ℝ)⁻¹)

private lemma coloring_weight_sum {E : Type*} [Fintype E] [DecidableEq E]
    (S : Finset E) (b : Bool) (u : ℝ) :
    (∑ c : E → Bool,
      Real.exp (u * ((S.card : ℝ) - 2 * ((S.filter fun e ↦ c e = b).card : ℝ))
        - u ^ 2 * S.card) / (2 : ℝ) ^ Fintype.card E) ≤
      Real.exp (-(u ^ 2 / 2) * S.card) := by
  classical
  let w (e : E) (v : Bool) : ℝ :=
    if e ∈ S then Real.exp (u * (if v = b then -1 else 1) - u ^ 2) / 2 else 1 / 2
  have hp (c : E → Bool) :
      ∏ e : E, w e (c e) =
        Real.exp (u * ((S.card : ℝ) - 2 * ((S.filter fun e ↦ c e = b).card : ℝ))
          - u ^ 2 * S.card) / (2 : ℝ) ^ Fintype.card E := by
    have hsum : (∑ e ∈ S, (if c e = b then (-1 : ℝ) else 1)) =
        (S.card : ℝ) - 2 * ((S.filter fun e ↦ c e = b).card : ℝ) := by
      calc
        _ = ∑ e ∈ S, (1 - if c e = b then (2 : ℝ) else 0) := by
          exact sum_congr rfl fun e _ ↦ by split_ifs <;> norm_num
        _ = _ := by simp [sum_sub_distrib, ← sum_filter, nsmul_eq_mul, mul_comm]
    have hw (e : E) :
        w e (c e) = Real.exp (if e ∈ S then u * (if c e = b then -1 else 1) - u ^ 2 else 0) / 2 := by
      by_cases he : e ∈ S <;> simp [w, he]
    change ∏ e : E, w e (c e) = _
    simp_rw [hw]
    rw [prod_div_distrib, ← Real.exp_sum]
    congr 1
    · congr 1
      simp only [← sum_filter, filter_mem_eq_inter, univ_inter, sum_sub_distrib, ← mul_sum,
        sum_const, nsmul_eq_mul, hsum]
      ring
    · simp
  rw [show (∑ c : E → Bool, Real.exp
      (u * ((S.card : ℝ) - 2 * ((S.filter fun e ↦ c e = b).card : ℝ))
        - u ^ 2 * S.card) / (2 : ℝ) ^ Fintype.card E) = ∑ c : E → Bool, ∏ e : E, w e (c e)
    from sum_congr rfl (fun c _ ↦ (hp c).symm), ← Fintype.prod_sum]
  have hcoord (e : E) : ∑ v : Bool, w e v ≤
      Real.exp (if e ∈ S then -(u ^ 2 / 2) else 0) := by
    rw [Fintype.sum_bool]
    by_cases he : e ∈ S
    · have hcosh := mul_le_mul_of_nonneg_left (Real.cosh_le_exp_half_sq u)
        (Real.exp_nonneg (-(u ^ 2)))
      rw [Real.cosh_eq, ← Real.exp_add] at hcosh
      have h₁ : -(u ^ 2) + u ^ 2 / 2 = -(u ^ 2 / 2) := by ring
      rw [h₁] at hcosh
      have h₂ : Real.exp (-(u ^ 2)) * ((Real.exp u + Real.exp (-u)) / 2) =
          Real.exp (u - u ^ 2) / 2 + Real.exp (-u - u ^ 2) / 2 := by
        simp only [Real.exp_sub, Real.exp_neg, div_eq_mul_inv]
        ring
      rw [h₂] at hcosh
      cases b <;> simpa [w, he, add_comm] using hcosh
    · norm_num [w, he]
  calc
    _ ≤ ∏ e : E, Real.exp (if e ∈ S then -(u ^ 2 / 2) else 0) :=
      prod_le_prod (fun e _ ↦ sum_nonneg (fun v _ ↦ by dsimp [w]; split_ifs <;> positivity))
        (fun e _ ↦ hcoord e)
    _ = _ := by
      rw [← Real.exp_sum]
      congr 1
      rw [← sum_filter]
      simp [nsmul_eq_mul, mul_comm]

private lemma coloring_of_small_weight {n t m : ℕ} {α : ℝ} (hα : 0 < α)
    (hα' : α < 1 / 2) (htm : t ≤ m)
    (hsmall : ∑ X ∈ (univ : Finset (Finset (Fin n))).filter (fun X ↦ m ≤ X.card),
      2 * Real.exp (-((1 - 2 * α) ^ 2 / 2) * (X.card.choose t : ℝ)) < 1) :
    ∃ c : Finset (Fin n) → Bool, ∀ X : Finset (Fin n), m ≤ X.card →
      ∀ b : Bool, let count := ((X.powersetCard t).filter (fun e ↦ c e = b)).card
        0 < count ∧ α * (X.card.choose t : ℝ) ≤ (count : ℝ) := by
  classical
  let E := Finset (Fin n)
  let P := (univ : Finset E).filter (fun X ↦ m ≤ X.card)
  let u := 1 - 2 * α
  let weight (c : E → Bool) (X : E) (b : Bool) : ℝ :=
    Real.exp (u * ((X.card.choose t : ℝ) -
      2 * (((X.powersetCard t).filter fun e ↦ c e = b).card : ℝ))
      - u ^ 2 * (X.card.choose t : ℝ))
  let total (c : E → Bool) := ∑ X ∈ P, ∑ b : Bool, weight c X b
  let M := (2 : ℝ) ^ Fintype.card E
  have hM : 0 < M := by dsimp [M]; positivity
  have hmean : ∑ c : E → Bool, total c / M < 1 := by
    calc
      _ = ∑ X ∈ P, ∑ b : Bool, ∑ c : E → Bool, weight c X b / M := by
        simp only [total, sum_div]
        rw [sum_comm]
        exact sum_congr rfl fun _ _ ↦ sum_comm
      _ ≤ ∑ X ∈ P, 2 * Real.exp (-(u ^ 2 / 2) * (X.card.choose t : ℝ)) := by
        apply sum_le_sum
        intro X _
        have h (b : Bool) : (∑ c : E → Bool, weight c X b / M) ≤
            Real.exp (-(u ^ 2 / 2) * (X.card.choose t : ℝ)) := by
          simpa [weight, M, E] using coloring_weight_sum (X.powersetCard t) b u
        rw [Fintype.sum_bool, two_mul]
        exact add_le_add (h true) (h false)
      _ < 1 := hsmall
  obtain ⟨c, hc⟩ : ∃ c, total c < 1 := by
    by_contra! h
    have hlower : ∑ c : E → Bool, (1 : ℝ) / M ≤ ∑ c : E → Bool, total c / M :=
      sum_le_sum fun c _ ↦ div_le_div_of_nonneg_right (h c) hM.le
    have heq : (∑ _c : E → Bool, (1 : ℝ) / M) = 1 := by
      simp [nsmul_eq_mul, M, hM.ne']
    rw [heq] at hlower
    exact hmean.not_ge hlower
  refine ⟨c, fun X hX b ↦ ?_⟩
  let count := ((X.powersetCard t).filter (fun e ↦ c e = b)).card
  have hxP : X ∈ P := mem_filter.mpr ⟨mem_univ _, hX⟩
  have hwt : weight c X b ≤ total c :=
    (single_le_sum (f := weight c X) (fun _ _ ↦ Real.exp_nonneg _) (mem_univ b)).trans
      (single_le_sum (f := fun Y ↦ ∑ v : Bool, weight c Y v)
        (fun _ _ ↦ sum_nonneg fun _ _ ↦ Real.exp_nonneg _) hxP)
  have hw : u * ((X.card.choose t : ℝ) - 2 * (count : ℝ)) -
      u ^ 2 * (X.card.choose t : ℝ) < 0 := by
    apply Real.exp_lt_exp.mp
    rw [Real.exp_zero]
    exact hwt.trans_lt hc
  have hu : 0 < u := by dsimp [u]; linarith
  have hid : u * ((X.card.choose t : ℝ) - 2 * (count : ℝ)) -
      u ^ 2 * (X.card.choose t : ℝ) =
      (2 * u) * (α * (X.card.choose t : ℝ) - (count : ℝ)) := by
    dsimp [u]
    ring
  rw [hid] at hw
  have hneg : α * (X.card.choose t : ℝ) - (count : ℝ) < 0 := by
    by_contra! h
    exact hw.not_ge (mul_nonneg (by positivity) h)
  have hp : 0 < (X.card.choose t : ℝ) := by
    exact_mod_cast Nat.choose_pos (htm.trans hX)
  exact ⟨by exact_mod_cast (mul_pos hα hp).trans (sub_neg.mp hneg), (sub_neg.mp hneg).le⟩

private lemma coloring_weight_bound {n t m : ℕ} (hn : 3 ≤ n) (hm : 2 ≤ m) {a : ℝ}
    (h : ∀ j ≥ m, 2 * (j : ℝ) * Real.log n ≤ a * (j.choose t : ℝ)) :
    (∑ X ∈ (univ : Finset (Finset (Fin n))).filter (fun X ↦ m ≤ X.card),
      2 * Real.exp (-a * (X.card.choose t : ℝ))) < 1 := by
  classical
  let P := (univ : Finset (Finset (Fin n))).filter (fun X ↦ m ≤ X.card)
  let w (j : ℕ) := 2 * Real.exp (-a * (j.choose t : ℝ))
  let N : ℝ := n
  have hN : 3 ≤ N := by dsimp [N]; exact_mod_cast hn
  have hNp : 0 < N := by linarith
  have hmap : ∀ X ∈ P, X.card ∈ range (n + 1) := by
    intro X _
    have hX : X.card ≤ n := by simpa using card_le_univ X
    simpa using Nat.lt_succ_of_le hX
  change (∑ X ∈ P, w X.card) < 1
  rw [← sum_fiberwise_of_maps_to' hmap w]
  calc
    _ ≤ ∑ _j ∈ range (n + 1), (2 / N ^ 2 : ℝ) := by
      apply sum_le_sum
      intro j _
      by_cases hj : m ≤ j
      · have hfilter : P.filter (fun X ↦ X.card = j) = (univ : Finset (Fin n)).powersetCard j := by
          ext X
          simp only [P, mem_filter, mem_univ, true_and, mem_powersetCard, subset_univ]
          exact ⟨And.right, fun hx ↦ ⟨hx ▸ hj, hx⟩⟩
        rw [hfilter, sum_const, nsmul_eq_mul, card_powersetCard, card_univ, Fintype.card_fin]
        have hchoose' : (n.choose j : ℝ) ≤ N ^ j := by dsimp [N]; exact_mod_cast Nat.choose_le_pow n j
        have hw : w j ≤ 2 / (N ^ j * N ^ j) := by
          dsimp [w]
          rw [div_eq_mul_inv, ← Real.exp_log (show 0 < N ^ j * N ^ j by positivity),
            ← Real.exp_neg, Real.log_mul (by positivity) (by positivity), Real.log_pow]
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply Real.exp_le_exp.mpr
          have hj' := h j hj
          change 2 * (j : ℝ) * Real.log N ≤ _ at hj'
          linarith
        have hjN : N ^ 2 ≤ N ^ j := pow_le_pow_right₀ (by linarith) (hm.trans hj)
        calc
          _ ≤ N ^ j * (2 / (N ^ j * N ^ j)) :=
            mul_le_mul hchoose' hw (by dsimp [w]; positivity) (by positivity)
          _ = 2 / N ^ j := by field_simp
          _ ≤ 2 / N ^ 2 := div_le_div_of_nonneg_left (by norm_num) (by positivity) hjN
      · have hfilter : P.filter (fun X ↦ X.card = j) = ∅ := by
          apply eq_empty_iff_forall_notMem.mpr
          intro X hX
          obtain ⟨hP, he⟩ := mem_filter.mp hX
          exact hj (he ▸ (mem_filter.mp hP).2)
        rw [hfilter, sum_empty]
        positivity
    _ < 1 := by
      simp only [sum_const, card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      change (N + 1) * (2 / N ^ 2) < 1
      rw [← mul_div_assoc, div_lt_one (by positivity)]
      nlinarith

/-- The random-coloring upper bound at the logarithmic scale. -/
private lemma threshold_bigO_logScale (d : ℕ) (hd : 0 < d) {α : ℝ}
    (hα : 0 < α) (hα' : α < 1 / 2) :
    threshold (d + 1) α =O[atTop] logScale d := by
  let t := d + 1
  let a : ℝ := (1 - 2 * α) ^ 2 / 2
  let A : ℝ := 2 ^ t * t.factorial
  let C : ℝ := (2 * A / a) ^ ((d : ℝ)⁻¹)
  have ha : 0 < a := by
    have hu : 0 < 1 - 2 * α := by linarith
    dsimp [a]
    positivity
  have hA : 0 < A := by
    have hfac : 0 < (t.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos t
    dsimp [A]
    positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hpow (z : ℝ) (hz : 0 ≤ z) : (z ^ ((d : ℝ)⁻¹)) ^ d = z := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hz,
      inv_mul_cancel₀ (by exact_mod_cast hd.ne'), Real.rpow_one]
  have hchoose (j : ℕ) (hj : 2 * t ≤ j) : (j : ℝ) ^ t / A ≤ (j.choose t : ℝ) := by
    have hhalf : (j : ℝ) / 2 ≤ ((j + 1 - t : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
      have h' : (2 : ℝ) * t ≤ j := by exact_mod_cast hj
      linarith
    calc
      _ = ((j : ℝ) / 2) ^ t / (t.factorial : ℝ) := by rw [div_pow, div_div]
      _ ≤ ((j + 1 - t : ℕ) : ℝ) ^ t / (t.factorial : ℝ) :=
        div_le_div_of_nonneg_right (pow_le_pow_left₀ (by positivity) hhalf _) (by positivity)
      _ ≤ _ := Nat.pow_le_choose t j
  have htend : Tendsto (logScale d) atTop atTop :=
    (tendsto_rpow_atTop (inv_pos.mpr (by exact_mod_cast hd))).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  apply IsBigO.of_bound ((2 * t : ℕ) + C + 1)
  filter_upwards [eventually_ge_atTop 3, htend.eventually (eventually_ge_atTop 1)] with n hn hL
  let L := logScale d n
  change 1 ≤ L at hL
  have hL0 : 0 ≤ L := by linarith
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hLpower : L ^ d = Real.log n := hpow _ hlog
  let m := max (2 * t) ⌈C * L⌉₊
  have hm : 2 * t ≤ m := le_max_left _ _
  have hmceil : ⌈C * L⌉₊ ≤ m := le_max_right _ _
  have htm : t ≤ m := by omega
  have hm2 : 2 ≤ m := by dsimp [t] at hm; omega
  have hweight (j : ℕ) (hj : m ≤ j) :
      2 * (j : ℝ) * Real.log n ≤ a * (j.choose t : ℝ) := by
    have hCL : C * L ≤ (j : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hmceil.trans hj)
    have hjpow := pow_le_pow_left₀ (mul_nonneg hC.le hL0) hCL d
    rw [mul_pow, show C ^ d = 2 * A / a from hpow _ (by positivity), hLpower] at hjpow
    have hmid : 2 * Real.log n ≤ a * ((j : ℝ) ^ d / A) := by
      rw [← mul_div_assoc]
      apply (le_div_iff₀ hA).mpr
      have hh : 2 * A * Real.log (n : ℝ) ≤ (j : ℝ) ^ d * a :=
        (div_le_iff₀ ha).mp (by simpa only [div_mul_eq_mul_div] using hjpow)
      nlinarith only [hh]
    calc
      _ = (j : ℝ) * (2 * Real.log n) := by ring
      _ ≤ (j : ℝ) * (a * ((j : ℝ) ^ d / A)) := mul_le_mul_of_nonneg_left hmid (by positivity)
      _ = a * ((j : ℝ) ^ t / A) := by dsimp [t]; rw [pow_succ]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hchoose j (hm.trans hj)) ha.le
  have hmle : Hypergraph.balancedColoringThreshold n t α ≤ m :=
    threshold_le_of_feasible (coloring_of_small_weight hα hα' htm (coloring_weight_bound hn hm2 hweight))
  have hceil : (⌈C * L⌉₊ : ℝ) ≤ C * L + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  have hmR : (m : ℝ) ≤ ((2 * t : ℕ) : ℝ) + (C * L + 1) := by
    rw [show (m : ℝ) = max (((2 * t : ℕ) : ℝ)) (⌈C * L⌉₊ : ℝ) by exact_mod_cast rfl]
    exact max_le (le_add_of_nonneg_right (by positivity))
      (hceil.trans (le_add_of_nonneg_left (by positivity)))
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg hL0]
  change (Hypergraph.balancedColoringThreshold n t α : ℝ) ≤
    (((2 * t : ℕ) : ℝ) + C + 1) * L
  calc
    _ ≤ (m : ℝ) := by exact_mod_cast hmle
    _ ≤ _ := hmR.trans (by
      have hbase : (0 : ℝ) ≤ ((2 * t : ℕ) : ℝ) := by positivity
      nlinarith only [mul_nonneg hbase (sub_nonneg.mpr hL), hL])

private lemma card_edges_containing_pair_le {n t : ℕ} (X : Finset (Fin n)) {x y : Fin n}
    (hxy : x ≠ y) :
    ((X.powersetCard t).filter (fun e ↦ x ∈ e ∧ y ∈ e)).card ≤ X.card ^ (t - 2) := by
  classical
  let f (e : Finset (Fin n)) := (e.erase x).erase y
  have hle : ((X.powersetCard t).filter (fun e ↦ x ∈ e ∧ y ∈ e)).card ≤
      (X.powersetCard (t - 2)).card := by
    apply card_le_card_of_injOn f
    · intro e he
      obtain ⟨hE, hx, hy⟩ := mem_filter.mp he
      obtain ⟨hsub, hc⟩ := mem_powersetCard.mp hE
      have hy' : y ∈ e.erase x := mem_erase.mpr ⟨hxy.symm, hy⟩
      exact mem_powersetCard.mpr ⟨erase_subset _ _ |>.trans (erase_subset _ _ |>.trans hsub), by
        simp only [f, card_erase_of_mem hy', card_erase_of_mem hx, hc]
        omega⟩
    · intro e he e' he' hf
      have rebuild {a : Finset (Fin n)}
          (ha : a ∈ (X.powersetCard t).filter (fun e ↦ x ∈ e ∧ y ∈ e)) :
          insert x (insert y (f a)) = a := by
        obtain ⟨_, hx, hy⟩ := mem_filter.mp ha
        have hy' : y ∈ a.erase x := mem_erase.mpr ⟨hxy.symm, hy⟩
        dsimp [f]
        rw [insert_erase hy', insert_erase hx]
      rw [← rebuild he, ← rebuild he', hf]
  exact hle.trans (by rw [card_powersetCard]; exact Nat.choose_le_pow _ _)

/-- A crossing-monochromatic multipartite subhypergraph has few edges of the other color. -/
private lemma threshold_gt_of_multipartite {n t q s : ℕ} {α : ℝ}
    (ht : 2 ≤ t) (hs : 0 < s) (hq : 2 * t ≤ q)
    (hαq : (2 : ℝ) ^ t * t.factorial < α * q)
    (hbox : ∀ col : Finset (Fin n) → Bool, ∃ (P : Fin q → Finset (Fin n)) (b : Bool),
      Pairwise (Disjoint on P) ∧ (∀ i, (P i).card = s) ∧
      ∀ e ∈ (univ.biUnion P).powersetCard t,
        (∀ i x y, x ∈ e → y ∈ e → x ∈ P i → y ∈ P i → x = y) → col e = b) :
    q * s < Hypergraph.balancedColoringThreshold n t α := by
  classical
  by_contra! h
  obtain ⟨col, hcol⟩ := threshold_feasible n t α
  obtain ⟨P, b, hdisj, hsize, hmono⟩ := hbox col
  let X := univ.biUnion P
  let bad := (X.powersetCard t).filter (fun e ↦ col e = !b)
  have hX : X.card = q * s := by
    dsimp [X]
    rw [card_biUnion (fun _ _ _ _ hij ↦ hdisj hij)]
    simp [hsize]
  let collision (p : Fin n × Fin n) :=
    (X.powersetCard t).filter (fun e ↦ p.1 ∈ e ∧ p.2 ∈ e)
  let clashes (i : Fin q) := ((P i ×ˢ P i).filter (fun p ↦ p.1 ≠ p.2)).biUnion collision
  have hbad : bad ⊆ univ.biUnion clashes := by
    intro e he
    obtain ⟨he', hc⟩ := mem_filter.mp he
    have hnmon : col e ≠ b := by rw [hc]; cases b <;> decide
    have hh : ¬ (∀ i x y, x ∈ e → y ∈ e → x ∈ P i → y ∈ P i → x = y) :=
      fun h ↦ hnmon (hmono e he' h)
    push Not at hh
    obtain ⟨i, x, y, hx, hy, hxi, hyi, hxy⟩ := hh
    exact mem_biUnion.mpr ⟨i, mem_univ _, mem_biUnion.mpr ⟨(x, y),
      mem_filter.mpr ⟨mem_product.mpr ⟨hxi, hyi⟩, hxy⟩, mem_filter.mpr ⟨he', hx, hy⟩⟩⟩
  have hclash (i : Fin q) : (clashes i).card ≤ s ^ 2 * X.card ^ (t - 2) := by
    calc
      _ ≤ ∑ p ∈ (P i ×ˢ P i).filter (fun p ↦ p.1 ≠ p.2), (collision p).card := card_biUnion_le
      _ ≤ ∑ _p ∈ (P i ×ˢ P i).filter (fun p ↦ p.1 ≠ p.2), X.card ^ (t - 2) :=
        sum_le_sum fun p hp ↦ card_edges_containing_pair_le X (mem_filter.mp hp).2
      _ ≤ s ^ 2 * X.card ^ (t - 2) := by
        rw [sum_const, smul_eq_mul, pow_two]
        apply Nat.mul_le_mul_right
        simpa [card_product, hsize] using
          (card_filter_le (s := P i ×ˢ P i) (p := fun p ↦ p.1 ≠ p.2))
  have hcount : bad.card ≤ q * s ^ 2 * X.card ^ (t - 2) := by
    calc
      _ ≤ ∑ i : Fin q, (clashes i).card := (card_le_card hbad).trans card_biUnion_le
      _ ≤ ∑ _i : Fin q, s ^ 2 * X.card ^ (t - 2) := sum_le_sum fun i _ ↦ hclash i
      _ = _ := by simp [smul_eq_mul, mul_assoc]
  let A : ℝ := 2 ^ t * t.factorial
  let v : ℝ := X.card
  have hv : v = (q : ℝ) * s := by dsimp [v]; exact_mod_cast hX
  have hql : 0 < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hvpos : 0 < v := by rw [hv]; exact mul_pos hql (by exact_mod_cast hs)
  have hA : 0 < A := by
    have : 0 < (t.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos t
    dsimp [A]
    positivity
  have hsmall : (bad.card : ℝ) < α * (X.card.choose t : ℝ) := by
    have hcount' : (bad.card : ℝ) ≤ (q : ℝ) * (s : ℝ) ^ 2 * v ^ (t - 2) := by
      dsimp [v]
      exact_mod_cast hcount
    have hhalf : v / 2 ≤ ((X.card + 1 - t : ℕ) : ℝ) := by
      have hj : 2 * t ≤ X.card := by
        rw [hX]
        exact hq.trans (Nat.le_mul_of_pos_right _ hs)
      have hj' : (2 : ℝ) * t ≤ X.card := by exact_mod_cast hj
      dsimp [v]
      rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
      linarith
    have hα : 0 < α := by
      by_contra! hα
      exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg hα hql.le)) (hA.trans hαq)
    have hratio : 1 / (q : ℝ) < α / A := by
      rw [div_lt_div_iff₀ hql hA, one_mul]
      exact hαq
    calc
      _ ≤ (q : ℝ) * (s : ℝ) ^ 2 * v ^ (t - 2) := hcount'
      _ = (1 / (q : ℝ)) * v ^ t := by
        conv_rhs => rw [show t = (t - 2) + 2 by omega, pow_add]
        rw [show v ^ 2 = ((q : ℝ) * s) ^ 2 by rw [hv]]
        field_simp
      _ < (α / A) * v ^ t := mul_lt_mul_of_pos_right hratio (by positivity)
      _ = α * ((v / 2) ^ t / (t.factorial : ℝ)) := by rw [div_pow, div_div]; dsimp [A]; ring
      _ ≤ α * (X.card.choose t : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ hα.le
        refine (div_le_div_of_nonneg_right (pow_le_pow_left₀ (by positivity) hhalf _) (by positivity)).trans ?_
        exact Nat.pow_le_choose t X.card
  rw [← hX] at h
  exact hsmall.not_ge (hcol X h (!b)).2

private lemma exists_half_color {A : Type*} (T : Finset A) (f : A → Bool) :
    ∃ b, T.card ≤ 2 * (T.filter (fun x ↦ f x = b)).card := by
  classical
  have hf : T.filter (fun x ↦ f x = false) = T.filter (fun x ↦ ¬ f x = true) := by
    ext x
    simp
  have h := card_filter_add_card_filter_not (s := T) (fun x ↦ f x = true)
  rw [← hf] at h
  by_cases hb : T.card ≤ 2 * (T.filter (fun x ↦ f x = true)).card
  · exact ⟨true, hb⟩
  · exact ⟨false, by omega⟩

/-- Stabilize the color of triples using one old part and two reservoir vertices. -/
private lemma logScale_bigO_threshold_of_finite (d : ℕ) (hd : 0 < d) (ρ : ℝ) (C : ℕ)
    (h : ∀ n s : ℕ, 0 < s → 2 ^ (C * (s + 1) ^ d) ≤ n →
      s < Hypergraph.balancedColoringThreshold n (d + 1) ρ) :
    logScale d =O[atTop] threshold (d + 1) ρ := by
  let K : ℝ := (C : ℝ) * 2 ^ d * Real.log 2
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  apply IsBigO.of_bound (K ^ ((d : ℝ)⁻¹))
  filter_upwards [eventually_ge_atTop 1] with n hn
  let m := Hypergraph.balancedColoringThreshold n (d + 1) ρ
  have hm := threshold_pos_of_pos_uniformity n d ρ
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hN : n < 2 ^ (C * (m + 1) ^ d) := lt_of_not_ge fun hh ↦ (lt_irrefl m) (h n m hm hh)
  have hN' : (n : ℝ) ≤ (2 : ℝ) ^ (C * (m + 1) ^ d) := by exact_mod_cast hN.le
  have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hlog : Real.log n ≤ K * (m : ℝ) ^ d := by
    calc
      _ ≤ Real.log ((2 : ℝ) ^ (C * (m + 1) ^ d)) :=
        Real.log_le_log (by exact_mod_cast (show 0 < n by omega)) hN'
      _ = (C : ℝ) * ((m : ℝ) + 1) ^ d * Real.log 2 := by rw [Real.log_pow]; push_cast; ring
      _ ≤ (C : ℝ) * (2 * (m : ℝ)) ^ d * Real.log 2 := by
        gcongr
        linarith
      _ = _ := by dsimp [K]; rw [mul_pow]; ring
  have hroot := Real.rpow_le_rpow hlog0 hlog (inv_nonneg.mpr (Nat.cast_nonneg d))
  have hpow : ((m : ℝ) ^ d) ^ ((d : ℝ)⁻¹) = m := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg m),
      mul_inv_cancel₀ (by exact_mod_cast hd.ne'), Real.rpow_one]
  rw [Real.mul_rpow hK (by positivity), hpow] at hroot
  simpa only [logScale, Real.norm_of_nonneg (Real.rpow_nonneg hlog0 _), threshold,
    Real.norm_of_nonneg (Nat.cast_nonneg _)] using hroot

-- The lower bound follows from Mubayi's coordinate repetition inequality
-- (Large blow-ups of uniform hypergraphs, arXiv:2611.33108).
section Blowup

open scoped Classical
open Finset

private lemma uniform_holder {s : ℕ} (hs : 0 < s) {A : Type*} [Fintype A]
    (f : Fin s → A → ℝ) (hf : ∀ i a, 0 ≤ f i a) :
    (∑ a, ∏ i, f i a) ^ s ≤ ∏ i, ∑ a, f i a ^ s := by
  let z (i : Fin s) := ∑ a, f i a ^ s
  have hz (i : Fin s) : 0 ≤ z i := sum_nonneg fun a _ => pow_nonneg (hf i a) _
  by_cases h : ∃ i, z i = 0
  · obtain ⟨i, hi⟩ := h
    have hzero (a : A) : f i a = 0 := by
      have hterm : f i a ^ s ≤ z i := single_le_sum
        (fun b _ => pow_nonneg (hf i b) _) (mem_univ a)
      have hp : f i a ^ s = 0 := le_antisymm (hi ▸ hterm) (pow_nonneg (hf i a) _)
      exact (pow_eq_zero_iff hs.ne').mp hp
    have hprod (a : A) : ∏ j, f j a = 0 := prod_eq_zero (mem_univ i) (hzero a)
    simp only [hprod, sum_const_zero, zero_pow hs.ne']
    exact prod_nonneg fun i _ => hz i
  · have hpos (i : Fin s) : 0 < z i := lt_of_le_of_ne (hz i) (fun he => h ⟨i, he.symm⟩)
    let g (i : Fin s) (a : A) := f i a ^ s / z i
    have hg (i : Fin s) (a : A) : 0 ≤ g i a := div_nonneg (pow_nonneg (hf i a) _) (hz i)
    have hg1 (i : Fin s) : ∑ a, g i a = 1 := by
      simp only [g, ← sum_div]
      exact div_self (hpos i).ne'
    have hs' : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
    have hweight : ∑ _i : Fin s, (s : ℝ)⁻¹ = 1 := by simp [nsmul_eq_mul, hs']
    have hgm (a : A) : (∏ i, (g i a) ^ (s : ℝ)⁻¹) ≤ ∑ i, (s : ℝ)⁻¹ * g i a :=
      Real.geom_mean_le_arith_mean_weighted univ (fun _ => (s : ℝ)⁻¹) (fun i => g i a)
        (fun _ _ => by positivity) hweight (fun i _ => hg i a)
    have hsum : (∑ a, ∏ i : Fin s, (g i a) ^ (s : ℝ)⁻¹) ≤ 1 := by
      refine (sum_le_sum fun a _ => hgm a).trans_eq ?_
      rw [sum_comm]
      simp only [← mul_sum, hg1, mul_one, hweight]
    have heq (i : Fin s) (a : A) : f i a = (g i a) ^ (s : ℝ)⁻¹ * (z i) ^ (s : ℝ)⁻¹ := by
      rw [← Real.mul_rpow (hg i a) (hz i), show g i a * z i = f i a ^ s by
        exact div_mul_cancel₀ _ (hpos i).ne', ← Real.rpow_natCast,
        ← Real.rpow_mul (hf i a), mul_inv_cancel₀ hs', Real.rpow_one]
    have hrel : (∑ a, ∏ i, f i a) ≤ ∏ i : Fin s, z i ^ (s : ℝ)⁻¹ := by
      simp_rw [heq, prod_mul_distrib, ← sum_mul]
      exact mul_le_of_le_one_left (prod_nonneg fun i _ => Real.rpow_nonneg (hz i) _) hsum
    calc
      _ ≤ (∏ i : Fin s, z i ^ (s : ℝ)⁻¹) ^ s :=
        pow_le_pow_left₀ (sum_nonneg fun a _ => prod_nonneg fun i _ => hf i a) hrel _
      _ = _ := by
        rw [← prod_pow]
        apply prod_congr rfl
        intro i _
        rw [← Real.rpow_natCast, ← Real.rpow_mul (hz i), inv_mul_cancel₀ hs', Real.rpow_one]

private abbrev Positions (d s : ℕ) := Fin d → Fin s

private abbrev Samples (d s n : ℕ) := Fin d → Fin s → Fin n

private noncomputable def countPattern {d s n : ℕ} (P : (Fin d → Fin n) → Prop)
    (J : Finset (Positions d s)) : ℕ :=
  (univ.filter fun x : Samples d s n => ∀ a ∈ J, P (fun i => x i (a i))).card

private lemma le_countPattern {d s n : ℕ} (P : (Fin d → Fin n) → Prop)
    (J : Finset (Positions d s)) (C : Finset (Samples d s n))
    (h : ∀ x ∈ C, ∀ a ∈ J, P (fun i => x i (a i))) :
    C.card ≤ countPattern P J := by
  unfold countPattern
  exact card_le_card fun x hx => mem_filter.mpr ⟨mem_univ _, h x hx⟩

private lemma countPattern_le_card {d s n : ℕ} (P : (Fin d → Fin n) → Prop)
    (J : Finset (Positions d s)) : countPattern P J ≤ Fintype.card (Samples d s n) := by
  unfold countPattern
  exact card_le_univ _

private noncomputable def repeatPosition {d s : ℕ} (i : Fin d) (u : Fin s) (J : Finset (Positions d s)) :
    Finset (Positions d s) := univ.filter (fun a => Function.update a i u ∈ J)

set_option maxHeartbeats 1000000 in
private lemma countPattern_repeat {d s n : ℕ} (hs : 0 < s) (P : (Fin d → Fin n) → Prop)
    (J : Finset (Positions d s)) (i : Fin d) :
    (countPattern P J : ℝ) ^ s ≤ ∏ u, (countPattern P (repeatPosition i u J) : ℝ) := by
  let R := {j : Fin d // j ≠ i} → Fin s → Fin n
  let B (y : R) (u : Fin s) (v : Fin n) : Prop :=
    ∀ a ∈ J, a i = u → P (fun j => if h : j = i then v else y ⟨j, h⟩ (a j))
  let f (u : Fin s) (y : R) := (@Finset.filter _ (B y u) (fun v => Classical.propDecidable (B y u v)) univ).card
  have splitCount (K : Finset (Positions d s)) (Q : R → Fin s → Fin n → Prop)
      (hQ : ∀ (x : Samples d s n),
        (∀ a ∈ K, P (fun j => x j (a j))) ↔ ∀ u, Q (fun j => x j) u (x i u)) :
      countPattern P K = ∑ y : R, ∏ u, (univ.filter (Q y u)).card := by
    let e := Equiv.funSplitAt i (Fin s → Fin n)
    let G (y : R) := Fintype.piFinset (fun u => univ.filter (Q y u))
    have hmem (x : Samples d s n) :
        x ∈ univ.filter (fun x => ∀ a ∈ K, P (fun j => x j (a j))) ↔ (e x).1 ∈ G (e x).2 := by
      simp [e, G, Fintype.mem_piFinset, hQ]
    rw [countPattern, card_filter]
    calc
      _ = ∑ p : (Fin s → Fin n) × R, if p.1 ∈ G p.2 then 1 else 0 :=
        Fintype.sum_equiv e _ _ (fun x => by
          simp only [show (∀ a ∈ K, P (fun j => x j (a j))) ↔ (e x).1 ∈ G (e x).2 by
            simpa only [mem_filter, mem_univ, true_and] using hmem x])
      _ = _ := by
        rw [Fintype.sum_prod_type_right]
        apply sum_congr rfl
        intro y _
        rw [← card_filter]
        rw [show univ.filter (fun x => x ∈ G y) = G y by ext x; simp]
        exact Fintype.card_piFinset _
  have eqn (x : Samples d s n) (a : Positions d s) (u : Fin s) (hu : a i = u) :
      (fun j => x j (a j)) = (fun j => if h : j = i then x i u else x j (a j)) := by
    funext j
    split
    · subst j
      rw [hu]
    · rfl
  have hJ : countPattern P J = ∑ y : R, ∏ u, f u y := by
    exact splitCount J B (fun x => by
      constructor
      · intro hx u a ha hu
        rw [← eqn x a u hu]
        exact hx a ha
      · intro hx a ha
        rw [eqn x a (a i) rfl]
        exact hx (a i) a ha rfl)
  have hR (u : Fin s) : countPattern P (repeatPosition i u J) = ∑ y : R, f u y ^ s := by
    rw [splitCount _ (fun y _ v => B y u v)]
    · simp only [prod_const, card_univ, Fintype.card_fin]
      rfl
    · intro x
      constructor
      · intro hx k a ha _
        let a' := Function.update a i k
        have hfit : Function.update a' i u = a := by
          funext j
          by_cases hj : j = i <;> simp_all [a', Function.update_of_ne]
        have ha' : a' ∈ repeatPosition i u J := by simp [repeatPosition, hfit, ha]
        convert hx a' ha' using 2
        rename_i j
        by_cases hj : j = i <;> simp [hj, a', Function.update_of_ne]
      · intro hx a ha
        have hj : Function.update a i u ∈ J := (mem_filter.mp ha).2
        have huv := hx (a i) _ hj (Function.update_self _ _ _)
        convert huv using 2
        rename_i j
        by_cases hj' : j = i <;> simp [hj', Function.update_of_ne]
  simp_rw [hJ, hR, Nat.cast_sum, Nat.cast_prod, Nat.cast_pow]
  exact uniform_holder hs (fun u y => f u y) (fun _ _ => Nat.cast_nonneg _)


private noncomputable def freezeRows {d s k : ℕ} (rows : Fin k → Fin d)
    (b : Fin k → Fin s) (J : Finset (Positions d s)) : Finset (Positions d s) :=
  match k with
  | 0 => J
  | k + 1 => freezeRows (Fin.tail rows) (Fin.tail b) (repeatPosition (rows 0) (b 0) J)

private lemma freezeRows_mem {d s k : ℕ} (rows : Fin k → Fin d) (b : Fin k → Fin s)
    (hr : Function.Injective rows) (J : Finset (Positions d s)) (a : Positions d s) :
    a ∈ freezeRows rows b J ↔
      ∃ z ∈ J, (∀ j, z (rows j) = b j) ∧
        (∀ i, (∀ j, rows j ≠ i) → z i = a i) := by
  induction k generalizing J with
  | zero =>
    simp only [freezeRows]
    exact ⟨fun ha => ⟨a, ha, fun j => j.elim0, fun _ _ => rfl⟩,
      fun ⟨z, hz, _, h⟩ => (funext fun i => h i (fun j => j.elim0)) ▸ hz⟩
  | succ k ih =>
    rw [freezeRows, ih (Fin.tail rows) (Fin.tail b)
      (hr.comp (Fin.succ_injective _))]
    simp only [repeatPosition, mem_filter, mem_univ, true_and, Fin.tail]
    constructor
    · rintro ⟨v, hv, htail, hout⟩
      refine ⟨Function.update v (rows 0) (b 0), hv, ?_, ?_⟩
      · refine Fin.cases (by simp) (fun j => ?_)
        have hj : rows j.succ ≠ rows 0 := fun h => Fin.succ_ne_zero _ (hr h)
        simpa [Function.update_of_ne hj] using htail j
      · intro i hi
        rw [Function.update_of_ne (Ne.symm (hi 0))]
        exact hout i (fun j => hi j.succ)
    · rintro ⟨z, hz, hrow, hout⟩
      refine ⟨Function.update z (rows 0) (a (rows 0)), ?_, ?_, ?_⟩
      · convert hz using 1
        funext i
        by_cases hi : i = rows 0
        · subst i
          simpa using (hrow 0).symm
        · simp [Function.update_of_ne hi]
      · intro j
        have hj : rows j.succ ≠ rows 0 := fun h => Fin.succ_ne_zero _ (hr h)
        simpa [Function.update_of_ne hj] using hrow j.succ
      · intro i hi
        by_cases h : i = rows 0
        · simp [h]
        · rw [Function.update_of_ne h]
          exact hout i (Fin.cases (Ne.symm h) hi)

private lemma countPattern_freeze {d s n : ℕ} (hs : 0 < s) (P : (Fin d → Fin n) → Prop)
    (J : Finset (Positions d s)) (k : ℕ) (rows : Fin k → Fin d) :
    (countPattern P J : ℝ) ^ (s ^ k) ≤ ∏ b, (countPattern P (freezeRows rows b J) : ℝ) := by
  induction k generalizing J with
  | zero => simp [freezeRows]
  | succ k ih =>
    rw [pow_succ', pow_mul]
    refine (pow_le_pow_left₀ (by positivity) (countPattern_repeat hs P J (rows 0)) _).trans ?_
    rw [← prod_pow]
    refine (prod_le_prod (fun _ _ => by positivity)
      (fun b _ => ih (repeatPosition (rows 0) b J) (Fin.tail rows))).trans_eq ?_
    rw [← Fintype.prod_prod_type']
    exact (Fin.consEquiv (fun _ : Fin (k + 1) => Fin s)).prod_comp
      (fun b => (countPattern P (freezeRows rows b J) : ℝ))

private noncomputable def densityPattern {d s n : ℕ} (P : (Fin d → Fin n) → Prop)
    (J : Finset (Positions d s)) : ℝ :=
  (countPattern P J : ℝ) / Fintype.card (Samples d s n)

private lemma densityPattern_le_full {d s n : ℕ} (hs : 0 < s) (hn : 0 < n)
    (P : (Fin d → Fin n) → Prop) (J : Finset (Positions d s)) :
    densityPattern P J ≤ (densityPattern P (univ : Finset (Positions d s))) ^
      ((J.card : ℝ) / (s : ℝ) ^ d) := by
  let M : ℝ := Fintype.card (Samples d s n)
  have hm : 0 < M := by
    dsimp [M, Samples]
    simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    positivity
  let A : ℕ := s ^ d
  have ha : (0 : ℝ) < A := by exact_mod_cast pow_pos hs d
  have hprod := countPattern_freeze hs P J d id
  have hfull (b : Positions d s) :
      freezeRows id b J = if b ∈ J then univ else ∅ := by
    ext a
    simp only [freezeRows_mem id b Function.injective_id, id_eq, ne_eq]
    by_cases hb : b ∈ J
    · simp [hb]
      exact ⟨b, hb, fun _ => rfl⟩
    · simp only [hb, if_false, notMem_empty, iff_false]
      rintro ⟨z, hz, heq, _⟩
      exact hb (funext heq ▸ hz)
  have hemp : countPattern P (∅ : Finset (Positions d s)) = Fintype.card (Samples d s n) := by
    simp [countPattern]
  simp_rw [hfull] at hprod
  have hrhs : (∏ b : Positions d s, (countPattern (s := s) P (if b ∈ J then univ else ∅) : ℝ)) =
      (countPattern (s := s) P univ : ℝ)^J.card * M^(A - J.card) := by
    simp only [apply_ite, hemp]
    have hpos : univ.filter (fun b => b ∈ J) = J := by ext x; simp
    have hneg : (univ.filter (fun b => b ∉ J)).card = A - J.card := by
      have h := card_sdiff_of_subset (subset_univ J)
      rw [show (univ.filter (fun b => b ∉ J)) = univ \ J by ext x; simp]
      simpa [A, Positions, Fintype.card_fun] using h
    rw [← prod_filter_mul_prod_filter_not univ (fun b => b ∈ J)
      (fun b => if b ∈ J then (countPattern (s := s) P univ : ℝ) else M)]
    rw [show (∏ b ∈ univ.filter (fun b => b ∈ J), if b ∈ J then (countPattern (s := s) P univ : ℝ)
        else (Fintype.card (Samples d s n) : ℝ)) = (countPattern (s := s) P univ : ℝ)^J.card by
      rw [hpos, ← prod_const]
      exact prod_congr rfl (fun b hb => if_pos hb)]
    congr 1
    rw [← hneg, ← prod_const]
    exact prod_congr rfl (fun b hb => if_neg (mem_filter.mp hb).2)
  rw [hrhs] at hprod
  have hcard : J.card ≤ A := by
    simpa [A, Positions, Fintype.card_fun] using card_le_univ J
  have hnorm : densityPattern P J ^ A ≤ densityPattern (s := s) P univ ^ J.card := by
    simp only [densityPattern, div_pow]
    apply (div_le_iff₀ (pow_pos hm _)).2
    rw [show M ^ A = M ^ (A-J.card) * M ^ J.card by
      rw [← pow_add, Nat.sub_add_cancel hcard]]
    rw [show (countPattern (s := s) P univ : ℝ)^J.card / M^J.card *
        (M^(A - J.card) * M^J.card) = (countPattern (s := s) P univ : ℝ)^J.card * M^(A - J.card) by
      field_simp]
    exact hprod
  have hb : 0 ≤ densityPattern P (univ : Finset (Positions d s)) := by
    unfold densityPattern
    positivity
  have hj : 0 ≤ densityPattern P J := by unfold densityPattern; positivity
  apply (Real.rpow_le_rpow_iff hj (Real.rpow_nonneg hb _) ha).mp
  rw [Real.rpow_natCast, ← Real.rpow_mul hb, ← Nat.cast_pow,
    show s ^ d = A from rfl, div_mul_cancel₀ _ ha.ne', Real.rpow_natCast]
  exact hnorm


private noncomputable def colorFiber {A B : Type*} [Fintype A] (f : A → B) (b : B) : Finset A :=
  univ.filter (fun a => f a = b)

private lemma mem_colorFiber {A B : Type*} [Fintype A] {f : A → B} {b : B} {a : A} :
    a ∈ colorFiber f b ↔ f a = b := by simp [colorFiber]

private lemma large_fiber {A B : Type*} [Fintype A] [Fintype B] [Nonempty B]
    (f : A → B) : ∃ b, Fintype.card A ≤ Fintype.card B * (colorFiber f b).card := by
  obtain ⟨b, _, hb⟩ := exists_max_image (univ : Finset B)
    (fun b => (colorFiber f b).card) univ_nonempty
  refine ⟨b, ?_⟩
  rw [show Fintype.card A = ∑ b : B, (colorFiber f b).card by
    unfold colorFiber
    exact card_eq_sum_card_fiberwise (fun _ _ => mem_univ _)]
  calc
    _ ≤ ∑ _ : B, (colorFiber f b).card := sum_le_sum hb
    _ = _ := by simp [nsmul_eq_mul]

private lemma finite_ramsey (t : ℕ) : ∀ q : ℕ, ∃ R : ℕ, ∀ (A : Type) [LinearOrder A]
    (X : Finset A), R ≤ X.card → ∀ c : Finset A → Bool,
    ∃ Q ⊆ X, Q.card = q ∧ ∃ b, ∀ e ∈ Q.powersetCard t, c e = b := by
  induction t with
  | zero =>
    intro q
    refine ⟨q, fun A _ X hX c => ?_⟩
    obtain ⟨Q, hQ, hcard⟩ := exists_subset_card_eq hX
    exact ⟨Q, hQ, hcard, c ∅, fun e he => by simp_all⟩
  | succ t ih =>
    have aux (k : ℕ) : ∃ R : ℕ, ∀ (A : Type) [LinearOrder A] (X : Finset A),
        R ≤ X.card → ∀ c : Finset A → Bool, ∃ Q ⊆ X, Q.card = k ∧ ∃ g : A → Bool,
          ∀ e ∈ Q.powersetCard (t + 1), ∀ a ∈ e, (∀ x ∈ e, a ≤ x) → c e = g a := by
      induction k with
      | zero =>
        refine ⟨0, fun A _ X _ c => ⟨∅, empty_subset _, rfl, fun _ => false, ?_⟩⟩
        intro e he
        simp at he
        simp_all
      | succ k hk =>
        obtain ⟨M, hM⟩ := hk
        obtain ⟨R, hR⟩ := ih M
        refine ⟨R+1, fun A _ X hX c => ?_⟩
        have hn : X.Nonempty := card_pos.mp (by omega)
        let a := X.min' hn
        have ha : a ∈ X := min'_mem _ _
        have herase : R ≤ (X.erase a).card := by rw [card_erase_of_mem ha]; omega
        obtain ⟨Y, hy, hyc, b, hb⟩ := hR A (X.erase a) herase (fun e => c (insert a e))
        obtain ⟨Z, hz, hzc, g, hg⟩ := hM A Y hyc.ge c
        have hza : Z ⊆ X.erase a := hz.trans hy
        have haZ : a ∉ Z := fun h => notMem_erase a X (hza h)
        refine ⟨insert a Z, insert_subset ha (hza.trans (erase_subset _ _)),
          by simp [haZ, hzc], Function.update g a b, ?_⟩
        intro e he x hx hmin
        obtain ⟨he, hec⟩ := mem_powersetCard.mp he
        by_cases hae : a ∈ e
        · have hxe : x ∈ X := insert_subset ha (hza.trans (erase_subset _ _)) (he hx)
          have hxa : x = a := le_antisymm (hmin a hae) (min'_le _ _ hxe)
          subst x
          rw [Function.update_self, ← insert_erase hae]
          apply hb
          refine mem_powersetCard.mpr ⟨?_, by rw [card_erase_of_mem hae, hec]; omega⟩
          intro v hv
          obtain ⟨hvne, hve⟩ := mem_erase.mp hv
          exact hz ((mem_insert.mp (he hve)).resolve_left hvne)
        · have hes : e ⊆ Z := fun v hv =>
            (mem_insert.mp (he hv)).resolve_left (fun hv' => hae (hv' ▸ hv))
          rw [Function.update_of_ne (show x ≠ a from fun h => hae (h ▸ hx))]
          exact hg e (mem_powersetCard.mpr ⟨hes, hec⟩) x hx hmin
    intro q
    obtain ⟨R, hR⟩ := aux (2*q)
    refine ⟨R, fun A _ X hx c => ?_⟩
    obtain ⟨Y, hY, hYc, g, hg⟩ := hR A X hx c
    obtain ⟨b, hb⟩ := exists_half_color Y g
    obtain ⟨Q, hQ, hQc⟩ := exists_subset_card_eq (show q ≤ (Y.filter fun x => g x = b).card by omega)
    have hQY : Q ⊆ Y := hQ.trans (filter_subset _ _)
    refine ⟨Q, hQY.trans hY, hQc, b, fun e he => ?_⟩
    obtain ⟨hes, hec⟩ := mem_powersetCard.mp he
    have hne : e.Nonempty := card_pos.mp (by omega)
    let x := e.min' hne
    have hxe : x ∈ e := min'_mem _ _
    exact (hg e (mem_powersetCard.mpr ⟨hes.trans hQY, hec⟩) x hxe
      (fun y hy => min'_le _ _ hy)).trans (mem_filter.mp (hQ (hes hxe))).2


set_option maxHeartbeats 600000 in
private lemma fullPattern_ge {R t q k N : ℕ} (hk : 0 < k) (hN : 0 < N)
    (ram : ∀ col : Finset (Fin R) → Bool, ∃ Q : Finset (Fin R), Q.card = q ∧ ∃ b,
      ∀ e ∈ Q.powersetCard t, col e = b)
    (col : (Fin R → Fin N) → Finset (Fin R) → Bool)
    (record : Samples R k N → ((Fin t → Fin R) → (Fin t → Fin k) → Bool))
    (hrecord : ∀ x y, record x = record y → ∀ a : Positions R k, ∀ e : Finset (Fin R),
      e.card = t → col (fun i => x i (a i)) e = col (fun i => y i (a i)) e) :
    ∃ Q : Finset (Fin R), Q.card = q ∧ ∃ b,
      (2 : ℝ) ^ (-(((2 ^ R * 2) * (R ^ t * k ^ t) : ℕ) : ℝ)) ≤
        densityPattern (fun v => ∀ e ∈ Q.powersetCard t, col v e = b)
          (univ : Finset (Positions R k)) := by
  obtain ⟨w, hw⟩ := large_fiber record
  let C := colorFiber record w
  let D : ℕ := 2 ^ R * 2
  let E : ℕ := R ^ t * k ^ t
  have cardRecord : Fintype.card ((Fin t → Fin R) → (Fin t → Fin k) → Bool) = 2 ^ E := by
    simp [E, Fintype.card_fun, ← pow_mul, mul_comm]
  rw [cardRecord] at hw
  have hM : 0 < Fintype.card (Samples R k N) := by
    simp [Samples, Fintype.card_fun, pow_pos hN]
  have hC : C.Nonempty := by
    apply card_pos.mp
    change _ ≤ _ * C.card at hw
    by_contra! h
    have hz : C.card = 0 := by omega
    rw [hz, mul_zero] at hw
    omega
  obtain ⟨x, hx⟩ := hC
  have hrect (a : Positions R k) := ram (col (fun i => x i (a i)))
  let z (a : Positions R k) : Finset (Fin R) × Bool :=
    (Classical.choose (hrect a), Classical.choose (Classical.choose_spec (hrect a)).2)
  have hz (a : Positions R k) : (z a).1.card = q ∧
      ∀ e ∈ (z a).1.powersetCard t, col (fun i => x i (a i)) e = (z a).2 :=
    ⟨(Classical.choose_spec (hrect a)).1,
      Classical.choose_spec (Classical.choose_spec (hrect a)).2⟩
  obtain ⟨p, hp⟩ := large_fiber z
  let J := colorFiber z p
  have hgrid : 0 < Fintype.card (Positions R k) := by simp [Positions, Fintype.card_fun, pow_pos hk]
  have hpos : 0 < J.card := by
    by_contra! h
    change _ ≤ _ * J.card at hp
    simp [show J.card = 0 by omega] at hp
    omega
  obtain ⟨a, ha⟩ := card_pos.mp hpos
  have hpq : p.1.card = q := mem_colorFiber.mp ha ▸ (hz a).1
  let P (v : Fin R → Fin N) : Prop := ∀ e ∈ p.1.powersetCard t, col v e = p.2
  have hcount : C.card ≤ countPattern P J := by
    apply le_countPattern P J C
    intro y hy a ha e he
    have hxy : record y = record x := (mem_colorFiber.mp hy).trans (mem_colorFiber.mp hx).symm
    rw [hrecord y x hxy a e (mem_powersetCard.mp he).2]
    exact (mem_colorFiber.mp ha ▸ (hz a).2) e he
  have hden : (0 : ℝ) < Fintype.card (Samples R k N) := Nat.cast_pos.mpr hM
  have hw' : (Fintype.card (Samples R k N) : ℝ) ≤ (2 : ℝ) ^ E * (countPattern P J : ℝ) :=
    by exact_mod_cast hw.trans (Nat.mul_le_mul_left _ hcount)
  have hlow : (2 : ℝ) ^ (-(E : ℝ)) ≤ densityPattern P J := by
    rw [densityPattern, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast,
      le_div_iff₀ hden, inv_mul_eq_div, div_le_iff₀ (by positivity)]
    simpa [mul_comm] using hw'
  have hp' : (k : ℝ) ^ R ≤ (D : ℝ) * (J.card : ℝ) := by
    change Fintype.card (Positions R k) ≤ Fintype.card (Finset (Fin R) × Bool) * J.card at hp
    rw [show Fintype.card (Positions R k) = k ^ R by simp [Positions, Fintype.card_fun],
      show Fintype.card (Finset (Fin R) × Bool) = D by simp [D, Fintype.card_finset]] at hp
    exact_mod_cast hp
  let F := densityPattern P (univ : Finset (Positions R k))
  have hF : 0 ≤ F := by dsimp [F, densityPattern]; positivity
  have hF1 : F ≤ 1 :=
    (div_le_one hden).mpr (Nat.cast_le.mpr (countPattern_le_card P univ))
  have hstep : (2 : ℝ) ^ (-(E : ℝ)) ≤ F ^ ((J.card : ℝ) / (k : ℝ) ^ R) :=
    hlow.trans (densityPattern_le_full hk hN P J)
  have hD : (0 : ℝ) < D := by dsimp [D]; positivity
  have hratio : (D : ℝ)⁻¹ ≤ (J.card : ℝ) / (k : ℝ) ^ R := by
    rw [le_div_iff₀ (by positivity), inv_mul_eq_div, div_le_iff₀ hD]
    simpa [mul_comm] using hp'
  have hbound := hstep.trans (Real.rpow_le_rpow_of_exponent_ge' hF hF1 (by positivity) hratio)
  have hbound' := Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _) hbound hD.le
  refine ⟨p.1, hpq, p.2, ?_⟩
  rw [← Real.rpow_mul hF, inv_mul_cancel₀ hD.ne', Real.rpow_one,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)] at hbound'
  push_cast
  convert hbound' using 2
  dsimp [E, D]
  push_cast
  ring

private lemma smallRange_card {s N : ℕ} (hs : 0 < s) (hN : 0 < N) :
    (univ.filter (fun x : Fin (2*s) → Fin N => (univ.image x).card < s)).card ≤
      s ^ (2*s) * N ^ s := by
  let U := (Fin (2*s) → Fin s) × (Fin s → Fin N)
  let f (p : U) := p.2 ∘ p.1
  have hsub : (univ.filter (fun x : Fin (2*s) → Fin N => (univ.image x).card < s)) ⊆
      (univ : Finset U).image f := by
    intro x hx
    let T := univ.image x
    have hc : T.card ≤ s := (mem_filter.mp hx).2.le
    let e := T.orderIsoOfFin rfl
    let g (j : Fin (2*s)) : Fin s := Fin.castLE hc (e.symm ⟨x j, mem_image_of_mem x (mem_univ j)⟩)
    let h (j : Fin s) : Fin N := if hj : j.val < T.card then e ⟨j.val, hj⟩ else ⟨0,hN⟩
    refine mem_image.mpr ⟨(g,h), mem_univ _, ?_⟩
    funext j
    simp [f,g,h]
  exact (card_le_card hsub).trans (by
    simpa [U, Fintype.card_fun] using card_image_le (s := (univ : Finset U)) (f := f))

private lemma badSamples_card {R s N : ℕ} (hs : 0 < s) (hN : 0 < N) :
    ((univ : Finset (Samples R (2*s) N)).filter
      (fun x => ∃ i, (univ.image (x i)).card < s)).card ≤
      R * (s ^ (2*s) * N ^ s) * (N ^ (2*s)) ^ (R - 1) := by
  let B := univ.filter (fun x : Fin (2*s) → Fin N => (univ.image x).card < s)
  let U (i : Fin R) := {j : Fin R // j ≠ i} → Fin (2*s) → Fin N
  let S (i : Fin R) := (univ : Finset (Samples R (2*s) N)).filter (fun x => x i ∈ B)
  have hcard (i : Fin R) : (S i).card = B.card * (N ^ (2*s)) ^ (R - 1) := by
    let e := Equiv.funSplitAt i (Fin (2*s) → Fin N)
    have he : (S i).map e.toEmbedding = B ×ˢ (univ : Finset (U i)) := by
      ext y
      simp [S, e, Equiv.funSplitAt]
    rw [← card_map e.toEmbedding, he, card_product]
    simp [U, Fintype.card_fun]
  have he : ((univ : Finset (Samples R (2*s) N)).filter
      (fun x => ∃ i, (univ.image (x i)).card < s)) = univ.biUnion S := by
    ext x
    simp [S,B]
  rw [he]
  calc
    _ ≤ ∑ i, (S i).card := card_biUnion_le
    _ = R * (B.card * (N ^ (2*s)) ^ (R - 1)) := by simp [hcard, nsmul_eq_mul]
    _ ≤ _ := by rw [mul_assoc]; gcongr; exact smallRange_card hs hN


private lemma multipartite_from_patterns {t q R s N n : ℕ} (hs : 0 < s) (hR : 0 < R)
    (hN : 0 < N) (hn : R * N ≤ n)
    (hsize : 2 ^ ((2 ^ R * 2) * (R ^ t * (2*s) ^ t)) * R * s ^ (2*s) < N ^ s)
    (ram : ∀ col : Finset (Fin R) → Bool, ∃ Q : Finset (Fin R), Q.card = q ∧ ∃ b,
      ∀ e ∈ Q.powersetCard t, col e = b)
    (col : Finset (Fin n) → Bool) :
    ∃ (P : Fin q → Finset (Fin n)) (b : Bool), Pairwise (Disjoint on P) ∧
      (∀ i, (P i).card = s) ∧ ∀ e ∈ (univ.biUnion P).powersetCard t,
        (∀ i x y, x ∈ e → y ∈ e → x ∈ P i → y ∈ P i → x = y) → col e = b := by
  let g (i : Fin R) (v : Fin N) := Fin.castLE hn (finProdFinEquiv (i, v))
  have hg : Function.Injective (fun (p : Fin R × Fin N) => g p.1 p.2) :=
    (Fin.castLEEmb hn).injective.comp finProdFinEquiv.injective
  have hg_pair {i j : Fin R} {x y : Fin N} (h : g i x = g j y) : (i,x) = (j,y) :=
    hg (show (fun (p : Fin R × Fin N) => g p.1 p.2) (i,x) =
      (fun (p : Fin R × Fin N) => g p.1 p.2) (j,y) from h)
  let ec (p : Fin R → Fin N) (I : Finset (Fin R)) := col (I.image fun i => g i (p i))
  let record (x : Samples R (2*s) N) (i : Fin t → Fin R) (a : Fin t → Fin (2*s)) :=
    col (univ.image fun j => g (i j) (x (i j) (a j)))
  have hrecord (x y : Samples R (2*s) N) (hxy : record x = record y)
      (a : Positions R (2*s)) (e : Finset (Fin R)) (he : e.card = t) :
      ec (fun i => x i (a i)) e = ec (fun i => y i (a i)) e := by
    let i := e.orderEmbOfFin he
    have himage : (univ.image i) = e := by
      ext z
      simpa [i, ← Set.mem_range, range_orderEmbOfFin] using
        (show z ∈ (univ.image i) ↔ z ∈ (Set.range i : Set (Fin R)) by simp)
    have h := congrFun (congrFun hxy i) (a ∘ i)
    change col (e.image (fun i => g i (x i (a i)))) = col (e.image (fun i => g i (y i (a i))))
    rw [← himage, image_image, image_image]
    exact h
  obtain ⟨Q, hQ, b, hF⟩ := fullPattern_ge (by omega : 0 < 2*s) hN ram ec record hrecord
  let X := univ.filter (fun x : Samples R (2*s) N =>
    ∀ a : Positions R (2*s), ∀ e ∈ Q.powersetCard t, ec (fun i => x i (a i)) e = b)
  let Y := univ.filter (fun x : Samples R (2*s) N => ∃ i, (univ.image (x i)).card < s)
  let E := (2 ^ R * 2) * (R ^ t * (2*s) ^ t)
  have hF' : (N ^ (2*s)) ^ R ≤ 2 ^ E * X.card := by
    have hden : (0 : ℝ) < Fintype.card (Samples R (2*s) N) := by
      haveI : Nonempty (Fin N) := ⟨⟨0,hN⟩⟩
      exact_mod_cast Fintype.card_pos
    rw [densityPattern, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast,
      le_div_iff₀ hden, inv_mul_eq_div, div_le_iff₀ (by positivity)] at hF
    have H : (Fintype.card (Samples R (2*s) N) : ℝ) ≤ (2 : ℝ) ^ E * (X.card : ℝ) := by
      simpa [E, X, countPattern, mul_comm] using hF
    have hnat : Fintype.card (Samples R (2*s) N) ≤ 2 ^ E * X.card := by
      exact_mod_cast H
    simpa [Samples] using hnat
  have hY' : 2 ^ E * Y.card < (N ^ (2*s)) ^ R := by
    refine (Nat.mul_le_mul_left _ (badSamples_card (R := R) hs hN)).trans_lt ?_
    rw [show (N ^ (2*s)) ^ R = (N ^ (2*s)) ^ (R - 1) * N ^ (2*s) by
      rw [← pow_succ]; congr 1; omega]
    have ha : 2 ^ E * R * s ^ (2*s) * N ^ s < N ^ (2*s) := by
      rw [show N ^ (2*s) = N ^ s * N ^ s by rw [two_mul, pow_add]]
      exact Nat.mul_lt_mul_of_pos_right hsize (pow_pos hN _)
    calc
      _ = (N ^ (2*s)) ^ (R - 1) * (2 ^ E * R * s ^ (2*s) * N ^ s) := by ac_rfl
      _ < _ := Nat.mul_lt_mul_of_pos_left ha (pow_pos (pow_pos hN _) _)
  obtain ⟨x, hx, hy⟩ := exists_mem_notMem_of_card_lt_card (show Y.card < X.card by
    by_contra! h
    exact (not_lt_of_ge ((Nat.mul_le_mul_left _ h).trans' hF')) hY')
  have hx' := (mem_filter.mp hx).2
  have hy' (i : Fin R) : s ≤ (univ.image (x i)).card := by
    by_contra! h
    exact hy (mem_filter.mpr ⟨mem_univ _, i, h⟩)
  let f := Q.orderEmbOfFin hQ
  choose V hV hcard using fun i : Fin q => exists_subset_card_eq (hy' (f i))
  let P (i : Fin q) := (V i).image (g (f i))
  have hg' (i : Fin q) : Function.Injective (g (f i)) :=
    fun _ _ h => congrArg Prod.snd (hg_pair h)
  refine ⟨P, b, ?_, fun i => (card_image_of_injective _ (hg' i)).trans (hcard i), ?_⟩
  · intro i j hij
    apply disjoint_left.mpr
    intro v hi hj
    obtain ⟨u, _, hu⟩ := mem_image.mp hi
    obtain ⟨w, _, hw⟩ := mem_image.mp hj
    exact hij (f.injective (congrArg Prod.fst (hg_pair (hu.trans hw.symm))))
  · intro e he hcross
    obtain ⟨hes, hec⟩ := mem_powersetCard.mp he
    let S := univ.filter (fun i : Fin q => ∃ v ∈ e, v ∈ P i)
    have hslots (i : Fin q) (hi : i ∈ S) : ∃ j : Fin (2*s), g (f i) (x (f i) j) ∈ e ∧ g (f i) (x (f i) j) ∈ P i := by
      obtain ⟨v,hve,hvp⟩ := (mem_filter.mp hi).2
      obtain ⟨w,hw,rfl⟩ := mem_image.mp hvp
      obtain ⟨j,_,rfl⟩ := mem_image.mp (hV i hw)
      exact ⟨j,hve,hvp⟩
    let j (i : Fin q) : Fin (2*s) :=
      if hi : i ∈ S then Classical.choose (hslots i hi) else ⟨0, by omega⟩
    let a : Fin R → Fin (2*s) := Function.extend f j (fun _ => ⟨0, by omega⟩)
    have ha (i : Fin q) (hi : i ∈ S) : ∃ v ∈ e, v ∈ P i ∧ g (f i) (x (f i) (a (f i))) = v := by
      have hav : a (f i) = Classical.choose (hslots i hi) := by
        change Function.extend f j _ (f i) = _
        rw [f.injective.extend_apply]
        simp [j, hi]
      obtain ⟨h1, h2⟩ := Classical.choose_spec (hslots i hi)
      exact ⟨g (f i) (x (f i) (a (f i))), hav.symm ▸ h1, hav.symm ▸ h2, rfl⟩
    let I := S.image f
    have himage : I.image (fun r => g r (x r (a r))) = e := by
      ext v
      constructor
      · intro hv
        obtain ⟨r,hr,rfl⟩ := mem_image.mp hv
        obtain ⟨i,hi,rfl⟩ := mem_image.mp hr
        obtain ⟨w,hw,_,h⟩ := ha i hi
        exact h ▸ hw
      · intro hv
        obtain ⟨i,_,hvi⟩ := mem_biUnion.mp (hes hv)
        have hi : i ∈ S := mem_filter.mpr ⟨mem_univ _,v,hv,hvi⟩
        obtain ⟨w,hw,hwi,h⟩ := ha i hi
        exact mem_image.mpr ⟨f i, mem_image_of_mem f hi, h.trans (hcross i w v hw hv hwi hvi)⟩
    have hinj : Function.Injective (fun r => g r (x r (a r))) :=
      fun _ _ hij => congrArg Prod.fst (hg_pair hij)
    have hI : I ∈ Q.powersetCard t := mem_powersetCard.mpr ⟨by
      intro z hz
      obtain ⟨i,_,rfl⟩ := mem_image.mp hz
      exact orderEmbOfFin_mem _ _ _, by
      rw [← hec, ← himage, card_image_of_injective I hinj]⟩
    simpa [ec,himage] using hx' a I hI

end Blowup

private lemma quarter_lower (d : ℕ) (hd : 0 < d) :
    logScale d =O[atTop] threshold (d + 1) (1 / 4) := by
  classical
  let t := d + 1
  let q := 4 * (2 ^ t * t.factorial) + 2 * t + 1
  have ht : 2 ≤ t := by dsimp [t]; omega
  have hq : 2*t ≤ q := by dsimp [q]; omega
  have hq' : (2 : ℝ)^t * t.factorial < (1/4 : ℝ) * q := by
    dsimp [q]
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) t]
  obtain ⟨R0, hR0⟩ := finite_ramsey t q
  let R := max R0 q
  have hR : 0 < R := by
    have := le_max_right R0 q
    omega
  have ram (col : Finset (Fin R) → Bool) :
      ∃ Q : Finset (Fin R), Q.card = q ∧ ∃ b,
        ∀ e ∈ Q.powersetCard t, col e = b := by
    obtain ⟨Q, _, hQc, hQ⟩ := hR0 (Fin R) univ (by simpa [R] using le_max_left R0 q) col
    exact ⟨Q,hQc,hQ⟩
  let A := (2 ^ R * 2) * (R ^ t * 2 ^ t)
  let K := A + R + 3
  apply logScale_bigO_threshold_of_finite d hd (1 / 4) (K + R)
  intro n s hs hn
  let L := (s + 1)^d
  let N := 2^(K*L)
  have hN : 0 < N := by dsimp [N]; positivity
  have hsL : s ≤ L := by
    refine (Nat.le_succ s).trans ?_
    simpa [pow_one] using (pow_le_pow_right₀ (show 1 ≤ s+1 by omega) hd)
  have hL : 1 ≤ L := by omega
  have hLs : 1 ≤ L*s := Nat.mul_pos hL hs
  have hRn : R * N ≤ n := by
    calc
      _ ≤ 2^R * N := Nat.mul_le_mul_right _ (show R < 2 ^ R from Nat.lt_two_pow_self).le
      _ = 2^(R + K*L) := by simp [N, pow_add]
      _ ≤ 2^((K+R)*L) := by
        apply pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ))
        calc
          R + K*L ≤ R*L + K*L := Nat.add_le_add_right (Nat.le_mul_of_pos_right R hL) _
          _ = (K+R)*L := by ring
      _ ≤ n := hn
  have hsize : 2 ^ ((2 ^ R * 2) * (R ^ t * (2*s) ^ t)) * R * s ^ (2*s) < N ^ s := by
    have hE : (2 ^ R * 2) * (R ^ t * (2*s) ^ t) = A*s^t := by
      dsimp [A]
      rw [mul_pow]
      ring
    rw [hE]
    calc
      _ ≤ 2^(A*s^t) * 2^R * (2^s)^(2*s) := by
        gcongr
        · exact (show R < 2 ^ R from Nat.lt_two_pow_self).le
        · exact (show s < 2 ^ s from Nat.lt_two_pow_self).le
      _ = 2^(A*s^t + R + s*(2*s)) := by
        simp only [pow_add, pow_mul (2 : ℕ) s (2*s)]
      _ < 2^(K*L*s) := by
        apply pow_lt_pow_right₀ (by decide : (1 : ℕ) < 2)
        have hd' : s^d ≤ L := pow_le_pow_left₀ (by omega) (by omega) _
        have hsT : s^t ≤ L*s := by
          change s^(d+1) ≤ _
          rw [pow_succ]
          exact Nat.mul_le_mul_right _ hd'
        have hA := Nat.mul_le_mul_left A hsT
        have hR' := Nat.le_mul_of_pos_right R hLs
        have hs' := Nat.mul_le_mul_right (2*s) hsL
        have h : 0 < L*s := hLs
        dsimp [K]
        nlinarith [Nat.mul_pos hL hs]
      _ = N ^ s := by rw [pow_mul _ (K*L) s]
  have hm := threshold_gt_of_multipartite (n := n) (t := t) (q := q) ht hs hq hq'
    (multipartite_from_patterns hs hR hN hRn hsize ram)
  exact (Nat.le_mul_of_pos_left s (show 0 < q by omega)).trans_lt hm

theorem OMA.solution : OMA.R_Erdos161_erdos_161_parts_ii_R2.H1 := by
  intro t ht γ hγ hγhalf
  obtain ⟨d,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show t ≠ 0 by omega)
  exact (threshold_bigO_logScale d (by omega) (by linarith) hγhalf).trans
    (quarter_lower d (by omega))

