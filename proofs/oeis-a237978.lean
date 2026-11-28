import OMAStatements.S_oeis_a237978

-- Problem: A237978: Number of partitions of n having depth 3; see Comments.
-- Upstream: formal-conjectures statements/oeis-a237978.lean:0 (declaration OMA.S_oeis_a237978.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea. Lower bound: a repeated part y of f(t) is m1*x1 = m2*x2 for distinct parts
-- x1 < x2 of t with multiplicities m1, m2, so m1 >= 2: x1 is a repeated part of t and y >= 2*x1.
-- By induction every repeated part of c(j,P) is at least 2^j. If P has depth d >= 1, c(d-1,P)
-- has a repeated part y >= 2^(d-1), so n = sum of c(d-1,P) >= 2y >= 2^d. Witness: with
-- U(0) = {} and U(k+1) = {2} + 2*U(k) (that is {2, 4, ..., 2^k}), the partition {1, 1} + U(k) of
-- 2^(k+1) has f-image {2} + U(k), which is 2*({1, 1} + U(k-1)) for k >= 1; f commutes with
-- scaling, so the depth of c*({1, 1} + U(k)) is k+1 for every c > 0.

open OMA.S_oeis_a237978 in
theorem OMA.solution : type_of% @OMA.S_oeis_a237978.main := by
  -- the multiplicity of y in f t
  have Fcount : ∀ (t : Multiset ℕ) (y : ℕ),
      (f t).count y = (t.toFinset.filter (fun x => y = t.count x * x)).card := by
    intro t y
    unfold f
    exact Multiset.count_map _ _ _
  -- a repeated part of f t comes from a repeated part of t
  have Fstep : ∀ (t : Multiset ℕ) (y : ℕ), 2 ≤ (f t).count y →
      ∃ x, 2 ≤ t.count x ∧ t.count x * x = y := by
    intro t y hy
    rw [Fcount t y] at hy
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp
      (show 1 < (t.toFinset.filter (fun x => y = t.count x * x)).card by omega)
    rw [Finset.mem_filter, Multiset.mem_toFinset] at ha hb
    obtain ⟨ha1, ha2⟩ := ha
    obtain ⟨hb1, hb2⟩ := hb
    have hca : 0 < t.count a := Multiset.count_pos.mpr ha1
    have hcb : 0 < t.count b := Multiset.count_pos.mpr hb1
    rcases Nat.lt_or_gt_of_ne hab with hlt | hlt
    · refine ⟨a, ?_, ha2.symm⟩
      by_contra hc
      have h1 : t.count a ≤ t.count b := by omega
      have h2 : t.count a * a ≤ t.count b * a := Nat.mul_le_mul_right a h1
      have h3 : t.count b * (a + 1) ≤ t.count b * b := Nat.mul_le_mul_left (t.count b) hlt
      rw [Nat.mul_add, Nat.mul_one] at h3
      omega
    · refine ⟨b, ?_, hb2.symm⟩
      by_contra hc
      have h1 : t.count b ≤ t.count a := by omega
      have h2 : t.count b * b ≤ t.count a * b := Nat.mul_le_mul_right b h1
      have h3 : t.count a * (b + 1) ≤ t.count a * a := Nat.mul_le_mul_left (t.count a) hlt
      rw [Nat.mul_add, Nat.mul_one] at h3
      omega
  -- every repeated part of c(j,s) is at least 2^j
  have Key : ∀ (s : Multiset ℕ), (∀ x ∈ s, 0 < x) →
      ∀ j y, 2 ≤ (f^[j] s).count y → 2 ^ j ≤ y := by
    intro s hs j
    induction j with
    | zero =>
      intro y hy
      have hpos : 0 < s.count y := by
        have e0 : f^[0] s = s := rfl
        rw [e0] at hy
        omega
      have hy0 := hs y (Multiset.count_pos.mp hpos)
      rw [pow_zero]
      omega
    | succ j ih =>
      intro y hy
      rw [Function.iterate_succ_apply'] at hy
      obtain ⟨x, hx2, hxy⟩ := Fstep _ y hy
      have hx := ih x hx2
      have h1 : 2 * x ≤ (f^[j] s).count x * x := Nat.mul_le_mul_right x hx2
      rw [pow_succ]
      omega
  -- f keeps the sum
  have Fsum : ∀ t : Multiset ℕ, (f t).sum = t.sum := by
    intro t
    unfold f
    rw [← Finset.sum_eq_multiset_sum, Finset.sum_multiset_count t]
    simp only [smul_eq_mul]
  have Isum : ∀ (t : Multiset ℕ) (j : ℕ), (f^[j] t).sum = t.sum := by
    intro t j
    induction j with
    | zero => rfl
    | succ j ih => rw [Function.iterate_succ_apply', Fsum, ih]
  -- the lower bound
  have Lower : ∀ d n : ℕ, 1 ≤ n → n < 2 ^ d → ∀ P : Nat.Partition n, ¬ HasDepth P.parts d := by
    intro d n hn hlt P hP
    cases d with
    | zero =>
      rw [pow_zero] at hlt
      omega
    | succ e =>
      obtain ⟨-, hP2⟩ := hP
      have hnd : ¬ (f^[e] P.parts).Nodup := hP2 e (by omega)
      rw [Multiset.nodup_iff_count_le_one] at hnd
      simp only [not_forall, not_le] at hnd
      obtain ⟨y, hy⟩ := hnd
      have hy2 : 2 ≤ (f^[e] P.parts).count y := by omega
      have hky := Key P.parts (fun x hx => P.parts_pos hx) e y hy2
      have hrep : Multiset.replicate 2 y ≤ f^[e] P.parts := Multiset.le_count_iff_replicate_le.mp hy2
      obtain ⟨u, hu⟩ := Multiset.le_iff_exists_add.mp hrep
      have hs : (f^[e] P.parts).sum = n := by rw [Isum, P.parts_sum]
      rw [hu, Multiset.sum_add, Multiset.sum_replicate, smul_eq_mul] at hs
      rw [pow_succ] at hlt
      omega
  -- the witnesses
  obtain ⟨U, hU0, hUs⟩ : ∃ U : ℕ → Multiset ℕ, U 0 = 0 ∧
      ∀ k, U (k + 1) = 2 ::ₘ (U k).map (fun x => 2 * x) :=
    ⟨fun k => Nat.rec (motive := fun _ => Multiset ℕ) 0
      (fun _ u => 2 ::ₘ u.map (fun x => 2 * x)) k, rfl, fun k => rfl⟩
  have Uge : ∀ k, ∀ x ∈ U k, 2 ≤ x := by
    intro k
    induction k with
    | zero =>
      intro x hx
      rw [hU0] at hx
      simp at hx
    | succ k ih =>
      intro x hx
      rw [hUs k, Multiset.mem_cons] at hx
      rcases hx with hx | hx
      · omega
      · obtain ⟨z, hz, hzx⟩ := Multiset.mem_map.mp hx
        have hzx' : 2 * z = x := hzx
        have := ih z hz
        omega
  have hinj2 : Function.Injective (fun x : ℕ => 2 * x) :=
    fun a b h => Nat.eq_of_mul_eq_mul_left (by norm_num) h
  have Unodup : ∀ k, (U k).Nodup := by
    intro k
    induction k with
    | zero =>
      rw [hU0]
      exact Multiset.nodup_zero
    | succ k ih =>
      rw [hUs k]
      apply Multiset.Nodup.cons
      · intro h2
        obtain ⟨z, hz, hz2⟩ := Multiset.mem_map.mp h2
        have hz2' : 2 * z = 2 := hz2
        have := Uge k z hz
        omega
      · exact (Multiset.nodup_map_iff_of_injective hinj2).mpr ih
  have hmap : ∀ s : Multiset ℕ, (s.map (fun x => 2 * x)).sum = 2 * s.sum := by
    intro s
    induction s using Multiset.induction_on with
    | empty => simp
    | cons a s ih =>
      rw [Multiset.map_cons, Multiset.sum_cons, Multiset.sum_cons, ih]
      ring
  have Usum : ∀ k, (U k).sum + 2 = 2 ^ (k + 1) := by
    intro k
    induction k with
    | zero =>
      rw [hU0]
      norm_num
    | succ k ih =>
      rw [hUs k, Multiset.sum_cons, hmap, pow_succ]
      omega
  -- f on {1, 1} + V
  have F2 : ∀ V : Multiset ℕ, V.Nodup → (∀ x ∈ V, 2 ≤ x) → f (1 ::ₘ 1 ::ₘ V) = 2 ::ₘ V := by
    intro V hVn hV
    have h1V : (1 : ℕ) ∉ V := fun h => absurd (hV 1 h) (by norm_num)
    have h1V' : (1 : ℕ) ∉ V.toFinset := by
      rw [Multiset.mem_toFinset]
      exact h1V
    have hc1 : (1 ::ₘ 1 ::ₘ V).count 1 = 2 := by
      have h0 := Multiset.count_eq_zero.mpr h1V
      rw [Multiset.count_cons_self, Multiset.count_cons_self]
      omega
    have hcx : ∀ x ∈ V, (1 ::ₘ 1 ::ₘ V).count x = 1 := by
      intro x hx
      have hx1 : x ≠ 1 := fun h => by
        have := hV x hx
        omega
      rw [Multiset.count_cons_of_ne hx1, Multiset.count_cons_of_ne hx1,
        Multiset.count_eq_one_of_mem hVn hx]
    unfold f
    rw [Multiset.toFinset_cons, Multiset.toFinset_cons,
      Finset.insert_eq_of_mem (Finset.mem_insert_self (1 : ℕ) _), Finset.insert_val_of_notMem h1V',
      Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hVn, Multiset.map_cons, hc1, mul_one]
    congr 1
    conv_rhs => rw [← Multiset.map_id' V]
    apply Multiset.map_congr rfl
    intro x hx
    show (1 ::ₘ 1 ::ₘ V).count x * x = x
    rw [hcx x hx, one_mul]
  -- f commutes with scaling
  have F3 : ∀ (c : ℕ) (s : Multiset ℕ), 0 < c →
      f (s.map (fun x => c * x)) = (f s).map (fun x => c * x) := by
    intro c s hc
    have hinj : Function.Injective (fun x : ℕ => c * x) :=
      fun a b h => Nat.eq_of_mul_eq_mul_left hc h
    have hinjOn : Set.InjOn (fun x : ℕ => c * x) (s.toFinset : Set ℕ) :=
      fun a _ b _ h => hinj h
    unfold f
    rw [Multiset.toFinset_map, Finset.image_val_of_injOn hinjOn,
      Multiset.map_map, Multiset.map_map]
    apply Multiset.map_congr rfl
    intro x _
    show (s.map (fun x => c * x)).count (c * x) * (c * x) = c * (s.count x * x)
    rw [Multiset.count_map_eq_count' _ _ hinj x]
    ring
  have mm : ∀ (a b : ℕ) (s : Multiset ℕ),
      (s.map (fun x => b * x)).map (fun x => a * x) = s.map (fun x => a * b * x) := by
    intro a b s
    rw [Multiset.map_map]
    congr 1
    funext x
    show a * (b * x) = a * b * x
    ring
  -- one step of depth
  have Dstep : ∀ (s : Multiset ℕ) (d : ℕ), ¬ s.Nodup → HasDepth (f s) d → HasDepth s (d + 1) := by
    intro s d hs hd
    obtain ⟨h1, h2⟩ := hd
    unfold HasDepth
    refine ⟨?_, ?_⟩
    · rw [Function.iterate_succ_apply]
      exact h1
    · intro j hj
      cases j with
      | zero => exact hs
      | succ i =>
        rw [Function.iterate_succ_apply]
        exact h2 i (by omega)
  have Ddepth : ∀ k (c : ℕ), 0 < c →
      HasDepth ((1 ::ₘ 1 ::ₘ U k).map (fun x => c * x)) (k + 1) := by
    intro k
    induction k with
    | zero =>
      intro c hc
      apply Dstep
      · intro h
        rw [Multiset.map_cons] at h
        exact (Multiset.nodup_cons.mp h).1 (by simp)
      · rw [F3 c _ hc, F2 (U 0) (Unodup 0) (Uge 0), hU0]
        unfold HasDepth
        refine ⟨?_, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
        simp
    | succ k ih =>
      intro c hc
      apply Dstep
      · intro h
        rw [Multiset.map_cons] at h
        exact (Multiset.nodup_cons.mp h).1 (by simp)
      · rw [F3 c _ hc, F2 (U (k + 1)) (Unodup (k + 1)) (Uge (k + 1))]
        have e : (2 ::ₘ U (k + 1)).map (fun x => c * x) =
            (1 ::ₘ 1 ::ₘ U k).map (fun x => c * 2 * x) := by
          rw [hUs k, Multiset.map_cons, Multiset.map_cons, Multiset.map_cons, Multiset.map_cons,
            mm c 2 (U k), mul_one]
        rw [e]
        exact ih (c * 2) (by omega)
  have Exist : ∀ d : ℕ, ∃ P : Nat.Partition (2 ^ d), HasDepth P.parts d := by
    intro d
    cases d with
    | zero =>
      have hpos0 : ∀ {i : ℕ}, i ∈ ({1} : Multiset ℕ) → 0 < i := by
        intro i hi
        rw [Multiset.mem_singleton] at hi
        omega
      have hsum0 : ({1} : Multiset ℕ).sum = 2 ^ 0 := by simp
      refine ⟨⟨{1}, hpos0, hsum0⟩, ?_⟩
      unfold HasDepth
      refine ⟨?_, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
      simp
    | succ k =>
      have hpos : ∀ {i : ℕ}, i ∈ 1 ::ₘ 1 ::ₘ U k → 0 < i := by
        intro i hi
        rw [Multiset.mem_cons, Multiset.mem_cons] at hi
        rcases hi with h | h | h
        · omega
        · omega
        · have := Uge k i h
          omega
      have hsum : (1 ::ₘ 1 ::ₘ U k).sum = 2 ^ (k + 1) := by
        rw [Multiset.sum_cons, Multiset.sum_cons]
        have := Usum k
        omega
      refine ⟨⟨1 ::ₘ 1 ::ₘ U k, hpos, hsum⟩, ?_⟩
      have h := Ddepth k 1 (by norm_num)
      have e1 : (1 ::ₘ 1 ::ₘ U k).map (fun x => 1 * x) = 1 ::ₘ 1 ::ₘ U k := by simp
      rw [e1] at h
      exact h
  intro d
  exact ⟨Exist d, Lower d⟩
