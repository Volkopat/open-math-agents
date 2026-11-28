import OMAReductions.R_IrvingLeather_irving_leather_growth_rate_R1

/-!
# Saturating stable-marriage markets

The independent block matchings follow the product injection in the merged
growth-rate H1 proof by @tatashbar. The sorted-rank argument follows the
interval-schedule reduction by @MrSeizy for the power-of-two problem. The cyclic
completion below supplies stable partners for the previously unused pairs.

A Latin marriage profile has complementary ranks on every pair, as in
Benjamin, Converse and Krieger, How do I marry thee? Let me count the ways!
The extension has this property outside a prefix of fixed width in every
man's list, even as the number of participants tends to infinity.
-/

open StableMarriage IrvingLeather

namespace OMA.R_IrvingLeather_irving_leather_growth_rate_R1_H3_R1

private theorem sorted_rank {N : ℕ} (f : Fin N → ℕ) (hf : Function.Injective f) :
    ∃ r : Equiv.Perm (Fin N), ∀ i j, r i < r j ↔ f i < f j := by
  classical
  let s := Finset.univ.image f
  have hs : s.card = N := by
    rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]
  let g : Fin N ≃ s := Equiv.ofBijective
    (fun i => ⟨f i, Finset.mem_image_of_mem f (Finset.mem_univ i)⟩)
    ⟨fun _ _ h => hf (congrArg Subtype.val h), by
      intro y
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp y.property
      exact ⟨i, Subtype.ext hi⟩⟩
  let order := (s.orderIsoOfFin hs).symm
  exact ⟨g.trans order.toEquiv, fun _ _ => order.lt_iff_lt⟩

private theorem ranked {N : ℕ} {A : Type*} (e : A ≃ Fin N)
    (f g : A → A → ℕ) (hf : ∀ x, Function.Injective (f x))
    (hg : ∀ y, Function.Injective (fun x => g x y)) :
    ∃ q : Profile N,
      (∀ x y z, q.manRank (e x) (e y) < q.manRank (e x) (e z) ↔ f x y < f x z) ∧
      (∀ y x z, q.womanRank (e y) (e x) < q.womanRank (e y) (e z) ↔ g z y < g x y) := by
  choose mr hm using fun x => sorted_rank (f x ∘ e.symm) ((hf x).comp e.symm.injective)
  choose wr hw using fun y => sorted_rank ((fun x => g x y) ∘ e.symm)
    ((hg y).comp e.symm.injective)
  refine ⟨⟨fun i => mr (e.symm i), fun j => (wr (e.symm j)).trans Fin.revPerm⟩, ?_, ?_⟩
  · intro x y z
    simpa using hm x (e y) (e z)
  · intro y x z
    simpa using (Fin.rev_lt_rev.trans (hw y (e z) (e x)))

private theorem stable_test {N : ℕ} {A : Type*} (e : A ≃ Fin N) (q : Profile N)
    (u : Equiv.Perm A)
    (h : ∀ x z, q.manRank (e x) (e (u z)) < q.manRank (e x) (e (u x)) →
      ¬ q.womanRank (e (u z)) (e x) < q.womanRank (e (u z)) (e z)) :
    IsStable q (e.permCongr u) := by
  intro m w hb
  obtain ⟨x, rfl⟩ := e.surjective m
  obtain ⟨z, rfl⟩ := (u.trans e).surjective w
  have hinv : (e.permCongr u).symm (e (u z)) = e z :=
    (e.permCongr u).symm_apply_eq.mpr (by simp [Equiv.permCongr_apply])
  exact h x z (by simpa [Equiv.permCongr_apply] using hb.2.1)
    (by simpa only [Equiv.trans_apply, hinv] using hb.2.2)

private theorem product_count {n k N : ℕ} (p : Profile n) (q : Profile N)
    (e : (Fin k × Fin n) ≃ Fin N)
    (h : ∀ u : Fin k → {a : Matching n // IsStable p a},
      IsStable q (e.permCongr (Equiv.prodCongrRight fun i => (u i).val))) :
    numStableMatchings p ^ k ≤ numStableMatchings q := by
  classical
  unfold numStableMatchings
  rw [← Fintype.card_fin k, ← Fintype.card_fun]
  refine Fintype.card_le_of_injective (fun u => ⟨_, h u⟩) ?_
  intro u v he
  have hperm := e.permCongr.injective (congrArg Subtype.val he)
  funext i
  apply Subtype.ext
  ext j
  have hval := congrArg (fun b : Equiv.Perm (Fin k × Fin n) => (b (i,j)).2) hperm
  exact congrArg Fin.val hval

set_option maxHeartbeats 1000000 in
/-- Two copies suffice to attain every pair, preserving the square of the count. -/
theorem saturate {n : ℕ} [NeZero n] (p : Profile n) :
    ∃ q : Profile (2*n),
      (∀ m w, ∃ a : Matching (2*n), IsStable q a ∧ a m = w) ∧
      numStableMatchings p ^ 2 ≤ numStableMatchings q := by
  classical
  let e : (Fin 2 × Fin n) ≃ Fin (2*n) := finProdFinEquiv
  let used (i j : Fin n) := ∃ a : Matching n, IsStable p a ∧ a i = j
  let early (x y : Fin 2 × Fin n) := x.1 = y.1 ∧ used x.2 y.2
  -- For each cyclic difference, cross-copy pairs occupy the even offset.
  -- Unused same-copy pairs occupy the immediately following odd offset.
  let time (x y : Fin 2 × Fin n) :=
    n + 2 * (y.2 - x.2).val + (if x.1 = y.1 then 1 else 0)
  let f (x y : Fin 2 × Fin n) := if early x y then (p.manRank x.2 y.2).val else time x y
  let g (x y : Fin 2 × Fin n) :=
    if early x y then (p.womanRank y.2 x.2).rev.val else time x y
  have ht (x y : Fin 2 × Fin n) : n ≤ time x y := by dsimp [time]; omega
  have hbit {a b c : Fin 2} (h : (a = b) ↔ (a = c)) : b = c := by
    fin_cases a <;> fin_cases b <;> fin_cases c <;> simp_all
  have htime {x y z : Fin 2 × Fin n} (h : time x y = time x z) : y = z := by
    simp only [time] at h
    have hd : y.2 - x.2 = z.2 - x.2 := Fin.ext (by split_ifs at h <;> omega)
    have hb : (x.1 = y.1) ↔ (x.1 = z.1) := by split_ifs at h <;> omega
    exact Prod.ext (hbit hb) (sub_left_inj.mp hd)
  have htime' {x y z : Fin 2 × Fin n} (h : time x y = time z y) : x = z := by
    simp only [time] at h
    have hd : y.2 - x.2 = y.2 - z.2 := Fin.ext (by split_ifs at h <;> omega)
    have hb : (y.1 = x.1) ↔ (y.1 = z.1) := by
      rw [eq_comm (a := y.1) (b := x.1), eq_comm (a := y.1) (b := z.1)]
      split_ifs at h <;> omega
    exact Prod.ext (hbit hb) (sub_right_inj.mp hd)
  have hf (x) : Function.Injective (f x) := by
    intro y z h
    simp only [f] at h
    split_ifs at h with hy hz hz
    · exact Prod.ext (hy.1.symm.trans hz.1) ((p.manRank x.2).injective (Fin.ext h))
    · exact False.elim (by have := (p.manRank x.2 y.2).isLt; have := ht x z; omega)
    · exact False.elim (by have := (p.manRank x.2 z.2).isLt; have := ht x y; omega)
    · exact htime h
  have hg (y) : Function.Injective (fun x => g x y) := by
    intro x z h
    simp only [g] at h
    split_ifs at h with hx hz hz
    · exact Prod.ext (hx.1.trans hz.1.symm) ((p.womanRank y.2).injective
        (Fin.rev_injective (Fin.ext h)))
    · exact False.elim (by have := (p.womanRank y.2 x.2).rev.isLt; have := ht z y; omega)
    · exact False.elim (by have := (p.womanRank y.2 z.2).rev.isLt; have := ht x y; omega)
    · exact htime' h
  obtain ⟨q, hm, hw⟩ := ranked e f g hf hg
  have hold (u : Fin 2 → {a : Matching n // IsStable p a}) :
      IsStable q (e.permCongr (Equiv.prodCongrRight fun i => (u i).val)) := by
    let v := Equiv.prodCongrRight fun i => (u i).val
    have hev (x : Fin 2 × Fin n) : early x (v x) :=
      ⟨rfl, (u x.1).val, (u x.1).property, rfl⟩
    apply stable_test e q v
    intro x z hm' hw'
    have ha := (hm _ _ _).mp hm'
    have hb := (hw _ _ _).mp hw'
    simp only [f, g, if_pos (hev x), if_pos (hev z)] at ha hb
    by_cases h : early x (v z)
    · rw [if_pos h] at ha hb
      obtain ⟨i, a⟩ := x
      obtain ⟨j, b⟩ := z
      have hij : i = j := h.1
      subst j
      change (p.manRank a ((u i).val b)).val < (p.manRank a ((u i).val a)).val at ha
      change (p.womanRank ((u i).val b) b).rev < (p.womanRank ((u i).val b) a).rev at hb
      apply (u i).property a ((u i).val b)
      exact ⟨fun eq => (ne_of_lt ha) (by rw [eq]), ha, by simpa using Fin.rev_lt_rev.mp hb⟩
    · rw [if_neg h] at ha
      have := ht x (v z)
      have := (p.manRank x.2 (v x).2).isLt
      omega
  -- A matching using two consecutive late scores is stable. An early
  -- candidate loses on the woman's side. A late blocker would need an
  -- integer strictly between the two scores.
  have hband (v : Equiv.Perm (Fin 2 × Fin n)) (t : ℕ)
      (hv : ∀ x, ¬early x (v x) ∧ t ≤ time x (v x) ∧ time x (v x) ≤ t+1) :
      IsStable q (e.permCongr v) := by
    apply stable_test e q v
    intro x z ha hb
    have hm' := (hm _ _ _).mp ha
    have hw' := (hw _ _ _).mp hb
    simp only [f, g, if_neg (hv x).1, if_neg (hv z).1] at hm' hw'
    by_cases h : early x (v z)
    · rw [if_pos h] at hw'
      have := ht z (v z)
      have := (p.womanRank (v z).2 x.2).rev.isLt
      omega
    · rw [if_neg h] at hm' hw'
      have := (hv x).2.2
      have := (hv z).2.1
      omega
  refine ⟨q, ?_, product_count p q e hold⟩
  intro m w
  obtain ⟨⟨i,a⟩, rfl⟩ := e.surjective m
  obtain ⟨⟨j,b⟩, rfl⟩ := e.surjective w
  by_cases h : early (i,a) (j,b)
  · obtain ⟨hi, u, hu, huv⟩ := h
    change i = j at hi
    subst j
    refine ⟨_, hold (fun _ => ⟨u, hu⟩), ?_⟩
    simp [Equiv.permCongr_apply, huv]
  · -- Use the same within-block translation everywhere. To attain a
    -- missing same-copy pair, keep the copy index at unused cells and
    -- interchange the two copies at the other cells.
    let d := b-a
    let switch (a' : Fin n) : Equiv.Perm (Fin 2) :=
      if i = j ∧ ¬used a' (a'+d) then Equiv.refl _ else Fin.revPerm
    let v : Equiv.Perm (Fin 2 × Fin n) := (Equiv.prodCongrLeft switch).trans
      ((Equiv.refl (Fin 2)).prodCongr (Equiv.addRight d))
    have hv (x : Fin 2 × Fin n) : v x = (switch x.2 x.1, x.2+d) := rfl
    have hrev (s : Fin 2) : s ≠ s.rev := by fin_cases s <;> decide
    have hs (x : Fin 2 × Fin n) : ¬ early x (v x) := by
      rw [hv]
      dsimp [early, switch]
      split_ifs with hh
      · exact fun he => hh.2 he.2
      · exact fun he => hrev x.1 he.1
    have hstable : IsStable q (e.permCongr v) := by
      apply hband v (n + 2*d.val)
      intro x
      refine ⟨hs x, ?_⟩
      simp only [time, hv, add_sub_cancel_left]
      split_ifs <;> omega
    refine ⟨_, hstable, ?_⟩
    simp only [Equiv.permCongr_apply, e.symm_apply_apply, hv]
    apply congrArg e
    have hd : a+d = b := by simp [d]
    apply Prod.ext _ hd
    dsimp [switch]
    rw [hd]
    by_cases hij : i = j
    · have hu : ¬used a b := fun hu => h ⟨hij, hu⟩
      simp [hij, hu]
    · simp only [hij, false_and, if_false, Fin.revPerm_apply]
      fin_cases i <;> fin_cases j <;> first | rfl | exact False.elim (hij rfl)

set_option maxHeartbeats 800000 in
/-- Replicate a market in cyclically indexed blocks. Beyond each man's first
`n` ranks, the two ranks on every pair are complementary. -/
theorem replicate_market {k n : ℕ} [NeZero k] [NeZero n] (p : Profile n)
    (full : ∀ m w, ∃ a : Matching n, IsStable p a ∧ a m = w) :
    ∃ q : Profile (k*n),
      (∀ m w, ∃ a : Matching (k*n), IsStable q a ∧ a m = w) ∧
      (∀ m w, n ≤ (q.manRank m w).val → q.manRank m w = (q.womanRank w m).rev) ∧
      numStableMatchings p ^ k ≤ numStableMatchings q := by
  classical
  let e : (Fin k × Fin n) ≃ Fin (k*n) := finProdFinEquiv
  let f (x y : Fin k × Fin n) := e (y.1-x.1,
    if y.1 = x.1 then p.manRank x.2 y.2 else y.2-x.2)
  let g (x y : Fin k × Fin n) := e (y.1-x.1,
    if y.1 = x.1 then (p.womanRank y.2 x.2).rev else y.2-x.2)
  have hf (x) : Function.Injective (f x) := by
    rintro ⟨a,b⟩ ⟨c,d⟩ h
    have hh := e.injective h
    have hac : a = c := sub_left_inj.mp (congrArg Prod.fst hh)
    subst c
    have he := congrArg Prod.snd hh
    by_cases ha : a = x.1
    · exact Prod.ext rfl ((p.manRank x.2).injective (by simpa [ha] using he))
    · exact Prod.ext rfl (by simpa [ha] using he)
  have hg (y) : Function.Injective (fun x => g x y) := by
    rintro ⟨a,b⟩ ⟨c,d⟩ h
    have hh := e.injective h
    have hac : a = c := sub_right_inj.mp (congrArg Prod.fst hh)
    subst c
    have he := congrArg Prod.snd hh
    by_cases ha : y.1 = a
    · exact Prod.ext rfl ((p.womanRank y.2).injective (Fin.rev_injective (by simpa [ha] using he)))
    · exact Prod.ext rfl (by simpa [ha] using he)
  let perm (h : Fin (k*n) → Fin (k*n)) (hh : Function.Injective h) :=
    Equiv.ofBijective h ((Finite.injective_iff_bijective).mp hh)
  let q : Profile (k*n) :=
    ⟨fun x => perm (f (e.symm x) ∘ e.symm) ((hf _).comp e.symm.injective),
     fun y => (perm ((fun x => g x (e.symm y)) ∘ e.symm)
       ((hg _).comp e.symm.injective)).trans Fin.revPerm⟩
  have hm (x y) : q.manRank (e x) (e y) = f x y := by simp [q, perm]
  have hw (x y) : q.womanRank (e y) (e x) = (g x y).rev := by simp [q, perm]
  have vzero (t : Fin n) : (e (0,t)).val = t.val := by simp [e, finProdFinEquiv]
  have vpos (r : Fin k) (t : Fin n) (hr : r ≠ 0) : n ≤ (e (r,t)).val := by
    have hr' : 1 ≤ r.val := by
      have : r.val ≠ 0 := fun he => hr (Fin.ext he)
      omega
    have hmul := Nat.mul_le_mul_left n hr'
    change n ≤ t.val + n*r.val
    simp only [Nat.mul_one] at hmul
    omega
  have hlow (x y : Fin k × Fin n) (h : y.1 = x.1) :
      (f x y).val = (p.manRank x.2 y.2).val ∧
      (g x y).val = (p.womanRank y.2 x.2).rev.val := by
    simp [f, g, h, vzero]
  have hhigh (x y : Fin k × Fin n) (h : y.1 ≠ x.1) : n ≤ (f x y).val ∧ f x y = g x y := by
    simpa [f, g, h] using vpos (y.1-x.1) (y.2-x.2) (sub_ne_zero.mpr h)
  have hold (u : Fin k → {a : Matching n // IsStable p a}) :
      IsStable q (e.permCongr (Equiv.prodCongrRight fun i => (u i).val)) := by
    let v := Equiv.prodCongrRight fun i => (u i).val
    apply stable_test e q v
    intro x z ha hb
    rw [hm, hm, Fin.lt_def, (hlow x (v x) rfl).1] at ha
    rw [hw, hw, Fin.rev_lt_rev, Fin.lt_def, (hlow z (v z) rfl).2] at hb
    by_cases he : (v z).1 = x.1
    · rw [(hlow x (v z) he).1] at ha
      rw [(hlow x (v z) he).2] at hb
      obtain ⟨i,a⟩ := x
      obtain ⟨j,b⟩ := z
      change j = i at he
      subst j
      change (p.manRank a ((u i).val b)).val < (p.manRank a ((u i).val a)).val at ha
      change (p.womanRank ((u i).val b) b).rev < (p.womanRank ((u i).val b) a).rev at hb
      apply (u i).property a ((u i).val b)
      exact ⟨fun eq => (ne_of_lt ha) (by rw [eq]), ha, by simpa using Fin.rev_lt_rev.mp hb⟩
    · have := (hhigh x (v z) he).1
      have := (p.manRank x.2 (v x).2).isLt
      omega
  refine ⟨q, ?_, ?_, product_count p q e hold⟩
  · intro m w
    obtain ⟨⟨i,a⟩, rfl⟩ := e.surjective m
    obtain ⟨⟨j,b⟩, rfl⟩ := e.surjective w
    by_cases he : j = i
    · subst j
      obtain ⟨u, hu, hval⟩ := full a b
      refine ⟨_, hold (fun _ => ⟨u, hu⟩), ?_⟩
      simp [Equiv.permCongr_apply, hval]
    · let r := j-i
      let d := b-a
      let v := (Equiv.addRight r).prodCongr (Equiv.addRight d)
      have hr : r ≠ 0 := sub_ne_zero.mpr he
      have hval (x : Fin k × Fin n) : f x (v x) = e (r,d) ∧ g x (v x) = e (r,d) := by
        simp [v, f, g, hr]
      refine ⟨e.permCongr v, stable_test e q v ?_, ?_⟩
      · intro x z ha hb
        rw [hm, hm, (hval x).1] at ha
        rw [hw, hw, Fin.rev_lt_rev, (hval z).2] at hb
        by_cases hx : (v z).1 = x.1
        · have hh := (hlow x (v z) hx).2
          have := (p.womanRank (v z).2 x.2).rev.isLt
          have := vpos r d hr
          change (e (r,d)).val < _ at hb
          omega
        · rw [← (hhigh x (v z) hx).2] at hb
          exact (not_lt_of_gt ha) hb
      · simp [Equiv.permCongr_apply, v, r, d]
  · intro m w h
    obtain ⟨x, rfl⟩ := e.surjective m
    obtain ⟨y, rfl⟩ := e.surjective w
    rw [hm] at h
    rw [hm, hw, Fin.rev_rev]
    by_cases he : y.1 = x.1
    · rw [(hlow x y he).1] at h
      exact False.elim ((not_lt_of_ge h) (p.manRank x.2 y.2).isLt)
    · exact (hhigh x y he).2

private theorem transfer {k n : ℕ} (hk : 0 < k) (hn : 0 < n) {a b : ℕ}
    (h : a^k ≤ b) :
    (a : ℝ) ^ (1/(n : ℝ)) ≤ (b : ℝ) ^ (1/((k*n : ℕ) : ℝ)) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hr : (a : ℝ)^k ≤ (b : ℝ) := by exact_mod_cast h
  calc
    (a : ℝ) ^ (1/(n : ℝ)) =
        ((a : ℝ)^k) ^ (1/((k*n : ℕ) : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
      push_cast
      congr 1
      field_simp
    _ ≤ _ := Real.rpow_le_rpow (by positivity) hr (by positivity)

/-- Any finite profile has arbitrarily large extensions attaining all pairs.
Rank complementarity can fail only within a prefix of width twice the
original size, independently of the size of the extension. -/
theorem exists_large_extension {n : ℕ} (hn : 0 < n) (p : Profile n) (N₀ : ℕ) :
    ∃ (N : ℕ) (r : Profile N), N₀ ≤ N ∧ 0 < N ∧
      (∀ m w, ∃ a : Matching N, IsStable r a ∧ a m = w) ∧
      (∀ m w, 2*n ≤ (r.manRank m w).val → r.manRank m w = (r.womanRank w m).rev) ∧
      (numStableMatchings p : ℝ) ^ (1/(n : ℝ)) ≤
        (numStableMatchings r : ℝ) ^ (1/(N : ℝ)) := by
  let _ : NeZero n := ⟨hn.ne'⟩
  obtain ⟨q, hfull, hs⟩ := saturate p
  let k := N₀+1
  have hk : 0 < k := Nat.succ_pos _
  let _ : NeZero k := ⟨hk.ne'⟩
  have hd : 0 < 2*n := by positivity
  let _ : NeZero (2*n) := ⟨hd.ne'⟩
  obtain ⟨r, hf, htail, hc⟩ := replicate_market (k := k) q hfull
  have hlarge : N₀ ≤ k*(2*n) := (Nat.le_succ _).trans (Nat.le_mul_of_pos_right k hd)
  exact ⟨k*(2*n), r, hlarge, Nat.mul_pos hk hd, hf, htail,
    (transfer (by decide : 0 < 2) hn hs).trans (transfer hk hd hc)⟩

/-- Bound for Latin marriage profiles, whose ranks are complementary on every pair. -/
def H1 : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ p : Profile n,
    (∀ m w, p.manRank m w = (p.womanRank w m).rev) →
    (numStableMatchings p : ℝ) ^ (1/(n : ℝ)) ≤
      ⨆ j : ℕ, (irvingLeatherCount j : ℝ) ^ (1/(2 : ℝ)^j)

/-- For a fixed exceptional prefix and all sufficiently large markets attaining
every pair, approximate the normalized count from above by a Latin market,
up to an arbitrarily small additive error. -/
def H2 : Prop :=
  ∀ (d : ℕ) (ε : ℝ), 0 < ε → ∃ N₀ : ℕ, ∀ (N : ℕ), N₀ ≤ N → 0 < N →
    ∀ p : Profile N,
      (∀ m w, ∃ a : Matching N, IsStable p a ∧ a m = w) →
      (∀ m w, d ≤ (p.manRank m w).val → p.manRank m w = (p.womanRank w m).rev) →
      ∃ (l : ℕ) (q : Profile l), 0 < l ∧ (∀ m w, q.manRank m w = (q.womanRank w m).rev) ∧
        (numStableMatchings p : ℝ) ^ (1/(N : ℝ)) ≤
          (numStableMatchings q : ℝ) ^ (1/(l : ℝ)) + ε

theorem main : H1 → H2 → OMA.R_IrvingLeather_irving_leather_growth_rate_R1.H3 := by
  intro latin approx n
  obtain ⟨p, _, hp⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Profile (n+1)))
    Finset.univ_nonempty (fun p => numStableMatchings p)
  change maxStableMatchings (n+1) = numStableMatchings p at hp
  rw [hp]
  have hden : (n : ℝ) + 1 = ((n+1 : ℕ) : ℝ) := by simp
  rw [hden]
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := approx (2*(n+1)) ε hε
  obtain ⟨N, r, hN, hpos, hf, htail, hc⟩ := exists_large_extension (Nat.succ_pos n) p N₀
  obtain ⟨l, q, hl, hlatin, ha⟩ := hN₀ N hN hpos r hf htail
  exact hc.trans (ha.trans (add_le_add (latin l hl q hlatin) le_rfl))

end OMA.R_IrvingLeather_irving_leather_growth_rate_R1_H3_R1
