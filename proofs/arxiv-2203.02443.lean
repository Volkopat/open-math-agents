import OMAStatements.S_arxiv_2203_02443

namespace Arxiv220302443Proof

open OMA.S_arxiv_2203_02443

private def arc (m : ℕ) [NeZero m] (r : ℕ) (k : Fin m) : Finset (Fin m) :=
  (Finset.range r).image (fun i => k + Fin.ofNat m i)

private lemma arc_prod {m : ℕ} [NeZero m] {r : ℕ} (hr : r ≤ m) (k : Fin m) (f : Fin m → ℝ) :
    (∏ i ∈ Finset.range r, f (k + Fin.ofNat m i)) = ∏ x ∈ arc m r k, f x := by
  unfold arc
  symm
  refine Finset.prod_image ?_
  intro i hi j hj hij
  simp only [Finset.mem_coe, Finset.mem_range] at hi hj
  have h1 : Fin.ofNat m i = Fin.ofNat m j := add_left_cancel hij
  have h2 := congrArg Fin.val h1
  simp only [Fin.val_ofNat] at h2
  rw [Nat.mod_eq_of_lt (lt_of_lt_of_le hi hr), Nat.mod_eq_of_lt (lt_of_lt_of_le hj hr)] at h2
  exact h2

private lemma arc_reflect {m : ℕ} [NeZero m] {r : ℕ} (hr1 : 1 ≤ r) (c k : Fin m) :
    arc m r (c - k - Fin.ofNat m (r - 1)) = (arc m r k).image (fun x => c - x) := by
  ext x
  simp only [arc, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    refine ⟨k + Fin.ofNat m (r - 1 - i), ⟨r - 1 - i, by omega, rfl⟩, ?_⟩
    have hsum : Fin.ofNat m (r - 1 - i) + Fin.ofNat m i = Fin.ofNat m (r - 1) := by
      apply Fin.ext
      simp only [Fin.val_add, Fin.val_ofNat]
      rw [Nat.add_mod_mod, Nat.mod_add_mod]
      congr 1
      omega
    calc
      c - (k + Fin.ofNat m (r - 1 - i))
          = c - k - Fin.ofNat m (r - 1 - i) := by abel
      _ = c - k - (Fin.ofNat m (r - 1) - Fin.ofNat m i) := by
            congr 1
            exact eq_sub_of_add_eq hsum
      _ = c - k - Fin.ofNat m (r - 1) + Fin.ofNat m i := by abel
  · rintro ⟨_, ⟨j, hj, rfl⟩, rfl⟩
    refine ⟨r - 1 - j, by omega, ?_⟩
    have hsum : Fin.ofNat m j + Fin.ofNat m (r - 1 - j) = Fin.ofNat m (r - 1) := by
      apply Fin.ext
      simp only [Fin.val_add, Fin.val_ofNat]
      rw [Nat.add_mod_mod, Nat.mod_add_mod]
      congr 1
      omega
    calc
      c - k - Fin.ofNat m (r - 1) + Fin.ofNat m (r - 1 - j)
          = c - k - (Fin.ofNat m j + Fin.ofNat m (r - 1 - j)) + Fin.ofNat m (r - 1 - j) := by
              rw [hsum]
      _ = c - (k + Fin.ofNat m j) := by abel

private def polarizeSwap {m : ℕ} [NeZero m] (c : Fin m) (Hp Hm : Finset (Fin m))
    (τ : Fin m → Fin m) (x : Fin m) : Fin m :=
  if (x ∈ Hp ∧ τ (c - x) < τ x) ∨ (x ∈ Hm ∧ τ x < τ (c - x)) then c - x else x

private lemma polarizeSwap_involutive {m : ℕ} [NeZero m] (c : Fin m) (Hp Hm : Finset (Fin m))
    (_hdisj : Disjoint Hp Hm) (hmap : ∀ x, x ∈ Hp ↔ c - x ∈ Hm) (τ : Fin m → Fin m) :
    Function.Involutive (polarizeSwap c Hp Hm τ) := by
  have hmap' : ∀ x, x ∈ Hm ↔ c - x ∈ Hp := fun x => by
    have := hmap (c - x)
    simpa [sub_sub_cancel] using this.symm
  intro x
  unfold polarizeSwap
  by_cases h1 : (x ∈ Hp ∧ τ (c - x) < τ x) ∨ (x ∈ Hm ∧ τ x < τ (c - x))
  · rw [if_pos h1]
    have h2 : (c - x ∈ Hp ∧ τ (c - (c - x)) < τ (c - x)) ∨
        (c - x ∈ Hm ∧ τ (c - x) < τ (c - (c - x))) := by
      rw [sub_sub_cancel]
      rcases h1 with ⟨hxp, hlt⟩ | ⟨hxm, hlt⟩
      · exact Or.inr ⟨(hmap x).mp hxp, hlt⟩
      · exact Or.inl ⟨(hmap' x).mp hxm, hlt⟩
    rw [if_pos h2, sub_sub_cancel]
  · rw [if_neg h1, if_neg h1]

private def polarizePerm {m : ℕ} [NeZero m] (c : Fin m) (Hp Hm : Finset (Fin m))
    (hdisj : Disjoint Hp Hm) (hmap : ∀ x, x ∈ Hp ↔ c - x ∈ Hm)
    (τ : Equiv.Perm (Fin m)) : Equiv.Perm (Fin m) :=
  (polarizeSwap_involutive c Hp Hm hdisj hmap τ).toPerm.trans τ

private lemma polarizePerm_apply {m : ℕ} [NeZero m] (c : Fin m) (Hp Hm : Finset (Fin m))
    (hdisj : Disjoint Hp Hm) (hmap : ∀ x, x ∈ Hp ↔ c - x ∈ Hm)
    (τ : Equiv.Perm (Fin m)) (x : Fin m) :
    polarizePerm c Hp Hm hdisj hmap τ x =
      if x ∈ Hp then min (τ x) (τ (c - x))
      else if x ∈ Hm then max (τ x) (τ (c - x))
      else τ x := by
  change τ (polarizeSwap c Hp Hm τ x) = _
  unfold polarizeSwap
  by_cases hxp : x ∈ Hp
  · have hxm : x ∉ Hm := Finset.disjoint_left.mp hdisj hxp
    rw [if_pos hxp]
    by_cases hlt : τ (c - x) < τ x
    · rw [if_pos (Or.inl ⟨hxp, hlt⟩), min_eq_right hlt.le]
    · have hc : ¬ ((x ∈ Hp ∧ τ (c - x) < τ x) ∨ (x ∈ Hm ∧ τ x < τ (c - x))) := by
        simp [hxp, hxm, hlt]
      rw [if_neg hc, min_eq_left (le_of_not_gt hlt)]
  · by_cases hxm : x ∈ Hm
    · rw [if_neg hxp, if_pos hxm]
      by_cases hlt : τ x < τ (c - x)
      · rw [if_pos (Or.inr ⟨hxm, hlt⟩), max_eq_right hlt.le]
      · have hc : ¬ ((x ∈ Hp ∧ τ (c - x) < τ x) ∨ (x ∈ Hm ∧ τ x < τ (c - x))) := by
          simp [hxp, hxm, hlt]
        rw [if_neg hc, max_eq_left (le_of_not_gt hlt)]
    · rw [if_neg hxp, if_neg hxm, if_neg (by simp [hxp, hxm])]

private lemma prod_max_min_ge {α : Type*} (A : Finset α) (u v : α → ℝ)
    (hu : ∀ x ∈ A, 0 < u x) (hv : ∀ x ∈ A, 0 < v x) :
    (∏ x ∈ A, u x) + (∏ x ∈ A, v x) ≤
      (∏ x ∈ A, max (u x) (v x)) + (∏ x ∈ A, min (u x) (v x)) := by
  set U := ∏ x ∈ A, u x
  set V := ∏ x ∈ A, v x
  set M := ∏ x ∈ A, max (u x) (v x)
  set N := ∏ x ∈ A, min (u x) (v x)
  have hMpos : 0 < M := Finset.prod_pos fun x hx => lt_of_lt_of_le (hu x hx) (le_max_left _ _)
  have hUM : U ≤ M := Finset.prod_le_prod (fun x hx => (hu x hx).le) (fun x _ => le_max_left _ _)
  have hVM : V ≤ M := Finset.prod_le_prod (fun x hx => (hv x hx).le) (fun x _ => le_max_right _ _)
  have hUV : U * V = M * N := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun x _ => ?_
    rcases le_total (u x) (v x) with h | h
    · rw [max_eq_right h, min_eq_left h, mul_comm]
    · rw [max_eq_left h, min_eq_right h]
  have hsq : 0 ≤ (M - U) * (M - V) := mul_nonneg (sub_nonneg.mpr hUM) (sub_nonneg.mpr hVM)
  nlinarith

private lemma cyclicProduct_le_polarize {m : ℕ} [NeZero m] (a : Fin m → ℝ)
    (ha_pos : ∀ j, 0 < a j) (ha_anti : Antitone a)
    {r : ℕ} (hr1 : 1 ≤ r) (hrm : r ≤ m)
    (c : Fin m) (Hp Hm : Finset (Fin m))
    (hdisj : Disjoint Hp Hm) (hmap : ∀ x, x ∈ Hp ↔ c - x ∈ Hm)
    (hsep : ∀ k : Fin m,
      let I := arc m r k
      let I' := I.image (fun x => c - x)
      I \ I' ⊆ Hp ∨ I \ I' ⊆ Hm)
    (τ : Equiv.Perm (Fin m)) :
    cyclicProduct m r τ a ≤ cyclicProduct m r (polarizePerm c Hp Hm hdisj hmap τ) a := by
  set τ' := polarizePerm c Hp Hm hdisj hmap τ
  set sw := polarizeSwap c Hp Hm τ
  have hsw_inv : Function.Involutive sw := polarizeSwap_involutive c Hp Hm hdisj hmap τ
  have hpair : ∀ k : Fin m,
      (∏ x ∈ arc m r k, a (τ x)) + (∏ x ∈ (arc m r k).image (fun x => c - x), a (τ x)) ≤
      (∏ x ∈ arc m r k, a (τ' x)) + (∏ x ∈ (arc m r k).image (fun x => c - x), a (τ' x)) := by
    intro k
    set I := arc m r k
    set I' := I.image (fun x => c - x)
    set S := I ∩ I'
    set A := I \ I'
    set B := I' \ I
    have hI_split : S ∪ A = I := by
      ext x; simp only [S, A, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]; tauto
    have hI_disj : Disjoint S A := by
      rw [Finset.disjoint_left]
      intro x h1 h2
      simp only [S, A, Finset.mem_inter, Finset.mem_sdiff] at h1 h2
      exact h2.2 h1.2
    have hI'_split : S ∪ B = I' := by
      ext x; simp only [S, B, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]; tauto
    have hI'_disj : Disjoint S B := by
      rw [Finset.disjoint_left]
      intro x h1 h2
      simp only [S, B, Finset.mem_inter, Finset.mem_sdiff] at h1 h2
      exact h2.2 h1.1
    have hS_ref : ∀ x ∈ S, c - x ∈ S := by
      intro x hx
      rw [Finset.mem_inter] at hx ⊢
      rcases Finset.mem_image.mp hx.2 with ⟨y, hy, hyx⟩
      have hcy : c - x = y := by rw [← hyx, sub_sub_cancel]
      exact ⟨hcy ▸ hy, Finset.mem_image.mpr ⟨x, hx.1, rfl⟩⟩
    have hS_prod : (∏ x ∈ S, a (τ' x)) = ∏ x ∈ S, a (τ x) := by
      refine Finset.prod_bij (fun x _ => sw x) ?_ ?_ ?_ ?_
      · intro x hx
        unfold sw polarizeSwap
        split_ifs
        · exact hS_ref x hx
        · exact hx
      · intro x₁ _ x₂ _ h
        exact hsw_inv.injective h
      · intro y hy
        refine ⟨sw y, ?_, hsw_inv y⟩
        unfold sw polarizeSwap
        split_ifs
        · exact hS_ref y hy
        · exact hy
      · intro x _
        rfl
    have hB_eq : B = A.image (fun x => c - x) := by
      ext y
      simp only [B, A, I', Finset.mem_sdiff, Finset.mem_image]
      constructor
      · rintro ⟨⟨x, hxI, rfl⟩, hnot⟩
        refine ⟨x, ⟨hxI, ?_⟩, rfl⟩
        rintro ⟨z, hzI, hzx⟩
        have hcz : c - x = z := by rw [← hzx, sub_sub_cancel]
        exact hnot (hcz ▸ hzI)
      · rintro ⟨x, ⟨hxI, hxnot⟩, rfl⟩
        refine ⟨⟨x, hxI, rfl⟩, ?_⟩
        intro hcxI
        exact hxnot ⟨c - x, hcxI, sub_sub_cancel c x⟩
    have hprod_B : ∀ f : Fin m → ℝ, (∏ y ∈ B, f y) = ∏ x ∈ A, f (c - x) := by
      intro f
      rw [hB_eq]
      exact Finset.prod_image fun x₁ _ x₂ _ h => by
        have := congrArg (fun z => c - z) h
        simpa [sub_sub_cancel] using this
    have hAB_le : (∏ x ∈ A, a (τ x)) + (∏ y ∈ B, a (τ y)) ≤
        (∏ x ∈ A, a (τ' x)) + (∏ y ∈ B, a (τ' y)) := by
      rw [hprod_B (fun y => a (τ y)), hprod_B (fun y => a (τ' y))]
      rcases hsep k with hAp | hAm
      · have h1 : (∏ x ∈ A, a (τ' x)) = ∏ x ∈ A, max (a (τ x)) (a (τ (c - x))) := by
          refine Finset.prod_congr rfl fun x hx => ?_
          have hxp : x ∈ Hp := hAp hx
          have hτ' := polarizePerm_apply c Hp Hm hdisj hmap τ x
          change τ' x = _ at hτ'
          rw [hτ', if_pos hxp]
          exact ha_anti.map_min
        have h2 : (∏ x ∈ A, a (τ' (c - x))) = ∏ x ∈ A, min (a (τ x)) (a (τ (c - x))) := by
          refine Finset.prod_congr rfl fun x hx => ?_
          have hxp : x ∈ Hp := hAp hx
          have hcxm : c - x ∈ Hm := (hmap x).mp hxp
          have hcxnp : c - x ∉ Hp := Finset.disjoint_right.mp hdisj hcxm
          have hτ' := polarizePerm_apply c Hp Hm hdisj hmap τ (c - x)
          change τ' (c - x) = _ at hτ'
          rw [hτ', if_neg hcxnp, if_pos hcxm, sub_sub_cancel, max_comm]
          exact ha_anti.map_max
        rw [h1, h2]
        exact prod_max_min_ge A (fun x => a (τ x)) (fun x => a (τ (c - x)))
          (fun x _ => ha_pos _) (fun x _ => ha_pos _)
      · have h1 : (∏ x ∈ A, a (τ' x)) = ∏ x ∈ A, min (a (τ x)) (a (τ (c - x))) := by
          refine Finset.prod_congr rfl fun x hx => ?_
          have hxm : x ∈ Hm := hAm hx
          have hxnp : x ∉ Hp := Finset.disjoint_right.mp hdisj hxm
          have hτ' := polarizePerm_apply c Hp Hm hdisj hmap τ x
          change τ' x = _ at hτ'
          rw [hτ', if_neg hxnp, if_pos hxm]
          exact ha_anti.map_max
        have h2 : (∏ x ∈ A, a (τ' (c - x))) = ∏ x ∈ A, max (a (τ x)) (a (τ (c - x))) := by
          refine Finset.prod_congr rfl fun x hx => ?_
          have hxm : x ∈ Hm := hAm hx
          have hcxp : c - x ∈ Hp := by
            have h := (hmap (c - x)).mpr
            rw [sub_sub_cancel] at h
            exact h hxm
          have hτ' := polarizePerm_apply c Hp Hm hdisj hmap τ (c - x)
          change τ' (c - x) = _ at hτ'
          rw [hτ', if_pos hcxp, sub_sub_cancel, min_comm]
          exact ha_anti.map_min
        rw [h1, h2, add_comm (∏ x ∈ A, min _ _)]
        exact prod_max_min_ge A (fun x => a (τ x)) (fun x => a (τ (c - x)))
          (fun x _ => ha_pos _) (fun x _ => ha_pos _)
    have hS_pos : 0 ≤ ∏ x ∈ S, a (τ x) := Finset.prod_nonneg fun x _ => (ha_pos _).le
    rw [← hI_split, ← hI'_split, Finset.prod_union hI_disj, Finset.prod_union hI'_disj,
      Finset.prod_union hI_disj, Finset.prod_union hI'_disj, hS_prod]
    nlinarith
  have hsum_ref : ∀ f : Fin m → ℝ,
      (∑ k : Fin m, ∏ x ∈ (arc m r k).image (fun x => c - x), f x) =
      ∑ k : Fin m, ∏ x ∈ arc m r k, f x := by
    intro f
    have heq : ∀ k : Fin m,
        (∏ x ∈ (arc m r k).image (fun x => c - x), f x) =
        ∏ x ∈ arc m r (c - k - Fin.ofNat m (r - 1)), f x := fun k => by
      rw [arc_reflect hr1 c k]
    simp_rw [heq]
    let e : Equiv.Perm (Fin m) :=
      { toFun := fun k => c - k - Fin.ofNat m (r - 1)
        invFun := fun k => c - k - Fin.ofNat m (r - 1)
        left_inv := fun k => by dsimp only; rw [sub_sub c k, sub_sub_cancel, add_sub_cancel_right]
        right_inv := fun k => by dsimp only; rw [sub_sub c k, sub_sub_cancel, add_sub_cancel_right] }
    exact Equiv.sum_comp e (fun k => ∏ x ∈ arc m r k, f x)
  have hcp_eq : ∀ σ : Equiv.Perm (Fin m),
      cyclicProduct m r σ a = ∑ k : Fin m, ∏ x ∈ arc m r k, a (σ x) := by
    intro σ
    unfold cyclicProduct
    refine Finset.sum_congr rfl fun k _ => arc_prod hrm k (fun x => a (σ x))
  have hsum := Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) => hpair k
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hsum_ref, hsum_ref] at hsum
  rw [hcp_eq τ, hcp_eq τ']
  linarith

private lemma mem_arc_iff_nonwrap {m : ℕ} [NeZero m] {r : ℕ} (k x : Fin m)
    (h : k.val + r ≤ m) :
    x ∈ arc m r k ↔ k.val ≤ x.val ∧ x.val < k.val + r := by
  simp only [arc, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    have hv : (k + Fin.ofNat m i).val = k.val + i := by
      simp only [Fin.val_add, Fin.val_ofNat]
      rw [Nat.add_mod_mod, Nat.mod_eq_of_lt (by omega)]
    rw [hv]
    omega
  · rintro ⟨h1, h2⟩
    refine ⟨x.val - k.val, by omega, ?_⟩
    apply Fin.ext
    simp only [Fin.val_add, Fin.val_ofNat]
    rw [Nat.add_mod_mod, Nat.mod_eq_of_lt (by omega)]
    omega

private lemma mem_arc_iff_wrap {m : ℕ} [NeZero m] {r : ℕ} (hrm : r ≤ m) (k x : Fin m)
    (h : m < k.val + r) :
    x ∈ arc m r k ↔ k.val ≤ x.val ∨ x.val < k.val + r - m := by
  simp only [arc, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    have hv : (k + Fin.ofNat m i).val = (k.val + i) % m := by
      simp only [Fin.val_add, Fin.val_ofNat]
      rw [Nat.add_mod_mod]
    rw [hv]
    by_cases hlt : k.val + i < m
    · rw [Nat.mod_eq_of_lt hlt]; left; omega
    · have hsub : (k.val + i) % m = k.val + i - m := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      rw [hsub]; right; omega
  · rintro (h1 | h2)
    · refine ⟨x.val - k.val, by omega, ?_⟩
      apply Fin.ext
      simp only [Fin.val_add, Fin.val_ofNat]
      rw [Nat.add_mod_mod, Nat.mod_eq_of_lt (by omega)]
      omega
    · refine ⟨m - k.val + x.val, by omega, ?_⟩
      apply Fin.ext
      simp only [Fin.val_add, Fin.val_ofNat]
      rw [Nat.add_mod_mod]
      have heq : k.val + (m - k.val + x.val) = m + x.val := by omega
      rw [heq, Nat.add_mod_left, Nat.mod_eq_of_lt x.isLt]

private lemma sep_of_interval {m : ℕ} [NeZero m] (c : Fin m) (Hp Hm : Finset (Fin m))
    (_hmap : ∀ x, x ∈ Hp ↔ c - x ∈ Hm) (hfix : ∀ x, x ∉ Hp → x ∉ Hm → c - x = x)
    (I : Finset (Fin m))
    (hno : ¬ (∃ u ∈ I, c - u ∉ I ∧ u ∈ Hp) ∨ ¬ (∃ v ∈ I, c - v ∉ I ∧ v ∈ Hm)) :
    I \ I.image (fun x => c - x) ⊆ Hp ∨ I \ I.image (fun x => c - x) ⊆ Hm := by
  have hmem_sdiff : ∀ x, x ∈ I \ I.image (fun y => c - y) ↔ x ∈ I ∧ c - x ∉ I := by
    intro x
    simp only [Finset.mem_sdiff, Finset.mem_image]
    constructor
    · rintro ⟨hx, hnot⟩
      exact ⟨hx, fun hcx => hnot ⟨c - x, hcx, sub_sub_cancel c x⟩⟩
    · rintro ⟨hx, hcx⟩
      refine ⟨hx, ?_⟩
      rintro ⟨y, hy, hyx⟩
      have : c - x = y := by rw [← hyx, sub_sub_cancel]
      exact hcx (this ▸ hy)
  rcases hno with hnoP | hnoM
  · right
    intro x hx
    rw [hmem_sdiff] at hx
    by_contra hxm
    by_cases hxp : x ∈ Hp
    · exact hnoP ⟨x, hx.1, hx.2, hxp⟩
    · exact hx.2 ((hfix x hxp hxm).symm ▸ hx.1)
  · left
    intro x hx
    rw [hmem_sdiff] at hx
    by_contra hxp
    by_cases hxm : x ∈ Hm
    · exact hnoM ⟨x, hx.1, hx.2, hxm⟩
    · exact hx.2 ((hfix x hxp hxm).symm ▸ hx.1)

private def H1p (m : ℕ) [NeZero m] : Finset (Fin m) :=
  Finset.univ.filter (fun x : Fin m => x.val < m / 2)

private def H1m (m : ℕ) [NeZero m] : Finset (Fin m) :=
  Finset.univ.filter (fun x : Fin m => m - m / 2 ≤ x.val)

private lemma neg_one_sub_val {m : ℕ} [NeZero m] (x : Fin m) :
    ((-1 : Fin m) - x).val = m - 1 - x.val := by
  have hm : 0 < m := NeZero.pos m
  have hadd : (⟨m - 1 - x.val, by omega⟩ : Fin m) + x + 1 = 0 := by
    apply Fin.ext
    simp only [Fin.val_add, Fin.val_one', Fin.val_zero]
    rw [Nat.mod_add_mod, Nat.add_mod_mod]
    have heq : m - 1 - x.val + x.val + 1 = m := by omega
    rw [heq, Nat.mod_self]
  have heq : (-1 : Fin m) - x = ⟨m - 1 - x.val, by omega⟩ := by
    have h1 : (-1 : Fin m) - x + (⟨m - 1 - x.val, by omega⟩ + x + 1) =
        ⟨m - 1 - x.val, by omega⟩ := by abel
    rw [hadd, add_zero] at h1
    exact h1
  rw [heq]

private lemma H1_disj (m : ℕ) [NeZero m] : Disjoint (H1p m) (H1m m) := by
  rw [Finset.disjoint_left]
  intro x hxp hxm
  simp only [H1p, H1m, Finset.mem_filter, Finset.mem_univ, true_and] at hxp hxm
  omega

private lemma H1_map (m : ℕ) [NeZero m] (x : Fin m) : x ∈ H1p m ↔ (-1 : Fin m) - x ∈ H1m m := by
  simp only [H1p, H1m, Finset.mem_filter, Finset.mem_univ, true_and, neg_one_sub_val]
  omega

private lemma H1_fix (m : ℕ) [NeZero m] (x : Fin m) (hp : x ∉ H1p m) (hm : x ∉ H1m m) :
    (-1 : Fin m) - x = x := by
  simp only [H1p, H1m, Finset.mem_filter, Finset.mem_univ, true_and] at hp hm
  apply Fin.ext
  rw [neg_one_sub_val]
  omega

private lemma H1_sep {m : ℕ} [NeZero m] {r : ℕ} (hrm : r ≤ m) (k : Fin m) :
    arc m r k \ (arc m r k).image (fun x => (-1 : Fin m) - x) ⊆ H1p m ∨
    arc m r k \ (arc m r k).image (fun x => (-1 : Fin m) - x) ⊆ H1m m := by
  refine sep_of_interval (-1 : Fin m) (H1p m) (H1m m) (H1_map m) (H1_fix m) (arc m r k) ?_
  by_contra hboth
  push Not at hboth
  rcases hboth with ⟨⟨u, huI, hunI, hup⟩, ⟨v, hvI, hvnI, hvm⟩⟩
  simp only [H1p, H1m, Finset.mem_filter, Finset.mem_univ, true_and] at hup hvm
  by_cases hwrap : k.val + r ≤ m
  · rw [mem_arc_iff_nonwrap k u hwrap] at huI
    rw [mem_arc_iff_nonwrap k (-1 - u) hwrap, neg_one_sub_val] at hunI
    rw [mem_arc_iff_nonwrap k v hwrap] at hvI
    rw [mem_arc_iff_nonwrap k (-1 - v) hwrap, neg_one_sub_val] at hvnI
    omega
  · push Not at hwrap
    rw [mem_arc_iff_wrap hrm k u hwrap] at huI
    rw [mem_arc_iff_wrap hrm k (-1 - u) hwrap, neg_one_sub_val] at hunI
    rw [mem_arc_iff_wrap hrm k v hwrap] at hvI
    rw [mem_arc_iff_wrap hrm k (-1 - v) hwrap, neg_one_sub_val] at hvnI
    omega

private def H2p (m : ℕ) [NeZero m] : Finset (Fin m) :=
  Finset.univ.filter (fun x : Fin m => m - (m - 1) / 2 ≤ x.val)

private def H2m (m : ℕ) [NeZero m] : Finset (Fin m) :=
  Finset.univ.filter (fun x : Fin m => 1 ≤ x.val ∧ x.val ≤ (m - 1) / 2)

private lemma zero_sub_val {m : ℕ} [NeZero m] (x : Fin m) :
    ((0 : Fin m) - x).val = if x.val = 0 then 0 else m - x.val := by
  rw [zero_sub]
  by_cases hx0 : x.val = 0
  · have hx : x = 0 := Fin.ext hx0
    subst hx
    simp
  · rw [if_neg hx0, Fin.val_neg', Nat.mod_eq_of_lt (by omega)]

private lemma H2_disj (m : ℕ) [NeZero m] : Disjoint (H2p m) (H2m m) := by
  rw [Finset.disjoint_left]
  intro x hxp hxm
  simp only [H2p, H2m, Finset.mem_filter, Finset.mem_univ, true_and] at hxp hxm
  omega

private lemma H2_map (m : ℕ) [NeZero m] (x : Fin m) : x ∈ H2p m ↔ (0 : Fin m) - x ∈ H2m m := by
  simp only [H2p, H2m, Finset.mem_filter, Finset.mem_univ, true_and, zero_sub_val]
  split_ifs <;> omega

private lemma H2_fix (m : ℕ) [NeZero m] (x : Fin m) (hp : x ∉ H2p m) (hm : x ∉ H2m m) :
    (0 : Fin m) - x = x := by
  simp only [H2p, H2m, Finset.mem_filter, Finset.mem_univ, true_and] at hp hm
  apply Fin.ext
  rw [zero_sub_val]
  split_ifs <;> omega

private lemma H2_sep {m : ℕ} [NeZero m] {r : ℕ} (hrm : r ≤ m) (k : Fin m) :
    arc m r k \ (arc m r k).image (fun x => (0 : Fin m) - x) ⊆ H2p m ∨
    arc m r k \ (arc m r k).image (fun x => (0 : Fin m) - x) ⊆ H2m m := by
  refine sep_of_interval (0 : Fin m) (H2p m) (H2m m) (H2_map m) (H2_fix m) (arc m r k) ?_
  by_contra hboth
  push Not at hboth
  rcases hboth with ⟨⟨u, huI, hunI, hup⟩, ⟨v, hvI, hvnI, hvm⟩⟩
  simp only [H2p, H2m, Finset.mem_filter, Finset.mem_univ, true_and] at hup hvm
  have hu0 : u.val ≠ 0 := by omega
  have hv0 : v.val ≠ 0 := by omega
  by_cases hwrap : k.val + r ≤ m
  · rw [mem_arc_iff_nonwrap k u hwrap] at huI
    rw [mem_arc_iff_nonwrap k (0 - u) hwrap, zero_sub_val, if_neg hu0] at hunI
    rw [mem_arc_iff_nonwrap k v hwrap] at hvI
    rw [mem_arc_iff_nonwrap k (0 - v) hwrap, zero_sub_val, if_neg hv0] at hvnI
    omega
  · push Not at hwrap
    rw [mem_arc_iff_wrap hrm k u hwrap] at huI
    rw [mem_arc_iff_wrap hrm k (0 - u) hwrap, zero_sub_val, if_neg hu0] at hunI
    rw [mem_arc_iff_wrap hrm k v hwrap] at hvI
    rw [mem_arc_iff_wrap hrm k (0 - v) hwrap, zero_sub_val, if_neg hv0] at hvnI
    omega

private def greedyInv (m : ℕ) [NeZero m] (t : Fin m) : Fin m :=
  if t.val % 2 = 0 then ⟨t.val / 2, by omega⟩
  else ⟨m - 1 - t.val / 2, by omega⟩

private lemma greedy_greedyInv (m : ℕ) [NeZero m] (t : Fin m) :
    greedy m (greedyInv m t) = t := by
  apply Fin.ext
  unfold greedy greedyInv
  split_ifs with h0 h1 h2 h3 h4
  all_goals simp only [Fin.val_ofNat] at *
  all_goals try rw [Nat.mod_eq_of_lt (by omega)]
  all_goals omega

private lemma greedyInv_greedy (m : ℕ) [NeZero m] (j : Fin m) :
    greedyInv m (greedy m j) = j := by
  apply Fin.ext
  unfold greedy greedyInv
  by_cases h1 : j.val < m / 2
  · have hlt : 2 * j.val < m := by omega
    have hmod : 2 * j.val % 2 = 0 := by omega
    simp only [if_pos h1, Fin.val_ofNat, Nat.mod_eq_of_lt hlt, if_pos hmod]
    omega
  · by_cases h2 : m - m / 2 ≤ j.val
    · have hlt : 2 * (m - 1 - j.val) + 1 < m := by omega
      have hmod : ¬ (2 * (m - 1 - j.val) + 1) % 2 = 0 := by omega
      simp only [if_neg h1, if_pos h2, Fin.val_ofNat, Nat.mod_eq_of_lt hlt, if_neg hmod]
      omega
    · have hlt : m - 1 < m := by omega
      have hmod : (m - 1) % 2 = 0 := by omega
      simp only [if_neg h1, if_neg h2, Fin.val_ofNat, Nat.mod_eq_of_lt hlt, if_pos hmod]
      omega

private def invCount {m : ℕ} [NeZero m] (f : Fin m → Fin m) : ℕ :=
  ((Finset.univ : Finset (Fin m × Fin m)).filter (fun p => p.1 < p.2 ∧ f p.2 < f p.1)).card

private lemma invCount_zero_strictMono {m : ℕ} [NeZero m] (f : Equiv.Perm (Fin m))
    (h0 : invCount f = 0) : StrictMono f := by
  intro p q hpq
  have hnot : (p, q) ∉ (Finset.univ : Finset (Fin m × Fin m)).filter
      (fun x => x.1 < x.2 ∧ f x.2 < f x.1) := by
    rw [Finset.card_eq_zero.mp h0]
    exact Finset.notMem_empty _
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_lt] at hnot
  have hle : f p ≤ f q := hnot hpq
  exact lt_of_le_of_ne hle (fun h => ne_of_lt hpq (f.injective h))

private lemma strictMono_perm_eq_id {m : ℕ} [NeZero m] (f : Equiv.Perm (Fin m))
    (hf : StrictMono f) : ∀ t : Fin m, f t = t := by
  have hge : ∀ t : Fin m, t ≤ f t := fun t => by
    obtain ⟨n, hn⟩ := t
    induction n with
    | zero => exact Fin.zero_le _
    | succ n ih =>
        have hlt : f ⟨n, by omega⟩ < f ⟨n + 1, hn⟩ := hf (by simp [Fin.lt_def])
        have hle : (⟨n, by omega⟩ : Fin m) ≤ f ⟨n, by omega⟩ := ih (by omega)
        change n + 1 ≤ (f ⟨n + 1, hn⟩).val
        have h1 : n ≤ (f ⟨n, by omega⟩).val := hle
        have h2 : (f ⟨n, by omega⟩).val < (f ⟨n + 1, hn⟩).val := hlt
        omega
  have hinv_mono : StrictMono f.symm := by
    intro a b hab
    by_contra hle
    push Not at hle
    have := hf.monotone hle
    simp only [Equiv.apply_symm_apply] at this
    exact not_lt_of_ge this hab
  have hle : ∀ t : Fin m, f t ≤ t := fun t => by
    have := hge (f t)
    -- use same argument on f.symm
    have hge_symm : ∀ s : Fin m, s ≤ f.symm s := fun s => by
      obtain ⟨n, hn⟩ := s
      induction n with
      | zero => exact Fin.zero_le _
      | succ n ih =>
          have hlt : f.symm ⟨n, by omega⟩ < f.symm ⟨n + 1, hn⟩ := hinv_mono (by simp [Fin.lt_def])
          have hle' : (⟨n, by omega⟩ : Fin m) ≤ f.symm ⟨n, by omega⟩ := ih (by omega)
          change n + 1 ≤ (f.symm ⟨n + 1, hn⟩).val
          have h1 : n ≤ (f.symm ⟨n, by omega⟩).val := hle'
          have h2 : (f.symm ⟨n, by omega⟩).val < (f.symm ⟨n + 1, hn⟩).val := hlt
          omega
    have := hge_symm (f t)
    simpa using this
  intro t
  exact le_antisymm (hle t) (hge t)

private lemma exists_adj_inv {m : ℕ} [NeZero m] (f : Equiv.Perm (Fin m)) (hpos : 0 < invCount f) :
    ∃ p : ℕ, ∃ hp : p + 1 < m, f ⟨p + 1, hp⟩ < f ⟨p, by omega⟩ := by
  by_contra hno
  push Not at hno
  have hmono : ∀ a b : Fin m, a ≤ b → f a ≤ f b := by
    intro a b hab
    obtain ⟨a, ha⟩ := a
    obtain ⟨b, hb⟩ := b
    change a ≤ b at hab
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
    clear hab
    induction d with
    | zero => exact le_rfl
    | succ d ih =>
        have hstep := hno (a + d) (by omega)
        exact le_trans (ih (by omega)) hstep
  have h0 : invCount f = 0 := by
    rw [invCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro p _
    rintro ⟨h1, h2⟩
    exact not_lt_of_ge (hmono p.1 p.2 h1.le) h2
  omega

private lemma invCount_brick_lt {m : ℕ} [NeZero m] (f : Fin m → Fin m)
    (b : ℕ) (σ : Fin m → Fin m) (hσ_inv : Function.Involutive σ)
    (hσ_move : ∀ t : Fin m, σ t = t ∨
      (t.val % 2 = b ∧ (σ t).val = t.val + 1) ∨
      (t.val % 2 ≠ b ∧ (σ t).val + 1 = t.val))
    (hσ_sort : ∀ t : Fin m, ∀ ht : t.val + 1 < m, t.val % 2 = b →
      f (σ t) ≤ f (σ ⟨t.val + 1, ht⟩))
    (p : ℕ) (hp : p + 1 < m) (hpinv : f ⟨p + 1, hp⟩ < f ⟨p, by omega⟩)
    (hσp : σ ⟨p, by omega⟩ = ⟨p + 1, hp⟩) :
    invCount (f ∘ σ) < invCount f := by
  set S' := (Finset.univ : Finset (Fin m × Fin m)).filter
    (fun q => q.1 < q.2 ∧ f (σ q.2) < f (σ q.1))
  set S := (Finset.univ : Finset (Fin m × Fin m)).filter
    (fun q => q.1 < q.2 ∧ f q.2 < f q.1)
  set pq : Fin m × Fin m := (⟨p, by omega⟩, ⟨p + 1, hp⟩)
  have hpq_mem : pq ∈ S := by
    simp only [S, pq, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨by simp [Fin.lt_def], hpinv⟩
  have hle : S'.card ≤ (S.erase pq).card := by
    refine Finset.card_le_card_of_injOn (fun q => (σ q.1, σ q.2)) ?_ ?_
    · intro q hq
      simp only [Finset.mem_coe, S', Finset.mem_filter, Finset.mem_univ, true_and] at hq
      rcases hq with ⟨h12, hf12⟩
      have hσ_lt : σ q.1 < σ q.2 := by
        by_contra hnot
        have hge : (σ q.2).val ≤ (σ q.1).val := by
          change ¬ (σ q.1).val < (σ q.2).val at hnot
          omega
        have hne : σ q.1 ≠ σ q.2 := fun h => ne_of_lt h12 (hσ_inv.injective h)
        have hlt_val : (σ q.2).val < (σ q.1).val := by
          have : (σ q.1).val ≠ (σ q.2).val := fun h => hne (Fin.ext h)
          omega
        have hm1 := hσ_move q.1
        have hm2 := hσ_move q.2
        have hu1 : (σ q.1).val ≤ q.1.val + 1 := by
          rcases hm1 with h | ⟨_, h⟩ | ⟨_, h⟩ <;> [rw [h]; skip; skip] <;> omega
        have hv2 : q.2.val ≤ (σ q.2).val + 1 := by
          rcases hm2 with h | ⟨_, h⟩ | ⟨_, h⟩ <;> [rw [h]; skip; skip] <;> omega
        have hq12 : q.1.val < q.2.val := h12
        have hval_eq : q.2.val = q.1.val + 1 := by omega
        have hσ1_val : (σ q.1).val = q.1.val + 1 := by omega
        have hq1_b : q.1.val % 2 = b := by
          rcases hm1 with h | ⟨hb, _⟩ | ⟨_, h⟩
          · rw [h] at hσ1_val; omega
          · exact hb
          · omega
        have hq2_eq : q.2 = ⟨q.1.val + 1, by omega⟩ := Fin.ext hval_eq
        have hord := hσ_sort q.1 (by omega) hq1_b
        rw [← hq2_eq] at hord
        exact not_lt_of_ge hord hf12
      rw [Finset.mem_coe, Finset.mem_erase]
      refine ⟨?_, ?_⟩
      · intro heq
        have h1 : σ q.1 = ⟨p, by omega⟩ := congrArg Prod.fst heq
        have h2 : σ q.2 = ⟨p + 1, hp⟩ := congrArg Prod.snd heq
        have hq1 : q.1 = ⟨p + 1, hp⟩ := by
          have := congrArg σ h1
          rw [hσ_inv, hσp] at this
          exact this
        have hq2 : q.2 = ⟨p, by omega⟩ := by
          have := congrArg σ h2
          rw [hσ_inv, ← hσp, hσ_inv] at this
          exact this
        have hltv : q.1.val < q.2.val := h12
        rw [hq1, hq2] at hltv
        simp at hltv
      · simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hσ_lt, hf12⟩
    · intro q₁ _ q₂ _ heq
      have h1 : σ q₁.1 = σ q₂.1 := congrArg Prod.fst heq
      have h2 : σ q₁.2 = σ q₂.2 := congrArg Prod.snd heq
      exact Prod.ext (hσ_inv.injective h1) (hσ_inv.injective h2)
  have herase : (S.erase pq).card < S.card := Finset.card_erase_lt_of_mem hpq_mem
  exact lt_of_le_of_lt hle herase

private def greedyEquiv (m : ℕ) [NeZero m] : Equiv.Perm (Fin m) :=
  { toFun := greedy m
    invFun := greedyInv m
    left_inv := greedyInv_greedy m
    right_inv := greedy_greedyInv m }

private lemma H1_greedyInv {m : ℕ} [NeZero m] (t : Fin m) :
    (t.val % 2 = 0 → ∀ hlt : t.val + 1 < m,
      greedyInv m t ∈ H1p m ∧ (-1 : Fin m) - greedyInv m t = greedyInv m ⟨t.val + 1, hlt⟩) ∧
    (t.val % 2 = 1 →
      greedyInv m t ∈ H1m m ∧
        (-1 : Fin m) - greedyInv m t = greedyInv m ⟨t.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) t.isLt⟩) ∧
    (t.val % 2 = 0 ∧ ¬ t.val + 1 < m →
      greedyInv m t ∉ H1p m ∧ greedyInv m t ∉ H1m m) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h0 hlt
    refine ⟨?_, ?_⟩
    · simp only [H1p, Finset.mem_filter, Finset.mem_univ, true_and, greedyInv, if_pos h0]
      omega
    · apply Fin.ext
      rw [neg_one_sub_val]
      simp only [greedyInv, if_pos h0]
      have h1 : ¬ (t.val + 1) % 2 = 0 := by omega
      simp only [if_neg h1]
      omega
  · intro h1
    have h0 : ¬ t.val % 2 = 0 := by omega
    refine ⟨?_, ?_⟩
    · simp only [H1m, Finset.mem_filter, Finset.mem_univ, true_and, greedyInv, if_neg h0]
      omega
    · apply Fin.ext
      rw [neg_one_sub_val]
      simp only [greedyInv, if_neg h0]
      have hprev : (t.val - 1) % 2 = 0 := by omega
      simp only [if_pos hprev]
      omega
  · rintro ⟨h0, hnot⟩
    simp only [H1p, H1m, Finset.mem_filter, Finset.mem_univ, true_and, greedyInv, if_pos h0]
    omega

private lemma H2_greedyInv {m : ℕ} [NeZero m] (t : Fin m) :
    (t.val % 2 = 1 → ∀ hlt : t.val + 1 < m,
      greedyInv m t ∈ H2p m ∧ (0 : Fin m) - greedyInv m t = greedyInv m ⟨t.val + 1, hlt⟩) ∧
    (t.val % 2 = 0 ∧ 0 < t.val →
      greedyInv m t ∈ H2m m ∧
        (0 : Fin m) - greedyInv m t = greedyInv m ⟨t.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) t.isLt⟩) ∧
    ((t.val = 0 ∨ (t.val % 2 = 1 ∧ ¬ t.val + 1 < m)) →
      greedyInv m t ∉ H2p m ∧ greedyInv m t ∉ H2m m) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h1 hlt
    have h0 : ¬ t.val % 2 = 0 := by omega
    refine ⟨?_, ?_⟩
    · simp only [H2p, Finset.mem_filter, Finset.mem_univ, true_and, greedyInv, if_neg h0]
      omega
    · apply Fin.ext
      rw [zero_sub_val]
      simp only [greedyInv, if_neg h0]
      have hnext : (t.val + 1) % 2 = 0 := by omega
      simp only [if_pos hnext]
      split_ifs <;> omega
  · rintro ⟨h0, hpos⟩
    refine ⟨?_, ?_⟩
    · simp only [H2m, Finset.mem_filter, Finset.mem_univ, true_and, greedyInv, if_pos h0]
      omega
    · apply Fin.ext
      rw [zero_sub_val]
      simp only [greedyInv, if_pos h0]
      have hprev : ¬ (t.val - 1) % 2 = 0 := by omega
      simp only [if_neg hprev]
      split_ifs <;> omega
  · rintro (h0 | ⟨h1, hnot⟩)
    · have hmod : t.val % 2 = 0 := by omega
      simp only [H2p, H2m, Finset.mem_filter, Finset.mem_univ, true_and, greedyInv, if_pos hmod]
      omega
    · have h0 : ¬ t.val % 2 = 0 := by omega
      simp only [H2p, H2m, Finset.mem_filter, Finset.mem_univ, true_and, greedyInv, if_neg h0]
      omega

private lemma main_by_inv {m : ℕ} [NeZero m] (a : Fin m → ℝ)
    (ha_pos : ∀ j, 0 < a j) (ha_anti : Antitone a)
    {r : ℕ} (hr1 : 1 ≤ r) (hrm : r ≤ m) :
    ∀ n : ℕ, ∀ τ : Equiv.Perm (Fin m), invCount ((greedyEquiv m).symm.trans τ) ≤ n →
      cyclicProduct m r τ a ≤ cyclicProduct m r (greedy m) a := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro τ hinv
      set f : Equiv.Perm (Fin m) := (greedyEquiv m).symm.trans τ
      by_cases h0 : invCount f = 0
      · have hsm := invCount_zero_strictMono f h0
        have hid := strictMono_perm_eq_id f hsm
        have hτ : (τ : Fin m → Fin m) = greedy m := by
          funext j
          have := hid (greedy m j)
          simpa [f, greedyEquiv, greedyInv_greedy] using this
        rw [hτ]
      · have hpos : 0 < invCount f := Nat.pos_of_ne_zero h0
        rcases exists_adj_inv f hpos with ⟨p, hp, hpinv⟩
        by_cases hp2 : p % 2 = 0
        · set τ' := polarizePerm (-1 : Fin m) (H1p m) (H1m m) (H1_disj m) (H1_map m) τ
          have hcp := cyclicProduct_le_polarize a ha_pos ha_anti hr1 hrm
            (-1 : Fin m) (H1p m) (H1m m) (H1_disj m) (H1_map m) (H1_sep hrm) τ
          set σ : Fin m → Fin m :=
            fun t => greedy m (polarizeSwap (-1 : Fin m) (H1p m) (H1m m) τ (greedyInv m t))
          have hσ_inv : Function.Involutive σ := fun t => by
            dsimp only [σ]
            rw [greedyInv_greedy, polarizeSwap_involutive (-1 : Fin m) (H1p m) (H1m m)
              (H1_disj m) (H1_map m) τ, greedy_greedyInv]
          have hf_eq : ∀ t, f t = τ (greedyInv m t) := fun _ => rfl
          have hf'_eq : ((greedyEquiv m).symm.trans τ' : Fin m → Fin m) = f ∘ σ := by
            funext t
            change τ' (greedyInv m t) = τ (greedyInv m (σ t))
            dsimp only [τ', polarizePerm, σ]
            simp [greedyInv_greedy]
          have hσ_move : ∀ t : Fin m, σ t = t ∨
              (t.val % 2 = 0 ∧ (σ t).val = t.val + 1) ∨
              (t.val % 2 ≠ 0 ∧ (σ t).val + 1 = t.val) := by
            intro t
            dsimp only [σ]
            unfold polarizeSwap
            by_cases hmod : t.val % 2 = 0
            · by_cases hlt : t.val + 1 < m
              · rcases (H1_greedyInv t).1 hmod hlt with ⟨hmem, href⟩
                split_ifs with hcond
                · right; left
                  rw [href, greedy_greedyInv]
                  exact ⟨hmod, rfl⟩
                · left; exact greedy_greedyInv m t
              · rcases (H1_greedyInv t).2.2 ⟨hmod, hlt⟩ with ⟨hnp, hnm⟩
                rw [if_neg (by simp [hnp, hnm])]
                left; exact greedy_greedyInv m t
            · have h1 : t.val % 2 = 1 := by omega
              rcases (H1_greedyInv t).2.1 h1 with ⟨hmem, href⟩
              split_ifs with hcond
              · right; right
                rw [href, greedy_greedyInv]
                exact ⟨hmod, by simp; omega⟩
              · left; exact greedy_greedyInv m t
          have hσ_sort : ∀ t : Fin m, ∀ ht : t.val + 1 < m, t.val % 2 = 0 →
              f (σ t) ≤ f (σ ⟨t.val + 1, ht⟩) := by
            intro t ht htb
            have h1 := congrFun hf'_eq t
            have h2 := congrFun hf'_eq ⟨t.val + 1, ht⟩
            dsimp only [Function.comp_apply] at h1 h2
            rw [← h1, ← h2]
            change τ' (greedyInv m t) ≤ τ' (greedyInv m ⟨t.val + 1, ht⟩)
            rcases (H1_greedyInv t).1 htb ht with ⟨hp_mem, href⟩
            have hm_mem : greedyInv m ⟨t.val + 1, ht⟩ ∈ H1m m := by
              rw [← href]; exact (H1_map m _).mp hp_mem
            have hm_np : greedyInv m ⟨t.val + 1, ht⟩ ∉ H1p m :=
              Finset.disjoint_right.mp (H1_disj m) hm_mem
            rw [polarizePerm_apply, polarizePerm_apply, if_pos hp_mem, if_neg hm_np, if_pos hm_mem]
            have href2 : (-1 : Fin m) - greedyInv m ⟨t.val + 1, ht⟩ = greedyInv m t := by
              rw [← href, sub_sub_cancel]
            rw [href, href2, max_comm]
            exact le_trans (min_le_left _ _) (le_max_left _ _)
          have hσp : σ ⟨p, by omega⟩ = ⟨p + 1, hp⟩ := by
            dsimp only [σ]
            unfold polarizeSwap
            rcases (H1_greedyInv ⟨p, by omega⟩).1 hp2 hp with ⟨hp_mem, href⟩
            have hlt : τ ((-1 : Fin m) - greedyInv m ⟨p, by omega⟩) < τ (greedyInv m ⟨p, by omega⟩) := by
              rw [href]; exact hpinv
            rw [if_pos (Or.inl ⟨hp_mem, hlt⟩), href, greedy_greedyInv]
          have hinv_lt : invCount ((greedyEquiv m).symm.trans τ') < invCount f := by
            have heq : invCount ((greedyEquiv m).symm.trans τ') = invCount (f ∘ σ) := by
              unfold invCount
              rw [hf'_eq]
            rw [heq]
            exact invCount_brick_lt f 0 σ hσ_inv hσ_move hσ_sort p hp hpinv hσp
          exact le_trans hcp (ih _ (lt_of_lt_of_le hinv_lt hinv) τ' le_rfl)
        · have hp1 : p % 2 = 1 := by omega
          set τ' := polarizePerm (0 : Fin m) (H2p m) (H2m m) (H2_disj m) (H2_map m) τ
          have hcp := cyclicProduct_le_polarize a ha_pos ha_anti hr1 hrm
            (0 : Fin m) (H2p m) (H2m m) (H2_disj m) (H2_map m) (H2_sep hrm) τ
          set σ : Fin m → Fin m :=
            fun t => greedy m (polarizeSwap (0 : Fin m) (H2p m) (H2m m) τ (greedyInv m t))
          have hσ_inv : Function.Involutive σ := fun t => by
            dsimp only [σ]
            rw [greedyInv_greedy, polarizeSwap_involutive (0 : Fin m) (H2p m) (H2m m)
              (H2_disj m) (H2_map m) τ, greedy_greedyInv]
          have hf'_eq : ((greedyEquiv m).symm.trans τ' : Fin m → Fin m) = f ∘ σ := by
            funext t
            change τ' (greedyInv m t) = τ (greedyInv m (σ t))
            dsimp only [τ', polarizePerm, σ]
            simp [greedyInv_greedy]
          have hσ_move : ∀ t : Fin m, σ t = t ∨
              (t.val % 2 = 1 ∧ (σ t).val = t.val + 1) ∨
              (t.val % 2 ≠ 1 ∧ (σ t).val + 1 = t.val) := by
            intro t
            dsimp only [σ]
            unfold polarizeSwap
            by_cases hmod : t.val % 2 = 1
            · by_cases hlt : t.val + 1 < m
              · rcases (H2_greedyInv t).1 hmod hlt with ⟨hmem, href⟩
                split_ifs with hcond
                · right; left
                  rw [href, greedy_greedyInv]
                  exact ⟨hmod, rfl⟩
                · left; exact greedy_greedyInv m t
              · rcases (H2_greedyInv t).2.2 (Or.inr ⟨hmod, hlt⟩) with ⟨hnp, hnm⟩
                rw [if_neg (by simp [hnp, hnm])]
                left; exact greedy_greedyInv m t
            · by_cases ht0 : t.val = 0
              · rcases (H2_greedyInv t).2.2 (Or.inl ht0) with ⟨hnp, hnm⟩
                rw [if_neg (by simp [hnp, hnm])]
                left; exact greedy_greedyInv m t
              · have h0' : t.val % 2 = 0 := by omega
                rcases (H2_greedyInv t).2.1 ⟨h0', by omega⟩ with ⟨hmem, href⟩
                split_ifs with hcond
                · right; right
                  rw [href, greedy_greedyInv]
                  exact ⟨hmod, by simp; omega⟩
                · left; exact greedy_greedyInv m t
          have hσ_sort : ∀ t : Fin m, ∀ ht : t.val + 1 < m, t.val % 2 = 1 →
              f (σ t) ≤ f (σ ⟨t.val + 1, ht⟩) := by
            intro t ht htb
            have h1 := congrFun hf'_eq t
            have h2 := congrFun hf'_eq ⟨t.val + 1, ht⟩
            dsimp only [Function.comp_apply] at h1 h2
            rw [← h1, ← h2]
            change τ' (greedyInv m t) ≤ τ' (greedyInv m ⟨t.val + 1, ht⟩)
            rcases (H2_greedyInv t).1 htb ht with ⟨hp_mem, href⟩
            have hm_mem : greedyInv m ⟨t.val + 1, ht⟩ ∈ H2m m := by
              rw [← href]; exact (H2_map m _).mp hp_mem
            have hm_np : greedyInv m ⟨t.val + 1, ht⟩ ∉ H2p m :=
              Finset.disjoint_right.mp (H2_disj m) hm_mem
            rw [polarizePerm_apply, polarizePerm_apply, if_pos hp_mem, if_neg hm_np, if_pos hm_mem]
            have href2 : (0 : Fin m) - greedyInv m ⟨t.val + 1, ht⟩ = greedyInv m t := by
              rw [← href, sub_sub_cancel]
            rw [href, href2, max_comm]
            exact le_trans (min_le_left _ _) (le_max_left _ _)
          have hσp : σ ⟨p, by omega⟩ = ⟨p + 1, hp⟩ := by
            dsimp only [σ]
            unfold polarizeSwap
            rcases (H2_greedyInv ⟨p, by omega⟩).1 hp1 hp with ⟨hp_mem, href⟩
            have hlt : τ ((0 : Fin m) - greedyInv m ⟨p, by omega⟩) < τ (greedyInv m ⟨p, by omega⟩) := by
              rw [href]; exact hpinv
            rw [if_pos (Or.inl ⟨hp_mem, hlt⟩), href, greedy_greedyInv]
          have hinv_lt : invCount ((greedyEquiv m).symm.trans τ') < invCount f := by
            have heq : invCount ((greedyEquiv m).symm.trans τ') = invCount (f ∘ σ) := by
              unfold invCount
              rw [hf'_eq]
            rw [heq]
            exact invCount_brick_lt f 1 σ hσ_inv hσ_move hσ_sort p hp hpinv hσp
          exact le_trans hcp (ih _ (lt_of_lt_of_le hinv_lt hinv) τ' le_rfl)

end Arxiv220302443Proof

theorem OMA.solution : type_of% @OMA.S_arxiv_2203_02443.main := by
  intro m _ a ha_pos ha_anti r hr1 hrm τ
  exact Arxiv220302443Proof.main_by_inv a ha_pos ha_anti hr1 hrm _ τ le_rfl

