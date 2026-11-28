import OMAReductions.R_arxiv_1811_10503_R2

/-!
# Four-element blocking and the remaining sizes in Sun's Conjecture 4.1

The reduction in PR #21739, by @ethduke, isolates blocked subsets of finite
abelian groups. Here the four-element case is proved, leaving the fixed sizes
5, 6, and 7 as separate hypotheses. The original conjecture is Zhi-Wei Sun's
Conjecture 4.1 (https://arxiv.org/abs/1811.10503). The pair orientation argument
also appears in Dingying Ma's Lemma 5.2 and §8.3
(https://arxiv.org/html/2611.13582v1).

With four elements, blocking leaves one cyclic class or two pairs. For the
one-class case at order greater than 15, a pair has at most two collision slots
and can have two only when one element is the square of the other. Each such
collision slot blocks two of the 24 assignments. A triangle of square-related
neighbors would give an order dividing 7, so at least one pair has at most one
collision slot. The only smaller possible orders are 7, 11, and 13. These are
checked by finite reduction in Lean's kernel after normalizing one residue to 1.
Two distinct two-element classes are assigned complementary exponent pairs.
-/

namespace OMA.SunPowerPermutation

open Finset Subgroup

theorem zpowers_pow_eq_of_coprime {G : Type*} [Group G] (a : G) (i : ℕ)
    (hi : (orderOf a).Coprime i) : zpowers (a ^ i) = zpowers a := by
  apply le_antisymm
  · exact zpowers_le.mpr (npow_mem_zpowers a i)
  · exact zpowers_le.mpr (mem_zpowers_pow_iff.mpr hi.symm.gcd_eq_one)

theorem zpowers_eq_of_power_collision {G : Type*} [Group G] {a b : G} {i j : ℕ}
    (ha : (orderOf a).Coprime i) (hb : (orderOf b).Coprime j) (h : a ^ i = b ^ j) :
    zpowers a = zpowers b := by
  rw [← zpowers_pow_eq_of_coprime a i ha, ← zpowers_pow_eq_of_coprime b j hb, h]

/-- If all orders from 2 to `n+1` are absent, every positive exponent at most `n`
is coprime to each element's order. -/
theorem power_order_coprime_of_no_small {G : Type*} [Group G] [Finite G]
    {n : ℕ} (hsmall : ∀ x : G, orderOf x ∉ Icc 2 (n + 1))
    (x : G) {i : ℕ} (hi : 0 < i) (hin : i ≤ n) : (orderOf x).Coprime i := by
  by_contra hn
  obtain ⟨p, hp, hpd, hpi⟩ := Nat.Prime.not_coprime_iff_dvd.mp hn
  have hpos : orderOf x ≠ 0 := (isOfFinOrder_of_finite x).orderOf_pos.ne'
  apply hsmall (x ^ (orderOf x / p))
  rw [orderOf_pow_orderOf_div hpos hpd]
  exact mem_Icc.mpr ⟨hp.two_le, (Nat.le_of_dvd hi hpi).trans (hin.trans (Nat.le_succ _))⟩

theorem zpowers_eq_of_small_power_collision {G : Type*} [Group G] [Finite G]
    {n : ℕ} (hsmall : ∀ x : G, orderOf x ∉ Icc 2 (n + 1))
    {a b : G} {i j : ℕ} (hi : 0 < i) (hin : i ≤ n) (hj : 0 < j) (hjn : j ≤ n)
    (h : a ^ i = b ^ j) : zpowers a = zpowers b :=
  zpowers_eq_of_power_collision (power_order_coprime_of_no_small hsmall a hi hin)
    (power_order_coprime_of_no_small hsmall b hj hjn) h

open Finset Subgroup

private theorem order_coprime_of_le_successor {G : Type*} [Group G] [Finite G]
    {n : ℕ} (hsmall : ∀ x : G, orderOf x ∉ Icc 2 (n + 1))
    (x : G) {u : ℕ} (hu : 0 < u) (hun : u ≤ n + 1) : (orderOf x).Coprime u := by
  by_contra hn
  obtain ⟨p, hp, hpd, hpu⟩ := Nat.Prime.not_coprime_iff_dvd.mp hn
  have hx0 : orderOf x ≠ 0 := (isOfFinOrder_of_finite x).orderOf_pos.ne'
  apply hsmall (x ^ (orderOf x / p))
  rw [orderOf_pow_orderOf_div hx0 hpd]
  exact mem_Icc.mpr ⟨hp.two_le, (Nat.le_of_dvd hu hpu).trans hun⟩

theorem pair_collision_order_dvd {G : Type*} [Group G] {x y : G} {r s : ℕ}
    (hrs : r ≤ s) (h₁ : x ^ r = y ^ s) (h₂ : y ^ r = x ^ s) :
    orderOf x ∣ (s - r) * (r + s) := by
  have heq : x ^ (r * r) = x ^ (s * s) := by
    calc
      x ^ (r * r) = (x ^ r) ^ r := pow_mul ..
      _ = (y ^ s) ^ r := congrArg (· ^ r) h₁
      _ = (y ^ r) ^ s := pow_right_comm ..
      _ = (x ^ s) ^ s := congrArg (· ^ s) h₂
      _ = x ^ (s * s) := (pow_mul ..).symm
  have hfactor : s * s - r * r = (s - r) * (r + s) := by
    rw [Nat.sub_mul, Nat.mul_add, Nat.mul_add, Nat.mul_comm s r]
    omega
  rw [← hfactor]
  exact (Nat.modEq_iff_dvd' (Nat.mul_le_mul hrs hrs)).mp (pow_eq_pow_iff_modEq.mp heq)

theorem either_pair_orientation_of_coprime {G : Type*} [Group G] {x y : G}
    (hxy : x ≠ y) {r s : ℕ} (hrs : r ≤ s)
    (hdiff : (orderOf x).Coprime (s - r)) (hsum : (orderOf x).Coprime (r + s))
    (hy : (orderOf y).Coprime s) : x ^ r ≠ y ^ s ∨ y ^ r ≠ x ^ s := by
  by_cases h₁ : x ^ r = y ^ s
  · right
    intro h₂
    have hxord : orderOf x = 1 := by
      rw [← Nat.gcd_eq_left (pair_collision_order_dvd hrs h₁ h₂)]
      exact (hdiff.mul_right hsum).gcd_eq_one
    have hx1 : x = 1 := orderOf_eq_one_iff.mp hxord
    have hydvd : orderOf y ∣ s := orderOf_dvd_of_pow_eq_one (by simpa [hx1] using h₁.symm)
    have hy1 : y = 1 := orderOf_eq_one_iff.mp ((Nat.gcd_eq_left hydvd).symm.trans hy.gcd_eq_one)
    exact hxy (hx1.trans hy1.symm)
  · exact Or.inl h₁

theorem either_pair_orientation {G : Type*} [Group G] [Finite G]
    {n : ℕ} (hsmall : ∀ x : G, orderOf x ∉ Icc 2 (n + 1)) {x y : G}
    (hxy : x ≠ y) {r s : ℕ} (hrs : r < s) (hsum : r + s ≤ n + 1) :
    x ^ r ≠ y ^ s ∨ y ^ r ≠ x ^ s :=
  either_pair_orientation_of_coprime hxy hrs.le
    (order_coprime_of_le_successor hsmall x (by omega) (by omega))
    (order_coprime_of_le_successor hsmall x (by omega) hsum)
    (order_coprime_of_le_successor hsmall y (by omega) (by omega))

/-- Distinct two-element cyclic classes admit one power permutation, using the
complementary exponent slots `j+1` and `2*m-j` for each class `j`. -/
theorem exists_distinct_powers_of_pairs {G : Type*} [Group G] [Finite G]
    (m : ℕ) (hsmall : ∀ g : G, orderOf g ∉ Icc 2 (2 * m + 1))
    (x y : Fin m → G) (hp : ∀ j, x j ≠ y j)
    (hclass : ∀ j, zpowers (x j) = zpowers (y j))
    (hsep : ∀ i j, i ≠ j → zpowers (x i) ≠ zpowers (x j)) :
    ∃ a : Fin (2 * m) → G, Function.Injective a ∧
      Set.range a = Set.range x ∪ Set.range y ∧
      Function.Injective (fun i => a i ^ (i.val + 1)) := by
  classical
  let slots : Fin m × Bool → Fin (2 * m) := fun p =>
    ⟨if p.2 then 2 * m - 1 - p.1.val else p.1.val, by
      have h := p.1.isLt
      split <;> omega⟩
  have hsInj : Function.Injective slots := by
    rintro ⟨i, bi⟩ ⟨j, bj⟩ h
    have h := congrArg Fin.val h
    have hi := i.isLt
    have hj := j.isLt
    cases bi <;> cases bj <;> simp [slots] at h ⊢ <;> omega
  let e : (Fin m × Bool) ≃ Fin (2 * m) := Equiv.ofBijective slots
    ((Fintype.bijective_iff_injective_and_card slots).mpr ⟨hsInj, by
      simp [Fintype.card_prod, mul_comm]⟩)
  let pairs : Fin m → G × G := fun j =>
    if x j ^ (j.val + 1) ≠ y j ^ (2 * m - j.val) then (x j, y j) else (y j, x j)
  have hpairs (j : Fin m) : pairs j = (x j, y j) ∨ pairs j = (y j, x j) := by
    unfold pairs
    split <;> simp
  have hpowers (j : Fin m) : (pairs j).1 ^ (j.val + 1) ≠ (pairs j).2 ^ (2 * m - j.val) := by
    have hj := j.isLt
    have hor := either_pair_orientation hsmall (hp j)
      (show j.val + 1 < 2 * m - j.val by omega)
      (show j.val + 1 + (2 * m - j.val) ≤ 2 * m + 1 by omega)
    unfold pairs
    split
    · assumption
    · exact hor.resolve_left ‹¬ _›
  let a₀ : Fin m × Bool → G := fun p => if p.2 then (pairs p.1).2 else (pairs p.1).1
  have hcyclic (p : Fin m × Bool) : zpowers (a₀ p) = zpowers (x p.1) := by
    obtain ⟨j, b⟩ := p
    rcases hpairs j with h | h <;> cases b <;> simp [a₀, h, ← hclass j]
  have hpairInj (f : Fin m × Bool → G)
      (hf : ∀ p, zpowers (f p) = zpowers (x p.1))
      (hne : ∀ j, f (j, false) ≠ f (j, true)) : Function.Injective f := by
    rintro ⟨i, bi⟩ ⟨j, bj⟩ h
    have hij : i = j := by
      by_contra hij
      exact hsep i j hij ((hf (i, bi)).symm.trans ((congrArg zpowers h).trans (hf (j, bj))))
    subst j
    cases bi <;> cases bj
    · rfl
    · exact (hne i h).elim
    · exact (hne i h.symm).elim
    · rfl
  have hOrdInj : Function.Injective a₀ := hpairInj a₀ hcyclic fun j => by
    rcases hpairs j with h | h
    · simpa [a₀, h] using hp j
    · simpa [a₀, h] using (hp j).symm
  have hrange : Set.range a₀ = Set.range x ∪ Set.range y := by
    ext z
    constructor
    · rintro ⟨⟨j, b⟩, rfl⟩
      rcases hpairs j with h | h <;> cases b
      · left; exact ⟨j, by simp [a₀, h]⟩
      · right; exact ⟨j, by simp [a₀, h]⟩
      · right; exact ⟨j, by simp [a₀, h]⟩
      · left; exact ⟨j, by simp [a₀, h]⟩
    · rintro (⟨j, rfl⟩ | ⟨j, rfl⟩) <;> rcases hpairs j with h | h
      · exact ⟨(j, false), by simp [a₀, h]⟩
      · exact ⟨(j, true), by simp [a₀, h]⟩
      · exact ⟨(j, true), by simp [a₀, h]⟩
      · exact ⟨(j, false), by simp [a₀, h]⟩
  let raised : Fin m × Bool → G := fun p => a₀ p ^ ((slots p).val + 1)
  have hRaisedInj : Function.Injective raised := by
    apply hpairInj
    · intro p
      have hlt := (slots p).isLt
      dsimp [raised]
      rw [zpowers_pow_eq_of_coprime _ _
        (power_order_coprime_of_no_small hsmall _ (by omega) (by omega)), hcyclic]
    · intro j
      have hj := j.isLt
      have heq : 2 * m - 1 - j.val + 1 = 2 * m - j.val := by omega
      simpa [raised, a₀, slots, heq] using hpowers j
  refine ⟨a₀ ∘ e.symm, hOrdInj.comp e.symm.injective, ?_, ?_⟩
  · rw [Set.range_comp, e.symm.surjective.range_eq, Set.image_univ]
    exact hrange
  · have heSlot (i : Fin (2 * m)) : slots (e.symm i) = i := e.apply_symm_apply i
    intro i j hij
    apply e.symm.injective
    apply hRaisedInj
    simpa only [raised, heSlot, Function.comp_apply] using hij

open Finset

private theorem ratioSlots_card_le :
    let ratioSlots := fun p : Fin 4 × Fin 4 =>
      (univ : Finset (Fin 4 × Fin 4)).filter fun q =>
        q.1 ≠ q.2 ∧ (p.1.val + 1) * (q.2.val + 1) = (q.1.val + 1) * (p.2.val + 1)
    ∀ p : (Fin 4 × Fin 4), p.1 ≠ p.2 → (ratioSlots p).card ≤ 2 := by
  dsimp only
  decide +kernel

private theorem ratioSlots_double :
    let ratioSlots := fun p : Fin 4 × Fin 4 =>
      (univ : Finset (Fin 4 × Fin 4)).filter fun q =>
        q.1 ≠ q.2 ∧ (p.1.val + 1) * (q.2.val + 1) = (q.1.val + 1) * (p.2.val + 1)
    ∀ p : (Fin 4 × Fin 4), p.1 ≠ p.2 → 2 ≤ (ratioSlots p).card →
    ((0, 1) : (Fin 4 × Fin 4)) ∈ ratioSlots p ∨ ((1, 0) : (Fin 4 × Fin 4)) ∈ ratioSlots p := by
  dsimp only
  decide +kernel

private theorem slot_product_bounds (r s : Fin 4) : 1 ≤ (r.val + 1) * (s.val + 1) ∧
    (r.val + 1) * (s.val + 1) ≤ 16 := by
  constructor
  · exact Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)
  · exact Nat.mul_le_mul (by exact Nat.succ_le_iff.mpr r.isLt) (by exact Nat.succ_le_iff.mpr s.isLt)

private theorem eq_slot_ratio_of_collisions {G : Type*} [Group G] {x y : G}
    (hx : 15 < orderOf x) {p q : (Fin 4 × Fin 4)}
    (hp : x ^ (p.1.val + 1) = y ^ (p.2.val + 1))
    (hq : x ^ (q.1.val + 1) = y ^ (q.2.val + 1)) :
    (p.1.val + 1) * (q.2.val + 1) = (q.1.val + 1) * (p.2.val + 1) := by
  have h : x ^ ((p.1.val + 1) * (q.2.val + 1)) = x ^ ((q.1.val + 1) * (p.2.val + 1)) := by
    calc
      _ = (x ^ (p.1.val + 1)) ^ (q.2.val + 1) := pow_mul ..
      _ = (y ^ (p.2.val + 1)) ^ (q.2.val + 1) := congrArg (· ^ (q.2.val + 1)) hp
      _ = (y ^ (q.2.val + 1)) ^ (p.2.val + 1) := pow_right_comm ..
      _ = (x ^ (q.1.val + 1)) ^ (p.2.val + 1) := congrArg (· ^ (p.2.val + 1)) hq.symm
      _ = _ := (pow_mul ..).symm
  have hm := pow_eq_pow_iff_modEq.mp h
  have hL := slot_product_bounds p.1 q.2
  have hR := slot_product_bounds q.1 p.2
  rcases lt_trichotomy ((p.1.val + 1) * (q.2.val + 1)) ((q.1.val + 1) * (p.2.val + 1)) with hlt | heq | hgt
  · have hle := Nat.le_of_dvd (Nat.sub_pos_of_lt hlt) hm.dvd'
    omega
  · exact heq
  · have hle := Nat.le_of_dvd (Nat.sub_pos_of_lt hgt) hm.symm.dvd'
    omega

/-- Outside the three possible small orders, two collision choices already
force one element to be the square of the other. -/
private theorem collisionSlots_bound {G : Type*} [Group G] {x y : G} (hx : 15 < orderOf x)
    (collisions : Finset (Fin 4 × Fin 4))
    (hmem : ∀ p : Fin 4 × Fin 4, p ∈ collisions ↔
      p.1 ≠ p.2 ∧ x ^ (p.1.val + 1) = y ^ (p.2.val + 1)) :
    collisions.card ≤ 2 ∧
    (2 ≤ collisions.card → x = y ^ 2 ∨ y = x ^ 2) := by
  let ratioSlots := fun p : Fin 4 × Fin 4 =>
    (univ : Finset (Fin 4 × Fin 4)).filter fun q =>
      q.1 ≠ q.2 ∧ (p.1.val + 1) * (q.2.val + 1) = (q.1.val + 1) * (p.2.val + 1)
  by_cases hc : (collisions).Nonempty
  · obtain ⟨p, hp⟩ := hc
    have hp' := (hmem _).mp hp
    have hsub : collisions ⊆ ratioSlots p := by
      intro q hq
      have hq' := (hmem _).mp hq
      exact mem_filter.mpr ⟨mem_univ q, hq'.1, eq_slot_ratio_of_collisions hx hp'.2 hq'.2⟩
    have hratio := ratioSlots_card_le p hp'.1
    refine ⟨(card_le_card hsub).trans hratio, ?_⟩
    intro hdouble
    have heq := eq_of_subset_of_card_le hsub (hratio.trans hdouble)
    rcases ratioSlots_double p hp'.1 (hdouble.trans (card_le_card hsub)) with h | h
    · change ((0, 1) : Fin 4 × Fin 4) ∈ ratioSlots p at h
      rw [← heq] at h
      exact Or.inl (by simpa using ((hmem _).mp h).2)
    · change ((1, 0) : Fin 4 × Fin 4) ∈ ratioSlots p at h
      rw [← heq] at h
      exact Or.inr (by simpa using ((hmem _).mp h).2.symm)
  · rw [not_nonempty_iff_eq_empty.mp hc]
    simp

/-- Orders below 16 permitted by the four-element problem, for a nonidentity element. -/
theorem order_eq_exception_or_gt_fifteen {G : Type*} [Group G] [Finite G]
    (hsmall : ∀ g : G, orderOf g ∉ Icc 2 5) {x : G} (hx : x ≠ 1) :
    orderOf x = 7 ∨ orderOf x = 11 ∨ orderOf x = 13 ∨ 15 < orderOf x := by
  let d := orderOf x
  have hpos : 0 < d := (isOfFinOrder_of_finite x).orderOf_pos
  have hne : d ≠ 1 := fun h => hx (orderOf_eq_one_iff.mp h)
  have hgt : 5 < d := by
    by_contra! h
    exact hsmall x (mem_Icc.mpr ⟨by omega, h⟩)
  have h₂ : d.Coprime 2 := power_order_coprime_of_no_small (n := 4) hsmall x (by decide) (by decide)
  have h₃ : d.Coprime 3 := power_order_coprime_of_no_small (n := 4) hsmall x (by decide) (by decide)
  by_cases hl : 15 < d
  · exact Or.inr (Or.inr (Or.inr hl))
  have hfinite : ∀ u : Fin 16, 5 < u.val → u.val.Coprime 2 → u.val.Coprime 3 →
      u.val = 7 ∨ u.val = 11 ∨ u.val = 13 := by decide +kernel
  rcases hfinite ⟨d, by omega⟩ hgt h₂ h₃ with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))

private theorem iterate_triangle {X : Type*} (f : X → X) (hf : Function.Injective f)
    {x y z : X} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (a : f x = y ∨ f y = x) (b : f y = z ∨ f z = y) (c : f x = z ∨ f z = x) :
    f (f (f x)) = x := by
  rcases a with a | a
  · rcases b with b | b
    · rcases c with c | c
      · exact (hyz (a.symm.trans c)).elim
      · rw [a, b, c]
    · exact (hxz (hf (a.trans b.symm))).elim
  · rcases b with b | b
    · exact (hxz (a.symm.trans b)).elim
    · rcases c with c | c
      · rw [c, b, a]
      · exact (hxy (c.symm.trans b)).elim

private theorem square_injective_of_no_small {G : Type*} [CommGroup G] [Finite G]
    (hsmall : ∀ g : G, orderOf g ∉ Icc 2 5) : Function.Injective (fun g : G => g ^ 2) := by
  intro x y h
  change x ^ (2 : ℕ) = y ^ (2 : ℕ) at h
  have hdvd : orderOf (x / y) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [div_pow, h, div_self'])
  have hcop := power_order_coprime_of_no_small (n := 4) hsmall (x / y)
    (i := 2) (by decide) (by decide)
  have hord := (Nat.gcd_eq_left hdvd).symm.trans hcop.gcd_eq_one
  exact div_eq_one.mp (orderOf_eq_one_iff.mp hord)

private theorem fixedSlots_card :
    let fixedSlots := fun (p q : Fin 4 × Fin 4) =>
      (univ : Finset (Equiv.Perm (Fin 4))).filter fun σ => σ p.1 = q.1 ∧ σ p.2 = q.2
    ∀ p q : Fin 4 × Fin 4, p.1 ≠ p.2 → q.1 ≠ q.2 → (fixedSlots p q).card = 2 := by
  dsimp only
  decide +kernel

/-- Four distinct elements of order greater than 15 have a collision-free
power permutation under the four-element problem's order exclusion. -/
theorem exists_permutation_four_of_large_order {G : Type*} [CommGroup G] [Finite G]
    (hsmall : ∀ x : G, orderOf x ∉ Icc 2 5)
    (a : Fin 4 → G) (ha : Function.Injective a) (hlarge : ∀ i, 15 < orderOf (a i)) :
    ∃ σ : Equiv.Perm (Fin 4), Function.Injective (fun i : Fin 4 => a (σ i) ^ (i.val + 1)) := by
  classical
  let slots := fun p : Fin 4 × Fin 4 =>
    (univ : Finset (Fin 4 × Fin 4)).filter fun q =>
      q.1 ≠ q.2 ∧ a p.1 ^ (q.1.val + 1) = a p.2 ^ (q.2.val + 1)
  let fixedSlots := fun (p q : Fin 4 × Fin 4) =>
    (univ : Finset (Equiv.Perm (Fin 4))).filter fun σ => σ p.1 = q.1 ∧ σ p.2 = q.2
  let increasingPairs := (univ : Finset (Fin 4 × Fin 4)).filter fun p => p.1 < p.2
  have hmem (p q : Fin 4 × Fin 4) : q ∈ slots p ↔
      q.1 ≠ q.2 ∧ a p.1 ^ (q.1.val + 1) = a p.2 ^ (q.2.val + 1) := by
    rw [show slots p = univ.filter (fun q => q.1 ≠ q.2 ∧
      a p.1 ^ (q.1.val + 1) = a p.2 ^ (q.2.val + 1)) from rfl, mem_filter]
    simp only [mem_univ, true_and]
  have hupper (p : Fin 4 × Fin 4) : (slots p).card ≤ 2 :=
    (collisionSlots_bound (hlarge p.1) (slots p) (hmem p)).1
  have hpair : ∃ p ∈ increasingPairs, (slots p).card ≤ 1 := by
    by_contra! h
    have hsquare (i j : Fin 4) (hij : i < j) : a i ^ 2 = a j ∨ a j ^ 2 = a i := by
      rcases (collisionSlots_bound (hlarge i) (slots (i, j)) (hmem (i, j))).2
        (h (i, j) (mem_filter.mpr ⟨mem_univ _, hij⟩)) with h₁ | h₂
      · exact Or.inr h₁.symm
      · exact Or.inl h₂.symm
    have ht := iterate_triangle (fun x : G => x ^ 2) (square_injective_of_no_small hsmall)
      (ha.ne (show (0 : Fin 4) ≠ 1 by decide)) (ha.ne (show (0 : Fin 4) ≠ 2 by decide))
      (ha.ne (show (1 : Fin 4) ≠ 2 by decide)) (hsquare 0 1 (by decide))
      (hsquare 1 2 (by decide)) (hsquare 0 2 (by decide))
    have hp : a 0 ^ (1 : ℕ) = a 0 ^ 8 := by
      simpa only [pow_one, ← pow_mul] using ht.symm
    have hdiv : orderOf (a 0) ∣ (8 : ℕ) - 1 := (pow_eq_pow_iff_modEq.mp hp).dvd'
    exact (not_le_of_gt (hlarge 0)) ((Nat.le_of_dvd (by decide) hdiv).trans (by decide))
  obtain ⟨p₀, hp₀, hlow⟩ := hpair
  have hcount : ∑ p ∈ increasingPairs, (slots p).card ≤ 11 := by
    have hrest : ∑ p ∈ increasingPairs.erase p₀, (slots p).card ≤
        (increasingPairs.erase p₀).card * 2 := by
      simpa using (sum_le_sum (fun p (_ : p ∈ increasingPairs.erase p₀) => hupper p) :
        ∑ p ∈ increasingPairs.erase p₀, (slots p).card ≤ ∑ _p ∈ increasingPairs.erase p₀, 2)
    have hc : (increasingPairs.erase p₀).card = 5 := by
      rw [card_erase_of_mem hp₀, show increasingPairs.card = 6 by decide +kernel]
    rw [hc] at hrest
    rw [← sum_erase_add _ _ hp₀]
    omega
  let badPair := fun p : (Fin 4 × Fin 4) => (slots p).biUnion (fixedSlots p)
  have hbadPair (p : (Fin 4 × Fin 4)) (hp : p ∈ increasingPairs) : (badPair p).card ≤ 2 * (slots p).card := by
    have hp' : p.1 < p.2 := (mem_filter.mp hp).2
    calc
      _ ≤ ∑ q ∈ slots p, (fixedSlots p q).card := card_biUnion_le
      _ = ∑ _q ∈ slots p, 2 := sum_congr rfl fun q hq =>
        fixedSlots_card p q hp'.ne ((hmem p q).mp hq).1
      _ = _ := by simp [Nat.mul_comm]
  let bad := increasingPairs.biUnion badPair
  have hbad : bad.card ≤ 22 := by
    calc
      _ ≤ ∑ p ∈ increasingPairs, (badPair p).card := card_biUnion_le
      _ ≤ ∑ p ∈ increasingPairs, 2 * (slots p).card := sum_le_sum hbadPair
      _ = 2 * ∑ p ∈ increasingPairs, (slots p).card := by
        simp only [two_mul, sum_add_distrib]
      _ ≤ 22 := by omega
  have hall : (univ : Finset (Equiv.Perm (Fin 4))).card = 24 := by
    rw [card_univ, Fintype.card_perm, Fintype.card_fin]
    decide
  have hsome : ∃ σ, σ ∉ bad := by
    by_contra! hf
    have hs : (univ : Finset (Equiv.Perm (Fin 4))) ⊆ bad := fun σ _ => hf σ
    have h := card_le_card hs
    omega
  obtain ⟨σ, hσ⟩ := hsome
  have hgood (i j : Fin 4) (hij : i < j) :
      a i ^ ((σ i).val + 1) ≠ a j ^ ((σ j).val + 1) := by
    intro h
    apply hσ
    apply mem_biUnion.mpr
    refine ⟨(i, j), mem_filter.mpr ⟨mem_univ _, hij⟩, mem_biUnion.mpr ?_⟩
    exact ⟨(σ i, σ j), (hmem (i, j) (σ i, σ j)).mpr ⟨σ.injective.ne hij.ne, h⟩,
      mem_filter.mpr ⟨mem_univ _, rfl, rfl⟩⟩
  refine ⟨σ.symm, ?_⟩
  intro i j h
  rcases lt_trichotomy (σ.symm i) (σ.symm j) with hij | hij | hij
  · exact (hgood _ _ hij (by simpa only [Equiv.apply_symm_apply] using h)).elim
  · exact σ.symm.injective hij
  · exact (hgood _ _ hij (by simpa only [Equiv.apply_symm_apply] using h.symm)).elim

open Finset Subgroup

set_option maxHeartbeats 1600000 in
private theorem four_residue_certificate :
    ∀ d : Fin 14, d.val = 7 ∨ d.val = 11 ∨ d.val = 13 →
    ∀ x y z : Fin d.val,
      let r : Fin 4 → ℕ := fun i => if i = 0 then 1 else if i = 1 then x.val else if i = 2 then y.val else z.val
      (∀ i j, r i = r j → i = j) →
      ∃ σ ∈ (List.finRange 4).flatMap (fun i => (List.finRange 3).flatMap (fun j =>
        (List.finRange 2).map fun k =>
          (Equiv.swap 0 i).trans ((Equiv.swap 1 j.succ).trans (Equiv.swap 2 k.succ.succ)))),
        ∀ i j : Fin 4, (r (σ i) * (i.val + 1)) % d.val = (r (σ j) * (j.val + 1)) % d.val → i = j := by
  decide +kernel

private theorem exists_perm_four_of_certificate {G : Type*} [Group G] [Finite G]
    (a : Fin 4 → G) (ha : Function.Injective a) (hmem : ∀ i, a i ∈ zpowers (a 0))
    {d : ℕ} (hd : orderOf (a 0) = d) (hd1 : 1 < d)
    (hde : d = 7 ∨ d = 11 ∨ d = 13) :
    ∃ σ : Equiv.Perm (Fin 4), Function.Injective (fun i : Fin 4 => a (σ i) ^ (i.val + 1)) := by
  let e : Fin d ≃ zpowers (a 0) := (finCongr hd.symm).trans (finEquivZPowers (isOfFinOrder_of_finite _))
  let r : Fin 4 → Fin d := fun i => e.symm ⟨a i, hmem i⟩
  have hrep (i : Fin 4) : a 0 ^ (r i).val = a i :=
    congrArg Subtype.val (e.apply_symm_apply ⟨a i, hmem i⟩)
  have hbase : r 0 = (⟨1, hd1⟩ : Fin d) := by
    apply e.injective
    apply Subtype.ext
    change a 0 ^ (r 0).val = a 0 ^ (1 : ℕ)
    rw [hrep, pow_one]
  let input : Fin 4 → ℕ := fun i =>
    if i = 0 then 1 else if i = 1 then (r 1).val else if i = 2 then (r 2).val else (r 3).val
  have hin : input = fun i => (r i).val := by
    funext i
    fin_cases i
    · exact (congrArg Fin.val hbase).symm
    · rfl
    · rfl
    · rfl
  have hr (i j : Fin 4) (hij : (r i).val = (r j).val) : i = j := by
    apply ha
    rw [← hrep i, ← hrep j, hij]
  have hinput (i j : Fin 4) (heq : input i = input j) : i = j := by
    rw [hin] at heq
    exact hr i j heq
  obtain ⟨σ, _, hσ⟩ := four_residue_certificate ⟨d, by omega⟩ hde (r 1) (r 2) (r 3) hinput
  refine ⟨σ, ?_⟩
  intro i j h
  apply hσ i j
  change (input (σ i) * (i.val + 1)) % d = (input (σ j) * (j.val + 1)) % d
  rw [hin]
  change a (σ i) ^ (i.val + 1) = a (σ j) ^ (j.val + 1) at h
  rw [← hrep (σ i), ← hrep (σ j), ← pow_mul, ← pow_mul] at h
  have hmod := pow_eq_pow_iff_modEq.mp h
  change ((r (σ i)).val * (i.val + 1)) % orderOf (a 0) =
    ((r (σ j)).val * (j.val + 1)) % orderOf (a 0) at hmod
  rwa [hd] at hmod

/-- A collision-free assignment of exponent slots to any four distinct
generators of one cyclic subgroup, assuming no order from 2 through 5. -/
theorem exists_permutation_four_single_class {G : Type*} [CommGroup G] [Finite G]
    (hsmall : ∀ x : G, orderOf x ∉ Icc 2 5) (a : Fin 4 → G) (ha : Function.Injective a)
    (hclass : ∀ i, zpowers (a i) = zpowers (a 0)) :
    ∃ σ : Equiv.Perm (Fin 4), Function.Injective (fun i : Fin 4 => a (σ i) ^ (i.val + 1)) := by
  have hmem (i : Fin 4) : a i ∈ zpowers (a 0) := (hclass i) ▸ mem_zpowers (a i)
  have hbase : a 0 ≠ 1 := by
    intro hx
    have h := hmem 1
    rw [hx, zpowers_one_eq_bot, mem_bot] at h
    exact ha.ne (show (0 : Fin 4) ≠ 1 by decide) (hx.trans h.symm)
  rcases order_eq_exception_or_gt_fifteen hsmall hbase with h | h | h | h
  · exact exists_perm_four_of_certificate a ha hmem h (by decide) (Or.inl rfl)
  · exact exists_perm_four_of_certificate a ha hmem h (by decide) (Or.inr (Or.inl rfl))
  · exact exists_perm_four_of_certificate a ha hmem h (by decide) (Or.inr (Or.inr rfl))
  · apply exists_permutation_four_of_large_order hsmall a ha
    intro i
    have horders : orderOf (a i) = orderOf (a 0) := Nat.dvd_antisymm
      (orderOf_dvd_of_mem_zpowers (hmem i))
      (orderOf_dvd_of_mem_zpowers ((hclass i).symm ▸ mem_zpowers (a 0)))
    exact horders.symm ▸ h

open Finset Subgroup

private theorem two_classes_four {X : Type*} (c : Fin 4 → X)
    (hcompanion : ∀ i, ∃ j, i ≠ j ∧ c i = c j) (hnonconstant : ¬ ∀ i, c i = c 0) :
    ∃ σ : Equiv.Perm (Fin 4), c (σ 0) = c (σ 1) ∧ c (σ 2) = c (σ 3) ∧
      c (σ 0) ≠ c (σ 2) := by
  obtain ⟨j, hj, hclass⟩ := hcompanion 0
  let σ := Equiv.swap (1 : Fin 4) j
  have hzero : σ 0 = 0 := Equiv.swap_apply_of_ne_of_ne (by decide) hj
  have hone : σ 1 = j := Equiv.swap_apply_left _ _
  have hfirst : c (σ 0) = c (σ 1) := by simpa only [hzero, hone] using hclass
  have hnot : ¬ ∀ i, c (σ i) = c (σ 0) := by
    intro h
    apply hnonconstant
    intro i
    obtain ⟨k, rfl⟩ := σ.surjective i
    simpa only [hzero] using h k
  have hcomp (i : Fin 4) : ∃ j, i ≠ j ∧ c (σ i) = c (σ j) := by
    obtain ⟨k, hik, he⟩ := hcompanion (σ i)
    refine ⟨σ.symm k, ?_, by simpa only [Equiv.apply_symm_apply] using he⟩
    intro h
    exact hik (by simpa only [Equiv.apply_symm_apply] using congrArg σ h)
  have hsep : c (σ 2) ≠ c (σ 0) := by
    intro htwo
    have hthree : c (σ 3) ≠ c (σ 0) := by
      intro hthree
      apply hnot
      intro i
      fin_cases i
      · rfl
      · exact hfirst.symm
      · exact htwo
      · exact hthree
    obtain ⟨k, hk, he⟩ := hcomp 3
    fin_cases k
    · exact hthree he
    · exact hthree (he.trans hfirst.symm)
    · exact hthree (he.trans htwo)
    · exact hk rfl
  refine ⟨σ, hfirst, ?_, hsep.symm⟩
  obtain ⟨k, hk, he⟩ := hcomp 2
  fin_cases k
  · exact (hsep he).elim
  · exact (hsep (he.trans hfirst.symm)).elim
  · exact (hk rfl).elim
  · exact he

/-- The fixed `n = 4` case of the blocked finite statement in
`OMA.R_arxiv_1811_10503_R2.H1`. -/
theorem sun_four_blocked (G : Type) [CommGroup G] [Finite G]
    (hsmall : ∀ g : G, orderOf g ∉ Icc 2 (4 + 1)) (A : Finset G) (hA : A.card = 4)
    (hblocked : ∀ b ∈ A, ∃ a ∈ A, a ≠ b ∧ ∃ k : ℕ, 1 ≤ k ∧ k < 4 ∧ b ^ 4 = a ^ k) :
    ∃ a : Fin 4 → G, Function.Injective a ∧ Set.range a = (A : Set G) ∧
      Function.Injective (fun i : Fin 4 => a i ^ (i.val + 1)) := by
  classical
  let e : A ≃ Fin 4 := Fintype.equivFinOfCardEq (by simpa using hA)
  let a : Fin 4 → G := fun i => (e.symm i).val
  have ha : Function.Injective a := fun _ _ h => e.symm.injective (Subtype.ext h)
  have harange : Set.range a = (A : Set G) := by
    ext g
    constructor
    · rintro ⟨i, rfl⟩
      exact (e.symm i).property
    · intro hg
      exact ⟨e ⟨g, hg⟩, by simp [a]⟩
  have hcompanion (i : Fin 4) : ∃ j, i ≠ j ∧ zpowers (a i) = zpowers (a j) := by
    obtain ⟨g, hg, hgi, k, hk, hk4, he⟩ := hblocked (a i) (e.symm i).property
    have hg' : g ∈ Set.range a := harange ▸ hg
    obtain ⟨j, hj⟩ := hg'
    refine ⟨j, ?_, ?_⟩
    · rintro rfl
      exact hgi hj.symm
    · apply zpowers_eq_of_small_power_collision (n := 4) hsmall
        (i := 4) (j := k) (by decide) (by decide) (by omega) (by omega)
      rwa [hj]
  by_cases hclass : ∀ i, zpowers (a i) = zpowers (a 0)
  · obtain ⟨σ, hσ⟩ := exists_permutation_four_single_class hsmall a ha hclass
    refine ⟨a ∘ σ, ha.comp σ.injective, ?_, hσ⟩
    rw [Set.range_comp, σ.surjective.range_eq, Set.image_univ, harange]
  · obtain ⟨σ, hfirst, hsecond, hsep⟩ := two_classes_four (fun i => zpowers (a i)) hcompanion hclass
    let lo : Fin 2 → Fin 4 := fun j => ⟨2 * j.val, by have := j.isLt; omega⟩
    let hi : Fin 2 → Fin 4 := fun j => ⟨2 * j.val + 1, by have := j.isLt; omega⟩
    let x : Fin 2 → G := a ∘ σ ∘ lo
    let y : Fin 2 → G := a ∘ σ ∘ hi
    have hne (j : Fin 2) : x j ≠ y j := by
      apply (ha.comp σ.injective).ne
      intro h
      have he := congrArg Fin.val h
      dsimp [lo, hi] at he
      omega
    have hsame (j : Fin 2) : zpowers (x j) = zpowers (y j) := by
      fin_cases j
      · exact hfirst
      · exact hsecond
    have hdistinct (i j : Fin 2) (hij : i ≠ j) : zpowers (x i) ≠ zpowers (x j) := by
      fin_cases i <;> fin_cases j
      · exact (hij rfl).elim
      · exact hsep
      · exact hsep.symm
      · exact (hij rfl).elim
    have hr : Set.range x ∪ Set.range y = Set.range (a ∘ σ) := by
      ext g
      constructor
      · rintro (⟨j, rfl⟩ | ⟨j, rfl⟩)
        · exact ⟨lo j, rfl⟩
        · exact ⟨hi j, rfl⟩
      · rintro ⟨i, rfl⟩
        fin_cases i
        · exact Or.inl ⟨0, rfl⟩
        · exact Or.inr ⟨0, rfl⟩
        · exact Or.inl ⟨1, rfl⟩
        · exact Or.inr ⟨1, rfl⟩
    rw [Set.range_comp a (σ : Fin 4 → Fin 4), σ.surjective.range_eq, Set.image_univ, harange] at hr
    obtain ⟨b, hb, hbr, hpow⟩ := exists_distinct_powers_of_pairs 2 hsmall x y hne hsame hdistinct
    exact ⟨b, hb, hbr.trans hr, hpow⟩

end OMA.SunPowerPermutation

namespace OMA.R_arxiv_1811_10503_R2_H1_R1

def H1 : Prop := ∀ (G : Type) [CommGroup G] [Finite G],
  (∀ g : G, orderOf g ∉ Finset.Icc 2 (5 + 1)) → ∀ A : Finset G, A.card = 5 →
  (∀ b ∈ A, ∃ a ∈ A, a ≠ b ∧ ∃ k : ℕ, 1 ≤ k ∧ k < 5 ∧ b ^ 5 = a ^ k) →
  ∃ a : Fin 5 → G, Function.Injective a ∧ Set.range a = (A : Set G) ∧
    Function.Injective (fun i : Fin 5 => a i ^ (i.val + 1))

def H2 : Prop := ∀ (G : Type) [CommGroup G] [Finite G],
  (∀ g : G, orderOf g ∉ Finset.Icc 2 (6 + 1)) → ∀ A : Finset G, A.card = 6 →
  (∀ b ∈ A, ∃ a ∈ A, a ≠ b ∧ ∃ k : ℕ, 1 ≤ k ∧ k < 6 ∧ b ^ 6 = a ^ k) →
  ∃ a : Fin 6 → G, Function.Injective a ∧ Set.range a = (A : Set G) ∧
    Function.Injective (fun i : Fin 6 => a i ^ (i.val + 1))

def H3 : Prop := ∀ (G : Type) [CommGroup G] [Finite G],
  (∀ g : G, orderOf g ∉ Finset.Icc 2 (7 + 1)) → ∀ A : Finset G, A.card = 7 →
  (∀ b ∈ A, ∃ a ∈ A, a ≠ b ∧ ∃ k : ℕ, 1 ≤ k ∧ k < 7 ∧ b ^ 7 = a ^ k) →
  ∃ a : Fin 7 → G, Function.Injective a ∧ Set.range a = (A : Set G) ∧
    Function.Injective (fun i : Fin 7 => a i ^ (i.val + 1))

theorem main : H1 → H2 → H3 → OMA.R_arxiv_1811_10503_R2.H1 := by
  intro five six seven n hn hn'
  interval_cases n
  · exact OMA.SunPowerPermutation.sun_four_blocked
  · exact five
  · exact six
  · exact seven

end OMA.R_arxiv_1811_10503_R2_H1_R1
