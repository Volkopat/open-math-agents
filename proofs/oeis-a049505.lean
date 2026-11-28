import OMAStatements.S_oeis_a049505
import Mathlib

-- Problem: OEIS A049505: three congruences for the number of symmetric plane partitions in an n-cube
-- Source: https://oeis.org/A049505
-- Credit: @marcelopierry (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.S_oeis_a049505

section Integrality

private def tri (n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 n).biUnion fun i => (Finset.Icc i n).image fun j => (i, j)

private lemma mem_tri {n : ℕ} {p : ℕ × ℕ} :
    p ∈ tri n ↔ 1 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ n := by
  simp only [tri, Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_image]
  constructor
  · rintro ⟨i, ⟨hi1, hin⟩, j, ⟨hij, hjn⟩, rfl⟩
    exact ⟨hi1, hij, hjn⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨p.1, ⟨h1, le_trans h2 h3⟩, p.2, ⟨h2, h3⟩, rfl⟩

private lemma prod_tri_eq {α : Type*} [CommMonoid α] (n : ℕ) (f : ℕ → ℕ → α) :
    ∏ p ∈ tri n, f p.1 p.2 = ∏ i ∈ Finset.Icc 1 n, ∏ j ∈ Finset.Icc i n, f i j := by
  unfold tri
  rw [Finset.prod_biUnion]
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [Finset.prod_image]
    intro a _ b _ h
    exact (Prod.mk.inj h).2
  · intro i1 _ i2 _ hne
    show Disjoint _ _
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rcases Finset.mem_image.mp hx1 with ⟨_, _, rfl⟩
    rcases Finset.mem_image.mp hx2 with ⟨_, _, h2⟩
    exact hne (Prod.mk.inj h2).1.symm

private lemma a_eq_prod_tri (n : ℕ) :
    a n = (∏ p ∈ tri n, ((p.1 + p.2 + n - 1 : ℕ) : ℚ)) /
          (∏ p ∈ tri n, ((p.1 + p.2 - 1 : ℕ) : ℚ)) := by
  unfold a
  rw [← prod_tri_eq n (fun i j => ((i + j + n - 1 : ℕ) : ℚ) / ((i + j - 1 : ℕ) : ℚ)),
      Finset.prod_div_distrib]

private def cnt (n s : ℕ) : ℕ :=
  ((tri n).filter fun p => p.1 + p.2 - 1 = s).card

private lemma cnt_eq (n s : ℕ) :
    cnt n s =
      if 1 ≤ s ∧ s ≤ n then (s + 1) / 2
      else if n < s ∧ s ≤ 2 * n - 1 then (2 * n - s + 1) / 2
      else 0 := by
  unfold cnt
  have himg : ((tri n).filter fun p => p.1 + p.2 - 1 = s).image Prod.fst =
      Finset.Icc (max 1 (s + 1 - n)) ((s + 1) / 2) := by
    ext i
    simp only [Finset.mem_image, Finset.mem_filter, mem_tri, Finset.mem_Icc, max_le_iff]
    constructor
    · rintro ⟨⟨i', j⟩, ⟨⟨h1, h2, h3⟩, hs⟩, rfl⟩
      dsimp at h1 h2 h3 hs
      omega
    · rintro ⟨⟨hi1, his⟩, hi2⟩
      by_cases hs0 : s = 0
      · omega
      · refine ⟨⟨i, s + 1 - i⟩, ⟨⟨hi1, by omega, by omega⟩, by dsimp; omega⟩, rfl⟩
  have hinj : Set.InjOn Prod.fst (↑((tri n).filter fun p => p.1 + p.2 - 1 = s) : Set (ℕ × ℕ)) := by
    intro p1 hp1 p2 hp2 hfst
    simp only [Finset.mem_coe, Finset.mem_filter, mem_tri] at hp1 hp2
    exact Prod.ext hfst (by omega)
  rw [← Finset.card_image_of_injOn hinj, himg, Nat.card_Icc]
  split_ifs <;> omega

private lemma card_Icc_block_dvd (a Q c : ℕ) (hQ : 1 ≤ Q) :
    ((Finset.Icc (a + 1) (a + Q)).filter fun i => Q ∣ i + c).card = 1 := by
  let x : ℕ := a + Q - ((a + c) % Q)
  have hx_mem : x ∈ (Finset.Icc (a + 1) (a + Q)).filter fun i => Q ∣ i + c := by
    have hlt : (a + c) % Q < Q := Nat.mod_lt _ (by omega)
    simp only [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨by dsimp [x]; omega, by dsimp [x]; omega⟩, ?_⟩
    have hdiv : a + c = Q * ((a + c) / Q) + (a + c) % Q := (Nat.div_add_mod (a + c) Q).symm
    have heq : x + c = Q * ((a + c) / Q + 1) := by
      rw [Nat.mul_add, mul_one]; dsimp [x]; omega
    exact ⟨(a + c) / Q + 1, heq⟩
  rw [Finset.card_eq_one]
  refine ⟨x, ?_⟩
  ext i
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨hi1, hi2⟩, ⟨k, hk⟩⟩
    have hx' := Finset.mem_filter.mp hx_mem
    have hx_bounds := Finset.mem_Icc.mp hx'.1
    rcases hx'.2 with ⟨kx, hkx⟩
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hkx_gt : k < kx := by nlinarith
      have hsub : Q * (kx - k) = x - i := by rw [Nat.mul_sub]; omega
      have : Q ≤ x - i := by
        calc Q = Q * 1 := (mul_one Q).symm
          _ ≤ Q * (kx - k) := Nat.mul_le_mul_left Q (by omega)
          _ = x - i := hsub
      omega
    · have hk_gt : kx < k := by nlinarith
      have hsub : Q * (k - kx) = i - x := by rw [Nat.mul_sub]; omega
      have : Q ≤ i - x := by
        calc Q = Q * 1 := (mul_one Q).symm
          _ ≤ Q * (k - kx) := Nat.mul_le_mul_left Q (by omega)
          _ = i - x := hsub
      omega
  · rintro rfl
    have hx' := Finset.mem_filter.mp hx_mem
    exact ⟨Finset.mem_Icc.mp hx'.1, hx'.2⟩

private lemma card_Icc_mul_dvd (q Q c : ℕ) (hQ : 1 ≤ Q) :
    ((Finset.Icc 1 (q * Q)).filter fun i => Q ∣ i + c).card = q := by
  induction q with
  | zero => simp
  | succ q ih =>
    have hunion : Finset.Icc 1 ((q + 1) * Q) =
        Finset.Icc 1 (q * Q) ∪ Finset.Icc (q * Q + 1) (q * Q + Q) := by
      ext i; simp only [Finset.mem_Icc, Finset.mem_union]
      have : (q + 1) * Q = q * Q + Q := by ring
      omega
    have hdisj : Disjoint (Finset.Icc 1 (q * Q)) (Finset.Icc (q * Q + 1) (q * Q + Q)) := by
      rw [Finset.disjoint_left]
      intro i h1 h2
      simp only [Finset.mem_Icc] at h1 h2; omega
    rw [hunion, Finset.filter_union, Finset.card_union_of_disjoint
        (Finset.disjoint_filter_filter hdisj), ih, card_Icc_block_dvd (q * Q) Q c hQ]

private lemma card_Icc_mul_two_mul_dvd_odd (q Q c : ℕ) (hQ : 1 ≤ Q) (hodd : Odd Q) :
    ((Finset.Icc 1 (q * Q)).filter fun i => Q ∣ 2 * i + c).card = q := by
  have hcop : Nat.Coprime 2 Q := by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
    rcases hodd with ⟨k, rfl⟩; omega
  have hblock : ∀ a : ℕ, ((Finset.Icc (a + 1) (a + Q)).filter fun i => Q ∣ 2 * i + c).card = 1 := by
    intro a
    -- In ZMod Q, 2 is a unit, so 2 * i + c = 0 has a unique solution modulo Q
    haveI : NeZero Q := ⟨by omega⟩
    let u2 : (ZMod Q)ˣ := ZMod.unitOfCoprime 2 hcop
    let target : ZMod Q := -(u2⁻¹ : ZMod Q) * (c : ZMod Q)
    -- Map i ↦ (i : ZMod Q) is a bijection from Icc (a+1) (a+Q) to ZMod Q
    have hbij : ∃! i ∈ Finset.Icc (a + 1) (a + Q), (i : ZMod Q) = target := by
      let r : ℕ := (target.val + Q - (a + 1) % Q) % Q
      let x : ℕ := a + 1 + r
      have hx_mem : x ∈ Finset.Icc (a + 1) (a + Q) := by
        have hr : r < Q := Nat.mod_lt _ (by omega)
        simp only [Finset.mem_Icc]; exact ⟨by omega, by omega⟩
      have hx_eq : (x : ZMod Q) = target := by
        have hmod : x ≡ target.val [MOD Q] := by
          have ht : target.val < Q := ZMod.val_lt target
          have ha : (a + 1) % Q < Q := Nat.mod_lt _ (by omega)
          have h1 : x ≡ (a + 1) % Q + (target.val + Q - (a + 1) % Q) [MOD Q] :=
            Nat.ModEq.add (Nat.mod_modEq (a + 1) Q).symm (Nat.mod_modEq _ Q)
          have h2 : (a + 1) % Q + (target.val + Q - (a + 1) % Q) = target.val + Q := by omega
          rw [h2] at h1
          exact h1.trans (Nat.ModEq.add_left target.val (Nat.modEq_zero_iff_dvd.mpr dvd_rfl))
        rw [← ZMod.natCast_zmod_val target, ZMod.natCast_eq_natCast_iff]
        exact hmod
      refine ⟨x, ⟨hx_mem, hx_eq⟩, ?_⟩
      rintro y ⟨hy_mem, hy_eq⟩
      have hmod : y % Q = x % Q := by
        have := hy_eq.trans hx_eq.symm
        rwa [ZMod.natCast_eq_natCast_iff] at this
      have hxb := Finset.mem_Icc.mp hx_mem
      have hyb := Finset.mem_Icc.mp hy_mem
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hdvd : Q ∣ x - y := (Nat.modEq_iff_dvd' (le_of_lt hlt)).mp hmod
        have := Nat.le_of_dvd (by omega) hdvd; omega
      · have hdvd : Q ∣ y - x := (Nat.modEq_iff_dvd' (le_of_lt hgt)).mp hmod.symm
        have := Nat.le_of_dvd (by omega) hdvd; omega
    have hiff : ∀ i : ℕ, (Q ∣ 2 * i + c) ↔ ((i : ZMod Q) = target) := by
      intro i
      rw [← ZMod.natCast_eq_zero_iff]
      push_cast
      have hu2 : (u2 : ZMod Q) = (2 : ZMod Q) := ZMod.coe_unitOfCoprime 2 hcop
      constructor
      · intro h0
        have h1 : (u2 : ZMod Q) * (i : ZMod Q) = -(c : ZMod Q) := by
          rw [hu2]; exact eq_neg_of_add_eq_zero_left h0
        calc (i : ZMod Q) = (u2⁻¹ : ZMod Q) * ((u2 : ZMod Q) * (i : ZMod Q)) := by
              rw [← mul_assoc]; simp
          _ = (u2⁻¹ : ZMod Q) * (-(c : ZMod Q)) := by rw [h1]
          _ = target := by dsimp [target]; ring
      · intro hi
        rw [hi, ← hu2]; dsimp [target]
        have : (u2 : ZMod Q) * (-(u2⁻¹ : ZMod Q) * (c : ZMod Q)) = -(c : ZMod Q) := by
          rw [neg_mul, mul_neg, ← mul_assoc]; simp
        rw [this, neg_add_cancel]
    rcases hbij with ⟨x, ⟨hx_mem, hx_eq⟩, huniq⟩
    rw [Finset.card_eq_one]
    refine ⟨x, ?_⟩
    ext i
    simp only [Finset.mem_filter, Finset.mem_singleton, hiff]
    exact ⟨fun ⟨hm, he⟩ => huniq i ⟨hm, he⟩, fun h => h ▸ ⟨hx_mem, hx_eq⟩⟩
  induction q with
  | zero => simp
  | succ q ih =>
    have hunion : Finset.Icc 1 ((q + 1) * Q) =
        Finset.Icc 1 (q * Q) ∪ Finset.Icc (q * Q + 1) (q * Q + Q) := by
      ext i; simp only [Finset.mem_Icc, Finset.mem_union]
      have : (q + 1) * Q = q * Q + Q := by ring
      omega
    have hdisj : Disjoint (Finset.Icc 1 (q * Q)) (Finset.Icc (q * Q + 1) (q * Q + Q)) := by
      rw [Finset.disjoint_left]
      intro i h1 h2
      simp only [Finset.mem_Icc] at h1 h2; omega
    rw [hunion, Finset.filter_union, Finset.card_union_of_disjoint
        (Finset.disjoint_filter_filter hdisj), ih, hblock (q * Q)]

private lemma two_mul_card_tri_dvd (m Q c : ℕ) :
    2 * ((tri m).filter fun p => Q ∣ p.1 + p.2 + c).card =
      (((Finset.Icc 1 m) ×ˢ (Finset.Icc 1 m)).filter fun p => Q ∣ p.1 + p.2 + c).card +
      ((Finset.Icc 1 m).filter fun i => Q ∣ 2 * i + c).card := by
  let S := ((Finset.Icc 1 m) ×ˢ (Finset.Icc 1 m)).filter fun p => Q ∣ p.1 + p.2 + c
  let T := (tri m).filter fun p => Q ∣ p.1 + p.2 + c
  let L := S.filter fun p => p.1 < p.2
  let D := S.filter fun p => p.1 = p.2
  let U := S.filter fun p => p.2 < p.1
  have hT_eq : T = L ∪ D := by
    ext ⟨i, j⟩
    simp only [T, L, D, S, Finset.mem_filter, mem_tri, Finset.mem_union, Finset.mem_product,
      Finset.mem_Icc]
    omega
  have hLD_disj : Disjoint L D := by
    rw [Finset.disjoint_left]; intro p h1 h2
    simp only [L, D, Finset.mem_filter] at h1 h2; omega
  have hS_eq : S = (L ∪ D) ∪ U := by
    ext ⟨i, j⟩
    simp only [S, L, D, U, Finset.mem_filter, Finset.mem_union]
    constructor
    · intro h
      rcases lt_trichotomy i j with hlt | rfl | hgt
      · exact Or.inl (Or.inl ⟨h, hlt⟩)
      · exact Or.inl (Or.inr ⟨h, rfl⟩)
      · exact Or.inr ⟨h, hgt⟩
    · rintro ((⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩) <;> exact h
  have hLDU_disj : Disjoint (L ∪ D) U := by
    rw [Finset.disjoint_left]; intro p h1 h2
    simp only [L, D, U, Finset.mem_union, Finset.mem_filter] at h1 h2; omega
  have hU_card : U.card = L.card := by
    have heq : U = L.image Prod.swap := by
      ext ⟨i, j⟩
      simp only [U, L, S, Finset.mem_filter, Finset.mem_image, Finset.mem_product, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨⟨hi, hj⟩, hdvd⟩, hji⟩
        exact ⟨⟨j, i⟩, ⟨⟨⟨hj, hi⟩, by rwa [add_comm j i]⟩, hji⟩, rfl⟩
      · rintro ⟨⟨a, b⟩, ⟨⟨⟨ha, hb⟩, hdvd⟩, hab⟩, hswap⟩
        rcases Prod.mk.inj hswap with ⟨rfl, rfl⟩
        exact ⟨⟨⟨hb, ha⟩, by rwa [add_comm b a]⟩, hab⟩
    rw [heq, Finset.card_image_of_injective _ Prod.swap_injective]
  have hD_card : D.card = ((Finset.Icc 1 m).filter fun i => Q ∣ 2 * i + c).card := by
    have heq : D = ((Finset.Icc 1 m).filter fun i => Q ∣ 2 * i + c).image (fun i => (i, i)) := by
      ext ⟨i, j⟩
      simp only [D, S, Finset.mem_filter, Finset.mem_image, Finset.mem_product, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨⟨hi, _⟩, hdvd⟩, rfl⟩
        exact ⟨i, ⟨hi, by rwa [two_mul]⟩, rfl⟩
      · rintro ⟨a, ⟨ha, hdvd⟩, hmk⟩
        rcases Prod.mk.inj hmk with ⟨rfl, rfl⟩
        exact ⟨⟨⟨ha, ha⟩, by rwa [two_mul] at hdvd⟩, rfl⟩
    rw [heq, Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).1)]
  have hT_c : T.card = L.card + D.card := by rw [hT_eq, Finset.card_union_of_disjoint hLD_disj]
  have hS_c : S.card = T.card + L.card := by
    rw [hS_eq, Finset.card_union_of_disjoint hLDU_disj, ← hT_eq, hU_card]
  change 2 * T.card = S.card + ((Finset.Icc 1 m).filter fun i => Q ∣ 2 * i + c).card
  omega

private lemma card_dvd_num_ge_den (n Q : ℕ) (hQ : 1 ≤ Q) :
    ((tri n).filter fun p => Q ∣ p.1 + p.2 - 1).card ≤
    ((tri n).filter fun p => Q ∣ p.1 + p.2 + n - 1).card := by
  let q := n / Q
  let r := n % Q
  let m := q * Q
  have hnr : m + r = n := by
    dsimp only [m, q, r]; rw [mul_comm]; exact Nat.div_add_mod n Q
  have hrQ : r < Q := Nat.mod_lt n (by omega)
  let P1 : Finset (ℕ × ℕ) := (Finset.Icc 1 m) ×ˢ (Finset.Icc (m + 1) n)
  let P2 : Finset (ℕ × ℕ) := tri m
  let P3 : Finset (ℕ × ℕ) := (tri r).image fun p => (p.1 + m, p.2 + m)
  have htri_eq : tri n = (P1 ∪ P2) ∪ P3 := by
    ext ⟨i, j⟩
    simp only [mem_tri, Finset.mem_union, P1, P2, P3, Finset.mem_product, Finset.mem_Icc,
      Finset.mem_image]
    constructor
    · rintro ⟨hi1, hij, hjn⟩
      by_cases hjm : j ≤ m
      · exact Or.inl (Or.inr ⟨hi1, hij, hjm⟩)
      · by_cases him : i ≤ m
        · exact Or.inl (Or.inl ⟨⟨hi1, him⟩, ⟨by omega, hjn⟩⟩)
        · exact Or.inr ⟨⟨i - m, j - m⟩, ⟨by omega, by omega, by omega⟩, by ext <;> dsimp <;> omega⟩
    · rintro ((⟨⟨hi1, him⟩, ⟨hjm, hjn⟩⟩ | ⟨hi1, hij, hjm⟩) | ⟨⟨a, b⟩, ⟨ha1, hab, hbr⟩, heq⟩)
      · exact ⟨hi1, by omega, hjn⟩
      · exact ⟨hi1, hij, by omega⟩
      · rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
        exact ⟨by omega, by omega, by omega⟩
  have h12 : Disjoint P1 P2 := by
    rw [Finset.disjoint_left]; intro p h1 h2
    simp only [P1, P2, Finset.mem_product, Finset.mem_Icc, mem_tri] at h1 h2; omega
  have h123 : Disjoint (P1 ∪ P2) P3 := by
    rw [Finset.disjoint_left]; intro p h1 h2
    simp only [P1, P2, P3, Finset.mem_union, Finset.mem_product, Finset.mem_Icc, mem_tri,
      Finset.mem_image] at h1 h2
    rcases h2 with ⟨⟨a, b⟩, ⟨ha1, _, _⟩, rfl⟩
    rcases h1 with ⟨⟨_, him⟩, _⟩ | ⟨_, _, hjm⟩ <;> (dsimp at *; omega)
  have hsplit : ∀ (P : ℕ × ℕ → Prop) [DecidablePred P],
      ((tri n).filter P).card = (P1.filter P).card + (P2.filter P).card + (P3.filter P).card := by
    intro P _
    rw [htri_eq, Finset.filter_union,
        Finset.card_union_of_disjoint (Finset.disjoint_filter_filter h123),
        Finset.filter_union,
        Finset.card_union_of_disjoint (Finset.disjoint_filter_filter h12)]
  rw [hsplit, hsplit]
  -- Piece 1: P1 = Icc 1 m × Icc (m+1) n, equal counts on both sides
  have hP1 : (P1.filter fun p => Q ∣ p.1 + p.2 - 1).card =
      (P1.filter fun p => Q ∣ p.1 + p.2 + n - 1).card := by
    have hcard_prod : ∀ c : ℕ, (P1.filter fun p => Q ∣ p.1 + p.2 + c).card = q * r := by
      intro c
      have hsum : (P1.filter fun p => Q ∣ p.1 + p.2 + c).card =
          ∑ j ∈ Finset.Icc (m + 1) n, ((Finset.Icc 1 m).filter fun i => Q ∣ i + (j + c)).card := by
        rw [Finset.card_eq_sum_ones, Finset.sum_filter]
        dsimp only [P1]
        rw [Finset.sum_product_right]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.card_eq_sum_ones, Finset.sum_filter]
        refine Finset.sum_congr rfl fun i _ => by rw [add_assoc]
      rw [hsum]
      have hconst : ∀ j ∈ Finset.Icc (m + 1) n,
          ((Finset.Icc 1 m).filter fun i => Q ∣ i + (j + c)).card = q :=
        fun j _ => card_Icc_mul_dvd q Q (j + c) hQ
      rw [Finset.sum_congr rfl hconst, Finset.sum_const, Nat.card_Icc, smul_eq_mul]
      have : n + 1 - (m + 1) = r := by omega
      rw [this, mul_comm]
    have hL : P1.filter (fun p => Q ∣ p.1 + p.2 - 1) = P1.filter (fun p => Q ∣ p.1 + p.2 + (Q - 1)) := by
      refine Finset.filter_congr fun p hp => ?_
      have hp1 : 1 ≤ p.1 := (Finset.mem_Icc.mp (Finset.mem_product.mp hp).1).1
      have heq : p.1 + p.2 + (Q - 1) = (p.1 + p.2 - 1) + Q := by omega
      rw [heq, Nat.dvd_add_self_right]
    have hR : P1.filter (fun p => Q ∣ p.1 + p.2 + n - 1) = P1.filter (fun p => Q ∣ p.1 + p.2 + (n + Q - 1)) := by
      refine Finset.filter_congr fun p hp => ?_
      have hp1 : 1 ≤ p.1 := (Finset.mem_Icc.mp (Finset.mem_product.mp hp).1).1
      have heq : p.1 + p.2 + (n + Q - 1) = (p.1 + p.2 + n - 1) + Q := by omega
      rw [heq, Nat.dvd_add_self_right]
    rw [hL, hR, hcard_prod (Q - 1), hcard_prod (n + Q - 1)]
  -- Piece 2: P2 = tri m
  have hP2 : (P2.filter fun p => Q ∣ p.1 + p.2 - 1).card ≤
      (P2.filter fun p => Q ∣ p.1 + p.2 + n - 1).card := by
    have hL : P2.filter (fun p => Q ∣ p.1 + p.2 - 1) = P2.filter (fun p => Q ∣ p.1 + p.2 + (Q - 1)) := by
      refine Finset.filter_congr fun p hp => ?_
      have hp1 : 1 ≤ p.1 := (mem_tri.mp hp).1
      have heq : p.1 + p.2 + (Q - 1) = (p.1 + p.2 - 1) + Q := by omega
      rw [heq, Nat.dvd_add_self_right]
    have hR : P2.filter (fun p => Q ∣ p.1 + p.2 + n - 1) = P2.filter (fun p => Q ∣ p.1 + p.2 + (n + Q - 1)) := by
      refine Finset.filter_congr fun p hp => ?_
      have hp1 : 1 ≤ p.1 := (mem_tri.mp hp).1
      have heq : p.1 + p.2 + (n + Q - 1) = (p.1 + p.2 + n - 1) + Q := by omega
      rw [heq, Nat.dvd_add_self_right]
    rw [hL, hR]
    have hsq : ∀ c : ℕ, (((Finset.Icc 1 m) ×ˢ (Finset.Icc 1 m)).filter fun p => Q ∣ p.1 + p.2 + c).card = q * m := by
      intro c
      rw [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product_right]
      have hinner : ∀ j ∈ Finset.Icc 1 m,
          (∑ i ∈ Finset.Icc 1 m, if Q ∣ i + j + c then 1 else 0) = q := by
        intro j _
        rw [← Finset.sum_filter, ← Finset.card_eq_sum_ones]
        have := card_Icc_mul_dvd q Q (j + c) hQ
        dsimp only [m]
        convert this using 2; ext i; simp [add_assoc]
      rw [Finset.sum_congr rfl hinner, Finset.sum_const, Nat.card_Icc, smul_eq_mul]
      have : m + 1 - 1 = m := by omega
      rw [this, mul_comm]
    have h2L := two_mul_card_tri_dvd m Q (Q - 1)
    have h2R := two_mul_card_tri_dvd m Q (n + Q - 1)
    rw [hsq (Q - 1)] at h2L
    rw [hsq (n + Q - 1)] at h2R
    have hdiag : ((Finset.Icc 1 m).filter fun i => Q ∣ 2 * i + (Q - 1)).card ≤
        ((Finset.Icc 1 m).filter fun i => Q ∣ 2 * i + (n + Q - 1)).card := by
      rcases Nat.even_or_odd Q with ⟨t, ht⟩ | hodd
      · have hemp : ((Finset.Icc 1 m).filter fun i => Q ∣ 2 * i + (Q - 1)) = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]
          rintro i hi
          rcases (Finset.mem_filter.mp hi).2 with ⟨k, hk⟩
          have hQk : Q * k = 2 * (t * k) := by rw [ht]; ring
          omega
        rw [hemp, Finset.card_empty]; exact Nat.zero_le _
      · rw [card_Icc_mul_two_mul_dvd_odd q Q (Q - 1) hQ hodd,
            card_Icc_mul_two_mul_dvd_odd q Q (n + Q - 1) hQ hodd]
    dsimp only [P2]
    omega
  -- Piece 3: P3 = shifted tri r
  have hP3 : (P3.filter fun p => Q ∣ p.1 + p.2 - 1).card ≤
      (P3.filter fun p => Q ∣ p.1 + p.2 + n - 1).card := by
    have h2mq : Q * (2 * q) = m + m := by dsimp only [m]; ring
    have hmq : Q * q = m := by dsimp only [m]; ring
    have hshift : ∀ c : ℕ,
        (P3.filter fun p => Q ∣ p.1 + p.2 + c - 1).card =
        ((tri r).filter fun p => Q ∣ p.1 + p.2 + c - 1).card := by
      intro c
      have heq : P3.filter (fun p => Q ∣ p.1 + p.2 + c - 1) =
          ((tri r).filter fun p => Q ∣ p.1 + p.2 + c - 1).image (fun p => (p.1 + m, p.2 + m)) := by
        ext ⟨i, j⟩
        simp only [P3, Finset.mem_filter, Finset.mem_image, mem_tri]
        constructor
        · rintro ⟨⟨⟨a, b⟩, hab, heq⟩, hdvd⟩
          rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
          refine ⟨⟨a, b⟩, ⟨hab, ?_⟩, rfl⟩
          have h1 : a + m + (b + m) + c - 1 = (a + b + c - 1) + Q * (2 * q) := by omega
          rw [h1] at hdvd
          exact (Nat.dvd_add_left (dvd_mul_right Q (2 * q))).mp hdvd
        · rintro ⟨⟨a, b⟩, ⟨hab, hdvd⟩, heq⟩
          rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
          refine ⟨⟨⟨a, b⟩, hab, rfl⟩, ?_⟩
          have h1 : a + m + (b + m) + c - 1 = (a + b + c - 1) + Q * (2 * q) := by omega
          rw [h1]
          exact dvd_add hdvd (dvd_mul_right Q (2 * q))
      rw [heq, Finset.card_image_of_injective _ (fun p1 p2 h => by
        rcases Prod.mk.inj h with ⟨h1, h2⟩; exact Prod.ext (by omega) (by omega))]
    have hL3 : (P3.filter fun p => Q ∣ p.1 + p.2 - 1).card =
        ((tri r).filter fun p => Q ∣ p.1 + p.2 - 1).card := by
      simpa using hshift 0
    have hR3 : (P3.filter fun p => Q ∣ p.1 + p.2 + n - 1).card =
        ((tri r).filter fun p => Q ∣ p.1 + p.2 + r - 1).card := by
      rw [hshift n]
      congr 1
      refine Finset.filter_congr fun p hp => ?_
      have hp1 : 1 ≤ p.1 := (mem_tri.mp hp).1
      have heq : p.1 + p.2 + n - 1 = (p.1 + p.2 + r - 1) + Q * q := by omega
      rw [heq, Nat.dvd_add_left (dvd_mul_right Q q)]
    rw [hL3, hR3]
    by_cases hsmall : 2 * r ≤ Q
    · have hemp : ((tri r).filter fun p => Q ∣ p.1 + p.2 - 1) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro p hp
        have hm := mem_tri.mp (Finset.mem_filter.mp hp).1
        have hdvd := (Finset.mem_filter.mp hp).2
        have := Nat.le_of_dvd (by omega) hdvd
        omega
      rw [hemp, Finset.card_empty]; exact Nat.zero_le _
    · push Not at hsmall
      have hL_eq : ((tri r).filter fun p => Q ∣ p.1 + p.2 - 1) =
          ((tri r).filter fun p => p.1 + p.2 - 1 = Q) := by
        refine Finset.filter_congr fun p hp => ?_
        have hm := mem_tri.mp hp
        constructor
        · rintro ⟨k, hk⟩
          have hpos : 1 ≤ p.1 + p.2 - 1 := by omega
          have hlt2Q : p.1 + p.2 - 1 < 2 * Q := by omega
          have hk1 : 1 ≤ k := by nlinarith
          have hk2 : k ≤ 1 := by nlinarith
          have hkeq : k = 1 := by omega
          rw [hkeq, mul_one] at hk
          exact hk
        · intro heq; rw [heq]
      have hR_sub : ((tri r).filter fun p => p.1 + p.2 - 1 = Q - r) ∪
          ((tri r).filter fun p => p.1 + p.2 - 1 = 2 * Q - r) ⊆
          ((tri r).filter fun p => Q ∣ p.1 + p.2 + r - 1) := by
        intro p hp
        simp only [Finset.mem_union, Finset.mem_filter] at hp ⊢
        rcases hp with ⟨hpt, heq⟩ | ⟨hpt, heq⟩
        · have hm := mem_tri.mp hpt
          exact ⟨hpt, ⟨1, by omega⟩⟩
        · have hm := mem_tri.mp hpt
          exact ⟨hpt, ⟨2, by omega⟩⟩
      have hR_disj : Disjoint ((tri r).filter fun p => p.1 + p.2 - 1 = Q - r)
          ((tri r).filter fun p => p.1 + p.2 - 1 = 2 * Q - r) := by
        rw [Finset.disjoint_left]; intro p h1 h2
        simp only [Finset.mem_filter] at h1 h2; omega
      have hle_R := Finset.card_le_card hR_sub
      rw [Finset.card_union_of_disjoint hR_disj] at hle_R
      rw [hL_eq]
      change cnt r Q ≤ _
      have hcnt_le : cnt r Q ≤ cnt r (Q - r) + cnt r (2 * Q - r) := by
        rw [cnt_eq, cnt_eq, cnt_eq]
        split_ifs <;> omega
      exact le_trans hcnt_le hle_R
  omega

private lemma factorization_eq_sum_card_pow_dvd {ι : Type*} (S : Finset ι) (f : ι → ℕ)
    (hf : ∀ x ∈ S, 0 < f x) (q : ℕ) (hq : q.Prime) (M : ℕ)
    (hM : ∀ x ∈ S, f x < q ^ (M + 1)) :
    (∏ x ∈ S, f x).factorization q =
      ∑ k ∈ Finset.Icc 1 M, (S.filter fun x => q ^ k ∣ f x).card := by
  rw [Nat.factorization_prod (fun x hx => Nat.ne_of_gt (hf x hx))]
  simp only [Finsupp.finset_sum_apply]
  have hsingle : ∀ x ∈ S, (f x).factorization q =
      ∑ k ∈ Finset.Icc 1 M, if q ^ k ∣ f x then 1 else 0 := by
    intro x hx
    have hpos : f x ≠ 0 := Nat.ne_of_gt (hf x hx)
    have hlt_exp : (f x).factorization q ≤ M := by
      by_contra hgt; push Not at hgt
      have hdvd : q ^ (M + 1) ∣ f x :=
        (hq.pow_dvd_iff_le_factorization hpos).mpr hgt
      have := Nat.le_of_dvd (hf x hx) hdvd
      have := hM x hx
      omega
    have hfilt : (Finset.Icc 1 M).filter (fun k => q ^ k ∣ f x) =
        Finset.Icc 1 ((f x).factorization q) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_Icc, hq.pow_dvd_iff_le_factorization hpos]
      omega
    rw [← Finset.sum_filter, ← Finset.card_eq_sum_ones, hfilt, Nat.card_Icc]
    omega
  rw [Finset.sum_congr rfl hsingle, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]

private lemma a_eq_nat (n : ℕ) : ∃ z : ℕ, a n = (z : ℚ) := by
  let N : ℕ := ∏ p ∈ tri n, (p.1 + p.2 + n - 1)
  let D : ℕ := ∏ p ∈ tri n, (p.1 + p.2 - 1)
  have hNpos : 0 < N := Finset.prod_pos fun p hp => by have := mem_tri.mp hp; omega
  have hDpos : 0 < D := Finset.prod_pos fun p hp => by have := mem_tri.mp hp; omega
  have hdvd : D ∣ N := by
    rw [← Nat.factorization_le_iff_dvd (Nat.ne_of_gt hDpos) (Nat.ne_of_gt hNpos)]
    intro q
    by_cases hq : q.Prime
    · let M := 3 * n + 1
      have hq2 : 2 ≤ q := hq.two_le
      have hpow_gt : ∀ x : ℕ, x ≤ 3 * n → x < q ^ (M + 1) := by
        intro x hx
        have h1 : M + 1 < 2 ^ (M + 1) := Nat.lt_two_pow_self
        have h2 : 2 ^ (M + 1) ≤ q ^ (M + 1) := Nat.pow_le_pow_left hq2 (M + 1)
        omega
      rw [factorization_eq_sum_card_pow_dvd (tri n) (fun p => p.1 + p.2 - 1)
            (fun p hp => by have := mem_tri.mp hp; omega) q hq M
            (fun p hp => hpow_gt _ (by have := mem_tri.mp hp; omega)),
          factorization_eq_sum_card_pow_dvd (tri n) (fun p => p.1 + p.2 + n - 1)
            (fun p hp => by have := mem_tri.mp hp; omega) q hq M
            (fun p hp => hpow_gt _ (by have := mem_tri.mp hp; omega))]
      refine Finset.sum_le_sum fun k _ => ?_
      exact card_dvd_num_ge_den n (q ^ k) (Nat.one_le_pow k q (by omega))
    · simp [Nat.factorization_eq_zero_of_not_prime _ hq]
  rcases hdvd with ⟨z, hz⟩
  refine ⟨z, ?_⟩
  rw [a_eq_prod_tri]
  have hN : (N : ℚ) = ∏ p ∈ tri n, ((p.1 + p.2 + n - 1 : ℕ) : ℚ) := by simp [N]
  have hD : (D : ℚ) = ∏ p ∈ tri n, ((p.1 + p.2 - 1 : ℕ) : ℚ) := by simp [D]
  rw [← hN, ← hD, hz, Nat.cast_mul, mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hDpos))]

end Integrality

section MasterCongruence

private lemma a_odd_formula (n : ℕ) (hodd : Odd n) :
    a n = (2 : ℚ) ^ ((n + 1) / 2) *
      ∏ r ∈ Finset.Icc 1 (n - 1),
        ((((n + r : ℕ) : ℚ) / (r : ℚ)) ^ ((r + 1) / 2) *
         (((2 * n + r : ℕ) : ℚ) / ((n + r : ℕ) : ℚ)) ^ ((n + 1) / 2 - (r + 1) / 2)) := by
  rcases hodd with ⟨m, rfl⟩
  have hm1 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
  rw [hm1, a_eq_prod_tri]
  rw [← Finset.prod_div_distrib]
  have hmaps : ∀ p ∈ tri (2 * m + 1), p.1 + p.2 - 1 ∈ Finset.Icc 1 (2 * (2 * m + 1) - 1) := by
    intro p hp; have := mem_tri.mp hp; simp only [Finset.mem_Icc]; omega
  rw [← Finset.prod_fiberwise_of_maps_to hmaps]
  have hfiber : ∀ s ∈ Finset.Icc 1 (2 * (2 * m + 1) - 1),
      (∏ p ∈ (tri (2 * m + 1)).filter (fun p => p.1 + p.2 - 1 = s),
        ((p.1 + p.2 + (2 * m + 1) - 1 : ℕ) : ℚ) / ((p.1 + p.2 - 1 : ℕ) : ℚ)) =
      (((s + (2 * m + 1) : ℕ) : ℚ) / (s : ℚ)) ^ cnt (2 * m + 1) s := by
    intro s _
    have hconst : ∀ p ∈ (tri (2 * m + 1)).filter (fun p => p.1 + p.2 - 1 = s),
        ((p.1 + p.2 + (2 * m + 1) - 1 : ℕ) : ℚ) / ((p.1 + p.2 - 1 : ℕ) : ℚ) =
        (((s + (2 * m + 1) : ℕ) : ℚ) / (s : ℚ)) := by
      intro p hp
      have hm := mem_tri.mp (Finset.mem_filter.mp hp).1
      have hs := (Finset.mem_filter.mp hp).2
      have h1 : p.1 + p.2 + (2 * m + 1) - 1 = s + (2 * m + 1) := by omega
      rw [h1, hs]
    rw [Finset.prod_congr rfl hconst, Finset.prod_const]
    rfl
  rw [Finset.prod_congr rfl hfiber]
  -- Split Icc 1 (4m + 1) into Icc 1 (2m), {2m + 1}, and Icc (2m + 2) (4m + 1)
  have hsplit1 : Finset.Icc 1 (2 * (2 * m + 1) - 1) =
      Finset.Icc 1 (2 * m) ∪ ({2 * m + 1} ∪ Finset.Icc (2 * m + 2) (4 * m + 1)) := by
    ext s; simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_singleton]; omega
  have hd1 : Disjoint (Finset.Icc 1 (2 * m)) ({2 * m + 1} ∪ Finset.Icc (2 * m + 2) (4 * m + 1)) := by
    rw [Finset.disjoint_left]; intro s h1 h2
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_singleton] at h1 h2; omega
  have hd2 : Disjoint ({2 * m + 1} : Finset ℕ) (Finset.Icc (2 * m + 2) (4 * m + 1)) := by
    rw [Finset.disjoint_left]; intro s h1 h2
    simp only [Finset.mem_Icc, Finset.mem_singleton] at h1 h2; omega
  rw [hsplit1, Finset.prod_union hd1, Finset.prod_union hd2, Finset.prod_singleton]
  have hmid : ((((2 * m + 1) + (2 * m + 1) : ℕ) : ℚ) / ((2 * m + 1 : ℕ) : ℚ)) ^ cnt (2 * m + 1) (2 * m + 1) =
      (2 : ℚ) ^ (m + 1) := by
    rw [cnt_eq]
    have hcond : 1 ≤ 2 * m + 1 ∧ 2 * m + 1 ≤ 2 * m + 1 := by omega
    rw [if_pos hcond, hm1]
    have hne : ((2 * m + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    have h2 : (((2 * m + 1) + (2 * m + 1) : ℕ) : ℚ) = 2 * ((2 * m + 1 : ℕ) : ℚ) := by push_cast; ring
    rw [h2, mul_div_cancel_right₀ _ hne]
  have hupper :
      (∏ s ∈ Finset.Icc (2 * m + 2) (4 * m + 1),
        (((s + (2 * m + 1) : ℕ) : ℚ) / (s : ℚ)) ^ cnt (2 * m + 1) s) =
      ∏ r ∈ Finset.Icc 1 (2 * m),
        (((2 * (2 * m + 1) + r : ℕ) : ℚ) / ((2 * m + 1 + r : ℕ) : ℚ)) ^ (m + 1 - (r + 1) / 2) := by
    have himg : Finset.Icc (2 * m + 2) (4 * m + 1) =
        (Finset.Icc 1 (2 * m)).image fun r => r + (2 * m + 1) := by
      ext s; simp only [Finset.mem_Icc, Finset.mem_image]
      exact ⟨fun ⟨h1, h2⟩ => ⟨s - (2 * m + 1), ⟨by omega, by omega⟩, by omega⟩,
             fun ⟨r, ⟨h1, h2⟩, hr⟩ => by omega⟩
    rw [himg, Finset.prod_image (fun a _ b _ h => by omega)]
    refine Finset.prod_congr rfl fun r hr => ?_
    have hrb := Finset.mem_Icc.mp hr
    rw [cnt_eq]
    have hcond1 : ¬ (1 ≤ r + (2 * m + 1) ∧ r + (2 * m + 1) ≤ 2 * m + 1) := by omega
    have hcond2 : 2 * m + 1 < r + (2 * m + 1) ∧ r + (2 * m + 1) ≤ 2 * (2 * m + 1) - 1 := by omega
    rw [if_neg hcond1, if_pos hcond2]
    have hexp : (2 * (2 * m + 1) - (r + (2 * m + 1)) + 1) / 2 = m + 1 - (r + 1) / 2 := by omega
    have hnum : r + (2 * m + 1) + (2 * m + 1) = 2 * (2 * m + 1) + r := by omega
    have hden : r + (2 * m + 1) = 2 * m + 1 + r := by omega
    rw [hexp, hnum, hden]
  have hlower :
      (∏ r ∈ Finset.Icc 1 (2 * m),
        (((r + (2 * m + 1) : ℕ) : ℚ) / (r : ℚ)) ^ cnt (2 * m + 1) r) =
      ∏ r ∈ Finset.Icc 1 (2 * m),
        (((2 * m + 1 + r : ℕ) : ℚ) / (r : ℚ)) ^ ((r + 1) / 2) := by
    refine Finset.prod_congr rfl fun r hr => ?_
    have hrb := Finset.mem_Icc.mp hr
    rw [cnt_eq]
    have hcond : 1 ≤ r ∧ r ≤ 2 * m + 1 := by omega
    rw [if_pos hcond, add_comm r (2 * m + 1)]
  rw [hmid, hupper, hlower, Nat.add_sub_cancel, Finset.prod_mul_distrib]
  ring

private lemma zmod_add_p_pow {p : ℕ} (x y : ZMod (p ^ 3)) (C : ℕ) :
    (1 + x * (p : ZMod (p ^ 3)) + y * (p : ZMod (p ^ 3)) ^ 2) ^ C =
      1 + (C : ZMod (p ^ 3)) * x * (p : ZMod (p ^ 3)) +
        ((C : ZMod (p ^ 3)) * y + (C.choose 2 : ZMod (p ^ 3)) * x ^ 2) * (p : ZMod (p ^ 3)) ^ 2 := by
  have hp3 : (p : ZMod (p ^ 3)) ^ 3 = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_self]
  induction C with
  | zero => simp
  | succ k ih =>
    rw [pow_succ (1 + x * (p : ZMod (p ^ 3)) + y * (p : ZMod (p ^ 3)) ^ 2), ih]
    have hch : ((k + 1).choose 2 : ZMod (p ^ 3)) = (k.choose 2 : ZMod (p ^ 3)) + (k : ZMod (p ^ 3)) := by
      have : (k + 1).choose 2 = k.choose 2 + k := by
        rw [Nat.choose_succ_succ, Nat.choose_one_right, add_comm]
      rw [this, Nat.cast_add]
    rw [hch, Nat.cast_add, Nat.cast_one]
    have h4 : (p : ZMod (p ^ 3)) ^ 4 = 0 := by
      calc (p : ZMod (p ^ 3)) ^ 4 = (p : ZMod (p ^ 3)) ^ 3 * (p : ZMod (p ^ 3)) := by ring
        _ = 0 := by rw [hp3, zero_mul]
    linear_combination
      (y * (k * x) + x * (k * y + ↑(k.choose 2) * x ^ 2)) * hp3 +
      y * (k * y + ↑(k.choose 2) * x ^ 2) * h4

private lemma zmod_add_p2_pow {p : ℕ} (z : ZMod (p ^ 3)) (C : ℕ) :
    (1 + z * (p : ZMod (p ^ 3)) ^ 2) ^ C =
      1 + (C : ZMod (p ^ 3)) * z * (p : ZMod (p ^ 3)) ^ 2 := by
  have h := zmod_add_p_pow (p := p) 0 z C
  simpa using h

private lemma zmod_prod_one_add_p2 {ι : Type*} {p : ℕ} (S : Finset ι) (f : ι → ZMod (p ^ 3)) :
    ∏ i ∈ S, (1 + f i * (p : ZMod (p ^ 3)) ^ 2) =
      1 + (∑ i ∈ S, f i) * (p : ZMod (p ^ 3)) ^ 2 := by
  have hp4 : (p : ZMod (p ^ 3)) ^ 4 = 0 := by
    have hp3 : (p : ZMod (p ^ 3)) ^ 3 = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
    calc (p : ZMod (p ^ 3)) ^ 4 = (p : ZMod (p ^ 3)) ^ 3 * (p : ZMod (p ^ 3)) := by ring
      _ = 0 := by rw [hp3, zero_mul]
  induction S using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    rw [Finset.prod_cons, Finset.sum_cons, ih]
    linear_combination f a * (∑ i ∈ s, f i) * hp4

private lemma zmod_p_add_inv {p : ℕ} (hp : p.Prime) {t : ℕ} (ht : ¬ p ∣ t) :
    ((p + t : ℕ) : ZMod (p ^ 3))⁻¹ =
      (t : ZMod (p ^ 3))⁻¹ - (p : ZMod (p ^ 3)) * (t : ZMod (p ^ 3))⁻¹ ^ 2 +
        (p : ZMod (p ^ 3)) ^ 2 * (t : ZMod (p ^ 3))⁻¹ ^ 3 := by
  have hcop_t : Nat.Coprime t (p ^ 3) := (hp.coprime_iff_not_dvd.mpr ht).symm.pow_right 3
  have hcop_pt : Nat.Coprime (p + t) (p ^ 3) := by
    refine (hp.coprime_iff_not_dvd.mpr ?_).symm.pow_right 3
    intro hd; exact ht ((Nat.dvd_add_right dvd_rfl).mp hd)
  have hu_t : IsUnit (t : ZMod (p ^ 3)) := (ZMod.isUnit_iff_coprime t (p ^ 3)).mpr hcop_t
  have hu_pt : IsUnit ((p + t : ℕ) : ZMod (p ^ 3)) := (ZMod.isUnit_iff_coprime (p + t) (p ^ 3)).mpr hcop_pt
  have ht_mul : (t : ZMod (p ^ 3)) * (t : ZMod (p ^ 3))⁻¹ = 1 :=
    ZMod.mul_inv_of_unit _ hu_t
  have hpt_mul : ((p + t : ℕ) : ZMod (p ^ 3)) * ((p + t : ℕ) : ZMod (p ^ 3))⁻¹ = 1 :=
    ZMod.mul_inv_of_unit _ hu_pt
  have hp3 : (p : ZMod (p ^ 3)) ^ 3 = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
  refine hu_pt.mul_left_cancel ?_
  rw [hpt_mul]
  push_cast
  symm
  linear_combination
    (1 - p * (t : ZMod (p ^ 3))⁻¹ + p ^ 2 * (t : ZMod (p ^ 3))⁻¹ ^ 2) * ht_mul +
    (t : ZMod (p ^ 3))⁻¹ ^ 3 * hp3

private lemma zmod_p_sub_inv {p : ℕ} (hp : p.Prime) {t : ℕ} (ht1 : 1 ≤ t) (htp : t < p) :
    ((p - t : ℕ) : ZMod (p ^ 3))⁻¹ =
      -(t : ZMod (p ^ 3))⁻¹ - (p : ZMod (p ^ 3)) * (t : ZMod (p ^ 3))⁻¹ ^ 2 -
        (p : ZMod (p ^ 3)) ^ 2 * (t : ZMod (p ^ 3))⁻¹ ^ 3 := by
  have ht : ¬ p ∣ t := fun h => by have := Nat.le_of_dvd (by omega) h; omega
  have hpt : ¬ p ∣ p - t := fun h => by have := Nat.le_of_dvd (by omega) h; omega
  have hcop_t : Nat.Coprime t (p ^ 3) := (hp.coprime_iff_not_dvd.mpr ht).symm.pow_right 3
  have hcop_pt : Nat.Coprime (p - t) (p ^ 3) := (hp.coprime_iff_not_dvd.mpr hpt).symm.pow_right 3
  have hu_t : IsUnit (t : ZMod (p ^ 3)) := (ZMod.isUnit_iff_coprime t (p ^ 3)).mpr hcop_t
  have hu_pt : IsUnit ((p - t : ℕ) : ZMod (p ^ 3)) := (ZMod.isUnit_iff_coprime (p - t) (p ^ 3)).mpr hcop_pt
  have ht_mul : (t : ZMod (p ^ 3)) * (t : ZMod (p ^ 3))⁻¹ = 1 := ZMod.mul_inv_of_unit _ hu_t
  have hpt_mul : ((p - t : ℕ) : ZMod (p ^ 3)) * ((p - t : ℕ) : ZMod (p ^ 3))⁻¹ = 1 :=
    ZMod.mul_inv_of_unit _ hu_pt
  have hp3 : (p : ZMod (p ^ 3)) ^ 3 = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
  have hsub : ((p - t : ℕ) : ZMod (p ^ 3)) = (p : ZMod (p ^ 3)) - (t : ZMod (p ^ 3)) := by
    rw [Nat.cast_sub (le_of_lt htp)]
  refine hu_pt.mul_left_cancel ?_
  rw [hpt_mul, hsub]
  symm
  linear_combination
    (1 + p * (t : ZMod (p ^ 3))⁻¹ + p ^ 2 * (t : ZMod (p ^ 3))⁻¹ ^ 2) * ht_mul -
    (t : ZMod (p ^ 3))⁻¹ ^ 3 * hp3

private lemma sum_inv_sq_mul_three_p2 {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) :
    (3 : ZMod (p ^ 3)) * (∑ t ∈ Finset.Icc 1 ((p - 1) / 2), ((t : ZMod (p ^ 3))⁻¹) ^ 2) *
      (p : ZMod (p ^ 3)) ^ 2 = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  -- It suffices to show that the image in ZMod p of 3 * ∑_{t=1}^{(p-1)/2} t^(-2) is 0!
  let S_half : ZMod (p ^ 3) := ∑ t ∈ Finset.Icc 1 ((p - 1) / 2), ((t : ZMod (p ^ 3))⁻¹) ^ 2
  let f : ZMod (p ^ 3) →+* ZMod p := ZMod.castHom (dvd_pow_self p (by omega)) (ZMod p)
  have hf_val : f ((3 : ZMod (p ^ 3)) * S_half) = 0 := by
    have hmap_inv : ∀ t ∈ Finset.Icc 1 (p - 1), f ((t : ZMod (p ^ 3))⁻¹) = ((t : ZMod p))⁻¹ := by
      intro t ht
      have htb := Finset.mem_Icc.mp ht
      have hnd : ¬ p ∣ t := fun h => by have := Nat.le_of_dvd (by omega) h; omega
      have hu : IsUnit (t : ZMod (p ^ 3)) :=
        (ZMod.isUnit_iff_coprime t (p ^ 3)).mpr ((hp.coprime_iff_not_dvd.mpr hnd).symm.pow_right 3)
      have h1 : (t : ZMod (p ^ 3)) * (t : ZMod (p ^ 3))⁻¹ = 1 := ZMod.mul_inv_of_unit _ hu
      have h2 : f (t : ZMod (p ^ 3)) * f ((t : ZMod (p ^ 3))⁻¹) = 1 := by
        rw [← map_mul, h1, map_one]
      have hft : f (t : ZMod (p ^ 3)) = (t : ZMod p) := map_natCast f t
      rw [hft] at h2
      have hne : (t : ZMod p) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]; exact hnd
      exact mul_left_cancel₀ hne (h2.trans (mul_inv_cancel₀ hne).symm)
    have hS_full : (2 : ZMod p) * f S_half = ∑ t ∈ Finset.Icc 1 (p - 1), ((t : ZMod p)⁻¹) ^ 2 := by
      have hfS : f S_half = ∑ t ∈ Finset.Icc 1 ((p - 1) / 2), ((t : ZMod p)⁻¹) ^ 2 := by
        dsimp only [S_half]
        rw [map_sum]
        refine Finset.sum_congr rfl fun t ht => ?_
        have htb := Finset.mem_Icc.mp ht
        rw [map_pow, hmap_inv t (Finset.mem_Icc.mpr ⟨htb.1, by omega⟩)]
      rw [hfS]
      have hodd : 2 * ((p - 1) / 2) = p - 1 := by
        have := hp.eq_two_or_odd.resolve_left (by omega); omega
      have hsplit : Finset.Icc 1 (p - 1) =
          Finset.Icc 1 ((p - 1) / 2) ∪ Finset.Icc ((p - 1) / 2 + 1) (p - 1) := by
        ext t; simp only [Finset.mem_Icc, Finset.mem_union]; omega
      have hdisj : Disjoint (Finset.Icc 1 ((p - 1) / 2)) (Finset.Icc ((p - 1) / 2 + 1) (p - 1)) := by
        rw [Finset.disjoint_left]; intro t h1 h2; simp only [Finset.mem_Icc] at h1 h2; omega
      rw [hsplit, Finset.sum_union hdisj]
      have hrev : (∑ t ∈ Finset.Icc ((p - 1) / 2 + 1) (p - 1), ((t : ZMod p)⁻¹) ^ 2) =
          ∑ t ∈ Finset.Icc 1 ((p - 1) / 2), ((t : ZMod p)⁻¹) ^ 2 := by
        refine Finset.sum_bij (fun t _ => p - t) ?_ ?_ ?_ ?_
        · intro t ht; simp only [Finset.mem_Icc] at ht ⊢; omega
        · intro a ha b hb h; simp only [Finset.mem_Icc] at ha hb; omega
        · intro t ht; simp only [Finset.mem_Icc] at ht
          exact ⟨p - t, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
        · intro t ht
          have htb := Finset.mem_Icc.mp ht
          have hcast : ((p - t : ℕ) : ZMod p) = -(t : ZMod p) := by
            rw [Nat.cast_sub (by omega : t ≤ p), ZMod.natCast_self, zero_sub]
          rw [hcast, inv_neg, neg_sq]
      rw [hrev, two_mul]
    have hfull_eq : ∑ t ∈ Finset.Icc 1 (p - 1), ((t : ZMod p)⁻¹) ^ 2 =
        ∑ x : (ZMod p)ˣ, (x : ZMod p) ^ 2 := by
      -- Map t ↦ (t : ZMod p)⁻¹ as a unit
      refine Finset.sum_bij (fun t ht => (Units.mk0 ((t : ZMod p)⁻¹) (by
        have htb := Finset.mem_Icc.mp ht
        have hnd : ¬ p ∣ t := fun h => by have := Nat.le_of_dvd (by omega) h; omega
        exact inv_ne_zero (fun h0 => hnd ((ZMod.natCast_eq_zero_iff t p).mp h0)))))
        (fun _ _ => Finset.mem_univ _) ?_ ?_ (fun _ _ => rfl)
      · intro a ha b hb h
        have h1 : ((a : ZMod p)⁻¹) = ((b : ZMod p)⁻¹) := congrArg Units.val h
        have h2 : (a : ZMod p) = (b : ZMod p) := inv_injective h1
        have hab := Finset.mem_Icc.mp ha; have hbb := Finset.mem_Icc.mp hb
        have := congrArg ZMod.val h2
        rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at this
        exact this
      · intro u _
        let t := (u⁻¹ : (ZMod p)ˣ).val.val
        have ht0 : 1 ≤ t := by
          by_contra h0
          have : (u⁻¹ : (ZMod p)ˣ).val = 0 := by
            apply ZMod.val_injective; rw [ZMod.val_zero]; change t = 0; omega
          exact u⁻¹.ne_zero this
        have htp : t ≤ p - 1 := by have := ZMod.val_lt (u⁻¹ : (ZMod p)ˣ).val; omega
        refine ⟨t, Finset.mem_Icc.mpr ⟨ht0, htp⟩, ?_⟩
        apply Units.ext
        change ((t : ZMod p))⁻¹ = (u : ZMod p)
        have htc : (t : ZMod p) = (u⁻¹ : (ZMod p)ˣ).val := ZMod.natCast_zmod_val _
        rw [htc, Units.val_inv_eq_inv_val, inv_inv]
    -- 4 * ∑ x^2 = ∑ (2*x)^2 = ∑ x^2, so 3 * ∑ x^2 = 0!
    have h2ne : (2 : ZMod p) ≠ 0 := by
      intro h0
      have h20 : ((2 : ℕ) : ZMod p) = 0 := h0
      have hdvd := (ZMod.natCast_eq_zero_iff 2 p).mp h20
      have := Nat.le_of_dvd (by omega) hdvd; omega
    have h3sum : (3 : ZMod p) * ∑ x : (ZMod p)ˣ, (x : ZMod p) ^ 2 = 0 := by
      let u2 : (ZMod p)ˣ := Units.mk0 2 h2ne
      have hmul : (4 : ZMod p) * ∑ x : (ZMod p)ˣ, (x : ZMod p) ^ 2 =
          ∑ x : (ZMod p)ˣ, (x : ZMod p) ^ 2 := by
        rw [Finset.mul_sum]
        have h1 : ∀ x : (ZMod p)ˣ, (4 : ZMod p) * (x : ZMod p) ^ 2 = ((u2 * x : (ZMod p)ˣ) : ZMod p) ^ 2 := by
          intro x; simp only [Units.val_mul, u2, Units.val_mk0]; ring
        simp_rw [h1]
        exact Equiv.sum_comp (Equiv.mulLeft u2) (fun x : (ZMod p)ˣ => (x : ZMod p) ^ 2)
      linear_combination hmul
    have h23 : (2 : ZMod p) * f ((3 : ZMod (p ^ 3)) * S_half) = 0 := by
      rw [map_mul, map_ofNat]
      calc (2 : ZMod p) * ((3 : ZMod p) * f S_half)
          = (3 : ZMod p) * ((2 : ZMod p) * f S_half) := by ring
        _ = (3 : ZMod p) * ∑ x : (ZMod p)ˣ, (x : ZMod p) ^ 2 := by rw [hS_full, hfull_eq]
        _ = 0 := h3sum
    exact (mul_eq_zero.mp h23).resolve_left h2ne
  -- Since f(x) = 0 in ZMod p, p ∣ x.val, so x * p^2 = 0 in ZMod (p^3)!
  set X : ZMod (p ^ 3) := (3 : ZMod (p ^ 3)) * S_half
  have hdvd : p ∣ X.val := by
    rw [← ZMod.natCast_eq_zero_iff]
    have hcast : (X.val : ZMod p) = f X := by
      rw [← map_natCast f X.val, ZMod.natCast_zmod_val]
    rw [hcast]; exact hf_val
  rcases hdvd with ⟨k, hk⟩
  calc X * (p : ZMod (p ^ 3)) ^ 2
      = (X.val : ZMod (p ^ 3)) * (p : ZMod (p ^ 3)) ^ 2 := by rw [ZMod.natCast_zmod_val]
    _ = ((p * k : ℕ) : ZMod (p ^ 3)) * (p : ZMod (p ^ 3)) ^ 2 := by rw [hk]
    _ = (k : ZMod (p ^ 3)) * ((p ^ 3 : ℕ) : ZMod (p ^ 3)) := by push_cast; ring
    _ = 0 := by rw [ZMod.natCast_self, mul_zero]

private lemma stratum_zmod_eq_one {p d e : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hd : 1 ≤ d) (he : e < d) :
    let q := p ^ (d - e)
    let S := (Finset.Icc 1 (q - 1)).filter fun t => ¬ p ∣ t
    let M := (p ^ d + 1) / 2
    ∏ t ∈ S,
      ((((q + t : ℕ) : ZMod (p ^ 3)) * (t : ZMod (p ^ 3))⁻¹) ^ ((p ^ e * t + 1) / 2) *
       (((2 * q + t : ℕ) : ZMod (p ^ 3)) * ((q + t : ℕ) : ZMod (p ^ 3))⁻¹) ^
         (M - (p ^ e * t + 1) / 2)) = 1 := by
  intro q S M
  have hp_pos : 0 < p := hp.pos
  have hodd_p : Odd p := Nat.odd_iff.mpr (hp.eq_two_or_odd.resolve_left (by omega))
  have hodd_pd : Odd (p ^ d) := hodd_p.pow
  have hodd_pe : Odd (p ^ e) := hodd_p.pow
  have hcop_t : ∀ t ∈ S, IsUnit (t : ZMod (p ^ 3)) := by
    intro t ht
    have hnd := (Finset.mem_filter.mp ht).2
    exact (ZMod.isUnit_iff_coprime t (p ^ 3)).mpr ((hp.coprime_iff_not_dvd.mpr hnd).symm.pow_right 3)
  have hcop_qt : ∀ t ∈ S, IsUnit ((q + t : ℕ) : ZMod (p ^ 3)) := by
    intro t ht
    have hnd := (Finset.mem_filter.mp ht).2
    have hpq : p ∣ q := dvd_pow_self p (by omega)
    have hnd' : ¬ p ∣ q + t := fun h => hnd ((Nat.dvd_add_right hpq).mp h)
    exact (ZMod.isUnit_iff_coprime (q + t) (p ^ 3)).mpr ((hp.coprime_iff_not_dvd.mpr hnd').symm.pow_right 3)
  by_cases h3 : 3 ≤ d - e
  · -- Case 1: p^3 ∣ q, so q = 0 in ZMod (p^3)
    have hq0 : (q : ZMod (p ^ 3)) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]
      exact pow_dvd_pow p h3
    refine Finset.prod_eq_one fun t ht => ?_
    have ht_inv : (t : ZMod (p ^ 3)) * (t : ZMod (p ^ 3))⁻¹ = 1 := ZMod.mul_inv_of_unit _ (hcop_t t ht)
    push_cast
    rw [hq0, zero_add, mul_zero, zero_add, ht_inv, one_pow, one_pow, mul_one]
  · by_cases h2 : d - e = 2
    · -- Case 2: q = p^2
      have hqeq : q = p ^ 2 := by dsimp only [q]; rw [h2]
      have hq_cast : (q : ZMod (p ^ 3)) = (p : ZMod (p ^ 3)) ^ 2 := by rw [hqeq, Nat.cast_pow]
      have hp3_0 : (p : ZMod (p ^ 3)) ^ 3 = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
      have hp4_0 : (p : ZMod (p ^ 3)) ^ 4 = 0 := by
        calc (p : ZMod (p ^ 3)) ^ 4 = (p : ZMod (p ^ 3)) ^ 3 * (p : ZMod (p ^ 3)) := by ring
          _ = 0 := by rw [hp3_0, zero_mul]
      have hterm : ∀ t ∈ S,
          ((((q + t : ℕ) : ZMod (p ^ 3)) * (t : ZMod (p ^ 3))⁻¹) ^ ((p ^ e * t + 1) / 2) *
           (((2 * q + t : ℕ) : ZMod (p ^ 3)) * ((q + t : ℕ) : ZMod (p ^ 3))⁻¹) ^
             (M - (p ^ e * t + 1) / 2)) =
          1 + (M : ZMod (p ^ 3)) * (t : ZMod (p ^ 3))⁻¹ * (p : ZMod (p ^ 3)) ^ 2 := by
        intro t ht
        have ht_inv : (t : ZMod (p ^ 3)) * (t : ZMod (p ^ 3))⁻¹ = 1 := ZMod.mul_inv_of_unit _ (hcop_t t ht)
        have hqt_inv : ((q + t : ℕ) : ZMod (p ^ 3)) * ((q + t : ℕ) : ZMod (p ^ 3))⁻¹ = 1 :=
          ZMod.mul_inv_of_unit _ (hcop_qt t ht)
        have hf1 : ((q + t : ℕ) : ZMod (p ^ 3)) * (t : ZMod (p ^ 3))⁻¹ =
            1 + (t : ZMod (p ^ 3))⁻¹ * (p : ZMod (p ^ 3)) ^ 2 := by
          push_cast; rw [hq_cast]; linear_combination ht_inv
        have hinv_qt : ((q + t : ℕ) : ZMod (p ^ 3))⁻¹ * (p : ZMod (p ^ 3)) ^ 2 =
            (t : ZMod (p ^ 3))⁻¹ * (p : ZMod (p ^ 3)) ^ 2 := by
          have hmul : ((q + t : ℕ) : ZMod (p ^ 3)) * ((t : ZMod (p ^ 3))⁻¹ * (p : ZMod (p ^ 3)) ^ 2) =
              (p : ZMod (p ^ 3)) ^ 2 := by
            push_cast; rw [hq_cast]
            linear_combination (p : ZMod (p ^ 3)) ^ 2 * ht_inv + (t : ZMod (p ^ 3))⁻¹ * hp4_0
          calc ((q + t : ℕ) : ZMod (p ^ 3))⁻¹ * (p : ZMod (p ^ 3)) ^ 2
              = ((q + t : ℕ) : ZMod (p ^ 3))⁻¹ *
                  (((q + t : ℕ) : ZMod (p ^ 3)) * ((t : ZMod (p ^ 3))⁻¹ * (p : ZMod (p ^ 3)) ^ 2)) := by
                rw [hmul]
            _ = (((q + t : ℕ) : ZMod (p ^ 3)) * ((q + t : ℕ) : ZMod (p ^ 3))⁻¹) *
                  ((t : ZMod (p ^ 3))⁻¹ * (p : ZMod (p ^ 3)) ^ 2) := by ring
            _ = (t : ZMod (p ^ 3))⁻¹ * (p : ZMod (p ^ 3)) ^ 2 := by rw [hqt_inv, one_mul]
        have hf2 : ((2 * q + t : ℕ) : ZMod (p ^ 3)) * ((q + t : ℕ) : ZMod (p ^ 3))⁻¹ =
            1 + (t : ZMod (p ^ 3))⁻¹ * (p : ZMod (p ^ 3)) ^ 2 := by
          have h2q : ((2 * q + t : ℕ) : ZMod (p ^ 3)) =
              ((q + t : ℕ) : ZMod (p ^ 3)) + (p : ZMod (p ^ 3)) ^ 2 := by
            push_cast; rw [hq_cast]; ring
          rw [h2q, add_mul, hqt_inv, mul_comm ((p : ZMod (p ^ 3)) ^ 2), hinv_qt]
        have htb := Finset.mem_Icc.mp (Finset.mem_filter.mp ht).1
        have hAle : (p ^ e * t + 1) / 2 ≤ M := by
          have hq1 : 1 ≤ q := Nat.one_le_pow _ _ hp_pos
          have htq : t < q := by omega
          have hprod : p ^ e * q = p ^ d := by rw [← pow_add, show e + (d - e) = d by omega]
          have hlt : p ^ e * t < p ^ d := by
            rw [← hprod]; exact Nat.mul_lt_mul_of_pos_left htq (pow_pos hp_pos e)
          dsimp only [M]; omega
        rw [hf1, hf2, ← pow_add, Nat.add_sub_of_le hAle, zmod_add_p2_pow]
      rw [Finset.prod_congr rfl hterm, zmod_prod_one_add_p2]
      have hsum_zero : (∑ t ∈ S, (M : ZMod (p ^ 3)) * (t : ZMod (p ^ 3))⁻¹) * (p : ZMod (p ^ 3)) ^ 2 = 0 := by
        rw [← Finset.mul_sum, mul_assoc]
        suffices h0 : (∑ t ∈ S, (t : ZMod (p ^ 3))⁻¹) * (p : ZMod (p ^ 3)) ^ 2 = 0 by rw [h0, mul_zero]
        have h2u : IsUnit (2 : ZMod (p ^ 3)) :=
          (ZMod.isUnit_iff_coprime 2 (p ^ 3)).mpr
            ((hp.coprime_iff_not_dvd.mpr (fun h => by have := Nat.le_of_dvd (by omega) h; omega)).symm.pow_right 3)
        refine h2u.mul_left_cancel ?_
        rw [mul_zero, two_mul, ← add_mul]
        have hrev : (∑ t ∈ S, (t : ZMod (p ^ 3))⁻¹) * (p : ZMod (p ^ 3)) ^ 2 =
            ∑ t ∈ S, -((t : ZMod (p ^ 3))⁻¹ * (p : ZMod (p ^ 3)) ^ 2) := by
          rw [Finset.sum_mul]
          refine Finset.sum_bij (fun t _ => q - t) ?_ ?_ ?_ ?_
          · intro t ht
            have htb := Finset.mem_Icc.mp (Finset.mem_filter.mp ht).1
            have hnd := (Finset.mem_filter.mp ht).2
            have hpq : p ∣ q := dvd_pow_self p (by omega)
            simp only [S, Finset.mem_filter, Finset.mem_Icc]
            exact ⟨⟨by omega, by omega⟩, fun h => hnd ((Nat.dvd_sub_iff_right (le_of_lt (by omega)) hpq).mp h)⟩
          · intro a ha b hb h
            have hab := Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1
            have hbb := Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1
            omega
          · intro t ht
            have htb := Finset.mem_Icc.mp (Finset.mem_filter.mp ht).1
            have hnd := (Finset.mem_filter.mp ht).2
            have hpq : p ∣ q := dvd_pow_self p (by omega)
            refine ⟨q - t, ?_, by omega⟩
            simp only [S, Finset.mem_filter, Finset.mem_Icc]
            exact ⟨⟨by omega, by omega⟩, fun h => hnd ((Nat.dvd_sub_iff_right (le_of_lt (by omega)) hpq).mp h)⟩
          · intro t ht
            have htb := Finset.mem_Icc.mp (Finset.mem_filter.mp ht).1
            have hnd := (Finset.mem_filter.mp ht).2
            have hpq : p ∣ q := dvd_pow_self p (by omega)
            have hnd' : ¬ p ∣ q - t := fun h => hnd ((Nat.dvd_sub_iff_right (le_of_lt (by omega)) hpq).mp h)
            have hu_qt : IsUnit ((q - t : ℕ) : ZMod (p ^ 3)) :=
              (ZMod.isUnit_iff_coprime (q - t) (p ^ 3)).mpr ((hp.coprime_iff_not_dvd.mpr hnd').symm.pow_right 3)
            have hqt_inv := ZMod.mul_inv_of_unit _ hu_qt
            have ht_inv := ZMod.mul_inv_of_unit _ (hcop_t t ht)
            have hsub : ((q - t : ℕ) : ZMod (p ^ 3)) = (p : ZMod (p ^ 3)) ^ 2 - (t : ZMod (p ^ 3)) := by
              rw [Nat.cast_sub (by omega : t ≤ q), hq_cast]
            refine hu_qt.mul_left_cancel ?_
            rw [mul_neg, ← mul_assoc ((q - t : ℕ) : ZMod (p ^ 3)) ((q - t : ℕ) : ZMod (p ^ 3))⁻¹,
                hqt_inv, one_mul, hsub]
            linear_combination
              -(p : ZMod (p ^ 3)) ^ 2 * ht_inv + (t : ZMod (p ^ 3))⁻¹ * hp4_0
        rw [add_mul]
        conv_lhs => rhs; rw [hrev]
        rw [Finset.sum_mul, Finset.sum_neg_distrib, add_neg_cancel]
      rw [hsum_zero, add_zero]
    · -- Case 3: d - e = 1, so q = p, S = Icc 1 (p - 1)
      have hde1 : d - e = 1 := by omega
      have hqeq : q = p := by dsimp only [q]; rw [hde1, pow_one]
      have hSeq : S = Finset.Icc 1 (p - 1) := by
        ext t; simp only [S, hqeq, Finset.mem_filter, Finset.mem_Icc, and_iff_left_iff_imp]
        rintro ⟨h1, h2⟩ hdvd; have := Nat.le_of_dvd (by omega) hdvd; omega
      rw [hSeq]
      have hp3_0 : (p : ZMod (p ^ 3)) ^ 3 = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
      have hp4_0 : (p : ZMod (p ^ 3)) ^ 4 = 0 := by
        calc (p : ZMod (p ^ 3)) ^ 4 = (p : ZMod (p ^ 3)) ^ 3 * (p : ZMod (p ^ 3)) := by ring
          _ = 0 := by rw [hp3_0, zero_mul]
      -- Define F(t) and expand it mod p^3
      let A : ℕ → ℕ := fun t => (p ^ e * t + 1) / 2
      let B : ℕ → ℕ := fun t => M - A t
      let F : ℕ → ZMod (p ^ 3) := fun t =>
        (((q + t : ℕ) : ZMod (p ^ 3)) * (t : ZMod (p ^ 3))⁻¹) ^ A t *
        (((2 * q + t : ℕ) : ZMod (p ^ 3)) * ((q + t : ℕ) : ZMod (p ^ 3))⁻¹) ^ B t
      change ∏ t ∈ Finset.Icc 1 (p - 1), F t = 1
      have hF_expand : ∀ t ∈ Finset.Icc 1 (p - 1),
          F t = 1 + (M : ZMod (p ^ 3)) * (t : ZMod (p ^ 3))⁻¹ * (p : ZMod (p ^ 3)) +
            (((M.choose 2 : ZMod (p ^ 3)) - (B t : ZMod (p ^ 3))) * ((t : ZMod (p ^ 3))⁻¹) ^ 2) *
              (p : ZMod (p ^ 3)) ^ 2 := by
        intro t ht
        have htb := Finset.mem_Icc.mp ht
        have hnd : ¬ p ∣ t := fun h => by have := Nat.le_of_dvd (by omega) h; omega
        have htS : t ∈ S := by rw [hSeq]; exact ht
        have ht_inv : (t : ZMod (p ^ 3)) * (t : ZMod (p ^ 3))⁻¹ = 1 := ZMod.mul_inv_of_unit _ (hcop_t t htS)
        have hqt_inv : ((p + t : ℕ) : ZMod (p ^ 3)) * ((p + t : ℕ) : ZMod (p ^ 3))⁻¹ = 1 := by
          have h := ZMod.mul_inv_of_unit _ (hcop_qt t htS)
          rw [hqeq] at h; exact h
        have hf1 : ((q + t : ℕ) : ZMod (p ^ 3)) * (t : ZMod (p ^ 3))⁻¹ =
            1 + (t : ZMod (p ^ 3))⁻¹ * (p : ZMod (p ^ 3)) + 0 * (p : ZMod (p ^ 3)) ^ 2 := by
          rw [hqeq]; push_cast; linear_combination ht_inv
        have hf2 : ((2 * q + t : ℕ) : ZMod (p ^ 3)) * ((q + t : ℕ) : ZMod (p ^ 3))⁻¹ =
            1 + (t : ZMod (p ^ 3))⁻¹ * (p : ZMod (p ^ 3)) +
              (-(((t : ZMod (p ^ 3))⁻¹) ^ 2)) * (p : ZMod (p ^ 3)) ^ 2 := by
          rw [hqeq]
          have h2p : ((2 * p + t : ℕ) : ZMod (p ^ 3)) =
              ((p + t : ℕ) : ZMod (p ^ 3)) + (p : ZMod (p ^ 3)) := by push_cast; ring
          rw [h2p, add_mul, hqt_inv, zmod_p_add_inv hp hnd]
          linear_combination (t : ZMod (p ^ 3))⁻¹ ^ 3 * hp3_0
        have hAle : A t ≤ M := by
          have htp : t < p := by omega
          have hprod : p ^ e * p = p ^ d := by rw [← pow_succ, show e + 1 = d by omega]
          have hlt : p ^ e * t < p ^ d := by
            rw [← hprod]; exact Nat.mul_lt_mul_of_pos_left htp (pow_pos hp_pos e)
          dsimp only [A, M]; omega
        have hAB_sum : (A t : ZMod (p ^ 3)) + (B t : ZMod (p ^ 3)) = (M : ZMod (p ^ 3)) := by
          rw [← Nat.cast_add, Nat.add_sub_of_le hAle]
        have hch_id : (A t).choose 2 + A t * B t + (B t).choose 2 = M.choose 2 := by
          have h1 : 2 * ((A t).choose 2 + A t * B t + (B t).choose 2) = 2 * M.choose 2 := by
            have hmul2 : ∀ k : ℕ, 2 * k.choose 2 = k * (k - 1) := by
              intro k
              rw [Nat.choose_two_right]
              have hev : Even (k * (k - 1)) := Nat.even_mul_pred_self k
              rcases hev with ⟨r, hr⟩; omega
            have hsum : A t + B t = M := Nat.add_sub_of_le hAle
            rw [mul_add, mul_add, hmul2, hmul2, hmul2, ← hsum]
            cases hA : A t <;> cases hB : B t <;> simp <;> ring
          omega
        have hch_z : ((A t).choose 2 : ZMod (p ^ 3)) + (A t : ZMod (p ^ 3)) * (B t : ZMod (p ^ 3)) +
            ((B t).choose 2 : ZMod (p ^ 3)) = (M.choose 2 : ZMod (p ^ 3)) := by
          have := congrArg (Nat.cast (R := ZMod (p ^ 3))) hch_id
          push_cast at this; exact this
        dsimp only [F]
        rw [hf1, hf2, zmod_add_p_pow, zmod_add_p_pow]
        set ti := (t : ZMod (p ^ 3))⁻¹
        linear_combination
          ti * (p : ZMod (p ^ 3)) * hAB_sum +
          ti ^ 2 * (p : ZMod (p ^ 3)) ^ 2 * hch_z +
          ((A t : ZMod (p ^ 3)) * ti * ((B t : ZMod (p ^ 3)) * (-ti ^ 2) + ((B t).choose 2 : ZMod (p ^ 3)) * ti ^ 2) +
            ((A t).choose 2 : ZMod (p ^ 3)) * ti ^ 2 * ((B t : ZMod (p ^ 3)) * ti)) * hp3_0 +
          ((A t).choose 2 : ZMod (p ^ 3)) * ti ^ 2 *
            ((B t : ZMod (p ^ 3)) * (-ti ^ 2) + ((B t).choose 2 : ZMod (p ^ 3)) * ti ^ 2) * hp4_0
      -- Pair t with p - t for t ∈ Icc 1 ((p - 1)/2)
      have hpair : ∀ t ∈ Finset.Icc 1 ((p - 1) / 2),
          F t * F (p - t) = 1 + (-(3 : ZMod (p ^ 3)) * (M : ZMod (p ^ 3)) * ((t : ZMod (p ^ 3))⁻¹) ^ 2) *
            (p : ZMod (p ^ 3)) ^ 2 := by
        intro t ht
        have htb := Finset.mem_Icc.mp ht
        have ht1 : t ∈ Finset.Icc 1 (p - 1) := Finset.mem_Icc.mpr ⟨htb.1, by omega⟩
        have ht2 : p - t ∈ Finset.Icc 1 (p - 1) := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
        rw [hF_expand t ht1, hF_expand (p - t) ht2, zmod_p_sub_inv hp htb.1 (by omega)]
        -- B t + B (p - t) = M!
        have hB_sum : B t + B (p - t) = M := by
          have hpe_sum : p ^ e * t + p ^ e * (p - t) = p ^ d := by
            have : p ^ e * p = p ^ d := by rw [← pow_succ, show e + 1 = d by omega]
            rw [← mul_add, Nat.add_sub_of_le (by omega : t ≤ p), this]
          have hAsum : A t + A (p - t) = M := by
            rcases hodd_pd with ⟨m', hm'⟩
            dsimp only [A, M]; omega
          dsimp only [B]; omega
        have hB_sum_z : (B t : ZMod (p ^ 3)) + (B (p - t) : ZMod (p ^ 3)) = (M : ZMod (p ^ 3)) := by
          have := congrArg (Nat.cast (R := ZMod (p ^ 3))) hB_sum
          push_cast at this; exact this
        have h2ch : (2 : ZMod (p ^ 3)) * (M.choose 2 : ZMod (p ^ 3)) =
            (M : ZMod (p ^ 3)) * (M : ZMod (p ^ 3)) - (M : ZMod (p ^ 3)) := by
          have hnat : 2 * M.choose 2 + M = M * M := by
            rw [Nat.choose_two_right]
            have hev : Even (M * (M - 1)) := Nat.even_mul_pred_self M
            rcases hev with ⟨r, hr⟩
            have : M * (M - 1) + M = M * M := by
              cases hM : M with
              | zero => simp
              | succ k => simp; ring
            omega
          have hz : (2 : ZMod (p ^ 3)) * (M.choose 2 : ZMod (p ^ 3)) + (M : ZMod (p ^ 3)) =
              (M : ZMod (p ^ 3)) * (M : ZMod (p ^ 3)) := by
            have := congrArg (Nat.cast (R := ZMod (p ^ 3))) hnat
            push_cast at this; exact this
          linear_combination hz
        set ti := (t : ZMod (p ^ 3))⁻¹
        set u := (p : ZMod (p ^ 3))
        have h1_pt : (-ti - u * ti ^ 2 - u ^ 2 * ti ^ 3) * u = -ti * u - ti ^ 2 * u ^ 2 := by
          linear_combination -ti ^ 3 * hp3_0
        have h2_pt : (-ti - u * ti ^ 2 - u ^ 2 * ti ^ 3) ^ 2 * u ^ 2 = ti ^ 2 * u ^ 2 := by
          have hu5 : u ^ 5 = 0 := by
            calc u ^ 5 = u ^ 4 * u := by ring
              _ = 0 := by rw [hp4_0, zero_mul]
          have hu6 : u ^ 6 = 0 := by
            calc u ^ 6 = u ^ 5 * u := by ring
              _ = 0 := by rw [hu5, zero_mul]
          linear_combination 2 * ti ^ 3 * hp3_0 + 3 * ti ^ 4 * hp4_0 + 2 * ti ^ 5 * hu5 + ti ^ 6 * hu6
        have hF2_simp :
            1 + (M : ZMod (p ^ 3)) * (-ti - u * ti ^ 2 - u ^ 2 * ti ^ 3) * u +
              (((M.choose 2 : ZMod (p ^ 3)) - (B (p - t) : ZMod (p ^ 3))) *
                (-ti - u * ti ^ 2 - u ^ 2 * ti ^ 3) ^ 2) * u ^ 2 =
            1 + (-(M : ZMod (p ^ 3)) * ti) * u +
              ((-(M : ZMod (p ^ 3)) + (M.choose 2 : ZMod (p ^ 3)) - (B (p - t) : ZMod (p ^ 3))) * ti ^ 2) *
                u ^ 2 := by
          rw [mul_assoc (M : ZMod (p ^ 3)), h1_pt, mul_assoc _ ((-ti - u * ti ^ 2 - u ^ 2 * ti ^ 3) ^ 2), h2_pt]
          ring
        rw [hF2_simp]
        have hmul :
            (1 + ((M : ZMod (p ^ 3)) * ti) * u +
              (((M.choose 2 : ZMod (p ^ 3)) - (B t : ZMod (p ^ 3))) * ti ^ 2) * u ^ 2) *
            (1 + (-(M : ZMod (p ^ 3)) * ti) * u +
              ((-(M : ZMod (p ^ 3)) + (M.choose 2 : ZMod (p ^ 3)) - (B (p - t) : ZMod (p ^ 3))) * ti ^ 2) *
                u ^ 2) =
            1 + ((M : ZMod (p ^ 3)) * ti + -(M : ZMod (p ^ 3)) * ti) * u +
              (((M : ZMod (p ^ 3)) * ti) * (-(M : ZMod (p ^ 3)) * ti) +
                ((M.choose 2 : ZMod (p ^ 3)) - (B t : ZMod (p ^ 3))) * ti ^ 2 +
                (-(M : ZMod (p ^ 3)) + (M.choose 2 : ZMod (p ^ 3)) - (B (p - t) : ZMod (p ^ 3))) * ti ^ 2) *
                u ^ 2 := by
          linear_combination
            (((M : ZMod (p ^ 3)) * ti) *
                ((-(M : ZMod (p ^ 3)) + (M.choose 2 : ZMod (p ^ 3)) - (B (p - t) : ZMod (p ^ 3))) * ti ^ 2) +
              (((M.choose 2 : ZMod (p ^ 3)) - (B t : ZMod (p ^ 3))) * ti ^ 2) *
                (-(M : ZMod (p ^ 3)) * ti)) * hp3_0 +
            (((M.choose 2 : ZMod (p ^ 3)) - (B t : ZMod (p ^ 3))) * ti ^ 2) *
              ((-(M : ZMod (p ^ 3)) + (M.choose 2 : ZMod (p ^ 3)) - (B (p - t) : ZMod (p ^ 3))) * ti ^ 2) * hp4_0
        rw [hmul]
        linear_combination ti ^ 2 * u ^ 2 * h2ch - ti ^ 2 * u ^ 2 * hB_sum_z
      -- Split ∏_{t=1}^{p-1} F t into pairs F t * F (p - t)
      have hodd_half : 2 * ((p - 1) / 2) = p - 1 := by
        rcases hodd_p with ⟨k, rfl⟩; omega
      have hsplit : Finset.Icc 1 (p - 1) =
          Finset.Icc 1 ((p - 1) / 2) ∪ Finset.Icc ((p - 1) / 2 + 1) (p - 1) := by
        ext t; simp only [Finset.mem_Icc, Finset.mem_union]; omega
      have hdisj : Disjoint (Finset.Icc 1 ((p - 1) / 2)) (Finset.Icc ((p - 1) / 2 + 1) (p - 1)) := by
        rw [Finset.disjoint_left]; intro t h1 h2; simp only [Finset.mem_Icc] at h1 h2; omega
      rw [hsplit, Finset.prod_union hdisj]
      have hrev : (∏ t ∈ Finset.Icc ((p - 1) / 2 + 1) (p - 1), F t) =
          ∏ t ∈ Finset.Icc 1 ((p - 1) / 2), F (p - t) := by
        refine Finset.prod_bij (fun t _ => p - t) ?_ ?_ ?_ ?_
        · intro t ht; simp only [Finset.mem_Icc] at ht ⊢; omega
        · intro a ha b hb h; simp only [Finset.mem_Icc] at ha hb; omega
        · intro t ht; simp only [Finset.mem_Icc] at ht
          exact ⟨p - t, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
        · intro t ht; simp only [Finset.mem_Icc] at ht; rw [Nat.sub_sub_self (by omega)]
      rw [hrev, ← Finset.prod_mul_distrib, Finset.prod_congr rfl hpair, zmod_prod_one_add_p2]
      have hsum_eq :
          (∑ t ∈ Finset.Icc 1 ((p - 1) / 2),
              -(3 : ZMod (p ^ 3)) * (M : ZMod (p ^ 3)) * ((t : ZMod (p ^ 3))⁻¹) ^ 2) *
            (p : ZMod (p ^ 3)) ^ 2 =
          -(M : ZMod (p ^ 3)) *
            ((3 : ZMod (p ^ 3)) *
              (∑ t ∈ Finset.Icc 1 ((p - 1) / 2), ((t : ZMod (p ^ 3))⁻¹) ^ 2) *
              (p : ZMod (p ^ 3)) ^ 2) := by
        rw [← Finset.mul_sum]; ring
      rw [hsum_eq, sum_inv_sq_mul_three_p2 hp hp3, mul_zero, add_zero]

private lemma master_cong {p d : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hd : 1 ≤ d) :
    ∃ z : ℕ, a (p ^ d) = (z : ℚ) ∧
      (z : ZMod (p ^ 3)) = (2 : ZMod (p ^ 3)) ^ ((p ^ d + 1) / 2) := by
  have hp_pos : 0 < p := hp.pos
  have hodd_p : Odd p := Nat.odd_iff.mpr (hp.eq_two_or_odd.resolve_left (by omega))
  have hodd_pd : Odd (p ^ d) := hodd_p.pow
  let M := (p ^ d + 1) / 2
  -- Define stratum numerators and denominators in ℕ
  let S : ℕ → Finset ℕ := fun e => (Finset.Icc 1 (p ^ (d - e) - 1)).filter fun t => ¬ p ∣ t
  let strNum : ℕ → ℕ := fun e =>
    ∏ t ∈ S e, (p ^ (d - e) + t) ^ ((p ^ e * t + 1) / 2) *
               (2 * p ^ (d - e) + t) ^ (M - (p ^ e * t + 1) / 2)
  let strDen : ℕ → ℕ := fun e =>
    ∏ t ∈ S e, t ^ ((p ^ e * t + 1) / 2) *
               (p ^ (d - e) + t) ^ (M - (p ^ e * t + 1) / 2)
  let N_all : ℕ := ∏ e ∈ Finset.range d, strNum e
  let D_all : ℕ := ∏ e ∈ Finset.range d, strDen e
  have hD_cop : Nat.Coprime D_all p := by
    refine Nat.Coprime.prod_left fun e he => ?_
    have hed : e < d := Finset.mem_range.mp he
    refine Nat.Coprime.prod_left fun t ht => ?_
    have hnd := (Finset.mem_filter.mp ht).2
    have hct : Nat.Coprime t p := (hp.coprime_iff_not_dvd.mpr hnd).symm
    have hpq : p ∣ p ^ (d - e) := dvd_pow_self p (by omega)
    have hnd' : ¬ p ∣ p ^ (d - e) + t := fun h => hnd ((Nat.dvd_add_right hpq).mp h)
    have hcqt : Nat.Coprime (p ^ (d - e) + t) p := (hp.coprime_iff_not_dvd.mpr hnd').symm
    exact (hct.pow_left _).mul_left (hcqt.pow_left _)
  have hD_pos : 0 < D_all := by
    by_contra h0
    have hD0 : D_all = 0 := by omega
    rw [hD0, Nat.coprime_zero_left] at hD_cop
    omega
  -- Show a (p ^ d) = 2 ^ M * N_all / D_all in ℚ via p-adic valuation stratification of r ∈ Icc 1 (p^d - 1)
  have ha_rat : a (p ^ d) = (2 : ℚ) ^ M * (N_all : ℚ) / (D_all : ℚ) := by
    rw [a_odd_formula (p ^ d) hodd_pd]
    rw [mul_div_assoc]
    congr 1
    -- Split Icc 1 (p^d - 1) into disjoint strata e ∈ range d via (e, t) ↦ p^e * t
    have hbij :
        (∏ r ∈ Finset.Icc 1 (p ^ d - 1),
          ((((p ^ d + r : ℕ) : ℚ) / (r : ℚ)) ^ ((r + 1) / 2) *
           (((2 * p ^ d + r : ℕ) : ℚ) / ((p ^ d + r : ℕ) : ℚ)) ^ (M - (r + 1) / 2))) =
        ∏ e ∈ Finset.range d, (strNum e : ℚ) / (strDen e : ℚ) := by
      have hsigma :
          (∏ e ∈ Finset.range d, (strNum e : ℚ) / (strDen e : ℚ)) =
          ∏ x ∈ (Finset.range d).sigma S,
            ((((p ^ (d - x.1) + x.2 : ℕ) : ℚ) / (x.2 : ℚ)) ^ ((p ^ x.1 * x.2 + 1) / 2) *
             (((2 * p ^ (d - x.1) + x.2 : ℕ) : ℚ) / ((p ^ (d - x.1) + x.2 : ℕ) : ℚ)) ^
               (M - (p ^ x.1 * x.2 + 1) / 2)) := by
        simp only [Finset.prod_sigma]
        refine Finset.prod_congr rfl fun e _ => ?_
        dsimp only [strNum, strDen]
        push_cast
        rw [← Finset.prod_div_distrib]
        refine Finset.prod_congr rfl fun t _ => ?_
        rw [div_pow, div_pow, mul_div_mul_comm]
      rw [hsigma]
      symm
      refine Finset.prod_bij (fun x _ => p ^ x.1 * x.2) ?_ ?_ ?_ ?_
      · intro x hx
        rcases Finset.mem_sigma.mp hx with ⟨he, ht⟩
        have hed : x.1 < d := Finset.mem_range.mp he
        have htb := Finset.mem_Icc.mp (Finset.mem_filter.mp ht).1
        have hpe_pos : 1 ≤ p ^ x.1 := Nat.one_le_pow x.1 p hp_pos
        have hq_pos : 1 ≤ p ^ (d - x.1) := Nat.one_le_pow _ p hp_pos
        have hxt_lt : x.2 < p ^ (d - x.1) := by omega
        have hprod : p ^ x.1 * p ^ (d - x.1) = p ^ d := by
          rw [← pow_add, show x.1 + (d - x.1) = d by omega]
        have hlt_pd : p ^ x.1 * x.2 < p ^ d := by
          rw [← hprod]; exact Nat.mul_lt_mul_of_pos_left hxt_lt (pow_pos hp_pos x.1)
        simp only [Finset.mem_Icc]
        exact ⟨by nlinarith, by omega⟩
      · intro x1 hx1 x2 hx2 heq
        rcases Finset.mem_sigma.mp hx1 with ⟨_, ht1⟩
        rcases Finset.mem_sigma.mp hx2 with ⟨_, ht2⟩
        have hnd1 := (Finset.mem_filter.mp ht1).2
        have hnd2 := (Finset.mem_filter.mp ht2).2
        have ht1_pos : 0 < x1.2 := by have := (Finset.mem_Icc.mp (Finset.mem_filter.mp ht1).1).1; omega
        have ht2_pos : 0 < x2.2 := by have := (Finset.mem_Icc.mp (Finset.mem_filter.mp ht2).1).1; omega
        have hfac := congrArg (fun k => k.factorization p) heq
        rw [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) (Nat.ne_of_gt ht1_pos),
            Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) (Nat.ne_of_gt ht2_pos)] at hfac
        simp only [Finsupp.coe_add, Pi.add_apply, hp.factorization_pow, Finsupp.single_eq_same,
          Nat.factorization_eq_zero_of_not_dvd hnd1, Nat.factorization_eq_zero_of_not_dvd hnd2,
          add_zero] at hfac
        rcases x1 with ⟨e1, t1⟩; rcases x2 with ⟨e2, t2⟩
        dsimp at hfac heq
        subst hfac
        have ht_eq : t1 = t2 := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (pow_ne_zero e1 hp.ne_zero)) heq
        subst ht_eq; rfl
      · intro r hr
        have hrb := Finset.mem_Icc.mp hr
        have hr_ne : r ≠ 0 := by omega
        let e := r.factorization p
        have hpe_dvd : p ^ e ∣ r := Nat.ordProj_dvd r p
        rcases hpe_dvd with ⟨t, ht_eq⟩
        have hed : e < d := by
          by_contra hge; push Not at hge
          have hdvd : p ^ d ∣ r := dvd_trans (pow_dvd_pow p hge) ⟨t, ht_eq⟩
          have := Nat.le_of_dvd (by omega) hdvd; omega
        have hnd : ¬ p ∣ t := by
          intro hpt
          have hpe1 : p ^ (e + 1) ∣ r := by
            rcases hpt with ⟨u, rfl⟩
            exact ⟨u, by rw [ht_eq, pow_succ]; ring⟩
          have hle := (hp.pow_dvd_iff_le_factorization hr_ne).mp hpe1
          dsimp only [e] at hle; omega
        have hprod : p ^ e * p ^ (d - e) = p ^ d := by
          rw [← pow_add, show e + (d - e) = d by omega]
        have ht1 : 1 ≤ t := by
          by_contra h0; have : t = 0 := by omega
          rw [this, mul_zero] at ht_eq; omega
        have ht2 : t ≤ p ^ (d - e) - 1 := by
          have hlt : p ^ e * t < p ^ e * p ^ (d - e) := by rw [← ht_eq, hprod]; omega
          have := Nat.lt_of_mul_lt_mul_left hlt; omega
        refine ⟨⟨e, t⟩, Finset.mem_sigma.mpr ⟨Finset.mem_range.mpr hed,
          Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨ht1, ht2⟩, hnd⟩⟩, ht_eq.symm⟩
      · intro x hx
        rcases Finset.mem_sigma.mp hx with ⟨he, _⟩
        have hed : x.1 < d := Finset.mem_range.mp he
        have hprod : p ^ x.1 * p ^ (d - x.1) = p ^ d := by
          rw [← pow_add, show x.1 + (d - x.1) = d by omega]
        have hpe_ne : ((p : ℚ) ^ x.1) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.ne_zero)
        have hnum1 : ((p ^ d + p ^ x.1 * x.2 : ℕ) : ℚ) / ((p ^ x.1 * x.2 : ℕ) : ℚ) =
            ((p ^ (d - x.1) + x.2 : ℕ) : ℚ) / (x.2 : ℚ) := by
          rw [← hprod, ← mul_add]
          push_cast
          exact mul_div_mul_left _ _ hpe_ne
        have hnum2 : ((2 * p ^ d + p ^ x.1 * x.2 : ℕ) : ℚ) / ((p ^ d + p ^ x.1 * x.2 : ℕ) : ℚ) =
            ((2 * p ^ (d - x.1) + x.2 : ℕ) : ℚ) / ((p ^ (d - x.1) + x.2 : ℕ) : ℚ) := by
          have h1 : 2 * p ^ d + p ^ x.1 * x.2 = p ^ x.1 * (2 * p ^ (d - x.1) + x.2) := by
            rw [← hprod]; ring
          have h2 : p ^ d + p ^ x.1 * x.2 = p ^ x.1 * (p ^ (d - x.1) + x.2) := by
            rw [← hprod]; ring
          rw [h1, h2]; push_cast
          exact mul_div_mul_left _ _ hpe_ne
        rw [hnum1, hnum2]
    rw [hbij, Finset.prod_div_distrib]
    dsimp only [N_all, D_all]
    push_cast
    rfl
  -- Show (N_all : ZMod (p^3)) = (D_all : ZMod (p^3))
  have hND_zmod : (N_all : ZMod (p ^ 3)) = (D_all : ZMod (p ^ 3)) := by
    dsimp only [N_all, D_all]
    push_cast
    refine Finset.prod_congr rfl fun e he => ?_
    have hed : e < d := Finset.mem_range.mp he
    have hstr := stratum_zmod_eq_one hp hp3 hd hed
    have hDe_u : IsUnit (strDen e : ZMod (p ^ 3)) := by
      refine (ZMod.isUnit_iff_coprime (strDen e) (p ^ 3)).mpr ?_
      refine Nat.Coprime.pow_right 3 ?_
      refine Nat.Coprime.prod_left fun t ht => ?_
      have hnd := (Finset.mem_filter.mp ht).2
      have hct : Nat.Coprime t p := (hp.coprime_iff_not_dvd.mpr hnd).symm
      have hpq : p ∣ p ^ (d - e) := dvd_pow_self p (by omega)
      have hnd' : ¬ p ∣ p ^ (d - e) + t := fun h => hnd ((Nat.dvd_add_right hpq).mp h)
      have hcqt : Nat.Coprime (p ^ (d - e) + t) p := (hp.coprime_iff_not_dvd.mpr hnd').symm
      exact (hct.pow_left _).mul_left (hcqt.pow_left _)
    have hmul_eq : (strNum e : ZMod (p ^ 3)) * (strDen e : ZMod (p ^ 3))⁻¹ = 1 := by
      have hinv_prod : ∀ t ∈ S e,
          ((p ^ (d - e) + t : ℕ) : ZMod (p ^ 3)) ^ ((p ^ e * t + 1) / 2) *
          ((2 * p ^ (d - e) + t : ℕ) : ZMod (p ^ 3)) ^ (M - (p ^ e * t + 1) / 2) =
          ((((p ^ (d - e) + t : ℕ) : ZMod (p ^ 3)) * (t : ZMod (p ^ 3))⁻¹) ^ ((p ^ e * t + 1) / 2) *
           (((2 * p ^ (d - e) + t : ℕ) : ZMod (p ^ 3)) * ((p ^ (d - e) + t : ℕ) : ZMod (p ^ 3))⁻¹) ^
             (M - (p ^ e * t + 1) / 2)) *
          ((t : ZMod (p ^ 3)) ^ ((p ^ e * t + 1) / 2) *
           ((p ^ (d - e) + t : ℕ) : ZMod (p ^ 3)) ^ (M - (p ^ e * t + 1) / 2)) := by
        intro t ht
        have hnd := (Finset.mem_filter.mp ht).2
        have hu_t : IsUnit (t : ZMod (p ^ 3)) :=
          (ZMod.isUnit_iff_coprime t (p ^ 3)).mpr ((hp.coprime_iff_not_dvd.mpr hnd).symm.pow_right 3)
        have hpq : p ∣ p ^ (d - e) := dvd_pow_self p (by omega)
        have hnd' : ¬ p ∣ p ^ (d - e) + t := fun h => hnd ((Nat.dvd_add_right hpq).mp h)
        have hu_qt : IsUnit ((p ^ (d - e) + t : ℕ) : ZMod (p ^ 3)) :=
          (ZMod.isUnit_iff_coprime (p ^ (d - e) + t) (p ^ 3)).mpr
            ((hp.coprime_iff_not_dvd.mpr hnd').symm.pow_right 3)
        have ht_inv : (t : ZMod (p ^ 3))⁻¹ * (t : ZMod (p ^ 3)) = 1 := by
          rw [mul_comm]; exact ZMod.mul_inv_of_unit _ hu_t
        have hqt_inv : ((p ^ (d - e) + t : ℕ) : ZMod (p ^ 3))⁻¹ * ((p ^ (d - e) + t : ℕ) : ZMod (p ^ 3)) = 1 := by
          rw [mul_comm]; exact ZMod.mul_inv_of_unit _ hu_qt
        rw [mul_pow, mul_pow]
        calc ((p ^ (d - e) + t : ℕ) : ZMod (p ^ 3)) ^ ((p ^ e * t + 1) / 2) *
              ((2 * p ^ (d - e) + t : ℕ) : ZMod (p ^ 3)) ^ (M - (p ^ e * t + 1) / 2)
            = ((p ^ (d - e) + t : ℕ) : ZMod (p ^ 3)) ^ ((p ^ e * t + 1) / 2) *
                (((t : ZMod (p ^ 3))⁻¹ * (t : ZMod (p ^ 3))) ^ ((p ^ e * t + 1) / 2)) *
              (((2 * p ^ (d - e) + t : ℕ) : ZMod (p ^ 3)) ^ (M - (p ^ e * t + 1) / 2) *
                (((p ^ (d - e) + t : ℕ) : ZMod (p ^ 3))⁻¹ * ((p ^ (d - e) + t : ℕ) : ZMod (p ^ 3))) ^
                  (M - (p ^ e * t + 1) / 2)) := by
              rw [ht_inv, hqt_inv, one_pow, one_pow, mul_one, mul_one]
          _ = _ := by rw [mul_pow, mul_pow]; ring
      have hnum_eq : (strNum e : ZMod (p ^ 3)) = (strDen e : ZMod (p ^ 3)) := by
        dsimp only [strNum, strDen]
        rw [Nat.cast_prod, Nat.cast_prod]
        simp_rw [Nat.cast_mul, Nat.cast_pow]
        rw [Finset.prod_congr rfl hinv_prod, Finset.prod_mul_distrib]
        dsimp only [S, M] at hstr ⊢
        rw [hstr, one_mul]
      rw [hnum_eq, ZMod.mul_inv_of_unit _ hDe_u]
    calc (strNum e : ZMod (p ^ 3))
        = (strNum e : ZMod (p ^ 3)) * ((strDen e : ZMod (p ^ 3))⁻¹ * (strDen e : ZMod (p ^ 3))) := by
          rw [mul_comm _ (strDen e : ZMod (p ^ 3)), ZMod.mul_inv_of_unit _ hDe_u, mul_one]
      _ = ((strNum e : ZMod (p ^ 3)) * (strDen e : ZMod (p ^ 3))⁻¹) * (strDen e : ZMod (p ^ 3)) := by ring
      _ = (strDen e : ZMod (p ^ 3)) := by rw [hmul_eq, one_mul]
  -- Combine with integrality a (p^d) = z
  rcases a_eq_nat (p ^ d) with ⟨z, hz⟩
  refine ⟨z, hz, ?_⟩
  have hnat_eq : z * D_all = 2 ^ M * N_all := by
    have hq : (z : ℚ) * (D_all : ℚ) = (2 : ℚ) ^ M * (N_all : ℚ) := by
      rw [← hz, ha_rat, div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hD_pos))]
    exact_mod_cast hq
  have hzmod_eq : (z : ZMod (p ^ 3)) * (D_all : ZMod (p ^ 3)) =
      (2 : ZMod (p ^ 3)) ^ M * (N_all : ZMod (p ^ 3)) := by
    have := congrArg (Nat.cast (R := ZMod (p ^ 3))) hnat_eq
    push_cast at this; exact this
  rw [hND_zmod] at hzmod_eq
  have hDu : IsUnit (D_all : ZMod (p ^ 3)) :=
    (ZMod.isUnit_iff_coprime D_all (p ^ 3)).mpr (hD_cop.pow_right 3)
  exact hDu.mul_right_cancel hzmod_eq

private lemma two_pow_half_totient_eq {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) :
    (2 : ZMod (p ^ 3)) ^ (p ^ 2 * (p - 1) / 2) =
      ((-1 : ℤ) ^ ((p ^ 2 - 1) / 8) : ZMod (p ^ 3)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hodd_p : Odd p := Nat.odd_iff.mpr (hp.eq_two_or_odd.resolve_left (by omega))
  have h2cop : Nat.Coprime 2 (p ^ 3) :=
    (hp.coprime_iff_not_dvd.mpr (fun h => by have := Nat.le_of_dvd (by omega) h; omega)).symm.pow_right 3
  let u2 : (ZMod (p ^ 3))ˣ := ZMod.unitOfCoprime 2 h2cop
  have hu2_val : (u2 : ZMod (p ^ 3)) = 2 := ZMod.coe_unitOfCoprime 2 h2cop
  set x : ZMod (p ^ 3) := (2 : ZMod (p ^ 3)) ^ (p ^ 2 * (p - 1) / 2)
  have hx2 : x ^ 2 = 1 := by
    dsimp only [x]
    rw [← pow_mul]
    have hexp : p ^ 2 * (p - 1) / 2 * 2 = (p ^ 3).totient := by
      rw [Nat.totient_prime_pow hp (by omega)]
      have hev : Even (p - 1) := by rcases hodd_p with ⟨k, rfl⟩; exact ⟨k, by omega⟩
      rcases hev with ⟨k, hk⟩
      have h1 : p ^ 2 * (p - 1) = 2 * (p ^ 2 * k) := by rw [hk]; ring
      rw [h1, Nat.mul_div_cancel_left _ (by omega)]
      ring
    rw [hexp, ← hu2_val, ← Units.val_pow_eq_pow_val, ZMod.pow_totient, Units.val_one]
  -- From x^2 = 1 in ZMod (p^3), deduce x = 1 ∨ x = -1
  have hx_pm : x = 1 ∨ x = -1 := by
    have h0 : (x - 1) * (x + 1) = 0 := by linear_combination hx2
    -- In ℤ, p^3 ∣ (x.val - 1) * (x.val + 1), and p cannot divide both!
    have hprod_dvd : ((p ^ 3 : ℕ) : ℤ) ∣ ((x.val : ℤ) - 1) * ((x.val : ℤ) + 1) := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [ZMod.natCast_zmod_val]
      exact h0
    have hp_prime_int : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    have hnot_both : ¬ ((p : ℤ) ∣ ((x.val : ℤ) - 1) ∧ (p : ℤ) ∣ ((x.val : ℤ) + 1)) := by
      rintro ⟨h1, h2⟩
      have hdiff : (p : ℤ) ∣ ((x.val : ℤ) + 1) - ((x.val : ℤ) - 1) := dvd_sub h2 h1
      have h2eq : ((x.val : ℤ) + 1) - ((x.val : ℤ) - 1) = (2 : ℤ) := by ring
      rw [h2eq] at hdiff
      have hnat : p ∣ 2 := Int.ofNat_dvd.mp hdiff
      have := Nat.le_of_dvd (by omega) hnat; omega
    by_cases h1 : (p : ℤ) ∣ ((x.val : ℤ) - 1)
    · left
      have hnot2 : ¬ (p : ℤ) ∣ ((x.val : ℤ) + 1) := fun h2 => hnot_both ⟨h1, h2⟩
      have hcop : IsCoprime ((p : ℤ) ^ 3) ((x.val : ℤ) + 1) :=
        ((hp_prime_int.coprime_iff_not_dvd).mpr hnot2).pow_left
      have hdvd1 : ((p ^ 3 : ℕ) : ℤ) ∣ ((x.val : ℤ) - 1) := by
        push_cast at hprod_dvd ⊢
        exact hcop.dvd_of_dvd_mul_right hprod_dvd
      have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdvd1
      push_cast at hz
      rw [ZMod.natCast_zmod_val] at hz
      exact sub_eq_zero.mp hz
    · right
      have hcop : IsCoprime ((p : ℤ) ^ 3) ((x.val : ℤ) - 1) :=
        ((hp_prime_int.coprime_iff_not_dvd).mpr h1).pow_left
      have hdvd2 : ((p ^ 3 : ℕ) : ℤ) ∣ ((x.val : ℤ) + 1) := by
        push_cast at hprod_dvd ⊢
        exact hcop.dvd_of_dvd_mul_left hprod_dvd
      have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdvd2
      push_cast at hz
      rw [ZMod.natCast_zmod_val] at hz
      exact eq_neg_of_add_eq_zero_left hz
  -- Compare images in ZMod p via legendreSym.eq_pow and legendreSym.at_two
  let f : ZMod (p ^ 3) →+* ZMod p := ZMod.castHom (dvd_pow_self p (by omega)) (ZMod p)
  have hchi8 : ZMod.χ₈ (p : ZMod 8) = (-1 : ℤ) ^ ((p ^ 2 - 1) / 8) := by
    have hmod : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by
      rcases hodd_p with ⟨k, rfl⟩; omega
    have hcast8 : (p : ZMod 8) = ((p % 8 : ℕ) : ZMod 8) := by
      rw [ZMod.natCast_eq_natCast_iff]; exact (Nat.mod_modEq p 8).symm
    have hdiv8 : ∀ r : ℕ, 1 ≤ r → p % 8 = r → (p ^ 2 - 1) / 8 % 2 = (r ^ 2 - 1) / 8 % 2 := by
      intro r hr1 hr
      let q := p / 8
      have hpq : p = 8 * q + r := by rw [← hr]; exact (Nat.div_add_mod p 8).symm
      have hsq : p ^ 2 - 1 = 8 * (2 * (4 * q ^ 2 + q * r)) + (r ^ 2 - 1) := by
        rw [hpq]
        have hr2 : 1 ≤ r ^ 2 := by nlinarith
        have h1 : (8 * q + r) ^ 2 = 8 * (2 * (4 * q ^ 2 + q * r)) + r ^ 2 := by ring
        omega
      rw [hsq, Nat.mul_add_div (by omega)]
      omega
    rcases hmod with h | h | h | h
    · have hev : Even ((p ^ 2 - 1) / 8) := by
        rw [Nat.even_iff, hdiv8 1 (by omega) h]; decide
      rw [hcast8, h, hev.neg_one_pow]; decide
    · have hodd' : Odd ((p ^ 2 - 1) / 8) := by
        rw [Nat.odd_iff, hdiv8 3 (by omega) h]; decide
      rw [hcast8, h, hodd'.neg_one_pow]; decide
    · have hodd' : Odd ((p ^ 2 - 1) / 8) := by
        rw [Nat.odd_iff, hdiv8 5 (by omega) h]; decide
      rw [hcast8, h, hodd'.neg_one_pow]; decide
    · have hev : Even ((p ^ 2 - 1) / 8) := by
        rw [Nat.even_iff, hdiv8 7 (by omega) h]; decide
      rw [hcast8, h, hev.neg_one_pow]; decide
  have hfx : f x = (((-1 : ℤ) ^ ((p ^ 2 - 1) / 8) : ℤ) : ZMod p) := by
    dsimp only [x]
    rw [map_pow, map_ofNat]
    have hexp : p ^ 2 * (p - 1) / 2 = (p / 2) * p ^ 2 := by
      rcases hodd_p with ⟨k, rfl⟩
      have h1 : (2 * k + 1) / 2 = k := by omega
      have hsub : 2 * k + 1 - 1 = 2 * k := by omega
      have h2 : (2 * k + 1) ^ 2 * (2 * k + 1 - 1) = 2 * (k * (2 * k + 1) ^ 2) := by
        rw [hsub]; ring
      rw [h1, h2, Nat.mul_div_cancel_left _ (by omega)]
    rw [hexp, pow_mul]
    have hleg := legendreSym.eq_pow p 2
    rw [legendreSym.at_two (by omega), hchi8] at hleg
    have h2eq : ((2 : ℤ) : ZMod p) = (2 : ZMod p) := by norm_num
    rw [h2eq] at hleg
    rw [← hleg]
    have hodd_p2 : Odd (p ^ 2) := hodd_p.pow
    push_cast
    rw [← pow_mul]
    rcases Nat.even_or_odd ((p ^ 2 - 1) / 8) with hev | hodd'
    · rw [hev.neg_one_pow, (hev.mul_right (p ^ 2)).neg_one_pow]
    · rw [hodd'.neg_one_pow, (hodd'.mul hodd_p2).neg_one_pow]
  have hne_pm : (1 : ZMod p) ≠ (-1 : ZMod p) := by
    intro h
    have h20 : ((2 : ℕ) : ZMod p) = 0 := by push_cast; linear_combination h
    have := (ZMod.natCast_eq_zero_iff 2 p).mp h20
    have := Nat.le_of_dvd (by omega) this; omega
  rcases Nat.even_or_odd ((p ^ 2 - 1) / 8) with hev | hodd'
  · rw [hev.neg_one_pow] at hfx
    rw [← Int.cast_pow, hev.neg_one_pow, Int.cast_one]
    rcases hx_pm with hx1 | hxm1
    · exact hx1
    · rw [hxm1, map_neg, map_one] at hfx
      exact absurd (by simpa using hfx.symm) hne_pm
  · rw [hodd'.neg_one_pow] at hfx
    rw [← Int.cast_pow, hodd'.neg_one_pow, Int.cast_neg, Int.cast_one]
    rcases hx_pm with hx1 | hxm1
    · rw [hx1, map_one] at hfx
      exact absurd (by simpa using hfx) hne_pm
    · exact hxm1

private lemma dvd_sub_of_zmod_eq {p : ℕ} {A B : ℤ} (h : (A : ZMod (p ^ 3)) = (B : ZMod (p ^ 3))) :
    ∃ m : ℤ, (A : ℚ) - (B : ℚ) = (p : ℚ) ^ 3 * (m : ℚ) := by
  have hdvd : ((p ^ 3 : ℕ) : ℤ) ∣ A - B := (ZMod.intCast_eq_intCast_iff_dvd_sub B A (p ^ 3)).mp h.symm
  rcases hdvd with ⟨m, hm⟩
  refine ⟨m, ?_⟩
  have hq : ((A - B : ℤ) : ℚ) = (((p ^ 3 : ℕ) : ℤ) * m : ℤ) := by exact_mod_cast hm
  push_cast at hq
  exact hq

end MasterCongruence

end OMA.S_oeis_a049505

theorem OMA.solution : type_of% @OMA.S_oeis_a049505.main := by
  refine ⟨?_, ?_, ?_⟩
  · -- Conjecture 1: a(p) == 2^((p+1)/2) (mod p^3) for all primes p >= 3
    intro p hp hp3
    rcases OMA.S_oeis_a049505.master_cong (d := 1) hp hp3 (by omega) with ⟨z, hz, hcong⟩
    rw [pow_one] at hz hcong
    have hz_int : ((z : ℤ) : ZMod (p ^ 3)) = (((2 : ℤ) ^ ((p + 1) / 2) : ℤ) : ZMod (p ^ 3)) := by
      push_cast; exact hcong
    rcases OMA.S_oeis_a049505.dvd_sub_of_zmod_eq hz_int with ⟨m, hm⟩
    refine ⟨m, ?_⟩
    rw [hz]
    simpa using hm
  · -- Conjecture 2: a(p^2) == (-1)^((p^2-1)/8) * a(p)^(p^2 - p + 1) (mod p^3) for all primes p >= 3
    intro p hp hp3
    rcases OMA.S_oeis_a049505.master_cong (d := 1) hp hp3 (by omega) with ⟨z1, hz1, hc1⟩
    rcases OMA.S_oeis_a049505.master_cong (d := 2) hp hp3 (by omega) with ⟨z2, hz2, hc2⟩
    rw [pow_one] at hz1 hc1
    have hodd_p : Odd p := Nat.odd_iff.mpr (hp.eq_two_or_odd.resolve_left (by omega))
    have hcong : ((z2 : ℤ) : ZMod (p ^ 3)) =
        (((-1 : ℤ) ^ ((p ^ 2 - 1) / 8) * (z1 : ℤ) ^ (p ^ 2 - p + 1) : ℤ) : ZMod (p ^ 3)) := by
      push_cast
      rw [hc1, hc2, ← pow_mul]
      have hexp : (p + 1) / 2 * (p ^ 2 - p + 1) = (p ^ 2 + 1) / 2 + p ^ 2 * (p - 1) / 2 := by
        rcases hodd_p with ⟨k, rfl⟩
        have h1 : (2 * k + 1 + 1) / 2 = k + 1 := by omega
        have h2 : ((2 * k + 1) ^ 2 + 1) / 2 = 2 * k ^ 2 + 2 * k + 1 := by
          have : (2 * k + 1) ^ 2 + 1 = 2 * (2 * k ^ 2 + 2 * k + 1) := by ring
          omega
        have h3 : (2 * k + 1) ^ 2 * (2 * k + 1 - 1) / 2 = (2 * k + 1) ^ 2 * k := by
          have hsub : 2 * k + 1 - 1 = 2 * k := by omega
          rw [hsub, show (2 * k + 1) ^ 2 * (2 * k) = 2 * ((2 * k + 1) ^ 2 * k) by ring,
              Nat.mul_div_cancel_left _ (by omega)]
        have h4 : (2 * k + 1) ^ 2 - (2 * k + 1) + 1 = 4 * k ^ 2 + 2 * k + 1 := by
          have : 2 * k + 1 ≤ (2 * k + 1) ^ 2 := by nlinarith
          zify [this]; ring
        rw [h1, h2, h3, h4]; ring
      rw [hexp, pow_add, OMA.S_oeis_a049505.two_pow_half_totient_eq hp hp3]
      push_cast
      have hsq : ((-1 : ZMod (p ^ 3)) ^ ((p ^ 2 - 1) / 8)) * ((-1 : ZMod (p ^ 3)) ^ ((p ^ 2 - 1) / 8)) = 1 := by
        rw [← pow_add, ← two_mul, pow_mul]; norm_num
      calc (2 : ZMod (p ^ 3)) ^ ((p ^ 2 + 1) / 2)
          = ((-1 : ZMod (p ^ 3)) ^ ((p ^ 2 - 1) / 8) * (-1 : ZMod (p ^ 3)) ^ ((p ^ 2 - 1) / 8)) *
              (2 : ZMod (p ^ 3)) ^ ((p ^ 2 + 1) / 2) := by rw [hsq, one_mul]
        _ = (-1 : ZMod (p ^ 3)) ^ ((p ^ 2 - 1) / 8) *
              ((2 : ZMod (p ^ 3)) ^ ((p ^ 2 + 1) / 2) * (-1 : ZMod (p ^ 3)) ^ ((p ^ 2 - 1) / 8)) := by ring
    rcases OMA.S_oeis_a049505.dvd_sub_of_zmod_eq hcong with ⟨m, hm⟩
    refine ⟨m, ?_⟩
    rw [hz1, hz2]
    simpa using hm
  · -- Conjecture 3: a(p^3) == a(p^2)^((p^3 - p^2 + 2)/2) (mod p^3) for all primes p >= 2
    intro p hp
    by_cases hp2 : p = 2
    · subst hp2
      refine ⟨339914081866, ?_⟩
      norm_num [OMA.S_oeis_a049505.a, Finset.prod_Icc_succ_top]
    · have hp3 : 3 ≤ p := by have := hp.two_le; omega
      have hodd_p : Odd p := Nat.odd_iff.mpr (hp.eq_two_or_odd.resolve_left hp2)
      rcases OMA.S_oeis_a049505.master_cong (d := 2) hp hp3 (by omega) with ⟨z2, hz2, hc2⟩
      rcases OMA.S_oeis_a049505.master_cong (d := 3) hp hp3 (by omega) with ⟨z3, hz3, hc3⟩
      have h2cop : Nat.Coprime 2 (p ^ 3) :=
        (hp.coprime_iff_not_dvd.mpr (fun h => by have := Nat.le_of_dvd (by omega) h; omega)).symm.pow_right 3
      let u2 : (ZMod (p ^ 3))ˣ := ZMod.unitOfCoprime 2 h2cop
      have hu2_val : (u2 : ZMod (p ^ 3)) = 2 := ZMod.coe_unitOfCoprime 2 h2cop
      have h2tot : (2 : ZMod (p ^ 3)) ^ (p ^ 3).totient = 1 := by
        rw [← hu2_val, ← Units.val_pow_eq_pow_val, ZMod.pow_totient, Units.val_one]
      have hcong : ((z3 : ℤ) : ZMod (p ^ 3)) =
          (((z2 : ℤ) ^ ((p ^ 3 - p ^ 2 + 2) / 2) : ℤ) : ZMod (p ^ 3)) := by
        push_cast
        rw [hc2, hc3, ← pow_mul]
        have hexp : (p ^ 2 + 1) / 2 * ((p ^ 3 - p ^ 2 + 2) / 2) =
            (p ^ 3 + 1) / 2 + (p ^ 3).totient * ((p ^ 2 - 1) / 4) := by
          rw [Nat.totient_prime_pow hp (by omega)]
          rcases hodd_p with ⟨k, rfl⟩
          have h1 : ((2 * k + 1) ^ 2 + 1) / 2 = 2 * k ^ 2 + 2 * k + 1 := by
            have : (2 * k + 1) ^ 2 + 1 = 2 * (2 * k ^ 2 + 2 * k + 1) := by ring
            omega
          have h2 : ((2 * k + 1) ^ 3 - (2 * k + 1) ^ 2 + 2) / 2 = 4 * k ^ 3 + 4 * k ^ 2 + k + 1 := by
            have hle : (2 * k + 1) ^ 2 ≤ (2 * k + 1) ^ 3 := by nlinarith
            have : (2 * k + 1) ^ 3 - (2 * k + 1) ^ 2 + 2 = 2 * (4 * k ^ 3 + 4 * k ^ 2 + k + 1) := by
              zify [hle]; ring
            omega
          have h3 : ((2 * k + 1) ^ 3 + 1) / 2 = 4 * k ^ 3 + 6 * k ^ 2 + 3 * k + 1 := by
            have : (2 * k + 1) ^ 3 + 1 = 2 * (4 * k ^ 3 + 6 * k ^ 2 + 3 * k + 1) := by ring
            omega
          have h4 : ((2 * k + 1) ^ 2 - 1) / 4 = k ^ 2 + k := by
            have : (2 * k + 1) ^ 2 - 1 = 4 * (k ^ 2 + k) := by
              have : 1 ≤ (2 * k + 1) ^ 2 := by nlinarith
              zify [this]; ring
            omega
          have h5 : 2 * k + 1 - 1 = 2 * k := by omega
          rw [h1, h2, h3, h4, h5]; ring
        rw [hexp, pow_add, pow_mul, h2tot, one_pow, mul_one]
      rcases OMA.S_oeis_a049505.dvd_sub_of_zmod_eq hcong with ⟨m, hm⟩
      refine ⟨m, ?_⟩
      rw [hz2, hz3]
      simpa using hm
