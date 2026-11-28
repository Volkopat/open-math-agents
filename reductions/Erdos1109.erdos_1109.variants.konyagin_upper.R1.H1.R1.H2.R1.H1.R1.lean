import OMAReductions.R_Erdos1109_erdos_1109_variants_konyagin_upper_R1_H1_R1_H2_R1
import Mathlib

/-!
# Spacing reduction for the primitive square-denominator large sieve

Uses the decomposition of Konyagin, Problems on the set of squarefree numbers,
Theorem 2 and Lemma 2, https://www.mathnet.ru/eng/im486.
-/

namespace OMA.R_Erdos1109_erdos_1109_variants_konyagin_upper_R1_H1_R1_H2_R1_H1_R1

open Filter Finset Real
open scoped Topology

private theorem sum_union_bound {ι : Type} [DecidableEq ι] (B J : Finset ι) (f : ι → ℝ)
    (hf : ∀ j, 0 ≤ f j) : ∑ j ∈ B ∪ J, f j ≤ (∑ j ∈ B, f j) + ∑ j ∈ J, f j := by
  have hI : 0 ≤ ∑ j ∈ B ∩ J, f j := sum_nonneg fun j _ => hf j
  linarith [sum_union_inter (s₁ := B) (s₂ := J) (f := f)]

private theorem sum_biUnion_bound {ι κ : Type} [DecidableEq ι] [DecidableEq κ]
    (S : Finset κ) (K : κ → Finset ι) (f : ι → ℝ) (hf : ∀ j, 0 ≤ f j) :
    ∑ j ∈ S.biUnion K, f j ≤ ∑ k ∈ S, ∑ j ∈ K k, f j := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert k S hk ih =>
    rw [biUnion_insert, sum_insert hk]
    exact (sum_union_bound (K k) (S.biUnion K) f hf).trans (by gcongr)

private theorem bound_at_frequency (A : Finset ℕ) (θ : ℝ) :
    ‖∑ a ∈ A, Complex.exp (2 * Real.pi * Complex.I * ((θ * a : ℝ) : ℂ))‖ ^ 2 ≤ (A.card : ℝ)^2 := by
  have hunit (a : ℕ) : ‖Complex.exp (2 * Real.pi * Complex.I * ((θ * a : ℝ) : ℂ))‖ = 1 := by
    have h : 2 * (Real.pi : ℂ) * Complex.I * ((θ * a : ℝ) : ℂ) =
        ((2 * Real.pi * (θ * a) : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [h, Complex.norm_exp_ofReal_mul_I]
  apply pow_le_pow_left₀ (norm_nonneg _) _ 2
  calc
    _ ≤ ∑ a ∈ A, ‖Complex.exp (2 * Real.pi * Complex.I * ((θ * a : ℝ) : ℂ))‖ := norm_sum_le _ _
    _ = ∑ _a ∈ A, (1 : ℝ) := sum_congr rfl fun a _ => hunit a
    _ = _ := by simp

private theorem normalization (p r a : ℕ) :
    (Complex.exp (2 * Real.pi * Complex.I / (p*p : ℕ)))^(a*r) =
      Complex.exp (2 * Real.pi * Complex.I * (((r : ℝ) / (p*p : ℕ) * a : ℝ) : ℂ)) := by
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  simp only [div_eq_mul_inv]
  ring

private theorem primitive_fraction_injective {p q r s : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hr : ¬ p ∣ r) (heq : (r : ℝ) / (p*p : ℕ) = (s : ℝ) / (q*q : ℕ)) : p = q ∧ r = s := by
  have hpr : (0 : ℝ) < (p*p : ℕ) := by exact_mod_cast Nat.mul_pos hp.pos hp.pos
  have hqr : (0 : ℝ) < (q*q : ℕ) := by exact_mod_cast Nat.mul_pos hq.pos hq.pos
  have hcross := (div_eq_div_iff hpr.ne' hqr.ne').mp heq
  have hnat : r*(q*q) = s*(p*p) := by exact_mod_cast hcross
  have hd : p ∣ r*(q*q) := by rw [hnat, ← mul_assoc]; exact dvd_mul_left p (s*p)
  have hqp : p ∣ q := (hp.dvd_mul.mp ((hp.dvd_mul.mp hd).resolve_left hr)).elim id id
  have hpq : p = q := (hq.eq_one_or_self_of_dvd p hqp).resolve_left hp.ne_one
  subst q
  exact ⟨rfl, by exact_mod_cast (div_left_inj' hpr.ne').mp heq⟩

private theorem choose_spacing {N Z : ℝ} (hN : 1 < N) (hZ : 1 ≤ Z) (hZN : Z ≤ N) :
    ∃ Y : ℝ, 1 ≤ Y ∧ Y < N ^ (8/15 : ℝ) ∧
      (1 / (Y / N^(16/15 : ℝ))) * Z = N^(64/75 : ℝ) * Z^(6/5 : ℝ) ∧
      Y^4 * Z^2 = N^(64/75 : ℝ) * Z^(6/5 : ℝ) := by
  have hNp : 0 < N := by linarith
  have hZp : 0 < Z := by linarith
  let Y := N^(16/75 : ℝ) / Z^(1/5 : ℝ)
  have hsub : Z^(1/5 : ℝ) ≤ N^(16/75 : ℝ) :=
    (Real.rpow_le_rpow hZp.le hZN (by norm_num)).trans
      (Real.rpow_le_rpow_of_exponent_le hN.le (by norm_num))
  have hY : 1 ≤ Y := (le_div_iff₀ (Real.rpow_pos_of_pos hZp _)).2 (by simpa using hsub)
  have hY2 : Y < N^(8/15 : ℝ) := by
    have hz : 1 ≤ Z^(1/5 : ℝ) := Real.one_le_rpow hZ (by norm_num)
    have hu : Y ≤ N^(16/75 : ℝ) := div_le_self (by positivity) hz
    exact hu.trans_lt (Real.rpow_lt_rpow_of_exponent_lt hN (by norm_num))
  refine ⟨Y, hY, hY2, ?_, ?_⟩
  · have hNpow : N^(16/15 : ℝ) = N^(64/75 : ℝ) * N^(16/75 : ℝ) := by
      rw [← Real.rpow_add hNp]
      norm_num
    have hZpow : Z^(6/5 : ℝ) = Z^(1/5 : ℝ) * Z := calc
      Z^(6/5 : ℝ) = Z^((1/5 : ℝ) + 1) := by norm_num
      _ = _ := by rw [Real.rpow_add hZp, Real.rpow_one]
    dsimp [Y]
    rw [hNpow, hZpow]
    have hn : 0 < N^(16/75 : ℝ) := Real.rpow_pos_of_pos hNp _
    have hz : 0 < Z^(1/5 : ℝ) := Real.rpow_pos_of_pos hZp _
    have hn' : 0 < N^(64/75 : ℝ) := Real.rpow_pos_of_pos hNp _
    field_simp
  · have hZpow : Z^2 = Z^(6/5 : ℝ) * Z^(4/5 : ℝ) := by
      rw [← Real.rpow_add hZp, ← Real.rpow_natCast]
      norm_num
    have hn : (N^(16/75 : ℝ))^4 = N^(64/75 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hNp.le]
      norm_num
    have hz : (Z^(1/5 : ℝ))^4 = Z^(4/5 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hZp.le]
      norm_num
    dsimp [Y]
    rw [div_pow, hn, hz, hZpow]
    have : 0 < Z^(4/5 : ℝ) := Real.rpow_pos_of_pos hZp _
    field_simp

private theorem packing_from_close_count {ι : Type} [DecidableEq ι] (J : Finset ι)
    (α : ι → ℝ) {e δ : ℝ} (hInjective : Set.InjOn α ↑J)
    (hrange : ∀ j ∈ J, e ≤ α j ∧ α j ≤ 1-e) (hδ : δ ≤ 2*e) :
    ∃ B : Finset ι, ∃ K : Fin 3 → Finset ι,
      J ⊆ B ∪ univ.biUnion K ∧
      B.card ≤ ((J ×ˢ (J ×ˢ (J ×ˢ J))).filter fun q =>
      α q.1 < α q.2.1 ∧ α q.2.1 < α q.2.2.1 ∧ α q.2.2.1 < α q.2.2.2 ∧
      α q.2.2.2 - α q.1 ≤ δ).card ∧ (∀ k, K k ⊆ J) ∧
      ∀ k, ∀ a ∈ K k, ∀ b ∈ K k, a ≠ b → δ ≤ |α a - α b| ∧ δ ≤ 1 - |α a - α b| := by
  classical
  let earlier {n : ℕ} (i : Fin n) (k : ℕ) : Fin n :=
    ⟨i.val-k, (Nat.sub_le _ _).trans_lt i.isLt⟩

  let exceptional {n : ℕ} (a : Fin n → ℝ) (δ : ℝ) : Finset (Fin n) := by
    classical
    exact univ.filter (fun i => 3 ≤ i.val ∧ a i - a (earlier i 3) ≤ δ)

  let retained {n : ℕ} (a : Fin n → ℝ) (δ : ℝ) (k : Fin 3) : Finset (Fin n) := by
    classical
    exact univ.filter (fun i => i.val % 3 = k.val ∧ i ∉ exceptional a δ)

  have packing_cover {n : ℕ} (a : Fin n → ℝ) (δ : ℝ) :
      (univ : Finset (Fin n)) ⊆ exceptional a δ ∪ univ.biUnion (retained a δ) := by
    classical
    intro i _
    by_cases hi : i ∈ exceptional a δ
    · exact mem_union_left _ hi
    · let k : Fin 3 := ⟨i.val % 3, Nat.mod_lt _ (by decide)⟩
      exact mem_union_right _ (mem_biUnion.mpr ⟨k,mem_univ _,
        mem_filter.mpr ⟨mem_univ _,rfl,hi⟩⟩)

  have straight_spacing {n : ℕ} {a : Fin n → ℝ} {δ : ℝ} (ha : StrictMono a)
      {i j : Fin n} (hij : i < j) (hmod : i.val % 3 = j.val % 3)
      (hj : j ∉ exceptional a δ) : δ ≤ a j - a i := by
    have hlt : i.val < j.val := hij
    have hgap : i.val + 3 ≤ j.val := by omega
    have hindex : i ≤ earlier j 3 := by
      change i.val ≤ j.val - 3
      omega
    have hnot : ¬ a j - a (earlier j 3) ≤ δ := by
      intro h
      exact hj (mem_filter.mpr ⟨mem_univ _,by omega,h⟩)
    have hleft := ha.monotone hindex
    linarith [lt_of_not_ge hnot]

  have retained_separated {n : ℕ} {a : Fin n → ℝ} {δ e : ℝ} (ha : StrictMono a)
      (hrange : ∀ i, e ≤ a i ∧ a i ≤ 1-e) (hδ : δ ≤ 2*e) :
      ∀ k, ∀ i ∈ retained a δ k, ∀ j ∈ retained a δ k, i ≠ j →
        δ ≤ |a i - a j| ∧ δ ≤ 1 - |a i - a j| := by
    intro k i hi j hj hne
    obtain ⟨hmodi,hbi⟩ := (mem_filter.mp hi).2
    obtain ⟨hmodj,hbj⟩ := (mem_filter.mp hj).2
    constructor
    · obtain hij | hji := lt_or_gt_of_ne hne
      · rw [abs_of_nonpos (sub_nonpos.mpr (ha.monotone hij.le)),neg_sub]
        exact straight_spacing ha hij (hmodi.trans hmodj.symm) hbj
      · rw [abs_of_nonneg (sub_nonneg.mpr (ha.monotone hji.le))]
        exact straight_spacing ha hji (hmodj.trans hmodi.symm) hbi
    · have habs : |a i - a j| ≤ 1-2*e := by
        apply abs_le.mpr
        obtain ⟨hiL,hiU⟩ := hrange i
        obtain ⟨hjL,hjU⟩ := hrange j
        exact ⟨by linarith,by linarith⟩
      linarith

  let closeQuadruples {n : ℕ} (a : Fin n → ℝ) (δ : ℝ) :
      Finset (Fin n × Fin n × Fin n × Fin n) := by
    classical
    exact univ.filter fun q => q.1 < q.2.1 ∧ q.2.1 < q.2.2.1 ∧ q.2.2.1 < q.2.2.2 ∧
      a q.2.2.2 - a q.1 ≤ δ

  have exceptional_card_le {n : ℕ} (a : Fin n → ℝ) (δ : ℝ) :
      (exceptional a δ).card ≤ (closeQuadruples a δ).card := by
    classical
    refine card_le_card_of_injOn (fun i => (earlier i 3,earlier i 2,earlier i 1,i)) ?_ ?_
    · intro i hi
      obtain ⟨hi3,hd⟩ := (mem_filter.mp (mem_coe.mp hi)).2
      apply mem_coe.mpr
      refine mem_filter.mpr ⟨mem_univ _,?_,?_,?_,hd⟩
      all_goals
        change (_ : ℕ) < _
        simp only [earlier]
        omega
    · intro i _ j _ he
      exact congrArg (fun q : Fin n × Fin n × Fin n × Fin n => q.2.2.2) he
  let F := J.image α
  let a := F.orderEmbOfFin rfl
  have hrepr (i : Fin F.card) : ∃ j ∈ J, α j = a i :=
    mem_image.mp (F.orderEmbOfFin_mem rfl i)
  choose f hf hα using hrepr
  have hfInj : Function.Injective f := by
    intro i j h
    exact a.injective (by rw [← hα i, ← hα j, h])
  let emb : Fin F.card ↪ ι := ⟨f,hfInj⟩
  let B := (exceptional a δ).map emb
  let K (k : Fin 3) := (retained a δ k).map emb
  refine ⟨B,K,?_,?_,?_,?_⟩
  · intro j hj
    have hjF : α j ∈ F := mem_image_of_mem α hj
    have hjA : α j ∈ Set.range a := by
      rw [show Set.range a = (F : Set ℝ) from F.range_orderEmbOfFin rfl]
      exact hjF
    obtain ⟨i,hi⟩ := hjA
    have hij : f i = j := hInjective (hf i) hj ((hα i).trans hi)
    rcases mem_union.mp (packing_cover a δ (mem_univ i)) with hB | hK
    · exact mem_union_left _ (mem_map.mpr ⟨i,hB,hij⟩)
    · obtain ⟨k,hk,hik⟩ := mem_biUnion.mp hK
      exact mem_union_right _ (mem_biUnion.mpr ⟨k,hk,mem_map.mpr ⟨i,hik,hij⟩⟩)
  · change ((exceptional a δ).map emb).card ≤ _
    rw [card_map]
    refine (exceptional_card_le a δ).trans ?_
    let emb₄ := emb.prodMap (emb.prodMap (emb.prodMap emb))
    refine card_le_card_of_injOn emb₄ ?_ emb₄.injective.injOn
    intro q hq
    obtain ⟨_,h01,h12,h23,hgap⟩ := mem_filter.mp (mem_coe.mp hq)
    apply mem_coe.mpr
    refine mem_filter.mpr ⟨mem_product.mpr ⟨hf _,mem_product.mpr
      ⟨hf _,mem_product.mpr ⟨hf _,hf _⟩⟩⟩,?_,?_,?_,?_⟩
    · change α (f q.1) < α (f q.2.1)
      rw [hα,hα]
      exact a.strictMono h01
    · change α (f q.2.1) < α (f q.2.2.1)
      rw [hα,hα]
      exact a.strictMono h12
    · change α (f q.2.2.1) < α (f q.2.2.2)
      rw [hα,hα]
      exact a.strictMono h23
    · change α (f q.2.2.2) - α (f q.1) ≤ δ
      rwa [hα,hα]
  · intro k j hj
    obtain ⟨i,_,rfl⟩ := mem_map.mp hj
    exact hf i
  · intro k i hi j hj hne
    obtain ⟨i',hi',rfl⟩ := mem_map.mp hi
    obtain ⟨j',hj',rfl⟩ := mem_map.mp hj
    change δ ≤ |α (f i')-α (f j')| ∧ δ ≤ 1-|α (f i')-α (f j')|
    rw [hα,hα]
    have hrange' (t : Fin F.card) : e ≤ a t ∧ a t ≤ 1-e := by
      rw [← hα t]
      exact hrange _ (hf t)
    exact retained_separated a.strictMono hrange' hδ k i' hi' j' hj'
      (fun he => hne (congrArg f he))

/-- Konyagin's arithmetic count of ordered close quadruples of primitive fractions. -/
def H1 : Prop := ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
  ∀ Y : ℝ, 1 ≤ Y → Y < (N : ℝ) ^ (8/15 : ℝ) →
    let X := ⌊(N : ℝ) ^ (4/15 : ℝ)⌋₊
    let P := (range (X+1)).filter Nat.Prime
    let J := P.sigma (fun p => (range (p*p)).filter (fun r => N < p^4 ∧ ¬p ∣ r))
    let α : Sigma (fun _ : ℕ => ℕ) → ℝ := fun j => (j.2 : ℝ) / (j.1 * j.1 : ℕ)
    let δ := Y / (N : ℝ) ^ (16/15 : ℝ)
    let Q := (J ×ˢ (J ×ˢ (J ×ˢ J))).filter fun q =>
      α q.1 < α q.2.1 ∧ α q.2.1 < α q.2.2.1 ∧ α q.2.2.1 < α q.2.2.2 ∧
      α q.2.2.2 - α q.1 ≤ δ
    (Q.card : ℝ) ≤ (N : ℝ)^ε * Y^4

/-- Ordinary large sieve for an arbitrary separated family on the circle. -/
def H2 : Prop := ∀ {ι : Type} [DecidableEq ι] (J : Finset ι) (N : ℕ) (A : Finset ℕ)
    (α : ι → ℝ) (δ : ℝ), 0 < N → A ⊆ Icc 1 N → 0 < δ →
    (∀ a ∈ J, 0 < α a ∧ α a < 1) →
    (∀ a ∈ J, ∀ b ∈ J, a ≠ b → δ ≤ |α a - α b| ∧ δ ≤ 1 - |α a - α b|) →
    (∑ j ∈ J, ‖∑ a ∈ A, Complex.exp (2 * Real.pi * Complex.I * ((α j * a : ℝ) : ℂ))‖^2)
      ≤ 16 * ((N : ℝ) + 1/δ) * A.card

/-- The exceptional and separated bounds balance at the fifth-root spacing. -/
theorem main : H1 → H2 → OMA.R_Erdos1109_erdos_1109_variants_konyagin_upper_R1_H1_R1_H2_R1.H1 := by
  intro hpack hsieve ε hε
  have hε2 : 0 < ε/2 := half_pos hε
  have hlarge : ∀ᶠ N : ℕ in atTop, (49 : ℝ) ≤ (N : ℝ)^(ε/2) :=
    ((tendsto_rpow_atTop hε2).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  filter_upwards [hpack (ε/2) hε2, hlarge, eventually_ge_atTop 2] with N hpack hlarge hN
  intro A hA
  let Z : ℝ := A.card
  let X := ⌊(N : ℝ)^(4/15 : ℝ)⌋₊
  let P := (range (X+1)).filter Nat.Prime
  let S (p : ℕ) := (range (p*p)).filter (fun r => N < p^4 ∧ ¬p ∣ r)
  let J := P.sigma S
  let α : Sigma (fun _ : ℕ => ℕ) → ℝ := fun j => (j.2 : ℝ) / (j.1*j.1 : ℕ)
  let F (j : Sigma (fun _ : ℕ => ℕ)) : ℝ :=
    ‖∑ a ∈ A, Complex.exp (2 * Real.pi * Complex.I * ((α j * a : ℝ) : ℂ))‖^2
  let R := (N : ℝ)^(ε/2)
  change (N : ℝ)^(7/15 : ℝ) < Z →
    (∑ p ∈ P, ∑ r ∈ S p, ‖∑ a ∈ A,
      (Complex.exp (2*Real.pi*Complex.I/(p*p : ℕ)))^(a*r)‖^2) ≤ _
  intro hdense
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hZ : 1 ≤ Z := (Real.one_le_rpow hNr.le (by norm_num)).trans hdense.le
  have hZN : Z ≤ N := by simpa [Z] using
    (show (A.card : ℝ) ≤ ((Icc 1 N).card : ℝ) by exact_mod_cast card_le_card hA)
  obtain ⟨Y, hY, hYN, hbalancedS, hbalancedB⟩ := choose_spacing hNr hZ hZN
  let δ := Y / (N : ℝ)^(16/15 : ℝ)
  have hδ : 0 < δ := div_pos (by linarith) (Real.rpow_pos_of_pos (by linarith) _)
  let e : ℝ := 1 / (N : ℝ)^(8/15 : ℝ)
  have hep : 0 < e := one_div_pos.mpr (Real.rpow_pos_of_pos (by linarith) _)
  have hpowers : (N : ℝ)^(16/15 : ℝ) = (N : ℝ)^(8/15 : ℝ) * (N : ℝ)^(8/15 : ℝ) := by
    rw [← Real.rpow_add (by linarith : (0 : ℝ) < N)]
    norm_num
  have hδe : δ ≤ 2*e := by
    have hd : δ ≤ e := calc
      δ ≤ (N : ℝ)^(8/15 : ℝ)/(N : ℝ)^(16/15 : ℝ) := div_le_div_of_nonneg_right hYN.le (by positivity)
      _ = e := by
        dsimp [e]
        rw [hpowers]
        have hn : 0 < (N : ℝ)^(8/15 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
        field_simp
    linarith
  have hinj : Set.InjOn α (↑J : Set (Sigma (fun _ : ℕ => ℕ))) := by
    rintro ⟨p,r⟩ hj ⟨q,s⟩ hk heq
    have hp := (mem_filter.mp (mem_sigma.mp hj).1).2
    have hq := (mem_filter.mp (mem_sigma.mp hk).1).2
    have hr := (mem_filter.mp (mem_sigma.mp hj).2).2.2
    obtain ⟨heq1, heq2⟩ := primitive_fraction_injective hp hq hr heq
    change p = q at heq1
    change r = s at heq2
    subst q
    subst s
    rfl
  have hseam (j) (hj : j ∈ J) : e ≤ α j ∧ α j ≤ 1-e := by
    rcases mem_sigma.mp hj with ⟨hp, hr⟩
    have hpp := (mem_filter.mp hp).2
    have hpX : j.1 ≤ X := Nat.lt_succ_iff.mp (mem_range.mp (mem_filter.mp hp).1)
    have hrlt := mem_range.mp (mem_filter.mp hr).1
    have hrpos : 0 < j.2 := by
      by_contra! hz
      have : j.2 = 0 := by omega
      exact (mem_filter.mp hr).2.2 (this ▸ dvd_zero _)
    have hprod : (0 : ℝ) < (j.1*j.1 : ℕ) := by exact_mod_cast Nat.mul_pos hpp.pos hpp.pos
    have hpr : (j.1 : ℝ) ≤ (N : ℝ)^(4/15 : ℝ) :=
      (show (j.1 : ℝ) ≤ (X : ℝ) by exact_mod_cast hpX).trans (Nat.floor_le (by positivity))
    have hsq : ((j.1*j.1 : ℕ) : ℝ) ≤ (N : ℝ)^(8/15 : ℝ) := by
      have hm := mul_le_mul hpr hpr (by positivity) (by positivity)
      rw [← Real.rpow_add (by linarith : (0 : ℝ) < N)] at hm
      norm_num at hm ⊢
      exact hm
    have hd : e ≤ 1 / ((j.1*j.1 : ℕ) : ℝ) := one_div_le_one_div_of_le hprod hsq
    constructor
    · apply hd.trans
      exact div_le_div_of_nonneg_right (by exact_mod_cast hrpos) hprod.le
    · have hprodGap : α j + 1 / ((j.1*j.1 : ℕ) : ℝ) ≤ 1 := by
        change (j.2 : ℝ) / _ + 1 / _ ≤ 1
        rw [← add_div, div_le_one hprod]
        exact_mod_cast (show j.2+1 ≤ j.1*j.1 by omega)
      linarith
  have hrange (j) (hj : j ∈ J) : 0 < α j ∧ α j < 1 := by
    obtain ⟨h₁, h₂⟩ := hseam j hj
    constructor <;> linarith
  have hQ := hpack Y hY hYN
  obtain ⟨B, K, hcover', hBcard, hK, hsep⟩ := packing_from_close_count J α hinj hseam hδe
  have hB : (B.card : ℝ) ≤ R * Y^4 := le_trans (Nat.cast_le.mpr hBcard) hQ
  have hF (j) : 0 ≤ F j := sq_nonneg _
  have hBterm : ∑ j ∈ B, F j ≤ R * (Y^4 * Z^2) := calc
    _ ≤ ∑ _j ∈ B, Z^2 := sum_le_sum fun j _ => bound_at_frequency A (α j)
    _ = (B.card : ℝ) * Z^2 := by simp [sum_const, nsmul_eq_mul]
    _ ≤ R * (Y^4 * Z^2) := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right hB (sq_nonneg _)
  have hKterm (k : Fin 3) : ∑ j ∈ K k, F j ≤ 16 * ((N : ℝ) + 1/δ) * Z :=
    hsieve (K k) N A α δ (by omega) hA hδ (fun j hj => hrange j (hK k hj)) (hsep k)
  have hKsum : ∑ j ∈ univ.biUnion K, F j ≤ 48 * ((N : ℝ) + 1/δ) * Z := calc
    _ ≤ ∑ k : Fin 3, ∑ j ∈ K k, F j := sum_biUnion_bound _ _ _ hF
    _ ≤ ∑ _k : Fin 3, 16 * ((N : ℝ) + 1/δ) * Z := sum_le_sum fun k _ => hKterm k
    _ = _ := by simp [sum_const, nsmul_eq_mul]; ring
  have hbound : ∑ j ∈ J, F j ≤ R * (Y^4 * Z^2) + 48 * (((N : ℝ) + 1/δ) * Z) := by
    refine (sum_le_sum_of_subset_of_nonneg hcover' fun j _ _ => hF j).trans ?_
    have h := (sum_union_bound B (univ.biUnion K) F hF).trans (add_le_add hBterm hKsum)
    simpa [mul_assoc] using h
  rw [add_mul, hbalancedS, hbalancedB] at hbound
  have hlhs : (∑ p ∈ P, ∑ r ∈ S p, ‖∑ a ∈ A,
      (Complex.exp (2 * Real.pi * Complex.I / (p*p : ℕ)))^(a*r)‖^2) = ∑ j ∈ J, F j := by
    rw [sum_sigma']
    exact sum_congr rfl fun j _ => by simp only [F, α, normalization]
  rw [hlhs]
  let T := (N : ℝ) * Z + (N : ℝ)^(64/75 : ℝ) * Z^(6/5 : ℝ)
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hcost : (N : ℝ)^(64/75 : ℝ) * Z^(6/5 : ℝ) ≤ T := le_add_of_nonneg_left (show 0 ≤ (N : ℝ) * Z by positivity)
  have hR : (49 : ℝ) ≤ R := hlarge
  have hcoeff : R + 48 ≤ R*R := by nlinarith
  have hpow : (N : ℝ)^ε = R*R := by
    dsimp [R]
    rw [← Real.rpow_add (by linarith : (0 : ℝ) < N)]
    ring_nf
  change _ ≤ (N : ℝ)^ε * T
  rw [hpow]
  refine hbound.trans ?_
  calc
    _ ≤ R * T + 48 * T := add_le_add (mul_le_mul_of_nonneg_left hcost (by linarith)) le_rfl
    _ = (R + 48) * T := by ring
    _ ≤ (R * R) * T := mul_le_mul_of_nonneg_right hcoeff hT

end OMA.R_Erdos1109_erdos_1109_variants_konyagin_upper_R1_H1_R1_H2_R1_H1_R1
