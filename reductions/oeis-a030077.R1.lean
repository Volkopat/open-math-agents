import OMAStatements.S_oeis_a030077
import Mathlib

namespace OMA.R_oeis_a030077_R1

/-- Every prescribed multiset using at most two jump lengths is realized by a Hamiltonian path. -/
def H1 : Prop :=
  ∀ (n : ℕ), n.Prime → 3 ≤ n → ∀ s : Sym (Fin (n / 2)) (n - 1),
    s.val.toFinset.card ≤ 2 → ∃ p : Equiv.Perm (Fin n),
      (↑(List.ofFn fun k : Fin (n - 1) =>
        let d := Nat.dist (p ⟨k.val, by omega⟩).val (p ⟨k.val + 1, by omega⟩).val
        min d (n - d)) : Multiset ℕ) = s.val.map (fun i => i.val + 1)

/-- Every prescribed multiset using at least three jump lengths is realized by a Hamiltonian path. -/
def H2 : Prop :=
  ∀ (n : ℕ), n.Prime → 3 ≤ n → ∀ s : Sym (Fin (n / 2)) (n - 1),
    3 ≤ s.val.toFinset.card → ∃ p : Equiv.Perm (Fin n),
      (↑(List.ofFn fun k : Fin (n - 1) =>
        let d := Nat.dist (p ⟨k.val, by omega⟩).val (p ⟨k.val + 1, by omega⟩).val
        min d (n - d)) : Multiset ℕ) = s.val.map (fun i => i.val + 1)

open OMA.S_oeis_a030077

private lemma oma_norm_pt_ordered {n : ℕ} (hn : 0 < n) (i j : Fin n) (hij : i.val ≤ j.val) :
    ‖pt n i - pt n j‖ = 2 * Real.sin (Real.pi * ((j.val - i.val : ℕ) : ℝ) / n) := by
  let θ (k : ℕ) : ℝ := 2 * Real.pi * k / n
  have hpt (k : Fin n) : pt n k = Complex.exp (Complex.I * (θ k.val : ℂ)) := by
    unfold pt θ
    push_cast
    ring_nf
  have hdif : θ j.val = θ i.val + θ (j.val - i.val) := by
    dsimp [θ]
    rw [Nat.cast_sub hij]
    ring
  have fac : pt n j - pt n i = Complex.exp (Complex.I * (θ i.val : ℂ)) *
      (Complex.exp (Complex.I * (θ (j.val - i.val) : ℂ)) - 1) := by
    rw [hpt j, hpt i, hdif, Complex.ofReal_add, mul_add, Complex.exp_add]
    ring
  have pos : (0 : ℝ) < n := by exact_mod_cast hn
  have dh : ((j.val - i.val : ℕ) : ℝ) ≤ n := by exact_mod_cast (show j.val - i.val ≤ n by omega)
  have half : θ (j.val-i.val) / 2 = Real.pi * ((j.val-i.val : ℕ) : ℝ) / n := by dsimp [θ]; ring
  have hs : 0 ≤ Real.sin (Real.pi * ((j.val-i.val : ℕ) : ℝ) / n) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi (by positivity)
    apply (div_le_iff₀ pos).mpr
    exact mul_le_mul_of_nonneg_left dh Real.pi_pos.le
  rw [norm_sub_rev, fac, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul,
    Complex.norm_exp_I_mul_ofReal_sub_one, half, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

private lemma oma_norm_pt {n : ℕ} (hn : 0 < n) (i j : Fin n) :
    ‖pt n i - pt n j‖ = 2 * Real.sin (Real.pi * ((min (Nat.dist i.val j.val) (n-Nat.dist i.val j.val) : ℕ) : ℝ) / n) := by
  have hd : ‖pt n i - pt n j‖ =
      2 * Real.sin (Real.pi * ((Nat.dist i.val j.val : ℕ) : ℝ) / n) := by
    rcases le_total i.val j.val with h | h
    · simpa [Nat.dist_eq_sub_of_le h] using oma_norm_pt_ordered hn i j h
    · rw [norm_sub_rev]
      simpa [Nat.dist_eq_sub_of_le_right h] using oma_norm_pt_ordered hn j i h
  rw [hd]
  set d := Nat.dist i.val j.val
  have hdn : d ≤ n := by
    dsimp [d, Nat.dist]
    omega
  rcases le_total d (n-d) with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h, Nat.cast_sub hdn]
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have he : Real.pi * ((n : ℝ) - d) / n = Real.pi - Real.pi * d / n := by field_simp
    rw [he, Real.sin_pi_sub]

private lemma oma_polygon_profiles {n : ℕ} (hn : 0 < n) :
    ∃ (profile : Equiv.Perm (Fin n) → Sym (Fin (n/2)) (n-1))
      (weight : Sym (Fin (n/2)) (n-1) → ℝ),
      (∀ p, pathLength p = weight (profile p)) ∧
      (∀ p, (profile p).val.map (fun j => j.val+1) =
        (List.ofFn (fun k : Fin (n-1) =>
          let d := Nat.dist (p ⟨k.val, by omega⟩).val (p ⟨k.val+1, by omega⟩).val
          min d (n-d)) : Multiset ℕ)) ∧
      (∀ s, weight s = (s.val.map (fun j =>
        2 * Real.sin (Real.pi * ((j.val+1 : ℕ) : ℝ) / n))).sum) := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  let edge (p : Equiv.Perm (Fin (m+1))) (k : Fin m) :=
    min (Nat.dist (p k.castSucc).val (p k.succ).val)
      (m+1-Nat.dist (p k.castSucc).val (p k.succ).val)
  have bounds (p : Equiv.Perm (Fin (m+1))) (k : Fin m) :
      1 ≤ edge p k ∧ edge p k ≤ (m+1)/2 := by
    have hne : (p k.castSucc).val ≠ (p k.succ).val := by
      intro e
      have := congrArg Fin.val (p.injective (Fin.ext e))
      simp at this
    have h₁ := (p k.castSucc).isLt
    have h₂ := (p k.succ).isLt
    dsimp [edge, Nat.dist]
    omega
  let index (p : Equiv.Perm (Fin (m+1))) (k : Fin m) : Fin ((m+1)/2) :=
    ⟨edge p k - 1, by have := bounds p k; omega⟩
  have hindex (p : Equiv.Perm (Fin (m+1))) (k : Fin m) : (index p k).val+1 = edge p k := by
    dsimp [index]
    have := bounds p k
    omega
  let profile (p : Equiv.Perm (Fin (m+1))) : Sym (Fin ((m+1)/2)) (m+1-1) :=
    ⟨(List.ofFn (index p) : Multiset _), by simp⟩
  let weight (s : Sym (Fin ((m+1)/2)) (m+1-1)) : ℝ :=
    (s.val.map (fun j => 2 * Real.sin (Real.pi * ((j.val+1 : ℕ) : ℝ) / (m+1 : ℕ)))).sum
  refine ⟨profile, weight, ?_, ?_, fun _ => rfl⟩
  · intro p
    unfold pathLength
    simp only [profile, weight, Multiset.map_coe, Multiset.sum_coe, List.map_ofFn, List.sum_ofFn]
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_last, Nat.lt_irrefl, ↓reduceDIte, add_zero]
    apply Finset.sum_congr rfl
    intro k _
    have hk : k.castSucc.val + 1 < m+1 := by simp
    rw [dif_pos hk]
    simp only [Function.comp_apply, hindex]
    exact oma_norm_pt hn (p k.castSucc) (p k.succ)
  · intro p
    simp only [profile, Multiset.map_coe, List.map_ofFn, Function.comp_def, hindex]
    rfl

/-- Count the possible multisets of jumps independently of any realizability hypothesis. -/
private theorem polygon_profile_card {n : ℕ} (hn : 3 ≤ n) :
    Nat.card (Sym (Fin (n / 2)) (n - 1)) = (n - 2 + n / 2).choose (n / 2 - 1) := by
  classical
  rw [Nat.card_eq_fintype_card, Sym.card_sym_eq_choose, Fintype.card_fin]
  rw [show n / 2 + (n - 1) - 1 = n - 2 + n / 2 by omega]
  exact Nat.choose_symm_of_eq_add (by omega)

/-- All lengths factor through a multiset of jumps, giving the upper bound at every polygon size. -/
private theorem polygon_count_le {n : ℕ} (hn : 3 ≤ n)
    (profile : Equiv.Perm (Fin n) → Sym (Fin (n / 2)) (n - 1))
    (weight : Sym (Fin (n / 2)) (n - 1) → ℝ)
    (hpath : ∀ p, pathLength p = weight (profile p)) :
    a n ≤ (n - 2 + n / 2).choose (n / 2 - 1) := by
  have hsub : Set.range (pathLength (n := n)) ⊆ Set.range weight := by
    rintro _ ⟨p, rfl⟩
    exact ⟨profile p, (hpath p).symm⟩
  calc
    a n ≤ (Set.range weight).ncard := Set.ncard_le_ncard hsub (Set.finite_range weight)
    _ ≤ Nat.card (Sym (Fin (n / 2)) (n - 1)) := by
      rw [← Set.image_univ, ← Set.ncard_univ]
      exact Set.ncard_image_le
    _ = _ := polygon_profile_card hn

/-- Realizing every profile, and separating their weights, attains the upper bound. -/
private theorem polygon_count_eq {n : ℕ} (hn : 3 ≤ n)
    (profile : Equiv.Perm (Fin n) → Sym (Fin (n / 2)) (n - 1))
    (weight : Sym (Fin (n / 2)) (n - 1) → ℝ)
    (hpath : ∀ p, pathLength p = weight (profile p))
    (hreal : Function.Surjective profile) (hinj : Function.Injective weight) :
    a n = (n - 2 + n / 2).choose (n / 2 - 1) := by
  have hrange : Set.range (pathLength (n := n)) = Set.range weight := by
    ext x
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨profile p, (hpath p).symm⟩
    · rintro ⟨v, rfl⟩
      obtain ⟨p, rfl⟩ := hreal v
      exact ⟨p, hpath p⟩
  rw [a, hrange, Set.ncard_range_of_injective hinj, polygon_profile_card hn]

/-- The count is maximal precisely when every profile is realized and different profiles
have different weights. Thus both hypotheses in the reduction are necessary. -/
private theorem polygon_count_iff {n : ℕ} (hn : 3 ≤ n)
    (profile : Equiv.Perm (Fin n) → Sym (Fin (n / 2)) (n - 1))
    (weight : Sym (Fin (n / 2)) (n - 1) → ℝ)
    (hpath : ∀ p, pathLength p = weight (profile p)) :
    a n = (n - 2 + n / 2).choose (n / 2 - 1) ↔
      Function.Surjective profile ∧ Function.Injective weight := by
  refine ⟨?_, fun ⟨hs, hi⟩ => polygon_count_eq hn profile weight hpath hs hi⟩
  intro h
  have hrange : Set.range (pathLength (n := n)) = weight '' Set.range profile := by
    rw [show pathLength (n := n) = weight ∘ profile from funext hpath, Set.range_comp]
  rw [a, hrange, ← polygon_profile_card hn, ← Set.ncard_univ] at h
  have hfull : Set.range profile = Set.univ :=
    Set.eq_of_subset_of_ncard_le (Set.subset_univ _) (h ▸ Set.ncard_image_le)
  refine ⟨Set.range_eq_univ.mp hfull, Set.injOn_univ.mp ?_⟩
  rw [hfull] at h
  exact Set.injOn_of_ncard_image_eq h

private lemma polygon_weight_injective {α : Type*} [Fintype α] {k : ℕ} (w : α → ℝ)
    (hw : ∀ c : α → ℚ, (∑ a, (c a : ℝ) * w a) = 0 → ∀ a, c a = 0) :
    Function.Injective (fun s : Sym α k => ((s : Multiset α).map w).sum) := by
  classical
  have expand (m : Multiset α) : (m.map w).sum = ∑ a, (m.count a : ℝ) * w a := by
    rw [Finset.sum_multiset_map_count]
    simp only [nsmul_eq_mul]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro a _ ha
    simp_all
  intro s t he
  let c (a : α) : ℚ := ((s : Multiset α).count a : ℚ) - (t : Multiset α).count a
  have hrel : ∑ a, (c a : ℝ) * w a = 0 := by
    simpa only [c, Rat.cast_sub, Rat.cast_natCast, sub_mul, Finset.sum_sub_distrib,
      ← expand, sub_eq_zero] using he
  apply Sym.coe_injective
  apply Multiset.ext.mpr
  intro a
  exact_mod_cast sub_eq_zero.mp (hw c hrel a)

open scoped BigOperators

private lemma polygon_paired_independence {K ι : Type*} [Field K] [CharZero K] [Fintype ι]
    {p : ℕ} (hp : p.Prime) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (e f : ι ↪ Fin p) (disj : ∀ i j, e i ≠ f j)
    (off : Fin p) (he : ∀ i, e i ≠ off) (hf : ∀ i, f i ≠ off)
    (c : ι → ℚ) (rel : ∑ i, (c i : K) * (ζ ^ (e i).val - ζ ^ (f i).val) = 0) :
    ∀ i, c i = 0 := by
  classical
  let coeff : Fin p → ℚ := fun j =>
    (∑ i, if e i = j then c i else 0) - ∑ i, if f i = j then c i else 0
  have combine (a : ι ↪ Fin p) :
      ∑ j : Fin p, ((∑ i, if a i = j then c i else 0 : ℚ) : K) * ζ ^ j.val =
        ∑ i, (c i : K) * ζ ^ (a i).val := by
    simp_rw [Rat.cast_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp [apply_ite, ite_mul]
  have vanish : ∑ j, (coeff j : K) * ζ ^ j.val = 0 := by
    simp only [coeff, Rat.cast_sub, sub_mul, Finset.sum_sub_distrib, combine]
    simpa only [mul_sub, Finset.sum_sub_distrib] using rel
  have same := (hζ.sum_eq_zero_iff_forall_eq hp coeff).mp vanish
  intro i
  have hoff : coeff off = 0 := by simp [coeff, he, hf]
  have hpos : coeff (e i) = c i := by
    simp [coeff, EmbeddingLike.apply_eq_iff_eq, fun j => (disj i j).symm]
  exact hpos.symm.trans ((same (e i) off).trans hoff)

private lemma polygon_chord_independent {K : Type*} [Field K] [CharZero K]
    {p : ℕ} (hp : p.Prime) (hodd : Odd p) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (c : Fin (p/2) → ℚ)
    (rel : ∑ j, (c j : K) * (ζ ^ (j.val+1) - ζ ^ (p-(j.val+1))) = 0) :
    ∀ j, c j = 0 := by
  obtain ⟨k, hk⟩ := hodd
  let e : Fin (p/2) ↪ Fin p :=
    ⟨fun j => ⟨j.val+1, by have := j.isLt; omega⟩, fun i j h => by
      apply Fin.ext
      exact Nat.add_right_cancel (congrArg Fin.val h)⟩
  let f : Fin (p/2) ↪ Fin p :=
    ⟨fun j => ⟨p-(j.val+1), by have := j.isLt; omega⟩, fun i j h => by
      have he : p-(i.val+1) = p-(j.val+1) := congrArg Fin.val h
      apply Fin.ext
      have := i.isLt
      have := j.isLt
      omega⟩
  apply polygon_paired_independence hp hζ e f _ ⟨0, hp.pos⟩ _ _ c rel
  · intro i j h
    have h' : i.val+1 = p-(j.val+1) := congrArg Fin.val h
    have := i.isLt
    have := j.isLt
    omega
  · intro i h
    have h' : i.val+1 = 0 := congrArg Fin.val h
    omega
  · intro i h
    have h' : p-(i.val+1) = 0 := congrArg Fin.val h
    have := i.isLt
    omega
open Complex

private lemma polygon_trig_independent {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    (c : Fin (p/2) → ℚ)
    (rel : ∑ j, (c j : ℝ) * (2 * Real.sin (Real.pi * (j.val+1) / p)) = 0) :
    ∀ j, c j = 0 := by
  have hodd := hp.odd_of_ne_two (by omega)
  let e := Complex.exp ((Real.pi : ℂ) * I / p)
  let ζ := -e
  have hn : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  let m := (p+1)/2
  have hm : 2*m=p+1 := by obtain ⟨k,hk⟩ := hodd; dsimp [m]; omega
  have hmc : 2*(m:ℂ)=(p:ℂ)+1 := by exact_mod_cast hm
  have cop : m.Coprime p := by
    apply Nat.Coprime.symm
    apply hp.coprime_iff_not_dvd.mpr
    intro h
    have hpos : 0 < m := by dsimp [m]; omega
    have hle := Nat.le_of_dvd hpos h
    omega
  have hz : IsPrimitiveRoot ζ p := by
    have heq : 2*(Real.pi:ℂ)*I*(m/p) = Real.pi*I+(Real.pi:ℂ)*I/p := by
      field_simp
      linear_combination hmc
    simpa only [heq, Complex.exp_add, Complex.exp_pi_mul_I, neg_one_mul, ζ, e] using
      Complex.isPrimitiveRoot_exp_of_coprime m p hp.ne_zero cop
  have edge (k : ℕ) (hk : k ≤ p) :
      ζ^k - ζ^(p-k) =
      (-1:ℂ)^k * ((2 * Real.sin (Real.pi*k/p) : ℝ) : ℂ) * I := by
    have he0 : ζ ≠ 0 := neg_ne_zero.mpr (Complex.exp_ne_zero _)
    have hneg : ζ^(p-k) = (ζ^k)⁻¹ := by rw [pow_sub₀ ζ he0 hk, hz.pow_eq_one, one_mul]
    let a : ℂ := ((Real.pi*k/p : ℝ) : ℂ)
    have he' : e^k = Complex.exp (a * I) := by
      dsimp only [e, a]
      rw [← Complex.exp_nat_mul]
      push_cast
      ring_nf
    rw [hneg]
    change (-e)^k - ((-e)^k)⁻¹ = _
    rw [show -e = (-1:ℂ)*e by simp, mul_pow, he', mul_inv_rev,
      ← inv_pow, inv_neg_one, ← Complex.exp_neg, ← neg_mul, Complex.exp_mul_I, Complex.exp_mul_I]
    simp only [Complex.cos_neg, Complex.sin_neg, Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_sin]
    dsimp only [a]
    ring
  let d (j : Fin (p/2)) : ℚ := c j / (-1 : ℚ)^(j.val+1)
  have rr : ∑ j, (d j : ℂ) * (ζ^(j.val+1) - ζ^(p-(j.val+1))) = 0 := by
    have r := congrArg (fun y : ℝ => (y : ℂ)) rel
    push_cast at r
    calc
      _ = (∑ j, (c j : ℂ) * (2 * Complex.sin ((Real.pi:ℂ)*(j.val+1)/p))) * I := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        rw [edge _ (by have := j.isLt; omega)]
        dsimp only [d]
        push_cast
        field_simp
      _ = 0 := by rw [r,zero_mul]
  have hd := polygon_chord_independent hp hodd hz d rr
  intro j
  exact (div_eq_zero_iff.mp (hd j)).resolve_right (by positivity)

/-- The source's upper bound is unconditional and applies to composite polygon sizes as well. -/
theorem polygon_upper_bound {n : ℕ} (hn : 3 ≤ n) :
    a n ≤ (n - 2 + n / 2).choose (n / 2 - 1) := by
  obtain ⟨profile, weight, hpath, _, _⟩ := oma_polygon_profiles (by omega : 0 < n)
  exact polygon_count_le hn profile weight hpath

/-- At prime order, attaining the bound is equivalent to the prime-order Buratti conjecture.
The right side involves only integer distances between vertex labels. -/
theorem prime_count_iff_all_lists {n : ℕ} (hp : n.Prime) (hn : 3 ≤ n) :
    a n = (n - 2 + n / 2).choose (n / 2 - 1) ↔
      ∀ s : Sym (Fin (n/2)) (n-1), ∃ p : Equiv.Perm (Fin n),
        (↑(List.ofFn fun k : Fin (n-1) =>
          let d := Nat.dist (p ⟨k.val, by omega⟩).val (p ⟨k.val+1, by omega⟩).val
          min d (n-d)) : Multiset ℕ) = s.val.map (fun i => i.val+1) := by
  obtain ⟨profile, weight, hpath, hmatch, hweight⟩ := oma_polygon_profiles (by omega : 0 < n)
  have hi : Function.Injective weight := by
    rw [funext hweight]
    apply polygon_weight_injective
    intro c hc
    apply polygon_trig_independent hp hn c
    simpa only [Nat.cast_add, Nat.cast_one] using hc
  rw [polygon_count_iff hn profile weight hpath]
  constructor
  · rintro ⟨hs,_⟩ s
    obtain ⟨p,hp'⟩ := hs s
    exact ⟨p, (hmatch p).symm.trans (by rw [hp'])⟩
  · intro hall
    refine ⟨?_,hi⟩
    intro s
    obtain ⟨p,hp'⟩ := hall s
    refine ⟨p,Subtype.ext ?_⟩
    exact Multiset.map_injective (f := fun i : Fin (n/2) => i.val+1)
      (fun i j hij => Fin.ext (Nat.add_right_cancel hij)) ((hmatch p).trans hp')

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a030077.main := by
  intro small large n hp hn
  apply (prime_count_iff_all_lists hp hn).2
  intro s
  rcases le_or_gt s.val.toFinset.card 2 with h | h
  · exact small n hp hn s h
  · exact large n hp hn s (by omega)

end OMA.R_oeis_a030077_R1
