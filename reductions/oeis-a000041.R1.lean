import OMAStatements.S_oeis_a000041

/-!
# Reduction of OEIS A000041

`OMA.S_oeis_a000041.main` is the conjunction of three statements on the partition numbers `a(n)`:
1. Adamson and Arndt's signed pentagonal composition formula for `a(n)` (`n ≥ 1`),
2. Zhi-Wei Sun's 2013 conjecture that no `a(n)` is a nontrivial perfect power `x^m`,
3. Zhi-Wei Sun's 2023 conjecture that every `n > 2` with `n ≠ 6` is a sum of pairwise
   non-dividing numbers of the form `a(k) + 2` (`k > 0`).

Here we:
* prove Conjecture 1 unconditionally via the power-series pentagonal number theorem, the
  partition generating function product, and a first-block decomposition of compositions;
* certify `a(0) .. a(150)` in the kernel from Euler's pentagonal recurrence, rule out all
  perfect powers for `n ≤ 150`, and reduce `H1` to prime exponents `p` and `n > 150`;
* prove Conjecture 3 unconditionally through `n = 200,000,000,000` (extending Sun's `n ≤ 7,140`
  verification by seven orders of magnitude) via direct witnesses below `60` and an 82-element
  divisibility antichain in `{a(k) + 2 | 1 ≤ k ≤ 150}` with contiguous subset-sum interval
  extension, leaving only `n > 200,000,000,000` in `H2`.
-/

namespace OMA.R_oeis_a000041_R1

open PowerSeries
open scoped PowerSeries.WithPiTopology

private theorem signedPentagonal_eq_neg_coeff {g : ℕ} (hg : 1 ≤ g) :
    OMA.S_oeis_a000041.signedPentagonal g = -(PowerSeries.pentagonalSeries ℤ).coeff g := by
  unfold OMA.S_oeis_a000041.signedPentagonal
  by_cases hmem : g ∈ Set.range pentagonal
  · obtain ⟨k, rfl⟩ := hmem
    have hk0 : k ≠ 0 := by
      rintro rfl
      simp [pentagonal] at hg
    rw [PowerSeries.coeff_pentagonalSeries_pentagonal, Int.coe_negOnePow]
    have hj_pos : 0 < k.natAbs := Int.natAbs_pos.mpr hk0
    have hj_le : k.natAbs ≤ pentagonal k := by
      rcases lt_or_gt_of_ne hk0 with hk | hk
      · have hkne : k = -(k.natAbs : ℤ) := by omega
        have h2 := two_mul_natCast_pentagonal_neg (k.natAbs : ℤ)
        rw [← hkne] at h2
        have hposZ : (1 : ℤ) ≤ k.natAbs := by exact_mod_cast hj_pos
        exact_mod_cast (by nlinarith : (k.natAbs : ℤ) ≤ (pentagonal k : ℤ))
      · have hkeq : k = (k.natAbs : ℤ) := by omega
        have h2 := two_mul_natCast_pentagonal (k.natAbs : ℤ)
        rw [← hkeq] at h2
        have hposZ : (1 : ℤ) ≤ k.natAbs := by exact_mod_cast hj_pos
        exact_mod_cast (by nlinarith : (k.natAbs : ℤ) ≤ (pentagonal k : ℤ))
    rw [Finset.sum_eq_single k.natAbs]
    · rcases lt_or_gt_of_ne hk0 with hk | hk
      · have hkne : k = -(k.natAbs : ℤ) := by omega
        have h1 : ¬ (k.natAbs ≠ 0 ∧ 2 * pentagonal k = k.natAbs * (3 * k.natAbs - 1)) := by
          rintro ⟨_, heq⟩
          have hle : 1 ≤ 3 * k.natAbs := by omega
          have heqZ : 2 * (pentagonal k : ℤ) = (k.natAbs : ℤ) * (3 * (k.natAbs : ℤ) - 1) := by
            have hcast : ((2 * pentagonal k : ℕ) : ℤ) = ((k.natAbs * (3 * k.natAbs - 1) : ℕ) : ℤ) :=
              congrArg Nat.cast heq
            simpa [Nat.cast_sub hle] using hcast
          rw [← two_mul_natCast_pentagonal (k.natAbs : ℤ)] at heqZ
          have hinj : pentagonal k = pentagonal (k.natAbs : ℤ) := by
            exact_mod_cast (by linarith : (pentagonal k : ℤ) = pentagonal (k.natAbs : ℤ))
          have := pentagonal_injective hinj
          omega
        have h2 : k.natAbs ≠ 0 ∧ 2 * pentagonal k = k.natAbs * (3 * k.natAbs + 1) := by
          refine ⟨hj_pos.ne', ?_⟩
          have h2Z := two_mul_natCast_pentagonal_neg (k.natAbs : ℤ)
          rw [← hkne] at h2Z
          exact_mod_cast h2Z
        rw [if_neg h1, if_pos h2, zero_add, pow_succ]
        ring
      · have hkeq : k = (k.natAbs : ℤ) := by omega
        have h1 : k.natAbs ≠ 0 ∧ 2 * pentagonal k = k.natAbs * (3 * k.natAbs - 1) := by
          refine ⟨hj_pos.ne', ?_⟩
          have h1Z := two_mul_natCast_pentagonal (k.natAbs : ℤ)
          have hpk : pentagonal (k.natAbs : ℤ) = pentagonal k := congrArg pentagonal hkeq.symm
          rw [hpk] at h1Z
          have hle : 1 ≤ 3 * k.natAbs := by omega
          have hcast : ((2 * pentagonal k : ℕ) : ℤ) = ((k.natAbs * (3 * k.natAbs - 1) : ℕ) : ℤ) := by
            push_cast [Nat.cast_sub hle]
            rw [Int.abs_eq_natAbs]
            exact h1Z
          exact Nat.cast_injective hcast
        have h2 : ¬ (k.natAbs ≠ 0 ∧ 2 * pentagonal k = k.natAbs * (3 * k.natAbs + 1)) := by
          rintro ⟨_, heq⟩
          have heqZ : 2 * (pentagonal k : ℤ) = (k.natAbs : ℤ) * (3 * (k.natAbs : ℤ) + 1) := by
            exact_mod_cast heq
          rw [← two_mul_natCast_pentagonal_neg (k.natAbs : ℤ)] at heqZ
          have hinj : pentagonal k = pentagonal (-(k.natAbs : ℤ)) := by
            exact_mod_cast (by linarith : (pentagonal k : ℤ) = pentagonal (-(k.natAbs : ℤ)))
          have := pentagonal_injective hinj
          omega
        rw [if_pos h1, if_neg h2, add_zero, pow_succ]
        ring
    · intro j _ hjne
      have h1 : ¬ (j ≠ 0 ∧ 2 * pentagonal k = j * (3 * j - 1)) := by
        rintro ⟨_, heq⟩
        have hle : 1 ≤ 3 * j := by omega
        have heqZ : 2 * (pentagonal k : ℤ) = (j : ℤ) * (3 * (j : ℤ) - 1) := by
          have hcast : ((2 * pentagonal k : ℕ) : ℤ) = ((j * (3 * j - 1) : ℕ) : ℤ) :=
            congrArg Nat.cast heq
          simpa [Nat.cast_sub hle] using hcast
        rw [← two_mul_natCast_pentagonal (j : ℤ)] at heqZ
        have hinj : pentagonal k = pentagonal (j : ℤ) := by
          exact_mod_cast (by linarith : (pentagonal k : ℤ) = pentagonal (j : ℤ))
        have := pentagonal_injective hinj
        omega
      have h2 : ¬ (j ≠ 0 ∧ 2 * pentagonal k = j * (3 * j + 1)) := by
        rintro ⟨_, heq⟩
        have heqZ : 2 * (pentagonal k : ℤ) = (j : ℤ) * (3 * (j : ℤ) + 1) := by exact_mod_cast heq
        rw [← two_mul_natCast_pentagonal_neg (j : ℤ)] at heqZ
        have hinj : pentagonal k = pentagonal (-(j : ℤ)) := by
          exact_mod_cast (by linarith : (pentagonal k : ℤ) = pentagonal (-(j : ℤ)))
        have := pentagonal_injective hinj
        omega
      rw [if_neg h1, if_neg h2, add_zero]
    · intro habs
      exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hj_le)) habs
  · rw [PowerSeries.coeff_pentagonalSeries_eq_zero ℤ hmem, neg_zero]
    apply Finset.sum_eq_zero
    intro j _
    have h1 : ¬ (j ≠ 0 ∧ 2 * g = j * (3 * j - 1)) := by
      rintro ⟨_, heq⟩
      apply hmem
      refine ⟨(j : ℤ), ?_⟩
      have hle : 1 ≤ 3 * j := by omega
      have heqZ : 2 * (g : ℤ) = (j : ℤ) * (3 * (j : ℤ) - 1) := by
        have hcast : ((2 * g : ℕ) : ℤ) = ((j * (3 * j - 1) : ℕ) : ℤ) := congrArg Nat.cast heq
        simpa [Nat.cast_sub hle] using hcast
      rw [← two_mul_natCast_pentagonal (j : ℤ)] at heqZ
      exact_mod_cast (by linarith : (pentagonal (j : ℤ) : ℤ) = g)
    have h2 : ¬ (j ≠ 0 ∧ 2 * g = j * (3 * j + 1)) := by
      rintro ⟨_, heq⟩
      apply hmem
      refine ⟨-(j : ℤ), ?_⟩
      have heqZ : 2 * (g : ℤ) = (j : ℤ) * (3 * (j : ℤ) + 1) := by exact_mod_cast heq
      rw [← two_mul_natCast_pentagonal_neg (j : ℤ)] at heqZ
      exact_mod_cast (by linarith : (pentagonal (-(j : ℤ)) : ℤ) = g)
    rw [if_neg h1, if_neg h2, add_zero]

private theorem pentagonalSeries_mul_genFun :
    PowerSeries.pentagonalSeries ℤ * Nat.Partition.genFun (fun _ _ => (1 : ℤ)) = 1 := by
  let _ : TopologicalSpace ℤ := ⊥
  have _ : DiscreteTopology ℤ := ⟨rfl⟩
  have hfactor : ∀ i : ℕ,
      (1 - X ^ (i + 1) : ℤ⟦X⟧) *
        ((1 : ℤ⟦X⟧) + ∑' j : ℕ, (1 : ℤ) • X ^ ((i + 1) * (j + 1))) = 1 := by
    intro i
    rw [mul_comm]
    set d := i + 1
    have hd : 0 < d := Nat.succ_pos i
    let f1 : ℕ → ℕ → ℤ := fun _ _ => 1
    set S : ℤ⟦X⟧ := 1 + ∑' j : ℕ, f1 (i + 1) (j + 1) • X ^ ((i + 1) * (j + 1))
    have hS_coeff : ∀ m : ℕ, S.coeff m = if d ∣ m then 1 else 0 := by
      intro m
      have hsum := (Nat.Partition.summable_genFun_term f1 i).map_tsum _
        (PowerSeries.WithPiTopology.continuous_coeff ℤ m)
      have hadd : S.coeff m = (1 : ℤ⟦X⟧).coeff m +
          ∑' j : ℕ, (coeff m) (f1 (i + 1) (j + 1) • X ^ ((i + 1) * (j + 1))) :=
        (map_add (coeff m) 1 _).trans (congrArg ((coeff m 1) + ·) hsum)
      rw [hadd, coeff_one]
      simp only [f1, one_smul, coeff_X_pow]
      rcases eq_or_ne m 0 with rfl | hm0
      · simp only [↓reduceIte, dvd_zero]
        have : ∀ x : ℕ, 0 ≠ (i + 1) * (x + 1) := fun x => (Nat.mul_pos hd (Nat.succ_pos x)).ne
        simp [this]
      · simp only [hm0, ↓reduceIte, zero_add]
        by_cases hdm : d ∣ m
        · obtain ⟨q, rfl⟩ := hdm
          have hq : 0 < q := by
            rcases eq_or_lt_of_le (Nat.zero_le q) with rfl | hq
            · simp at hm0
            · exact hq
          rw [if_pos ⟨q, rfl⟩, tsum_eq_single (q - 1)]
          · simp [d, Nat.sub_add_cancel hq]
          · intro b hb
            have : (i + 1) * q ≠ (i + 1) * (b + 1) := by
              intro heq
              have := Nat.eq_of_mul_eq_mul_left hd heq
              omega
            simp [d, this]
        · rw [if_neg hdm]
          convert tsum_zero with b
          have : m ≠ (i + 1) * (b + 1) := fun h => hdm ⟨b + 1, h⟩
          simp [this]
    ext m
    rw [mul_sub, mul_one, map_sub, coeff_mul_X_pow', hS_coeff]
    rcases eq_or_ne m 0 with rfl | hm0
    · have : ¬ d ≤ 0 := by omega
      simp [this]
    · simp only [coeff_one, hm0, ↓reduceIte]
      by_cases hdm : d ≤ m
      · rw [if_pos hdm, hS_coeff]
        by_cases h : d ∣ m
        · obtain ⟨q, rfl⟩ := h
          have hsub_dvd : d ∣ d * q - d := ⟨q - 1, (Nat.mul_sub_one d q).symm⟩
          rw [if_pos ⟨q, rfl⟩, if_pos hsub_dvd, sub_self]
        · have hsub_ndvd : ¬ d ∣ m - d := by
            rintro ⟨q, hq⟩
            exact h ⟨q + 1, by rw [Nat.mul_succ]; omega⟩
          rw [if_neg h, if_neg hsub_ndvd, sub_self]
      · have hndvd : ¬ d ∣ m := fun h => hdm (Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) h)
        simp [hdm, hndvd]
  have h1 := PowerSeries.WithPiTopology.hasProd_one_sub_X_pow ℤ
  have h2 := Nat.Partition.hasProd_genFun (fun _ _ => (1 : ℤ))
  have hmul : HasProd (fun _ : ℕ => (1 : ℤ⟦X⟧))
      (PowerSeries.pentagonalSeries ℤ * Nat.Partition.genFun (fun _ _ => (1 : ℤ))) :=
    (h1.mul h2).congr fun s => Finset.prod_congr rfl fun i _ => hfactor i
  exact hmul.unique hasProd_one

private theorem partition_pentagonal_recurrence {n : ℕ} (hn : 1 ≤ n) :
    (OMA.S_oeis_a000041.a n : ℤ) =
      ∑ k ∈ Finset.range n, OMA.S_oeis_a000041.signedPentagonal (k + 1) *
        (OMA.S_oeis_a000041.a (n - 1 - k) : ℤ) := by
  have hcoeff_gen : ∀ m : ℕ, (Nat.Partition.genFun (fun _ _ => (1 : ℤ))).coeff m =
      (OMA.S_oeis_a000041.a m : ℤ) := by
    intro m
    rw [Nat.Partition.coeff_genFun]
    simp [OMA.S_oeis_a000041.a, Finsupp.prod]
  have hmul := congrArg (PowerSeries.coeff n) pentagonalSeries_mul_genFun
  have hn0 : n ≠ 0 := by omega
  rw [PowerSeries.coeff_one, if_neg hn0, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j =>
        (PowerSeries.pentagonalSeries ℤ).coeff i *
          (Nat.Partition.genFun (fun _ _ => (1 : ℤ))).coeff j),
      Finset.sum_range_succ'] at hmul
  have hc0 : (PowerSeries.pentagonalSeries ℤ).coeff 0 = 1 := by
    have h0 : pentagonal 0 = 0 := rfl
    rw [← h0, PowerSeries.coeff_pentagonalSeries_pentagonal]
    rfl
  rw [hc0, one_mul, Nat.sub_zero, hcoeff_gen n] at hmul
  have hsum_eq :
      ∑ k ∈ Finset.range n,
        (PowerSeries.pentagonalSeries ℤ).coeff (k + 1) *
          (Nat.Partition.genFun (fun _ _ => (1 : ℤ))).coeff (n - (k + 1)) =
      -∑ k ∈ Finset.range n,
        OMA.S_oeis_a000041.signedPentagonal (k + 1) *
          (OMA.S_oeis_a000041.a (n - 1 - k) : ℤ) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hsp := signedPentagonal_eq_neg_coeff (by omega : 1 ≤ k + 1)
    have hsub : n - (k + 1) = n - 1 - k := by omega
    rw [hsub, hcoeff_gen, hsp]
    ring
  rw [hsum_eq] at hmul
  linarith

private theorem composition_pentagonal_zero :
    (∑ c : Composition 0, (c.blocks.map OMA.S_oeis_a000041.signedPentagonal).prod) = 1 := by
  have huniq : ∀ c : Composition 0, c = Composition.ones 0 := by
    intro c
    ext1
    rw [c.blocks_eq_nil.mpr rfl, Composition.ones_blocks, List.replicate_zero]
  rw [Finset.sum_eq_single (Composition.ones 0)]
  · simp [Composition.ones_blocks]
  · intro c _ hc
    exact absurd (huniq c) hc
  · simp

private theorem composition_pentagonal_recurrence {n : ℕ} (hn : 1 ≤ n) :
    (∑ c : Composition n, (c.blocks.map OMA.S_oeis_a000041.signedPentagonal).prod) =
      ∑ k ∈ Finset.range n, OMA.S_oeis_a000041.signedPentagonal (k + 1) *
        (∑ c' : Composition (n - 1 - k),
          (c'.blocks.map OMA.S_oeis_a000041.signedPentagonal).prod) := by
  let e : (Σ k : Fin n, Composition (n - 1 - k.val)) ≃ Composition n :=
    { toFun := fun ⟨k, c'⟩ =>
        ⟨(k.val + 1) :: c'.blocks,
         by
           intro i hi
           rcases List.mem_cons.mp hi with rfl | hi'
           · omega
           · exact c'.blocks_pos hi',
         by
           simp only [List.sum_cons, c'.blocks_sum]
           have := k.isLt
           omega⟩
      invFun := fun c =>
        have hne : c.blocks ≠ [] := c.blocks_eq_nil.not.mpr (by omega)
        have hmem : c.blocks.head hne ∈ c.blocks := List.head_mem hne
        have hpos : 1 ≤ c.blocks.head hne := c.one_le_blocks hmem
        have hle : c.blocks.head hne ≤ n := c.blocks_le hmem
        ⟨⟨c.blocks.head hne - 1, by omega⟩,
         ⟨c.blocks.tail,
          fun hi => c.blocks_pos (List.mem_of_mem_tail hi),
          by
            have hcons := List.cons_head_tail hne
            have hsum : (c.blocks.head hne :: c.blocks.tail).sum = n := by
              rw [hcons, c.blocks_sum]
            simp only [List.sum_cons] at hsum
            dsimp only
            omega⟩⟩
      left_inv := fun ⟨k, c'⟩ => by
        refine Sigma.ext (Fin.ext (by simp)) (heq_of_eq ?_)
        ext1
        simp
      right_inv := fun c => by
        have hne : c.blocks ≠ [] := c.blocks_eq_nil.not.mpr (by omega)
        have hpos : 1 ≤ c.blocks.head hne := c.one_le_blocks (List.head_mem hne)
        ext1
        simp only [Nat.sub_add_cancel hpos]
        exact List.cons_head_tail hne }
  have hsum := Fintype.sum_equiv e
    (fun x : Σ k : Fin n, Composition (n - 1 - k.val) =>
      OMA.S_oeis_a000041.signedPentagonal (x.1.val + 1) *
        (x.2.blocks.map OMA.S_oeis_a000041.signedPentagonal).prod)
    (fun c : Composition n => (c.blocks.map OMA.S_oeis_a000041.signedPentagonal).prod)
    (fun ⟨k, c'⟩ => by simp [e, List.map_cons, List.prod_cons])
  rw [← hsum, Fintype.sum_sigma]
  have hmul : ∀ k : Fin n,
      (∑ c' : Composition (n - 1 - k.val),
        OMA.S_oeis_a000041.signedPentagonal (k.val + 1) *
          (c'.blocks.map OMA.S_oeis_a000041.signedPentagonal).prod) =
      OMA.S_oeis_a000041.signedPentagonal (k.val + 1) *
        ∑ c' : Composition (n - 1 - k.val),
          (c'.blocks.map OMA.S_oeis_a000041.signedPentagonal).prod :=
    fun k => (Finset.mul_sum Finset.univ _ _).symm
  simp_rw [hmul]
  exact Fin.sum_univ_eq_sum_range
    (fun k => OMA.S_oeis_a000041.signedPentagonal (k + 1) *
      ∑ c' : Composition (n - 1 - k),
        (c'.blocks.map OMA.S_oeis_a000041.signedPentagonal).prod) n

theorem conjecture_1 :
    ∀ n : ℕ, 1 ≤ n →
      (OMA.S_oeis_a000041.a n : ℤ) =
        ∑ c : Composition n, (c.blocks.map OMA.S_oeis_a000041.signedPentagonal).prod := by
  have hall : ∀ n : ℕ, (OMA.S_oeis_a000041.a n : ℤ) =
      ∑ c : Composition n, (c.blocks.map OMA.S_oeis_a000041.signedPentagonal).prod := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      rcases eq_or_ne n 0 with rfl | hn0
      · rw [composition_pentagonal_zero]
        simp [OMA.S_oeis_a000041.a]
      · have hn1 : 1 ≤ n := by omega
        rw [partition_pentagonal_recurrence hn1, composition_pentagonal_recurrence hn1]
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [Finset.mem_range] at hk
        rw [ih (n - 1 - k) (by omega)]
  exact fun n _ => hall n

private theorem sum_range_eq_list_sum {α : Type*} [AddCommMonoid α] (m : ℕ) (f : ℕ → α) :
    (∑ j ∈ Finset.range m, f j) = ((List.range m).map f).sum := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, List.range_succ, List.map_append, List.sum_append, ih]
    simp

private theorem ne_pow_of_ne_prime_pow {v : ℕ}
    (hprime : ∀ p y : ℕ, Nat.Prime p → 1 < y → v ≠ y ^ p) :
    ∀ x m : ℕ, 1 < m → 1 < x → v ≠ x ^ m := by
  intro x m hm hx heq
  let p := m.minFac
  have hp : Nat.Prime p := Nat.minFac_prime (by omega)
  obtain ⟨q, hmq⟩ := Nat.minFac_dvd m
  have hq0 : q ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hmq
    omega
  have hy1 : 1 < x ^ q := by
    obtain ⟨q', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq0
    calc 1 < x := hx
      _ = x ^ 1 := (pow_one x).symm
      _ ≤ x ^ (q' + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hpow : (x ^ q) ^ p = x ^ m := by
    rw [← pow_mul, mul_comm, ← hmq]
  exact hprime p (x ^ q) hp hy1 (heq.trans hpow.symm)

private theorem prime_lt_36_mem {p : ℕ} (hp : Nat.Prime p) (hlt : p < 36) :
    ∃ j : Fin 11, [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31][j.val]?.getD 0 = p := by
  have hdec : ∀ q : Fin 36, Nat.Prime q.val →
      ∃ j : Fin 11, [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31][j.val]?.getD 0 = q.val := by
    decide +kernel
  exact hdec ⟨p, hlt⟩ hp

private theorem witness_of_ks {n : ℕ} (ks : List ℕ)
    (hpos : ∀ k ∈ ks, 0 < k)
    (hpair : (ks.map fun k => OMA.S_oeis_a000041.a k + 2).Pairwise
      (fun x y => ¬ x ∣ y ∧ ¬ y ∣ x))
    (hsum : (ks.map fun k => OMA.S_oeis_a000041.a k + 2).sum = n) :
    ∃ (j : ℕ) (b : Fin j → ℕ),
      (∀ i, ∃ k : ℕ, 0 < k ∧ b i = OMA.S_oeis_a000041.a k + 2) ∧
      (∀ i i', i ≠ i' → ¬ b i ∣ b i') ∧
      ∑ i, b i = n := by
  let bs := ks.map fun k => OMA.S_oeis_a000041.a k + 2
  refine ⟨bs.length, bs.get, ?_, ?_, ?_⟩
  · intro i
    have hi : i.val < ks.length := by simpa [bs] using i.isLt
    refine ⟨ks[i.val], hpos _ (List.getElem_mem hi), ?_⟩
    simp [bs]
  · intro i i' hii'
    have hne : i.val ≠ i'.val := Fin.val_ne_of_ne hii'
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact (List.pairwise_iff_getElem.mp hpair i.val i'.val i.isLt i'.isLt hlt).1
    · exact (List.pairwise_iff_getElem.mp hpair i'.val i.val i'.isLt i.isLt hgt).2
  · rw [← List.sum_ofFn, List.ofFn_get]
    exact hsum

private theorem sublist_interval_step {w : ℕ → ℕ} {P : List ℕ} {k : ℕ}
    (hbase : ∀ n, 60 ≤ n → n ≤ (P.map w).sum - 60 → ∃ sub, List.Sublist sub P ∧ (sub.map w).sum = n)
    (hk : 119 + w k ≤ (P.map w).sum) :
    ∀ n, 60 ≤ n → n ≤ ((P ++ [k]).map w).sum - 60 →
      ∃ sub, List.Sublist sub (P ++ [k]) ∧ (sub.map w).sum = n := by
  intro n hn1 hn2
  rw [List.map_append, List.sum_append, List.map_singleton, List.sum_singleton] at hn2
  by_cases hle : n ≤ (P.map w).sum - 60
  · obtain ⟨sub, hsub, hsum⟩ := hbase n hn1 hle
    exact ⟨sub, hsub.trans (List.sublist_append_left P [k]), hsum⟩
  · obtain ⟨sub, hsub, hsum⟩ := hbase (n - w k) (by omega) (by omega)
    refine ⟨sub ++ [k], hsub.append (List.Sublist.refl [k]), ?_⟩
    rw [List.map_append, List.sum_append, List.map_singleton, List.sum_singleton, hsum]
    omega

private theorem sublist_interval_extend {w : ℕ → ℕ} (rest P : List ℕ)
    (hbase : ∀ n, 60 ≤ n → n ≤ (P.map w).sum - 60 → ∃ sub, List.Sublist sub P ∧ (sub.map w).sum = n)
    (hcond : ∀ i : Fin rest.length, 119 + w rest[i.val] ≤ ((P ++ rest.take i.val).map w).sum) :
    ∀ n, 60 ≤ n → n ≤ ((P ++ rest).map w).sum - 60 →
      ∃ sub, List.Sublist sub (P ++ rest) ∧ (sub.map w).sum = n := by
  induction rest generalizing P with
  | nil => simpa using hbase
  | cons k tail ih =>
    have hk0 : 119 + w k ≤ (P.map w).sum := by
      simpa using hcond ⟨0, Nat.succ_pos _⟩
    have hbase' := sublist_interval_step hbase hk0
    have hcond' : ∀ i : Fin tail.length,
        119 + w tail[i.val] ≤ (((P ++ [k]) ++ tail.take i.val).map w).sum := by
      intro i
      have hi := hcond ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
      simpa [List.take_succ_cons, List.append_assoc] using hi
    simpa [List.append_assoc] using ih (P ++ [k]) hbase' hcond'

set_option maxHeartbeats 800000 in
private theorem exists_certified_tables :
    ∃ (spTable : List ℤ) (pTable : List ℕ) (c2Roots : List (List ℕ))
      (smallWits : List (List ℕ)) (ks82 ws82 : List ℕ) (baseSubs : List (List ℕ)),
      (∀ k : Fin 150,
        spTable[k.val]?.getD 0 =
          ((List.range (k.val + 2)).map fun j =>
            (if j ≠ 0 ∧ 2 * (k.val + 1) = j * (3 * j - 1) then (-1 : ℤ) ^ (j + 1) else 0) +
              (if j ≠ 0 ∧ 2 * (k.val + 1) = j * (3 * j + 1) then (-1 : ℤ) ^ (j + 1) else 0)).sum) ∧
      (pTable[0]?.getD 0 = 1 ∧ pTable[1]?.getD 0 = 1 ∧
        ∀ m : Fin 150,
          (pTable[m.val + 1]?.getD 0 : ℤ) =
            ((List.range (m.val + 1)).map fun k =>
              spTable[k]?.getD 0 * (pTable[m.val - k]?.getD 0 : ℤ)).sum) ∧
      ((∀ idx : Fin 149, pTable[idx.val + 2]?.getD 0 < 2 ^ 36) ∧
        (∀ idx : Fin 149, ∀ j : Fin 11,
          let v := pTable[idx.val + 2]?.getD 0
          let p := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31][j.val]?.getD 0
          let r := (c2Roots[idx.val]?.getD [])[j.val]?.getD 0
          r ^ p < v ∧ v < (r + 1) ^ p)) ∧
      (∀ n : Fin 60,
        n.val < 3 ∨ n.val = 6 ∨
          (let ks := smallWits[n.val]?.getD []
           (∀ k ∈ ks, 1 ≤ k ∧ k ≤ 150) ∧
             (ks.map fun k => pTable[k]?.getD 0 + 2).Pairwise (fun x y => ¬ x ∣ y ∧ ¬ y ∣ x) ∧
             (ks.map fun k => pTable[k]?.getD 0 + 2).sum = n.val)) ∧
      ((∀ k ∈ ks82, 1 ≤ k ∧ k ≤ 150) ∧
        ks82.map (fun k => pTable[k]?.getD 0 + 2) = ws82 ∧
        ws82.Pairwise (fun x y => ¬ x ∣ y ∧ ¬ y ∣ x) ∧
        (ws82.take 9).sum = 283 ∧
        200000000060 ≤ ws82.sum ∧
        (∀ d : Fin 164,
          let sub := baseSubs[d.val]?.getD []
          List.Sublist sub (ks82.take 9) ∧
            (sub.map fun k => pTable[k]?.getD 0 + 2).sum = d.val + 60) ∧
        (∀ i : Fin (ks82.drop 9).length,
          119 + (pTable[(ks82.drop 9)[i.val]]?.getD 0 + 2) ≤
            (ws82.take 9 ++ (ws82.drop 9).take i.val).sum)) :=
  ⟨[
        1, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 1, 0, 0, 1,
        0, 0, 0, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0, 0,
        0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0,
        0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, -1, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0,
        0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0
      ],
   [
        1, 1, 2, 3, 5, 7,
        11, 15, 22, 30, 42, 56,
        77, 101, 135, 176, 231, 297,
        385, 490, 627, 792, 1002, 1255,
        1575, 1958, 2436, 3010, 3718, 4565,
        5604, 6842, 8349, 10143, 12310, 14883,
        17977, 21637, 26015, 31185, 37338, 44583,
        53174, 63261, 75175, 89134, 105558, 124754,
        147273, 173525, 204226, 239943, 281589, 329931,
        386155, 451276, 526823, 614154, 715220, 831820,
        966467, 1121505, 1300156, 1505499, 1741630, 2012558,
        2323520, 2679689, 3087735, 3554345, 4087968, 4697205,
        5392783, 6185689, 7089500, 8118264, 9289091, 10619863,
        12132164, 13848650, 15796476, 18004327, 20506255, 23338469,
        26543660, 30167357, 34262962, 38887673, 44108109, 49995925,
        56634173, 64112359, 72533807, 82010177, 92669720, 104651419,
        118114304, 133230930, 150198136, 169229875, 190569292, 214481126,
        241265379, 271248950, 304801365, 342325709, 384276336, 431149389,
        483502844, 541946240, 607163746, 679903203, 761002156, 851376628,
        952050665, 1064144451, 1188908248, 1327710076, 1482074143, 1653668665,
        1844349560, 2056148051, 2291320912, 2552338241, 2841940500, 3163127352,
        3519222692, 3913864295, 4351078600, 4835271870, 5371315400, 5964539504,
        6620830889, 7346629512, 8149040695, 9035836076, 10015581680, 11097645016,
        12292341831, 13610949895, 15065878135, 16670689208, 18440293320, 20390982757,
        22540654445, 24908858009, 27517052599, 30388671978, 33549419497, 37027355200,
        40853235313
      ],
   [
        [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
        [3, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1], [3, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1], [4, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1], [5, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1],
        [6, 3, 2, 1, 1, 1, 1, 1, 1, 1, 1], [7, 3, 2, 1, 1, 1, 1, 1, 1, 1, 1], [8, 4, 2, 1, 1, 1, 1, 1, 1, 1, 1], [10, 4, 2, 1, 1, 1, 1, 1, 1, 1, 1],
        [11, 5, 2, 2, 1, 1, 1, 1, 1, 1, 1], [13, 5, 2, 2, 1, 1, 1, 1, 1, 1, 1], [15, 6, 2, 2, 1, 1, 1, 1, 1, 1, 1], [17, 6, 3, 2, 1, 1, 1, 1, 1, 1, 1],
        [19, 7, 3, 2, 1, 1, 1, 1, 1, 1, 1], [22, 7, 3, 2, 1, 1, 1, 1, 1, 1, 1], [25, 8, 3, 2, 1, 1, 1, 1, 1, 1, 1], [28, 9, 3, 2, 1, 1, 1, 1, 1, 1, 1],
        [31, 10, 3, 2, 1, 1, 1, 1, 1, 1, 1], [35, 10, 4, 2, 1, 1, 1, 1, 1, 1, 1], [39, 11, 4, 2, 1, 1, 1, 1, 1, 1, 1], [44, 12, 4, 2, 1, 1, 1, 1, 1, 1, 1],
        [49, 13, 4, 3, 2, 1, 1, 1, 1, 1, 1], [54, 14, 4, 3, 2, 1, 1, 1, 1, 1, 1], [60, 15, 5, 3, 2, 1, 1, 1, 1, 1, 1], [67, 16, 5, 3, 2, 1, 1, 1, 1, 1, 1],
        [74, 17, 5, 3, 2, 1, 1, 1, 1, 1, 1], [82, 18, 5, 3, 2, 1, 1, 1, 1, 1, 1], [91, 20, 6, 3, 2, 2, 1, 1, 1, 1, 1], [100, 21, 6, 3, 2, 2, 1, 1, 1, 1, 1],
        [110, 23, 6, 3, 2, 2, 1, 1, 1, 1, 1], [121, 24, 6, 3, 2, 2, 1, 1, 1, 1, 1], [134, 26, 7, 4, 2, 2, 1, 1, 1, 1, 1], [147, 27, 7, 4, 2, 2, 1, 1, 1, 1, 1],
        [161, 29, 7, 4, 2, 2, 1, 1, 1, 1, 1], [176, 31, 7, 4, 2, 2, 1, 1, 1, 1, 1], [193, 33, 8, 4, 2, 2, 1, 1, 1, 1, 1], [211, 35, 8, 4, 2, 2, 1, 1, 1, 1, 1],
        [230, 37, 8, 4, 2, 2, 1, 1, 1, 1, 1], [251, 39, 9, 4, 2, 2, 1, 1, 1, 1, 1], [274, 42, 9, 4, 2, 2, 1, 1, 1, 1, 1], [298, 44, 9, 5, 2, 2, 1, 1, 1, 1, 1],
        [324, 47, 10, 5, 2, 2, 1, 1, 1, 1, 1], [353, 49, 10, 5, 2, 2, 1, 1, 1, 1, 1], [383, 52, 10, 5, 2, 2, 2, 1, 1, 1, 1], [416, 55, 11, 5, 2, 2, 2, 1, 1, 1, 1],
        [451, 58, 11, 5, 3, 2, 2, 1, 1, 1, 1], [489, 62, 11, 5, 3, 2, 2, 1, 1, 1, 1], [530, 65, 12, 6, 3, 2, 2, 1, 1, 1, 1], [574, 69, 12, 6, 3, 2, 2, 1, 1, 1, 1],
        [621, 72, 13, 6, 3, 2, 2, 1, 1, 1, 1], [671, 76, 13, 6, 3, 2, 2, 1, 1, 1, 1], [725, 80, 13, 6, 3, 2, 2, 2, 1, 1, 1], [783, 85, 14, 6, 3, 2, 2, 2, 1, 1, 1],
        [845, 89, 14, 6, 3, 2, 2, 2, 1, 1, 1], [912, 94, 15, 7, 3, 2, 2, 2, 1, 1, 1], [983, 98, 15, 7, 3, 2, 2, 2, 1, 1, 1], [1059, 103, 16, 7, 3, 2, 2, 2, 1, 1, 1],
        [1140, 109, 16, 7, 3, 2, 2, 2, 1, 1, 1], [1226, 114, 17, 7, 3, 2, 2, 2, 1, 1, 1], [1319, 120, 17, 7, 3, 3, 2, 2, 1, 1, 1], [1418, 126, 18, 7, 3, 3, 2, 2, 1, 1, 1],
        [1524, 132, 18, 8, 3, 3, 2, 2, 1, 1, 1], [1636, 138, 19, 8, 3, 3, 2, 2, 1, 1, 1], [1757, 145, 19, 8, 3, 3, 2, 2, 1, 1, 1], [1885, 152, 20, 8, 3, 3, 2, 2, 1, 1, 1],
        [2021, 159, 21, 8, 3, 3, 2, 2, 1, 1, 1], [2167, 167, 21, 8, 4, 3, 2, 2, 1, 1, 1], [2322, 175, 22, 9, 4, 3, 2, 2, 1, 1, 1], [2487, 183, 22, 9, 4, 3, 2, 2, 1, 1, 1],
        [2662, 192, 23, 9, 4, 3, 2, 2, 1, 1, 1], [2849, 200, 24, 9, 4, 3, 2, 2, 1, 1, 1], [3047, 210, 24, 9, 4, 3, 2, 2, 2, 1, 1], [3258, 219, 25, 10, 4, 3, 2, 2, 2, 1, 1],
        [3483, 229, 26, 10, 4, 3, 2, 2, 2, 1, 1], [3721, 240, 26, 10, 4, 3, 2, 2, 2, 1, 1], [3974, 250, 27, 10, 4, 3, 2, 2, 2, 1, 1], [4243, 262, 28, 10, 4, 3, 2, 2, 2, 1, 1],
        [4528, 273, 28, 11, 4, 3, 2, 2, 2, 1, 1], [4830, 285, 29, 11, 4, 3, 2, 2, 2, 1, 1], [5152, 298, 30, 11, 4, 3, 2, 2, 2, 1, 1], [5492, 311, 31, 11, 4, 3, 2, 2, 2, 1, 1],
        [5853, 324, 32, 11, 4, 3, 2, 2, 2, 1, 1], [6235, 338, 32, 12, 4, 3, 2, 2, 2, 1, 1], [6641, 353, 33, 12, 4, 3, 2, 2, 2, 1, 1], [7070, 368, 34, 12, 5, 3, 2, 2, 2, 1, 1],
        [7525, 384, 35, 12, 5, 3, 2, 2, 2, 1, 1], [8007, 400, 36, 13, 5, 3, 2, 2, 2, 1, 1], [8516, 417, 37, 13, 5, 4, 2, 2, 2, 1, 1], [9055, 434, 38, 13, 5, 4, 2, 2, 2, 1, 1],
        [9626, 452, 39, 13, 5, 4, 2, 2, 2, 1, 1], [10229, 471, 40, 13, 5, 4, 2, 2, 2, 1, 1], [10868, 490, 41, 14, 5, 4, 2, 2, 2, 1, 1], [11542, 510, 42, 14, 5, 4, 3, 2, 2, 1, 1],
        [12255, 531, 43, 14, 5, 4, 3, 2, 2, 1, 1], [13008, 553, 44, 14, 5, 4, 3, 2, 2, 1, 1], [13804, 575, 45, 15, 5, 4, 3, 2, 2, 1, 1], [14645, 598, 46, 15, 5, 4, 3, 2, 2, 1, 1],
        [15532, 622, 47, 15, 5, 4, 3, 2, 2, 1, 1], [16469, 647, 48, 16, 5, 4, 3, 2, 2, 1, 1], [17458, 672, 49, 16, 5, 4, 3, 2, 2, 1, 1], [18502, 699, 50, 16, 5, 4, 3, 2, 2, 1, 1],
        [19602, 727, 52, 16, 6, 4, 3, 2, 2, 1, 1], [20764, 755, 53, 17, 6, 4, 3, 2, 2, 1, 1], [21988, 784, 54, 17, 6, 4, 3, 2, 2, 1, 1], [23279, 815, 55, 17, 6, 4, 3, 2, 2, 2, 1],
        [24640, 846, 57, 17, 6, 4, 3, 2, 2, 2, 1], [26074, 879, 58, 18, 6, 4, 3, 2, 2, 2, 1], [27586, 912, 59, 18, 6, 4, 3, 2, 2, 2, 1], [29178, 947, 61, 18, 6, 4, 3, 2, 2, 2, 1],
        [30855, 983, 62, 19, 6, 4, 3, 2, 2, 2, 1], [32621, 1020, 63, 19, 6, 4, 3, 2, 2, 2, 1], [34480, 1059, 65, 19, 6, 4, 3, 3, 2, 2, 1], [36437, 1099, 66, 20, 6, 5, 3, 3, 2, 2, 1],
        [38497, 1140, 68, 20, 6, 5, 3, 3, 2, 2, 1], [40665, 1182, 69, 20, 6, 5, 3, 3, 2, 2, 1], [42945, 1226, 71, 21, 6, 5, 3, 3, 2, 2, 1], [45344, 1271, 72, 21, 7, 5, 3, 3, 2, 2, 1],
        [47867, 1318, 74, 21, 7, 5, 3, 3, 2, 2, 2], [50520, 1366, 76, 22, 7, 5, 3, 3, 2, 2, 2], [53309, 1416, 77, 22, 7, 5, 3, 3, 2, 2, 2], [56241, 1467, 79, 22, 7, 5, 3, 3, 2, 2, 2],
        [59323, 1521, 81, 23, 7, 5, 3, 3, 2, 2, 2], [62560, 1575, 82, 23, 7, 5, 3, 3, 2, 2, 2], [65962, 1632, 84, 23, 7, 5, 3, 3, 2, 2, 2], [69536, 1690, 86, 24, 7, 5, 3, 3, 2, 2, 2],
        [73289, 1751, 88, 24, 7, 5, 3, 3, 2, 2, 2], [77230, 1813, 90, 24, 7, 5, 3, 3, 2, 2, 2], [81368, 1877, 92, 25, 7, 5, 3, 3, 2, 2, 2], [85712, 1943, 94, 25, 7, 5, 3, 3, 2, 2, 2],
        [90272, 2012, 95, 26, 7, 5, 3, 3, 2, 2, 2], [95057, 2082, 97, 26, 8, 5, 3, 3, 2, 2, 2], [100077, 2155, 100, 26, 8, 5, 3, 3, 2, 2, 2], [105345, 2230, 102, 27, 8, 5, 3, 3, 2, 2, 2],
        [110870, 2307, 104, 27, 8, 5, 3, 3, 2, 2, 2], [116665, 2387, 106, 28, 8, 6, 3, 3, 2, 2, 2], [122743, 2469, 108, 28, 8, 6, 3, 3, 2, 2, 2], [129115, 2554, 110, 28, 8, 6, 3, 3, 2, 2, 2],
        [135795, 2641, 113, 29, 8, 6, 4, 3, 2, 2, 2], [142796, 2731, 115, 29, 8, 6, 4, 3, 2, 2, 2], [150135, 2824, 117, 30, 8, 6, 4, 3, 2, 2, 2], [157825, 2920, 120, 30, 8, 6, 4, 3, 2, 2, 2],
        [165882, 3019, 122, 31, 8, 6, 4, 3, 2, 2, 2], [174323, 3120, 124, 31, 8, 6, 4, 3, 2, 2, 2], [183165, 3225, 127, 31, 9, 6, 4, 3, 2, 2, 2], [192424, 3333, 129, 32, 9, 6, 4, 3, 2, 2, 2],
        [202121, 3444, 132, 32, 9, 6, 4, 3, 2, 2, 2]
      ],
   [
        [], [], [], [1], [2], [3], [], [1, 2],
        [1, 3], [2, 3], [1, 4], [2, 4], [1, 2, 3], [2, 5], [1, 2, 4], [1, 3, 4],
        [1, 6], [2, 6], [2, 3, 5], [1, 2, 3, 4], [1, 2, 6], [1, 3, 6], [2, 3, 6], [1, 4, 6],
        [1, 2, 7], [1, 2, 3, 6], [2, 3, 7], [1, 2, 4, 6], [1, 3, 4, 6], [1, 2, 3, 7], [2, 5, 7], [1, 2, 4, 7],
        [1, 2, 3, 4, 6], [1, 6, 7], [2, 6, 7], [1, 9], [1, 2, 3, 4, 7], [1, 2, 6, 7], [1, 3, 6, 7], [2, 3, 6, 7],
        [1, 3, 9], [2, 4, 6, 7], [1, 2, 3, 6, 7], [2, 5, 6, 7], [1, 2, 4, 6, 7], [1, 3, 4, 6, 7], [2, 3, 4, 6, 7], [1, 3, 4, 9],
        [1, 6, 9], [1, 2, 3, 4, 6, 7], [2, 4, 5, 6, 7], [3, 4, 5, 6, 7], [1, 3, 10], [1, 3, 6, 9], [1, 4, 10], [1, 4, 6, 9],
        [3, 4, 10], [1, 3, 7, 9], [3, 4, 5, 6, 8], [1, 3, 4, 10]
      ],
   [
        4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 19,
        21, 22, 23, 24, 26, 29, 30, 33, 37, 38, 40, 41, 43, 47,
        49, 51, 52, 53, 54, 57, 58, 59, 63, 66, 68, 69, 70, 71,
        76, 78, 79, 80, 84, 85, 87, 88, 91, 92, 93, 94, 96, 97,
        99, 101, 106, 107, 108, 110, 111, 114, 115, 116, 120, 121, 124, 125,
        130, 132, 135, 136, 137, 138, 139, 140, 144, 145, 148, 150
      ],
   [
        7, 9, 13, 17, 24, 32, 44, 58,
        79, 103, 137, 178, 233, 492, 794, 1004,
        1257, 1577, 2438, 4567, 5606, 10145, 21639, 26017,
        37340, 44585, 63263, 124756, 173527, 239945, 281591, 329933,
        386157, 614156, 715222, 831822, 1505501, 2323522, 3087737, 3554347,
        4087970, 4697207, 9289093, 12132166, 13848652, 15796478, 26543662, 30167359,
        38887675, 44108111, 64112361, 72533809, 82010179, 92669722, 118114306, 133230932,
        169229877, 214481128, 384276338, 431149391, 483502846, 607163748, 679903205, 952050667,
        1064144453, 1188908250, 1844349562, 2056148053, 2841940502, 3163127354, 5371315402, 6620830891,
        9035836078, 10015581682, 11097645018, 12292341833, 13610949897, 15065878137, 22540654447, 24908858011,
        33549419499, 40853235315
      ],
   [
        [4, 5, 10], [4, 6, 7, 8], [6, 7, 9], [5, 6, 7, 8], [4, 6, 10], [4, 5, 7, 9],
        [5, 6, 10], [5, 11], [4, 7, 10], [4, 6, 7, 9], [4, 5, 6, 7, 8], [5, 6, 7, 9],
        [4, 5, 8, 9], [7, 8, 9], [6, 7, 10], [4, 8, 10], [4, 6, 8, 9], [4, 5, 7, 10],
        [4, 5, 6, 7, 9], [12], [4, 7, 8, 9], [4, 6, 7, 10], [5, 7, 8, 9], [5, 6, 7, 10],
        [4, 5, 8, 10], [4, 5, 6, 8, 9], [6, 7, 8, 9], [4, 5, 6, 11], [4, 6, 8, 10], [4, 5, 7, 8, 9],
        [4, 5, 6, 7, 10], [4, 5, 7, 11], [4, 7, 8, 10], [4, 6, 7, 8, 9], [5, 7, 8, 10], [5, 6, 7, 8, 9],
        [4, 6, 9, 10], [4, 5, 6, 8, 10], [6, 7, 8, 10], [7, 8, 11], [4, 7, 9, 10], [4, 5, 7, 8, 10],
        [4, 5, 6, 7, 8, 9], [6, 9, 11], [4, 5, 6, 7, 11], [4, 6, 7, 8, 10], [6, 7, 9, 10], [5, 6, 7, 8, 10],
        [5, 7, 8, 11], [4, 5, 7, 9, 10], [4, 6, 9, 11], [4, 5, 6, 8, 11], [6, 7, 8, 11], [4, 6, 7, 9, 10],
        [4, 5, 6, 7, 8, 10], [5, 6, 7, 9, 10], [4, 5, 8, 9, 10], [7, 8, 9, 10], [4, 5, 10, 11], [4, 6, 7, 8, 11],
        [4, 6, 8, 9, 10], [5, 6, 7, 8, 11], [4, 5, 6, 7, 9, 10], [4, 5, 7, 9, 11], [4, 7, 8, 9, 10], [4, 5, 6, 7, 12],
        [5, 7, 8, 9, 10], [4, 6, 7, 9, 11], [4, 5, 6, 7, 8, 11], [4, 5, 6, 8, 9, 10], [6, 7, 8, 9, 10], [7, 8, 9, 11],
        [6, 7, 10, 11], [4, 5, 7, 8, 9, 10], [4, 6, 8, 9, 11], [4, 5, 7, 10, 11], [4, 5, 6, 7, 9, 11], [4, 6, 7, 8, 9, 10],
        [4, 7, 8, 9, 11], [5, 6, 7, 8, 9, 10], [5, 7, 8, 9, 11], [5, 6, 7, 10, 11], [4, 5, 8, 10, 11], [4, 5, 6, 8, 9, 11],
        [6, 7, 8, 9, 11], [5, 6, 10, 12], [4, 5, 6, 7, 8, 9, 10], [4, 5, 7, 8, 9, 11], [4, 5, 6, 7, 10, 11], [4, 5, 6, 7, 8, 12],
        [4, 7, 8, 10, 11], [4, 6, 7, 8, 9, 11], [5, 7, 8, 10, 11], [5, 6, 7, 8, 9, 11], [4, 6, 9, 10, 11], [4, 5, 6, 8, 10, 11],
        [6, 7, 8, 10, 11], [4, 5, 6, 7, 9, 12], [4, 7, 9, 10, 11], [4, 5, 7, 8, 10, 11], [4, 5, 6, 7, 8, 9, 11], [5, 7, 8, 9, 12],
        [5, 6, 7, 10, 12], [4, 6, 7, 8, 10, 11], [6, 7, 9, 10, 11], [5, 6, 7, 8, 10, 11], [4, 5, 6, 11, 12], [4, 5, 7, 9, 10, 11],
        [4, 5, 7, 8, 9, 12], [4, 5, 6, 7, 10, 12], [4, 5, 7, 11, 12], [4, 6, 7, 9, 10, 11], [4, 5, 6, 7, 8, 10, 11], [5, 6, 7, 9, 10, 11],
        [4, 5, 8, 9, 10, 11], [7, 8, 9, 10, 11], [4, 5, 6, 8, 10, 12], [6, 7, 8, 10, 12], [4, 6, 8, 9, 10, 11], [4, 7, 9, 10, 12],
        [4, 5, 6, 7, 9, 10, 11], [4, 5, 6, 7, 8, 9, 12], [4, 7, 8, 9, 10, 11], [4, 5, 6, 7, 11, 12], [5, 7, 8, 9, 10, 11], [6, 7, 9, 10, 12],
        [5, 6, 7, 8, 10, 12], [4, 5, 6, 8, 9, 10, 11], [6, 7, 8, 9, 10, 11], [4, 6, 9, 11, 12], [4, 5, 6, 8, 11, 12], [4, 5, 7, 8, 9, 10, 11],
        [4, 6, 7, 9, 10, 12], [4, 5, 6, 7, 8, 10, 12], [5, 6, 7, 9, 10, 12], [4, 6, 7, 8, 9, 10, 11], [7, 8, 9, 10, 12], [5, 6, 7, 8, 9, 10, 11],
        [4, 6, 7, 8, 11, 12], [4, 6, 8, 9, 10, 12], [5, 6, 7, 8, 11, 12], [4, 5, 6, 7, 9, 10, 12], [4, 5, 7, 9, 11, 12], [4, 7, 8, 9, 10, 12],
        [4, 5, 6, 7, 8, 9, 10, 11], [5, 7, 8, 9, 10, 12], [4, 6, 7, 9, 11, 12], [4, 5, 6, 7, 8, 11, 12], [4, 5, 6, 8, 9, 10, 12], [6, 7, 8, 9, 10, 12],
        [7, 8, 9, 11, 12], [6, 7, 10, 11, 12], [4, 5, 7, 8, 9, 10, 12], [4, 6, 8, 9, 11, 12], [4, 5, 7, 10, 11, 12], [4, 5, 6, 7, 9, 11, 12],
        [4, 6, 7, 8, 9, 10, 12], [4, 7, 8, 9, 11, 12], [5, 6, 7, 8, 9, 10, 12], [5, 7, 8, 9, 11, 12], [5, 6, 7, 10, 11, 12], [4, 5, 8, 10, 11, 12],
        [4, 5, 6, 8, 9, 11, 12], [6, 7, 8, 9, 11, 12]
      ],
   by decide +kernel⟩

theorem certified_small_and_medium :
    (∀ n x m : ℕ, n ≤ 150 → 1 < m → 1 < x → OMA.S_oeis_a000041.a n ≠ x ^ m) ∧
    (∀ n : ℕ, 2 < n → n ≠ 6 → n ≤ 200000000000 →
      ∃ (j : ℕ) (b : Fin j → ℕ),
        (∀ i, ∃ k : ℕ, 0 < k ∧ b i = OMA.S_oeis_a000041.a k + 2) ∧
        (∀ i i', i ≠ i' → ¬ b i ∣ b i') ∧
        ∑ i, b i = n) := by
  obtain ⟨spTable, pTable, c2Roots, smallWits, ks82, ws82, baseSubs,
    hsp_cert, hp_rec, hp_c2_cert, hsmall_cert, h82_cert⟩ := exists_certified_tables
  have hsp_eq : ∀ k : ℕ, k < 150 →
      OMA.S_oeis_a000041.signedPentagonal (k + 1) = spTable[k]?.getD 0 := by
    intro k hk
    unfold OMA.S_oeis_a000041.signedPentagonal
    rw [sum_range_eq_list_sum, ← hsp_cert ⟨k, hk⟩]
  have hp_eq : ∀ n : ℕ, n < 151 → OMA.S_oeis_a000041.a n = pTable[n]?.getD 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      rcases n with _ | m
      · rw [hp_rec.1]
        simp [OMA.S_oeis_a000041.a]
      · apply Nat.cast_injective (R := ℤ)
        rw [partition_pentagonal_recurrence (by omega : 1 ≤ m + 1)]
        have hm150 : m < 150 := by omega
        have hcongr :
            ∑ k ∈ Finset.range (m + 1),
              OMA.S_oeis_a000041.signedPentagonal (k + 1) *
                (OMA.S_oeis_a000041.a (m + 1 - 1 - k) : ℤ) =
            ∑ k ∈ Finset.range (m + 1),
              spTable[k]?.getD 0 * (pTable[m - k]?.getD 0 : ℤ) := by
          refine Finset.sum_congr rfl fun k hk => ?_
          rw [Finset.mem_range] at hk
          have hsub : m + 1 - 1 - k = m - k := by omega
          rw [hsub, hsp_eq k (by omega), ih (m - k) (by omega) (by omega)]
        rw [hcongr, sum_range_eq_list_sum, ← hp_rec.2.2 ⟨m, hm150⟩]
  let w : ℕ → ℕ := fun k => pTable[k]?.getD 0 + 2
  have hw_eq : ∀ ks : List ℕ, (∀ k ∈ ks, 1 ≤ k ∧ k ≤ 150) →
      (ks.map fun k => OMA.S_oeis_a000041.a k + 2) = ks.map w := by
    intro ks hks
    refine List.map_congr_left fun k hk => ?_
    have hk' := hks k hk
    dsimp [w]
    rw [hp_eq k (by omega)]
  refine ⟨?_, ?_⟩
  · intro n x m hn150 hm hx
    refine ne_pow_of_ne_prime_pow ?_ x m hm hx
    intro p y hp hy
    rw [hp_eq n (by omega)]
    by_cases hn2 : n < 2
    · have hv1 : pTable[n]?.getD 0 = 1 := by
        rcases n with _ | _ | _
        · exact hp_rec.1
        · exact hp_rec.2.1
        · omega
      rw [hv1]
      have hp2 : 2 ≤ p := hp.two_le
      have hge4 : 4 ≤ y ^ p := calc
        4 = 2 ^ 2 := rfl
        _ ≤ 2 ^ p := Nat.pow_le_pow_right (by decide) hp2
        _ ≤ y ^ p := Nat.pow_le_pow_left (by omega) p
      omega
    · have hidx : n - 2 < 149 := by omega
      have hsub2 : n - 2 + 2 = n := by omega
      by_cases hp36 : 36 ≤ p
      · have hlt := hp_c2_cert.1 ⟨n - 2, hidx⟩
        dsimp only at hlt
        rw [hsub2] at hlt
        have hge : 2 ^ 36 ≤ y ^ p := calc
          2 ^ 36 ≤ 2 ^ p := Nat.pow_le_pow_right (by decide) hp36
          _ ≤ y ^ p := Nat.pow_le_pow_left (by omega) p
        omega
      · obtain ⟨j, hj⟩ := prime_lt_36_mem hp (by omega)
        have hrt := hp_c2_cert.2 ⟨n - 2, hidx⟩ j
        dsimp only at hrt
        rw [hsub2, hj] at hrt
        set r := (c2Roots[n - 2]?.getD [])[j.val]?.getD 0
        rcases le_or_gt y r with hle | hgt
        · have hpow : y ^ p ≤ r ^ p := Nat.pow_le_pow_left hle p
          have := hrt.1
          omega
        · have hpow : (r + 1) ^ p ≤ y ^ p := Nat.pow_le_pow_left (by omega) p
          have := hrt.2
          omega
  · intro n hn2 hn6 hnmax
    by_cases hn60 : n < 60
    · rcases hsmall_cert ⟨n, hn60⟩ with hlt | heq | hok
      · dsimp only at hlt
        omega
      · dsimp only at heq
        exact absurd heq hn6
      · dsimp only at hok
        let ks := smallWits[n]?.getD []
        have hmap := hw_eq ks hok.1
        refine witness_of_ks ks (fun k hk => by have := (hok.1 k hk).1; omega) ?_ ?_
        · rw [hmap]
          exact hok.2.1
        · rw [hmap]
          exact hok.2.2
    · let pref9 := ks82.take 9
      let rest73 := ks82.drop 9
      have hws_eq : ks82.map w = ws82 := h82_cert.2.1
      have hpref_sum : (pref9.map w).sum = 283 := by
        dsimp only [pref9]
        rw [List.map_take, hws_eq]
        exact h82_cert.2.2.2.1
      have hbase : ∀ u, 60 ≤ u → u ≤ (pref9.map w).sum - 60 →
          ∃ sub, List.Sublist sub pref9 ∧ (sub.map w).sum = u := by
        intro u hu1 hu2
        rw [hpref_sum] at hu2
        have hd : u - 60 < 164 := by omega
        have hc := h82_cert.2.2.2.2.2.1 ⟨u - 60, hd⟩
        dsimp only at hc
        have hc2 : ((baseSubs[u - 60]?.getD []).map w).sum = u - 60 + 60 := hc.2
        exact ⟨baseSubs[u - 60]?.getD [], hc.1, by omega⟩
      have hstep : ∀ i : Fin rest73.length,
          119 + w rest73[i.val] ≤ ((pref9 ++ rest73.take i.val).map w).sum := by
        intro i
        have hi := h82_cert.2.2.2.2.2.2 i
        have hmap_eq : (pref9 ++ rest73.take i.val).map w =
            ws82.take 9 ++ (ws82.drop 9).take i.val := by
          simp [pref9, rest73, ← hws_eq]
        rw [hmap_eq]
        exact hi
      have hext := sublist_interval_extend rest73 pref9 hbase hstep
      rw [List.take_append_drop 9 ks82, hws_eq] at hext
      have hsum82 := h82_cert.2.2.2.2.1
      obtain ⟨sub, hsub, hsum⟩ := hext n (by omega) (by omega)
      have hsub_ks : ∀ k ∈ sub, 1 ≤ k ∧ k ≤ 150 :=
        fun k hk => h82_cert.1 k (hsub.subset hk)
      have hmap := hw_eq sub hsub_ks
      refine witness_of_ks sub (fun k hk => by have := (hsub_ks k hk).1; omega) ?_ ?_
      · rw [hmap]
        have hanti : (ks82.map w).Pairwise (fun x y => ¬ x ∣ y ∧ ¬ y ∣ x) := by
          rw [hws_eq]
          exact h82_cert.2.2.1
        exact hanti.sublist (hsub.map w)
      · rw [hmap]
        exact hsum

/-- Zhi-Wei Sun's prime-exponent conjecture on partition numbers beyond the certified prefix. -/
def H1 : Prop := ∀ n y p : ℕ, 150 < n → Nat.Prime p → 1 < y →
  OMA.S_oeis_a000041.a n ≠ y ^ p

/-- Zhi-Wei Sun's pairwise non-dividing representation conjecture beyond two hundred billion. -/
def H2 : Prop := ∀ n : ℕ, 200000000000 < n →
  ∃ (j : ℕ) (b : Fin j → ℕ),
    (∀ i, ∃ k : ℕ, 0 < k ∧ b i = OMA.S_oeis_a000041.a k + 2) ∧
    (∀ i i', i ≠ i' → ¬ b i ∣ b i') ∧
    ∑ i, b i = n

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a000041.main := by
  intro h1 h2
  obtain ⟨hc2_small, hc3_small⟩ := certified_small_and_medium
  refine ⟨conjecture_1, ?_, ?_⟩
  · intro n x m hm hx
    by_cases hn : n ≤ 150
    · exact hc2_small n x m hn hm hx
    · exact ne_pow_of_ne_prime_pow (fun p y hp hy => h1 n y p (by omega) hp hy) x m hm hx
  · intro n hn2 hn6
    by_cases hn : n ≤ 200000000000
    · exact hc3_small n hn2 hn6 hn
    · exact h2 n (by omega)

end OMA.R_oeis_a000041_R1
