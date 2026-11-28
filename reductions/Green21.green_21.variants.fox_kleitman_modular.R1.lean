import FormalConjectures.GreensOpenProblems.«21»
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement

/-!
Reduction `Green21.green_21.variants.fox_kleitman_modular.R1` of the modular Fox-Kleitman
conjecture (`Green21.green_21.variants.fox_kleitman_modular`).

Unconditionally proved in-file:
1. Prefix-sum pigeonhole bound `k < p` whenever `a : Fin k -> Z` avoids non-empty zero-sum
   subsets modulo `p`.
2. Complete solution for `k = 1` (`1` colour) and `k = 2` (`3` colours, via finite-abelian
   cyclic-coset `3`-colouring `tri_col`) for every prime `p`.
3. Normalization of any admissible tuple `a : Fin k -> Z` to a unit tuple `u : Fin k -> (ZMod p)ˣ`
   with `u 0 = 1` and no non-empty zero-sum subset.
4. Complete solution for all small primes `p <= k^2` (using at most `k^2` colours via injective
   canonical representatives) and all `L^1`-small-scaling tuples `∃ m : (ZMod p)ˣ, ∑ i, (m * u i).val <= k^2`
   (including all constant tuples `(c, ..., c)` in `k` colours) via modular interval partitioning.

Remaining open cores:
- `H1`: Arity `k = 3` (`11 <= p`, normalized `u 0 = 1`, no scaling into `L^1 <= 9`).
- `H2`: Higher arity `k >= 4` (`k^2 < p`, normalized `u 0 = 1`, no scaling into `L^1 <= k^2`).
-/

-- Reduction Green21.green_21.variants.fox_kleitman_modular.R1 of Ben Green's Open Problem 21 — fox kleitman modular
-- Credit: @paynebrowning

namespace OMA.R_Green21_green_21_variants_fox_kleitman_modular_R1

def H1 : Prop :=
  ∃ C : ℕ, ∀ (p : ℕ), p.Prime → 9 < p →
    ∀ u : Fin 3 → (ZMod p)ˣ, u 0 = 1 →
      (∀ I : Finset (Fin 3), I.Nonempty → ∑ i ∈ I, (u i : ZMod p) ≠ 0) →
      (∀ m : (ZMod p)ˣ, 9 < ∑ i : Fin 3, ((m * u i : (ZMod p)ˣ) : ZMod p).val) →
      ∃ col : (ZMod p)ˣ → Fin C, ∀ x : Fin 3 → (ZMod p)ˣ,
        (∀ i j, col (x i) = col (x j)) → ∑ i, (u i : ZMod p) * (x i : ZMod p) ≠ 0

def H2 : Prop :=
  ∃ f : ℕ → ℕ, ∀ (k p : ℕ) (hk : 4 ≤ k), p.Prime → k ^ 2 < p →
    ∀ u : Fin k → (ZMod p)ˣ, u ⟨0, Nat.lt_of_lt_of_le (by norm_num) hk⟩ = 1 →
      (∀ I : Finset (Fin k), I.Nonempty → ∑ i ∈ I, (u i : ZMod p) ≠ 0) →
      (∀ m : (ZMod p)ˣ, k ^ 2 < ∑ i : Fin k, ((m * u i : (ZMod p)ˣ) : ZMod p).val) →
      ∃ col : (ZMod p)ˣ → Fin (f k), ∀ x : Fin k → (ZMod p)ˣ,
        (∀ i j, col (x i) = col (x j)) → ∑ i, (u i : ZMod p) * (x i : ZMod p) ≠ 0

section ReductionProofs

private lemma not_dvd_of_no_zero_subset {k p : ℕ} {a : Fin k → ℤ}
    (ha : ∀ I : Finset (Fin k), (p : ℤ) ∣ ∑ i ∈ I, a i → I = ∅) (i : Fin k) :
    ¬ (p : ℤ) ∣ a i := by
  intro hd
  have hsing : ({i} : Finset (Fin k)) = ∅ := ha {i} (by simpa using hd)
  exact Finset.singleton_ne_empty i hsing

private lemma isUnit_of_not_dvd_prime {p : ℕ} (hp : p.Prime) {z : ℤ}
    (hz : ¬ (p : ℤ) ∣ z) : IsUnit (z : ZMod p) := by
  have : Fact p.Prime := ⟨hp⟩
  refine isUnit_iff_ne_zero.mpr ?_
  intro h0
  exact hz ((ZMod.intCast_zmod_eq_zero_iff_dvd z p).mp h0)

private lemma k_lt_prime_of_no_zero_subset {k p : ℕ} (hp : p.Prime)
    {a : Fin k → ℤ} (ha : ∀ I : Finset (Fin k), (p : ℤ) ∣ ∑ i ∈ I, a i → I = ∅) :
    k < p := by
  by_contra hle
  have hpk : p ≤ k := Nat.le_of_not_lt hle
  let S : Fin (k + 1) → ZMod p := fun j =>
    ∑ i ∈ Finset.univ.filter (fun i : Fin k => i.val < j.val), (a i : ZMod p)
  have : NeZero p := ⟨hp.ne_zero⟩
  have hcard : Fintype.card (ZMod p) < Fintype.card (Fin (k + 1)) := by
    rw [ZMod.card, Fintype.card_fin]
    omega
  obtain ⟨j1, j2, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt S hcard
  have hval_ne : j1.val ≠ j2.val := fun h => hne (Fin.ext h)
  wlog hlt : j1.val < j2.val generalizing j1 j2
  · exact this j2 j1 hne.symm heq.symm hval_ne.symm (by omega)
  let I : Finset (Fin k) := Finset.univ.filter (fun i : Fin k => j1.val ≤ i.val ∧ i.val < j2.val)
  have hI_nonempty : I.Nonempty := by
    refine ⟨⟨j1.val, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hlt⟩⟩
  have hsplit : Finset.univ.filter (fun i : Fin k => i.val < j2.val) =
      Finset.univ.filter (fun i : Fin k => i.val < j1.val) ∪ I := by
    ext i
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, I]
    omega
  have hdisj : Disjoint (Finset.univ.filter (fun i : Fin k => i.val < j1.val)) I := by
    rw [Finset.disjoint_left]
    intro i hi1 hi2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, I] at hi1 hi2
    omega
  have hsum_eq : (∑ i ∈ I, (a i : ZMod p)) = S j2 - S j1 := by
    dsimp [S]
    rw [hsplit, Finset.sum_union hdisj, add_sub_cancel_left]
  have hsum_zero : ((∑ i ∈ I, a i : ℤ) : ZMod p) = 0 := by
    push_cast
    rw [hsum_eq, heq, sub_self]
  have hdvd : (p : ℤ) ∣ ∑ i ∈ I, a i := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hsum_zero
  exact hI_nonempty.ne_empty (ha I hdvd)

private lemma tri_col {G : Type*} [CommGroup G] [Finite G] (g : G) (hg : g ≠ 1) :
    ∃ χ : G → Fin 3, ∀ u, χ (g * u) ≠ χ u := by
  classical
  have hfin : IsOfFinOrder g := isOfFinOrder_of_finite g
  have hn : 2 ≤ orderOf g := by
    have h0 : 0 < orderOf g := hfin.orderOf_pos
    have h1 : orderOf g ≠ 1 := by rwa [Ne, orderOf_eq_one_iff]
    omega
  let r : G → G := fun u => (QuotientGroup.mk u : G ⧸ Subgroup.zpowers g).out
  have hr : ∀ u, ∃ j : ℕ, g ^ j * r u = u := by
    intro u
    have h1 : (QuotientGroup.mk (r u) : G ⧸ Subgroup.zpowers g) = QuotientGroup.mk u :=
      QuotientGroup.out_eq' _
    rw [QuotientGroup.eq] at h1
    obtain ⟨j, hj⟩ := (mem_powers_iff_mem_zpowers).mpr h1
    refine ⟨j, ?_⟩
    change g ^ j = _ at hj
    rw [hj, mul_comm, mul_inv_cancel_left]
  have hrg : ∀ u, r (g * u) = r u := by
    intro u
    have hq : (QuotientGroup.mk (g * u) : G ⧸ Subgroup.zpowers g) = QuotientGroup.mk u := by
      rw [QuotientGroup.eq]
      have hid : (g * u)⁻¹ * u = g⁻¹ := by
        rw [mul_inv_rev, mul_assoc, mul_comm g⁻¹ u, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [hid]
      exact Subgroup.inv_mem _ (Subgroup.mem_zpowers g)
    simp only [r, hq]
  let j : G → ℕ := fun u => Nat.find (hr u)
  have hj : ∀ u, g ^ j u * r u = u := fun u => Nat.find_spec (hr u)
  have hjmin : ∀ u m, g ^ m * r u = u → j u ≤ m := fun u m h => Nat.find_min' (hr u) h
  have hjlt : ∀ u, j u < orderOf g := by
    intro u
    by_contra hcon
    have hcon' : orderOf g ≤ j u := by omega
    have h1 : g ^ (j u - orderOf g) * r u = u := by
      have hju := hj u
      rw [← Nat.sub_add_cancel hcon', pow_add, pow_orderOf_eq_one, mul_one] at hju
      exact hju
    have hle := hjmin u _ h1
    have h0 : 0 < orderOf g := hfin.orderOf_pos
    omega
  let χ : G → Fin 3 := fun u => if j u = orderOf g - 1 then 2 else ⟨j u % 2, by omega⟩
  refine ⟨χ, fun u => ?_⟩
  have hu := hjlt u
  by_cases hA : j u + 1 < orderOf g
  · have e1 : g ^ (j u + 1) * r (g * u) = g * u := by
      rw [hrg, pow_succ, mul_comm (g ^ j u) g, mul_assoc, hj]
    have e2 : g ^ j (g * u) * r u = g ^ (j u + 1) * r u := by
      have hgu := hj (g * u)
      rw [hrg] at hgu
      rw [hgu, ← hrg u, e1]
    have e3 : g ^ j (g * u) = g ^ (j u + 1) := mul_right_cancel e2
    have e4 : j (g * u) = j u + 1 := pow_injOn_Iio_orderOf (hjlt _) hA e3
    simp only [χ, e4]
    split_ifs with h1 h2 h2
    · omega
    · simp [Fin.ext_iff]; omega
    · simp [Fin.ext_iff]; omega
    · simp only [ne_eq, Fin.mk.injEq]; omega
  · have hB : j u + 1 = orderOf g := by omega
    have e1 : g * u = r u := by
      have hju := hj u
      calc g * u = g * (g ^ j u * r u) := by rw [hju]
        _ = g ^ (j u + 1) * r u := by rw [pow_succ', mul_assoc]
        _ = r u := by rw [hB, pow_orderOf_eq_one, one_mul]
    have e2 : j (g * u) = 0 := by
      have hle := hjmin (g * u) 0 (by rw [pow_zero, one_mul, hrg, e1])
      omega
    simp only [χ, e2]
    split_ifs with h1 h2
    · omega
    · omega
    · simp [Fin.ext_iff]
    · omega

private lemma solve_k_one {p : ℕ} (hp : p.Prime) (a : Fin 1 → ℤ)
    (ha : ∀ I : Finset (Fin 1), (p : ℤ) ∣ ∑ i ∈ I, a i → I = ∅) :
    ∃ col : (ZMod p)ˣ → Fin 1, ∀ x : Fin 1 → (ZMod p)ˣ,
      (∀ i j, col (x i) = col (x j)) → ∑ i, (a i : ZMod p) * (x i : ZMod p) ≠ 0 := by
  have : Fact p.Prime := ⟨hp⟩
  refine ⟨fun _ => 0, fun x _ hsum => ?_⟩
  rw [Fin.sum_univ_one] at hsum
  have ha0 : IsUnit (a 0 : ZMod p) :=
    isUnit_of_not_dvd_prime hp (not_dvd_of_no_zero_subset ha 0)
  have hx0 : IsUnit ((x 0 : ZMod p)) := (x 0).isUnit
  exact (ha0.mul hx0).ne_zero hsum

private lemma solve_k_two {p : ℕ} (hp : p.Prime) (a : Fin 2 → ℤ)
    (ha : ∀ I : Finset (Fin 2), (p : ℤ) ∣ ∑ i ∈ I, a i → I = ∅) :
    ∃ col : (ZMod p)ˣ → Fin 3, ∀ x : Fin 2 → (ZMod p)ˣ,
      (∀ i j, col (x i) = col (x j)) → ∑ i, (a i : ZMod p) * (x i : ZMod p) ≠ 0 := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have ha0 := isUnit_of_not_dvd_prime hp (not_dvd_of_no_zero_subset ha 0)
  have ha1 := isUnit_of_not_dvd_prime hp (not_dvd_of_no_zero_subset ha 1)
  let u0 : (ZMod p)ˣ := ha0.unit
  let u1 : (ZMod p)ˣ := ha1.unit
  have hu0 : (u0 : ZMod p) = a 0 := ha0.unit_spec
  have hu1 : (u1 : ZMod p) = a 1 := ha1.unit_spec
  let g : (ZMod p)ˣ := -(u1 * u0⁻¹)
  have hg : g ≠ 1 := by
    intro hg1
    have hval : ((g : (ZMod p)ˣ) : ZMod p) = 1 := by rw [hg1]; rfl
    simp only [g, Units.val_neg, Units.val_mul] at hval
    have h01 : ((a 0 + a 1 : ℤ) : ZMod p) = 0 := by
      push_cast
      rw [← hu0, ← hu1]
      have hmul : (u0 : ZMod p) * ((u0⁻¹ : (ZMod p)ˣ) : ZMod p) = 1 := Units.mul_inv u0
      linear_combination -(u0 : ZMod p) * hval - (u1 : ZMod p) * hmul
    have hdvd : (p : ℤ) ∣ a 0 + a 1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h01
    have hfull : (Finset.univ : Finset (Fin 2)) = ∅ := by
      refine ha Finset.univ ?_
      simpa [Fin.sum_univ_two] using hdvd
    exact Finset.univ_nonempty.ne_empty hfull
  obtain ⟨χ, hχ⟩ := tri_col g hg
  refine ⟨χ, fun x hcol hsum => ?_⟩
  rw [Fin.sum_univ_two] at hsum
  apply hχ (x 1)
  rw [← hcol 0 1]
  congr 1
  apply Units.ext
  simp only [g, Units.val_neg, Units.val_mul]
  rw [← hu0, ← hu1] at hsum
  have hmul : ((u0⁻¹ : (ZMod p)ˣ) : ZMod p) * (u0 : ZMod p) = 1 := Units.inv_mul u0
  linear_combination -((u0⁻¹ : (ZMod p)ˣ) : ZMod p) * hsum + ((x 0 : (ZMod p)ˣ) : ZMod p) * hmul

private lemma solve_small_prime {k p : ℕ} (hk : 0 < k) (hp : p.Prime) (hle : p ≤ k ^ 2)
    (u : Fin k → (ZMod p)ˣ)
    (hu : ∀ I : Finset (Fin k), I.Nonempty → ∑ i ∈ I, (u i : ZMod p) ≠ 0) :
    ∃ col : (ZMod p)ˣ → Fin (k ^ 2), ∀ x : Fin k → (ZMod p)ˣ,
      (∀ i j, col (x i) = col (x j)) → ∑ i, (u i : ZMod p) * (x i : ZMod p) ≠ 0 := by
  have : NeZero p := ⟨hp.ne_zero⟩
  let col : (ZMod p)ˣ → Fin (k ^ 2) := fun x => ⟨(x : ZMod p).val, lt_of_lt_of_le (ZMod.val_lt _) hle⟩
  refine ⟨col, fun x hcol hsum => ?_⟩
  let i0 : Fin k := ⟨0, hk⟩
  have hx_eq : ∀ i : Fin k, (x i : ZMod p) = (x i0 : ZMod p) := by
    intro i
    have hval : (x i : ZMod p).val = (x i0 : ZMod p).val := by
      have := congrArg Fin.val (hcol i i0)
      simpa [col] using this
    exact ZMod.val_injective p hval
  have hsum' : (∑ i : Fin k, (u i : ZMod p)) * (x i0 : ZMod p) = 0 := by
    rw [Finset.sum_mul]
    convert hsum using 1
    exact Finset.sum_congr rfl fun i _ => by rw [hx_eq i]
  have hu_ne : ∑ i : Fin k, (u i : ZMod p) ≠ 0 := hu Finset.univ ⟨i0, Finset.mem_univ i0⟩
  have hunit : IsUnit ((x i0 : (ZMod p)ˣ) : ZMod p) := (x i0).isUnit
  exact hu_ne ((hunit.mul_left_eq_zero).mp hsum')

private lemma solve_bounded_L1 {k p B : ℕ} (hk : 0 < k) (hp : p.Prime) (hBp : B < p)
    (u : Fin k → (ZMod p)ˣ) (m : (ZMod p)ˣ)
    (hm : ∑ i : Fin k, ((m * u i : (ZMod p)ˣ) : ZMod p).val ≤ B) :
    ∃ col : (ZMod p)ˣ → Fin B, ∀ x : Fin k → (ZMod p)ˣ,
      (∀ i j, col (x i) = col (x j)) → ∑ i, (u i : ZMod p) * (x i : ZMod p) ≠ 0 := by
  have : Fact p.Prime := ⟨hp⟩
  let S : ℕ := ∑ i : Fin k, ((m * u i : (ZMod p)ˣ) : ZMod p).val
  have hb_pos : ∀ i : Fin k, 0 < ((m * u i : (ZMod p)ˣ) : ZMod p).val := by
    intro i
    refine Nat.pos_of_ne_zero fun h0 => ?_
    have hz : ((m * u i : (ZMod p)ˣ) : ZMod p) = 0 := by
      rw [← ZMod.val_eq_zero]
      exact h0
    exact (m * u i).ne_zero hz
  have hS_pos : 0 < S := by
    let i0 : Fin k := ⟨0, hk⟩
    exact lt_of_lt_of_le (hb_pos i0)
      (Finset.single_le_sum (f := fun i => ((m * u i : (ZMod p)ˣ) : ZMod p).val)
        (fun i _ => Nat.zero_le _) (Finset.mem_univ i0))
  have hS_lt_p : S < p := lt_of_le_of_lt hm hBp
  let col : (ZMod p)ˣ → Fin B := fun x =>
    ⟨(S * ((m⁻¹ * x : (ZMod p)ˣ) : ZMod p).val) / p, by
      have h1 : S * ((m⁻¹ * x : (ZMod p)ˣ) : ZMod p).val < p * S := by
        calc S * ((m⁻¹ * x : (ZMod p)ˣ) : ZMod p).val
            < S * p := Nat.mul_lt_mul_of_pos_left (ZMod.val_lt _) hS_pos
          _ = p * S := mul_comm S p
      have h2 : (S * ((m⁻¹ * x : (ZMod p)ˣ) : ZMod p).val) / p < S :=
        Nat.div_lt_of_lt_mul h1
      exact lt_of_lt_of_le h2 hm⟩
  refine ⟨col, fun x hcol hsum => ?_⟩
  let i0 : Fin k := ⟨0, hk⟩
  let c : ℕ := (S * ((m⁻¹ * x i0 : (ZMod p)ˣ) : ZMod p).val) / p
  have hy_pos : ∀ i : Fin k, 0 < ((m⁻¹ * x i : (ZMod p)ˣ) : ZMod p).val := by
    intro i
    refine Nat.pos_of_ne_zero fun h0 => ?_
    have hz : ((m⁻¹ * x i : (ZMod p)ˣ) : ZMod p) = 0 := by
      rw [← ZMod.val_eq_zero]
      exact h0
    exact (m⁻¹ * x i).ne_zero hz
  have hc_bounds : ∀ i : Fin k,
      c * p < S * ((m⁻¹ * x i : (ZMod p)ˣ) : ZMod p).val ∧
      S * ((m⁻¹ * x i : (ZMod p)ˣ) : ZMod p).val < (c + 1) * p := by
    intro i
    have hci : (S * ((m⁻¹ * x i : (ZMod p)ˣ) : ZMod p).val) / p = c :=
      congrArg Fin.val (hcol i i0)
    have hdiv_le : c * p ≤ S * ((m⁻¹ * x i : (ZMod p)ˣ) : ZMod p).val := by
      rw [← hci]
      exact Nat.div_mul_le_self _ p
    have hlt_succ : S * ((m⁻¹ * x i : (ZMod p)ˣ) : ZMod p).val < (c + 1) * p := by
      have hraw := Nat.lt_div_mul_add hp.pos (a := S * ((m⁻¹ * x i : (ZMod p)ˣ) : ZMod p).val)
      rw [hci] at hraw
      nlinarith
    have hne : c * p ≠ S * ((m⁻¹ * x i : (ZMod p)ˣ) : ZMod p).val := by
      intro heq
      rcases Nat.eq_zero_or_pos c with hc0 | hcpos
      · rw [hc0, zero_mul] at heq
        have hprod_pos : 0 < S * ((m⁻¹ * x i : (ZMod p)ˣ) : ZMod p).val :=
          Nat.mul_pos hS_pos (hy_pos i)
        omega
      · have hp_dvd : p ∣ S * ((m⁻¹ * x i : (ZMod p)ˣ) : ZMod p).val := ⟨c, by linarith⟩
        rcases hp.dvd_mul.mp hp_dvd with hpS | hpY
        · have := Nat.le_of_dvd hS_pos hpS; omega
        · have := Nat.le_of_dvd (hy_pos i) hpY
          have hylt := ZMod.val_lt ((m⁻¹ * x i : (ZMod p)ˣ) : ZMod p)
          omega
    exact ⟨lt_of_le_of_ne hdiv_le hne, hlt_succ⟩
  have hsum_lo : S * (c * p) < S * ∑ i : Fin k,
      ((m * u i : (ZMod p)ˣ) : ZMod p).val * ((m⁻¹ * x i : (ZMod p)ˣ) : ZMod p).val := by
    have hterm : ∀ i ∈ (Finset.univ : Finset (Fin k)),
        ((m * u i : (ZMod p)ˣ) : ZMod p).val * (c * p) <
        ((m * u i : (ZMod p)ˣ) : ZMod p).val * (S * ((m⁻¹ * x i : (ZMod p)ˣ) : ZMod p).val) :=
      fun i _ => Nat.mul_lt_mul_of_pos_left (hc_bounds i).1 (hb_pos i)
    have hsum_lt := Finset.sum_lt_sum_of_nonempty ⟨i0, Finset.mem_univ i0⟩ hterm
    rw [← Finset.sum_mul] at hsum_lt
    have hrhs : (∑ i : Fin k, ((m * u i : (ZMod p)ˣ) : ZMod p).val *
        (S * ((m⁻¹ * x i : (ZMod p)ˣ) : ZMod p).val)) =
        S * ∑ i : Fin k, ((m * u i : (ZMod p)ˣ) : ZMod p).val *
          ((m⁻¹ * x i : (ZMod p)ˣ) : ZMod p).val := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    change S * (c * p) < _ at hsum_lt
    rw [hrhs] at hsum_lt
    exact hsum_lt
  have hsum_hi : S * ∑ i : Fin k,
      ((m * u i : (ZMod p)ˣ) : ZMod p).val * ((m⁻¹ * x i : (ZMod p)ˣ) : ZMod p).val <
      S * ((c + 1) * p) := by
    have hterm : ∀ i ∈ (Finset.univ : Finset (Fin k)),
        ((m * u i : (ZMod p)ˣ) : ZMod p).val * (S * ((m⁻¹ * x i : (ZMod p)ˣ) : ZMod p).val) <
        ((m * u i : (ZMod p)ˣ) : ZMod p).val * ((c + 1) * p) :=
      fun i _ => Nat.mul_lt_mul_of_pos_left (hc_bounds i).2 (hb_pos i)
    have hsum_lt := Finset.sum_lt_sum_of_nonempty ⟨i0, Finset.mem_univ i0⟩ hterm
    rw [← Finset.sum_mul] at hsum_lt
    have hlhs : (∑ i : Fin k, ((m * u i : (ZMod p)ˣ) : ZMod p).val *
        (S * ((m⁻¹ * x i : (ZMod p)ˣ) : ZMod p).val)) =
        S * ∑ i : Fin k, ((m * u i : (ZMod p)ˣ) : ZMod p).val *
          ((m⁻¹ * x i : (ZMod p)ˣ) : ZMod p).val := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    change _ < S * ((c + 1) * p) at hsum_lt
    rw [hlhs] at hsum_lt
    exact hsum_lt
  have hlt1 : c * p < ∑ i : Fin k,
      ((m * u i : (ZMod p)ˣ) : ZMod p).val * ((m⁻¹ * x i : (ZMod p)ˣ) : ZMod p).val :=
    Nat.lt_of_mul_lt_mul_left hsum_lo
  have hlt2 : ∑ i : Fin k,
      ((m * u i : (ZMod p)ˣ) : ZMod p).val * ((m⁻¹ * x i : (ZMod p)ˣ) : ZMod p).val < (c + 1) * p :=
    Nat.lt_of_mul_lt_mul_left hsum_hi
  have hzmod : ((∑ i : Fin k,
      ((m * u i : (ZMod p)ˣ) : ZMod p).val * ((m⁻¹ * x i : (ZMod p)ˣ) : ZMod p).val : ℕ) : ZMod p) = 0 := by
    push_cast
    simp only [ZMod.natCast_zmod_val]
    have hminv : (m : ZMod p) * (m : ZMod p)⁻¹ = 1 := by
      rw [← Units.val_inv_eq_inv_val, Units.mul_inv]
    have hterm : ∀ i : Fin k,
        (m : ZMod p) * (u i : ZMod p) * ((m : ZMod p)⁻¹ * (x i : ZMod p)) =
        ((m : ZMod p) * (m : ZMod p)⁻¹) * ((u i : ZMod p) * (x i : ZMod p)) := fun i => by ring
    rw [Finset.sum_congr rfl fun i _ => hterm i, ← Finset.mul_sum, hminv, hsum, mul_zero]
  obtain ⟨q, hq⟩ := (ZMod.natCast_eq_zero_iff _ p).mp hzmod
  rw [hq] at hlt1 hlt2
  have hq_lo : c < q := by nlinarith [hp.pos]
  have hq_hi : q < c + 1 := by nlinarith [hp.pos]
  omega

private lemma solve_constant_coeffs {k p : ℕ} (hk : 0 < k) (hp : p.Prime)
    (a : Fin k → ℤ) (ha : ∀ I : Finset (Fin k), (p : ℤ) ∣ ∑ i ∈ I, a i → I = ∅)
    (hconst : ∀ i j : Fin k, (a i : ZMod p) = (a j : ZMod p)) :
    ∃ col : (ZMod p)ˣ → Fin k, ∀ x : Fin k → (ZMod p)ˣ,
      (∀ i j, col (x i) = col (x j)) → ∑ i, (a i : ZMod p) * (x i : ZMod p) ≠ 0 := by
  have hkp : k < p := k_lt_prime_of_no_zero_subset hp ha
  have : Fact p.Prime := ⟨hp⟩
  have hunit0 : IsUnit (a ⟨0, hk⟩ : ZMod p) :=
    isUnit_of_not_dvd_prime hp (not_dvd_of_no_zero_subset ha ⟨0, hk⟩)
  let c : (ZMod p)ˣ := hunit0.unit
  have hc : (c : ZMod p) = a ⟨0, hk⟩ := hunit0.unit_spec
  let u : Fin k → (ZMod p)ˣ := fun _ => 1
  have hm : ∑ i : Fin k, ((1 * u i : (ZMod p)ˣ) : ZMod p).val ≤ k := by
    simp [u, ZMod.val_one]
  obtain ⟨col, hcol⟩ := solve_bounded_L1 hk hp hkp u 1 hm
  refine ⟨col, fun x hmon hsum => ?_⟩
  apply hcol x hmon
  have hsum' : (c : ZMod p) * ∑ i : Fin k, (u i : ZMod p) * (x i : ZMod p) = 0 := by
    rw [Finset.mul_sum]
    convert hsum using 1
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [u, Units.val_one, one_mul, hc, hconst ⟨0, hk⟩ i]
  exact (c.isUnit.mul_right_eq_zero).mp hsum'

private lemma normalize_units {k p : ℕ} (hk : 0 < k) (hp : p.Prime)
    (a : Fin k → ℤ)
    (ha : ∀ I : Finset (Fin k), (p : ℤ) ∣ ∑ i ∈ I, a i → I = ∅) :
    ∃ (c : (ZMod p)ˣ) (u : Fin k → (ZMod p)ˣ),
      u ⟨0, hk⟩ = 1 ∧
      (∀ i : Fin k, (a i : ZMod p) = (c : ZMod p) * (u i : ZMod p)) ∧
      (∀ I : Finset (Fin k), I.Nonempty → ∑ i ∈ I, (u i : ZMod p) ≠ 0) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have hunit : ∀ i : Fin k, IsUnit (a i : ZMod p) :=
    fun i => isUnit_of_not_dvd_prime hp (not_dvd_of_no_zero_subset ha i)
  let c : (ZMod p)ˣ := (hunit ⟨0, hk⟩).unit
  let u : Fin k → (ZMod p)ˣ := fun i => c⁻¹ * (hunit i).unit
  refine ⟨c, u, ?_, ?_, ?_⟩
  · exact inv_mul_cancel c
  · intro i
    have hci : (c : ZMod p) * (u i : ZMod p) = ((hunit i).unit : ZMod p) := by
      simp only [u, Units.val_mul, ← mul_assoc, Units.mul_inv, one_mul]
    rw [hci, IsUnit.unit_spec]
  · intro I hIne hsum
    have hsum_a : ((∑ i ∈ I, a i : ℤ) : ZMod p) = 0 := by
      push_cast
      have hterm : ∀ i ∈ I, (a i : ZMod p) = (c : ZMod p) * (u i : ZMod p) := fun i _ => by
        simp only [u, Units.val_mul, ← mul_assoc, Units.mul_inv, one_mul, IsUnit.unit_spec]
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hsum, mul_zero]
    have hdvd := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hsum_a
    exact hIne.ne_empty (ha I hdvd)

end ReductionProofs

theorem main : H1 → H2 → type_of% @Green21.green_21.variants.fox_kleitman_modular := by
  rintro ⟨C, hH1⟩ ⟨f2, hH2⟩
  refine ⟨fun k => if k = 1 then 1 else if k = 2 then 3 else if k = 3 then max 9 C else max (k ^ 2) (f2 k), ?_⟩
  intro k p hk hp a ha
  rcases eq_or_ne k 1 with rfl | hk1
  · simpa using solve_k_one hp a ha
  rcases eq_or_ne k 2 with rfl | hk2
  · simpa using solve_k_two hp a ha
  obtain ⟨c, u, hu0, hcu, hu_ne⟩ := normalize_units hk hp a ha
  have hcol_cast : ∀ {n m : ℕ} (hnm : n ≤ m),
      (∃ col : (ZMod p)ˣ → Fin n, ∀ x : Fin k → (ZMod p)ˣ,
        (∀ i j, col (x i) = col (x j)) → ∑ i, (u i : ZMod p) * (x i : ZMod p) ≠ 0) →
      ∃ col : (ZMod p)ˣ → Fin m, ∀ x : Fin k → (ZMod p)ˣ,
        (∀ i j, col (x i) = col (x j)) → ∑ i, (a i : ZMod p) * (x i : ZMod p) ≠ 0 := by
    intro n m hnm ⟨col, hcol⟩
    refine ⟨fun x => Fin.castLE hnm (col x), fun x hmon hsum => ?_⟩
    apply hcol x (fun i j => Fin.castLE_injective hnm (hmon i j))
    have hsum' : (c : ZMod p) * ∑ i, (u i : ZMod p) * (x i : ZMod p) = 0 := by
      rw [Finset.mul_sum]
      convert hsum using 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hcu i, mul_assoc]
    exact (c.isUnit.mul_right_eq_zero).mp hsum'
  by_cases hpk2 : p ≤ k ^ 2
  · have hsol := solve_small_prime hk hp hpk2 u hu_ne
    rcases eq_or_ne k 3 with rfl | hk3
    · exact hcol_cast (show 3 ^ 2 ≤ _ from by simp) hsol
    · exact hcol_cast (show k ^ 2 ≤ _ from by dsimp only; rw [if_neg hk1, if_neg hk2, if_neg hk3]; exact le_max_left _ _) hsol
  · have hgt : k ^ 2 < p := Nat.lt_of_not_le hpk2
    by_cases hm : ∃ m : (ZMod p)ˣ, ∑ i : Fin k, ((m * u i : (ZMod p)ˣ) : ZMod p).val ≤ k ^ 2
    · obtain ⟨m, hm⟩ := hm
      have hsol := solve_bounded_L1 hk hp hgt u m hm
      rcases eq_or_ne k 3 with rfl | hk3
      · exact hcol_cast (show 3 ^ 2 ≤ _ from by simp) hsol
      · exact hcol_cast (show k ^ 2 ≤ _ from by dsimp only; rw [if_neg hk1, if_neg hk2, if_neg hk3]; exact le_max_left _ _) hsol
    · push Not at hm
      rcases eq_or_ne k 3 with rfl | hk3
      · exact hcol_cast (show C ≤ _ from by simp) (hH1 p hp hgt u hu0 hu_ne hm)
      · have hk4 : 4 ≤ k := by omega
        exact hcol_cast (show f2 k ≤ _ from by dsimp only; rw [if_neg hk1, if_neg hk2, if_neg hk3]; exact le_max_right _ _)
          (hH2 k p hk4 hp hgt u hu0 hu_ne hm)

end OMA.R_Green21_green_21_variants_fox_kleitman_modular_R1
