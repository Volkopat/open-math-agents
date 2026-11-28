import OMAReductions.R_Erdos243_erdos_243_R1

/-!
# Proof of `Erdos243.erdos_243.R1.H1`

Constructs the positive integer tail sequences `c` and `d` from the rational tails
`R m = S - ∑_{i < m} 1 / a i` (shifted by `s = 1` so `a (n + 1) ≥ 1`), and proves
`c (n + 1) / c n → 1` from `a n / a (n - 1) ^ 2 → 1` via a geometric tail bound.
-/

-- Step Erdos243.erdos_243.R1.H1: hypothesis H1 of reduction Erdos243.erdos_243.R1
-- Credit: @KevinBigham

namespace Erdos243R1H1

open Filter Finset
open scoped Topology

private lemma hasSum_rat_cast_real {f : ℕ → ℚ} {S : ℚ} (h : HasSum f S) :
    HasSum (fun n ↦ (f n : ℝ)) (S : ℝ) := by
  have hiso : Isometry (Rat.cast : ℚ → ℝ) :=
    isometry_iff_dist_eq.mpr fun x y => by
      rw [Real.dist_eq, Rat.dist_eq]
  have ht : Tendsto (fun s : Finset ℕ ↦ ((∑ i ∈ s, f i : ℚ) : ℝ)) atTop (𝓝 (S : ℝ)) :=
    (hiso.continuous.tendsto S).comp h
  simpa [HasSum, Rat.cast_sum] using ht

private lemma strictMono_pos_of_pos {a : ℕ → ℕ} (ha : StrictMono a) {m : ℕ} (hm : 1 ≤ m) :
    0 < a m := by
  have h : m ≤ a m := ha.id_le m
  omega

private lemma tail_hasSum {a : ℕ → ℕ} {S : ℚ}
    (hSR : HasSum (fun n ↦ (1 : ℝ) / a n) (S : ℝ)) (m : ℕ) :
    HasSum (fun k ↦ (1 : ℝ) / a (k + m))
      (((S - ∑ i ∈ range m, (1 : ℚ) / a i : ℚ) : ℝ)) := by
  have h := (hasSum_nat_add_iff' m).mpr hSR
  have heq : (((S - ∑ i ∈ range m, (1 : ℚ) / a i : ℚ) : ℝ)) =
      (S : ℝ) - ∑ i ∈ range m, (1 : ℝ) / a i := by
    rw [Rat.cast_sub, Rat.cast_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Rat.cast_div, Rat.cast_one, Rat.cast_natCast]
  rw [heq]
  exact h

private lemma tail_pos {a : ℕ → ℕ} (ha : StrictMono a) {S : ℚ}
    (hSR : HasSum (fun n ↦ (1 : ℝ) / a n) (S : ℝ)) {m : ℕ} (hm : 1 ≤ m) :
    0 < S - ∑ i ∈ range m, (1 : ℚ) / a i := by
  have hRm := tail_hasSum hSR m
  have hnonneg : ∀ k : ℕ, 0 ≤ (1 : ℝ) / a (k + m) := fun k => by positivity
  have hle : (1 : ℝ) / a (0 + m) ≤ ((S - ∑ i ∈ range m, (1 : ℚ) / a i : ℚ) : ℝ) := by
    rw [← hRm.tsum_eq]
    exact hRm.summable.le_tsum 0 (fun k _ => hnonneg k)
  have hpos : (0 : ℝ) < (1 : ℝ) / a (0 + m) := by
    have ham : 0 < a (0 + m) := strictMono_pos_of_pos ha (by omega)
    positivity
  have hRpos : (0 : ℝ) < ((S - ∑ i ∈ range m, (1 : ℚ) / a i : ℚ) : ℝ) :=
    lt_of_lt_of_le hpos hle
  exact_mod_cast hRpos

private lemma tail_step {a : ℕ → ℕ} (S : ℚ) (m : ℕ) :
    (S - ∑ i ∈ range m, (1 : ℚ) / a i) =
      (1 : ℚ) / a m + (S - ∑ i ∈ range (m + 1), (1 : ℚ) / a i) := by
  rw [Finset.sum_range_succ]
  ring

private lemma geom_lower_bound {a : ℕ → ℕ} {M₀ : ℕ}
    (hstep : ∀ k ≥ M₀, 2 * (a k : ℝ) ≤ (a (k + 1) : ℝ))
    {m : ℕ} (hm : M₀ ≤ m) (j : ℕ) :
    (2 : ℝ) ^ j * (a (m + 1) : ℝ) ≤ (a (m + 1 + j) : ℝ) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hnext := hstep (m + 1 + j) (by omega)
    calc
      (2 : ℝ) ^ (j + 1) * (a (m + 1) : ℝ)
          = 2 * ((2 : ℝ) ^ j * (a (m + 1) : ℝ)) := by ring
      _ ≤ 2 * (a (m + 1 + j) : ℝ) := by linarith
      _ ≤ (a (m + 1 + j + 1) : ℝ) := hnext
      _ = (a (m + 1 + (j + 1)) : ℝ) := by ring_nf

private lemma tendsto_a_mul_tail {a : ℕ → ℕ} (ha : StrictMono a)
    (hlim : Tendsto (fun n ↦ (a n : ℝ) / (a (n - 1) : ℝ) ^ 2) atTop (𝓝 1))
    {S : ℚ} (hSR : HasSum (fun n ↦ (1 : ℝ) / a n) (S : ℝ)) :
    Tendsto (fun m ↦ (a m : ℝ) * ((S - ∑ i ∈ range m, (1 : ℚ) / a i : ℚ) : ℝ)) atTop (𝓝 1) := by
  let R (m : ℕ) : ℚ := S - ∑ i ∈ range m, (1 : ℚ) / a i
  have hshift : Tendsto (fun m ↦ (a (m + 1) : ℝ) / (a m : ℝ) ^ 2) atTop (𝓝 1) := by
    have hcomp := hlim.comp (tendsto_add_atTop_nat 1)
    simpa [Function.comp_def, Nat.add_sub_cancel] using hcomp
  obtain ⟨M₁, hM₁⟩ := Metric.tendsto_atTop.mp hshift (1 / 2) (by norm_num)
  let M₀ := max M₁ 4
  have hhalf : ∀ m ≥ M₀, (1 / 2 : ℝ) * (a m : ℝ) ^ 2 ≤ (a (m + 1) : ℝ) := by
    intro m hm
    have hd := hM₁ m (le_trans (le_max_left _ _) hm)
    rw [Real.dist_eq, abs_lt] at hd
    have ham_pos : (0 : ℝ) < (a m : ℝ) := by
      have : 0 < a m := strictMono_pos_of_pos ha (by omega)
      exact_mod_cast this
    have hsq_pos : (0 : ℝ) < (a m : ℝ) ^ 2 := by positivity
    have hge : (1 / 2 : ℝ) ≤ (a (m + 1) : ℝ) / (a m : ℝ) ^ 2 := by linarith [hd.1]
    exact (le_div_iff₀ hsq_pos).mp hge
  have hdouble : ∀ m ≥ M₀, 2 * (a m : ℝ) ≤ (a (m + 1) : ℝ) := by
    intro m hm
    have h1 := hhalf m hm
    have ham4 : (4 : ℝ) ≤ (a m : ℝ) := by
      have : 4 ≤ a m := le_trans (by omega : 4 ≤ m) (ha.id_le m)
      exact_mod_cast this
    nlinarith
  have hupper : ∀ᶠ m in atTop,
      (a m : ℝ) * (R m : ℝ) ≤ 1 + 4 / (m : ℝ) := by
    refine eventually_atTop.mpr ⟨M₀, fun m hm => ?_⟩
    have hm_pos : (0 : ℝ) < (m : ℝ) := by
      have : 0 < m := by omega
      exact_mod_cast this
    have ham_pos : (0 : ℝ) < (a m : ℝ) := by
      have : 0 < a m := strictMono_pos_of_pos ha (by omega)
      exact_mod_cast this
    have ham1_pos : (0 : ℝ) < (a (m + 1) : ℝ) := by
      have : 0 < a (m + 1) := strictMono_pos_of_pos ha (by omega)
      exact_mod_cast this
    have hRm1 : HasSum (fun j ↦ (1 : ℝ) / a (j + (m + 1))) (R (m + 1) : ℝ) :=
      tail_hasSum hSR (m + 1)
    have hgeom : HasSum (fun j : ℕ ↦ (1 / (a (m + 1) : ℝ)) * ((1 / 2 : ℝ) ^ j))
        ((1 / (a (m + 1) : ℝ)) * 2) := by
      have h2 := hasSum_geometric_two
      simpa using h2.mul_left (1 / (a (m + 1) : ℝ))
    have hterm_le : ∀ j : ℕ,
        (1 : ℝ) / a (j + (m + 1)) ≤ (1 / (a (m + 1) : ℝ)) * ((1 / 2 : ℝ) ^ j) := by
      intro j
      have hgb : (2 : ℝ) ^ j * (a (m + 1) : ℝ) ≤ (a (j + (m + 1)) : ℝ) := by
        simpa [add_comm, add_left_comm, add_assoc] using geom_lower_bound hdouble hm j
      have hpos_lhs : (0 : ℝ) < (2 : ℝ) ^ j * (a (m + 1) : ℝ) := by positivity
      have hinv := one_div_le_one_div_of_le hpos_lhs hgb
      calc
        (1 : ℝ) / a (j + (m + 1)) ≤ 1 / ((2 : ℝ) ^ j * (a (m + 1) : ℝ)) := hinv
        _ = (1 / (a (m + 1) : ℝ)) * ((1 / 2 : ℝ) ^ j) := by
          rw [one_div_pow]
          field_simp
    have hRbound : (R (m + 1) : ℝ) ≤ 2 / (a (m + 1) : ℝ) := by
      calc
        (R (m + 1) : ℝ) ≤ (1 / (a (m + 1) : ℝ)) * 2 := hasSum_le hterm_le hRm1 hgeom
        _ = 2 / (a (m + 1) : ℝ) := by ring
    have hsplit : (R m : ℝ) = (1 : ℝ) / (a m : ℝ) + (R (m + 1) : ℝ) := by
      have hq := tail_step (a := a) S m
      have hr : ((R m : ℚ) : ℝ) = (((1 : ℚ) / a m + R (m + 1) : ℚ) : ℝ) := congrArg Rat.cast hq
      simpa [R] using hr
    have hratio : (a m : ℝ) * (2 / (a (m + 1) : ℝ)) ≤ 4 / (a m : ℝ) := by
      have hh := hhalf m hm
      rw [mul_div_assoc', div_le_div_iff₀ ham1_pos ham_pos]
      nlinarith
    have hmle : (m : ℝ) ≤ (a m : ℝ) := by exact_mod_cast ha.id_le m
    have hdiv_le : 4 / (a m : ℝ) ≤ 4 / (m : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) hm_pos hmle
    calc
      (a m : ℝ) * (R m : ℝ) = (a m : ℝ) * ((1 : ℝ) / (a m : ℝ) + (R (m + 1) : ℝ)) := by
        rw [hsplit]
      _ = 1 + (a m : ℝ) * (R (m + 1) : ℝ) := by
        rw [mul_add, mul_one_div_cancel ham_pos.ne']
      _ ≤ 1 + (a m : ℝ) * (2 / (a (m + 1) : ℝ)) := by
        linarith [mul_le_mul_of_nonneg_left hRbound ham_pos.le]
      _ ≤ 1 + 4 / (a m : ℝ) := by linarith
      _ ≤ 1 + 4 / (m : ℝ) := by linarith
  have hlower : ∀ᶠ m in atTop, (1 : ℝ) ≤ (a m : ℝ) * (R m : ℝ) := by
    refine eventually_atTop.mpr ⟨1, fun m hm => ?_⟩
    have ham_pos : (0 : ℝ) < (a m : ℝ) := by
      have : 0 < a m := strictMono_pos_of_pos ha hm
      exact_mod_cast this
    have hR1 : (0 : ℝ) < (R (m + 1) : ℝ) := by
      exact_mod_cast tail_pos ha hSR (by omega)
    have hsplit : (R m : ℝ) = (1 : ℝ) / (a m : ℝ) + (R (m + 1) : ℝ) := by
      have hq := tail_step (a := a) S m
      have hr : ((R m : ℚ) : ℝ) = (((1 : ℚ) / a m + R (m + 1) : ℚ) : ℝ) := congrArg Rat.cast hq
      simpa [R] using hr
    rw [hsplit, mul_add, mul_one_div_cancel ham_pos.ne']
    nlinarith
  have ht_hi : Tendsto (fun m : ℕ ↦ (1 : ℝ) + 4 / (m : ℝ)) atTop (𝓝 1) := by
    have h0 : Tendsto (fun m : ℕ ↦ (4 : ℝ) / (m : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat 4
    simpa using tendsto_const_nhds.add h0
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht_hi hlower hupper

private def seqD (a : ℕ → ℕ) (d0 : ℕ) : ℕ → ℕ
  | 0 => d0
  | n + 1 => a (n + 1) * seqD a d0 n

private def seqC (a : ℕ → ℕ) (c0 d0 : ℕ) : ℕ → ℕ
  | 0 => c0
  | n + 1 => a (n + 1) * seqC a c0 d0 n - seqD a d0 n

end Erdos243R1H1

theorem OMA.solution : OMA.R_Erdos243_erdos_243_R1.H1 := by
  intro a ha hlim hsum
  obtain ⟨S, hS⟩ := hsum
  have hSR : HasSum (fun n ↦ (1 : ℝ) / a n) (S : ℝ) := by
    simpa [Rat.cast_div, Rat.cast_one, Rat.cast_natCast] using Erdos243R1H1.hasSum_rat_cast_real hS
  let R (m : ℕ) : ℚ := S - ∑ i ∈ Finset.range m, (1 : ℚ) / a i
  have hRpos : ∀ m ≥ 1, 0 < R m := fun m hm => Erdos243R1H1.tail_pos ha hSR hm
  let d : ℕ → ℕ := Erdos243R1H1.seqD a (R 1).den
  let c : ℕ → ℕ := Erdos243R1H1.seqC a (R 1).num.toNat (R 1).den
  have hd_pos : ∀ n, 0 < d n := by
    intro n
    induction n with
    | zero => exact (R 1).den_pos
    | succ n ih =>
      have ha1 : 0 < a (n + 1) := Erdos243R1H1.strictMono_pos_of_pos ha (by omega)
      exact Nat.mul_pos ha1 ih
  have hd_rec : ∀ n, d (n + 1) = a (n + 1) * d n := fun _ => rfl
  have hc_inv : ∀ n, ((c n : ℕ) : ℚ) = ((d n : ℕ) : ℚ) * R (n + 1) ∧ 0 < c n := by
    intro n
    induction n with
    | zero =>
      have hpos1 : 0 < R 1 := hRpos 1 le_rfl
      have hnum_pos : 0 < (R 1).num := Rat.num_pos.mpr hpos1
      have htoNat : ((R 1).num.toNat : ℤ) = (R 1).num := Int.toNat_of_nonneg hnum_pos.le
      have hc0 : ((c 0 : ℕ) : ℚ) = ((d 0 : ℕ) : ℚ) * R 1 := by
        change (((R 1).num.toNat : ℕ) : ℚ) = ((R 1).den : ℚ) * R 1
        have h1 : (((R 1).num.toNat : ℕ) : ℚ) = ((R 1).num : ℚ) := by
          rw [← Int.cast_natCast, htoNat]
        rw [h1]
        have hden : ((R 1).den : ℚ) ≠ 0 := by exact_mod_cast (R 1).den_pos.ne'
        have hnd := Rat.num_div_den (R 1)
        field_simp [hden] at hnd ⊢
        linarith
      exact ⟨hc0, by change 0 < (R 1).num.toNat; omega⟩
    | succ n ih =>
      obtain ⟨hcq, _⟩ := ih
      have ha1_pos : 0 < a (n + 1) := Erdos243R1H1.strictMono_pos_of_pos ha (by omega)
      have ha1_ne : ((a (n + 1) : ℕ) : ℚ) ≠ 0 := by exact_mod_cast ha1_pos.ne'
      have hstep := Erdos243R1H1.tail_step (a := a) S (n + 1)
      have hR2_eq : R (n + 2) = R (n + 1) - (1 : ℚ) / a (n + 1) := by
        change S - ∑ i ∈ Finset.range (n + 2), (1 : ℚ) / a i =
          (S - ∑ i ∈ Finset.range (n + 1), (1 : ℚ) / a i) - (1 : ℚ) / a (n + 1)
        linarith
      have hprod :
          ((d (n + 1) : ℕ) : ℚ) * R (n + 2) =
            ((a (n + 1) : ℕ) : ℚ) * ((c n : ℕ) : ℚ) - ((d n : ℕ) : ℚ) := by
        rw [hd_rec n, Nat.cast_mul, hR2_eq, mul_sub]
        have h1 :
            (((a (n + 1) : ℕ) : ℚ) * ((d n : ℕ) : ℚ)) * R (n + 1) =
              ((a (n + 1) : ℕ) : ℚ) * ((c n : ℕ) : ℚ) := by
          rw [hcq]; ring
        have h2 :
            (((a (n + 1) : ℕ) : ℚ) * ((d n : ℕ) : ℚ)) * ((1 : ℚ) / a (n + 1)) =
              ((d n : ℕ) : ℚ) := by
          field_simp [ha1_ne]
        linarith
      have hprod_pos : 0 < ((d (n + 1) : ℕ) : ℚ) * R (n + 2) :=
        mul_pos (by exact_mod_cast hd_pos (n + 1)) (hRpos (n + 2) (by omega))
      have hlt_q : ((d n : ℕ) : ℚ) < ((a (n + 1) : ℕ) : ℚ) * ((c n : ℕ) : ℚ) := by linarith
      have hlt_nat : d n < a (n + 1) * c n := by exact_mod_cast hlt_q
      have hc1_pos : 0 < c (n + 1) := by
        change 0 < a (n + 1) * c n - d n
        omega
      have hc1_q : ((c (n + 1) : ℕ) : ℚ) = ((d (n + 1) : ℕ) : ℚ) * R (n + 2) := by
        change ((a (n + 1) * c n - d n : ℕ) : ℚ) = _
        rw [Nat.cast_sub hlt_nat.le, Nat.cast_mul, hprod]
      exact ⟨hc1_q, hc1_pos⟩
  have hc_pos : ∀ n, 0 < c n := fun n => (hc_inv n).2
  have hc_rec : ∀ n, c (n + 1) + d n = a (n + 1) * c n := by
    intro n
    have hlt_nat : d n ≤ a (n + 1) * c n := by
      have hpos : 0 < a (n + 1) * c n - d n := hc_pos (n + 1)
      omega
    change (a (n + 1) * c n - d n) + d n = a (n + 1) * c n
    exact Nat.sub_add_cancel hlt_nat
  have haR_lim : Filter.Tendsto (fun m ↦ (a m : ℝ) * (R m : ℝ)) Filter.atTop (nhds 1) :=
    Erdos243R1H1.tendsto_a_mul_tail ha hlim hSR
  have hc_ratio_lim :
      Filter.Tendsto (fun n ↦ (c (n + 1) : ℝ) / (c n : ℝ)) Filter.atTop (nhds 1) := by
    have h1 : Filter.Tendsto (fun n ↦ ((a (n + 2) : ℝ) / (a (n + 1) : ℝ) ^ 2)⁻¹)
        Filter.atTop (nhds (1 : ℝ)⁻¹) := by
      have hcomp := hlim.comp (Filter.tendsto_add_atTop_nat 2)
      have hcomp' : Filter.Tendsto (fun n ↦ (a (n + 2) : ℝ) / (a (n + 1) : ℝ) ^ 2)
          Filter.atTop (nhds 1) := by
        simpa [Function.comp_def, Nat.add_sub_cancel] using hcomp
      exact hcomp'.inv₀ one_ne_zero
    have h2 : Filter.Tendsto (fun n ↦ (a (n + 2) : ℝ) * (R (n + 2) : ℝ))
        Filter.atTop (nhds 1) := haR_lim.comp (Filter.tendsto_add_atTop_nat 2)
    have h3 : Filter.Tendsto (fun n ↦ (a (n + 1) : ℝ) * (R (n + 1) : ℝ))
        Filter.atTop (nhds 1) := haR_lim.comp (Filter.tendsto_add_atTop_nat 1)
    have hprod_lim :
        Filter.Tendsto
          (fun n ↦ ((a (n + 2) : ℝ) / (a (n + 1) : ℝ) ^ 2)⁻¹ *
            (((a (n + 2) : ℝ) * (R (n + 2) : ℝ)) / ((a (n + 1) : ℝ) * (R (n + 1) : ℝ))))
          Filter.atTop (nhds 1) := by
      have hq := h1.mul (h2.div h3 one_ne_zero)
      simpa using hq
    refine hprod_lim.congr fun n => ?_
    have hcn : (c n : ℝ) = (d n : ℝ) * (R (n + 1) : ℝ) := by
      have h := congrArg (fun x : ℚ => (x : ℝ)) (hc_inv n).1
      simpa using h
    have hcn1 : (c (n + 1) : ℝ) = (a (n + 1) : ℝ) * (d n : ℝ) * (R (n + 2) : ℝ) := by
      have h := congrArg (fun x : ℚ => (x : ℝ)) (hc_inv (n + 1)).1
      rw [hd_rec n] at h
      simpa [mul_assoc] using h
    have hdn_ne : (d n : ℝ) ≠ 0 := by exact_mod_cast (hd_pos n).ne'
    have ha1_ne : (a (n + 1) : ℝ) ≠ 0 := by
      exact_mod_cast (Erdos243R1H1.strictMono_pos_of_pos ha (by omega)).ne'
    have ha2_ne : (a (n + 2) : ℝ) ≠ 0 := by
      exact_mod_cast (Erdos243R1H1.strictMono_pos_of_pos ha (by omega)).ne'
    have hR1_ne : (R (n + 1) : ℝ) ≠ 0 := by
      have : (0 : ℝ) < (R (n + 1) : ℝ) := by exact_mod_cast hRpos (n + 1) (by omega)
      exact this.ne'
    rw [hcn, hcn1]
    field_simp [hdn_ne, ha1_ne, ha2_ne, hR1_ne]
  refine ⟨1, c, d, hc_pos, hd_pos, hc_rec, hd_rec, ?_⟩
  intro k
  have hε : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hc_ratio_lim (1 / ((k : ℝ) + 1)) hε
  refine ⟨N, fun n hn => ?_⟩
  have hdist := hN n hn
  rw [Real.dist_eq, abs_lt] at hdist
  have hcn_pos : (0 : ℝ) < (c n : ℝ) := by exact_mod_cast hc_pos n
  have hlo : -((c n : ℝ) / ((k : ℝ) + 1)) < (c (n + 1) : ℝ) - (c n : ℝ) := by
    have h1 := hdist.1
    rw [div_sub_one hcn_pos.ne'] at h1
    have h2 := (lt_div_iff₀ hcn_pos).mp h1
    have h3 : -(1 / ((k : ℝ) + 1)) * (c n : ℝ) = -((c n : ℝ) / ((k : ℝ) + 1)) := by ring
    linarith
  have hhi : (c (n + 1) : ℝ) - (c n : ℝ) < (c n : ℝ) / ((k : ℝ) + 1) := by
    have h1 := hdist.2
    rw [div_sub_one hcn_pos.ne'] at h1
    have h2 := (div_lt_iff₀ hcn_pos).mp h1
    have h3 : 1 / ((k : ℝ) + 1) * (c n : ℝ) = (c n : ℝ) / ((k : ℝ) + 1) := by ring
    linarith
  have hk1_pos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hhi_mul : ((k : ℝ) + 1) * ((c (n + 1) : ℝ) - (c n : ℝ)) < (c n : ℝ) := by
    have := (lt_div_iff₀ hk1_pos).mp hhi
    linarith
  have hlo_mul : ((k : ℝ) + 1) * ((c n : ℝ) - (c (n + 1) : ℝ)) < (c n : ℝ) := by
    have : (c n : ℝ) - (c (n + 1) : ℝ) < (c n : ℝ) / ((k : ℝ) + 1) := by linarith
    have := (lt_div_iff₀ hk1_pos).mp this
    linarith
  constructor
  · by_cases hle : c n ≤ c (n + 1)
    · have hreal : ((k * (c (n + 1) - c n) : ℕ) : ℝ) < (c n : ℝ) := by
        rw [Nat.cast_mul, Nat.cast_sub hle]
        have hdiff_nn : (0 : ℝ) ≤ (c (n + 1) : ℝ) - (c n : ℝ) := by
          have : (c n : ℝ) ≤ (c (n + 1) : ℝ) := by exact_mod_cast hle
          linarith
        nlinarith
      exact_mod_cast hreal
    · have hzero : c (n + 1) - c n = 0 := Nat.sub_eq_zero_of_le (le_of_not_ge hle)
      rw [hzero, mul_zero]
      exact hc_pos n
  · by_cases hle : c (n + 1) ≤ c n
    · have hreal : ((k * (c n - c (n + 1)) : ℕ) : ℝ) < (c n : ℝ) := by
        rw [Nat.cast_mul, Nat.cast_sub hle]
        have hdiff_nn : (0 : ℝ) ≤ (c n : ℝ) - (c (n + 1) : ℝ) := by
          have : (c (n + 1) : ℝ) ≤ (c n : ℝ) := by exact_mod_cast hle
          linarith
        nlinarith
      exact_mod_cast hreal
    · have hzero : c n - c (n + 1) = 0 := Nat.sub_eq_zero_of_le (le_of_not_ge hle)
      rw [hzero, mul_zero]
      exact hc_pos n
