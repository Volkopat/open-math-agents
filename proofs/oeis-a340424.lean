import OMAStatements.S_oeis_a340424
import Mathlib

open OMA.S_oeis_a340424

namespace P340424

open Finset

/-- partition counts -/
def pc (m : ℕ) : ℕ := Fintype.card (Nat.Partition m)

/-- number of partitions of `n` with at least `j` parts equal to `d` -/
def N (n d j : ℕ) : ℕ := (univ.filter fun p : Nat.Partition n => j ≤ p.parts.count d).card

theorem N_zero (n d : ℕ) : N n d 0 = pc n := by
  simp [N, pc]

theorem N_succ (n d j : ℕ) (hd : 1 ≤ d) : N n d (j + 1) = if d ≤ n then N (n - d) d j else 0 := by
  split_ifs with h
  · unfold N
    rw [← Fintype.card_subtype, ← Fintype.card_subtype]
    let e := Nat.Partition.partitionWithPartEquiv hd h
    have e2 : {p : Nat.Partition n // j + 1 ≤ p.parts.count d} ≃
        {x : {p : Nat.Partition n // d ∈ p.parts} // j + 1 ≤ x.1.parts.count d} :=
      { toFun := fun p => ⟨⟨p.1, Multiset.count_pos.mp (by have := p.2; omega)⟩, p.2⟩
        invFun := fun x => ⟨x.1.1, x.2⟩
        left_inv := fun p => rfl
        right_inv := fun x => rfl }
    rw [Fintype.card_congr e2]
    apply Fintype.card_congr
    refine Equiv.subtypeEquiv e fun x => ?_
    rw [Nat.Partition.partitionWithPartEquiv_apply_parts, Multiset.count_erase_self]
    have := Multiset.count_pos.mpr x.2
    omega
  · unfold N
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro p _ hp
    have hm : d ∈ p.parts := Multiset.count_pos.mp (by omega)
    exact h (Nat.Partition.le_of_mem_parts hm)

theorem N_formula (d : ℕ) (hd : 1 ≤ d) (j : ℕ) :
    ∀ n, N n d j = if d * j ≤ n then pc (n - d * j) else 0 := by
  induction j with
  | zero => intro n; simp [N_zero]
  | succ j ih =>
    intro n
    rw [N_succ n d j hd]
    split_ifs with h1 h2 h2
    · rw [ih, if_pos (by rw [mul_add] at h2; omega)]
      congr 1
      rw [mul_add]; omega
    · rw [ih, if_neg (by rw [mul_add] at h2; omega)]
    · exfalso; rw [mul_add] at h2; omega
    · rfl

theorem count_le (n d : ℕ) (hd : 1 ≤ d) (p : Nat.Partition n) : p.parts.count d ≤ n := by
  have h1 : p.parts.count d ≤ Multiset.card p.parts := Multiset.count_le_card _ _
  have h2 : Multiset.card p.parts ≤ p.parts.sum := by
    have : ∀ x ∈ p.parts, 1 ≤ x := fun x hx => p.parts_pos hx
    have := Multiset.card_nsmul_le_sum this
    simpa using this
  rw [p.parts_sum] at h2
  omega

theorem sum_count (n d : ℕ) (hd : 1 ≤ d) :
    ∑ p : Nat.Partition n, p.parts.count d = ∑ j ∈ range n, N n d (j + 1) := by
  have key : ∀ p : Nat.Partition n,
      p.parts.count d = ∑ j ∈ range n, if j + 1 ≤ p.parts.count d then 1 else 0 := by
    intro p
    rw [Finset.sum_boole]
    have : (range n).filter (fun j => j + 1 ≤ p.parts.count d) = range (p.parts.count d) := by
      ext j
      simp only [mem_filter, mem_range]
      have := count_le n d hd p
      omega
    rw [this, card_range]; simp
  rw [Finset.sum_congr rfl fun p _ => key p, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [N, Finset.card_filter]

theorem parts_sum_eq (n : ℕ) (p : Nat.Partition n) :
    p.parts.sum = ∑ d ∈ Icc 1 n, d * p.parts.count d := by
  rw [Finset.sum_multiset_count_of_subset p.parts (Icc 1 n)]
  · refine Finset.sum_congr rfl fun d _ => ?_
    rw [smul_eq_mul, mul_comm]
  · intro x hx
    rw [Multiset.mem_toFinset] at hx
    rw [mem_Icc]
    exact ⟨p.parts_pos hx, Nat.Partition.le_of_mem_parts hx⟩

theorem lhs_eq (n : ℕ) : n * pc n =
    ∑ d ∈ Icc 1 n, ∑ j ∈ range n, d * (if d * (j + 1) ≤ n then pc (n - d * (j + 1)) else 0) := by
  have h1 : n * pc n = ∑ p : Nat.Partition n, p.parts.sum := by
    simp [pc, Nat.Partition.parts_sum, mul_comm]
  rw [h1, Finset.sum_congr rfl fun p _ => parts_sum_eq n p, Finset.sum_comm]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [mem_Icc] at hd
  rw [← Finset.mul_sum, ← Finset.mul_sum, sum_count n d hd.1]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [N_formula d hd.1]

theorem sigma_eq (n k : ℕ) (hk : k ∈ Icc 1 n) :
    ArithmeticFunction.sigma 1 k = ∑ d ∈ Icc 1 n, if d ∣ k then d else 0 := by
  rw [mem_Icc] at hk
  rw [ArithmeticFunction.sigma_one_apply, ← Finset.sum_filter]
  congr 1
  ext d
  simp only [Nat.mem_divisors, mem_filter, mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨⟨Nat.pos_of_dvd_of_pos h1 (by omega), ?_⟩, h1⟩
    exact le_trans (Nat.le_of_dvd (by omega) h1) hk.2
  · rintro ⟨_, h⟩
    exact ⟨h, by omega⟩

theorem inner_eq (n d : ℕ) (hd : 1 ≤ d) (f : ℕ → ℕ) :
    ∑ k ∈ Icc 1 n, (if d ∣ k then f k else 0) =
      ∑ j ∈ range n, if d * (j + 1) ≤ n then f (d * (j + 1)) else 0 := by
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  refine Finset.sum_nbij' (fun k => k / d - 1) (fun j => d * (j + 1)) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    simp only [mem_filter, mem_Icc] at hk
    obtain ⟨⟨hk1, hk2⟩, m, rfl⟩ := hk
    simp only [mem_filter, mem_range]
    rw [Nat.mul_div_cancel_left _ (by omega)]
    have hm : 1 ≤ m := by rcases m with _ | m <;> simp_all
    have : m ≤ d * m := Nat.le_mul_of_pos_left m (by omega)
    refine ⟨by omega, ?_⟩
    rw [show m - 1 + 1 = m by omega]; exact hk2
  · intro j hj
    simp only [mem_filter, mem_range] at hj
    simp only [mem_filter, mem_Icc]
    refine ⟨⟨?_, hj.2⟩, dvd_mul_right _ _⟩
    exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  · intro k hk
    simp only [mem_filter, mem_Icc] at hk
    obtain ⟨⟨hk1, hk2⟩, m, rfl⟩ := hk
    rw [Nat.mul_div_cancel_left _ (by omega)]
    have hm : 1 ≤ m := by rcases m with _ | m <;> simp_all
    rw [show m - 1 + 1 = m by omega]
  · intro j _
    rw [Nat.mul_div_cancel_left _ (by omega)]
    omega
  · intro k hk
    simp only [mem_filter, mem_Icc] at hk
    obtain ⟨⟨hk1, hk2⟩, m, rfl⟩ := hk
    rw [Nat.mul_div_cancel_left _ (by omega)]
    have hm : 1 ≤ m := by rcases m with _ | m <;> simp_all
    rw [show m - 1 + 1 = m by omega]

theorem euler (n : ℕ) : n * pc n = ∑ k ∈ Icc 1 n, ArithmeticFunction.sigma 1 k * pc (n - k) := by
  rw [lhs_eq]
  have hr : ∑ k ∈ Icc 1 n, ArithmeticFunction.sigma 1 k * pc (n - k) =
      ∑ k ∈ Icc 1 n, ∑ d ∈ Icc 1 n, (if d ∣ k then d * pc (n - k) else 0) :=
    Finset.sum_congr rfl fun k hk => by
      rw [sigma_eq n k hk, Finset.sum_mul]
      exact Finset.sum_congr rfl fun d _ => by split_ifs <;> simp
  rw [hr]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [mem_Icc] at hd
  rw [inner_eq n d hd.1 (fun k => d * pc (n - k))]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

theorem q_zero : A002865 0 = pc 0 := by
  unfold A002865 pc
  rw [Finset.filter_true_of_mem (fun p _ => by simp [Nat.Partition.partition_zero_parts])]
  rfl

theorem q_succ (m : ℕ) : pc (m + 1) = A002865 (m + 1) + pc m := by
  unfold A002865 pc
  rw [← Finset.card_univ, ← Finset.card_filter_add_card_filter_not
    (s := (univ : Finset (Nat.Partition (m + 1)))) (fun p => 1 ∈ p.parts), add_comm]
  congr 1
  rw [← Fintype.card_subtype]
  have := Fintype.card_congr (Nat.Partition.partitionWithPartEquiv (n := m + 1) (a := 1) le_rfl
    (by omega))
  rw [this]
  rfl

theorem Icc_sum (n : ℕ) (f : ℕ → ℤ) : ∑ k ∈ Icc 1 n, f k = ∑ j ∈ range n, f (j + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

open PowerSeries in
theorem row_sum (n : ℕ) : (∑ k ∈ Icc 1 n, T n k : ℕ) = n * pc n := by
  set Sg : PowerSeries ℤ := mk fun m => (A024916 m : ℤ) with hSg
  set Qg : PowerSeries ℤ := mk fun m => (A002865 m : ℤ) with hQg
  set Pg : PowerSeries ℤ := mk fun m => (pc m : ℤ) with hPg
  set Sig : PowerSeries ℤ := mk fun m => (ArithmeticFunction.sigma 1 m : ℤ) with hSig
  have hS : (1 - X) * Sg = Sig := by
    ext m
    rcases m with _ | m
    · simp [hSg, hSig, A024916]
    · rw [sub_mul, one_mul, map_sub, coeff_succ_X_mul, hSg, hSig, coeff_mk, coeff_mk, coeff_mk,
        A024916, A024916, Finset.sum_Icc_succ_top (by omega)]
      push_cast; ring
  have hQ : (1 - X) * Pg = Qg := by
    ext m
    rcases m with _ | m
    · simp [hPg, hQg, q_zero]
    · rw [sub_mul, one_mul, map_sub, coeff_succ_X_mul, hPg, hQg, coeff_mk, coeff_mk, coeff_mk,
        q_succ]
      push_cast; ring
  have hE : Qg * Sg = Sig * Pg := by
    rw [← hQ, ← hS]; ring
  have e := congrArg (coeff n) hE
  rw [coeff_mul, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
    Finset.sum_range_succ'] at e
  simp only [hSg, hQg, hPg, hSig, coeff_mk, Nat.sub_self, ArithmeticFunction.map_zero] at e
  have h0 : A024916 0 = 0 := by simp [A024916]
  rw [h0] at e
  have eu := euler n
  have eu' : ((n * pc n : ℕ) : ℤ) = ∑ k ∈ Icc 1 n, ((ArithmeticFunction.sigma 1 k : ℕ) : ℤ) *
      (pc (n - k) : ℤ) := by
    rw [eu]; push_cast; rfl
  rw [Icc_sum] at eu'
  have lhs : ((∑ k ∈ Icc 1 n, T n k : ℕ) : ℤ) = ∑ j ∈ range n, (A002865 j : ℤ) * (A024916 (n - j) : ℤ) := by
    push_cast
    rw [Icc_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [mem_range] at hj
    rw [T, show n - (j + 1) + 1 = n - j by omega, Nat.add_sub_cancel]
    push_cast; ring
  have : ((∑ k ∈ Icc 1 n, T n k : ℕ) : ℤ) = ((n * pc n : ℕ) : ℤ) := by
    rw [lhs, eu']
    simp only [Nat.cast_zero, mul_zero, add_zero, zero_mul] at e
    rw [e]
  exact_mod_cast this

end P340424

theorem OMA.solution : type_of% @OMA.S_oeis_a340424.main := by
  intro n _
  rw [P340424.row_sum]
  unfold A066186 P340424.pc
  simp [Nat.Partition.parts_sum, mul_comm]
