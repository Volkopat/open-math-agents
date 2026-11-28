import OMAStatements.S_oeis_a384928
import Mathlib.Tactic

namespace OMA.P_oeis_a384928

open OMA.S_oeis_a384928

private lemma sortedDivisors_mem_iff {m x : ℕ} :
    x ∈ sortedDivisors m ↔ x ∈ m.divisors := by
  simp [sortedDivisors]

private lemma sortedDivisors_sorted (m : ℕ) : (sortedDivisors m).Pairwise (· < ·) := by
  have h1 : (sortedDivisors m).Pairwise (· ≤ ·) := Finset.pairwise_sort m.divisors (· ≤ ·)
  have h2 : (sortedDivisors m).Nodup := Finset.sort_nodup m.divisors (· ≤ ·)
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  exact lt_of_le_of_ne (List.pairwise_iff_getElem.mp h1 i j hi hj hij)
    (List.pairwise_iff_getElem.mp h2 i j hi hj hij)

private lemma sortedDivisors_strictMono {m : ℕ} {i j : ℕ}
    (hi : i < (sortedDivisors m).length) (hj : j < (sortedDivisors m).length) (hij : i < j) :
    (sortedDivisors m)[i] < (sortedDivisors m)[j] :=
  List.pairwise_iff_getElem.mp (sortedDivisors_sorted m) i j hi hj hij

private lemma sortedDivisors_mono {m : ℕ} {i j : ℕ}
    (hi : i < (sortedDivisors m).length) (hj : j < (sortedDivisors m).length) (hij : i ≤ j) :
    (sortedDivisors m)[i] ≤ (sortedDivisors m)[j] := by
  rcases eq_or_lt_of_le hij with rfl | hlt
  · exact le_rfl
  · exact le_of_lt (sortedDivisors_strictMono hi hj hlt)

/-- Divisor reversal: for `m > 0`, `ds[i] * ds[r - 1 - i] = m`. -/
private lemma sortedDivisors_mul_rev {m : ℕ} (hm : 0 < m) :
    let ds := sortedDivisors m
    ∀ i (hi : i < ds.length),
      ds[i] * ds[ds.length - 1 - i]'(by omega) = m := by
  intro ds
  -- The mapped list `(ds.map (fun d => m / d)).reverse` is strictly increasing and has the same
  -- elements as `ds`, hence equals `ds`!
  let rev := (ds.map (fun d => m / d)).reverse
  have hlen : rev.length = ds.length := by simp [rev]
  have hpos_mem : ∀ d ∈ ds, 0 < d ∧ d ∣ m := by
    intro d hd
    rw [sortedDivisors_mem_iff, Nat.mem_divisors] at hd
    exact ⟨Nat.pos_of_dvd_of_pos hd.1 hm, hd.1⟩
  have hrev_sorted : rev.Pairwise (· < ·) := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    simp only [rev, List.getElem_reverse, List.getElem_map, List.length_map]
    have hi' : ds.length - 1 - i < ds.length := by
      simp only [rev, List.length_reverse, List.length_map] at hi; omega
    have hj' : ds.length - 1 - j < ds.length := by
      simp only [rev, List.length_reverse, List.length_map] at hj; omega
    have hlt_d : ds[ds.length - 1 - j] < ds[ds.length - 1 - i] :=
      sortedDivisors_strictMono hj' hi' (by omega)
    have hdi := hpos_mem _ (List.getElem_mem hi')
    have hdj := hpos_mem _ (List.getElem_mem hj')
    have hmul_i : ds[ds.length - 1 - i] * (m / ds[ds.length - 1 - i]) = m :=
      Nat.mul_div_cancel' hdi.2
    have hmul_j : ds[ds.length - 1 - j] * (m / ds[ds.length - 1 - j]) = m :=
      Nat.mul_div_cancel' hdj.2
    have hpos_j : 0 < m / ds[ds.length - 1 - j] :=
      Nat.div_pos (Nat.le_of_dvd hm hdj.2) hdj.1
    nlinarith
  have hrev_eq : rev = ds := by
    have hnodup1 : rev.Nodup := List.Pairwise.imp (fun h => ne_of_lt h) hrev_sorted
    have hnodup2 : ds.Nodup := Finset.sort_nodup m.divisors (· ≤ ·)
    have hperm : rev.Perm ds := by
      rw [List.perm_ext_iff_of_nodup hnodup1 hnodup2]
      intro x
      simp only [rev, List.mem_reverse, List.mem_map, ds, sortedDivisors_mem_iff, Nat.mem_divisors]
      constructor
      · rintro ⟨d, ⟨hd, hm0⟩, rfl⟩
        exact ⟨Nat.div_dvd_of_dvd hd, hm0⟩
      · rintro ⟨hx, hm0⟩
        refine ⟨m / x, ⟨Nat.div_dvd_of_dvd hx, hm0⟩, ?_⟩
        have hx_pos : 0 < x := Nat.pos_of_dvd_of_pos hx hm
        exact Nat.div_div_self hx (by omega)
    exact hperm.eq_of_pairwise (fun _ _ _ _ h1 h2 => le_antisymm h1 h2)
      (List.Pairwise.imp (fun h => le_of_lt h) hrev_sorted)
      (List.Pairwise.imp (fun h => le_of_lt h) (sortedDivisors_sorted m))
  intro i hi
  have hget : ds[i] = rev[i]'(by omega) := by simp [hrev_eq]
  have hrev_i : rev[i]'(by omega) = m / ds[ds.length - 1 - i]'(by omega) := by
    simp [rev]
  rw [hget, hrev_i]
  have hd := (hpos_mem _ (List.getElem_mem (by omega : ds.length - 1 - i < ds.length))).2
  exact Nat.div_mul_cancel hd

/-- Break-index symmetry: `i` is a break iff `r - 2 - i` is a break. -/
private lemma break_symm {m : ℕ} (hm : 0 < m) :
    let ds := sortedDivisors m
    ∀ i : ℕ, i < ds.length - 1 →
      (2 * ds.getD i 0 < ds.getD (i + 1) 0 ↔
       2 * ds.getD (ds.length - 2 - i) 0 < ds.getD (ds.length - 2 - i + 1) 0) := by
  intro ds i hi
  have hi0 : i < ds.length := by omega
  have hi1 : i + 1 < ds.length := by omega
  have hj0 : ds.length - 2 - i < ds.length := by omega
  have hj1 : ds.length - 2 - i + 1 < ds.length := by omega
  have hget : ∀ k (hk : k < ds.length), ds.getD k 0 = ds[k] := by
    intro k hk; simp [List.getD_eq_getElem?_getD, hk]
  rw [hget i hi0, hget (i + 1) hi1, hget (ds.length - 2 - i) hj0, hget (ds.length - 2 - i + 1) hj1]
  have hm0 := sortedDivisors_mul_rev hm i hi0
  have hm1 := sortedDivisors_mul_rev hm (i + 1) hi1
  have hidx0 : ds.length - 1 - i = ds.length - 2 - i + 1 := by omega
  have hidx1 : ds.length - 1 - (i + 1) = ds.length - 2 - i := by omega
  have ha_pos : 0 < ds[i] :=
    Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp (sortedDivisors_mem_iff.mp (List.getElem_mem hi0))).1 hm
  have hb_pos : 0 < ds[i + 1] :=
    Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp (sortedDivisors_mem_iff.mp (List.getElem_mem hi1))).1 hm
  have hc_pos : 0 < ds[ds.length - 2 - i] :=
    Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp (sortedDivisors_mem_iff.mp (List.getElem_mem hj0))).1 hm
  have hd_pos : 0 < ds[ds.length - 2 - i + 1] :=
    Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp (sortedDivisors_mem_iff.mp (List.getElem_mem hj1))).1 hm
  have heq0 : ds[i] * ds[ds.length - 2 - i + 1] = m := by
    convert hm0 using 2
    simp only [ds, hidx0]
  have heq1 : ds[i + 1] * ds[ds.length - 2 - i] = m := by
    convert hm1 using 2
    simp only [ds, hidx1]
  constructor <;> intro h <;> nlinarith

/-- If a finite set `S ⊆ range N` is closed under `i ↦ N - 1 - i` and has no fixed point,
then `S.card` is even. -/
private lemma even_card_of_invol {N : ℕ} (S : Finset ℕ) (hsub : S ⊆ Finset.range N)
    (hsym : ∀ i ∈ S, N - 1 - i ∈ S) (hnofix : ∀ i ∈ S, N - 1 - i ≠ i) :
    Even S.card := by
  let A := S.filter (fun i => i < N - 1 - i)
  let B := S.filter (fun i => N - 1 - i < i)
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro i hiA hiB
    simp only [A, B, Finset.mem_filter] at hiA hiB
    omega
  have hunion : S = A ∪ B := by
    ext i
    simp only [A, B, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hi
      have hne := hnofix i hi
      rcases lt_trichotomy i (N - 1 - i) with h | h | h
      · exact Or.inl ⟨hi, h⟩
      · exact absurd h.symm hne
      · exact Or.inr ⟨hi, h⟩
    · rintro (⟨hi, _⟩ | ⟨hi, _⟩) <;> exact hi
  have hcardAB : A.card = B.card := by
    refine Finset.card_bij (fun i _ => N - 1 - i) ?_ ?_ ?_
    · intro i hi
      simp only [A, B, Finset.mem_filter] at hi ⊢
      have hiN : i < N := Finset.mem_range.mp (hsub hi.1)
      exact ⟨hsym i hi.1, by omega⟩
    · intro i1 h1 i2 h2 heq
      simp only [A, Finset.mem_filter] at h1 h2
      have hi1 : i1 < N := Finset.mem_range.mp (hsub h1.1)
      have hi2 : i2 < N := Finset.mem_range.mp (hsub h2.1)
      omega
    · intro j hj
      simp only [A, B, Finset.mem_filter] at hj ⊢
      have hjN : j < N := Finset.mem_range.mp (hsub hj.1)
      exact ⟨N - 1 - j, ⟨hsym j hj.1, by omega⟩, by omega⟩
  rw [hunion, Finset.card_union_of_disjoint hdisj, hcardAB]
  exact ⟨B.card, by ring⟩

private theorem prove_main : type_of% @OMA.S_oeis_a384928.main := by
  intro k
  set m := tri (2 * k + 1)
  have hm_eq : m = (2 * k + 1) * (k + 1) := by
    unfold m tri
    have : (2 * k + 1) * (2 * k + 1 + 1) = 2 * ((2 * k + 1) * (k + 1)) := by ring
    rw [this, Nat.mul_div_cancel_left _ (by norm_num)]
  have hm_pos : 0 < m := by rw [hm_eq]; positivity
  set ds := sortedDivisors m
  have hds_ne : ds ≠ [] := by
    intro h0
    have h1 : 1 ∈ ds := sortedDivisors_mem_iff.mpr (Nat.one_mem_divisors.mpr (by omega))
    rw [h0] at h1
    exact List.not_mem_nil h1
  unfold a numTwoDenseSublists
  change Odd (if ds.isEmpty then 0
    else 1 + ((List.range (ds.length - 1)).filter (fun i =>
      2 * ds.getD i 0 < ds.getD (i + 1) 0)).length)
  rw [if_neg (by simp [hds_ne])]
  -- Convert List.filter length to Finset.filter card
  set N := ds.length - 1
  set S : Finset ℕ := (Finset.range N).filter (fun i => 2 * ds.getD i 0 < ds.getD (i + 1) 0)
  have hlen_eq : ((List.range N).filter (fun i => 2 * ds.getD i 0 < ds.getD (i + 1) 0)).length = S.card := by
    have hnodup : ((List.range N).filter (fun i => decide (2 * ds.getD i 0 < ds.getD (i + 1) 0))).Nodup :=
      List.nodup_range.filter _
    rw [← List.toFinset_card_of_nodup hnodup]
    congr 1
    ext i
    simp [S]
  rw [hlen_eq]
  suffices hEven : Even S.card by
    rcases hEven with ⟨t, ht⟩
    exact ⟨t, by omega⟩
  apply even_card_of_invol S (Finset.filter_subset _ _)
  · intro i hi
    simp only [S, Finset.mem_filter, Finset.mem_range] at hi ⊢
    have hsym := break_symm hm_pos i hi.1
    refine ⟨by omega, ?_⟩
    have hN1 : N - 1 - i = ds.length - 2 - i := by omega
    rw [hN1]
    exact hsym.mp hi.2
  · intro i hi heq
    simp only [S, Finset.mem_filter, Finset.mem_range] at hi
    -- Fixed point: ds.length = 2 * i + 2, so ds[i] * ds[i+1] = m and 2 * ds[i] < ds[i+1]
    have hi0 : i < ds.length := by omega
    have hi1 : i + 1 < ds.length := by omega
    have hget : ∀ j (hj : j < ds.length), ds.getD j 0 = ds[j] := by
      intro j hj; simp [List.getD_eq_getElem?_getD, hj]
    have hbrk : 2 * ds[i] < ds[i + 1] := by
      rw [← hget i hi0, ← hget (i + 1) hi1]; exact hi.2
    have hmul : ds[i] * ds[i + 1] = m := by
      have := sortedDivisors_mul_rev hm_pos i hi0
      have hidx : ds.length - 1 - i = i + 1 := by omega
      convert this using 2
      simp only [ds, hidx]
    -- Now use the divisor d = k + 1 ∈ ds!
    have hd_mem : k + 1 ∈ ds := by
      rw [sortedDivisors_mem_iff, Nat.mem_divisors]
      exact ⟨⟨2 * k + 1, by linarith⟩, by omega⟩
    obtain ⟨j, hj, hdj⟩ := List.mem_iff_getElem.mp hd_mem
    have hsq1 : ds[i] ^ 2 < m := by
      have hlt : ds[i] < ds[i + 1] := sortedDivisors_strictMono hi0 hi1 (by omega)
      nlinarith
    have hsq2 : m < ds[i + 1] ^ 2 := by
      have hlt : ds[i] < ds[i + 1] := sortedDivisors_strictMono hi0 hi1 (by omega)
      nlinarith
    have hle_k : (k + 1) ^ 2 ≤ m := by rw [hm_eq]; nlinarith
    have hj_le : j ≤ i := by
      by_contra hgt
      have hji1 : i + 1 ≤ j := by omega
      have hle := sortedDivisors_mono hi1 hj hji1
      rw [hdj] at hle
      nlinarith
    have hdi_ge : k + 1 ≤ ds[i] := by
      rw [← hdj]
      exact sortedDivisors_mono hj hi0 hj_le
    -- Also 2k + 1 ∈ ds gives ds[i+1] ≤ 2k + 1!
    have hd2_mem : 2 * k + 1 ∈ ds := by
      rw [sortedDivisors_mem_iff, Nat.mem_divisors]
      exact ⟨⟨k + 1, by linarith⟩, by omega⟩
    obtain ⟨j2, hj2, hdj2⟩ := List.mem_iff_getElem.mp hd2_mem
    have hge_2k : m ≤ (2 * k + 1) ^ 2 := by rw [hm_eq]; nlinarith
    have hj2_ge : i + 1 ≤ j2 := by
      by_contra hlt
      have hj2i : j2 ≤ i := by omega
      have hle := sortedDivisors_mono hj2 hi0 hj2i
      rw [hdj2] at hle
      nlinarith
    have hdi1_le : ds[i + 1] ≤ 2 * k + 1 := by
      rw [← hdj2]
      exact sortedDivisors_mono hi1 hj2 hj2_ge
    omega

end OMA.P_oeis_a384928

theorem OMA.solution : type_of% @OMA.S_oeis_a384928.main :=
  OMA.P_oeis_a384928.prove_main
