import OMAStatements.S_oeis_a237685

namespace OMA.S_oeis_a237685

open Multiset

private theorem merge_sum (p : Multiset ℕ) : (mergeParts p).sum = p.sum := by
  change (∑ x ∈ p.toFinset, p.count x * x) = p.sum
  simp only [Finset.sum_multiset_count, nsmul_eq_mul, Nat.cast_id]

private theorem iterate_sum (p : Multiset ℕ) (i : ℕ) :
    (mergeParts^[i] p).sum = p.sum := by
  induction i with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply', merge_sum, ih]

private theorem repeat_source {p : Multiset ℕ} {y : ℕ} (hy : 2 ≤ (mergeParts p).count y) :
    ∃ x, 2 ≤ p.count x ∧ y = p.count x * x := by
  let f : Multiset ℕ := p.dedup.filter fun x => y = p.count x * x
  have hcard : 2 ≤ f.card := by
    simpa only [f, mergeParts, Multiset.count_map] using hy
  by_contra hn
  have he : f = Multiset.replicate f.card y := by
    apply Multiset.eq_replicate_card.mpr
    intro x hx
    have hmem : x ∈ p.dedup ∧ y = p.count x * x := Multiset.mem_filter.mp hx
    have hxpos := Multiset.count_pos.mpr (Multiset.mem_dedup.mp hmem.1)
    by_cases hlarge : 2 ≤ p.count x
    · exact False.elim (hn ⟨x, hlarge, hmem.2⟩)
    · have hone : p.count x = 1 := by omega
      simpa [hone] using hmem.2.symm
  have hnodup : f.Nodup := (Multiset.nodup_dedup _).filter _
  have hcnt := Multiset.nodup_iff_count_le_one.mp hnodup y
  rw [he] at hcnt
  simp at hcnt
  omega

private theorem repeat_large {p : Multiset ℕ} (hp : ∀ x ∈ p, 0 < x) (i : ℕ) :
    ∀ y, 2 ≤ (mergeParts^[i] p).count y → 2^i ≤ y := by
  induction i with
  | zero =>
    intro y hy
    have hym : y ∈ p := Multiset.count_pos.mp (by simpa using (show 0 < (mergeParts^[0] p).count y by omega))
    have hyp := hp y hym
    rw [pow_zero]
    omega
  | succ i ih =>
    intro y hy
    rw [Function.iterate_succ_apply'] at hy
    obtain ⟨x, hx, rfl⟩ := repeat_source hy
    calc
      2^(i+1) = 2 * 2^i := by rw [pow_succ, mul_comm]
      _ ≤ ((mergeParts^[i] p).count x) * x := Nat.mul_le_mul hx (ih x hx)

private theorem two_le_sum {p : Multiset ℕ} {x : ℕ} (hx : 2 ≤ p.count x) :
    2*x ≤ p.sum := by
  have hmem : x ∈ p.toFinset := Multiset.mem_toFinset.mpr (Multiset.count_pos.mp (by omega))
  rw [← merge_sum p]
  change 2*x ≤ ∑ i ∈ p.toFinset, p.count i * i
  exact (Nat.mul_le_mul_right x hx).trans (Finset.single_le_sum (f := fun i => p.count i * i) (fun _ _ => Nat.zero_le _) hmem)

private theorem depth_bound {n d : ℕ} (hn : 0 < n) (p : Nat.Partition n)
    (hp : hasDepth p.parts d) : 2^d ≤ n := by
  cases d with
  | zero =>
    rw [pow_zero]
    omega
  | succ i =>
    have hi := hp.2 i (Nat.lt_succ_self i)
    rw [Multiset.nodup_iff_count_le_one] at hi
    obtain ⟨x, hx⟩ := not_forall.mp hi
    have hx2 : 2 ≤ (mergeParts^[i] p.parts).count x := by omega
    have hxL := repeat_large (fun _ h => p.parts_pos h) i x hx2
    calc
      2^(i+1) = 2 * 2^i := by rw [pow_succ, mul_comm]
      _ ≤ 2*x := Nat.mul_le_mul_left _ hxL
      _ ≤ (mergeParts^[i] p.parts).sum := two_le_sum hx2
      _ = n := (iterate_sum p.parts i).trans p.parts_sum

private def tower : ℕ → ℕ → Multiset ℕ
  | 0, _ => 0
  | d+1, x => x ::ₘ tower d (2*x)

private def cascade (d x : ℕ) : Multiset ℕ := x ::ₘ tower d x

private theorem tower_mem_le (d x : ℕ) : ∀ y ∈ tower d x, x ≤ y := by
  induction d generalizing x with
  | zero => simp [tower]
  | succ d ih =>
    intro y hy
    rw [tower, Multiset.mem_cons] at hy
    rcases hy with rfl | hy
    · rfl
    · exact (show x ≤ 2*x by omega).trans (ih _ _ hy)

private theorem tower_nodup (d : ℕ) {x : ℕ} (hx : 0 < x) : (tower d x).Nodup := by
  induction d generalizing x with
  | zero => simp [tower]
  | succ d ih =>
    rw [tower, Multiset.nodup_cons]
    refine ⟨?_, ih (by omega)⟩
    intro hmem
    have := tower_mem_le d (2*x) x hmem
    omega

private theorem merge_cascade (d : ℕ) {x : ℕ} (hx : 0 < x) :
    mergeParts (cascade (d+1) x) = cascade d (2*x) := by
  let p := tower d (2*x)
  have hmem : x ∉ p := by
    intro hm
    have := tower_mem_le d (2*x) x hm
    omega
  have hp : p.Nodup := tower_nodup d (by omega)
  change ((x ::ₘ x ::ₘ p).dedup.map fun y => (x ::ₘ x ::ₘ p).count y * y) = (2*x) ::ₘ p
  rw [Multiset.dedup_cons_of_mem (Multiset.mem_cons_self x p),
    Multiset.dedup_cons_of_notMem hmem, Multiset.dedup_eq_self.mpr hp, Multiset.map_cons]
  have hcount : p.count x = 0 := Multiset.count_eq_zero_of_notMem hmem
  have hhead : (x ::ₘ x ::ₘ p).count x * x = 2*x := by simp [hcount]
  rw [hhead]
  congr 1
  calc
    p.map (fun y => (x ::ₘ x ::ₘ p).count y * y) = p.map id := by
      apply Multiset.map_congr rfl
      intro y hy
      have hne : x ≠ y := fun e => hmem (e ▸ hy)
      have hc := Multiset.nodup_iff_count_eq_one.mp hp y hy
      simp [hc, Ne.symm hne]
    _ = p := Multiset.map_id _

private theorem cascade_depth (d : ℕ) {x : ℕ} (hx : 0 < x) :
    hasDepth (cascade d x) d := by
  induction d generalizing x with
  | zero =>
    simp [hasDepth, cascade, tower]
  | succ d ih =>
    have hf := merge_cascade d hx
    have hi := ih (x := 2*x) (by omega)
    constructor
    · rw [Function.iterate_succ_apply, hf]
      exact hi.1
    · intro k hk
      cases k with
      | zero => simp [cascade, tower]
      | succ k =>
        rw [Function.iterate_succ_apply, hf]
        exact hi.2 k (by omega)

private theorem cascade_sum (d : ℕ) {x : ℕ} (hx : 0 < x) :
    (cascade d x).sum = 2^d*x := by
  induction d generalizing x with
  | zero => simp [cascade, tower]
  | succ d ih =>
    rw [← merge_sum (cascade (d+1) x), merge_cascade d hx, ih (by omega)]
    rw [pow_succ, mul_assoc]

end OMA.S_oeis_a237685

open OMA.S_oeis_a237685 in
theorem OMA.solution : type_of% @OMA.S_oeis_a237685.main := by
  intro d
  have hd : 0 < 2^d := Nat.pow_pos (by decide)
  refine ⟨⟨hd, ?_⟩, ?_⟩
  · let p : Nat.Partition (2^d) := {
      parts := cascade d 1
      parts_pos := by
        intro y hy
        rw [cascade, Multiset.mem_cons] at hy
        rcases hy with rfl | hy
        · decide
        · exact tower_mem_le d 1 y hy
      parts_sum := by simpa using cascade_sum d (x := 1) (by decide)
      }
    exact ⟨p, cascade_depth d (x := 1) (by decide)⟩
  · rintro n ⟨hn, p, hp⟩
    exact depth_bound hn p hp
