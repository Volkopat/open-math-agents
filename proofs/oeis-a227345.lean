import OMAStatements.S_oeis_a227345

open scoped BigOperators
open OMA.S_oeis_a227345

private def part (i : ℕ) : ℕ := 1 + i + i / 2

private def mass (k : ℕ) : ℕ := ∑ i ∈ Finset.range k, part i

private theorem mass_bounds (k : ℕ) : 3 * k ^ 2 ≤ 4 * mass k ∧ 4 * mass k ≤ 3 * k ^ 2 + 3 := by
  induction k using Nat.twoStepInduction with
  | zero => simp [mass]
  | one => norm_num [mass, part]
  | more k ih _ =>
    have hp : part k + part (k+1) = 3*k+3 := by unfold part; omega
    have hm : mass (k+2) = mass k + (3*k+3) := by
      unfold mass
      rw [show k+2=k+1+1 by omega, Finset.sum_range_succ, Finset.sum_range_succ, add_assoc, hp]
    rw [hm]
    constructor <;> nlinarith only [ih.1, ih.2]

private theorem mass_le_partition {S : Finset ℕ} {k : ℕ} (hk : boundarySize S = k)
    (hpos : ∀ p ∈ S, 0 < p) : mass k ≤ ∑ p ∈ S, p := by
  let B := S.filter (fun p => ¬ (p - 1 ∈ S ∧ p + 1 ∈ S))
  have hB : B.card = k := hk
  let e := B.orderEmbOfFin hB
  have hm (i : Fin k) : e i ∈ B := B.orderEmbOfFin_mem hB i
  have hp (i : Fin k) : 0 < e i := hpos _ (Finset.mem_filter.mp (hm i)).1
  have he : ∀ (i : ℕ) (hi : i < k), part i ≤ e ⟨i, hi⟩ := by
    intro i
    induction i using Nat.twoStepInduction with
    | zero =>
      intro hi
      change 1 ≤ e ⟨0, hi⟩
      exact Nat.succ_le_iff.mpr (hp ⟨0, hi⟩)
    | one =>
      intro hi
      let u : Fin k := ⟨0, by omega⟩
      let v : Fin k := ⟨1, hi⟩
      have hlt : e u < e v := e.strictMono (show (0 : ℕ) < 1 by omega)
      have h0 := hp u
      change part 1 ≤ e v
      simp only [part]
      omega
    | more i ih _ =>
      intro hi
      let u : Fin k := ⟨i, by omega⟩
      let v : Fin k := ⟨i+1, by omega⟩
      let w : Fin k := ⟨i+2, hi⟩
      have huv : e u < e v := e.strictMono (show i < i+1 by omega)
      have hvw : e v < e w := e.strictMono (show i+1 < i+2 by omega)
      have hg : e u + 3 ≤ e w := by
        by_contra! h
        have hu : e u = e v - 1 := by omega
        have hw : e w = e v + 1 := by omega
        have huS := (Finset.mem_filter.mp (hm u)).1
        have hwS := (Finset.mem_filter.mp (hm w)).1
        exact (Finset.mem_filter.mp (hm v)).2 ⟨hu ▸ huS, hw ▸ hwS⟩
      have hlow : part i ≤ e u := ih u.isLt
      change part (i+2) ≤ e w
      unfold part at hlow ⊢
      omega
  calc
    mass k = ∑ i : Fin k, part i.val := by
      symm
      exact Fin.sum_univ_eq_sum_range part k
    _ ≤ ∑ i : Fin k, e i := Finset.sum_le_sum (fun i _ => he i.val i.isLt)
    _ = ∑ p ∈ B, p := by
      rw [← B.map_orderEmbOfFin_univ hB, Finset.sum_map]
      rfl
    _ ≤ ∑ p ∈ S, p := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset _ _) (fun i _ _ => Nat.zero_le i)

private theorem construct_partition {n k : ℕ} (hk : 1 ≤ k) (hn : mass k ≤ n) :
    ∃ S : Finset ℕ, (∀ p ∈ S, 0 < p) ∧ ∑ p ∈ S, p = n ∧ boundarySize S = k := by
  let last : Fin k := ⟨k-1, by omega⟩
  let t := n - mass k
  let f (i : Fin k) : ℕ := part i.val + if i = last then t else 0
  have hnot {i j : Fin k} (h : i < j) : i ≠ last := by
    intro heq
    have e := congrArg Fin.val heq
    change i.val = k - 1 at e
    have hj := j.isLt
    change i.val < j.val at h
    omega
  have fm : StrictMono f := by
    intro i j hij
    have h : i.val < j.val := hij
    unfold f part
    rw [if_neg (hnot hij), add_zero]
    omega
  have fg {i j : Fin k} (h : i.val + 2 ≤ j.val) : f i + 3 ≤ f j := by
    unfold f part
    rw [if_neg (hnot (show i < j from (by omega : i.val < j.val))), add_zero]
    omega
  let emb : Fin k ↪ ℕ := ⟨f, fm.injective⟩
  let S := Finset.univ.map emb
  have he (p : ℕ) : p ∈ S ↔ ∃ i : Fin k, f i = p := by simp [S, emb]
  have hpos (i : Fin k) : 0 < f i := by unfold f part; omega
  have hf : (S.filter fun p => ¬ (p-1 ∈ S ∧ p+1 ∈ S)) = S := by
    apply Finset.filter_eq_self.mpr
    intro p hp h
    obtain ⟨i, hi⟩ := (he p).mp hp
    obtain ⟨j, hj⟩ := (he (p-1)).mp h.1
    obtain ⟨l, hl⟩ := (he (p+1)).mp h.2
    have hji : f j < f i := by have := hpos i; omega
    have hil : f i < f l := by omega
    have h₁ : j.val < i.val := fm.lt_iff_lt.mp hji
    have h₂ : i.val < l.val := fm.lt_iff_lt.mp hil
    have hh := fg (i := j) (j := l) (by omega)
    omega
  refine ⟨S, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨i, rfl⟩ := (he p).mp hp
    exact hpos i
  · have hmass : (∑ i : Fin k, part i.val) = mass k := Fin.sum_univ_eq_sum_range part k
    have htotal : (∑ i : Fin k, f i) = mass k + t := by
      unfold f
      rw [Finset.sum_add_distrib, hmass]
      simp
    unfold S
    rw [Finset.sum_map]
    change (∑ i : Fin k, f i) = n
    rw [htotal]
    omega
  · unfold boundarySize
    rw [hf]
    simp [S]

theorem OMA.solution : type_of% @OMA.S_oeis_a227345.main := by
  intro n k _ hk
  have h := mass_bounds k
  constructor
  · rintro ⟨S, hp, hs, hb⟩
    have hl := mass_le_partition hb hp
    omega
  · intro hn
    exact construct_partition hk (by omega)