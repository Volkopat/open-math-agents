import OMAStatements.S_oeis_a060957
import Mathlib

/-!
# Reduction oeis-a060957.R1

We lift Yan Sheng Ang's conjecture (OEIS A060957) via `Nat.factorization` to finite
nonzero order ideals `I ⊆ ℕ →₀ ℕ` (i.e. `0 ∉ I` and `v ∈ I → u ≤ v → u ≠ 0 → u ∈ I`).
The stronger claim is that the subset-sum set `P(I) = {∑ v ∈ S, v | S ⊆ I}` is
`ℓ₁`-geodesically convex (`IsGen1 I`): for any distinct `x, y ∈ P(I)` there is a coordinate `k`
where stepping `x` by `±1` toward `y` stays in `P(I)`.

Peeling a maximal element `w ∈ I` (`I' = I.erase w`) reduces `IsGen1 I` by induction on `|I|`
(and inner induction on the `ℓ₁` distance `dist₁ x y`) to two clean inductive lemmas:

* `H1`: When `x, y' ∈ P(I')` do not satisfy `y' ≤ x ≤ y' + w`, some coordinate outside
  `[y', y' + w]` admits a unit step from `x` toward `y'` or from `y'` toward `x` inside `P(I')`.
* `H2`: When `y' ≤ x ≤ y' + w` and `dist₁ x (y' + w) ≥ 2`, picking `k` with `x k < y' k + w k`
  and `v = w - single k 1 ∈ I'`, the deletion `H = I'.erase v` cannot contain `a, x ∈ P(H)`
  with `a + v ≤ x < a + 2v` while missing both `a + v` and `x - v`.

Both `H1` and `H2` have been stress-tested across hundreds of random and adversarial order ideals
(including `{1, …, 14}`, 3-cubes, 4-cycles, and asymmetric hole-inducing ideals) with zero
counterexamples. From `IsGen1` on `(Icc 2 n).image Nat.factorization`, `OMA.S_oeis_a060957.main`
follows immediately by applying `IsGen1` to `m.factorization` and `(p ^ a * m).factorization`.
-/

-- Credit: @Rickxscz

namespace OMA.R_oeis_a060957_R1

/-- Inductive off-box step lemma: for finite nonzero order ideals `I'` and `insert w I'`
(`w ∉ I'`) with `I'` `ℓ₁`-geodesically convex, any `x, y' ∈ P(I')` with at least one coordinate
outside `[y', y' + w]` admit a unit step inside `P(I')` toward each other in such a coordinate. -/
def H1 : Prop :=
  ∀ (I' : Finset (ℕ →₀ ℕ)) (w : ℕ →₀ ℕ),
    ((0 : ℕ →₀ ℕ) ∉ I' ∧ ∀ u v, v ∈ I' → u ≤ v → u ≠ 0 → u ∈ I') →
    ((0 : ℕ →₀ ℕ) ∉ insert w I' ∧ ∀ u v, v ∈ insert w I' → u ≤ v → u ≠ 0 → u ∈ insert w I') →
    w ∉ I' →
    (∀ x y : ℕ →₀ ℕ,
      (∃ S ⊆ I', ∑ v ∈ S, v = x) → (∃ T ⊆ I', ∑ v ∈ T, v = y) → x ≠ y →
      ∃ k : ℕ, (x k < y k ∧ ∃ S ⊆ I', ∑ v ∈ S, v = x + Finsupp.single k 1) ∨
               (y k < x k ∧ ∃ S ⊆ I', ∑ v ∈ S, v = x - Finsupp.single k 1)) →
    ∀ x y' : ℕ →₀ ℕ,
      (∃ S ⊆ I', ∑ v ∈ S, v = x) → (∃ T ⊆ I', ∑ v ∈ T, v = y') →
      (∃ k : ℕ, x k < y' k ∨ y' k + w k < x k) →
      ∃ k : ℕ,
        (x k < y' k ∧ ((∃ S ⊆ I', ∑ v ∈ S, v = x + Finsupp.single k 1) ∨
                       (∃ T ⊆ I', ∑ v ∈ T, v = y' - Finsupp.single k 1))) ∨
        (y' k + w k < x k ∧ ((∃ S ⊆ I', ∑ v ∈ S, v = x - Finsupp.single k 1) ∨
                             (∃ T ⊆ I', ∑ v ∈ T, v = y' + Finsupp.single k 1)))

/-- Single-element deletion interval lemma: for a finite nonzero `ℓ₁`-geodesically convex order
ideal `I'` and `v ∈ I'`, the subset sums of `I'.erase v` cannot contain `a` and `x` with
`a + v ≤ x < a + 2v` while missing both `a + v` and `x - v`. -/
def H2 : Prop :=
  ∀ (I' : Finset (ℕ →₀ ℕ)) (v : ℕ →₀ ℕ),
    ((0 : ℕ →₀ ℕ) ∉ I' ∧ ∀ u u', u' ∈ I' → u ≤ u' → u ≠ 0 → u ∈ I') →
    v ∈ I' →
    (∀ x y : ℕ →₀ ℕ,
      (∃ S ⊆ I', ∑ u ∈ S, u = x) → (∃ T ⊆ I', ∑ u ∈ T, u = y) → x ≠ y →
      ∃ k : ℕ, (x k < y k ∧ ∃ S ⊆ I', ∑ u ∈ S, u = x + Finsupp.single k 1) ∨
               (y k < x k ∧ ∃ S ⊆ I', ∑ u ∈ S, u = x - Finsupp.single k 1)) →
    ∀ a x : ℕ →₀ ℕ,
      (∃ S ⊆ I'.erase v, ∑ u ∈ S, u = a) → (∃ T ⊆ I'.erase v, ∑ u ∈ T, u = x) →
      a + v ≤ x → x ≤ a + v + v → x ≠ a + v + v →
      (∃ S ⊆ I'.erase v, ∑ u ∈ S, u = a + v) ∨ (∃ T ⊆ I'.erase v, ∑ u ∈ T, u = x - v)

lemma sum_eq_finset_sum (x : ℕ →₀ ℕ) (s : Finset ℕ) (hs : x.support ⊆ s) :
    x.sum (fun _ c => c) = ∑ k ∈ s, x k := by
  rw [Finsupp.sum]
  exact Finset.sum_subset hs (fun k _ hk => Finsupp.notMem_support_iff.mp hk)

lemma dist_eq_sum (x y : ℕ →₀ ℕ) (s : Finset ℕ)
    (hx : x.support ⊆ s) (hy : y.support ⊆ s) :
    (x - y).sum (fun _ c => c) + (y - x).sum (fun _ c => c) =
      ∑ k ∈ s, ((x k - y k) + (y k - x k)) := by
  have hxy : (x - y).support ⊆ s := by
    intro k hk
    rw [Finsupp.mem_support_iff, Finsupp.tsub_apply] at hk
    exact hx (Finsupp.mem_support_iff.mpr (by omega))
  have hyx : (y - x).support ⊆ s := by
    intro k hk
    rw [Finsupp.mem_support_iff, Finsupp.tsub_apply] at hk
    exact hy (Finsupp.mem_support_iff.mpr (by omega))
  rw [sum_eq_finset_sum _ s hxy, sum_eq_finset_sum _ s hyx, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun k _ => by simp [Finsupp.tsub_apply])

lemma dist_comm (x y : ℕ →₀ ℕ) :
    (x - y).sum (fun _ c => c) + (y - x).sum (fun _ c => c) =
      (y - x).sum (fun _ c => c) + (x - y).sum (fun _ c => c) :=
  add_comm _ _

lemma dist_add_left (w x y : ℕ →₀ ℕ) :
    ((w + x) - (w + y)).sum (fun _ c => c) + ((w + y) - (w + x)).sum (fun _ c => c) =
      (x - y).sum (fun _ c => c) + (y - x).sum (fun _ c => c) := by
  have h1 : (w + x) - (w + y) = x - y := by
    ext k; simp only [Finsupp.add_apply, Finsupp.tsub_apply]; omega
  have h2 : (w + y) - (w + x) = y - x := by
    ext k; simp only [Finsupp.add_apply, Finsupp.tsub_apply]; omega
  rw [h1, h2]

lemma dist_eq_zero_iff (x y : ℕ →₀ ℕ) :
    (x - y).sum (fun _ c => c) + (y - x).sum (fun _ c => c) = 0 ↔ x = y := by
  rw [dist_eq_sum x y (x.support ∪ y.support) Finset.subset_union_left Finset.subset_union_right]
  rw [Finset.sum_eq_zero_iff]
  constructor
  · intro h
    ext k
    by_cases hk : k ∈ x.support ∪ y.support
    · have := h k hk; omega
    · have hx : x k = 0 := Finsupp.notMem_support_iff.mp (fun h' => hk (Finset.mem_union_left _ h'))
      have hy : y k = 0 := Finsupp.notMem_support_iff.mp (fun h' => hk (Finset.mem_union_right _ h'))
      omega
  · intro h k _; subst h; omega

lemma dist_box_add (x y z : ℕ →₀ ℕ)
    (hbox : ∀ k, min (x k) (y k) ≤ z k ∧ z k ≤ max (x k) (y k)) :
    ((x - z).sum (fun _ c => c) + (z - x).sum (fun _ c => c)) +
      ((z - y).sum (fun _ c => c) + (y - z).sum (fun _ c => c)) =
      (x - y).sum (fun _ c => c) + (y - x).sum (fun _ c => c) := by
  let s := x.support ∪ y.support ∪ z.support
  have hx : x.support ⊆ s := Finset.Subset.trans Finset.subset_union_left Finset.subset_union_left
  have hy : y.support ⊆ s := Finset.Subset.trans Finset.subset_union_right Finset.subset_union_left
  have hz : z.support ⊆ s := Finset.subset_union_right
  rw [dist_eq_sum x z s hx hz, dist_eq_sum z y s hz hy, dist_eq_sum x y s hx hy,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have hk := hbox k
  omega

lemma dist_add_single_one (x : ℕ →₀ ℕ) (k : ℕ) :
    (x - (x + Finsupp.single k 1)).sum (fun _ c => c) +
      ((x + Finsupp.single k 1) - x).sum (fun _ c => c) = 1 := by
  have h1 : x - (x + Finsupp.single k 1) = 0 := by
    ext j; simp [Finsupp.tsub_apply, Finsupp.add_apply]
  have h2 : (x + Finsupp.single k 1) - x = Finsupp.single k 1 := by
    ext j; simp
  rw [h1, h2]
  simp [Finsupp.sum_single_index]

lemma dist_sub_single_one (x : ℕ →₀ ℕ) (k : ℕ) (hk : 0 < x k) :
    (x - (x - Finsupp.single k 1)).sum (fun _ c => c) +
      ((x - Finsupp.single k 1) - x).sum (fun _ c => c) = 1 := by
  have h1 : x - (x - Finsupp.single k 1) = Finsupp.single k 1 := by
    ext j
    simp only [Finsupp.tsub_apply, Finsupp.single_apply]
    split_ifs with h
    · subst h; omega
    · omega
  have h2 : (x - Finsupp.single k 1) - x = 0 := by
    ext j; simp [Finsupp.tsub_apply]
  rw [h1, h2]
  simp [Finsupp.sum_single_index]

lemma eq_of_dist_eq_one (x y : ℕ →₀ ℕ)
    (hd : (x - y).sum (fun _ c => c) + (y - x).sum (fun _ c => c) = 1) :
    ∃ k : ℕ, (x k < y k ∧ y = x + Finsupp.single k 1) ∨
             (y k < x k ∧ y = x - Finsupp.single k 1) := by
  let s := x.support ∪ y.support
  have hsum : ∑ k ∈ s, ((x k - y k) + (y k - x k)) = 1 := by
    rw [← dist_eq_sum x y s Finset.subset_union_left Finset.subset_union_right]; exact hd
  have hne : ∑ k ∈ s, ((x k - y k) + (y k - x k)) ≠ 0 := by omega
  obtain ⟨k, hk, hkne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have hsplit := Finset.add_sum_erase s (fun j => (x j - y j) + (y j - x j)) hk
  rw [hsum] at hsplit
  have hterm : (x k - y k) + (y k - x k) = 1 := by omega
  have hrest : ∑ j ∈ s.erase k, ((x j - y j) + (y j - x j)) = 0 := by omega
  rw [Finset.sum_eq_zero_iff] at hrest
  have heq_ne : ∀ j, j ≠ k → x j = y j := by
    intro j hj
    by_cases hjs : j ∈ s
    · have := hrest j (Finset.mem_erase.mpr ⟨hj, hjs⟩); omega
    · have hx : x j = 0 := Finsupp.notMem_support_iff.mp (fun h' => hjs (Finset.mem_union_left _ h'))
      have hy : y j = 0 := Finsupp.notMem_support_iff.mp (fun h' => hjs (Finset.mem_union_right _ h'))
      omega
  refine ⟨k, ?_⟩
  by_cases hlt : x k < y k
  · left
    refine ⟨hlt, ?_⟩
    ext j
    simp only [Finsupp.add_apply, Finsupp.single_apply]
    split_ifs with h
    · subst h; omega
    · have := heq_ne j (Ne.symm h); omega
  · right
    have hgt : y k < x k := by omega
    refine ⟨hgt, ?_⟩
    ext j
    simp only [Finsupp.tsub_apply, Finsupp.single_apply]
    split_ifs with h
    · subst h; omega
    · have := heq_ne j (Ne.symm h); omega

lemma gen1_of_box_mid (I : Finset (ℕ →₀ ℕ))
    (hmid : ∀ x y : ℕ →₀ ℕ,
      (∃ S ⊆ I, ∑ v ∈ S, v = x) → (∃ T ⊆ I, ∑ v ∈ T, v = y) →
      2 ≤ (x - y).sum (fun _ c => c) + (y - x).sum (fun _ c => c) →
      ∃ z : ℕ →₀ ℕ, (∃ U ⊆ I, ∑ v ∈ U, v = z) ∧ z ≠ x ∧ z ≠ y ∧
        ∀ k, min (x k) (y k) ≤ z k ∧ z k ≤ max (x k) (y k)) :
    ∀ x y : ℕ →₀ ℕ,
      (∃ S ⊆ I, ∑ v ∈ S, v = x) → (∃ T ⊆ I, ∑ v ∈ T, v = y) → x ≠ y →
      ∃ k : ℕ, (x k < y k ∧ ∃ S ⊆ I, ∑ v ∈ S, v = x + Finsupp.single k 1) ∨
               (y k < x k ∧ ∃ S ⊆ I, ∑ v ∈ S, v = x - Finsupp.single k 1) := by
  have hstrong : ∀ d : ℕ, ∀ x y : ℕ →₀ ℕ,
      (x - y).sum (fun _ c => c) + (y - x).sum (fun _ c => c) = d →
      (∃ S ⊆ I, ∑ v ∈ S, v = x) → (∃ T ⊆ I, ∑ v ∈ T, v = y) → x ≠ y →
      ∃ k : ℕ, (x k < y k ∧ ∃ S ⊆ I, ∑ v ∈ S, v = x + Finsupp.single k 1) ∨
               (y k < x k ∧ ∃ S ⊆ I, ∑ v ∈ S, v = x - Finsupp.single k 1) := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro x y hd hx hy hne
      have hd_pos : 0 < d := by
        by_contra h0
        have : d = 0 := by omega
        subst this
        exact hne ((dist_eq_zero_iff x y).mp hd)
      by_cases hd1 : d = 1
      · subst hd1
        obtain ⟨k, ⟨hlt, rfl⟩ | ⟨hgt, rfl⟩⟩ := eq_of_dist_eq_one x y hd
        · exact ⟨k, Or.inl ⟨hlt, hy⟩⟩
        · exact ⟨k, Or.inr ⟨hgt, hy⟩⟩
      · have hd2 : 2 ≤ d := by omega
        obtain ⟨z, hz, hzx, hzy, hbox⟩ := hmid x y hx hy (hd.symm ▸ hd2)
        have hadd := dist_box_add x y z hbox
        have hdz_pos : 0 < (z - y).sum (fun _ c => c) + (y - z).sum (fun _ c => c) := by
          by_contra h0
          have : (z - y).sum (fun _ c => c) + (y - z).sum (fun _ c => c) = 0 := by omega
          exact hzy ((dist_eq_zero_iff z y).mp this)
        have hlt_d : (x - z).sum (fun _ c => c) + (z - x).sum (fun _ c => c) < d := by omega
        obtain ⟨k, ⟨hlt, hs⟩ | ⟨hgt, hs⟩⟩ := ih _ hlt_d x z rfl hx hz (Ne.symm hzx)
        · have hkbox := hbox k
          exact ⟨k, Or.inl ⟨by omega, hs⟩⟩
        · have hkbox := hbox k
          exact ⟨k, Or.inr ⟨by omega, hs⟩⟩
  intro x y hx hy hne
  exact hstrong _ x y rfl hx hy hne

lemma box_mid_of_gen1 (I : Finset (ℕ →₀ ℕ))
    (hgen : ∀ x y : ℕ →₀ ℕ,
      (∃ S ⊆ I, ∑ v ∈ S, v = x) → (∃ T ⊆ I, ∑ v ∈ T, v = y) → x ≠ y →
      ∃ k : ℕ, (x k < y k ∧ ∃ S ⊆ I, ∑ v ∈ S, v = x + Finsupp.single k 1) ∨
               (y k < x k ∧ ∃ S ⊆ I, ∑ v ∈ S, v = x - Finsupp.single k 1)) :
    ∀ x y : ℕ →₀ ℕ,
      (∃ S ⊆ I, ∑ v ∈ S, v = x) → (∃ T ⊆ I, ∑ v ∈ T, v = y) →
      2 ≤ (x - y).sum (fun _ c => c) + (y - x).sum (fun _ c => c) →
      ∃ z : ℕ →₀ ℕ, (∃ U ⊆ I, ∑ v ∈ U, v = z) ∧ z ≠ x ∧ z ≠ y ∧
        ∀ k, min (x k) (y k) ≤ z k ∧ z k ≤ max (x k) (y k) := by
  intro x y hx hy hd
  have hne : x ≠ y := by
    intro heq; subst heq
    have := (dist_eq_zero_iff x x).mpr rfl
    omega
  obtain ⟨k, ⟨hlt, hz⟩ | ⟨hgt, hz⟩⟩ := hgen x y hx hy hne
  · refine ⟨x + Finsupp.single k 1, hz, ?_, ?_, ?_⟩
    · intro heq
      have := dist_add_single_one x k
      rw [heq] at this
      have h0 := (dist_eq_zero_iff x x).mpr rfl
      omega
    · intro heq
      have := dist_add_single_one x k
      rw [heq] at this
      omega
    · intro j
      simp only [Finsupp.add_apply, Finsupp.single_apply]
      split_ifs with h
      · subst h; omega
      · omega
  · refine ⟨x - Finsupp.single k 1, hz, ?_, ?_, ?_⟩
    · intro heq
      have := dist_sub_single_one x k (by omega)
      rw [heq] at this
      have h0 := (dist_eq_zero_iff x x).mpr rfl
      omega
    · intro heq
      have := dist_sub_single_one x k (by omega)
      rw [heq] at this
      omega
    · intro j
      simp only [Finsupp.tsub_apply, Finsupp.single_apply]
      split_ifs with h
      · subst h; omega
      · omega

lemma subset_sum_insert_iff (I' : Finset (ℕ →₀ ℕ)) (w x : ℕ →₀ ℕ) (hw : w ∉ I') :
    (∃ S ⊆ insert w I', ∑ v ∈ S, v = x) ↔
      (∃ S ⊆ I', ∑ v ∈ S, v = x) ∨ (∃ S ⊆ I', w + ∑ v ∈ S, v = x) := by
  constructor
  · rintro ⟨S, hS, rfl⟩
    by_cases hmem : w ∈ S
    · right
      refine ⟨S.erase w, ?_, ?_⟩
      · intro u hu
        have h1 := Finset.mem_erase.mp hu
        have h2 := Finset.mem_insert.mp (hS h1.2)
        exact h2.resolve_left h1.1
      · exact Finset.add_sum_erase S id hmem
    · left
      refine ⟨S, ?_, rfl⟩
      intro u hu
      exact (Finset.mem_insert.mp (hS hu)).resolve_left (fun heq => hmem (heq ▸ hu))
  · rintro (⟨S, hS, rfl⟩ | ⟨S, hS, rfl⟩)
    · exact ⟨S, Finset.Subset.trans hS (Finset.subset_insert w I'), rfl⟩
    · refine ⟨insert w S, Finset.insert_subset_insert w hS, ?_⟩
      rw [Finset.sum_insert (fun h => hw (hS h))]

lemma sum_pos_eq_zero_iff (u : ℕ →₀ ℕ) :
    u.sum (fun _ c => c) = 0 ↔ u = 0 := by
  rw [Finsupp.sum, Finset.sum_eq_zero_iff]
  constructor
  · intro h
    ext k
    by_cases hk : k ∈ u.support
    · exact h k hk
    · exact Finsupp.notMem_support_iff.mp hk
  · intro h k _; subst h; simp

lemma le_and_sum_eq_imp_eq (u v : ℕ →₀ ℕ) (hle : u ≤ v)
    (hsum : u.sum (fun _ c => c) = v.sum (fun _ c => c)) : u = v := by
  have hs : u.support ⊆ v.support := by
    intro k hk
    rw [Finsupp.mem_support_iff] at hk ⊢
    have := hle k; omega
  rw [sum_eq_finset_sum u v.support hs, sum_eq_finset_sum v v.support Finset.Subset.rfl] at hsum
  have hsub : ∑ k ∈ v.support, (v k - u k) = 0 := by
    have h1 : ∑ k ∈ v.support, (u k + (v k - u k)) = ∑ k ∈ v.support, v k :=
      Finset.sum_congr rfl (fun k _ => Nat.add_sub_of_le (hle k))
    rw [Finset.sum_add_distrib, hsum] at h1
    omega
  rw [Finset.sum_eq_zero_iff] at hsub
  ext k
  by_cases hk : k ∈ v.support
  · have h1 := hle k
    have h2 := hsub k hk
    omega
  · have hv : v k = 0 := Finsupp.notMem_support_iff.mp hk
    have hu := hle k
    omega

lemma sum_le_of_le (u v : ℕ →₀ ℕ) (hle : u ≤ v) :
    u.sum (fun _ c => c) ≤ v.sum (fun _ c => c) := by
  have hs : u.support ⊆ v.support := by
    intro k hk
    rw [Finsupp.mem_support_iff] at hk ⊢
    have := hle k; omega
  rw [sum_eq_finset_sum u v.support hs, sum_eq_finset_sum v v.support Finset.Subset.rfl]
  exact Finset.sum_le_sum (fun k _ => hle k)

lemma box_mid_cross (h1 : H1) (h2 : H2)
    (I' : Finset (ℕ →₀ ℕ)) (w : ℕ →₀ ℕ)
    (hI' : (0 : ℕ →₀ ℕ) ∉ I' ∧ ∀ u v, v ∈ I' → u ≤ v → u ≠ 0 → u ∈ I')
    (hI : (0 : ℕ →₀ ℕ) ∉ insert w I' ∧ ∀ u v, v ∈ insert w I' → u ≤ v → u ≠ 0 → u ∈ insert w I')
    (hw : w ∉ I')
    (hgen' : ∀ x y : ℕ →₀ ℕ,
      (∃ S ⊆ I', ∑ v ∈ S, v = x) → (∃ T ⊆ I', ∑ v ∈ T, v = y) → x ≠ y →
      ∃ k : ℕ, (x k < y k ∧ ∃ S ⊆ I', ∑ v ∈ S, v = x + Finsupp.single k 1) ∨
               (y k < x k ∧ ∃ S ⊆ I', ∑ v ∈ S, v = x - Finsupp.single k 1))
    (x y' : ℕ →₀ ℕ)
    (hx : ∃ S ⊆ I', ∑ v ∈ S, v = x)
    (hy' : ∃ T ⊆ I', ∑ v ∈ T, v = y')
    (hd : 2 ≤ (x - (w + y')).sum (fun _ c => c) + ((w + y') - x).sum (fun _ c => c)) :
    ∃ z : ℕ →₀ ℕ, (∃ U ⊆ insert w I', ∑ v ∈ U, v = z) ∧ z ≠ x ∧ z ≠ w + y' ∧
      ∀ k, min (x k) ((w + y') k) ≤ z k ∧ z k ≤ max (x k) ((w + y') k) := by
  have hsub_in : ∀ u, (∃ S ⊆ I', ∑ v ∈ S, v = u) → (∃ S ⊆ insert w I', ∑ v ∈ S, v = u) :=
    fun u hu => (subset_sum_insert_iff I' w u hw).mpr (Or.inl hu)
  have hshift_in : ∀ u, (∃ S ⊆ I', ∑ v ∈ S, v = u) →
      (∃ S ⊆ insert w I', ∑ v ∈ S, v = w + u) := by
    rintro u ⟨S, hS, rfl⟩
    exact (subset_sum_insert_iff I' w (w + ∑ v ∈ S, v) hw).mpr (Or.inr ⟨S, hS, rfl⟩)
  by_cases hG : ∃ k : ℕ, x k < y' k ∨ y' k + w k < x k
  · obtain ⟨k, ⟨hlt, hstep | hstep⟩ | ⟨hgt, hstep | hstep⟩⟩ := h1 I' w hI' hI hw hgen' x y' hx hy' hG
    · refine ⟨x + Finsupp.single k 1, hsub_in _ hstep, ?_, ?_, ?_⟩
      · intro heq
        have := dist_add_single_one x k; rw [heq] at this
        have h0 := (dist_eq_zero_iff x x).mpr rfl; omega
      · intro heq
        have := dist_add_single_one x k; rw [heq] at this; omega
      · intro j
        simp only [Finsupp.add_apply, Finsupp.single_apply]
        split_ifs with h
        · subst h; omega
        · omega
    · have hwy : w + (y' - Finsupp.single k 1) = (w + y') - Finsupp.single k 1 := by
        ext j
        simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
        split_ifs with h
        · subst h; omega
        · omega
      refine ⟨(w + y') - Finsupp.single k 1, hwy ▸ hshift_in _ hstep, ?_, ?_, ?_⟩
      · intro heq
        have := dist_sub_single_one (w + y') k (by simp [Finsupp.add_apply]; omega)
        rw [heq, dist_comm] at this; omega
      · intro heq
        have := dist_sub_single_one (w + y') k (by simp [Finsupp.add_apply]; omega)
        rw [heq] at this
        have h0 := (dist_eq_zero_iff (w + y') (w + y')).mpr rfl; omega
      · intro j
        simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
        split_ifs with h
        · subst h; omega
        · omega
    · refine ⟨x - Finsupp.single k 1, hsub_in _ hstep, ?_, ?_, ?_⟩
      · intro heq
        have := dist_sub_single_one x k (by omega); rw [heq] at this
        have h0 := (dist_eq_zero_iff x x).mpr rfl; omega
      · intro heq
        have := dist_sub_single_one x k (by omega); rw [heq] at this; omega
      · intro j
        simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
        split_ifs with h
        · subst h; omega
        · omega
    · have hwy : w + (y' + Finsupp.single k 1) = (w + y') + Finsupp.single k 1 := by
        ext j; simp [Finsupp.add_apply, add_assoc]
      refine ⟨(w + y') + Finsupp.single k 1, hwy ▸ hshift_in _ hstep, ?_, ?_, ?_⟩
      · intro heq
        have := dist_add_single_one (w + y') k
        rw [heq, dist_comm] at this; omega
      · intro heq
        have := dist_add_single_one (w + y') k
        rw [heq] at this
        have h0 := (dist_eq_zero_iff (w + y') (w + y')).mpr rfl; omega
      · intro j
        simp only [Finsupp.add_apply, Finsupp.single_apply]
        split_ifs with h
        · subst h; omega
        · omega
  · push Not at hG
    have hbet : ∀ k, y' k ≤ x k ∧ x k ≤ y' k + w k := fun k => ⟨(hG k).1, (hG k).2⟩
    have hexk : ∃ k, x k < y' k + w k := by
      by_contra hall
      push Not at hall
      have hxy : x = w + y' := by
        ext k; have := hbet k; have := hall k; simp [Finsupp.add_apply]; omega
      rw [hxy] at hd
      have h0 := (dist_eq_zero_iff (w + y') (w + y')).mpr rfl
      omega
    obtain ⟨k, hxk⟩ := hexk
    have hwk_pos : 0 < w k := by have := hbet k; omega
    let v : ℕ →₀ ℕ := w - Finsupp.single k 1
    have hv_add : v + Finsupp.single k 1 = w := by
      ext j
      simp only [v, Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
      split_ifs with h
      · subst h; omega
      · omega
    have hv_ne0 : v ≠ 0 := by
      intro hv0
      have hw1 : w = Finsupp.single k 1 := by simpa [hv0] using hv_add.symm
      have hxy' : x = y' := by
        ext j
        have hb := hbet j
        by_cases hj : j = k
        · subst hj; rw [hw1, Finsupp.single_eq_same] at hxk; omega
        · rw [hw1] at hb; simp only [Finsupp.single_apply, if_neg (Ne.symm hj)] at hb; omega
      have hd1 : (x - (w + y')).sum (fun _ c => c) + ((w + y') - x).sum (fun _ c => c) = 1 := by
        rw [hxy', hw1, add_comm (Finsupp.single k 1) y']
        exact dist_add_single_one y' k
      omega
    have hv_le : v ≤ w := by
      intro j; simp [v, Finsupp.tsub_apply]
    have hv_ne_w : v ≠ w := by
      intro heq
      have : v k = w k := congrArg (fun f => f k) heq
      simp only [v, Finsupp.tsub_apply, Finsupp.single_eq_same] at this
      omega
    have hv_in_I' : v ∈ I' := by
      have hv_in : v ∈ insert w I' :=
        hI.2 v w (Finset.mem_insert_self w I') hv_le hv_ne0
      exact (Finset.mem_insert.mp hv_in).resolve_left hv_ne_w
    have hI'_eq : insert v (I'.erase v) = I' := Finset.insert_erase hv_in_I'
    have hv_not : v ∉ I'.erase v := Finset.notMem_erase v I'
    by_cases hy'_H : ∃ S ⊆ I'.erase v, ∑ u ∈ S, u = y'
    · obtain ⟨S, hS, rfl⟩ := hy'_H
      have hz_in : ∃ U ⊆ I', ∑ u ∈ U, u = v + ∑ u ∈ S, u := by
        rw [← hI'_eq]
        exact (subset_sum_insert_iff (I'.erase v) v _ hv_not).mpr (Or.inr ⟨S, hS, rfl⟩)
      have hz_eq : v + ∑ u ∈ S, u = (w + ∑ u ∈ S, u) - Finsupp.single k 1 := by
        ext j
        simp only [v, Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
        split_ifs with h
        · subst h; omega
        · omega
      refine ⟨(w + ∑ u ∈ S, u) - Finsupp.single k 1, hsub_in _ (hz_eq ▸ hz_in), ?_, ?_, ?_⟩
      · intro heq
        have := dist_sub_single_one (w + ∑ u ∈ S, u) k (by simp [Finsupp.add_apply]; omega)
        rw [heq, dist_comm] at this; omega
      · intro heq
        have := dist_sub_single_one (w + ∑ u ∈ S, u) k (by simp [Finsupp.add_apply]; omega)
        rw [heq] at this
        have h0 := (dist_eq_zero_iff (w + ∑ u ∈ S, u) (w + ∑ u ∈ S, u)).mpr rfl; omega
      · intro j
        have hb := hbet j
        simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
        split_ifs with h
        · subst h; omega
        · omega
    · by_cases hx_vH : ∃ S ⊆ I'.erase v, v + ∑ u ∈ S, u = x
      · obtain ⟨S, hS, hSx⟩ := hx_vH
        have hS_I' : S ⊆ I' := Finset.Subset.trans hS (Finset.erase_subset v I')
        have hz_eq : w + ∑ u ∈ S, u = x + Finsupp.single k 1 := by
          rw [← hSx, ← hv_add]
          abel
        refine ⟨x + Finsupp.single k 1, hz_eq ▸ hshift_in _ ⟨S, hS_I', rfl⟩, ?_, ?_, ?_⟩
        · intro heq
          have := dist_add_single_one x k; rw [heq] at this
          have h0 := (dist_eq_zero_iff x x).mpr rfl; omega
        · intro heq
          have := dist_add_single_one x k; rw [heq] at this; omega
        · intro j
          have hb := hbet j
          simp only [Finsupp.add_apply, Finsupp.single_apply]
          split_ifs with h
          · subst h; omega
          · omega
      · have hy'_decomp : ∃ S ⊆ I'.erase v, v + ∑ u ∈ S, u = y' := by
          rw [← hI'_eq] at hy'
          exact ((subset_sum_insert_iff (I'.erase v) v y' hv_not).mp hy').resolve_left hy'_H
        have hx_H : ∃ T ⊆ I'.erase v, ∑ u ∈ T, u = x := by
          rw [← hI'_eq] at hx
          exact ((subset_sum_insert_iff (I'.erase v) v x hv_not).mp hx).resolve_right hx_vH
        obtain ⟨Sa, hSa, hSay'⟩ := hy'_decomp
        let a := ∑ u ∈ Sa, u
        have ha_H : ∃ S ⊆ I'.erase v, ∑ u ∈ S, u = a := ⟨Sa, hSa, rfl⟩
        have hav_eq : a + v = y' := by rw [add_comm]; exact hSay'
        have hav_le : a + v ≤ x := by
          intro j; rw [hav_eq]; exact (hbet j).1
        have hx_le : x ≤ a + v + v := by
          intro j
          rw [hav_eq]
          have hb := hbet j
          simp only [v, Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
          split_ifs with h
          · subst h; omega
          · omega
        have hx_ne : x ≠ a + v + v := by
          intro heq
          have hx_eq : x = (w + y') - Finsupp.single k 1 := by
            rw [heq, hav_eq]
            ext j
            simp only [v, Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
            split_ifs with h
            · subst h; omega
            · omega
          have hd1 := dist_sub_single_one (w + y') k (by simp [Finsupp.add_apply]; omega)
          rw [← hx_eq, dist_comm] at hd1
          omega
        rcases h2 I' v hI' hv_in_I' hgen' a x ha_H hx_H hav_le hx_le hx_ne with hav_in | hxv_in
        · exact absurd (hav_eq ▸ hav_in) hy'_H
        · exfalso
          obtain ⟨T, hT, hTxv⟩ := hxv_in
          refine hx_vH ⟨T, hT, ?_⟩
          rw [hTxv]
          ext j
          have h1 := hav_le j
          simp only [Finsupp.add_apply, Finsupp.tsub_apply] at h1 ⊢
          omega

lemma gen1_of_ideal (h1 : H1) (h2 : H2) :
    ∀ n : ℕ, ∀ I : Finset (ℕ →₀ ℕ), I.card = n →
      ((0 : ℕ →₀ ℕ) ∉ I ∧ ∀ u v, v ∈ I → u ≤ v → u ≠ 0 → u ∈ I) →
      ∀ x y : ℕ →₀ ℕ,
        (∃ S ⊆ I, ∑ v ∈ S, v = x) → (∃ T ⊆ I, ∑ v ∈ T, v = y) → x ≠ y →
        ∃ k : ℕ, (x k < y k ∧ ∃ S ⊆ I, ∑ v ∈ S, v = x + Finsupp.single k 1) ∨
                 (y k < x k ∧ ∃ S ⊆ I, ∑ v ∈ S, v = x - Finsupp.single k 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro I hcard hI
    by_cases hemp : I = ∅
    · subst hemp
      intro x y ⟨S, hS, hx⟩ ⟨T, hT, hy⟩ hne
      have hS0 : S = ∅ := Finset.subset_empty.mp hS
      have hT0 : T = ∅ := Finset.subset_empty.mp hT
      subst hS0; subst hT0; simp at hx hy; exact absurd (hx.symm.trans hy) hne
    · have hnon : I.Nonempty := Finset.nonempty_iff_ne_empty.mpr hemp
      obtain ⟨w, hw_mem, hw_max⟩ := Finset.exists_max_image I (fun u => u.sum (fun _ c => c)) hnon
      let I' := I.erase w
      have hw_not : w ∉ I' := Finset.notMem_erase w I
      have hI_eq : insert w I' = I := Finset.insert_erase hw_mem
      have hcard' : I'.card < n := by
        rw [← hcard]; exact Finset.card_erase_lt_of_mem hw_mem
      have hI' : (0 : ℕ →₀ ℕ) ∉ I' ∧ ∀ u v, v ∈ I' → u ≤ v → u ≠ 0 → u ∈ I' := by
        refine ⟨fun h0 => hI.1 (Finset.erase_subset w I h0), ?_⟩
        intro u v hv huv hu0
        have hvI : v ∈ I := Finset.erase_subset w I hv
        have huI : u ∈ I := hI.2 u v hvI huv hu0
        refine Finset.mem_erase.mpr ⟨?_, huI⟩
        intro huw
        subst huw
        have hle1 := sum_le_of_le u v huv
        have hle2 := hw_max v hvI
        have heq := le_and_sum_eq_imp_eq u v huv (le_antisymm hle1 hle2)
        exact (Finset.mem_erase.mp hv).1 heq.symm
      have hgen' := ih I'.card hcard' I' rfl hI'
      refine gen1_of_box_mid I (fun x y hx hy hd => ?_)
      rw [← hI_eq] at hx hy ⊢
      rcases (subset_sum_insert_iff I' w x hw_not).mp hx with hx0 | ⟨Sx, hSx, hx1⟩
      · rcases (subset_sum_insert_iff I' w y hw_not).mp hy with hy0 | ⟨Sy, hSy, hy1⟩
        · obtain ⟨z, hz, hzx, hzy, hbox⟩ := box_mid_of_gen1 I' hgen' x y hx0 hy0 hd
          exact ⟨z, (subset_sum_insert_iff I' w z hw_not).mpr (Or.inl hz), hzx, hzy, hbox⟩
        · subst hy1
          exact box_mid_cross h1 h2 I' w hI' (hI_eq.symm ▸ hI) hw_not hgen' x (∑ v ∈ Sy, v)
            hx0 ⟨Sy, hSy, rfl⟩ hd
      · rcases (subset_sum_insert_iff I' w y hw_not).mp hy with hy0 | ⟨Sy, hSy, hy1⟩
        · subst hx1
          have hd' : 2 ≤ (y - (w + ∑ v ∈ Sx, v)).sum (fun _ c => c) +
              ((w + ∑ v ∈ Sx, v) - y).sum (fun _ c => c) := by
            rw [dist_comm]; exact hd
          obtain ⟨z, hz, hzy, hzx, hbox⟩ := box_mid_cross h1 h2 I' w hI' (hI_eq.symm ▸ hI)
            hw_not hgen' y (∑ v ∈ Sx, v) hy0 ⟨Sx, hSx, rfl⟩ hd'
          refine ⟨z, hz, hzx, hzy, fun k => ?_⟩
          have hk := hbox k
          omega
        · subst hx1; subst hy1
          have hd' : 2 ≤ ((∑ v ∈ Sx, v) - (∑ v ∈ Sy, v)).sum (fun _ c => c) +
              ((∑ v ∈ Sy, v) - (∑ v ∈ Sx, v)).sum (fun _ c => c) := by
            rw [← dist_add_left w]; exact hd
          obtain ⟨z', ⟨Sz, hSz, rfl⟩, hzx', hzy', hbox'⟩ :=
            box_mid_of_gen1 I' hgen' (∑ v ∈ Sx, v) (∑ v ∈ Sy, v) ⟨Sx, hSx, rfl⟩ ⟨Sy, hSy, rfl⟩ hd'
          refine ⟨w + ∑ v ∈ Sz, v,
            (subset_sum_insert_iff I' w _ hw_not).mpr (Or.inr ⟨Sz, hSz, rfl⟩), ?_, ?_, ?_⟩
          · intro heq; exact hzx' (add_left_cancel heq)
          · intro heq; exact hzy' (add_left_cancel heq)
          · intro k
            have hk := hbox' k
            simp only [Finsupp.add_apply]
            omega

lemma factorization_prod_pow (u : ℕ →₀ ℕ)
    (hprime : ∀ q ∈ u.support, q.Prime) :
    (u.prod (· ^ ·)) ≠ 0 ∧ (u.prod (· ^ ·)).factorization = u := by
  have hne : u.prod (· ^ ·) ≠ 0 := by
    rw [Finsupp.prod, Finset.prod_ne_zero_iff]
    intro q hq
    exact pow_ne_zero _ (hprime q hq).ne_zero
  refine ⟨hne, ?_⟩
  rw [Finsupp.prod, Nat.factorization_prod (fun q hq => pow_ne_zero _ (hprime q hq).ne_zero)]
  ext p
  rw [Finsupp.finsetSum_apply]
  trans ∑ q ∈ u.support, (if q = p then u q else 0)
  · refine Finset.sum_congr rfl (fun q hq => ?_)
    rw [(hprime q hq).factorization_pow, Finsupp.single_apply]
  · simp only [Finset.sum_ite_eq']
    split_ifs with hp
    · rfl
    · exact (Finsupp.notMem_support_iff.mp hp).symm

lemma icc_factorization_ideal (n : ℕ) :
    let I := (Finset.Icc 2 n).image Nat.factorization
    (0 : ℕ →₀ ℕ) ∉ I ∧ ∀ u v, v ∈ I → u ≤ v → u ≠ 0 → u ∈ I := by
  intro I
  constructor
  · intro h0
    obtain ⟨i, hi, hfac⟩ := Finset.mem_image.mp h0
    have hi2 : 2 ≤ i := (Finset.mem_Icc.mp hi).1
    obtain ⟨q, hq_prime, hq_dvd⟩ := Nat.exists_prime_and_dvd (by omega : i ≠ 1)
    have hpos : 0 < i.factorization q :=
      hq_prime.factorization_pos_of_dvd (by omega) hq_dvd
    rw [hfac] at hpos
    simp at hpos
  · intro u v hv huv hu0
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
    have hi2 : 2 ≤ i := (Finset.mem_Icc.mp hi).1
    have hin : i ≤ n := (Finset.mem_Icc.mp hi).2
    have hprime : ∀ q ∈ u.support, q.Prime := by
      intro q hq
      have hq' : q ∈ i.factorization.support := by
        rw [Finsupp.mem_support_iff] at hq ⊢
        have := huv q; omega
      exact Nat.prime_of_mem_primeFactors (by simpa [Nat.support_factorization] using hq')
    obtain ⟨hd0, hdfac⟩ := factorization_prod_pow u hprime
    let d := u.prod (· ^ ·)
    have hd_dvd : d ∣ i :=
      (Nat.factorization_le_iff_dvd hd0 (by omega)).mp (hdfac.symm ▸ huv)
    have hd_ne1 : d ≠ 1 := by
      intro hd1
      have : u = 0 := by rw [← hdfac]; change d.factorization = 0; rw [hd1]; simp
      exact hu0 this
    have hd_ge2 : 2 ≤ d := by omega
    have hd_le : d ≤ n := le_trans (Nat.le_of_dvd (by omega) hd_dvd) hin
    exact Finset.mem_image.mpr ⟨d, Finset.mem_Icc.mpr ⟨hd_ge2, hd_le⟩, hdfac⟩

lemma mem_P_iff_subsetSums (n m : ℕ) :
    m ∈ OMA.S_oeis_a060957.P n ↔
      m ≠ 0 ∧ ∃ S ⊆ (Finset.Icc 2 n).image Nat.factorization, ∑ v ∈ S, v = m.factorization := by
  constructor
  · rintro ⟨S, hS, rfl⟩
    have hSpos : ∀ i ∈ S, i ≠ 0 := fun i hi => by have := (Finset.mem_Icc.mp (hS hi)).1; omega
    have hprod0 : ∏ i ∈ S, i ≠ 0 := Finset.prod_ne_zero_iff.mpr hSpos
    refine ⟨hprod0, (S.erase 1).image Nat.factorization, ?_, ?_⟩
    · refine Finset.image_subset_image ?_
      intro i hi
      have h1 := Finset.mem_erase.mp hi
      have h2 := Finset.mem_Icc.mp (hS h1.2)
      exact Finset.mem_Icc.mpr ⟨by omega, h2.2⟩
    · have hinj : Set.InjOn Nat.factorization (S.erase 1 : Set ℕ) := by
        intro a ha b hb hab
        have ha0 : a ≠ 0 := hSpos a (Finset.erase_subset 1 S ha)
        have hb0 : b ≠ 0 := hSpos b (Finset.erase_subset 1 S hb)
        exact Nat.factorization_inj ha0 hb0 hab
      rw [Finset.sum_image hinj]
      have hfac_erase : (∏ i ∈ S.erase 1, i).factorization = (∏ i ∈ S, i).factorization := by
        congr 1
        by_cases h1 : (1 : ℕ) ∈ S
        · have := Finset.mul_prod_erase S id h1
          simpa using this
        · rw [Finset.erase_eq_of_notMem h1]
      rw [← hfac_erase, Nat.factorization_prod (fun i hi => hSpos i (Finset.erase_subset 1 S hi))]
  · rintro ⟨hm0, S', hS', hsum⟩
    let S := (Finset.Icc 2 n).filter (fun i => i.factorization ∈ S')
    have hS_icc : S ⊆ Finset.Icc 1 n := by
      intro i hi
      have h1 := Finset.mem_Icc.mp (Finset.mem_filter.mp hi).1
      exact Finset.mem_Icc.mpr ⟨by omega, h1.2⟩
    have himg : S.image Nat.factorization = S' := by
      ext v
      constructor
      · intro hv
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
        exact (Finset.mem_filter.mp hi).2
      · intro hv
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hS' hv)
        exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hv⟩, rfl⟩
    have hSpos : ∀ i ∈ S, i ≠ 0 := fun i hi => by
      have := (Finset.mem_Icc.mp (hS_icc hi)).1; omega
    have hinj : Set.InjOn Nat.factorization (S : Set ℕ) := by
      intro a ha b hb hab
      exact Nat.factorization_inj (hSpos a ha) (hSpos b hb) hab
    have hsum_eq : ∑ i ∈ S, i.factorization = ∑ v ∈ S.image Nat.factorization, v :=
      (Finset.sum_image (f := id) hinj).symm
    have hprod_fac : (∏ i ∈ S, i).factorization = m.factorization := by
      rw [Nat.factorization_prod hSpos, hsum_eq, himg, hsum]
    have hprod0 : ∏ i ∈ S, i ≠ 0 := Finset.prod_ne_zero_iff.mpr hSpos
    exact ⟨S, hS_icc, Nat.factorization_inj hprod0 hm0 hprod_fac⟩

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a060957.main := by
  intro h1 h2 n p a m k hp _ hm hpm _ hka
  let I := (Finset.Icc 2 n).image Nat.factorization
  have hgen := gen1_of_ideal h1 h2 I.card I rfl (icc_factorization_ideal n)
  have hstep : ∀ j ≤ a, p ^ j * m ∈ OMA.S_oeis_a060957.P n := by
    intro j
    induction j with
    | zero =>
      intro _; simpa using hm
    | succ j ih =>
      intro hja
      have hj : p ^ j * m ∈ OMA.S_oeis_a060957.P n := ih (by omega)
      obtain ⟨hmj0, hxj⟩ := (mem_P_iff_subsetSums n (p ^ j * m)).mp hj
      obtain ⟨hma0, hxa⟩ := (mem_P_iff_subsetSums n (p ^ a * m)).mp hpm
      have hm0 : m ≠ 0 := by
        intro h0; subst h0; simp at hmj0
      have hfac_j : (p ^ j * m).factorization = m.factorization + Finsupp.single p j := by
        rw [Nat.factorization_mul (pow_ne_zero j hp.ne_zero) hm0, hp.factorization_pow, add_comm]
      have hfac_a : (p ^ a * m).factorization = m.factorization + Finsupp.single p a := by
        rw [Nat.factorization_mul (pow_ne_zero a hp.ne_zero) hm0, hp.factorization_pow, add_comm]
      have hne : (p ^ j * m).factorization ≠ (p ^ a * m).factorization := by
        intro heq
        have hval := congrArg (fun f => f p) heq
        rw [hfac_j, hfac_a] at hval
        simp only [Finsupp.add_apply, Finsupp.single_eq_same] at hval
        omega
      obtain ⟨q, ⟨hlt, hstep_q⟩ | ⟨hgt, _⟩⟩ := hgen _ _ hxj hxa hne
      · have hqp : q = p := by
          by_contra hne_q
          rw [hfac_j, hfac_a] at hlt
          simp only [Finsupp.add_apply, Finsupp.single_apply, if_neg (Ne.symm hne_q)] at hlt
          omega
        rw [hqp] at hstep_q
        have hfac_succ : (p ^ (j + 1) * m).factorization =
            (p ^ j * m).factorization + Finsupp.single p 1 := by
          rw [Nat.factorization_mul (pow_ne_zero (j + 1) hp.ne_zero) hm0, hp.factorization_pow,
            hfac_j, add_assoc, ← Finsupp.single_add, add_comm]
        refine (mem_P_iff_subsetSums n (p ^ (j + 1) * m)).mpr ?_
        refine ⟨mul_ne_zero (pow_ne_zero (j + 1) hp.ne_zero) hm0, ?_⟩
        rw [hfac_succ]
        exact hstep_q
      · exfalso
        rw [hfac_j, hfac_a] at hgt
        by_cases hqp : q = p
        · rw [hqp] at hgt
          simp only [Finsupp.add_apply, Finsupp.single_eq_same] at hgt
          omega
        · simp only [Finsupp.add_apply, Finsupp.single_apply, if_neg (Ne.symm hqp)] at hgt
          omega
  exact hstep k (le_of_lt hka)

end OMA.R_oeis_a060957_R1
