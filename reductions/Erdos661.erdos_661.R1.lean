import FormalConjectures.ErdosProblems.«661»
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
An approximate squared-distance table suffices if its exceptional entries have
small matching number. The construction step is a rank-constrained matrix
completion problem. The other step is the planar realization of Gram matrices.
Credit: @ubuwaits.
-/

namespace OMA.R_Erdos661_erdos_661_R1

open Filter EuclideanGeometry

/-- Find a positive semidefinite matrix of rank at most two with distinct
represented points. Its cross block may contain entries outside the palette.
No matching of exceptional entries may have more than `n` edges. -/
def H1 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
    let I := Fin (2 * n)
    ∃ (G : Matrix (I ⊕ I) (I ⊕ I) ℝ) (D : Finset ℝ),
      G.PosSemidef ∧ G.rank ≤ 2 ∧
      (D.card : ℝ) ≤ ε * ((n : ℝ) / (Real.log n).sqrt) ∧
      let q (i j : I ⊕ I) := G i i + G j j - 2 * G i j
      (∀ i j, i ≠ j → 0 < q i j) ∧
      ∀ M : Finset (I × I), Set.InjOn Prod.fst (M : Set (I × I)) →
        Set.InjOn Prod.snd (M : Set (I × I)) →
        (∀ e ∈ M, q (.inl e.1) (.inr e.2) ∉ D) → M.card ≤ n

/-- Realize the squared-distance table of a rank-at-most-two Gram matrix
in the Euclidean plane, including the singular and zero-rank cases. -/
def H2 : Prop :=
  ∀ m : ℕ, ∀ G : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ,
    G.PosSemidef → G.rank ≤ 2 →
    ∃ x : (Fin m ⊕ Fin m) → ℝ², ∀ i j,
      dist (x i) (x j) ^ 2 = G i i + G j j - 2 * G i j

lemma clean_rectangle (n : ℕ) (bad : Finset (Fin (2*n) × Fin (2*n)))
    (small : ∀ M ⊆ bad, Set.InjOn Prod.fst (M : Set (Fin (2*n) × Fin (2*n))) →
      Set.InjOn Prod.snd (M : Set (Fin (2*n) × Fin (2*n))) → M.card ≤ n) :
    ∃ R S : Finset (Fin (2*n)), R.card = n ∧ S.card = n ∧
      ∀ i ∈ R, ∀ j ∈ S, (i,j) ∉ bad := by
  classical
  let matchings := bad.powerset.filter fun M : Finset (Fin (2*n) × Fin (2*n)) =>
    Set.InjOn Prod.fst (M : Set (Fin (2*n) × Fin (2*n))) ∧
    Set.InjOn Prod.snd (M : Set (Fin (2*n) × Fin (2*n)))
  have empty_mem : ∅ ∈ matchings := by simp [matchings]
  obtain ⟨M, hM, maximal⟩ := matchings.exists_max_image Finset.card ⟨∅, empty_mem⟩
  obtain ⟨hsub, hrow, hcol⟩ := Finset.mem_filter.mp hM
  have sub := Finset.mem_powerset.mp hsub
  have size := small M sub hrow hcol
  let rows := M.image Prod.fst
  let cols := M.image Prod.snd
  have room (U : Finset (Fin (2*n))) (hU : U.card ≤ n) : n ≤ Uᶜ.card := by
    rw [Finset.card_compl, Fintype.card_fin]
    omega
  obtain ⟨R, hR, rcard⟩ := Finset.exists_subset_card_eq
    (room rows (Finset.card_image_le.trans size))
  obtain ⟨S, hS, scard⟩ := Finset.exists_subset_card_eq
    (room cols (Finset.card_image_le.trans size))
  refine ⟨R, S, rcard, scard, ?_⟩
  intro i hi j hj edge
  have freshRow : i ∉ rows := Finset.mem_compl.mp (hR hi)
  have freshCol : j ∉ cols := Finset.mem_compl.mp (hS hj)
  have newEdge : (i,j) ∉ M := fun h => freshRow (Finset.mem_image_of_mem Prod.fst h)
  have extended : insert (i,j) M ∈ matchings := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr (Finset.insert_subset edge sub), ?_, ?_⟩
    · rw [Finset.coe_insert, Set.injOn_insert newEdge]
      exact ⟨hrow, by simpa [rows] using freshRow⟩
    · rw [Finset.coe_insert, Set.injOn_insert newEdge]
      exact ⟨hcol, by simpa [cols] using freshCol⟩
  have contradiction := maximal _ extended
  simp [Finset.card_insert_of_notMem newEdge] at contradiction

lemma bound_of_table {n : ℕ} {D : Finset ℝ} {x : (Fin (2*n) ⊕ Fin (2*n)) → ℝ²}
    (inj : Function.Injective x)
    (small : ∀ M : Finset (Fin (2*n) × Fin (2*n)),
      Set.InjOn Prod.fst (M : Set (Fin (2*n) × Fin (2*n))) → Set.InjOn Prod.snd (M : Set (Fin (2*n) × Fin (2*n))) →
      (∀ e ∈ M, dist (x (.inl e.1)) (x (.inr e.2)) ^ 2 ∉ D) → M.card ≤ n) :
    Erdos661.minimalCrossDistances ℝ² n ≤ D.card := by
  classical
  let bad := Finset.univ.filter fun e : Fin (2*n) × Fin (2*n) =>
    dist (x (.inl e.1)) (x (.inr e.2)) ^ 2 ∉ D
  obtain ⟨R, S, hR, hS, good⟩ := clean_rectangle n bad fun M sub hr hc =>
    small M hr hc fun e he => (Finset.mem_filter.mp (sub he)).2
  let A := R.image (fun i => x (.inl i))
  let B := S.image (fun j => x (.inr j))
  have cardA : A.card = n := (Finset.card_image_of_injective R
    (inj.comp Sum.inl_injective)).trans hR
  have cardB : B.card = n := (Finset.card_image_of_injective S
    (inj.comp Sum.inr_injective)).trans hS
  have sep : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro z hz hw
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨j, _, eq⟩ := Finset.mem_image.mp hw
    cases inj eq
  apply (Nat.sInf_le (s := {k | ∃ A B : Finset ℝ²,
    A.card = n ∧ B.card = n ∧ Disjoint A B ∧ (Erdos661.crossDistanceSet A B).card = k})
    ⟨A, B, cardA, cardB, sep, rfl⟩).trans
  apply (Finset.card_le_card (t := D.image Real.sqrt) ?_).trans Finset.card_image_le
  intro d hd
  obtain ⟨⟨a,b⟩, hab, rfl⟩ := Finset.mem_image.mp hd
  obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
  have ok : dist (x (.inl i)) (x (.inr j)) ^ 2 ∈ D := by
    by_contra h
    exact good i hi j hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  exact Finset.mem_image.mpr ⟨_, ok, Real.sqrt_sq dist_nonneg⟩

theorem main : H1 → H2 → type_of% @Erdos661.erdos_661 := by
  intro construct realize
  apply Asymptotics.isLittleO_iff.mpr
  intro ε hε
  filter_upwards [construct ε hε] with n hn
  obtain ⟨G, D, psd, rank, short, sep, small⟩ := hn
  obtain ⟨x, hx⟩ := realize (2*n) G psd rank
  have inj : Function.Injective x := by
    intro i j eq
    by_contra ne
    have pos := sep i j ne
    dsimp only at pos
    rw [← hx, eq, dist_self] at pos
    norm_num at pos
  have bound := bound_of_table (D := D) inj fun M hr hc hbad =>
    small M hr hc fun e he => by simpa only [hx] using hbad e he
  simp only [Real.norm_eq_abs, Nat.abs_cast,
    abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _))]
  exact (by exact_mod_cast bound : (Erdos661.minimalCrossDistances ℝ² n : ℝ) ≤ D.card).trans short

end OMA.R_Erdos661_erdos_661_R1
