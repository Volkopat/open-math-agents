import FormalConjectures.ErdosProblems.«723»

/-!
Puncture a projective plane at a line, then discard two directions. The
remaining array has n² rows, n-1 columns and n symbols. Any two columns
determine a row uniquely. At order 12 this leaves 11 columns (nine Latin
squares). Bruck's completion theorem, Finite nets II, Theorem 4.3,
shows that for n > 4 such a deficiency-two net can always be completed.
Only the elementary forward construction is needed for this reduction.
-/

namespace OMA.R_Erdos723_erdos_723_R1

open Configuration

/-- The small-order theorem, including the computational result at ten. -/
def H1 : Prop :=
  ∀ {P L : Type} [Membership P L] [Fintype P] [Fintype L] (pp : ProjectivePlane P L),
    pp.order ≤ 11 → IsPrimePow pp.order

/-- The Bruck-Ryser necessary condition. -/
def H2 : Prop :=
  ∀ {P L : Type} [Membership P L] [Fintype P] [Fintype L] (pp : ProjectivePlane P L),
    pp.order % 4 = 1 ∨ pp.order % 4 = 2 →
    ∃ a b : ℕ, pp.order = a ^ 2 + b ^ 2

/-- A purely finite-array obstruction, restricted to the surviving orders. -/
def H3 : Prop :=
  ∀ n : ℕ, 12 ≤ n → ¬ IsPrimePow n →
    (n % 4 = 1 ∨ n % 4 = 2 → ∃ a b : ℕ, n = a ^ 2 + b ^ 2) →
    ∀ A : Fin (n ^ 2) → Fin (n - 1) → Fin n,
      ∃ x y i j, x ≠ y ∧ i ≠ j ∧ A x i = A y i ∧ A x j = A y j

theorem array_of_plane {P L : Type} [Membership P L] [Fintype P] [Fintype L]
    (pp : ProjectivePlane P L) (k : ℕ) (hk : k ≤ pp.order + 1) :
    ∃ A : Fin (pp.order ^ 2) → Fin k → Fin pp.order,
      ∀ x y i j, i ≠ j → A x i = A y i → A x j = A y j → x = y := by
  classical
  let _ : ProjectivePlane P L := pp
  let n := pp.order
  obtain ⟨_, _, _, horizon, _⟩ := pp.exists_config
  let Direction := {p : P // p ∈ horizon}
  let Affine := {p : P // p ∉ horizon}
  have dirCard : Fintype.card Direction = n + 1 := by
    simpa [Direction, pointCount, Nat.card_eq_fintype_card, n] using
      ProjectivePlane.pointCount_eq P horizon
  have affCard : Fintype.card Affine = n ^ 2 := by
    change Fintype.card {p : P // ¬ p ∈ horizon} = n ^ 2
    rw [Fintype.card_subtype_compl (fun p : P => p ∈ horizon), ProjectivePlane.card_points P L]
    change n ^ 2 + n + 1 - Fintype.card Direction = n ^ 2
    rw [dirCard]
    omega
  let labelDir := Fintype.equivFinOfCardEq dirCard
  let labelAff := Fintype.equivFinOfCardEq affCard
  let dir (i : Fin k) : Direction := labelDir.symm (Fin.castLE hk i)
  have dirInj : Function.Injective dir := by
    intro i j h
    exact Fin.ext (congrArg (fun t : Fin (pp.order + 1) => t.val) (labelDir.symm.injective h))
  let Pencil (d : Direction) := {l : {l : L // d.val ∈ l} // l.val ≠ horizon}
  have pencilCard (d : Direction) : Fintype.card (Pencil d) = n := by
    let base : {l : L // d.val ∈ l} := ⟨horizon, d.property⟩
    have hcard : Fintype.card {l : L // d.val ∈ l} = n + 1 := by
      simpa [lineCount, Nat.card_eq_fintype_card, n] using ProjectivePlane.lineCount_eq L d.val
    have hb : ∀ l : {l : L // d.val ∈ l}, l.val ≠ horizon ↔ l ≠ base := by
      intro l
      change l.val ≠ base.val ↔ l ≠ base
      exact not_congr (Subtype.ext_iff (a1 := l) (a2 := base)).symm
    change Fintype.card {l : {l : L // d.val ∈ l} // l.val ≠ horizon} = n
    rw [Fintype.card_congr (Equiv.subtypeEquivRight hb),
      Fintype.card_subtype_compl (fun l => l = base), Fintype.card_subtype_eq, hcard]
    omega
  let label (d : Direction) := Fintype.equivFinOfCardEq (pencilCard d)
  have apart (x : Affine) (d : Direction) : x.val ≠ d.val :=
    fun h => x.property (h ▸ d.property)
  let ray (x : Affine) (d : Direction) : Pencil d :=
    ⟨⟨HasLines.mkLine (L := L) (apart x d), (HasLines.mkLine_ax (L := L) (apart x d)).2⟩,
      by
        intro h
        apply x.property
        change HasLines.mkLine (L := L) (apart x d) = horizon at h
        exact (congrArg (fun l : L => x.val ∈ l) h).mp
          (HasLines.mkLine_ax (L := L) (apart x d)).1⟩
  have hit (x : Affine) (d : Direction) : x.val ∈ (ray x d).val.val :=
    (HasLines.mkLine_ax (L := L) (apart x d)).1
  refine ⟨fun x i => label (dir i) (ray (labelAff.symm x) (dir i)), ?_⟩
  intro x y i j hij hi hj
  let u := labelAff.symm x
  let v := labelAff.symm y
  have same (d : Direction) (h : ray u d = ray v d) : v.val ∈ (ray u d).val.val :=
    h ▸ hit v d
  have eqi := (label (dir i)).injective hi
  have eqj := (label (dir j)).injective hj
  have distinct : (ray u (dir i)).val.val ≠ (ray u (dir j)).val.val := by
    intro h
    have also : (dir j).val ∈ (ray u (dir i)).val.val := h ▸ (ray u (dir j)).val.property
    have e := Nondegenerate.eq_or_eq (dir i).property (dir j).property
      (ray u (dir i)).val.property also
    exact hij (dirInj (Subtype.ext (e.resolve_right (Ne.symm (ray u (dir i)).property))))
  have uv := (Nondegenerate.eq_or_eq (hit u (dir i)) (same (dir i) eqi)
    (hit u (dir j)) (same (dir j) eqj)).resolve_right distinct
  exact labelAff.symm.injective (Subtype.ext uv)

theorem main : H1 → H2 → H3 → type_of% @Erdos723.erdos_723 := by
  intro small ryser obstruction P L mem fp fl pp
  let n := pp.order
  by_cases hn : n ≤ 11
  · exact small pp hn
  · by_contra h
    obtain ⟨A, hA⟩ := array_of_plane pp (n - 1) (by dsimp [n]; omega)
    obtain ⟨x, y, i, j, hxy, hij, hi, hj⟩ :=
      obstruction n (by omega) h (ryser pp) A
    exact hxy (hA x y i j hij hi hj)

end OMA.R_Erdos723_erdos_723_R1
