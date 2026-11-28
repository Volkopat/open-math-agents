import OMAStatements.S_oeis_a098052

/-! Finite lower sets in four dimensions with exactly four one-point extensions are boxes. -/
-- Credit: @STARDUSTLC666

namespace SolidBoxes

open Finset OMA.S_oeis_a098052

private abbrev Point := ℕ × ℕ × ℕ × ℕ
private def coord (x : Point) : Fin 4 → ℕ := ![x.1, x.2.1, x.2.2.1, x.2.2.2]
private def point (f : Fin 4 → ℕ) : Point := (f 0, f 1, f 2, f 3)

private lemma coord_point (f : Fin 4 → ℕ) (i : Fin 4) : coord (point f) i = f i := by
  fin_cases i <;> rfl

private lemma point_ext {x y : Point} (h : ∀ i, coord x i = coord y i) : x = y := by
  obtain ⟨a,b,c,d⟩ := x
  obtain ⟨a',b',c',d'⟩ := y
  exact Prod.ext (h 0) (Prod.ext (h 1) (Prod.ext (h 2) (h 3)))

private def Below (x y : Point) : Prop := ∀ i, coord x i ≤ coord y i
private def Lower (S : Finset Point) : Prop := ∀ x ∈ S, ∀ y, Below y x → y ∈ S
private def Positive (t : Point) : Prop := ∀ i, 0 < coord t i
private def volume (t : Point) : ℕ := t.1*t.2.1*t.2.2.1*t.2.2.2

private lemma solid_iff {n : ℕ} {S : Finset Point} :
    IsSolidPartition n S ↔ S.card = n ∧ Lower S := by
  constructor
  · rintro ⟨hc,h⟩
    refine ⟨hc, ?_⟩
    rintro ⟨a,b,c,d⟩ hx ⟨a',b',c',d'⟩ hy
    exact h a b c d a' b' c' d' hx (hy 0) (hy 1) (hy 2) (hy 3)
  · rintro ⟨hc,h⟩
    refine ⟨hc, ?_⟩
    intro a b c d a' b' c' d' hx ha hb hc' hd
    apply h _ hx (a',b',c',d')
    intro i
    fin_cases i <;> assumption

private def box (t : Point) : Finset Point :=
  range t.1 ×ˢ (range t.2.1 ×ˢ (range t.2.2.1 ×ˢ range t.2.2.2))

private lemma mem_box {t x : Point} : x ∈ box t ↔ ∀ i, coord x i < coord t i := by
  simp only [box, mem_product, mem_range]
  constructor
  · rintro ⟨ha,hb,hc,hd⟩ i
    fin_cases i <;> assumption
  · intro h
    exact ⟨h 0, h 1, h 2, h 3⟩

private lemma box_lower (t : Point) : Lower (box t) := by
  intro x hx y hy
  exact mem_box.mpr (fun i => (hy i).trans_lt (mem_box.mp hx i))

private lemma card_box (t : Point) : (box t).card = volume t := by
  simp [box, volume, Nat.mul_assoc]

private def axial (i : Fin 4) (k : ℕ) : Point := point (fun j => if j = i then k else 0)

private lemma axial_coord (i : Fin 4) (k : ℕ) (j : Fin 4) :
    coord (axial i k) j = if j = i then k else 0 := coord_point _ _

private lemma axial_below {i : Fin 4} {k : ℕ} {x : Point} (hk : k ≤ coord x i) :
    Below (axial i k) x := by
  intro j
  rw [axial_coord]
  split <;> simp_all

private lemma missing_axis (S : Finset Point) (i : Fin 4) : ∃ k, axial i k ∉ S := by
  refine ⟨S.sup (fun x => coord x i) + 1, ?_⟩
  intro h
  have bound := Finset.le_sup (f := fun x => coord x i) h
  rw [axial_coord, if_pos rfl] at bound
  exact (Nat.not_succ_le_self _) bound

private noncomputable def width (S : Finset Point) (i : Fin 4) : ℕ :=
  Nat.find (missing_axis S i)

private lemma outside (S : Finset Point) (i : Fin 4) : axial i (width S i) ∉ S :=
  Nat.find_spec (missing_axis S i)

private lemma earlier {S : Finset Point} {i : Fin 4} {k : ℕ} (hk : k < width S i) :
    axial i k ∈ S := not_not.mp (Nat.find_min (missing_axis S i) hk)

private lemma fits {S : Finset Point} (low : Lower S) :
    S ⊆ box (point (width S)) := by
  intro x hx
  apply mem_box.mpr
  intro i
  rw [coord_point]
  by_contra! h
  exact outside S i (low x hx _ (axial_below h))

private lemma widths_pos {S : Finset Point} (low : Lower S) (hs : S.Nonempty) :
    ∀ i, 0 < width S i := by
  obtain ⟨x,hx⟩ := hs
  intro i
  exact (Nat.zero_le _).trans_lt (by simpa only [coord_point] using mem_box.mp (fits low hx) i)

private def Addable (S : Finset Point) (x : Point) : Prop :=
  x ∉ S ∧ ∀ y, Below y x → y ≠ x → y ∈ S

private lemma extension_count {n : ℕ} {S : Finset Point} (solid : IsSolidPartition n S) :
    numExtensions n S = {x | Addable S x}.ncard := by
  classical
  obtain ⟨card,low⟩ := solid_iff.mp solid
  let f (x : Point) := insert x S
  have img : {U | IsSolidPartition (n+1) U ∧ S ⊆ U} = f '' {x | Addable S x} := by
    ext U
    constructor
    · rintro ⟨hU,sub⟩
      obtain ⟨size,down⟩ := solid_iff.mp hU
      obtain ⟨x,out,rfl⟩ := Finset.exists_eq_insert_iff.mpr ⟨sub, by omega⟩
      refine ⟨x, ⟨out, ?_⟩, rfl⟩
      intro y hy ne
      exact (mem_insert.mp (down x (mem_insert_self _ _) y hy)).resolve_left ne
    · rintro ⟨x,hx,rfl⟩
      refine ⟨solid_iff.mpr ⟨?_, ?_⟩, subset_insert _ _⟩
      · simp only [f, card_insert_of_notMem hx.1, card]
      · intro v hv y hy
        rcases mem_insert.mp hv with rfl | old
        · by_cases eq : y = v
          · exact mem_insert.mpr (.inl eq)
          · exact mem_insert_of_mem (hx.2 y hy eq)
        · exact mem_insert_of_mem (low v old y hy)
  have inj : Set.InjOn f {x | Addable S x} := by
    intro x hx y hy eq
    have mem : x ∈ f y := eq ▸ mem_insert_self x S
    exact (mem_insert.mp mem).resolve_right hx.1
  rw [numExtensions, img, inj.ncard_image]

private lemma axial_addable (S : Finset Point) (i : Fin 4) :
    Addable S (axial i (width S i)) := by
  refine ⟨outside S i, ?_⟩
  intro x hx ne
  have eq : x = axial i (coord x i) := by
    apply point_ext
    intro j
    have le := hx j
    rw [axial_coord] at le ⊢
    split <;> simp_all
  have le : coord x i ≤ width S i := by simpa [axial_coord] using hx i
  have lt : coord x i < width S i := lt_of_le_of_ne le (fun h => ne (h ▸ eq))
  exact eq ▸ earlier lt

private noncomputable def ends (S : Finset Point) : Finset Point :=
  univ.image (fun i => axial i (width S i))

private lemma end_mem {S : Finset Point} {x : Point} :
    x ∈ ends S ↔ ∃ i, axial i (width S i) = x := by simp [ends]

private lemma card_ends {S : Finset Point} (pos : ∀ i, 0 < width S i) : (ends S).card = 4 := by
  have inj : Function.Injective (fun i => axial i (width S i)) := by
    intro i j eq
    by_contra ne
    have same := congrArg (fun x => coord x i) eq
    simp [axial_coord, ne, (pos i).ne'] at same
  rw [ends, card_image_of_injective _ inj]
  decide

private lemma ends_subset (S : Finset Point) : (ends S : Set Point) ⊆ {x | Addable S x} := by
  intro x hx
  obtain ⟨i,rfl⟩ := end_mem.mp hx
  exact axial_addable S i

private def weight (x : Point) := x.1 + x.2.1 + x.2.2.1 + x.2.2.2

private lemma lighter {x y : Point} (below : Below y x) (ne : y ≠ x) : weight y < weight x := by
  obtain ⟨a,b,c,d⟩ := x
  obtain ⟨a',b',c',d'⟩ := y
  have ha : a' ≤ a := below 0
  have hb : b' ≤ b := below 1
  have hc : c' ≤ c := below 2
  have hd : d' ≤ d := below 3
  change a'+b'+c'+d' < a+b+c+d
  by_contra! h
  exact ne (Prod.ext (show a' = a by omega) (Prod.ext (show b' = b by omega)
    (Prod.ext (show c' = c by omega) (show d' = d by omega))))

-- A hole in the bounding box of a lower set gives an extra addable point.
private lemma full_if_four {n : ℕ} {S : Finset Point} (posn : 0 < n)
    (solid : IsSolidPartition n S) (four : numExtensions n S = 4) :
    S = box (point (width S)) := by
  classical
  obtain ⟨card,low⟩ := solid_iff.mp solid
  have pos := widths_pos low (Finset.card_pos.mp (by omega))
  rw [extension_count solid] at four
  have ends_eq : (ends S : Set Point) = {x | Addable S x} :=
    Set.eq_of_subset_of_ncard_le (ends_subset S)
      (by rw [four, Set.ncard_coe_finset, card_ends pos]) (Set.finite_of_ncard_pos (by omega))
  apply Finset.Subset.antisymm (fits low)
  intro x hx
  by_contra absent
  let holes := box (point (width S)) \ S
  have nonempty : holes.Nonempty := ⟨x, mem_sdiff.mpr ⟨hx,absent⟩⟩
  obtain ⟨y,hy,least⟩ := exists_min_image holes weight nonempty
  obtain ⟨inside,missing⟩ := mem_sdiff.mp hy
  have addable : Addable S y := by
    refine ⟨missing, ?_⟩
    intro z hz ne
    by_contra mz
    have inholes : z ∈ holes := mem_sdiff.mpr ⟨box_lower _ y inside z hz, mz⟩
    exact (not_lt_of_ge (least z inholes)) (lighter hz ne)
  have member : y ∈ ends S := by
    change y ∈ (ends S : Set Point)
    rw [ends_eq]
    exact addable
  obtain ⟨i,eq⟩ := end_mem.mp member
  have bad := mem_box.mp inside i
  rw [← eq, axial_coord, if_pos rfl, coord_point] at bad
  exact (Nat.lt_irrefl _) bad

private lemma width_box {t : Point} (pos : Positive t) (i : Fin 4) :
    width (box t) i = coord t i := by
  apply le_antisymm
  · apply Nat.find_min' (missing_axis _ i)
    intro h
    have bad := mem_box.mp h i
    simp [axial_coord] at bad
  · by_contra! h
    apply outside (box t) i
    apply mem_box.mpr
    intro j
    rw [axial_coord]
    split
    · next e => simpa [e] using h
    · exact pos j

private lemma four_on_box {n : ℕ} {t : Point} (pos : Positive t) (size : volume t = n) :
    IsSolidPartition n (box t) ∧ numExtensions n (box t) = 4 := by
  have solid := solid_iff.mpr ⟨(card_box t).trans size, box_lower t⟩
  refine ⟨solid, ?_⟩
  rw [extension_count solid]
  have same : {x | Addable (box t) x} = (ends (box t) : Set Point) := by
    apply Set.Subset.antisymm _ (ends_subset _)
    intro x hx
    have out := hx.1
    rw [mem_box] at out
    push Not at out
    obtain ⟨i,ge⟩ := out
    apply end_mem.mpr
    refine ⟨i, ?_⟩
    by_contra ne
    apply outside (box t) i
    exact hx.2 _ (axial_below (by rwa [width_box pos])) ne
  rw [same, Set.ncard_coe_finset, card_ends (fun i => (width_box pos i).symm ▸ pos i)]

end SolidBoxes

open SolidBoxes OMA.S_oeis_a098052

theorem OMA.solution : type_of% @OMA.S_oeis_a098052.main := by
  intro n hn
  let lengths : Set Point := {t | Positive t ∧ volume t = n}
  have indexed : {S : Finset Point | IsSolidPartition n S ∧ numExtensions n S = 1+3} =
      box '' lengths := by
    ext S
    constructor
    · rintro ⟨solid,four⟩
      have eq := full_if_four hn solid four
      obtain ⟨hc,low⟩ := solid_iff.mp solid
      have pos := widths_pos low (Finset.card_pos.mp (by omega))
      refine ⟨point (width S), ⟨fun i => by simpa only [coord_point] using pos i, ?_⟩, eq.symm⟩
      rw [← card_box, ← eq, hc]
    · rintro ⟨t,ht,rfl⟩
      exact four_on_box ht.1 ht.2
  have inj : Set.InjOn box lengths := by
    intro a ha b hb eq
    apply point_ext
    intro i
    rw [← width_box ha.1 i, ← width_box hb.1 i, eq]
  have literal : lengths = {t : Point | 0 < t.1 ∧ 0 < t.2.1 ∧ 0 < t.2.2.1 ∧ 0 < t.2.2.2 ∧
      t.1*t.2.1*t.2.2.1*t.2.2.2 = n} := by
    ext t
    constructor
    · rintro ⟨h,v⟩
      exact ⟨h 0,h 1,h 2,h 3,v⟩
    · rintro ⟨a,b,c,d,v⟩
      refine ⟨?_,v⟩
      intro i
      fin_cases i <;> assumption
  rw [T, indexed, inj.ncard_image, literal, tau4]
