import OMAStatements.S_oeis_a096597

/-!
# The outer diagonals of the plane-partition triangle A096597

Write m = n − k with k < n/2. An order ideal of n unit cubes that just
fits in an m-cube has a unique axis of length m. Two such axes would
already use 2m−1 > n cubes. The three choices give equal counts.

After choosing the vertical axis, delete its m cubes. The remainder
is a plane partition of k on the quadrant with its corner removed.
Conversely, every such remainder fits when the axis is restored.

For this last enumeration we formalize the one-cell specialization of
the modified jeu de taquin of Kadell used by Bruce E. Sagan. The hole starts at the missing
corner. An east move preserves weight and a south move removes one unit.
At the terminal hole in row d, the filled array is an ordinary plane
partition of k−d. The inverse starts at the first zero of row d. The
local inverse and strictly decreasing measures are proved in both
directions. Summing over d gives the claimed partial sum.

Source: https://oeis.org/A096597
Sagan, Combinatorial proofs of hook generating functions for skew plane
partitions, Theoretical Computer Science 117 (1993), 273–287, Theorem 2.1.
https://doi.org/10.1016/0304-3975(93)90319-O
-/

namespace Plane597

abbrev P3 := ℕ × ℕ × ℕ
def Ideal (S : Finset P3) : Prop := ∀ p ∈ S, ∀ q, q ≤ p → q ∈ S
def InCube (S : Finset P3) (m : ℕ) : Prop :=
  ∀ p ∈ S, p.1 < m ∧ p.2.1 < m ∧ p.2.2 < m

end Plane597

namespace Plane597

open OMA.S_oeis_a096597

private def flattenColumn : (Σ _ : ℕ × ℕ, ℕ) ↪ P3 where
  toFun v := (v.1.1, v.1.2, v.2)
  inj' := by
    rintro ⟨⟨a,b⟩,c⟩ ⟨⟨d,e⟩,f⟩ h
    change (a,b,c) = (d,e,f) at h
    obtain rfl : a = d := congrArg Prod.fst h
    obtain rfl : b = e := congrArg (fun v : P3 => v.2.1) h
    obtain rfl : c = f := congrArg (fun v : P3 => v.2.2) h
    rfl

def shape (n : ℕ) (π : ℕ × ℕ → ℕ) : Finset P3 :=
  (((Finset.range n) ×ˢ (Finset.range n)).sigma (fun b => Finset.range (π b))).map flattenColumn

theorem mem_shape_raw {n i j z : ℕ} {π : ℕ × ℕ → ℕ} :
    (i,j,z) ∈ shape n π ↔ i < n ∧ j < n ∧ z < π (i,j) := by
  simp only [shape, Finset.mem_map, Finset.mem_sigma, Finset.mem_product, Finset.mem_range]
  constructor
  · rintro ⟨⟨⟨u,v⟩,w⟩, ⟨⟨hu,hv⟩,hw⟩, eq⟩
    change (u,v,w) = (i,j,z) at eq
    cases eq
    exact ⟨hu,hv,hw⟩
  · rintro ⟨hi,hj,hz⟩
    exact ⟨⟨(i,j),z⟩, ⟨⟨hi,hj⟩,hz⟩, rfl⟩

theorem mem_shape {n i j z : ℕ} {π : ℕ × ℕ → ℕ} (h : IsPlanePartition n π) :
    (i,j,z) ∈ shape n π ↔ z < π (i,j) := by
  rw [mem_shape_raw]
  constructor
  · exact fun hl => hl.2.2
  · intro hz
    by_cases hi : n ≤ i
    · rw [h.1 i j (.inl hi)] at hz
      omega
    by_cases hj : n ≤ j
    · rw [h.1 i j (.inr hj)] at hz
      omega
    exact ⟨by omega, by omega, hz⟩

theorem shape_card_sum (n : ℕ) (π : ℕ × ℕ → ℕ) :
    (shape n π).card = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, π (i,j) := by
  simp only [shape, Finset.card_map, Finset.card_sigma, Finset.card_range, Finset.sum_product]

theorem shape_card {n : ℕ} {π : ℕ × ℕ → ℕ} (h : IsPlanePartition n π) :
    (shape n π).card = n := (shape_card_sum n π).trans h.2.2

theorem shape_ideal {n : ℕ} {π : ℕ × ℕ → ℕ} (h : IsPlanePartition n π) :
    Ideal (shape n π) := by
  rintro ⟨i,j,z⟩ hp ⟨a,b,c⟩ hle
  exact (mem_shape h).2 (lt_of_le_of_lt hle.2.2
    (lt_of_lt_of_le ((mem_shape h).1 hp) (h.2.1 a i b j hle.1 hle.2.1)))

private theorem axis_lt_card {S : Finset P3} {a : ℕ} (f : ℕ → P3)
    (hf : Function.Injective f) (hmem : ∀ i ≤ a, f i ∈ S) : a < S.card := by
  have h := Finset.card_le_card_of_injOn (s := Finset.range (a+1)) (t := S) f
    (fun i hi => hmem i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))) hf.injOn
  simpa using h

theorem point_lt_card {S : Finset P3} (h : Ideal S) {p : P3} (hp : p ∈ S) :
    p.1 < S.card ∧ p.2.1 < S.card ∧ p.2.2 < S.card := by
  obtain ⟨i,j,z⟩ := p
  refine ⟨axis_lt_card (fun a => (a,j,z)) (fun _ _ e => congrArg Prod.fst e)
    (fun _ ha => h _ hp _ ⟨ha,le_rfl,le_rfl⟩), ?_, ?_⟩
  · exact axis_lt_card (fun a => (i,a,z)) (fun _ _ e => congrArg (fun v : P3 => v.2.1) e)
      (fun _ ha => h _ hp _ ⟨le_rfl,ha,le_rfl⟩)
  · exact axis_lt_card (fun a => (i,j,a)) (fun _ _ e => congrArg (fun v : P3 => v.2.2) e)
      (fun _ ha => h _ hp _ ⟨le_rfl,le_rfl,ha⟩)

def height (S : Finset P3) (b : ℕ × ℕ) : ℕ :=
  S.sup (fun p => if (p.1,p.2.1) = b then p.2.2 + 1 else 0)

theorem mem_iff_lt_height {S : Finset P3} (h : Ideal S) {i j z : ℕ} :
    (i,j,z) ∈ S ↔ z < height S (i,j) := by
  rw [height, Finset.lt_sup_iff]
  constructor
  · intro hp
    exact ⟨(i,j,z), hp, by simp⟩
  · rintro ⟨⟨a,b,c⟩, hp, hl⟩
    by_cases he : (a,b) = (i,j)
    · cases he
      simp only [if_true] at hl
      exact h (i,j,c) hp (i,j,z) ⟨le_rfl,le_rfl,by simpa using hl⟩
    · simp [he] at hl

theorem shape_height {S : Finset P3} (h : Ideal S) : shape S.card (height S) = S := by
  ext p
  obtain ⟨i,j,z⟩ := p
  rw [mem_shape_raw]
  constructor
  · exact fun hm => (mem_iff_lt_height h).2 hm.2.2
  · intro hm
    have ha := point_lt_card h hm
    exact ⟨ha.1,ha.2.1,(mem_iff_lt_height h).1 hm⟩

theorem height_shape {n : ℕ} {π : ℕ × ℕ → ℕ} (h : IsPlanePartition n π) :
    height (shape n π) = π := by
  funext ⟨i,j⟩
  have w : ∀ z : ℕ, z < height (shape n π) (i,j) ↔ z < π (i,j) :=
    fun _ => (mem_iff_lt_height (shape_ideal h)).symm.trans (mem_shape h)
  have h1 := w (π (i,j))
  have h2 := w (height (shape n π) (i,j))
  omega

theorem height_partition {S : Finset P3} (h : Ideal S) : IsPlanePartition S.card (height S) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j hb
    by_contra! hn
    have hm := (mem_iff_lt_height h (z := 0)).2 (Nat.pos_of_ne_zero hn)
    obtain ⟨hi,hj,_⟩ := point_lt_card h hm
    change i < S.card at hi
    change j < S.card at hj
    omega
  · intro a i b j ha hb
    by_contra! hn
    have hm := (mem_iff_lt_height h).2 hn
    have hlow := h (i,j,height S (a,b)) hm (a,b,height S (a,b)) ⟨ha,hb,le_rfl⟩
    exact (Nat.lt_irrefl _ ((mem_iff_lt_height h).1 hlow))
  · rw [← shape_card_sum, shape_height h]

def shapeEquiv (n : ℕ) : {π // IsPlanePartition n π} ≃ {S : Finset P3 // Ideal S ∧ S.card = n} where
  toFun p := ⟨shape n p.1, shape_ideal p.2, shape_card p.2⟩
  invFun S := ⟨height S.1, by simpa only [S.2.2] using height_partition S.2.1⟩
  left_inv p := Subtype.ext (height_shape p.2)
  right_inv S := Subtype.ext (by simpa [← S.2.2] using shape_height S.2.1)

theorem fits_shape_iff {n : ℕ} {π : ℕ × ℕ → ℕ} (h : IsPlanePartition n π) (m : ℕ) :
    FitsInBox m π ↔ InCube (shape n π) m := by
  constructor
  · rintro ⟨ht,hb⟩ ⟨i,j,z⟩ hmem
    have hz := (mem_shape h).1 hmem
    have hx : ¬ (m ≤ i ∨ m ≤ j) := by
      intro hl
      rw [hb i j hl] at hz
      omega
    exact ⟨by change i < m; omega, by change j < m; omega, lt_of_lt_of_le hz (ht i j)⟩
  · intro hc
    constructor
    · intro i j
      by_contra! hlt
      exact (Nat.lt_irrefl m) (hc (i,j,m) ((mem_shape h).2 hlt)).2.2
    · intro i j hb
      by_contra! hn
      obtain ⟨hi,hj,_⟩ := hc (i,j,0) ((mem_shape h).2 (Nat.pos_of_ne_zero hn))
      change i < m at hi
      change j < m at hj
      omega

end Plane597

namespace Plane597

open OMA.S_oeis_a096597

theorem numPlanePartitions_eq_card (n : ℕ) :
    numPlanePartitions n = Nat.card {S : Finset P3 // Ideal S ∧ S.card = n} :=
  Nat.card_congr (shapeEquiv n)

def exactShapeEquiv (n m : ℕ) :
    {π : ℕ × ℕ → ℕ // IsPlanePartition n π ∧ FitsInBox m π ∧ ¬ FitsInBox (m-1) π} ≃
    {S : Finset P3 // Ideal S ∧ S.card=n ∧ InCube S m ∧ ¬ InCube S (m-1)} where
  toFun π := ⟨shape n π.1, shape_ideal π.2.1, shape_card π.2.1,
    (fits_shape_iff π.2.1 m).1 π.2.2.1, fun h => π.2.2.2 ((fits_shape_iff π.2.1 (m-1)).2 h)⟩
  invFun s := ⟨height s.1, by
    rcases s with ⟨S,hi,hn,hm,hprev⟩
    subst n
    have hf (k : ℕ) : FitsInBox k (height S) ↔ InCube S k := by
      rw [fits_shape_iff (height_partition hi) k, shape_height hi]
    exact ⟨height_partition hi,(hf m).2 hm,fun w => hprev ((hf (m-1)).1 w)⟩⟩
  left_inv π := by
    rcases π with ⟨π,hi,hb,hm⟩
    apply Subtype.ext
    exact height_shape hi
  right_inv s := by
    rcases s with ⟨S,hi,hn,hb,hm⟩
    subst n
    exact Subtype.ext (shape_height hi)

theorem T_eq_card (n m : ℕ) :
    T n m = Nat.card {S : Finset P3 // Ideal S ∧ S.card=n ∧ InCube S m ∧ ¬ InCube S (m-1)} :=
  Nat.card_congr (exactShapeEquiv n m)

end Plane597

namespace Plane597

private def ax (i : Fin 3) (t : ℕ) : P3 :=
  if i=0 then (t,0,0) else if i=1 then (0,t,0) else (0,0,t)

private theorem ax_inj (i : Fin 3) : Function.Injective (ax i) := by
  intro a b h
  fin_cases i <;> simpa [ax] using h

private theorem ax_mono (i : Fin 3) {u v : ℕ} (hu : u≤v) : ax i u ≤ ax i v := by
  fin_cases i <;> simp [ax,Prod.le_def,hu]

private theorem separate {i j : Fin 3} (h : i≠j) (u v : ℕ) : ax i u ≠ ax j (v+1) := by
  fin_cases i <;> fin_cases j <;> simp_all [ax]

private theorem axes_size {n m : ℕ} {S : Finset P3} (H : Ideal S) (hc : S.card=n)
    {i j : Fin 3} (ij : i≠j) (hi : ax i m ∈ S) (hj : ax j m ∈ S) : 2*m+1≤n := by
  let A := (Finset.range (m+1)).image (ax i)
  let B := (Finset.range m).image (fun k => ax j (k+1))
  have sep : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro q hq hq'
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hq'
    exact separate ij u v hv.symm
  have incl : A ∪ B ⊆ S := by
    intro q hq
    rcases Finset.mem_union.mp hq with a | b
    · obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp a
      exact H _ hi _ (ax_mono i (by simpa using Finset.mem_range.mp hk))
    · obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp b
      exact H _ hj _ (ax_mono j (Finset.mem_range.mp hk))
  have ca : A.card=m+1 := by simp [A,Finset.card_image_of_injective _ (ax_inj i)]
  have cb : B.card=m := by
    have inj : Function.Injective (fun k => ax j (k+1)) := (ax_inj j).comp Nat.succ_injective
    simp [B,Finset.card_image_of_injective _ inj]
  have bound := Finset.card_le_card incl
  rw [Finset.card_union_of_disjoint sep,ca,cb,hc] at bound
  omega

private theorem hit_face {S : Finset P3} (H : Ideal S) (m : ℕ) :
    ¬InCube S m ↔ ax 0 m ∈ S ∨ ax 1 m ∈ S ∨ ax 2 m ∈ S := by
  constructor
  · intro h
    by_contra! h'
    apply h
    intro p hp
    obtain ⟨a,b,c⟩ := p
    change a < m ∧ b < m ∧ c < m
    constructor
    · by_contra! bad
      exact h'.1 (H _ hp _ (show ax 0 m ≤ (a,b,c) by simpa [ax,Prod.le_def] using bad))
    constructor
    · by_contra! bad
      exact h'.2.1 (H _ hp _ (show ax 1 m ≤ (a,b,c) by simpa [ax,Prod.le_def] using bad))
    · by_contra! bad
      exact h'.2.2 (H _ hp _ (show ax 2 m ≤ (a,b,c) by simpa [ax,Prod.le_def] using bad))
  · rintro (ha|ha|ha) hb
    · exact (lt_irrefl m) (hb _ ha).1
    · exact (lt_irrefl m) (hb _ ha).2.1
    · exact (lt_irrefl m) (hb _ ha).2.2

private def rot : P3 ≃ P3 where
  toFun p := (p.2.1,p.2.2,p.1)
  invFun p := (p.2.2,p.1,p.2.1)
  left_inv _ := rfl
  right_inv _ := rfl

private theorem rot_mem (S : Finset P3) (p : P3) :
    rot p ∈ rot.finsetCongr S ↔ p ∈ S := by simp

private theorem rot_core (S : Finset P3) (n m : ℕ) :
    (Ideal (rot.finsetCongr S) ∧ (rot.finsetCongr S).card = n ∧ InCube (rot.finsetCongr S) m) ↔
    (Ideal S ∧ S.card=n ∧ InCube S m) := by
  have mono {a b : P3} : rot a ≤ rot b ↔ a ≤ b := by
    change (_ ∧ _ ∧ _) ↔ _ ∧ _ ∧ _
    tauto
  have cub (a : P3) : ((rot a).1 < m ∧ (rot a).2.1 < m ∧ (rot a).2.2 < m) ↔
      (a.1 < m ∧ a.2.1 < m ∧ a.2.2 < m) := by
    dsimp [rot]
    tauto
  simp only [Equiv.finsetCongr_apply,Finset.card_map]
  constructor
  · rintro ⟨hi,hc,hu⟩
    refine ⟨?_,hc,?_⟩
    · intro p hp q hq
      exact (rot_mem S q).mp (hi _ ((rot_mem S p).mpr hp) _ (mono.mpr hq))
    · exact fun p hp => (cub p).mp (hu _ ((rot_mem S p).mpr hp))
  · rintro ⟨hi,hc,hu⟩
    refine ⟨?_,hc,?_⟩
    · intro p hp q hq
      obtain ⟨u,rfl⟩ := rot.surjective p
      obtain ⟨v,rfl⟩ := rot.surjective q
      exact (rot_mem S v).mpr (hi _ ((rot_mem S u).mp hp) _ (mono.mp hq))
    · intro p hp
      obtain ⟨u,rfl⟩ := rot.surjective p
      exact (cub u).mpr (hu _ ((rot_mem S u).mp hp))

private def oriented (n m : ℕ) (i : Fin 3) : Set (Finset P3) :=
  {S | Ideal S ∧ S.card=n ∧ InCube S m ∧ ax i (m-1) ∈ S}

private theorem rotate_count (n m : ℕ) {i j : Fin 3} (h : rot (ax i (m-1))=ax j (m-1)) :
    (oriented n m i).ncard=(oriented n m j).ncard := by
  have corr (S : Finset P3) : rot.finsetCongr S ∈ oriented n m j ↔ S ∈ oriented n m i := by
    change (Ideal _ ∧ _ ∧ InCube _ m ∧ _) ↔ Ideal _ ∧ _ ∧ InCube _ m ∧ _
    rw [←h,rot_mem]
    have hc := rot_core S n m
    tauto
  have im : rot.finsetCongr '' oriented n m i = oriented n m j := by
    ext S
    rcases rot.finsetCongr.surjective S with ⟨T,rfl⟩
    constructor
    · rintro ⟨U,hU,e⟩
      exact (corr T).mpr ((rot.finsetCongr.injective e) ▸ hU)
    · intro hc
      exact ⟨T,(corr T).mp hc,rfl⟩
  rw [←im, Set.ncard_image_of_injective _ rot.finsetCongr.injective]

private theorem oriented_finite (n m : ℕ) (i : Fin 3) : (oriented n m i).Finite := by
  let box : Finset P3 := (Finset.range m) ×ˢ ((Finset.range m) ×ˢ (Finset.range m))
  apply box.powerset.finite_toSet.subset
  intro S h
  apply Finset.mem_powerset.mpr
  intro p hp
  simpa [box] using h.2.2.1 p hp

theorem three_axes (n k : ℕ) (_hn : 1 ≤ n) (hk : k < n/2) :
    Set.ncard {S : Finset P3 | Ideal S ∧ S.card=n ∧ InCube S (n-k) ∧ ¬InCube S (n-k-1)} =
      3 * Set.ncard {S : Finset P3 | Ideal S ∧ S.card=n ∧ InCube S (n-k) ∧ (0,0,n-k-1) ∈ S} := by
  let m := n-k
  have sep {i j : Fin 3} (ij : i≠j) : Disjoint (oriented n m i) (oriented n m j) := by
    apply Set.disjoint_left.mpr
    intro S hi hj
    have bound := axes_size hi.1 hi.2.1 ij hi.2.2.2 hj.2.2.2
    dsimp [m] at bound
    omega
  have part : {S : Finset P3 | Ideal S ∧ S.card=n ∧ InCube S m ∧ ¬InCube S (m-1)} =
      (oriented n m 0 ∪ oriented n m 1) ∪ oriented n m 2 := by
    ext S
    simp only [Set.mem_union,oriented,Set.mem_ofPred_eq]
    by_cases hs : Ideal S
    · rw [hit_face hs]; tauto
    · tauto
  have dis : Disjoint (oriented n m 0 ∪ oriented n m 1) (oriented n m 2) :=
    Set.disjoint_union_left.mpr ⟨sep (by decide),sep (by decide)⟩
  change _ = 3*(oriented n m 2).ncard
  rw [part,Set.ncard_union_eq dis
    ((oriented_finite n m 0).union (oriented_finite n m 1)) (oriented_finite n m 2),
    Set.ncard_union_eq (sep (by decide)) (oriented_finite n m 0) (oriented_finite n m 1)]
  have h02 := rotate_count n m (i:=0) (j:=2) rfl
  have h10 := rotate_count n m (i:=1) (j:=0) rfl
  omega

theorem zface_iff {S : Finset P3} {n k : ℕ} (H : Ideal S) (hc : S.card=n)
    (hk : k<n/2) :
    (InCube S (n-k) ∧ (0,0,n-k-1) ∈ S) ↔
      (0,0,n-k-1) ∈ S ∧ (0,0,n-k) ∉ S := by
  constructor
  · rintro ⟨h,hz⟩
    exact ⟨hz,fun h' => (lt_irrefl _) (h _ h').2.2⟩
  · rintro ⟨hz,hn⟩
    refine ⟨?_,hz⟩
    by_contra outside
    have noOther (i : Fin 3) (hi : i≠2) (q : ax i (n-k) ∈ S) : False := by
      have smaller := H _ q _ (ax_mono i (show n-k-1≤n-k by omega))
      have count := axes_size H hc hi smaller (show ax 2 (n-k-1) ∈ S from hz)
      omega
    rcases (hit_face H _).mp outside with h|h|h
    · exact noOther 0 (by decide) h
    · exact noOther 1 (by decide) h
    · exact hn h

end Plane597

namespace Plane597
open Finset

def OffAxis (p : P3) : Prop := 0 < p.1 ∨ 0 < p.2.1

instance (p : P3) : Decidable (OffAxis p) := by unfold OffAxis; infer_instance

/-- A finite 3D order ideal in the ambient poset with the vertical axis deleted. -/
def PunctIdeal (R : Finset P3) : Prop :=
  (∀ p ∈ R, OffAxis p) ∧ ∀ p ∈ R, ∀ q, q ≤ p → OffAxis q → q ∈ R

def ray (m : ℕ) : Finset P3 :=
  (range m).map ⟨fun z => (0,0,z),fun _ _ h => congrArg (fun p : P3 => p.2.2) h⟩

theorem mem_ray (p : P3) (m : ℕ) : p ∈ ray m ↔ p.1=0 ∧ p.2.1=0 ∧ p.2.2 < m := by
  rcases p with ⟨i,j,z⟩
  simp only [ray,mem_map,mem_range]
  change (∃ a, a < m ∧ ((0,0,a) : P3)=(i,j,z)) ↔ i=0 ∧ j=0 ∧ z < m
  constructor
  · rintro ⟨a,h,e⟩
    cases e
    exact ⟨rfl,rfl,h⟩
  · rintro ⟨rfl,rfl,h⟩
    exact ⟨z,h,rfl⟩

theorem ray_card (m : ℕ) : (ray m).card=m := by simp [ray]

theorem punct_bounds {R : Finset P3} (h : PunctIdeal R) {p : P3} (hp : p ∈ R) :
    p.1 ≤ R.card ∧ p.2.1 ≤ R.card ∧ p.2.2 < R.card := by
  rcases p with ⟨i,j,z⟩
  have along (a : ℕ) (f : ℕ → P3) (hf : ∀ b < a, f b ∈ R) (hi : Function.Injective f) :
      a ≤ R.card := by
    simpa using card_le_card_of_injOn (s:=range a) (t:=R) f
      (fun b hb => hf b (mem_range.mp hb)) hi.injOn
  refine ⟨along i (fun b => (b+1,j,z)) ?_ ?_, along j (fun b => (i,b+1,z)) ?_ ?_, ?_⟩
  · intro b hb
    exact h.2 _ hp _ ⟨by omega,le_rfl⟩ (Or.inl (by dsimp; omega))
  · intro a b e
    have := congrArg Prod.fst e
    simpa using this
  · intro b hb
    exact h.2 _ hp _ ⟨le_rfl,by exact ⟨show b+1 ≤ j by omega,le_rfl⟩⟩ (Or.inr (by dsimp; omega))
  · intro a b e
    have := congrArg (fun p : P3 => p.2.1) e
    simpa using this
  · exact along (z+1) (fun b => (i,j,b)) (fun b hb => h.2 _ hp _ ⟨le_rfl,le_rfl,show b ≤ z by omega⟩
      (h.1 (i,j,z) hp)) (fun _ _ e => congrArg (fun p : P3 => p.2.2) e)

def puncture (S : Finset P3) : Finset P3 := S.filter OffAxis

theorem puncture_ideal {S : Finset P3} (h : Ideal S) : PunctIdeal (puncture S) := by
  exact ⟨fun _ hp => (mem_filter.mp hp).2,fun _ hp q hq ho =>
    mem_filter.mpr ⟨h _ (mem_filter.mp hp).1 q hq,ho⟩⟩

theorem disjoint_ray {R : Finset P3} (h : ∀ p ∈ R, OffAxis p) (m : ℕ) : Disjoint R (ray m) := by
  apply Finset.disjoint_left.mpr
  intro p hp hr
  have ha := h p hp
  obtain ⟨i,j,_⟩ := (mem_ray p m).mp hr
  unfold OffAxis at ha
  omega

theorem restore_ray {S : Finset P3} {m : ℕ} (h : Ideal S) (box : InCube S m)
    (top : (0,0,m-1) ∈ S) : puncture S ∪ ray m = S := by
  ext p
  simp only [puncture,mem_union,mem_filter,mem_ray]
  constructor
  · rintro (⟨hs,_⟩ | ⟨i,j,z⟩)
    · exact hs
    · exact h _ top p ⟨i.le,j.le,show p.2.2 ≤ m-1 by omega⟩
  · intro hp
    by_cases ho : OffAxis p
    · exact Or.inl ⟨hp,ho⟩
    · have bz := (box p hp).2.2
      simp only [OffAxis,not_or,not_lt,Nat.le_zero] at ho
      exact Or.inr ⟨ho.1,ho.2,bz⟩

theorem fill_ray {R : Finset P3} {m : ℕ} (h : PunctIdeal R) (hm : R.card < m) :
    Ideal (R ∪ ray m) ∧ InCube (R ∪ ray m) m ∧ (0,0,m-1) ∈ R ∪ ray m := by
  have cover : InCube (R ∪ ray m) m := by
    intro p hp
    rcases mem_union.mp hp with hr|hr
    · obtain ⟨a,b,c⟩ := punct_bounds h hr
      exact ⟨by omega,by omega,by omega⟩
    · obtain ⟨a,b,c⟩ := (mem_ray p m).mp hr
      exact ⟨by omega,by omega,c⟩
  refine ⟨?_,cover,mem_union_right _ ((mem_ray _ _).mpr ⟨rfl,rfl,by dsimp; omega⟩)⟩
  intro p hp q hq
  by_cases ho : OffAxis q
  · have ep : p ∈ R := by
      rcases mem_union.mp hp with hr|hr
      · exact hr
      · obtain ⟨i,j,_⟩ := (mem_ray p m).mp hr
        have le₁ := hq.1
        have le₂ := hq.2.1
        unfold OffAxis at ho
        omega
    exact mem_union_left _ (h.2 _ ep _ hq ho)
  · have hb := (cover p hp).2.2
    have hz := hq.2.2
    simp only [OffAxis,not_or,not_lt,Nat.le_zero] at ho
    exact mem_union_right _ ((mem_ray _ _).mpr ⟨ho.1,ho.2,by omega⟩)

theorem remove_ray {R : Finset P3} (h : PunctIdeal R) (m : ℕ) :
    puncture (R ∪ ray m) = R := by
  ext p
  simp only [puncture,mem_filter,mem_union,mem_ray]
  constructor
  · rintro ⟨hp,ho⟩
    rcases hp with hp | ⟨i,j,_⟩
    · exact hp
    · unfold OffAxis at ho
      omega
  · exact fun hp => ⟨Or.inl hp,h.1 _ hp⟩

def punctureEquiv (n k : ℕ) (hk : k < n/2) :
    {S : Finset P3 // Ideal S ∧ S.card=n ∧ InCube S (n-k) ∧ (0,0,n-k-1) ∈ S} ≃
    {R : Finset P3 // PunctIdeal R ∧ R.card=k} where
  toFun S := ⟨puncture S.val,by
    obtain ⟨h,sz,bx,tp⟩ := S.property
    have hi := puncture_ideal h
    have eq := congrArg Finset.card (restore_ray h bx tp)
    rw [card_union_of_disjoint (disjoint_ray hi.1 _),ray_card,sz] at eq
    exact ⟨hi,by omega⟩⟩
  invFun R := ⟨R.val ∪ ray (n-k),by
    obtain ⟨h,bx,tp⟩ := fill_ray R.property.1 (m:=n-k) (by have := R.property.2; omega)
    exact ⟨h,by rw [card_union_of_disjoint (disjoint_ray R.property.1.1 _),ray_card,R.property.2]; omega,bx,tp⟩⟩
  left_inv S := Subtype.ext (restore_ray S.property.1 S.property.2.2.1 S.property.2.2.2)
  right_inv R := Subtype.ext (remove_ray R.property.1 _)

end Plane597

namespace Plane597

abbrev Table := (ℕ × ℕ) →₀ ℕ

def weight (f : Table) : ℕ := f.sum (fun _ v => v)

def potential (f : Table) : ℕ := f.sum (fun p v => (p.1+p.2+1)*v)

structure SlideState where
  row : ℕ
  col : ℕ
  tab : Table

structure Valid (s : SlideState) : Prop where
  zero : s.tab (s.row,s.col) = 0
  hor : ∀ r c, (r,c) ≠ (s.row,s.col) → (r,c+1) ≠ (s.row,s.col) →
    s.tab (r,c+1) ≤ s.tab (r,c)
  ver : ∀ r c, (r,c) ≠ (s.row,s.col) → (r+1,c) ≠ (s.row,s.col) →
    s.tab (r+1,c) ≤ s.tab (r,c)
  hgap : ∀ c, s.col=c+1 → s.tab (s.row,s.col+1) ≤ s.tab (s.row,c)
  vgap : ∀ r, s.row=r+1 → s.tab (s.row+1,s.col) ≤ s.tab (r,s.col)+1
  west : ∀ c, s.col=c+1 → 0 < s.tab (s.row,c)

def Terminal (s : SlideState) : Prop :=
  s.tab (s.row,s.col+1) = 0 ∧ s.tab (s.row+1,s.col) = 0

inductive Slide : SlideState → SlideState → Prop
  | east (i j a : ℕ) (b : Table) (h₀ : b (i,j)=0) (h₁ : b (i,j+1)=0)
      (ha : 0<a) (he : b (i+1,j) ≤ a) :
      Slide ⟨i,j,b + Finsupp.single (i,j+1) a⟩
        ⟨i,j+1,b + Finsupp.single (i,j) a⟩
  | south (i j a : ℕ) (b : Table) (h₀ : b (i,j)=0) (h₁ : b (i+1,j)=0)
      (he : b (i,j+1) ≤ a) :
      Slide ⟨i,j,b + Finsupp.single (i+1,j) (a+1)⟩
        ⟨i+1,j,b + Finsupp.single (i,j) a⟩

end Plane597

namespace Plane597

def Ordinary (A : Table) : Prop :=
  (∀ i j : ℕ, A (i+1,j) ≤ A (i,j)) ∧ ∀ i j : ℕ, A (i,j+1) ≤ A (i,j)

def Punct (A : Table) : Prop :=
  A (0,0)=0 ∧ (∀ i j : ℕ, (i,j)≠(0,0) → A (i+1,j) ≤ A (i,j)) ∧
    ∀ i j : ℕ, (i,j)≠(0,0) → A (i,j+1) ≤ A (i,j)

end Plane597

namespace Plane597
open OMA.S_oeis_a096597

private theorem fixed_ideals_finite (n : ℕ) :
    Finite {S : Finset P3 // Ideal S ∧ S.card=n} := by
  let B := Finset.range n ×ˢ (Finset.range n ×ˢ Finset.range n)
  have hf : {S : Finset P3 | Ideal S ∧ S.card=n}.Finite := by
    apply B.powerset.finite_toSet.subset
    intro S h
    apply Finset.mem_powerset.mpr
    intro p hp
    have b := point_lt_card h.1 hp
    simpa [B,h.2] using b
  exact hf.to_subtype

theorem count_conclusion
    (ordinary : ∀ j : ℕ, {S : Finset P3 // Ideal S ∧ S.card=j} ≃
      {A : Table // Ordinary A ∧ weight A=j})
    (punct : ∀ k : ℕ, {R : Finset P3 // PunctIdeal R ∧ R.card=k} ≃
      {A : Table // Punct A ∧ weight A=k})
    (slides : ∀ k : ℕ, {A : Table // Punct A ∧ weight A=k} ≃
      (Σ j : Fin (k+1), {A : Table // Ordinary A ∧ weight A=j.val})) :
    type_of% @OMA.S_oeis_a096597.main := by
  intro n hn k hk
  let (j : Fin (k+1)) : Finite {A : Table // Ordinary A ∧ weight A=j.val} :=
    @Finite.of_equiv _ _ (fixed_ideals_finite j.val) (ordinary j.val)
  have ca (j : ℕ) : Nat.card {A : Table // Ordinary A ∧ weight A=j} = numPlanePartitions j :=
    (Nat.card_congr (ordinary j)).symm.trans (numPlanePartitions_eq_card j).symm
  have base := (T_eq_card n (n-k)).trans (three_axes n k hn hk)
  rw [base]
  apply congrArg (3 * ·)
  calc
    _ = Nat.card (Σ j : Fin (k+1), {A : Table // Ordinary A ∧ weight A=j.val}) :=
      Nat.card_congr (((punctureEquiv n k hk).trans (punct k)).trans (slides k))
    _ = ∑ j : Fin (k+1), Nat.card {A : Table // Ordinary A ∧ weight A=j.val} := Nat.card_sigma
    _ = ∑ j : Fin (k+1), numPlanePartitions j := Finset.sum_congr rfl (fun j _ => ca j)
    _ = _ := Fin.sum_univ_eq_sum_range numPlanePartitions (k+1)

end Plane597

namespace Plane597

open Finset

private def embedColumn : (Σ _ : ℕ × ℕ, ℕ) ↪ P3 where
  toFun v := (v.1.1, v.1.2, v.2)
  inj' := by
    rintro ⟨⟨a,b⟩,c⟩ ⟨⟨d,e⟩,f⟩ h
    change (a,b,c) = (d,e,f) at h
    cases h
    rfl

def tableShape (A : Table) : Finset P3 :=
  (A.support.sigma (fun b => range (A b))).map embedColumn

theorem mem_tableShape {A : Table} {i j z : ℕ} :
    (i,j,z) ∈ tableShape A ↔ z < A (i,j) := by
  simp only [tableShape, mem_map, mem_sigma, mem_range]
  constructor
  · rintro ⟨⟨⟨a,b⟩,c⟩,⟨_,hl⟩,he⟩
    change (a,b,c) = (i,j,z) at he
    cases he
    exact hl
  · intro hz
    have hi : (i,j) ∈ A.support := Finsupp.mem_support_iff.mpr (Nat.ne_of_gt ((Nat.zero_le z).trans_lt hz))
    exact ⟨⟨(i,j),z⟩,⟨hi,hz⟩,rfl⟩

theorem card_tableShape (A : Table) : (tableShape A).card = weight A := by
  simp only [tableShape, card_map, card_sigma, card_range,weight,Finsupp.sum]

noncomputable def heightTable (S : Finset P3) : Table :=
  Finsupp.onFinset (S.image fun p => (p.1,p.2.1)) (height S) (by
    intro x h
    have hpos := Nat.pos_of_ne_zero h
    rw [height,Finset.lt_sup_iff] at hpos
    obtain ⟨p,hp,hv⟩ := hpos
    by_cases he : (p.1,p.2.1) = x
    · exact mem_image.mpr ⟨p,hp,he⟩
    · simp [he] at hv)

theorem heightTable_apply (S : Finset P3) (i j : ℕ) : heightTable S (i,j) = height S (i,j) := rfl

private theorem col_height_iff {S : Finset P3}
    (h : ∀ i j z c : ℕ, (i,j,z) ∈ S → c ≤ z → (i,j,c) ∈ S) (i j z : ℕ) :
    (i,j,z) ∈ S ↔ z < heightTable S (i,j) := by
  rw [heightTable_apply,height,Finset.lt_sup_iff]
  constructor
  · intro hp
    exact ⟨(i,j,z),hp,by simp⟩
  · rintro ⟨⟨a,b,c⟩,hp,hl⟩
    by_cases he : (a,b) = (i,j)
    · cases he
      exact h i j c z hp (by simpa using hl)
    · simp [he] at hl

private theorem idealDown {S : Finset P3} (h : Ideal S) :
    ∀ i j z c : ℕ, (i,j,z) ∈ S → c ≤ z → (i,j,c) ∈ S :=
  fun _ _ _ _ hp hc => h _ hp _ ⟨le_rfl,le_rfl,hc⟩

private theorem punctDown {S : Finset P3} (h : PunctIdeal S) :
    ∀ i j z c : ℕ, (i,j,z) ∈ S → c ≤ z → (i,j,c) ∈ S :=
  fun i j z _ hp hc => h.2 _ hp _ ⟨le_rfl,le_rfl,hc⟩ (h.1 (i,j,z) hp)

theorem tableShape_heightTable {S : Finset P3}
    (h : ∀ i j z c : ℕ, (i,j,z) ∈ S → c ≤ z → (i,j,c) ∈ S) :
    tableShape (heightTable S) = S := by
  ext ⟨i,j,z⟩
  exact mem_tableShape.trans (col_height_iff h i j z).symm

theorem heightTable_tableShape (A : Table) : heightTable (tableShape A) = A := by
  apply Finsupp.ext
  rintro ⟨i,j⟩
  have h (z : ℕ) : z < heightTable (tableShape A) (i,j) ↔ z < A (i,j) :=
    (col_height_iff (S := tableShape A) (fun _ _ _ _ hp hc =>
      mem_tableShape.mpr (hc.trans_lt (mem_tableShape.mp hp))) i j z).symm.trans mem_tableShape
  have := h (heightTable (tableShape A) (i,j))
  have := h (A (i,j))
  omega

private theorem table_anti {A : Table}
    (hver : ∀ i j : ℕ, (i,j) ≠ (0,0) → A (i+1,j) ≤ A (i,j))
    (hhor : ∀ i j : ℕ, (i,j) ≠ (0,0) → A (i,j+1) ≤ A (i,j))
    {i j u v : ℕ} (h₀ : (i,j) ≠ (0,0)) (hi : i ≤ u) (hj : j ≤ v) :
    A (u,v) ≤ A (i,j) := by
  have nz {a b : ℕ} (ha : i ≤ a) (hb : j ≤ b) : (a,b) ≠ (0,0) := by
    intro he
    cases he
    apply h₀
    simp only [Prod.mk.injEq]
    omega
  have hleft : A (u,j) ≤ A (i,j) := by
    induction u,hi using Nat.le_induction with
    | base => exact le_rfl
    | succ u hu ih => exact (hver u j (nz hu le_rfl)).trans ih
  have htop : A (u,v) ≤ A (u,j) := by
    induction v,hj using Nat.le_induction with
    | base => exact le_rfl
    | succ v hv ih => exact (hhor u v (nz hi hv)).trans ih
  exact htop.trans hleft

theorem ordinary_shape_ideal {A : Table} (h : Ordinary A) : Ideal (tableShape A) := by
  rintro ⟨u,v,z⟩ hp ⟨i,j,c⟩ ⟨hi,hj,hc⟩
  have ver : Antitone (fun w : ℕ => A (w,j)) := antitone_nat_of_succ_le (fun w => h.1 w j)
  have hor : Antitone (fun w : ℕ => A (u,w)) := antitone_nat_of_succ_le (fun w => h.2 u w)
  exact mem_tableShape.mpr <| hc.trans_lt <| (mem_tableShape.mp hp).trans_le ((hor hj).trans (ver hi))

theorem punct_shape_ideal {A : Table} (h : Punct A) : PunctIdeal (tableShape A) := by
  constructor
  · rintro ⟨i,j,z⟩ hp
    have hz := mem_tableShape.mp hp
    by_contra! hn
    simp only [OffAxis,not_or,not_lt,Nat.le_zero] at hn
    rcases hn with ⟨rfl,rfl⟩
    rw [h.1] at hz
    omega
  · rintro ⟨u,v,z⟩ hp ⟨i,j,c⟩ ⟨hi,hj,hc⟩ ho
    have nz : (i,j) ≠ (0,0) := by
      intro he
      cases he
      simp [OffAxis] at ho
    exact mem_tableShape.mpr <| hc.trans_lt <| (mem_tableShape.mp hp).trans_le
      (table_anti h.2.1 h.2.2 nz hi hj)

theorem ideal_height_ordinary {S : Finset P3} (h : Ideal S) : Ordinary (heightTable S) := by
  have mono (i j u v : ℕ) (hi : i ≤ u) (hj : j ≤ v) : heightTable S (u,v) ≤ heightTable S (i,j) := by
    by_contra! hh
    have hp := (col_height_iff (idealDown h) u v _).2 hh
    have h' := h _ hp (i,j,heightTable S (i,j)) ⟨hi,hj,le_rfl⟩
    exact (Nat.lt_irrefl _) ((col_height_iff (idealDown h) i j _).1 h')
  exact ⟨fun i j => mono i j (i+1) j (by omega) le_rfl,
    fun i j => mono i j i (j+1) le_rfl (by omega)⟩

theorem punct_height_punct {S : Finset P3} (h : PunctIdeal S) : Punct (heightTable S) := by
  have mono (i j u v : ℕ) (ho : (i,j) ≠ (0,0)) (hi : i ≤ u) (hj : j ≤ v) :
      heightTable S (u,v) ≤ heightTable S (i,j) := by
    by_contra! hh
    have hp := (col_height_iff (punctDown h) u v _).2 hh
    have hoff : OffAxis (i,j,heightTable S (i,j)) := by
      by_cases hi0 : i=0
      · have hj0 : j ≠ 0 := fun hj0 => ho (by simp [hi0,hj0])
        exact Or.inr (Nat.pos_of_ne_zero hj0)
      · exact Or.inl (Nat.pos_of_ne_zero hi0)
    have h' := h.2 _ hp (i,j,heightTable S (i,j)) ⟨hi,hj,le_rfl⟩ hoff
    exact (Nat.lt_irrefl _) ((col_height_iff (punctDown h) i j _).1 h')
  refine ⟨?_,fun i j ho => mono i j (i+1) j ho (by omega) le_rfl,
    fun i j ho => mono i j i (j+1) ho le_rfl (by omega)⟩
  by_contra! hp
  have hn := h.1 (0,0,0) ((col_height_iff (punctDown h) 0 0 0).2 (Nat.pos_of_ne_zero hp))
  simp [OffAxis] at hn

noncomputable def ordinaryTableEquiv (n : ℕ) :
    {S : Finset P3 // Ideal S ∧ S.card=n} ≃ {A : Table // Ordinary A ∧ weight A=n} where
  toFun s := ⟨heightTable s.1,ideal_height_ordinary s.2.1,by
    rw [← card_tableShape,tableShape_heightTable (idealDown s.2.1),s.2.2]⟩
  invFun a := ⟨tableShape a.1,ordinary_shape_ideal a.2.1,(card_tableShape a.1).trans a.2.2⟩
  left_inv s := Subtype.ext (tableShape_heightTable (idealDown s.2.1))
  right_inv a := Subtype.ext (heightTable_tableShape a.1)

noncomputable def punctTableEquiv (k : ℕ) :
    {S : Finset P3 // PunctIdeal S ∧ S.card=k} ≃ {A : Table // Punct A ∧ weight A=k} where
  toFun s := ⟨heightTable s.1,punct_height_punct s.2.1,by
    rw [← card_tableShape,tableShape_heightTable (punctDown s.2.1),s.2.2]⟩
  invFun a := ⟨tableShape a.1,punct_shape_ideal a.2.1,(card_tableShape a.1).trans a.2.2⟩
  left_inv s := Subtype.ext (tableShape_heightTable (punctDown s.2.1))
  right_inv a := Subtype.ext (heightTable_tableShape a.1)

end Plane597

namespace Plane597
open Relation

/-- A strictly decreasing integer statistic guarantees a terminal state. -/
private theorem walk_end {α : Type*} (r : α → α → Prop) (μ : α → ℕ)
    (desc : ∀ a b, r a b → μ b < μ a) (a : α) :
    ∃ b, ReflTransGen r a b ∧ ∀ c, ¬ r b c := by
  classical
  induction h : μ a using Nat.strong_induction_on generalizing a with
  | h n ih =>
    by_cases hstop : ∀ c, ¬ r a c
    · exact ⟨a,.refl,hstop⟩
    · push Not at hstop
      obtain ⟨b,ab⟩ := hstop
      obtain ⟨c,bc,hc⟩ := ih (μ b) (h ▸ desc _ _ ab) b rfl
      exact ⟨c,bc.head ab,hc⟩

private theorem walk_unique {α : Type*} {r : α → α → Prop}
    (det : ∀ a b c, r a b → r a c → b=c) {a b c : α}
    (ab : ReflTransGen r a b) (nb : ∀ d, ¬ r b d)
    (ac : ReflTransGen r a c) (nc : ∀ d, ¬ r c d) : b=c := by
  induction ab using ReflTransGen.head_induction_on generalizing c with
  | refl => exact ((reflTransGen_iff_eq nb).mp ac).symm
  | @head x y xy _ ih =>
    rcases ac.cases_head with e | ⟨y',xy',yc⟩
    · subst c
      exact (nc y xy).elim
    · obtain rfl := det x y' y xy' xy
      exact ih yc nc

/-- Finite forward and backward walks with unique moves pair their endpoints. -/
noncomputable def walkEquiv {α : Type*} (r : α → α → Prop) (fwd back : α → ℕ)
    (hf : ∀ a b, r a b → fwd b < fwd a)
    (hb : ∀ a b, r a b → back a < back b)
    (df : ∀ a b c, r a b → r a c → b=c)
    (db : ∀ a b c, r b a → r c a → b=c) :
    {a : α // ∀ c, ¬ r c a} ≃ {b : α // ∀ c, ¬ r b c} := by
  classical
  let F (a : α) := (walk_end r fwd hf a).choose
  let G (b : α) := (walk_end (Function.swap r) back (fun x y e => hb y x e) b).choose
  have fs (a : α) : ReflTransGen r a (F a) ∧ ∀ c, ¬ r (F a) c :=
    (walk_end r fwd hf a).choose_spec
  have gs (b : α) : ReflTransGen (Function.swap r) b (G b) ∧ ∀ c, ¬ r c (G b) :=
    (walk_end (Function.swap r) back (fun x y e => hb y x e) b).choose_spec
  exact {
    toFun := fun a => ⟨F a.val,(fs _).2⟩
    invFun := fun b => ⟨G b.val,(gs _).2⟩
    left_inv := fun a => Subtype.ext (walk_unique (r:=Function.swap r) db (gs _).1 (gs _).2
      (reflTransGen_swap.mpr (fs _).1) a.property)
    right_inv := fun b => Subtype.ext (walk_unique df (fs _).1 (fs _).2
      (reflTransGen_swap.mp (gs _).1) b.property) }

end Plane597

namespace Plane597

/-- The local forward and backward slide rules pair starting holes with terminal holes. -/
noncomputable def slideEndpoints
    (next : ∀ {s : SlideState}, Valid s → ¬Terminal s → ∃ t, Valid t ∧ Slide s t)
    (prev : ∀ {t : SlideState}, Valid t → (t.row≠0 ∨ t.col≠0) → ∃ s, Valid s ∧ Slide s t)
    (funiq : ∀ {s t u : SlideState}, Slide s t → Slide s u → t=u)
    (buniq : ∀ {s t u : SlideState}, Valid s → Valid t → Slide s u → Slide t u → s=t)
    (wt : ∀ {s t : SlideState}, Slide s t → weight s.tab+s.row = weight t.tab+t.row)
    (pot : ∀ {s t : SlideState}, Slide s t → potential t.tab < potential s.tab)
    (rank : ∀ {s t : SlideState}, Slide s t → t.row+t.col = s.row+s.col+1)
    (active : ∀ {s t : SlideState}, Slide s t → ¬Terminal s) (k : ℕ) :
    {s : SlideState // Valid s ∧ (weight s.tab+s.row=k) ∧ s.row=0 ∧ s.col=0} ≃
    {s : SlideState // Valid s ∧ (weight s.tab+s.row=k) ∧ Terminal s} := by
  let Good := {s : SlideState // Valid s ∧ weight s.tab+s.row=k}
  let R (s t : Good) := Slide s.val t.val
  have starting (s : Good) : (∀ c, ¬R c s) ↔ s.val.row=0 ∧ s.val.col=0 := by
    constructor
    · intro h
      by_contra! bad
      obtain ⟨c,vc,step⟩ := prev s.property.1 (by omega)
      exact h ⟨c,vc,(wt step).trans s.property.2⟩ step
    · rintro ⟨hr,hc⟩ c step
      have e := rank step
      rw [hr,hc] at e
      omega
  have ending (s : Good) : (∀ c, ¬R s c) ↔ Terminal s.val := by
    constructor
    · intro h
      by_contra bad
      obtain ⟨c,vc,step⟩ := next s.property.1 bad
      exact h ⟨c,vc,(wt step).symm.trans s.property.2⟩ step
    · exact fun v c e => active e v
  let I : {s : SlideState // Valid s ∧ (weight s.tab+s.row=k) ∧ s.row=0 ∧ s.col=0} ≃
      {s : Good // ∀ c, ¬R c s} := {
    toFun := fun s => ⟨⟨s.val,s.property.1,s.property.2.1⟩,(starting _).mpr s.property.2.2⟩
    invFun := fun s => ⟨s.val.val,s.val.property.1,s.val.property.2,(starting _).mp s.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  let E : {s : Good // ∀ c, ¬R s c} ≃
      {s : SlideState // Valid s ∧ (weight s.tab+s.row=k) ∧ Terminal s} := {
    toFun := fun s => ⟨s.val.val,s.val.property.1,s.val.property.2,(ending _).mp s.property⟩
    invFun := fun s => ⟨⟨s.val,s.property.1,s.property.2.1⟩,(ending _).mpr s.property.2.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  apply I.trans
  refine (walkEquiv R (fun s => potential s.val.tab) (fun s => s.val.row+s.val.col)
    (fun _ _ h => pot h) (fun a b h => ?_)
    (fun _ _ _ h g => Subtype.ext (funiq h g))
    (fun _ b c h g => Subtype.ext (buniq b.property.1 c.property.1 h g))).trans E
  have e := rank h
  omega

end Plane597

namespace Plane597

/-- When the hole is in the first position, the slide inequalities are precisely those
of the punctured array. -/
theorem valid_initial_iff (A : Table) : Valid ⟨0,0,A⟩ ↔ Punct A := by
  constructor
  · intro h
    refine ⟨h.zero,?_,?_⟩
    · exact fun i j hij => h.ver _ _ hij (by simp)
    · exact fun i j hij => h.hor _ _ hij (by simp)
  · rintro ⟨h0,hv,hh⟩
    refine ⟨h0,fun r c h _ => hh r c h,fun r c h _ => hv r c h,?_,?_,?_⟩ <;>
      intro i hi <;> simp at hi

noncomputable def initialEquiv (k : ℕ) :
    {s : SlideState // Valid s ∧ (weight s.tab + s.row = k) ∧ s.row=0 ∧ s.col=0} ≃
      {A : Table // Punct A ∧ weight A=k} where
  toFun := fun ⟨⟨r,c,A⟩,h⟩ => by
    rcases h with ⟨h,hn,hr,hc⟩
    change r=0 at hr
    change c=0 at hc
    subst r; subst c
    exact ⟨A,(valid_initial_iff _).mp h,by simpa using hn⟩
  invFun A := ⟨⟨0,0,A.val⟩,(valid_initial_iff _).mpr A.property.1,
    by simpa using A.property.2,rfl,rfl⟩
  left_inv := by
    rintro ⟨⟨r,c,A⟩,_,_,hr,hc⟩
    change r=0 at hr
    change c=0 at hc
    subst r; subst c; rfl
  right_inv := by rintro ⟨A,h⟩; rfl

theorem terminal_ordinary {s : SlideState} (h : Valid s) (e : Terminal s) : Ordinary s.tab := by
  constructor
  · intro i j
    by_cases p : (i,j)=(s.row,s.col)
    · obtain ⟨rfl,rfl⟩ := Prod.mk.inj p
      rw [e.2]; exact Nat.zero_le _
    by_cases q : (i+1,j)=(s.row,s.col)
    · rw [q,h.zero]; exact Nat.zero_le _
    exact h.ver _ _ p q
  · intro i j
    by_cases p : (i,j)=(s.row,s.col)
    · obtain ⟨rfl,rfl⟩ := Prod.mk.inj p
      rw [e.1]; exact Nat.zero_le _
    by_cases q : (i,j+1)=(s.row,s.col)
    · rw [q,h.zero]; exact Nat.zero_le _
    exact h.hor _ _ p q

private theorem row_has_zero (A : Table) (r : ℕ) : ∃ c, A (r,c)=0 := by
  let C := A.support.sup Prod.snd
  refine ⟨C+1,Finsupp.notMem_support_iff.mp ?_⟩
  intro h
  have bound : C+1 ≤ C := Finset.le_sup (f:=Prod.snd) h
  omega

noncomputable def firstZero (A : Table) (r : ℕ) : ℕ := Nat.find (row_has_zero A r)

private theorem zero_at_first (A : Table) (r : ℕ) : A (r,firstZero A r)=0 :=
  Nat.find_spec (row_has_zero A r)

private theorem first_characterization {A : Table} (h : Ordinary A) {r c : ℕ}
    (hz : A (r,c)=0) (hw : ∀ j, c=j+1 → 0<A (r,j)) : firstZero A r=c := by
  apply le_antisymm (Nat.find_min' (row_has_zero A r) hz)
  by_contra! lt
  cases c with
  | zero => omega
  | succ j =>
    change firstZero A r < j+1 at lt
    have hj : firstZero A r ≤ j := by omega
    have row : Antitone (fun k => A (r,k)) := antitone_nat_of_succ_le (h.2 r)
    have bound := row hj
    change A (r,j) ≤ A (r,firstZero A r) at bound
    rw [zero_at_first] at bound
    have := hw j rfl
    omega

private theorem first_terminal (A : Table) (H : Ordinary A) (r : ℕ) :
    Valid ⟨r,firstZero A r,A⟩ ∧ Terminal ⟨r,firstZero A r,A⟩ := by
  let c := firstZero A r
  have h0 : A (r,c)=0 := zero_at_first A r
  have e : A (r,c+1)=0 := Nat.le_zero.mp ((H.2 r c).trans_eq h0)
  have s : A (r+1,c)=0 := Nat.le_zero.mp ((H.1 r c).trans_eq h0)
  refine ⟨⟨h0,fun i j _ _ => H.2 i j,fun i j _ _ => H.1 i j,?_,?_,?_⟩,e,s⟩
  · intro j _
    change A (r,c+1) ≤ A (r,j)
    simp [e]
  · intro i _
    change A (r+1,c) ≤ A (i,c)+1
    simp [s]
  · intro j hj
    change c=j+1 at hj
    exact Nat.pos_of_ne_zero (Nat.find_min (row_has_zero A r) (show j<c by omega))

/-- A stopped slide is determined by the ordinary table and the number of lost units.
Its hole is the first zero in the row indexed by those lost units. -/
noncomputable def terminalEquiv (k : ℕ) :
    {s : SlideState // Valid s ∧ (weight s.tab + s.row = k) ∧ Terminal s} ≃
      (Σ j : Fin (k+1), {A : Table // Ordinary A ∧ weight A=j.val}) where
  toFun s := ⟨⟨weight s.val.tab,by have := s.property.2.1; omega⟩,
    ⟨s.val.tab,terminal_ordinary s.property.1 s.property.2.2,rfl⟩⟩
  invFun := fun ⟨j,A⟩ => by
    let d := k-j.val
    have h := first_terminal A.val A.property.1 d
    refine ⟨⟨d,firstZero A.val d,A.val⟩,h.1,?_,h.2⟩
    change weight A.val + (k-j.val) = k
    have := j.isLt
    have := A.property.2
    omega
  left_inv := by
    rintro ⟨⟨r,c,A⟩,hv,wt, ht⟩
    have d : k-weight A=r := by change weight A+r=k at wt; omega
    have e : firstZero A r=c := first_characterization (terminal_ordinary hv ht) hv.zero hv.west
    apply Subtype.ext
    change (⟨k-weight A,firstZero A (k-weight A),A⟩ : SlideState) = ⟨r,c,A⟩
    rw [d,e]
  right_inv := by
    rintro ⟨⟨j,hj⟩,⟨A,ha,hA⟩⟩
    change weight A=j at hA
    subst j
    rfl

end Plane597

namespace Plane597

private theorem weight_single (b : Table) (p : ℕ×ℕ) (v : ℕ) :
    weight (b + Finsupp.single p v) = weight b + v := by
  simp [weight, Finsupp.sum_add_index]

private theorem pot_single (b : Table) (p : ℕ×ℕ) (v : ℕ) :
    potential (b + Finsupp.single p v) = potential b + (p.1+p.2+1)*v := by
  simp [potential, Finsupp.sum_add_index,Nat.mul_add]

theorem slide_rank {s t} (h : Slide s t) : t.row+t.col=s.row+s.col+1 := by
  cases h <;> dsimp only <;> omega

theorem slide_weight {s t} (h : Slide s t) : weight s.tab+s.row = weight t.tab+t.row := by
  cases h <;> simp only [weight_single]
  all_goals omega

theorem slide_potential {s t} (h : Slide s t) : potential t.tab < potential s.tab := by
  cases h with
  | east i j a b _ _ ha _ =>
    simp only [pot_single]
    ring_nf
    omega
  | south i j a b _ _ _ =>
    simp only [pot_single]
    ring_nf
    omega

theorem slide_not_terminal {s t} (h : Slide s t) : ¬Terminal s := by
  cases h <;> simp_all [Terminal]
  all_goals omega

end Plane597

namespace Plane597

private theorem relocation {s t : SlideState} (hs : Valid s)
    (z : t.tab (t.row,t.col)=0)
    (same : ∀ p, p≠(s.row,s.col) → p≠(t.row,t.col) → t.tab p = s.tab p)
    (w : ∀ c, s.col=c+1 → (s.row,c)≠(t.row,t.col) → t.tab (s.row,s.col) ≤ t.tab (s.row,c))
    (e : (s.row,s.col+1)≠(t.row,t.col) → t.tab (s.row,s.col+1) ≤ t.tab (s.row,s.col))
    (n : ∀ r, s.row=r+1 → (r,s.col)≠(t.row,t.col) → t.tab (s.row,s.col) ≤ t.tab (r,s.col))
    (d : (s.row+1,s.col)≠(t.row,t.col) → t.tab (s.row+1,s.col) ≤ t.tab (s.row,s.col))
    (hg : ∀ c, t.col=c+1 → t.tab (t.row,t.col+1) ≤ t.tab (t.row,c))
    (vg : ∀ r, t.row=r+1 → t.tab (t.row+1,t.col) ≤ t.tab (r,t.col)+1)
    (wp : ∀ c, t.col=c+1 → 0<t.tab (t.row,c)) : Valid t := by
  refine ⟨z,?_,?_,hg,vg,wp⟩
  · intro r c h₀ h₁
    by_cases a : (r,c)=(s.row,s.col)
    · obtain ⟨rfl,rfl⟩ := Prod.mk.inj a
      exact e h₁
    by_cases b : (r,c+1)=(s.row,s.col)
    · obtain ⟨rfl,b'⟩ := Prod.mk.inj b
      simpa only [← b'] using w c b'.symm h₀
    rw [same _ b h₁,same _ a h₀]
    exact hs.hor r c a b
  · intro r c h₀ h₁
    by_cases a : (r,c)=(s.row,s.col)
    · obtain ⟨rfl,rfl⟩ := Prod.mk.inj a
      exact d h₁
    by_cases b : (r+1,c)=(s.row,s.col)
    · obtain ⟨b',rfl⟩ := Prod.mk.inj b
      simpa only [← b'] using n r b'.symm h₀
    rw [same _ b h₁,same _ a h₀]
    exact hs.ver r c a b

-- Generated four local directions.

theorem east_valid_forward (i j a : ℕ) (b : Table)
    (h₀ : b (i,j)=0) (h₁ : b (i,j+1)=0)
    (ha : 0<a) (he : b (i+1,j) ≤ a)
    (hs : Valid ⟨i,j,b + Finsupp.single (i,j+1) a⟩) : Valid ⟨i,j+1,b + Finsupp.single (i,j) a⟩ := by
  apply relocation hs
  · simp [h₁]
  · intro p hp hq
    dsimp only at hp hq ⊢
    simp [Ne.symm hp, Ne.symm hq]
  · intro c eq hne
    dsimp only at *
    subst j
    have z0 := hs.hgap (c) rfl
    simp_all [Prod.ext_iff]
  · intro hne
    dsimp only at *
    simp_all
  · intro r eq hne
    dsimp only at *
    subst i
    have z0 := hs.ver (r) (j+1) (by simp [Prod.ext_iff]) (by simp [Prod.ext_iff])
    have z1 := hs.hor (r) (j) (by simp [Prod.ext_iff]) (by simp [Prod.ext_iff])
    simp_all [Prod.ext_iff]
    omega
  · intro hne
    dsimp only at *
    simp_all [Prod.ext_iff]
  · intro c eq
    dsimp only at *
    have eq2 : c = j := by omega
    subst c
    have z0 := hs.hor (i) (j+1) (by simp [Prod.ext_iff]) (by simp [Prod.ext_iff] ; omega)
    simp_all [Finsupp.single_apply, Prod.ext_iff]
    split_ifs at * <;> omega
  · intro r eq
    dsimp only at *
    subst i
    have z0 := hs.ver (r) (j+1) (by simp [Prod.ext_iff]) (by simp [Prod.ext_iff])
    have z1 := hs.ver ((r+1)) (j+1) (by simp [Prod.ext_iff]) (by simp [Prod.ext_iff])
    simp_all [Prod.ext_iff]
    omega
  · intro c eq
    dsimp only at *
    have eq2 : c = j := by omega
    subst c
    simp_all

theorem south_valid_forward (i j a : ℕ) (b : Table)
    (h₀ : b (i,j)=0) (h₁ : b (i+1,j)=0)
    (he : b (i,j+1) ≤ a)
    (hs : Valid ⟨i,j,b + Finsupp.single (i+1,j) (a+1)⟩) : Valid ⟨i+1,j,b + Finsupp.single (i,j) a⟩ := by
  apply relocation hs
  · simp [h₁]
  · intro p hp hq
    dsimp only at hp hq ⊢
    simp [Ne.symm hp, Ne.symm hq]
  · intro c eq hne
    dsimp only at *
    subst j
    have z0 := hs.ver (i) (c) (by simp [Prod.ext_iff]) (by simp [Prod.ext_iff])
    have z1 := hs.hor (i+1) (c) (by simp [Prod.ext_iff]) (by simp [Prod.ext_iff])
    simp_all [Prod.ext_iff]
    omega
  · intro hne
    dsimp only at *
    simp_all [Prod.ext_iff]
  · intro r eq hne
    dsimp only at *
    subst i
    have z0 := hs.vgap (r) rfl
    simp_all [Prod.ext_iff]
  · intro hne
    dsimp only at *
    simp_all
  · intro c eq
    dsimp only at *
    subst j
    have z0 := hs.hor (i+1) (c) (by simp [Prod.ext_iff]) (by simp [Prod.ext_iff])
    have z1 := hs.hor (i+1) ((c+1)) (by simp [Prod.ext_iff]) (by simp [Prod.ext_iff])
    simp_all [Prod.ext_iff]
    omega
  · intro r eq
    dsimp only at *
    have eq2 : r = i := by omega
    subst r
    have z0 := hs.ver (i+1) (j) (by simp [Prod.ext_iff]) (by simp [Prod.ext_iff] ; omega)
    simp_all [Finsupp.single_apply, Prod.ext_iff]
    split_ifs at * <;> omega
  · intro c eq
    dsimp only at *
    subst j
    have z0 := hs.hor (i+1) (c) (by simp [Prod.ext_iff]) (by simp [Prod.ext_iff])
    simp_all [Prod.ext_iff]
    omega

theorem east_valid_backward (i j a : ℕ) (b : Table)
    (h₀ : b (i,j)=0) (h₁ : b (i,j+1)=0)
    (ha : 0<a) (he : b (i+1,j) ≤ a)
    (guard : ∀ r, i=r+1 → a ≤ b (r,j+1))
    (hs : Valid ⟨i,j+1,b + Finsupp.single (i,j) a⟩) : Valid ⟨i,j,b + Finsupp.single (i,j+1) a⟩ := by
  apply relocation hs
  · simp [h₀]
  · intro p hp hq
    dsimp only at hp hq ⊢
    simp [Ne.symm hp, Ne.symm hq]
  · intro c eq hne
    dsimp only at *
    have eq2 : c = j := by omega
    subst c
    simp_all
  · intro hne
    dsimp only at *
    have z0 := hs.hgap (j) rfl
    simp_all [Prod.ext_iff]
  · intro r eq hne
    dsimp only at *
    subst i
    have z0 := guard (r) rfl
    simp_all [Prod.ext_iff]
  · intro hne
    dsimp only at *
    have z0 := hs.ver (i) (j) (by simp [Prod.ext_iff]) (by simp [Prod.ext_iff])
    have z1 := hs.hor (i+1) (j) (by simp [Prod.ext_iff]) (by simp [Prod.ext_iff])
    simp_all [Prod.ext_iff]
    omega
  · intro c eq
    dsimp only at *
    subst j
    have z0 := hs.hor (i) (c) (by simp [Prod.ext_iff] ; omega) (by simp [Prod.ext_iff])
    simp_all [Finsupp.single_apply, Prod.ext_iff]
    split_ifs at * <;> omega
  · intro r eq
    dsimp only at *
    subst i
    have z0 := hs.ver (r) (j) (by simp [Prod.ext_iff]) (by simp [Prod.ext_iff])
    have z1 := hs.ver ((r+1)) (j) (by simp [Prod.ext_iff]) (by simp [Prod.ext_iff])
    simp_all [Prod.ext_iff]
    omega
  · intro c eq
    dsimp only at *
    subst j
    have z0 := hs.hor (i) (c) (by simp [Prod.ext_iff] ; omega) (by simp [Prod.ext_iff])
    simp_all [Finsupp.single_apply, Prod.ext_iff]
    split_ifs at * <;> omega

theorem south_valid_backward (i j a : ℕ) (b : Table)
    (h₀ : b (i,j)=0) (h₁ : b (i+1,j)=0)
    (he : b (i,j+1) ≤ a)
    (guard : ∀ c, j=c+1 → a < b (i+1,c))
    (hs : Valid ⟨i+1,j,b + Finsupp.single (i,j) a⟩) : Valid ⟨i,j,b + Finsupp.single (i+1,j) (a+1)⟩ := by
  apply relocation hs
  · simp [h₀]
  · intro p hp hq
    dsimp only at hp hq ⊢
    simp [Ne.symm hp, Ne.symm hq]
  · intro c eq hne
    dsimp only at *
    subst j
    have z0 := guard (c) rfl
    simp_all [Prod.ext_iff]
  · intro hne
    dsimp only at *
    have z0 := hs.ver (i) (j+1) (by simp [Prod.ext_iff]) (by simp [Prod.ext_iff])
    have z1 := hs.hor (i) (j) (by simp [Prod.ext_iff]) (by simp [Prod.ext_iff])
    simp_all [Prod.ext_iff]
    omega
  · intro r eq hne
    dsimp only at *
    have eq2 : r = i := by omega
    subst r
    simp_all
  · intro hne
    dsimp only at *
    have z0 := hs.vgap (i) rfl
    simp_all [Prod.ext_iff]
  · intro c eq
    dsimp only at *
    subst j
    have z0 := hs.hor (i) (c) (by simp [Prod.ext_iff]) (by simp [Prod.ext_iff])
    have z1 := hs.hor (i) ((c+1)) (by simp [Prod.ext_iff]) (by simp [Prod.ext_iff])
    simp_all [Prod.ext_iff]
    omega
  · intro r eq
    dsimp only at *
    subst i
    have z0 := hs.ver (r) (j) (by simp [Prod.ext_iff] ; omega) (by simp [Prod.ext_iff])
    simp_all [Finsupp.single_apply, Prod.ext_iff]
    split_ifs at * <;> omega
  · intro c eq
    dsimp only at *
    subst j
    have z0 := hs.ver (i) (c) (by simp [Prod.ext_iff]) (by simp [Prod.ext_iff])
    have z1 := guard (c) rfl
    simp_all [Prod.ext_iff]
    omega

end Plane597

namespace Plane597

theorem slide_next {s : SlideState} (hs : Valid s) (hn : ¬Terminal s) :
    ∃ t, Valid t ∧ Slide s t := by
  rcases s with ⟨i,j,f⟩
  by_cases e : f (i+1,j) ≤ f (i,j+1)
  · let b := f.erase (i,j+1)
    have h₀ : b (i,j)=0 := (Finsupp.erase_ne (by simp)).trans hs.zero
    have h₁ : b (i,j+1)=0 := Finsupp.erase_same
    have he : b (i+1,j) ≤ f (i,j+1) := by simpa [b,Finsupp.erase_ne (show (i+1,j)≠(i,j+1) by simp)] using e
    have ha : 0<f (i,j+1) := by
      simp only [Terminal,not_and] at hn
      by_contra! h
      exact (hn (by omega)) (by omega)
    have eq : b+Finsupp.single (i,j+1) (f (i,j+1))=f := Finsupp.erase_add_single _ _
    refine ⟨_, east_valid_forward i j _ b h₀ h₁ ha he (by rw [eq]; exact hs),?_⟩
    simpa only [eq] using Slide.east i j _ b h₀ h₁ ha he
  · let b := f.erase (i+1,j)
    let a := f (i+1,j)-1
    have ha : a+1=f (i+1,j) := by dsimp [a]; omega
    have h₀ : b (i,j)=0 := (Finsupp.erase_ne (by simp)).trans hs.zero
    have h₁ : b (i+1,j)=0 := Finsupp.erase_same
    have he : b (i,j+1) ≤ a := by
      rw [show b (i,j+1) = f (i,j+1) from Finsupp.erase_ne (by simp)]
      omega
    have eq : b+Finsupp.single (i+1,j) (a+1)=f := by rw [ha]; exact Finsupp.erase_add_single _ _
    refine ⟨_, south_valid_forward i j _ b h₀ h₁ he (by rw [eq]; exact hs),?_⟩
    simpa only [eq] using Slide.south i j _ b h₀ h₁ he

private theorem prev_east (i j : ℕ) (f : Table) (ht : Valid ⟨i,j+1,f⟩)
    (guard : ∀ r, i=r+1 → f (i,j) ≤ f (r,j+1)) :
    ∃ s, Valid s ∧ Slide s ⟨i,j+1,f⟩ := by
  let b := f.erase (i,j)
  have h₀ : b (i,j)=0 := Finsupp.erase_same
  have h₁ : b (i,j+1)=0 := (Finsupp.erase_ne (by simp)).trans ht.zero
  have ha := ht.west j rfl
  have he : b (i+1,j) ≤ f (i,j) := by
    rw [show b (i+1,j) = f (i+1,j) from Finsupp.erase_ne (by simp)]
    exact ht.ver i j (by simp) (by simp)
  have g : ∀ r, i=r+1 → f (i,j) ≤ b (r,j+1) := by
    intro r eh
    rw [show b (r,j+1) = f (r,j+1) from Finsupp.erase_ne (by simp)]
    exact guard r eh
  have eq : b+Finsupp.single (i,j) (f (i,j))=f := Finsupp.erase_add_single _ _
  refine ⟨_, east_valid_backward i j _ b h₀ h₁ ha he g (by rw [eq]; exact ht), ?_⟩
  simpa only [eq] using Slide.east i j _ b h₀ h₁ ha he

private theorem prev_south (i j : ℕ) (f : Table) (ht : Valid ⟨i+1,j,f⟩)
    (guard : ∀ c, j=c+1 → f (i,j) < f (i+1,c)) :
    ∃ s, Valid s ∧ Slide s ⟨i+1,j,f⟩ := by
  let b := f.erase (i,j)
  have h₀ : b (i,j)=0 := Finsupp.erase_same
  have h₁ : b (i+1,j)=0 := (Finsupp.erase_ne (by simp)).trans ht.zero
  have he : b (i,j+1) ≤ f (i,j) := by
    rw [show b (i,j+1) = f (i,j+1) from Finsupp.erase_ne (by simp)]
    exact ht.hor i j (by simp) (by simp)
  have g : ∀ c, j=c+1 → f (i,j) < b (i+1,c) := by
    intro c eh
    rw [show b (i+1,c) = f (i+1,c) from Finsupp.erase_ne (by simp)]
    exact guard c eh
  have eq : b+Finsupp.single (i,j) (f (i,j))=f := Finsupp.erase_add_single _ _
  refine ⟨_, south_valid_backward i j _ b h₀ h₁ he g (by rw [eq]; exact ht), ?_⟩
  simpa only [eq] using Slide.south i j _ b h₀ h₁ he

theorem slide_prev {t : SlideState} (ht : Valid t) (h : t.row≠0 ∨ t.col≠0) :
    ∃ s, Valid s ∧ Slide s t := by
  rcases t with ⟨i,j,f⟩
  rcases i with _|i <;> rcases j with _|j
  · simp at h
  · exact prev_east 0 j f ht (by intro r h; omega)
  · exact prev_south i 0 f ht (by intro c h; omega)
  · by_cases e : f (i+1,j) ≤ f (i,j+1)
    · exact prev_east _ j f ht (by
        intro r h
        rw [show r=i by omega]
        exact e)
    · exact prev_south i _ f ht (by
        intro c h
        rw [show c=j by omega]
        omega)

end Plane597

namespace Plane597

private theorem empty_add_inj {b c : Table} {p : ℕ × ℕ} {u v : ℕ}
    (hb : b p=0) (hc : c p=0) (e : b+Finsupp.single p u=c+Finsupp.single p v) :
    b=c ∧ u=v := by
  have eq := congrArg (fun T : Table => T p) e
  have uv : u=v := by simpa [hb,hc] using eq
  subst v
  exact ⟨add_right_cancel e,rfl⟩

private theorem east_south_input {i j a d : ℕ} {b c : Table}
    (hb : b (i,j+1)=0) (hc : c (i+1,j)=0)
    (eb : b (i+1,j)≤a) (ec : c (i,j+1)≤d)
    (e : b+Finsupp.single (i,j+1) a=c+Finsupp.single (i+1,j) (d+1)) : False := by
  have east := congrArg (fun T : Table => T (i,j+1)) e
  have south := congrArg (fun T : Table => T (i+1,j)) e
  simp [hb,hc] at east south
  omega

private theorem unique_target_aux {s t s' t' : SlideState} (a : Slide s t) (b : Slide s' t')
    (h : s=s') : t=t' := by
  cases a with
  | east i j u B b0 b1 u1 gu =>
    cases b with
    | east l m v C c0 c1 v1 gv =>
      injection h with ih jh et
      subst l; subst m
      obtain ⟨rfl,rfl⟩ := empty_add_inj b1 c1 et
      rfl
    | south l m v C c0 c1 gv =>
      injection h with ih jh et
      subst l; subst m
      exact (east_south_input b1 c1 gu gv et).elim
  | south i j u B b0 b1 gu =>
    cases b with
    | east l m v C c0 c1 v1 gv =>
      injection h with ih jh et
      subst l; subst m
      exact (east_south_input c1 b1 gv gu et.symm).elim
    | south l m v C c0 c1 gv =>
      injection h with ih jh et
      subst l; subst m
      obtain ⟨rfl,hv⟩ := empty_add_inj b1 c1 et
      obtain rfl := Nat.succ.inj hv
      rfl

theorem slide_next_unique {s t u : SlideState} (a : Slide s t) (b : Slide s u) : t=u :=
  unique_target_aux a b rfl

private theorem east_south_output {i j a d : ℕ} {b c : Table}
    (hb : b (i+1,j)=0) (be : b (i+1,j+1)=0)
    (hc : c (i,j+1)=0) (cs : c (i+1,j+1)=0)
    (vb : Valid ⟨i+1,j,b+Finsupp.single (i+1,j+1) a⟩)
    (vc : Valid ⟨i,j+1,c+Finsupp.single (i+1,j+1) (d+1)⟩)
    (e : b+Finsupp.single (i+1,j) a=c+Finsupp.single (i,j+1) d) : False := by
  have north := congrArg (fun T : Table => T (i,j+1)) e
  have west := congrArg (fun T : Table => T (i+1,j)) e
  have ob := vb.ver i (j+1) (by simp) (by simp)
  have oc := vc.hor (i+1) j (by simp) (by simp)
  simp [hb,be,hc,cs] at north west ob oc
  omega

private theorem unique_source_aux {s t s' t' : SlideState} (a : Slide s t) (b : Slide s' t')
    (hs : Valid s) (hs' : Valid s') (h : t=t') : s=s' := by
  cases a with
  | east i j u B b0 b1 u1 gu =>
    cases b with
    | east l m v C c0 c1 v1 gv =>
      injection h with ih jh et
      subst l
      obtain rfl := Nat.succ.inj jh
      obtain ⟨rfl,rfl⟩ := empty_add_inj b0 c0 et
      rfl
    | south l m v C c0 c1 gv =>
      injection h with ih jh et
      subst i; subst m
      exact (east_south_output b0 b1 c0 c1 hs hs' et).elim
  | south i j u B b0 b1 gu =>
    cases b with
    | east l m v C c0 c1 v1 gv =>
      injection h with ih jh et
      subst l; subst j
      exact (east_south_output c0 c1 b0 b1 hs' hs et.symm).elim
    | south l m v C c0 c1 gv =>
      injection h with ih jh et
      subst m
      obtain rfl := Nat.succ.inj ih
      obtain ⟨rfl,rfl⟩ := empty_add_inj b0 c0 et
      rfl

theorem slide_prev_unique {s t u : SlideState} (hs : Valid s) (ht : Valid t)
    (a : Slide s u) (b : Slide t u) : s=t := unique_source_aux a b hs ht rfl

end Plane597

open Plane597 in
theorem OMA.solution : type_of% @OMA.S_oeis_a096597.main := by
  apply count_conclusion ordinaryTableEquiv punctTableEquiv
  intro k
  exact (initialEquiv k).symm.trans ((slideEndpoints slide_next slide_prev slide_next_unique
      slide_prev_unique slide_weight slide_potential slide_rank slide_not_terminal k).trans (terminalEquiv k))
