import OMAStatements.S_mo_350931

/-!
A signed-area proof of the three-cell ribbon invariant for rectangles.
The edge labels are integer vectors. On tile boundaries a horizontal edge
has one of three cyclic labels, according to its diagonal, and a vertical
edge has label zero. Adjusting the labels on the two interior edges of each
tile makes each unit square close up. The signed areas of these squares
then telescope over the rectangle. A straight tile contributes zero and
the two bends contribute opposite areas, so their count difference is fixed.

See I. Pak, Ribbon Tile Invariants, Theorem 1.4, and C. Moore and I. Pak,
Ribbon Tile Invariants from the Signed Area, Section 3.
-/

namespace OMA.S_mo_350931

abbrev Vec := ℤ × ℤ

def det (a b : Vec) : ℤ := a.1 * b.2 - a.2 * b.1

/-- Twice the oriented area of the quadrilateral traced by a closed cell. -/
def cellArea (bottom right top left : Vec) : ℤ :=
  det bottom right - det left top

def cellCurl (bottom right top left : Vec) : Vec := bottom + right - top - left

-- For a = r(s), b = r(s+1), c = r(s+2), we have c = -a-b.
-- Entries below are the counterclockwise edge vectors, with top/left
-- given in their positive (east/north) orientations.
theorem horizontal_local (a b : Vec) :
    let c := -a-b
    cellArea a (b-a) b 0 + cellArea b (c-a) c (b-a) + cellArea c 0 a (c-a) = 0 := by
  simp [cellArea, det]
  ring

theorem vertical_local (a : Vec) : cellArea a 0 a 0 = 0 := by
  simp [cellArea, det]

theorem leftDown_local (a b : Vec) :
    let c := -a-b
    cellArea a 0 a 0 + cellArea a (c-a) c 0 + cellArea c 0 a (c-a) = -2 * det a b := by
  simp [cellArea, det]
  ring

theorem downLeft_local (a b : Vec) :
    cellArea a (b-a) b 0 + cellArea b 0 a (b-a) + cellArea a 0 a 0 = 2 * det a b := by
  simp [cellArea, det]
  ring

def triRoot (n : ℕ) : Vec :=
  if n % 3 = 0 then (1,0) else if n % 3 = 1 then (0,1) else (-1,-1)

theorem triRoot_sum (n : ℕ) : triRoot (n+2) = -triRoot n - triRoot (n+1) := by
  have h : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases h with h | h | h <;>
    norm_num [triRoot, h, show (n+1)%3 = (n%3+1)%3 by omega,
      show (n+2)%3 = (n%3+2)%3 by omega]

theorem triRoot_det (n : ℕ) : det (triRoot n) (triRoot (n+1)) = 1 := by
  have h : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases h with h | h | h <;>
    norm_num [triRoot, det, h, show (n+1)%3 = (n%3+1)%3 by omega]

def localH : Placement → ℕ → ℕ → Vec
  | (.horizontal, _, _), x, y => triRoot (x+y)
  | (.vertical, u, v), x, y =>
      if x = u ∧ (y = v+1 ∨ y = v+2) then triRoot (u+v) else triRoot (x+y)
  | (.leftDown, u, v), x, y =>
      if x = u ∧ y = v+1 then triRoot (u+v) else triRoot (x+y)
  | (.downLeft, u, v), x, y =>
      if x = u+1 ∧ y = v+1 then triRoot (u+v) else triRoot (x+y)

def localV : Placement → ℕ → ℕ → Vec
  | (.horizontal, u, v), x, y =>
      if x = u+1 ∧ y = v then triRoot (u+v+1)-triRoot (u+v)
      else if x = u+2 ∧ y = v then triRoot (u+v+2)-triRoot (u+v) else 0
  | (.vertical, _, _), _, _ => 0
  | (.leftDown, u, v), x, y =>
      if x = u+1 ∧ y = v+1 then triRoot (u+v+2)-triRoot (u+v) else 0
  | (.downLeft, u, v), x, y =>
      if x = u+1 ∧ y = v then triRoot (u+v+1)-triRoot (u+v) else 0

def HInternal (p : Placement) (x y : ℕ) : Prop :=
  0 < y ∧ (x,y-1) ∈ cells p ∧ (x,y) ∈ cells p

def VInternal (p : Placement) (x y : ℕ) : Prop :=
  0 < x ∧ (x-1,y) ∈ cells p ∧ (x,y) ∈ cells p

theorem localH_support (p : Placement) (x y : ℕ) (h : ¬ HInternal p x y) :
    localH p x y = triRoot (x+y) := by
  rcases p with ⟨s,u,v⟩
  cases s <;> simp only [localH]
  all_goals split_ifs <;> try rfl
  all_goals exfalso; apply h; simp only [HInternal, cells, Finset.mem_insert,
    Finset.mem_singleton, Prod.mk.injEq]; omega

theorem localV_support (p : Placement) (x y : ℕ) (h : ¬ VInternal p x y) :
    localV p x y = 0 := by
  rcases p with ⟨s,u,v⟩
  cases s <;> simp only [localV]
  all_goals split_ifs <;> try rfl
  all_goals exfalso; apply h; simp only [VInternal, cells, Finset.mem_insert,
    Finset.mem_singleton, Prod.mk.injEq]; omega

theorem triRoot_period (n : ℕ) : triRoot (n+3) = triRoot n := by
  simp [triRoot]

theorem local_curl (p : Placement) (x y : ℕ) (hc : (x,y) ∈ cells p) :
    cellCurl (localH p x y) (localV p (x+1) y)
      (localH p x (y+1)) (localV p x y) = 0 := by
  rcases p with ⟨s,u,v⟩
  cases s <;> simp only [cells, Finset.mem_insert, Finset.mem_singleton,
    Prod.mk.injEq] at hc
  all_goals rcases hc with h | h | h
  all_goals rcases h with ⟨rfl,rfl⟩
  all_goals simp [localH, localV, cellCurl, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm]
  all_goals simp only [← Nat.add_assoc, triRoot_period]; abel

def tileSign : Shape → ℤ
  | .horizontal | .vertical => 0
  | .leftDown => -2
  | .downLeft => 2

def shapeWeight (p : Placement) : ℤ := tileSign p.1

theorem local_area (p : Placement) :
    ∑ z ∈ cells p, cellArea (localH p z.1 z.2) (localV p (z.1+1) z.2)
      (localH p z.1 (z.2+1)) (localV p z.1 z.2) = shapeWeight p := by
  rcases p with ⟨s,u,v⟩
  cases s <;> simp [cells, localH, localV, shapeWeight, tileSign, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm]
  all_goals simp only [triRoot_period, triRoot_sum, ← add_assoc]
  · exact horizontal_local (triRoot (u+v)) (triRoot (u+v+1))
  · simp [vertical_local]
  · simpa only [triRoot_det, mul_one] using
      leftDown_local (triRoot (u+v)) (triRoot (u+v+1))
  · simpa only [triRoot_det, mul_one] using
      downLeft_local (triRoot (u+v)) (triRoot (u+v+1))

namespace Glue

abbrev EdgeField := ℕ → ℕ → ℤ × ℤ

noncomputable def field (T : Finset Placement) (base : EdgeField)
    (loc : Placement → EdgeField) : EdgeField :=
  fun x y => base x y + ∑ p ∈ T, (loc p x y - base x y)

lemma field_eq (T : Finset Placement) (base : EdgeField)
    (loc : Placement → EdgeField) {p : Placement} (hp : p ∈ T) (x y : ℕ)
    (ho : ∀ q ∈ T, q ≠ p → loc q x y = base x y) :
    field T base loc x y = loc p x y := by
  classical
  unfold field
  rw [Finset.sum_eq_single p]
  · abel
  · intro q hq hqp
    simp [ho q hq hqp]
  · exact fun h => (h hp).elim

lemma field_base (T : Finset Placement) (base : EdgeField)
    (loc : Placement → EdgeField) (x y : ℕ)
    (ho : ∀ q ∈ T, loc q x y = base x y) :
    field T base loc x y = base x y := by
  classical
  unfold field
  have hz : (∑ q ∈ T, (loc q x y - base x y)) = 0 := by
    apply Finset.sum_eq_zero
    intro q hq
    simp only [ho q hq, sub_self]
  rw [hz, add_zero]

lemma not_mem_other {T : Finset Placement}
    (hd : (T : Set Placement).PairwiseDisjoint cells)
    {p q : Placement} (hp : p ∈ T) (hq : q ∈ T) (hqp : q ≠ p)
    {c : ℕ × ℕ} (hc : c ∈ cells p) : c ∉ cells q := by
  exact fun h => Finset.disjoint_left.mp (hd hp hq (Ne.symm hqp)) hc h

variable {T : Finset Placement} {H₀ V₀ : EdgeField}
  {H V : Placement → EdgeField}

lemma bottom_agree (hd : (T : Set Placement).PairwiseDisjoint cells)
    (support : ∀ p ∈ T, ∀ x y, ¬ HInternal p x y → H p x y = H₀ x y)
    {p : Placement} (hp : p ∈ T) {x y : ℕ} (hc : (x,y) ∈ cells p) :
    field T H₀ H x y = H p x y := by
  apply field_eq T H₀ H hp
  intro q hq hqp
  apply support q hq
  intro hi
  exact not_mem_other hd hp hq hqp hc hi.2.2

lemma top_agree (hd : (T : Set Placement).PairwiseDisjoint cells)
    (support : ∀ p ∈ T, ∀ x y, ¬ HInternal p x y → H p x y = H₀ x y)
    {p : Placement} (hp : p ∈ T) {x y : ℕ} (hc : (x,y) ∈ cells p) :
    field T H₀ H x (y+1) = H p x (y+1) := by
  apply field_eq T H₀ H hp
  intro q hq hqp
  apply support q hq
  intro hi
  exact not_mem_other hd hp hq hqp hc (by simpa using hi.2.1)

lemma left_agree (hd : (T : Set Placement).PairwiseDisjoint cells)
    (support : ∀ p ∈ T, ∀ x y, ¬ VInternal p x y → V p x y = V₀ x y)
    {p : Placement} (hp : p ∈ T) {x y : ℕ} (hc : (x,y) ∈ cells p) :
    field T V₀ V x y = V p x y := by
  apply field_eq T V₀ V hp
  intro q hq hqp
  apply support q hq
  intro hi
  exact not_mem_other hd hp hq hqp hc hi.2.2

lemma right_agree (hd : (T : Set Placement).PairwiseDisjoint cells)
    (support : ∀ p ∈ T, ∀ x y, ¬ VInternal p x y → V p x y = V₀ x y)
    {p : Placement} (hp : p ∈ T) {x y : ℕ} (hc : (x,y) ∈ cells p) :
    field T V₀ V (x+1) y = V p (x+1) y := by
  apply field_eq T V₀ V hp
  intro q hq hqp
  apply support q hq
  intro hi
  exact not_mem_other hd hp hq hqp hc (by simpa using hi.2.1)

lemma bottom_boundary
    (support : ∀ p ∈ T, ∀ x y, ¬ HInternal p x y → H p x y = H₀ x y)
    (x : ℕ) : field T H₀ H x 0 = H₀ x 0 := by
  apply field_base
  intro p hp
  exact support p hp x 0 (by simp [HInternal])

lemma left_boundary
    (support : ∀ p ∈ T, ∀ x y, ¬ VInternal p x y → V p x y = V₀ x y)
    (y : ℕ) : field T V₀ V 0 y = V₀ 0 y := by
  apply field_base
  intro p hp
  exact support p hp 0 y (by simp [VInternal])

lemma cell_in_rectangle {w h : ℕ} (ht : Tiles w h T)
    {p : Placement} (hp : p ∈ T) {c : ℕ × ℕ} (hc : c ∈ cells p) :
    c ∈ rectangle w h := by
  rw [← ht.1]
  exact Finset.mem_biUnion.mpr ⟨p,hp,hc⟩

lemma top_boundary {w h : ℕ} (ht : Tiles w h T)
    (support : ∀ p ∈ T, ∀ x y, ¬ HInternal p x y → H p x y = H₀ x y)
    (x : ℕ) : field T H₀ H x h = H₀ x h := by
  apply field_base
  intro p hp
  apply support p hp
  intro hi
  have hh := cell_in_rectangle ht hp hi.2.2
  simp [rectangle] at hh

lemma right_boundary {w h : ℕ} (ht : Tiles w h T)
    (support : ∀ p ∈ T, ∀ x y, ¬ VInternal p x y → V p x y = V₀ x y)
    (y : ℕ) : field T V₀ V w y = V₀ w y := by
  apply field_base
  intro p hp
  apply support p hp
  intro hi
  have hh := cell_in_rectangle ht hp hi.2.2
  simp [rectangle] at hh

/-- Any functional of the four edge values, in bottom/right/top/left order. -/
def integrand (A : (ℤ × ℤ) → (ℤ × ℤ) → (ℤ × ℤ) → (ℤ × ℤ) → ℤ)
    (H V : EdgeField) (c : ℕ × ℕ) : ℤ :=
  A (H c.1 c.2) (V (c.1+1) c.2) (H c.1 (c.2+1)) (V c.1 c.2)

lemma integrand_agree
    (A : (ℤ × ℤ) → (ℤ × ℤ) → (ℤ × ℤ) → (ℤ × ℤ) → ℤ)
    (hd : (T : Set Placement).PairwiseDisjoint cells)
    (hs : ∀ p ∈ T, ∀ x y, ¬ HInternal p x y → H p x y = H₀ x y)
    (vs : ∀ p ∈ T, ∀ x y, ¬ VInternal p x y → V p x y = V₀ x y)
    {p : Placement} (hp : p ∈ T) {c : ℕ × ℕ} (hc : c ∈ cells p) :
    integrand A (field T H₀ H) (field T V₀ V) c = integrand A (H p) (V p) c := by
  unfold integrand
  rw [bottom_agree hd hs hp hc, right_agree hd vs hp hc,
    top_agree hd hs hp hc, left_agree hd vs hp hc]

lemma sum_integrand {w h : ℕ} (ht : Tiles w h T)
    (A : (ℤ × ℤ) → (ℤ × ℤ) → (ℤ × ℤ) → (ℤ × ℤ) → ℤ)
    (hs : ∀ p ∈ T, ∀ x y, ¬ HInternal p x y → H p x y = H₀ x y)
    (vs : ∀ p ∈ T, ∀ x y, ¬ VInternal p x y → V p x y = V₀ x y) :
    (∑ p ∈ T, ∑ c ∈ cells p, integrand A (H p) (V p) c) =
      ∑ c ∈ rectangle w h, integrand A (field T H₀ H) (field T V₀ V) c := by
  classical
  rw [← ht.1, Finset.sum_biUnion ht.2]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro c hc
  exact (integrand_agree A ht.2 hs vs hp hc).symm

end Glue
namespace Stokes

abbrev Field := Glue.EdgeField

/-- Integrate east along the bottom, then north in the destination column. -/
def potential (H V : Field) (x y : ℕ) : ℤ × ℤ :=
  (∑ i ∈ Finset.range x, H i 0) + ∑ j ∈ Finset.range y, V x j

def Flat (w h : ℕ) (H V : Field) : Prop :=
  ∀ x < w, ∀ y < h, H x y + V (x+1) y = V x y + H x (y+1)

theorem potential_up (H V : Field) (x y : ℕ) :
    potential H V x (y+1) = potential H V x y + V x y := by
  simp [potential, Finset.sum_range_succ, add_assoc]

theorem potential_right {H V : Field} {w h : ℕ} (flat : Flat w h H V)
    {x : ℕ} (hx : x < w) {y : ℕ} (hy : y ≤ h) :
    potential H V (x+1) y = potential H V x y + H x y := by
  induction y with
  | zero => simp [potential, Finset.sum_range_succ]
  | succ y ih =>
    rw [potential_up, potential_up, ih (by omega), add_assoc, flat x hx y (by omega), add_assoc]

def integratedArea (H V : Field) (x y : ℕ) : ℤ :=
  det (H x y) (V (x+1) y) - det (V x y) (H x (y+1))

def fluxH (H V : Field) (x y : ℕ) := det (potential H V x y) (H x y)
def fluxV (H V : Field) (x y : ℕ) := det (potential H V x y) (V x y)

theorem cell_flux {H V : Field} {w h x y : ℕ} (flat : Flat w h H V) (hx : x < w) (hy : y < h) :
    integratedArea H V x y = (fluxV H V (x+1) y - fluxV H V x y)
        - (fluxH H V x (y+1) - fluxH H V x y) := by
  have e := flat x hx y hy
  have e₁ := congrArg Prod.fst e
  have e₂ := congrArg Prod.snd e
  dsimp at e₁ e₂
  unfold integratedArea fluxH fluxV
  rw [potential_right flat hx (by omega), potential_up]
  simp only [det, Prod.fst_add, Prod.snd_add]
  linear_combination (potential H V x y).2 * e₁ - (potential H V x y).1 * e₂

private theorem telescope (f : ℕ → ℤ) (n : ℕ) :
    ∑ i ∈ Finset.range n, (f (i+1) - f i) = f n - f 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; ring

/-- Summing cell areas cancels each internal edge with its opposite orientation. -/
theorem boundary_formula {H V : Field} {w h : ℕ} (flat : Flat w h H V) :
    ∑ c ∈ rectangle w h, integratedArea H V c.1 c.2 =
      (∑ y ∈ Finset.range h, (fluxV H V w y - fluxV H V 0 y)) -
      ∑ x ∈ Finset.range w, (fluxH H V x h - fluxH H V x 0) := by
  rw [rectangle, Finset.sum_product]
  calc
    _ = ∑ x ∈ Finset.range w, ∑ y ∈ Finset.range h,
          ((fluxV H V (x+1) y - fluxV H V x y) -
          (fluxH H V x (y+1) - fluxH H V x y)) := by
      apply Finset.sum_congr rfl
      intro x hx
      exact Finset.sum_congr rfl fun y hy =>
        cell_flux flat (Finset.mem_range.mp hx) (Finset.mem_range.mp hy)
    _ = (∑ x ∈ Finset.range w, ∑ y ∈ Finset.range h,
              (fluxV H V (x+1) y - fluxV H V x y)) -
          ∑ x ∈ Finset.range w, ∑ y ∈ Finset.range h,
              (fluxH H V x (y+1) - fluxH H V x y) := by
      simp only [Finset.sum_sub_distrib]
    _ = _ := by
      rw [Finset.sum_comm]
      congr 1
      · exact Finset.sum_congr rfl fun y _ => telescope (fun x => fluxV H V x y) w
      · exact Finset.sum_congr rfl fun x _ => telescope (fluxH H V x) h

private theorem potential_top {H V : Field} {w h : ℕ} (B : Field) (flat : Flat w h H V)
    (top : ∀ x, H x h = B x h) (left : ∀ y, V 0 y = 0) {x : ℕ} (hx : x ≤ w) :
    potential H V x h = ∑ i ∈ Finset.range x, B i h := by
  induction x with
  | zero => simp [potential, left]
  | succ x ih =>
    rw [potential_right flat (by omega) le_rfl, ih (by omega), top, Finset.sum_range_succ]

private theorem boundary_value {H V : Field} {w h : ℕ} (B : Field) (flat : Flat w h H V)
    (hb : ∀ x, H x 0 = B x 0) (ht : ∀ x, H x h = B x h)
    (vl : ∀ y, V 0 y = 0) (vr : ∀ y, V w y = 0) :
    ∑ c ∈ rectangle w h, integratedArea H V c.1 c.2 =
    -(∑ x ∈ Finset.range w,
      (det (∑ i ∈ Finset.range x, B i h) (B x h) -
       det (∑ i ∈ Finset.range x, B i 0) (B x 0))) := by
  rw [boundary_formula flat]
  simp only [fluxV, vr, vl, det, Prod.snd_zero, Prod.fst_zero, mul_zero, sub_self,
    Finset.sum_const_zero, zero_sub, neg_inj]
  apply Finset.sum_congr rfl
  intro x hx
  unfold fluxH
  rw [potential_top B flat ht vl (Finset.mem_range.mp hx).le, ht, hb]
  simp [potential, hb, det]

theorem boundary_invariant {w h : ℕ} {H V H' V' : Field} (B : Field)
    (flat : Flat w h H V) (flat' : Flat w h H' V')
    (hb : ∀ x, H x 0 = B x 0) (ht : ∀ x, H x h = B x h)
    (vl : ∀ y, V 0 y = 0) (vr : ∀ y, V w y = 0)
    (hb' : ∀ x, H' x 0 = B x 0) (ht' : ∀ x, H' x h = B x h)
    (vl' : ∀ y, V' 0 y = 0) (vr' : ∀ y, V' w y = 0) :
    (∑ c ∈ rectangle w h, integratedArea H V c.1 c.2) =
      ∑ c ∈ rectangle w h, integratedArea H' V' c.1 c.2 := by
  rw [boundary_value B flat hb ht vl vr, boundary_value B flat' hb' ht' vl' vr']

end Stokes
namespace Assemble

noncomputable def globalH (T : Finset Placement) : Glue.EdgeField :=
  Glue.field T (fun x y => triRoot (x+y)) localH
noncomputable def globalV (T : Finset Placement) : Glue.EdgeField :=
  Glue.field T (fun _ _ => 0) localV

lemma h_support (T : Finset Placement) :
    ∀ p ∈ T, ∀ x y, ¬ HInternal p x y → localH p x y = triRoot (x+y) :=
  fun p _ x y h => localH_support p x y h
lemma v_support (T : Finset Placement) :
    ∀ p ∈ T, ∀ x y, ¬ VInternal p x y → localV p x y = 0 :=
  fun p _ x y h => localV_support p x y h

lemma global_flat {w h : ℕ} {T : Finset Placement} (ht : Tiles w h T) :
    Stokes.Flat w h (globalH T) (globalV T) := by
  intro x hx y hy
  have hc : (x,y) ∈ T.biUnion cells := by
    rw [ht.1]
    simp [rectangle, hx, hy]
  obtain ⟨p,hp,hc⟩ := Finset.mem_biUnion.mp hc
  dsimp [globalH, globalV]
  rw [Glue.bottom_agree ht.2 (h_support T) hp hc,
    Glue.right_agree ht.2 (v_support T) hp hc,
    Glue.left_agree ht.2 (v_support T) hp hc,
    Glue.top_agree ht.2 (h_support T) hp hc]
  have e := local_curl p x y hc
  dsimp [cellCurl] at e
  have e := sub_eq_zero.mp e
  simpa [add_comm] using sub_eq_iff_eq_add.mp e

lemma total_area {w h : ℕ} {T : Finset Placement} (ht : Tiles w h T) :
    (∑ p ∈ T, shapeWeight p) =
      ∑ c ∈ rectangle w h, Stokes.integratedArea (globalH T) (globalV T) c.1 c.2 := by
  calc
    _ = ∑ p ∈ T, ∑ c ∈ cells p, Glue.integrand cellArea (localH p) (localV p) c :=
      Finset.sum_congr rfl fun p _ => (local_area p).symm
    _ = _ := Glue.sum_integrand ht cellArea (h_support T) (v_support T)

lemma signed_invariant {w h : ℕ} {T U : Finset Placement}
    (ht : Tiles w h T) (hu : Tiles w h U) :
    (∑ p ∈ T, shapeWeight p) = ∑ p ∈ U, shapeWeight p := by
  rw [total_area ht, total_area hu]
  exact Stokes.boundary_invariant (fun x y => triRoot (x+y))
    (global_flat ht) (global_flat hu)
    (Glue.bottom_boundary (h_support T)) (Glue.top_boundary ht (h_support T))
    (Glue.left_boundary (v_support T)) (Glue.right_boundary ht (v_support T))
    (Glue.bottom_boundary (h_support U)) (Glue.top_boundary hu (h_support U))
    (Glue.left_boundary (v_support U)) (Glue.right_boundary hu (v_support U))

end Assemble

def countShape (s : Shape) (T : Finset Placement) : ℕ :=
  (T.filter (fun p => p.1 = s)).card

theorem count_formulas (T : Finset Placement) :
    lCount T = countShape .leftDown T + countShape .downLeft T ∧
    ∑ p ∈ T, shapeWeight p =
      2 * ((countShape .downLeft T : ℤ) - (countShape .leftDown T : ℤ)) := by
  induction T using Finset.induction_on with
  | empty => simp [countShape, lCount]
  | @insert p T h ih =>
    obtain ⟨s, x, y⟩ := p
    obtain ⟨hcount, hsum⟩ := ih
    unfold countShape lCount at *
    simp only [shapeWeight, tileSign] at hsum
    cases s <;> simp [Finset.filter_insert, Finset.sum_insert, shapeWeight, tileSign,
      h, hcount, hsum] <;> omega

/-- Pak's signed orientation count for two tilings of the same rectangle. -/
theorem orientation_difference {w h : ℕ} {T U : Finset Placement}
    (ht : Tiles w h T) (hu : Tiles w h U) :
    (countShape .downLeft T : ℤ) - countShape .leftDown T =
      (countShape .downLeft U : ℤ) - countShape .leftDown U := by
  have e := Assemble.signed_invariant ht hu
  rw [(count_formulas T).2, (count_formulas U).2] at e
  omega

end OMA.S_mo_350931

open OMA.S_mo_350931 in
theorem OMA.solution : type_of% @OMA.S_mo_350931.main := by
  rintro w h _ _ ⟨T, ht, he⟩ U hu
  have e := orientation_difference ht hu
  rw [(count_formulas T).1, Nat.even_iff] at he
  rw [(count_formulas U).1, Nat.even_iff]
  omega
