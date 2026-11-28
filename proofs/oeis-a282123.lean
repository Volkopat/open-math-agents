import OMAStatements.S_oeis_a282123

-- Problem: A282123, the left half-axis of Rule 430.
-- Credit: @RiverMint78

open OMA.S_oeis_a282123 (cell a)
open scoped BigOperators

private abbrev Grid := ℤ → ℤ → Bool

private def total (r l u d : Bool) : ℕ := r.toNat + l.toNat + u.toNat + d.toNat

private def rule (c r l u d : Bool) : Bool :=
  (430 : ℕ).testBit (c.toNat + 2 * total r l u d)

private def tick (g : Grid) (x y : ℤ) : Bool :=
  rule (g x y) (g (x + 1) y) (g (x - 1) y) (g x (y + 1)) (g x (y - 1))

private theorem cell_tick (t : ℕ) : cell 430 (t + 1) = tick (cell 430 t) := rfl

private def seed (x y : ℤ) : Bool := decide (x = 0 ∧ y = 0)

private def neighbours (g : Grid) (x y : ℤ) : ℕ :=
  total (g (x + 1) y) (g (x - 1) y) (g x (y + 1)) (g x (y - 1))

/-- A coarse vertex stays on, or is born when it has exactly one on neighbour. -/
private def grow (g : Grid) (x y : ℤ) : Bool := g x y || decide (neighbours g x y = 1)

private def coarse : ℕ → Grid
  | 0 => seed
  | t + 1 => grow (coarse t)

private theorem persists (t : ℕ) (x y : ℤ) (h : coarse t x y = true) :
    coarse (t + 1) x y = true := by
  change grow (coarse t) x y = true
  simp [grow, h]

private theorem count_increases (t : ℕ) (x y : ℤ) :
    neighbours (coarse t) x y ≤ neighbours (coarse (t + 1)) x y := by
  have h (i j : ℤ) : (coarse t i j).toNat ≤ (coarse (t + 1) i j).toNat := by
    cases h₀ : coarse t i j with
    | false => simp
    | true => simp [persists t i j h₀]
  have hr := h (x + 1) y
  have hl := h (x - 1) y
  have hu := h x (y + 1)
  have hd := h x (y - 1)
  unfold neighbours total
  omega

private theorem count_zero {r l u d : Bool} (h : total r l u d = 0) :
    r = false ∧ l = false ∧ u = false ∧ d = false := by
  cases r <;> cases l <;> cases u <;> cases d <;> simp_all [total]

private theorem count_pos {r l u d : Bool} (h : 0 < total r l u d) :
    r = true ∨ l = true ∨ u = true ∨ d = true := by
  cases r <;> cases l <;> cases u <;> cases d <;> simp_all [total]

private theorem birth_neighbours {t : ℕ} {x y : ℤ} (h : coarse t x y = false)
    (h' : coarse (t + 1) x y = true) : neighbours (coarse t) x y = 1 := by
  change (coarse t x y || decide (neighbours (coarse t) x y = 1)) = true at h'
  simpa [h] using h'

/-- A birth in step t+1 comes from a neighbour born in step t.
Consequently two adjacent coarse vertices cannot be born in the same step. -/
private theorem birth_parity (t : ℕ) (x y : ℤ) (h : coarse t x y = false)
    (h' : coarse (t + 1) x y = true) : (x + y) % 2 = ((t + 1 : ℕ) : ℤ) % 2 := by
  induction t generalizing x y with
  | zero =>
    have hsum := birth_neighbours h h'
    have hsome := count_pos (show 0 < neighbours (coarse 0) x y by omega)
    change decide (x + 1 = 0 ∧ y = 0) = true ∨
      decide (x - 1 = 0 ∧ y = 0) = true ∨
      decide (x = 0 ∧ y + 1 = 0) = true ∨
      decide (x = 0 ∧ y - 1 = 0) = true at hsome
    simp only [decide_eq_true_eq] at hsome
    rcases hsome with hr | hl | hu | hd <;> norm_num <;> omega
  | succ t ih =>
    have hsum := birth_neighbours h h'
    have hne : neighbours (coarse t) x y ≠ 1 := by
      intro he
      change grow (coarse t) x y = false at h
      simp [grow, he] at h
    have hz : neighbours (coarse t) x y = 0 := by
      have hm := count_increases t x y
      omega
    obtain ⟨hr, hl, hu, hd⟩ := count_zero hz
    have hsome := count_pos (show 0 < neighbours (coarse (t + 1)) x y by omega)
    rcases hsome with hn | hn | hn | hn
    · have hh := ih (x + 1) y hr hn
      push_cast at hh ⊢
      omega
    · have hh := ih (x - 1) y hl hn
      push_cast at hh ⊢
      omega
    · have hh := ih x (y + 1) hu hn
      push_cast at hh ⊢
      omega
    · have hh := ih x (y - 1) hd hn
      push_cast at hh ⊢
      omega

private theorem isolated_births {t : ℕ} {x y x' y' : ℤ}
    (hpar : (x + y) % 2 ≠ (x' + y') % 2)
    (h : coarse t x y = false) (h' : coarse t x' y' = false)
    (hn : grow (coarse t) x y = true) (hn' : grow (coarse t) x' y' = true) : False :=
  hpar ((birth_parity t x y h hn).trans (birth_parity t x' y' h' hn').symm)

private def vertex (g : Grid) (i j : ℤ) := g (2 * i) (2 * j)
private def east (g : Grid) (i j : ℤ) := g (2 * i + 1) (2 * j)
private def north (g : Grid) (i j : ℤ) := g (2 * i) (2 * j + 1)
private def face (g : Grid) (i j : ℤ) := g (2 * i + 1) (2 * j + 1)

private theorem tick_vertex (g : Grid) (i j : ℤ) :
    vertex (tick g) i j =
      rule (vertex g i j) (east g i j) (east g (i - 1) j) (north g i j) (north g i (j - 1)) := by
  simp [vertex, tick, east, north, show 2*i - 1 = 2*(i-1)+1 by ring,
    show 2*j - 1 = 2*(j-1)+1 by ring]

private theorem tick_east (g : Grid) (i j : ℤ) :
    east (tick g) i j =
      rule (east g i j) (vertex g (i + 1) j) (vertex g i j) (face g i j) (face g i (j - 1)) := by
  simp [vertex, tick, east, face, show 2*i+1+1 = 2*(i+1) by ring,
    show 2*j-1 = 2*(j-1)+1 by ring]

private theorem tick_north (g : Grid) (i j : ℤ) :
    north (tick g) i j =
      rule (north g i j) (face g i j) (face g (i - 1) j) (vertex g i (j + 1)) (vertex g i j) := by
  simp [vertex, tick, north, face, show 2*j+1+1 = 2*(j+1) by ring,
    show 2*i-1 = 2*(i-1)+1 by ring]

private theorem tick_face (g : Grid) (i j : ℤ) :
    face (tick g) i j =
      rule (face g i j) (north g (i + 1) j) (north g i j) (east g i (j + 1)) (east g i j) := by
  simp [tick, north, east, face, show 2*i+1+1 = 2*(i+1) by ring,
    show 2*j+1+1 = 2*(j+1) by ring]


private def vertexRule (c r l u d : Bool) : Bool :=
  rule c (c || r) (l || c) (c || u) (d || c)

private def faceRule (a b c d : Bool) : Bool :=
  rule false (b || d) (a || c) (c || d) (a || b)

private def middleVertex (v : Grid) (i j : ℤ) : Bool :=
  vertexRule (v i j) (v (i + 1) j) (v (i - 1) j) (v i (j + 1)) (v i (j - 1))

private def middleFace (v : Grid) (i j : ℤ) : Bool :=
  faceRule (v i j) (v (i + 1) j) (v i (j + 1)) (v (i + 1) (j + 1))

private theorem rule_axes (c r l u d : Bool) : rule c r l u d = rule c u d r l := by
  unfold rule total
  congr 1
  omega

private theorem edge_fixed (a b : Bool) : rule (a || b) b a false false = (a || b) := by
  cases a <;> cases b <;> decide

private theorem vertex_twice (c r l u d : Bool) :
    rule (vertexRule c r l u d) (c || r) (l || c) (c || u) (d || c) =
      (c || decide (total r l u d = 1)) := by
  cases c <;> cases r <;> cases l <;> cases u <;> cases d <;> decide

private theorem face_twice (a b c d : Bool) :
    rule (faceRule a b c d) (b || d) (a || c) (c || d) (a || b) = false := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

private theorem vertex_middle_of_on (r l u d : Bool) : vertexRule true r l u d = false := by
  cases r <;> cases l <;> cases u <;> cases d <;> decide

private theorem vertex_middle_of_off (r l u d : Bool) :
    (r = false ∨ l = false ∨ u = false ∨ d = false) →
      vertexRule false r l u d = decide (total r l u d = 1) := by
  cases r <;> cases l <;> cases u <;> cases d <;> decide

private theorem face_middle_of_off_edge (a b c d : Bool) :
    ((a = false ∧ b = false) ∨ (a = false ∧ c = false) ∨
      (b = false ∧ d = false) ∨ (c = false ∧ d = false)) → faceRule a b c d = false := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

private theorem keep_on (r l u d : Bool) :
    (r = false ∨ l = false ∨ u = false ∨ d = false) → rule true r l u d = true := by
  cases r <;> cases l <;> cases u <;> cases d <;> decide

private theorem edge_with_two_off (r l : Bool) :
    (r = true → l = true → False) → rule false r l false false = (l || r) := by
  cases r <;> cases l <;> decide

/-- The four parity classes consist of coarse vertices, horizontal and vertical edges,
and face centers. An edge is on exactly when an incident coarse vertex is on. -/
private structure Encoded (g v : Grid) : Prop where
  vertex_eq : ∀ i j, vertex g i j = v i j
  east_eq : ∀ i j, east g i j = (v i j || v (i + 1) j)
  north_eq : ∀ i j, north g i j = (v i j || v i (j + 1))
  face_eq : ∀ i j, face g i j = false

private structure Intermediate (g v : Grid) : Prop where
  vertex_eq : ∀ i j, vertex g i j = middleVertex v i j
  east_eq : ∀ i j, east g i j = (v i j || v (i + 1) j)
  north_eq : ∀ i j, north g i j = (v i j || v i (j + 1))
  face_eq : ∀ i j, face g i j = middleFace v i j

private theorem first_half {g v : Grid} (h : Encoded g v) : Intermediate (tick g) v := by
  constructor
  · intro i j
    simp [tick_vertex, h.vertex_eq, h.east_eq, h.north_eq, middleVertex, vertexRule]
  · intro i j
    rw [tick_east, h.east_eq, h.vertex_eq, h.vertex_eq, h.face_eq, h.face_eq]
    exact edge_fixed _ _
  · intro i j
    rw [tick_north, h.north_eq, h.face_eq, h.face_eq, h.vertex_eq, h.vertex_eq, rule_axes]
    exact edge_fixed _ _
  · intro i j
    simp [tick_face, h.face_eq, h.east_eq, h.north_eq, middleFace, faceRule]

private theorem middle_on {v : Grid} {i j : ℤ} (h : v i j = true) :
    middleVertex v i j = false := by
  simp only [middleVertex, h]
  exact vertex_middle_of_on _ _ _ _

private theorem middle_off {v : Grid} {i j : ℤ} (h : v i j = false)
    (hnear : v (i + 1) j = false ∨ v (i - 1) j = false ∨
      v i (j + 1) = false ∨ v i (j - 1) = false) :
    middleVertex v i j = grow v i j := by
  simp only [middleVertex, grow, h, Bool.false_or, neighbours]
  exact vertex_middle_of_off _ _ _ _ hnear

private theorem finish_edge {t : ℕ} {i j i' j' : ℤ} {up down : Bool}
    (hpar : (i + j) % 2 ≠ (i' + j') % 2)
    (hnear : coarse t i' j' = false → coarse t (i + 1) j = false ∨
      coarse t (i - 1) j = false ∨ coarse t i (j + 1) = false ∨ coarse t i (j - 1) = false)
    (hnear' : coarse t i j = false → coarse t (i' + 1) j' = false ∨
      coarse t (i' - 1) j' = false ∨ coarse t i' (j' + 1) = false ∨ coarse t i' (j' - 1) = false)
    (hfaces : coarse t i j = false → coarse t i' j' = false → up = false ∧ down = false) :
    rule (coarse t i j || coarse t i' j') (middleVertex (coarse t) i' j')
      (middleVertex (coarse t) i j) up down =
        (grow (coarse t) i j || grow (coarse t) i' j') := by
  cases h₁ : coarse t i j with
  | true =>
    have hm := middle_on h₁
    have hg : grow (coarse t) i j = true := persists t i j h₁
    simp only [Bool.true_or, hm, hg]
    apply keep_on
    exact Or.inr (Or.inl rfl)
  | false =>
    cases h₂ : coarse t i' j' with
    | true =>
      have hm := middle_on h₂
      have hg : grow (coarse t) i' j' = true := persists t i' j' h₂
      simp only [Bool.or_true, hm, hg]
      apply keep_on
      exact Or.inl rfl
    | false =>
      obtain ⟨hf, hf'⟩ := hfaces h₁ h₂
      simp only [Bool.false_or, middle_off h₁ (hnear h₂), middle_off h₂ (hnear' h₁), hf, hf']
      apply edge_with_two_off
      intro h₂' h₁'
      exact isolated_births hpar h₁ h₂ h₁' h₂'

private theorem second_half {g : Grid} {t : ℕ} (h : Intermediate g (coarse t)) :
    Encoded (tick g) (coarse (t + 1)) := by
  change Encoded (tick g) (grow (coarse t))
  constructor
  · intro i j
    simp [tick_vertex, h.vertex_eq, h.east_eq, h.north_eq, middleVertex, neighbours, grow,
      vertex_twice]
    rfl
  · intro i j
    rw [tick_east, h.east_eq, h.vertex_eq, h.vertex_eq, h.face_eq, h.face_eq]
    apply finish_edge (by omega)
    · exact Or.inl
    · intro hx
      exact Or.inr (Or.inl (by simpa using hx))
    · intro hl hr
      constructor
      · apply face_middle_of_off_edge
        exact Or.inl ⟨hl, hr⟩
      · apply face_middle_of_off_edge
        exact Or.inr (Or.inr (Or.inr (by simpa using And.intro hl hr)))
  · intro i j
    rw [tick_north, h.north_eq, h.face_eq, h.face_eq, h.vertex_eq, h.vertex_eq, rule_axes]
    apply finish_edge (by omega)
    · intro hv
      exact Or.inr (Or.inr (Or.inl hv))
    · intro hx
      exact Or.inr (Or.inr (Or.inr (by simpa using hx)))
    · intro hb ht
      constructor
      · apply face_middle_of_off_edge
        exact Or.inr (Or.inl ⟨hb, ht⟩)
      · apply face_middle_of_off_edge
        exact Or.inr (Or.inr (Or.inl (by simpa using And.intro hb ht)))
  · intro i j
    simp [tick_face, h.face_eq, h.east_eq, h.north_eq, middleFace, face_twice]

private theorem bool_ext {a b : Bool} (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

private theorem rule_with_at_most_one (c r l u d : Bool) :
    total r l u d ≤ 1 → rule c r l u d = (c || r || l || u || d) := by
  cases c <;> cases r <;> cases l <;> cases u <;> cases d <;> decide

private theorem seed_tick (x y : ℤ) :
    tick seed x y = decide ((x = 0 ∧ y = 0) ∨ (x + 1 = 0 ∧ y = 0) ∨
      (x - 1 = 0 ∧ y = 0) ∨ (x = 0 ∧ y + 1 = 0) ∨ (x = 0 ∧ y - 1 = 0)) := by
  unfold tick
  have hs : total (seed (x + 1) y) (seed (x - 1) y) (seed x (y + 1)) (seed x (y - 1)) ≤ 1 := by
    unfold seed
    by_cases hr : x + 1 = 0 ∧ y = 0 <;>
      by_cases hl : x - 1 = 0 ∧ y = 0 <;>
      by_cases hu : x = 0 ∧ y + 1 = 0 <;>
      by_cases hd : x = 0 ∧ y - 1 = 0 <;>
      simp [hr, hl, hu, hd, total] <;> omega
  rw [rule_with_at_most_one _ _ _ _ _ hs]
  apply bool_ext
  simp [seed, Bool.or_eq_true, or_assoc]

private theorem first_encoded : Encoded (tick seed) (coarse 0) := by
  constructor <;> intro i j <;>
    simp only [vertex, east, north, face, coarse, seed_tick, seed] <;>
    apply bool_ext <;> simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.false_eq_true]
  all_goals first
  | omega
  | have hi : 2*i + 1 ≠ 0 := by omega
    have hj : 2*j + 1 ≠ 0 := by omega
    simp [hi, hj]

private theorem odd_encoded (t : ℕ) : Encoded (cell 430 (2 * t + 1)) (coarse t) := by
  induction t with
  | zero => exact first_encoded
  | succ t h =>
    rw [show 2 * (t + 1) + 1 = (2*t+1)+1+1 by omega, cell_tick, cell_tick]
    exact second_half (first_half h)

private theorem even_intermediate (t : ℕ) :
    Intermediate (cell 430 (2 * t + 2)) (coarse t) := by
  rw [show 2 * t + 2 = (2*t+1)+1 by omega, cell_tick]
  exact first_half (odd_encoded t)


private theorem abs_near (x : ℤ) : |x| ≤ |x + 1| + 1 ∧ |x| ≤ |x - 1| + 1 := by
  constructor
  · simpa using (abs_add_le (x+1) (-1))
  · simpa using (abs_add_le (x-1) 1)

private theorem coarse_outside (t : ℕ) (x y : ℤ) (h : (t : ℤ) < |x| + |y|) :
    coarse t x y = false := by
  induction t generalizing x y with
  | zero =>
    change decide (x = 0 ∧ y = 0) = false
    apply decide_eq_false_iff_not.mpr
    rintro ⟨rfl, rfl⟩
    norm_num at h
  | succ t ih =>
    have hx := abs_near x
    have hy := abs_near y
    have h₀ := ih x y (by omega)
    have hr := ih (x+1) y (by omega)
    have hl := ih (x-1) y (by omega)
    have hu := ih x (y+1) (by omega)
    have hd := ih x (y-1) (by omega)
    change grow (coarse t) x y = false
    simp [grow, neighbours, total, h₀, hr, hl, hu, hd]

private theorem left_boundary_count (t : ℕ) (h : coarse t (-(t : ℤ)) 0 = true) :
    neighbours (coarse t) (-(t : ℤ) - 1) 0 = 1 := by
  let x := -(t : ℤ) - 1
  change neighbours (coarse t) x 0 = 1
  have hx : x < 0 := by dsimp [x]; omega
  have hd : coarse t (x - 1) 0 = false := by
    apply coarse_outside
    rw [abs_zero, add_zero, abs_of_neg (by omega : x - 1 < 0)]
    dsimp [x]
    omega
  have hfar (w : ℤ) (hw : |w| = 1) : coarse t x w = false := by
    apply coarse_outside
    rw [hw, abs_of_neg hx]
    dsimp [x]
    omega
  have hr : coarse t (x + 1) 0 = true := by
    simpa [x] using h
  simpa [neighbours, total, hr, hd] using
    (show (1 : ℕ) + 0 + (coarse t x 1).toNat + (coarse t x (-1)).toNat = 1 by
      rw [hfar 1 (by norm_num), hfar (-1) (by norm_num)]
      decide)

private theorem coarse_left (t : ℕ) (x : ℤ) (hlo : -(t : ℤ) ≤ x) (hhi : x ≤ 0) :
    coarse t x 0 = true := by
  induction t generalizing x with
  | zero =>
    have hx : x = 0 := by omega
    simp [coarse, seed, hx]
  | succ t ih =>
    by_cases h : -(t : ℤ) ≤ x
    · exact persists t x 0 (ih x h hhi)
    · have hx : x = -(t : ℤ) - 1 := by omega
      rw [hx]
      change grow (coarse t) (-(t : ℤ) - 1) 0 = true
      simp [grow, left_boundary_count t (ih (-(t : ℤ)) (by omega) (by omega))]

private theorem odd_left (t r : ℕ) (h : r ≤ 2 * t + 1) :
    cell 430 (2 * t + 1) (-(r : ℤ)) 0 = true := by
  obtain ⟨s, rfl | rfl⟩ := Nat.even_or_odd' r
  · rw [show -((2*s : ℕ) : ℤ) = 2 * (-(s : ℤ)) by push_cast; ring]
    change vertex (cell 430 (2 * t + 1)) (-(s : ℤ)) 0 = true
    rw [(odd_encoded t).vertex_eq]
    exact coarse_left t _ (by omega) (by omega)
  · rw [show -((2*s+1 : ℕ) : ℤ) = 2 * (-(s : ℤ) - 1) + 1 by push_cast; ring]
    change east (cell 430 (2 * t + 1)) (-(s : ℤ) - 1) 0 = true
    rw [(odd_encoded t).east_eq]
    have hs : coarse t (-(s : ℤ)) 0 = true := coarse_left t _ (by omega) (by omega)
    simp [hs]

private theorem front_vertex (t : ℕ) : middleVertex (coarse t) (-(t : ℤ) - 1) 0 = true := by
  have hcentre : coarse t (-(t : ℤ) - 1) 0 = false := by
    apply coarse_outside
    rw [abs_zero, add_zero, abs_of_neg (by omega : -(t : ℤ) - 1 < 0)]
    omega
  have hnext : grow (coarse t) (-(t : ℤ) - 1) 0 = true := by
    simp [grow, left_boundary_count t (coarse_left t _ (by omega) (by omega))]
  have hleft : coarse t (-(t : ℤ) - 1 - 1) 0 = false := by
    apply coarse_outside
    rw [abs_zero, add_zero, abs_of_neg (by omega : -(t : ℤ) - 1 - 1 < 0)]
    omega
  rw [middle_off hcentre (Or.inr (Or.inl hleft))]
  exact hnext

private theorem even_left (t r : ℕ) (h : r ≤ 2 * t + 2) :
    cell 430 (2 * t + 2) (-(r : ℤ)) 0 = decide (r % 2 = 1 ∨ r = 2 * t + 2) := by
  obtain ⟨s, rfl | rfl⟩ := Nat.even_or_odd' r
  · rw [show -((2*s : ℕ) : ℤ) = 2 * (-(s : ℤ)) by push_cast; ring]
    change vertex (cell 430 (2 * t + 2)) (-(s : ℤ)) 0 = _
    rw [(even_intermediate t).vertex_eq]
    by_cases hs : s ≤ t
    · rw [middle_on (coarse_left t _ (by omega) (by omega))]
      symm
      exact decide_eq_false_iff_not.mpr (by omega)
    · have hlast : s = t + 1 := by omega
      subst s
      rw [show -((t + 1 : ℕ) : ℤ) = -(t : ℤ) - 1 by push_cast; ring, front_vertex]
      symm
      exact decide_eq_true_eq.mpr (by omega)
  · rw [show -((2*s+1 : ℕ) : ℤ) = 2 * (-(s : ℤ) - 1) + 1 by push_cast; ring]
    change east (cell 430 (2 * t + 2)) (-(s : ℤ) - 1) 0 = _
    rw [(even_intermediate t).east_eq]
    have hs : coarse t (-(s : ℤ)) 0 = true := coarse_left t _ (by omega) (by omega)
    rw [show (2*s+1) % 2 = 1 by omega]
    simp [hs]


/-- Reverse the summation index to count binary place values from the origin. -/
private theorem read_axis (n : ℕ) :
    a n = ∑ r ∈ Finset.range (n+1),
      if cell 430 n (-(r : ℤ)) 0 then (2 : ℤ)^r else 0 := by
  let digit (r : ℕ) : ℤ := if cell 430 n (-(r : ℤ)) 0 then (2 : ℤ)^r else 0
  change a n = ∑ r ∈ Finset.range (n+1), digit r
  rw [← Finset.sum_range_reflect digit (n+1)]
  unfold a
  apply Finset.sum_congr rfl
  intro r hr
  have h := Nat.le_of_lt_succ (Finset.mem_range.mp hr)
  have hcoord : -((n-r : ℕ) : ℤ) = (r : ℤ) - n := by rw [Nat.cast_sub h]; ring
  simp [digit, hcoord]

private theorem odd_places (m : ℕ) :
    (∑ r ∈ Finset.range (2*m), if r % 2 = 1 then (2 : ℤ)^r else 0) =
      2 * ∑ j ∈ Finset.range m, (4 : ℤ)^j := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2*(m+1) = 2*m+1+1 by omega, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ]
    simp [show (2*m+1)%2 = 1 by omega, pow_add, pow_mul]
    ring

private theorem even_axis_sum (t : ℕ) :
    a (2*t+2) = (2 : ℤ)^(2*t+2) + 2 * ∑ j ∈ Finset.range (t+1), (4 : ℤ)^j := by
  have hbelow :
      (∑ r ∈ Finset.range (2*t+2), if cell 430 (2*t+2) (-(r : ℤ)) 0 then (2 : ℤ)^r else 0) =
      ∑ r ∈ Finset.range (2*t+2), if r%2=1 then (2 : ℤ)^r else 0 := by
    apply Finset.sum_congr rfl
    intro r hr
    have hr' := Finset.mem_range.mp hr
    rw [even_left t r (by omega)]
    simp [show r ≠ 2*t+2 by omega]
  rw [read_axis, Finset.sum_range_succ, hbelow, even_left t _ le_rfl]
  simp only [or_true, decide_true, if_true]
  rw [show 2*t+2 = 2*(t+1) by omega, odd_places]
  ring

private theorem even_value (m : ℕ) :
    (a (2*m) : ℚ) = (5 * (4 : ℚ)^m - 2) / 3 := by
  cases m with
  | zero => norm_num [a, cell]
  | succ t =>
    have hgeom : (3 : ℚ) * (∑ j ∈ Finset.range (t+1), (4 : ℚ)^j) =
        (4 : ℚ)^(t+1) - 1 := by
      simpa [show (4 : ℚ) - 1 = 3 by norm_num, mul_comm] using (geom_sum_mul (4 : ℚ) (t+1))
    have hs := even_axis_sum t
    rw [show 2 * (t+1) = 2*t+2 by omega, hs]
    push_cast
    rw [show 2*t+2 = 2*(t+1) by omega, pow_mul]
    norm_num
    linarith only [hgeom]

private theorem odd_value (t : ℕ) : (a (2*t+1) : ℚ) = (4 : ℚ)^(t+1) - 1 := by
  have hl :
      a (2*t+1) = ∑ r ∈ Finset.range (2*t+2), (2 : ℤ)^r := by
    rw [read_axis]
    apply Finset.sum_congr rfl
    intro r hr
    rw [odd_left t r (by have := Finset.mem_range.mp hr; omega)]
    simp
  have hgeom : (∑ r ∈ Finset.range (2*t+2), (2 : ℤ)^r) = (2 : ℤ)^(2*t+2)-1 := by
    simpa using (geom_sum_mul (2 : ℤ) (2*t+2))
  rw [hl, hgeom]
  push_cast
  rw [show 2*t+2 = 2*(t+1) by omega, pow_mul]
  norm_num

private theorem closed_form (n : ℕ) :
    (a n : ℚ) = (-5 - (-2 : ℚ)^n + (-1 : ℚ)^n + 11*(2 : ℚ)^n) / 6 := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · norm_num [even_value, pow_mul]
    ring
  · norm_num [odd_value, pow_add, pow_mul]
    ring

private theorem recurrence (n : ℕ) (hn : 4 ≤ n) :
    (a n : ℚ) = 5 * a (n-2) - 4 * a (n-4) := by
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' (n-4)
  · rw [show n = 2*(k+2) by omega, show 2*(k+2)-2 = 2*(k+1) by omega,
        show 2*(k+2)-4 = 2*k by omega]
    simp only [even_value, pow_succ]
    ring
  · rw [show n = 2*(k+2)+1 by omega, show 2*(k+2)+1-2 = 2*(k+1)+1 by omega,
        show 2*(k+2)+1-4 = 2*k+1 by omega]
    simp only [odd_value, pow_succ]
    ring

open PowerSeries

private theorem generating :
    mk (fun n => (a n : ℚ)) * ((1-X)*(1+X)*(1-2*X)*(1+2*X)) =
      1 + 3*X + X^2 := by
  let S := mk (fun n => (a n : ℚ))
  change S * _ = _
  rw [show S * ((1-X)*(1+X)*(1-2*X)*(1+2*X)) =
        S - C (5:ℚ) * (S * X^2) + C (4:ℚ) * (S * X^4) by
        simp only [map_ofNat]
        ring]
  rw [show (1 + 3*X + X^2 : PowerSeries ℚ) =
        C (1:ℚ)*X^0 + C (3:ℚ)*X^1 + C (1:ℚ)*X^2 by
        simp only [map_one, map_ofNat, pow_zero, pow_one, one_mul, mul_one]]
  ext n
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', S, coeff_mk]
  by_cases hn : 4 ≤ n
  · simp (disch := omega) only [if_pos, if_neg, coeff_C, add_zero]
    linarith only [recurrence n hn]
  · have h₀ := even_value 0
    have h₁ := odd_value 0
    have h₂ := even_value 1
    have h₃ := odd_value 1
    norm_num at h₀ h₁ h₂ h₃
    interval_cases n <;> norm_num [h₀, h₁, h₂, h₃]

theorem OMA.solution : type_of% @OMA.S_oeis_a282123.main :=
  ⟨closed_form, recurrence, generating⟩

