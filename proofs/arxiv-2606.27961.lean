import OMAStatements.S_arxiv_2606_27961

/-!
# Transversal difference numbers in the square plane

For every odd prime p, the smallest difference set of a transversal of the
reduction from (ℤ/p²ℤ)² to (ℤ/pℤ)² has cardinality (2p−1)².

Proof by Mapika / Codex. Barcau, Paşol and Ţurcaş formulated the conjecture,
gave the standard box, settled p=3,5 and proved the cyclic difference estimate.
The collinear projection uses Robert Leshner’s argument. The box construction,
fiber count and compensation lemmas use ZedingZhang’s merged reduction R1.
The finite part rectifies any strict counterexample into an integral transversal.

The lattice argument applies the support-row deletion of González Merino and
Henze. The common-hull sum bound of Böröczky, Matolcsi, Ruzsa, Santos and Serra
is proved here by two polygonal chain sweeps. For a large centrally symmetric
boundary we count distinct sums of elementary segments, using the midpoint
parallelograms of Craizer, Teixeira and da Silva. The last theorem combines
the two parts and the sharp box upper bound in the upstream declaration.
-/

/-! Canonical carry labels for a section ZMod(p)² → ZMod(p²)². They are
based at the edge through the origin and so their image always contains zero. -/

namespace SquarePlaneLabels
abbrev V (p : ℕ) := ZMod p × ZMod p
abbrev G (p : ℕ) := V (p^2)

def red (p : ℕ) : ZMod (p^2) →+* ZMod p :=
  ZMod.castHom (show p ∣ p^2 by simp [pow_two]) (ZMod p)

def down (p : ℕ) : G p →+ V p := (red p).toAddMonoidHom.prodMap (red p).toAddMonoidHom

def timesPInt (p : ℕ) : ℤ →+ ZMod (p^2) where
  toFun z := (p : ZMod (p^2))*z
  map_zero' := by simp
  map_add' a b := by push_cast; ring

def timesP (p : ℕ) : ZMod p →+ ZMod (p^2) :=
  ZMod.lift p ⟨timesPInt p, by
    change (p : ZMod (p^2))*((p : ℤ) : ZMod (p^2)) = 0
    rw [Int.cast_natCast, ← Nat.cast_mul, ← pow_two, ZMod.natCast_self]⟩

theorem timesP_int (p : ℕ) (a : ℤ) : timesP p (a : ZMod p) = (p : ZMod (p^2))*a :=
  ZMod.lift_coe _ _ _

theorem timesP_red (p : ℕ) (a : ZMod (p^2)) : timesP p (red p a) = (p : ZMod (p^2))*a := by
  obtain ⟨z,rfl⟩ := ZMod.intCast_surjective a
  rw [map_intCast, timesP_int]

variable {p : ℕ} [NeZero p]

theorem timesP_inj : Function.Injective (timesP p) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  obtain ⟨z,rfl⟩ := ZMod.intCast_surjective x
  rw [timesP_int] at hx
  rw [← Int.cast_natCast p, ← Int.cast_mul, ZMod.intCast_zmod_eq_zero_iff_dvd] at hx
  rw [Nat.cast_pow, pow_two] at hx
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
    (Int.dvd_of_mul_dvd_mul_left (by exact_mod_cast NeZero.ne p) hx)

theorem ker_eq_range (a : ZMod (p^2)) (ha : red p a = 0) : ∃ x, timesP p x = a := by
  obtain ⟨z,rfl⟩ := ZMod.intCast_surjective a
  rw [map_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd] at ha
  obtain ⟨k,rfl⟩ := ha
  exact ⟨(k : ZMod p), by simp [timesP_int]⟩

def embed (p : ℕ) : V p →+ G p := (timesP p).prodMap (timesP p)

theorem embed_inj : Function.Injective (embed p) := fun _ _ h =>
  Prod.ext (timesP_inj (congrArg Prod.fst h)) (timesP_inj (congrArg Prod.snd h))

theorem embed_down (a : G p) : embed p (down p a) = p • a := by
  apply Prod.ext <;> simp [embed,down,timesP_red,nsmul_eq_mul]

theorem ker_embed (a : G p) (ha : down p a = 0) : ∃ x, embed p x = a := by
  obtain ⟨u,hu⟩ := ker_eq_range a.1 (congrArg Prod.fst ha)
  obtain ⟨v,hv⟩ := ker_eq_range a.2 (congrArg Prod.snd ha)
  exact ⟨(u,v),Prod.ext hu hv⟩

def edge (s : V p → G p) (u x : V p) := s (x+u) - s x

theorem down_edge (s : V p → G p) (hs : Function.RightInverse s (down p)) (u x : V p) :
    down p (edge s u x) = u := by rw [edge,map_sub,hs,hs,add_sub_cancel_left]

theorem label_exists (s : V p → G p) (hs : Function.RightInverse s (down p)) (u x : V p) :
    ∃ v, embed p v = edge s u x - edge s u 0 := by
  apply ker_embed
  rw [map_sub,down_edge s hs,down_edge s hs,sub_self]

noncomputable def label (s : V p → G p) (hs : Function.RightInverse s (down p)) (u x : V p) :
    V p := (label_exists s hs u x).choose

theorem label_spec (s : V p → G p) (hs : Function.RightInverse s (down p)) (u x : V p) :
    embed p (label s hs u x) = edge s u x - edge s u 0 := (label_exists s hs u x).choose_spec

theorem label_zero (s : V p → G p) (hs : Function.RightInverse s (down p)) (u : V p) :
    label s hs u 0 = 0 := by apply embed_inj; rw [label_spec, sub_self, map_zero]

theorem label_curl (s : V p → G p) (hs : Function.RightInverse s (down p)) (u v x : V p) :
    label s hs u (x+v) - label s hs u x = label s hs v (x+u) - label s hs v x := by
  apply embed_inj
  simp only [map_sub,label_spec,edge,add_right_comm x v u]
  abel

theorem cycle_edges (s : V p → G p) (u x : V p) (n : ℕ) :
    ∑ i ∈ Finset.range n, edge s u (x+i • u) = s (x+n • u) - s x := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ,ih,succ_nsmul,← add_assoc]; unfold edge; abel

theorem p_smul_zero (x : V p) : p • x = 0 := by ext <;> simp [nsmul_eq_mul]

theorem cycle_labels (s : V p → G p) (hs : Function.RightInverse s (down p)) (u x : V p) :
    ∑ i ∈ Finset.range p, label s hs u (x+i • u) = -u := by
  apply embed_inj
  rw [map_sum]
  simp only [label_spec, Finset.sum_sub_distrib, cycle_edges, p_smul_zero, add_zero, sub_self,
    Finset.sum_const, Finset.card_range, zero_sub, map_neg]
  rw [← embed_down, down_edge s hs]

end SquarePlaneLabels

namespace SquarePlaneLabels
open scoped Pointwise

/-- Matrix with columns U,V, on a pair of coordinates. -/
def columns {R : Type*} [CommRing R] (U V : R × R) : R × R →+ R × R where
  toFun x := (x.1*U.1 + x.2*V.1, x.1*U.2 + x.2*V.2)
  map_zero' := by simp
  map_add' a b := by ext <;> simp <;> ring

def determinant {R : Type*} [CommRing R] (u v : R × R) := u.1*v.2 - u.2*v.1

theorem columns_inj_of_det {K : Type*} [Field K] {u v : K × K} (h : determinant u v ≠ 0) :
    Function.Injective (columns u v) := by
  apply (injective_iff_map_eq_zero _).mpr
  rintro ⟨x,y⟩ hxy
  have hx : x*u.1+y*v.1 = 0 := congrArg Prod.fst hxy
  have hy : x*u.2+y*v.2 = 0 := congrArg Prod.snd hxy
  have h₁ : x*determinant u v = 0 := by unfold determinant; linear_combination v.2*hx-v.1*hy
  have h₂ : y*determinant u v = 0 := by unfold determinant; linear_combination u.1*hy-u.2*hx
  exact Prod.ext ((mul_eq_zero.mp h₁).resolve_right h) ((mul_eq_zero.mp h₂).resolve_right h)

variable {p : ℕ} [NeZero p]

def liftPoint (x : V p) : G p := (x.1.val, x.2.val)

theorem down_lift (x : V p) : down p (liftPoint x) = x := by
  apply Prod.ext <;> simp [down,liftPoint]

theorem down_columns (U W : G p) (x : G p) :
    down p (columns U W x) = columns (down p U) (down p W) (down p x) := by
  ext <;> simp [columns,down]

theorem columns_embed (U W : G p) (x : V p) :
    columns U W (embed p x) = embed p (columns (down p U) (down p W) x) := by
  nth_rw 1 [← down_lift x]
  rw [embed_down, map_nsmul, ← embed_down, down_columns, down_lift]

theorem columns_inj_lift {U W : G p} (h : Function.Injective (columns (down p U) (down p W))) :
    Function.Injective (columns U W) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  have hred := congrArg (down p) hx
  rw [down_columns, map_zero] at hred
  obtain ⟨v,rfl⟩ := ker_embed x (h (hred.trans (map_zero _).symm))
  rw [columns_embed, ← map_zero (embed p)] at hx
  rw [h ((embed_inj hx).trans (map_zero _).symm), map_zero]

noncomputable def basisChange (u v : V p) (h : Function.Injective (columns u v)) :
    G p ≃+ G p := by
  have hi : Function.Injective (columns (liftPoint u) (liftPoint v)) :=
    columns_inj_lift (by simpa only [down_lift] using h)
  exact AddEquiv.ofBijective _ ⟨hi,Finite.surjective_of_injective hi⟩

theorem basisChange_apply (u v : V p) (h : Function.Injective (columns u v)) (x : G p) :
    basisChange u v h x = columns (liftPoint u) (liftPoint v) x := rfl

theorem down_basis (u v : V p) (h : Function.Injective (columns u v)) (x : G p) :
    down p (basisChange u v h x) = columns u v (down p x) := by
  rw [basisChange_apply,down_columns,down_lift,down_lift]

theorem basis_embed (u v : V p) (h : Function.Injective (columns u v)) (x : V p) :
    basisChange u v h (embed p x) = embed p (columns u v x) := by
  rw [basisChange_apply,columns_embed,down_lift,down_lift]

noncomputable def rebase (s : V p → G p) (u v : V p) (h : Function.Injective (columns u v))
    (x : V p) := (basisChange u v h).symm (s (columns u v x))

theorem rebase_section (s : V p → G p) (hs : Function.RightInverse s (down p))
    (u v : V p) (h : Function.Injective (columns u v)) :
    Function.RightInverse (rebase s u v h) (down p) := by
  intro x
  apply h
  rw [← down_basis]
  change down p (basisChange u v h ((basisChange u v h).symm _)) = _
  rw [AddEquiv.apply_symm_apply, hs]

theorem rebase_edge (s : V p → G p) (u v : V p) (h : Function.Injective (columns u v))
    (w x : V p) : basisChange u v h (edge (rebase s u v h) w x) =
    edge s (columns u v w) (columns u v x) := by
  simp [edge,rebase]

theorem rebase_label (s : V p → G p) (hs : Function.RightInverse s (down p))
    (u v : V p) (h : Function.Injective (columns u v)) (w x : V p) :
    columns u v (label (rebase s u v h) (rebase_section s hs u v h) w x) =
      label s hs (columns u v w) (columns u v x) := by
  apply embed_inj
  rw [← basis_embed _ _ h, label_spec, map_sub, rebase_edge, rebase_edge, label_spec, map_zero]

theorem rebase_ncard (s : V p → G p) (u v : V p) (h : Function.Injective (columns u v)) :
    (Set.range (rebase s u v h) - Set.range (rebase s u v h)).ncard =
      (Set.range s - Set.range s).ncard := by
  classical
  have hr : Set.range (rebase s u v h) = (basisChange u v h).symm '' Set.range s := by
    ext z
    constructor
    · rintro ⟨x,rfl⟩
      exact ⟨_,Set.mem_range_self _,rfl⟩
    · rintro ⟨_,⟨x,rfl⟩,rfl⟩
      obtain ⟨t,rfl⟩ := (Finite.surjective_of_injective h) x
      exact ⟨t,rfl⟩
  rw [hr, ← Set.image_sub, (basisChange u v h).symm.injective.injOn.ncard_image]

end SquarePlaneLabels

/-! Coordinatewise reduction preserves the difference count of a lattice set
whose coordinate diameters are at most `⌊(q - 1) / 2⌋`. For the square-plane
rectification one takes `q = p ^ 2`. -/

namespace SquarePlaneRectification

open scoped Pointwise

/-- Reduce integer coordinates modulo `q`. -/
def reduceLattice (q : ℕ) : ℤ × ℤ →+ ZMod q × ZMod q where
  toFun x := ((x.1 : ZMod q), (x.2 : ZMod q))
  map_zero' := by simp
  map_add' x y := by ext <;> simp

/-- Pairwise coordinate bounds, with the half-width computed in the integers. -/
def HalfWidth (q : ℕ) (S : Set (ℤ × ℤ)) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S,
    |a.1 - b.1| ≤ ((q : ℤ) - 1) / 2 ∧ |a.2 - b.2| ≤ ((q : ℤ) - 1) / 2

private theorem eq_of_cast_eq_of_halfWidth (q : ℕ) (x y : ℤ)
    (hx : |x| ≤ ((q : ℤ) - 1) / 2) (hy : |y| ≤ ((q : ℤ) - 1) / 2)
    (he : (x : ZMod q) = (y : ZMod q)) : x = y := by
  obtain ⟨hxlo, hxhi⟩ := abs_le.mp hx
  obtain ⟨hylo, hyhi⟩ := abs_le.mp hy
  have hdiv : (q : ℤ) ∣ y - x := (ZMod.intCast_eq_intCast_iff_dvd_sub x y q).mp he
  have hlt : |y - x| < (q : ℤ) := abs_lt.mpr (by constructor <;> omega)
  have hz := Int.eq_zero_of_abs_lt_dvd hdiv hlt
  omega

/-- No two lattice differences agree after coordinatewise reduction. -/
theorem injOn_difference (q : ℕ) (S : Set (ℤ × ℤ)) (hS : HalfWidth q S) :
    Set.InjOn (reduceLattice q) (S - S) := by
  intro x hx y hy hxy
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_sub.mp hx
  obtain ⟨c, hc, d, hd, rfl⟩ := Set.mem_sub.mp hy
  obtain ⟨hab₁, hab₂⟩ := hS a ha b hb
  obtain ⟨hcd₁, hcd₂⟩ := hS c hc d hd
  apply Prod.ext
  · exact eq_of_cast_eq_of_halfWidth q _ _ hab₁ hcd₁ (congrArg Prod.fst hxy)
  · exact eq_of_cast_eq_of_halfWidth q _ _ hab₂ hcd₂ (congrArg Prod.snd hxy)

/-- The integer difference set and its image have the same cardinality. -/
theorem ncard_image_difference (q : ℕ) (S : Set (ℤ × ℤ)) (hS : HalfWidth q S) :
    ((reduceLattice q) '' (S - S)).ncard = (S - S).ncard :=
  (injOn_difference q S hS).ncard_image

/-- Equivalently, taking differences after reduction gives the same count. -/
theorem ncard_difference_of_reduction (q : ℕ) (S : Set (ℤ × ℤ)) (hS : HalfWidth q S) :
    ((reduceLattice q) '' S - (reduceLattice q) '' S).ncard = (S - S).ncard := by
  rw [← Set.image_sub]
  exact ncard_image_difference q S hS


end SquarePlaneRectification

/-! Integration of a closed discrete one-form on a natural-number grid,
and constancy of its period displacements. All results apply coordinatewise
or to the entire pair of integer labels. -/

namespace SquarePlaneRectification

variable {A : Type*} [AddCommGroup A]

def gridPotential (X Y : ℕ → ℕ → A) (i j : ℕ) : A :=
  (∑ t ∈ Finset.range i, X t 0) + ∑ t ∈ Finset.range j, Y i t

theorem gridPotential_zero (X Y : ℕ → ℕ → A) : gridPotential X Y 0 0 = 0 := by
  simp [gridPotential]

theorem gridPotential_y (X Y : ℕ → ℕ → A) (i j : ℕ) :
    gridPotential X Y i (j+1) = gridPotential X Y i j + Y i j := by
  simp [gridPotential, Finset.sum_range_succ, add_assoc]

theorem gridPotential_x (X Y : ℕ → ℕ → A)
    (closed : ∀ i j, X i j + Y (i+1) j = Y i j + X i (j+1)) (i j : ℕ) :
    gridPotential X Y (i+1) j = gridPotential X Y i j + X i j := by
  induction j with
  | zero => simp [gridPotential, Finset.sum_range_succ]
  | succ j ih =>
    rw [gridPotential_y, gridPotential_y, ih, add_assoc, closed, ← add_assoc]

theorem grid_eq_of_edges {F G : ℕ → ℕ → A} (base : F 0 0 = G 0 0)
    (dx : ∀ i j, F (i+1) j - F i j = G (i+1) j - G i j)
    (dy : ∀ i j, F i (j+1) - F i j = G i (j+1) - G i j) (i j : ℕ) :
    F i j = G i j := by
  have bottom (k : ℕ) : F k 0 = G k 0 := by
    induction k with
    | zero => exact base
    | succ k ih => exact sub_left_inj.mp (ih ▸ dx k 0)
  induction j with
  | zero => exact bottom i
  | succ j ih => exact sub_left_inj.mp (ih ▸ dy i j)

theorem grid_period {F X Y : ℕ → ℕ → A}
    (dx : ∀ i j, F (i+1) j = F i j + X i j)
    (dy : ∀ i j, F i (j+1) = F i j + Y i j)
    (a b : ℕ) (px : ∀ i j, X (i+a) (j+b) = X i j)
    (py : ∀ i j, Y (i+a) (j+b) = Y i j) (i j : ℕ) :
    F (i+a) (j+b) - F i j = F a b - F 0 0 := by
  have eq := grid_eq_of_edges (F := fun i j => F (i+a) (j+b))
    (G := fun i j => F i j + (F a b - F 0 0))
    (by simp) (fun i j => by
      rw [show i+1+a = i+a+1 by omega, dx, dx i j, px]; abel)
    (fun i j => by
      rw [show j+1+b = j+b+1 by omega, dy, dy i j, py]; abel) i j
  change F (i+a) (j+b) = F i j + (F a b - F 0 0) at eq
  rw [eq]
  abel

theorem gridPotential_period (X Y : ℕ → ℕ → A)
    (closed : ∀ i j, X i j + Y (i+1) j = Y i j + X i (j+1))
    (a b : ℕ) (px : ∀ i j, X (i+a) (j+b) = X i j)
    (py : ∀ i j, Y (i+a) (j+b) = Y i j) (i j : ℕ) :
    gridPotential X Y (i+a) (j+b) - gridPotential X Y i j = gridPotential X Y a b := by
  simpa only [gridPotential_zero, sub_zero] using
    grid_period (gridPotential_x X Y closed) (gridPotential_y X Y) a b px py i j


end SquarePlaneRectification

/-! Oscillation of the centered lattice potential in the all-prime rectification.
The period and both indices of the potential are natural numbers. Each increment
of the uncentered coordinate is an integer between zero and one. -/

namespace SquarePlaneRectification

theorem walk_bounds (f : ℕ → ℤ) (step : ∀ n, 0 ≤ f (n+1) - f n ∧ f (n+1) - f n ≤ 1)
    (a k : ℕ) : 0 ≤ f (a+k) - f a ∧ f (a+k) - f a ≤ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hs := step (a+k)
    push_cast
    change 0 ≤ f (a+k+1) - f a ∧ f (a+k+1) - f a ≤ (k : ℤ) + 1
    omega

/-- The centered displacement of any arc of the cycle has absolute value at
most the product of the number of ones and the number of zeros. -/
theorem cyclic_displacement (p : ℕ) (h : ℤ) (f : ℕ → ℤ)
    (step : ∀ n, 0 ≤ f (n+1) - f n ∧ f (n+1) - f n ≤ 1)
    (period : ∀ n, f (n+p) - f n = h) (a k : ℕ) (hk : k ≤ p) :
    |(p : ℤ) * (f (a+k) - f a) - k*h| ≤ h*(p-h) := by
  let d := f (a+k) - f a
  have h₁ := walk_bounds f step a k
  have h₂ := walk_bounds f step (a+k) (p-k)
  rw [show a+k+(p-k) = a+p by omega] at h₂
  have ht := period a
  have hk' : ((p-k : ℕ) : ℤ) = (p : ℤ) - k := Int.ofNat_sub hk
  rw [hk'] at h₂
  have hd : 0 ≤ d := h₁.1
  have hdk : d ≤ k := h₁.2
  have hdh : d ≤ h := by dsimp [d]; omega
  have hz : (k : ℤ) - d ≤ (p : ℤ) - h := by dsimp [d]; omega
  have hh : 0 ≤ h := le_trans hd hdh
  have hz' : 0 ≤ (p : ℤ) - h := by omega
  change |(p : ℤ) * d - k*h| ≤ h*(p-h)
  apply abs_le.mpr
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hz hh, mul_nonneg hd hz']
  · nlinarith [mul_le_mul_of_nonneg_right hdh hz',
      mul_nonneg (sub_nonneg.mpr hdk) hh]

theorem cyclic_quarter_bound (p : ℕ) (ho : Odd p) (h : ℤ) :
    4 * (h * ((p : ℤ)-h)) ≤ (p : ℤ)^2 - 1 := by
  obtain ⟨r, hr⟩ := ho
  have hodd : (p : ℤ) = 2*(r : ℤ)+1 := by exact_mod_cast hr
  rcases le_or_gt (h : ℤ) r with hl | hl
  · have hx : 0 ≤ (p : ℤ)-2*h-1 := by omega
    nlinarith [mul_nonneg hx (show 0 ≤ (p : ℤ)-2*h+1 by omega)]
  · have hx : 0 ≤ 2*h-(p : ℤ)-1 := by omega
    nlinarith [mul_nonneg hx (show 0 ≤ 2*h-(p : ℤ)+1 by omega)]

def centered (p : ℕ) (hx hy : ℤ) (F : ℕ → ℕ → ℤ) (i j : ℕ) : ℤ :=
  (p : ℤ)*F i j - i*hx - j*hy

theorem centered_line (p : ℕ) (h : ℤ) (f : ℕ → ℤ)
    (step : ∀ n, 0 ≤ f (n+1) - f n ∧ f (n+1) - f n ≤ 1)
    (period : ∀ n, f (n+p) - f n = h) (i j : ℕ) (hi : i ≤ p) (hj : j ≤ p) :
    |((p : ℤ)*f i - i*h) - ((p : ℤ)*f j - j*h)| ≤ h*(p-h) := by
  wlog hij : j ≤ i generalizing i j
  · rw [abs_sub_comm]
    exact this j i hj hi (by omega)
  have ha := cyclic_displacement p h f step period j (i-j) (by omega)
  rw [show j+(i-j)=i by omega, Int.ofNat_sub hij] at ha
  convert ha using 2; ring

/-- Every coordinate of the image on a fundamental square meets the half-width
bound required by the no-wrap theorem at modulus p². -/
theorem centered_half_width (p : ℕ) (ho : Odd p) (hx hy : ℤ) (F : ℕ → ℕ → ℤ)
    (sx : ∀ i j, 0 ≤ F (i+1) j - F i j ∧ F (i+1) j - F i j ≤ 1)
    (sy : ∀ i j, 0 ≤ F i (j+1) - F i j ∧ F i (j+1) - F i j ≤ 1)
    (px : ∀ i j, F (i+p) j - F i j = hx)
    (py : ∀ i j, F i (j+p) - F i j = hy)
    (a b c d : Fin p) :
    |centered p hx hy F a b - centered p hx hy F c d| ≤ ((p : ℤ)^2 - 1) / 2 := by
  have X := centered_line p hx (fun i => F i b) (fun i => sx i b)
    (fun i => px i b) a c a.isLt.le c.isLt.le
  have Y := centered_line p hy (F c) (sy c) (py c) b d b.isLt.le d.isLt.le
  have hx' := cyclic_quarter_bound p ho hx
  have hy' := cyclic_quarter_bound p ho hy
  have htri := abs_add_le ((p : ℤ)*F a b - a.val*hx - ((p : ℤ)*F c b - c.val*hx))
    ((p : ℤ)*F c b - b.val*hy - ((p : ℤ)*F c d - d.val*hy))
  have he : centered p hx hy F a b - centered p hx hy F c d =
      ((p : ℤ)*F a b - a.val*hx - ((p : ℤ)*F c b - c.val*hx)) +
      ((p : ℤ)*F c b - b.val*hy - ((p : ℤ)*F c d - d.val*hy)) := by unfold centered; ring
  rw [he]
  omega


end SquarePlaneRectification

namespace SquarePlaneRectification

theorem cancel_mod_sq {p : ℕ} (hp : 0 < p) {u : ℤ}
    (he : (p : ZMod (p^2)) * (u : ZMod (p^2)) = 0) : (p : ℤ) ∣ u := by
  have hd : (↑(p^2) : ℤ) ∣ (p : ℤ)*u := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    push_cast
    exact he
  rw [Nat.cast_pow, pow_two] at hd
  exact Int.dvd_of_mul_dvd_mul_left (by exact_mod_cast hp.ne') hd

/-- One output coordinate of the section in normalized independent axes. -/
structure NormalCoord (p : ℕ) where
  s : ℕ → ℕ → ZMod (p^2)
  X : ℕ → ℕ → ℤ
  Y : ℕ → ℕ → ℤ
  a : ℤ
  b : ℤ
  X01 : ∀ i j, 0 ≤ X i j ∧ X i j ≤ 1
  Y01 : ∀ i j, 0 ≤ Y i j ∧ Y i j ≤ 1
  sx : ∀ i j, s (i+1) j = s i j + a + (p : ZMod (p^2))*X i j
  sy : ∀ i j, s i (j+1) = s i j + b + (p : ZMod (p^2))*Y i j
  sperx : ∀ i j, s (i+p) j = s i j
  spery : ∀ i j, s i (j+p) = s i j

namespace NormalCoord
variable {p : ℕ}

theorem small_eq (hp : 2 < p) {u v : ℤ} (hlo : -2 ≤ u-v) (hhi : u-v ≤ 2)
    (he : (p : ZMod (p^2)) * ((u-v : ℤ) : ZMod (p^2)) = 0) : u = v := by
  have hd := cancel_mod_sq (by omega : 0 < p) he
  have hh : |u-v| < (p : ℤ) := abs_lt.mpr (by constructor <;> omega)
  have := Int.eq_zero_of_abs_lt_dvd hd hh
  omega

theorem closed (C : NormalCoord p) (hp : 2 < p) (i j : ℕ) :
    C.X i j + C.Y (i+1) j = C.Y i j + C.X i (j+1) := by
  have h := C.sy (i+1) j
  rw [C.sx i j, C.sx i (j+1), C.sy i j] at h
  have h₁ := C.X01 i j
  have h₂ := C.Y01 (i+1) j
  have h₃ := C.Y01 i j
  have h₄ := C.X01 i (j+1)
  apply small_eq hp (by omega) (by omega)
  push_cast
  linear_combination -h

theorem labels_unique (hp : 2 < p) {a b : ℤ} (ha : 0 ≤ a ∧ a ≤ 1)
    (hb : 0 ≤ b ∧ b ≤ 1) (he : (p : ZMod (p^2))*a = (p : ZMod (p^2))*b) : a = b := by
  apply small_eq hp (by omega) (by omega)
  push_cast
  linear_combination he

theorem periodic_labels (C : NormalCoord p) (hp : 2 < p) (u v : ℕ)
    (hs : ∀ i j, C.s (i+u) (j+v) = C.s i j) (i j : ℕ) :
    C.X (i+u) (j+v) = C.X i j ∧ C.Y (i+u) (j+v) = C.Y i j := by
  constructor
  · have h := C.sx (i+u) (j+v)
    rw [show i+u+1=i+1+u by omega, hs, hs, C.sx] at h
    exact labels_unique hp (C.X01 _ _) (C.X01 _ _) (add_left_cancel h.symm)
  · have h := C.sy (i+u) (j+v)
    rw [show j+v+1=j+1+v by omega, hs, hs, C.sy] at h
    exact labels_unique hp (C.Y01 _ _) (C.Y01 _ _) (add_left_cancel h.symm)

def F (C : NormalCoord p) := gridPotential C.X C.Y
def hx (C : NormalCoord p) := C.F p 0
def hy (C : NormalCoord p) := C.F 0 p
def R (C : NormalCoord p) := centered p C.hx C.hy C.F

theorem Fpx (C : NormalCoord p) (hp : 2 < p) (i j : ℕ) : C.F (i+p) j - C.F i j = C.hx := by
  have h := C.periodic_labels hp p 0 (by simpa using C.sperx)
  exact gridPotential_period C.X C.Y (C.closed hp) p 0 (fun i j => (h i j).1)
    (fun i j => (h i j).2) i j

theorem Fpy (C : NormalCoord p) (hp : 2 < p) (i j : ℕ) : C.F i (j+p) - C.F i j = C.hy := by
  have h := C.periodic_labels hp 0 p (by simpa using C.spery)
  exact gridPotential_period C.X C.Y (C.closed hp) 0 p (fun i j => (h i j).1)
    (fun i j => (h i j).2) i j

theorem width (C : NormalCoord p) (hp : 2 < p) (ho : Odd p) (a b c d : Fin p) :
    |C.R a b - C.R c d| ≤ ((p : ℤ)^2-1)/2 := by
  apply centered_half_width p ho C.hx C.hy C.F _ _ (C.Fpx hp) (C.Fpy hp)
  · intro i j
    simpa only [F, gridPotential_x C.X C.Y (C.closed hp), add_sub_cancel_left] using C.X01 i j
  · intro i j
    simpa only [F, gridPotential_y, add_sub_cancel_left] using C.Y01 i j

end NormalCoord
end SquarePlaneRectification

namespace SquarePlaneRectification.NormalCoord
variable {p : ℕ}

theorem integrate_section (C : NormalCoord p) (hp : 2 < p) (i j : ℕ) :
    C.s i j = C.s 0 0 + i*C.a + j*C.b + (p : ZMod (p^2))*C.F i j := by
  apply grid_eq_of_edges (F := C.s)
    (G := fun i j => C.s 0 0 + i*C.a + j*C.b + (p : ZMod (p^2))*C.F i j)
  · simp [F, gridPotential_zero]
  · intro i j
    rw [C.sx]
    simp only [F, gridPotential_x C.X C.Y (C.closed hp), Nat.cast_add, Nat.cast_one,
      Int.cast_add]
    ring
  · intro i j
    rw [C.sy]
    simp only [F, gridPotential_y, Nat.cast_add, Nat.cast_one, Int.cast_add]
    ring

theorem period_congruences (C : NormalCoord p) (hp : 2 < p) :
    (p : ℤ) ∣ C.a + C.hx ∧ (p : ℤ) ∣ C.b + C.hy := by
  constructor
  · have he := C.integrate_section hp p 0
    rw [show C.s p 0 = C.s 0 0 by simpa using C.sperx 0 0] at he
    apply cancel_mod_sq (by omega : 0 < p)
    simp only [hx, Int.cast_add]
    simp at he
    linear_combination -he
  · have he := C.integrate_section hp 0 p
    rw [show C.s 0 p = C.s 0 0 by simpa using C.spery 0 0] at he
    apply cancel_mod_sq (by omega : 0 < p)
    simp only [hy, Int.cast_add]
    simp at he
    linear_combination -he

/-- The uncentered and centered lifts differ, modulo p², by an affine expression
whose linear coefficients are divisible by p. -/
theorem section_centered (C : NormalCoord p) (hp : 2 < p) (i j : ℕ) :
    C.s i j = C.s 0 0 + (C.R i j : ZMod (p^2)) +
      i * ((C.a+C.hx : ℤ) : ZMod (p^2)) + j * ((C.b+C.hy : ℤ) : ZMod (p^2)) := by
  rw [C.integrate_section hp i j]
  unfold R centered
  push_cast
  ring

theorem cast_window_correction {m n : ℤ} (hm : (p : ℤ) ∣ m) (hn : (p : ℤ) ∣ n) :
    (m : ZMod (p^2)) * (n : ZMod (p^2)) = 0 := by
  rw [← Int.cast_mul]
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
  simpa only [Nat.cast_pow, pow_two, Nat.cast_mul] using mul_dvd_mul hm hn

theorem diff_modsq_iff (C : NormalCoord p) (hp : 2 < p) (i j k l u v w z : ℕ)
    (h₁ : (p : ℤ) ∣ ((i : ℤ)-k) - (u-w))
    (h₂ : (p : ℤ) ∣ ((j : ℤ)-l) - (v-z)) :
    C.s i j - C.s k l = C.s u v - C.s w z ↔
    ((C.R i j - C.R k l : ℤ) : ZMod (p^2)) = ((C.R u v - C.R w z : ℤ) : ZMod (p^2)) := by
  have hper := C.period_congruences hp
  have e₁ := cast_window_correction h₁ hper.1
  have e₂ := cast_window_correction h₂ hper.2
  push_cast at e₁ e₂ ⊢
  simp only [C.section_centered hp i j, C.section_centered hp k l,
    C.section_centered hp u v, C.section_centered hp w z, Int.cast_add]
  constructor <;> intro h
  · linear_combination h - e₁ - e₂
  · linear_combination h + e₁ + e₂

end SquarePlaneRectification.NormalCoord

namespace SquarePlaneRectification
open scoped Pointwise

def coordReduce (p : ℕ) : ZMod (p^2) →+* ZMod p :=
  ZMod.castHom (show p ∣ p^2 by simp [pow_two]) (ZMod p)

variable {p : ℕ} [NeZero p]

def linearCoord (C : NormalCoord p) (t : ZMod p × ZMod p) : ZMod p :=
  t.1*C.a + t.2*C.b

def axes (C D : NormalCoord p) (t : ZMod p × ZMod p) : ZMod p × ZMod p :=
  (linearCoord C t, linearCoord D t)

def lifted (C D : NormalCoord p) (t : ZMod p × ZMod p) : ℤ × ℤ :=
  (C.R t.1.val t.2.val, D.R t.1.val t.2.val)

def original (C D : NormalCoord p) (t : ZMod p × ZMod p) : ZMod (p^2) × ZMod (p^2) :=
  (C.s t.1.val t.2.val, D.s t.1.val t.2.val)

theorem axes_sub (C D : NormalCoord p) (t u : ZMod p × ZMod p) :
    axes C D (t-u) = axes C D t - axes C D u := by
  ext <;> simp [axes, linearCoord] <;> ring

theorem cast_R (C : NormalCoord p) (hp : 2 < p) (t : ZMod p × ZMod p) :
    (C.R t.1.val t.2.val : ZMod p) = linearCoord C t := by
  have h := C.period_congruences hp
  have ha := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h.1
  have hb := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h.2
  push_cast at ha hb
  simp [NormalCoord.R, centered, linearCoord]
  linear_combination -t.1*ha - t.2*hb

theorem reduce_lifted (C D : NormalCoord p) (hp : 2 < p) (t : ZMod p × ZMod p) :
    reduceLattice p (lifted C D t) = axes C D t :=
  Prod.ext (cast_R C hp t) (cast_R D hp t)

theorem reduce_original_coord (C : NormalCoord p) (hp : 2 < p) (t : ZMod p × ZMod p) :
    coordReduce p (C.s t.1.val t.2.val) = coordReduce p (C.s 0 0) + linearCoord C t := by
  rw [C.integrate_section hp]
  simp [linearCoord, add_assoc]

theorem original_residue_diff (C D : NormalCoord p) (hp : 2 < p) (t u : ZMod p × ZMod p) :
    Prod.map (coordReduce p) (coordReduce p) (original C D t - original C D u) =
      axes C D (t-u) := by
  rw [axes_sub]
  apply Prod.ext <;> simp [original, axes, reduce_original_coord _ hp]

theorem lifted_halfWidth (C D : NormalCoord p) (hp : 2 < p) (ho : Odd p) :
    HalfWidth (p^2) (Set.range (lifted C D)) := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  let ix (x : ZMod p) : Fin p := ⟨x.val, x.val_lt⟩
  simpa only [lifted, Nat.cast_pow] using
    And.intro (C.width hp ho (ix a.1) (ix a.2) (ix b.1) (ix b.2))
      (D.width hp ho (ix a.1) (ix a.2) (ix b.1) (ix b.2))

theorem index_dvd {a b c d : ZMod p} (h : a-b = c-d) :
    (p : ℤ) ∣ ((a.val : ℤ)-b.val) - (c.val-d.val) := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  simp [h]

theorem congruent_displacement (C D : NormalCoord p) (hp : 2 < p) (t u v w : ZMod p × ZMod p)
    (h : t-u = v-w) :
    original C D t - original C D u = original C D v - original C D w ↔
    reduceLattice (p^2) (lifted C D t - lifted C D u) =
      reduceLattice (p^2) (lifted C D v - lifted C D w) := by
  have hx := index_dvd (congrArg Prod.fst h)
  have hy := index_dvd (congrArg Prod.snd h)
  have f (E : NormalCoord p) := E.diff_modsq_iff hp _ _ _ _ _ _ _ _ hx hy
  change (_, _) = (_, _) ↔ (_, _) = (_, _)
  rw [Prod.mk.injEq, Prod.mk.injEq]
  exact and_congr (f C) (f D)

end SquarePlaneRectification

namespace SquarePlaneRectification
open scoped Pointwise

theorem ncard_range_of_same_fibers {I A B : Type*} (f : I → A) (g : I → B)
    (fibers : ∀ x y, f x = f y ↔ g x = g y) :
    (Set.range f).ncard = (Set.range g).ncard := by
  classical
  let pick (a : A) (ha : a ∈ Set.range f) : I := Classical.choose ha
  have pick_spec (a : A) (ha : a ∈ Set.range f) : f (pick a ha) = a :=
    Classical.choose_spec ha
  apply Set.ncard_congr (fun a ha => g (pick a ha))
  · exact fun a ha => Set.mem_range_self _
  · intro a b ha hb h
    simpa only [pick_spec] using (fibers _ _).mpr h
  · rintro _ ⟨i, rfl⟩
    exact ⟨f i, Set.mem_range_self _, (fibers _ _).mp (pick_spec _ _)⟩

theorem range_diff {I A : Type*} [SubtractionMonoid A] (f : I → A) :
    Set.range f - Set.range f = Set.range (fun x : I × I => f x.1 - f x.2) := by
  ext z
  constructor
  · rintro ⟨_, ⟨x,rfl⟩, _, ⟨y,rfl⟩, rfl⟩
    exact ⟨(x,y),rfl⟩
  · rintro ⟨⟨x,y⟩,rfl⟩
    exact ⟨_, ⟨x,rfl⟩, _, ⟨y,rfl⟩, rfl⟩

variable {p : ℕ} [NeZero p]

theorem lift_diff_iff (C D : NormalCoord p) (hp : 2 < p) (ho : Odd p)
    (indep : Function.Injective (axes C D)) (t u v w : ZMod p × ZMod p) :
    original C D t - original C D u = original C D v - original C D w ↔
      lifted C D t - lifted C D u = lifted C D v - lifted C D w := by
  constructor
  · intro h
    have hd := congrArg (Prod.map (coordReduce p) (coordReduce p)) h
    rw [original_residue_diff C D hp, original_residue_diff C D hp] at hd
    have hm := (congruent_displacement C D hp t u v w (indep hd)).mp h
    apply injOn_difference (p^2) _ (lifted_halfWidth C D hp ho) _ _ hm <;>
      exact Set.sub_mem_sub (Set.mem_range_self _) (Set.mem_range_self _)
  · intro h
    have hd := congrArg (reduceLattice p) h
    simp only [map_sub, reduce_lifted C D hp, ← axes_sub] at hd
    exact (congruent_displacement C D hp t u v w (indep hd)).mpr
      (congrArg (reduceLattice (p^2)) h)

/-- For two normalized output coordinates with independent residue axes, the
explicit integer lift is a transversal with exactly the original number of
differences. This is the last implication in finite-to-lattice rectification. -/
theorem normalized_lift (C D : NormalCoord p) (hp : 2 < p) (ho : Odd p)
    (indep : Function.Injective (axes C D)) :
    Set.BijOn (reduceLattice p) (Set.range (lifted C D)) Set.univ ∧
    (Set.range (original C D) - Set.range (original C D)).ncard =
      (Set.range (lifted C D) - Set.range (lifted C D)).ncard := by
  constructor
  · refine ⟨fun _ _ => Set.mem_univ _, ?_, ?_⟩
    · rintro _ ⟨t,rfl⟩ _ ⟨u,rfl⟩ h
      rw [reduce_lifted C D hp, reduce_lifted C D hp] at h
      rw [indep h]
    · intro y _
      obtain ⟨t,rfl⟩ := (Finite.surjective_of_injective indep) y
      exact ⟨_, Set.mem_range_self t, reduce_lifted C D hp t⟩
  · rw [range_diff, range_diff]
    apply ncard_range_of_same_fibers
    exact fun x y => lift_diff_iff C D hp ho indep x.1 x.2 y.1 y.2

end SquarePlaneRectification

/-! Moving compatible triangular label images to normalized coordinates. -/

namespace SquarePlaneLabels
open SquarePlaneRectification
open scoped Pointwise
variable {p : ℕ} [Fact p.Prime]

def bit {q : ℕ} (z : ZMod q) : ℤ := if z = 0 then 0 else 1

theorem bit_bounds {q : ℕ} (z : ZMod q) : 0 ≤ bit z ∧ bit z ≤ 1 := by
  unfold bit; split <;> omega

theorem bit_step (r t a : ZMod (p^2)) (h : t-r = a ∨ t-r = a+(p : ZMod (p^2))) :
    t = r+a+(p : ZMod (p^2))*(bit (t-r-a) : ZMod (p^2)) := by
  by_cases e : t-r-a = 0
  · simp [bit,e]; linear_combination e
  · simp [bit,e]
    rcases h with h|h
    · exact (e (by linear_combination h)).elim
    · linear_combination h

def makeCoord (r : V p → ZMod (p^2)) (a b : ZMod (p^2))
    (sx : ∀ i j : ZMod p, r (i+1,j)-r (i,j) = a ∨ r (i+1,j)-r (i,j) = a+(p : ZMod (p^2)))
    (sy : ∀ i j : ZMod p, r (i,j+1)-r (i,j) = b ∨ r (i,j+1)-r (i,j) = b+(p : ZMod (p^2))) :
    NormalCoord p where
  s i j := r (i,j)
  X i j := bit (r ((i : ZMod p)+1,j)-r (i,j)-a)
  Y i j := bit (r (i,(j : ZMod p)+1)-r (i,j)-b)
  a := a.val
  b := b.val
  X01 _ _ := bit_bounds _
  Y01 _ _ := bit_bounds _
  sx i j := by simpa using bit_step (r (i,j)) _ a (sx i j)
  sy i j := by simpa using bit_step (r (i,j)) _ b (sy i j)
  sperx i j := by simp
  spery i j := by simp

def Rectified (s : V p → G p) : Prop :=
  ∃ S : Set (ℤ × ℤ), S.Finite ∧ Set.BijOn (reduceLattice p) S Set.univ ∧
    (Set.range s - Set.range s).ncard = (S-S).ncard

/-- The finite alphabet of each coordinate of one edge has at most two values. -/
def binaryStep (r : V p → G p) (e : V p) (a : G p) : Prop :=
  ∀ x, let z := edge r e x
       (z.1 = a.1 ∨ z.1 = a.1+p) ∧ (z.2 = a.2 ∨ z.2 = a.2+p)

theorem rectified_binary (r : V p → G p) (hp : 2 < p) (ho : Odd p) (A B : G p)
    (sx : binaryStep r (1,0) A) (sy : binaryStep r (0,1) B)
    (hi : Function.Injective (columns (down p A) (down p B))) : Rectified r := by
  have sx' (i j : ZMod p) := sx (i,j)
  have sy' (i j : ZMod p) := sy (i,j)
  simp [edge] at sx' sy'
  let C := makeCoord (fun t => (r t).1) A.1 B.1 (fun i j => (sx' i j).1) (fun i j => (sy' i j).1)
  let D := makeCoord (fun t => (r t).2) A.2 B.2 (fun i j => (sx' i j).2) (fun i j => (sy' i j).2)
  have haxes : axes C D = columns (down p A) (down p B) := by
    funext t
    apply Prod.ext <;> simp [axes,linearCoord,C,D,makeCoord,columns,down,red,ZMod.castHom_apply]
  have horig : original C D = r := by
    funext t
    simp [original,C,D,makeCoord]
  obtain ⟨bij,eq⟩ := normalized_lift C D hp ho (haxes ▸ hi)
  exact ⟨_,Set.finite_range _,bij,horig ▸ eq⟩

end SquarePlaneLabels

namespace SquarePlaneLabels
open SquarePlaneRectification
open scoped Pointwise
variable {p : ℕ} [Fact p.Prime]

def triangle (t P Q : V p) : Set (V p) := {t,t+P,t+Q}

theorem down_embed_zero (z : V p) : down p (embed p z) = 0 := by
  rw [← down_lift z,embed_down,map_nsmul,p_smul_zero]

/-- For two independent input axes whose label triangles are translates, the
point set in the original finite plane rectifies. The two input axes and the two
label columns may be different bases. -/
theorem rectified_of_aligned (s : V p → G p) (hs : Function.RightInverse s (down p))
    (hp : 2 < p) (ho : Odd p) (u v P Q t z : V p)
    (huv : determinant u v ≠ 0) (hPQ : determinant P Q ≠ 0)
    (hu : ∀ x, label s hs u x ∈ triangle t P Q)
    (hv : ∀ x, label s hs v x ∈ triangle z P Q) : Rectified s := by
  let M := columns u v
  have hM := columns_inj_of_det huv
  let B := basisChange P Q (columns_inj_of_det hPQ)
  let r (x : V p) := B.symm (s (M x))
  let shift (w a : V p) := B.symm (edge s w 0 + embed p a)
  have bone : timesP p 1 = (p : ZMod (p^2)) := by simpa using timesP_int p 1
  have eP : B.symm (embed p P) = ((p : ZMod (p^2)), 0) := by
    apply B.injective
    rw [B.apply_symm_apply]
    have h := basis_embed P Q (columns_inj_of_det hPQ) (1,0)
    change B _ = _ at h
    have h₁ : embed p (1,0) = ((p : ZMod (p^2)),0) := by
      exact Prod.ext bone (map_zero (timesP p))
    simpa only [h₁,columns,AddMonoidHom.coe_mk,ZeroHom.coe_mk,one_mul,zero_mul,add_zero,
      Prod.mk.eta] using h.symm
  have eQ : B.symm (embed p Q) = (0, (p : ZMod (p^2))) := by
    apply B.injective
    rw [B.apply_symm_apply]
    have h := basis_embed P Q (columns_inj_of_det hPQ) (0,1)
    change B _ = _ at h
    have h₁ : embed p (0,1) = (0,(p : ZMod (p^2))) := by
      exact Prod.ext (map_zero (timesP p)) bone
    simpa only [h₁,columns,AddMonoidHom.coe_mk,ZeroHom.coe_mk,one_mul,zero_mul,zero_add,
      Prod.mk.eta] using h.symm
  have binary (e w a : V p) (he : M e = w) (H : ∀ x, label s hs w x ∈ triangle a P Q) :
      binaryStep r e (shift w a) := by
    intro x
    have E : edge r e x = B.symm (edge s w 0 + embed p (label s hs w (M x))) := by
      simp only [r,edge,map_add,he,← map_sub,label_spec]
      simp [edge]
    have Hx := H (M x)
    rcases Hx with h|h|h
    · rw [E,h]; exact ⟨Or.inl rfl,Or.inl rfl⟩
    · rw [E,h,map_add (embed p),← add_assoc,map_add,eP]
      exact ⟨Or.inr rfl,Or.inl (by simp [shift])⟩
    · change label s hs w (M x) = a+Q at h
      rw [E,h,map_add (embed p),← add_assoc,map_add,eQ]
      exact ⟨Or.inl (by simp [shift]),Or.inr rfl⟩
  let U := shift u t
  let W := shift v z
  have indepShift (w a : V p) : columns P Q (down p (shift w a)) = w := by
    rw [← down_basis P Q (columns_inj_of_det hPQ)]
    change down p (B (B.symm _)) = _
    rw [B.apply_symm_apply,map_add,down_edge s hs,down_embed_zero,add_zero]
  have comp (i : V p) : columns P Q (columns (down p U) (down p W) i) = M i := by
    have hA := indepShift u t
    have hB := indepShift v z
    change columns P Q (down p U) = u at hA
    change columns P Q (down p W) = v at hB
    change _ = columns u v i
    rw [← hA,← hB]
    ext <;> simp [columns] <;> ring
  have indep : Function.Injective (columns (down p U) (down p W)) := by
    intro a b he
    exact hM ((comp a).symm.trans ((congrArg (columns P Q) he).trans (comp b)))
  have hz := rectified_binary r hp ho U W
    (binary (1,0) u t (by ext <;> simp [M,columns]) hu)
    (binary (0,1) v z (by ext <;> simp [M,columns]) hv) indep
  obtain ⟨S,fin,bij,card⟩ := hz
  refine ⟨S,fin,bij,?_⟩
  have hr : Set.range r = B.symm '' Set.range s := by
    ext y
    constructor
    · rintro ⟨x,rfl⟩
      exact ⟨_,Set.mem_range_self _,rfl⟩
    · rintro ⟨_,⟨x,rfl⟩,rfl⟩
      obtain ⟨y,rfl⟩ := (Finite.surjective_of_injective hM) x
      exact ⟨y,rfl⟩
  rwa [hr, ← Set.image_sub,B.symm.injective.injOn.ncard_image] at card

end SquarePlaneLabels

/-! Cyclic cross-transversal estimate used in Leshner's projection argument.
The one-dimensional bound is due to Barcau, Paşol and Ţurcaş. The proof below
uses the fact that two singleton displacement fibers force equal residues. -/

namespace SquarePlaneCyclic

open scoped Pointwise

def red (p : ℕ) : ZMod (p^2) →+* ZMod p :=
  ZMod.castHom (show p ∣ p^2 by simp [pow_two]) (ZMod p)

variable {p : ℕ} [NeZero p]

theorem red_of_mul_eq_zero {a : ZMod (p^2)} (h : (p : ZMod (p^2))*a = 0) : red p a = 0 := by
  have hd : p^2 ∣ p*a.val := (ZMod.natCast_eq_zero_iff _ _).mp (by simpa using h)
  have hv : p ∣ a.val := Nat.dvd_of_mul_dvd_mul_left (NeZero.pos p) (by simpa [pow_two] using hd)
  rw [← ZMod.natCast_zmod_val a, map_natCast, ZMod.natCast_eq_zero_iff]
  exact hv

theorem singleton_unique (s t : ZMod p → ZMod (p^2))
    (hs : Function.RightInverse s (red p))
    (u v : ZMod p) (a b : ZMod (p^2))
    (hu : ∀ x, s (x+u) - t x = a) (hv : ∀ x, s (x+v) - t x = b) : u = v := by
  have move (x : ZMod p) : s (x + (u-v)) = s x + (a-b) := by
    have h₁ := hu (x-v)
    have h₂ := hv (x-v)
    rw [sub_add_cancel] at h₂
    rw [show x+(u-v) = x-v+u by ring]
    abel_nf at h₁ h₂ ⊢
    grind
  have walk (n : ℕ) : s ((n : ZMod p)*(u-v)) = s 0 + (n : ZMod (p^2))*(a-b) := by
    induction n with
    | zero => simp
    | succ n ih => rw [Nat.cast_succ, Nat.cast_succ, add_mul, one_mul, move, ih]; ring
  have hz := walk p
  simp only [ZMod.natCast_self, zero_mul, eq_comm (a := s 0)] at hz
  have hred := red_of_mul_eq_zero (a := a-b) (by linear_combination hz)
  have hmove := congrArg (red p) (move 0)
  simp [hred] at hmove
  rw [hs, hs] at hmove
  exact sub_eq_zero.mp hmove

def fiber (s t : ZMod p → ZMod (p^2)) (u : ZMod p) : Set (ZMod (p^2)) :=
  Set.range (fun x => s (x+u) - t x)

theorem cross_count (s t : ZMod p → ZMod (p^2))
    (hs : Function.RightInverse s (red p)) (ht : Function.RightInverse t (red p)) :
    (Set.range s - Set.range t).ncard = ∑ u, (fiber s t u).ncard := by
  classical
  let D := (Set.range s - Set.range t).toFinset
  have hf (u : ZMod p) : D.filter (fun z => red p z = u) = (fiber s t u).toFinset := by
    ext z
    rw [Set.mem_toFinset]
    simp only [D, Finset.mem_filter, Set.mem_toFinset, Set.mem_sub, fiber, Set.mem_range]
    constructor
    · rintro ⟨⟨_, ⟨i,rfl⟩, _, ⟨j,rfl⟩,rfl⟩, he⟩
      rw [map_sub, hs, ht] at he
      exact ⟨j, by rw [← he]; congr 2; abel⟩
    · rintro ⟨j,rfl⟩
      exact ⟨⟨_,⟨_,rfl⟩,_,⟨_,rfl⟩,rfl⟩,by rw [map_sub,hs,ht]; abel⟩
  have h := Finset.card_eq_sum_card_fiberwise (f := red p) (s := D) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)
  simpa only [hf, D, ← Set.ncard_eq_toFinset_card'] using h

theorem cross_transversals (s t : ZMod p → ZMod (p^2))
    (hs : Function.RightInverse s (red p)) (ht : Function.RightInverse t (red p)) :
    2*p-1 ≤ (Set.range s - Set.range t).ncard := by
  classical
  rw [cross_count s t hs ht]
  have pos (u : ZMod p) : 0 < (fiber s t u).ncard := (Set.ncard_pos (Set.toFinite _)).mpr ⟨_,Set.mem_range_self 0⟩
  have unique (u v : ZMod p) (hu : (fiber s t u).ncard = 1) (hv : (fiber s t v).ncard = 1) :
      u = v := by
    obtain ⟨a,ha⟩ := Set.ncard_eq_one.mp hu
    obtain ⟨b,hb⟩ := Set.ncard_eq_one.mp hv
    apply singleton_unique s t hs u v a b
    · intro x
      have hx : s (x+u) - t x ∈ fiber s t u := Set.mem_range_self x
      rwa [ha, Set.mem_singleton_iff] at hx
    · intro x
      have hx : s (x+v) - t x ∈ fiber s t v := Set.mem_range_self x
      rwa [hb, Set.mem_singleton_iff] at hx
  obtain ⟨r,hr⟩ : ∃ r : ZMod p, ∀ u, u ≠ r → 2 ≤ (fiber s t u).ncard := by
    by_cases h : ∃ r, (fiber s t r).ncard = 1
    · obtain ⟨r,hr⟩ := h
      refine ⟨r,fun u hne => ?_⟩
      have := pos u
      by_contra! hl
      exact hne (unique u r (by omega) hr)
    · exact ⟨0,fun u _ => by have := pos u; have := not_exists.mp h u; omega⟩
  have lower := Finset.sum_le_sum (s := (Finset.univ : Finset (ZMod p)).erase r)
    (f := fun _ => 2) (g := fun u => (fiber s t u).ncard)
    (fun u hu => hr u (Finset.mem_erase.mp hu).1)
  have all := Finset.sum_erase_add (Finset.univ : Finset (ZMod p))
    (fun u => (fiber s t u).ncard) (Finset.mem_univ r)
  simp [Finset.card_erase_of_mem, ZMod.card] at lower
  have := pos r
  omega

end SquarePlaneCyclic

namespace SquarePlaneCyclic
open scoped Pointwise
variable {p : ℕ} [NeZero p]

def rows (X : ZMod p → ZMod p → ZMod (p^2)) (Y : ZMod p → ZMod (p^2)) :
    Set (ZMod (p^2) × ZMod (p^2)) :=
  Set.range (fun t : ZMod p × ZMod p => (X t.2 t.1, Y t.2))

/-- Leshner's projection bound after the horizontal derivative has been straightened. -/
theorem rows_bound (X : ZMod p → ZMod p → ZMod (p^2)) (Y : ZMod p → ZMod (p^2))
    (hX : ∀ j, Function.RightInverse (X j) (red p))
    (hY : Function.RightInverse Y (red p)) :
    (2*p-1)^2 ≤ (rows X Y - rows X Y).ncard := by
  classical
  let V := (Set.range Y - Set.range Y).toFinset
  let D := (rows X Y - rows X Y).toFinset
  have maps : ∀ z ∈ D, z.2 ∈ V := by
    rintro z hz
    change z ∈ (rows X Y - rows X Y).toFinset at hz
    rw [Set.mem_toFinset] at hz
    obtain ⟨_,⟨a,rfl⟩,_,⟨b,rfl⟩,rfl⟩ := Set.mem_sub.mp hz
    exact Set.mem_toFinset.mpr (Set.sub_mem_sub (Set.mem_range_self _) (Set.mem_range_self _))
  have fiber_lower (v : ZMod (p^2)) (hv : v ∈ V) :
      2*p-1 ≤ (D.filter (fun z => z.2 = v)).card := by
    obtain ⟨_,⟨j,rfl⟩,_,⟨k,rfl⟩,rfl⟩ := Set.mem_sub.mp (Set.mem_toFinset.mp hv)
    let A := (Set.range (X j) - Set.range (X k)).toFinset
    have embed : A.card ≤ (D.filter (fun z => z.2 = Y j-Y k)).card := by
      apply Finset.card_le_card_of_injOn (fun x => (x, Y j - Y k))
      · intro x hx
        obtain ⟨_,⟨i,rfl⟩,_,⟨l,rfl⟩,rfl⟩ := Set.mem_sub.mp (Set.mem_toFinset.mp hx)
        refine Finset.mem_filter.mpr ⟨Set.mem_toFinset.mpr ?_,rfl⟩
        exact Set.sub_mem_sub (Set.mem_range_self (f := fun t : ZMod p × ZMod p =>
          (X t.2 t.1, Y t.2)) (i,j)) (Set.mem_range_self (l,k))
      · intro a _ b _ h
        exact congrArg Prod.fst h
    exact (cross_transversals _ _ (hX j) (hX k)).trans (by
      simpa only [A, ← Set.ncard_eq_toFinset_card'] using embed)
  have sum_bound := Finset.sum_le_sum fiber_lower
  have total := Finset.card_eq_sum_card_fiberwise (f := Prod.snd) maps
  rw [← total] at sum_bound
  simp only [Finset.sum_const, nsmul_eq_mul, V, D, ← Set.ncard_eq_toFinset_card'] at sum_bound
  rw [pow_two]
  exact (Nat.mul_le_mul_right _ (cross_transversals Y Y hY hY)).trans sum_bound

theorem ker_mul_ker {x y : ZMod (p^2)} (hx : red p x = 0) (hy : red p y = 0) :
    x*y = 0 := by
  have dvd (z : ZMod (p^2)) (hz : red p z = 0) : p ∣ z.val := by
    rw [← ZMod.natCast_zmod_val z, map_natCast, ZMod.natCast_eq_zero_iff] at hz
    exact hz
  have hd : p^2 ∣ x.val*y.val := by simpa only [pow_two] using mul_dvd_mul (dvd x hx) (dvd y hy)
  simpa only [Nat.cast_mul, ZMod.natCast_zmod_val] using
    (ZMod.natCast_eq_zero_iff _ _).mpr hd

def shear (c : ZMod (p^2)) : ZMod (p^2) × ZMod (p^2) →+ ZMod (p^2) × ZMod (p^2) where
  toFun x := (x.1, x.2 - c*x.1)
  map_zero' := by simp
  map_add' x y := by ext <;> simp <;> ring

theorem shear_injective (c : ZMod (p^2)) : Function.Injective (shear c) := by
  rintro ⟨a,b⟩ ⟨u,v⟩ h
  change (a,b-c*a) = (u,v-c*u) at h
  obtain ⟨rfl,hv⟩ := Prod.mk.inj h
  exact Prod.ext rfl (sub_left_inj.mp hv)

/-- A section with constant transverse increment on horizontal edges satisfies
the sharp lower bound. The shear uses that the product of two elements of the
kernel of reduction mod p is zero modulo p². -/
theorem constant_horizontal (s : ZMod p × ZMod p → ZMod (p^2) × ZMod (p^2))
    (hs : ∀ t, (red p (s t).1, red p (s t).2) = t)
    (c : ZMod (p^2)) (step : ∀ i j, (s (i+1,j)).2 - (s (i,j)).2 = c) :
    (2*p-1)^2 ≤ (Set.range s - Set.range s).ncard := by
  have sx (i j : ZMod p) : red p (s (i,j)).1 = i := congrArg Prod.fst (hs (i,j))
  have sy (i j : ZMod p) : red p (s (i,j)).2 = j := congrArg Prod.snd (hs (i,j))
  have hc : red p c = 0 := by rw [← step 0 0, map_sub, sy, sy, sub_self]
  let X (j i : ZMod p) := (s (i,j)).1
  let Y (j : ZMod p) := ((shear c) (s (0,j))).2
  have fixed (i j : ZMod p) : ((shear c) (s (i+1,j))).2 = ((shear c) (s (i,j))).2 := by
    have hker : red p ((s (i+1,j)).1 - (s (i,j)).1 - 1) = 0 := by
      rw [map_sub,map_sub,map_one,sx,sx]; ring
    have e := ker_mul_ker hc hker
    change (s (i+1,j)).2 - c*(s (i+1,j)).1 = (s (i,j)).2 - c*(s (i,j)).1
    linear_combination step i j - e
  have allrows (i j : ZMod p) : ((shear c) (s (i,j))).2 = Y j := by
    have iter (n : ℕ) : ((shear c) (s ((n : ZMod p),j))).2 = Y j := by
      induction n with
      | zero => simp [Y]
      | succ n ih => rw [Nat.cast_succ, fixed, ih]
    simpa using iter i.val
  have hr : rows X Y = (shear c) '' Set.range s := by
    ext z
    constructor
    · rintro ⟨⟨i,j⟩,rfl⟩
      exact ⟨_,⟨(i,j),rfl⟩,Prod.ext rfl (allrows i j)⟩
    · rintro ⟨_,⟨⟨i,j⟩,rfl⟩,rfl⟩
      exact ⟨(i,j),Prod.ext rfl (allrows i j).symm⟩
  have hY : Function.RightInverse Y (red p) := by
    intro j
    change red p ((s (0,j)).2 - c*(s (0,j)).1) = j
    rw [map_sub,map_mul,sy,hc,zero_mul,sub_zero]
  have h := rows_bound X Y (fun j i => sx i j) hY
  rw [hr, ← Set.image_sub, (shear_injective c).injOn.ncard_image] at h
  exact h

end SquarePlaneCyclic

/-! Leshner's projection theorem in the original coordinates of any section. -/

namespace SquarePlaneLabels
open scoped Pointwise
variable {p : ℕ} [Fact p.Prime]

theorem scalar_of_det_zero {K : Type*} [Field K] {u v : K × K} (hu : u ≠ 0)
    (h : determinant u v = 0) : ∃ t : K, v = t • u := by
  change u.1*v.2-u.2*v.1=0 at h
  by_cases hx : u.1 = 0
  · have hy : u.2 ≠ 0 := fun he => hu (Prod.ext hx he)
    have hv : v.1 = 0 := by
      rw [hx,zero_mul,zero_sub,neg_eq_zero] at h
      exact (mul_eq_zero.mp h).resolve_left hy
    refine ⟨v.2/u.2,Prod.ext ?_ ?_⟩
    · simp [hx,hv]
    · exact (div_mul_cancel₀ _ hy).symm
  · refine ⟨v.1/u.1,Prod.ext (div_mul_cancel₀ _ hx).symm ?_⟩
    change v.2 = v.1/u.1*u.2
    field_simp
    linear_combination h

def detMap {K : Type*} [CommRing K] (w : K × K) : K × K →+ K where
  toFun x := determinant w x
  map_zero' := by simp [determinant]
  map_add' a b := by simp [determinant]; ring

theorem collinear_direction (s : V p → G p) (hs : Function.RightInverse s (down p))
    (u w : V p) (hw : w ≠ 0)
    (line : ∀ x, determinant w (label s hs u x) = 0) :
    ∀ x, determinant u (label s hs u x) = 0 := by
  have loop := congrArg (detMap w) (cycle_labels s hs u 0)
  rw [map_sum,map_neg] at loop
  have z (x : V p) : detMap w (label s hs u x) = 0 := line x
  simp only [z,Finset.sum_const_zero,zero_eq_neg] at loop
  obtain ⟨t,ht⟩ := scalar_of_det_zero hw (show determinant w u = 0 from loop)
  intro x
  obtain ⟨r,hr⟩ := scalar_of_det_zero hw (line x)
  rw [hr,ht]
  simp [determinant]; ring

theorem exists_second_column (u : V p) (hu : u ≠ 0) : ∃ v : V p, determinant u v ≠ 0 := by
  by_cases h : u.1 = 0
  · refine ⟨(1,0),?_⟩
    have hy : u.2 ≠ 0 := fun e => hu (Prod.ext h e)
    simpa [determinant] using hy
  · exact ⟨(0,1),by simpa [determinant] using h⟩

theorem collinear_bound (s : V p → G p) (hs : Function.RightInverse s (down p))
    (u : V p) (hu : u ≠ 0) (w : V p) (hw : w ≠ 0)
    (line : ∀ x, determinant w (label s hs u x) = 0) :
    (2*p-1)^2 ≤ (Set.range s - Set.range s).ncard := by
  obtain ⟨v,hv⟩ := exists_second_column u hu
  have hi := columns_inj_of_det hv
  let f := rebase s u v hi
  have hf := rebase_section s hs u v hi
  have ha : columns u v (1,0) = u := by ext <;> simp [columns]
  have hy (x : V p) : (label f hf (1,0) x).2 = 0 := by
    have h := collinear_direction s hs u w hw line (columns u v x)
    have change_label := rebase_label s hs u v hi (1,0) x
    rw [ha] at change_label
    rw [← change_label] at h
    let z := label f hf (1,0) x
    change determinant u (columns u v z) = 0 at h
    have prod : z.2*determinant u v = 0 := by
      unfold determinant at h ⊢
      unfold columns at h
      dsimp at h
      linear_combination h
    exact (mul_eq_zero.mp prod).resolve_right hv
  have transverse (i j : ZMod p) : (f (i+1,j)).2 - (f (i,j)).2 = (edge f (1,0) 0).2 := by
    have he := congrArg Prod.snd (label_spec f hf (1,0) (i,j))
    change timesP p (label f hf (1,0) (i,j)).2 = (edge f (1,0) (i,j)).2 - _ at he
    rw [hy, map_zero] at he
    simpa [edge] using sub_eq_zero.mp he.symm
  rw [← rebase_ncard s u v hi]
  apply SquarePlaneCyclic.constant_horizontal f _ _ transverse
  intro t
  exact hf t

end SquarePlaneLabels

/-! The standard box is due to Barcau, Paşol and Ţurcaş. The Lean box,
fiber count and compensation below are reused from ZedingZhang, merged
Left to Solve reduction arxiv-2606.27961.R1 (PR 8755). -/

namespace SquarePlaneUpstream
open OMA.S_arxiv_2606_27961
open scoped Pointwise BigOperators

lemma box (p : ℕ) [NeZero p] (hp : 2 ≤ p) :
    ∃ T : Set (Plane (p^2)), Set.BijOn (reduce p) T Set.univ ∧
      (T-T).ncard = (2*p-1)^2 := by
  classical
  let lift (x : ZMod p) : ZMod (p^2) := x.val
  let A := Set.range lift
  have hpp : p ≤ p^2 := by nlinarith
  have hw : 2*p-1 ≤ p^2 := by
    have : 2*p ≤ p^2 := by nlinarith
    omega
  have inv (x : ZMod p) : ((lift x).val : ZMod p) = x := by
    dsimp [lift]
    rw [ZMod.val_natCast_of_lt (x.val_lt.trans_le hpp), ZMod.natCast_zmod_val]
  have hb : Set.BijOn (fun z : ZMod (p^2) => (z.val : ZMod p)) A Set.univ := by
    refine ⟨fun _ _ => Set.mem_univ _, ?_, ?_⟩
    · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ he
      exact congrArg lift ((inv x).symm.trans (he.trans (inv y)))
    · intro y _
      exact ⟨lift y, ⟨y, rfl⟩, inv y⟩
  refine ⟨A ×ˢ A, ?_, ?_⟩
  · unfold OMA.S_arxiv_2606_27961.reduce
    simpa only [Prod.map, Set.univ_prod_univ] using hb.prodMap hb
  have hm (i : ℕ) (hi : i < p) : (i : ZMod (p^2)) ∈ A :=
    ⟨(i : ZMod p), by dsimp only [lift]; rw [ZMod.val_natCast_of_lt hi]⟩
  let shift (i : ℕ) : ZMod (p^2) := (i : ZMod (p^2)) - ((p-1 : ℕ) : ZMod (p^2))
  let I := Finset.range (2*p-1)
  have repr : A-A = shift '' (I : Set ℕ) := by
    ext z
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, _, ⟨y, rfl⟩, rfl⟩
      have hx := x.val_lt
      have hy := y.val_lt
      let k := x.val + (p-1-y.val)
      have hsum : k+y.val = x.val+(p-1) := by dsimp [k]; omega
      refine ⟨k, Finset.mem_range.mpr (by dsimp [k]; omega), ?_⟩
      have hh := congrArg (fun n : ℕ => (n : ZMod (p^2))) hsum
      push_cast at hh
      dsimp [shift,lift]
      linear_combination hh
    · rintro ⟨i, hi, rfl⟩
      have hi' := Finset.mem_range.mp hi
      by_cases h : i < p
      · exact ⟨_, hm i h, _, hm (p-1) (by omega), rfl⟩
      · have hd : i-(p-1) < p := by omega
        refine ⟨_, hm _ hd, _, hm 0 (by omega), ?_⟩
        simp [shift, Nat.cast_sub (show p-1 ≤ i by omega)]
  have inj : Set.InjOn shift (I : Set ℕ) := by
    intro i hi j hj he
    have hh : (i : ZMod (p^2)) = j := by simpa only [shift, sub_left_inj] using he
    have := congrArg ZMod.val hh
    rwa [ZMod.val_natCast_of_lt ((Finset.mem_range.mp hi).trans_le hw),
      ZMod.val_natCast_of_lt ((Finset.mem_range.mp hj).trans_le hw)] at this
  rw [Set.prod_sub_prod_comm, Set.ncard_prod, repr, inj.ncard_image, Set.ncard_coe_finset]
  simp [I,pow_two]

lemma reduce_sub (p : ℕ) [NeZero p] (a b : Plane (p^2)) :
    reduce p (a-b) = reduce p a - reduce p b := by
  have hd : p ∣ p^2 := by simp [pow_two]
  unfold OMA.S_arxiv_2606_27961.reduce
  apply Prod.ext
  · exact (by simpa only [Prod.fst_sub, Prod.snd_sub, ZMod.cast_eq_val] using
      (ZMod.cast_sub (R := ZMod p) hd a.1 b.1))
  · exact (by simpa only [Prod.fst_sub, Prod.snd_sub, ZMod.cast_eq_val] using
      (ZMod.cast_sub (R := ZMod p) hd a.2 b.2))

lemma fiber_count (p : ℕ) [NeZero p] (s : Plane p → Plane (p^2))
    (hs : Function.RightInverse s (reduce p)) :
    (Set.range s - Set.range s).ncard =
      ∑ u, (Set.range (fun x : Plane p => s (x+u) - s x)).ncard := by
  classical
  let D := (Set.range s - Set.range s).toFinset
  have hf (u : Plane p) : D.filter (fun t => reduce p t = u) =
      (Set.range (fun x : Plane p => s (x+u) - s x)).toFinset := by
    ext t
    simp only [Finset.mem_filter, D, Set.mem_toFinset, Set.mem_range, Set.mem_sub]
    constructor
    · rintro ⟨⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, rfl⟩, he⟩
      rw [reduce_sub, hs a, hs b] at he
      exact ⟨b, by rw [← he]; abel_nf⟩
    · rintro ⟨x, rfl⟩
      refine ⟨⟨_, ⟨x+u, rfl⟩, _, ⟨x, rfl⟩, rfl⟩, ?_⟩
      rw [reduce_sub, hs _, hs _]
      abel
  have h := Finset.card_eq_sum_card_fiberwise (f := reduce p) (s := D)
    (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
  simpa only [hf, D, ← Set.ncard_eq_toFinset_card'] using h

lemma compensation (p : ℕ) [NeZero p] (hp : 2 ≤ p) (c : Plane p → ℕ) (hz : c 0 = 1)
    (h : (∑ u ∈ Finset.univ.erase 0, (4 - c u)) ≤
      4*(p-1) + ∑ u ∈ Finset.univ.erase 0, (c u - 4)) :
    (2*p-1)^2 ≤ ∑ u, c u := by
  classical
  let U := (Finset.univ : Finset (Plane p)).erase 0
  have bal : (∑ u ∈ U, c u) + (∑ u ∈ U, (4-c u)) =
      (∑ _u ∈ U, (4 : ℕ)) + ∑ u ∈ U, (c u-4) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun u _ => by omega)
  have hcard : U.card = p*p-1 := by simp [U,Plane,Fintype.card_prod,ZMod.card]
  have tot := Finset.sum_erase_add (Finset.univ : Finset (Plane p)) c (Finset.mem_univ 0)
  change (∑ u ∈ U, c u) + c 0 = _ at tot
  change (∑ u ∈ U, (4-c u)) ≤ 4*(p-1) + ∑ u ∈ U, (c u-4) at h
  simp only [Finset.sum_const, nsmul_eq_mul, hcard] at bal
  have pp : 1 ≤ p*p := by nlinarith
  have sq : (2*p-1)^2 + 4*(p-1) = (p*p-1)*4 + 1 := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hp
    simp only [Nat.mul_add]
    have e : 2*2+2*k-1 = 3+2*k := by omega
    have f : 2+k-1 = 1+k := by omega
    have g : (2+k)*2+(2+k)*k-1 = 3+4*k+k*k := by
      have := Nat.zero_le (k*k)
      nlinarith [Nat.sub_add_cancel (show 1 ≤ (2+k)*2+(2+k)*k by omega)]
    rw [e,f,g]
    ring
  rw [hz] at tot
  change (∑ u ∈ U, c u) + (∑ u ∈ U, (4-c u)) =
    (p*p-1)*4 + ∑ u ∈ U, (c u-4) at bal
  have bound : (2*p-1)^2 + 4*(p-1) ≤ (∑ u, c u) + 4*(p-1) := by
    rw [sq, ← tot]
    omega
  exact Nat.le_of_add_le_add_right bound


end SquarePlaneUpstream

namespace SquarePlaneLabels
open scoped Pointwise
open OMA.S_arxiv_2606_27961 (reduce)

variable {p : ℕ} [Fact p.Prime]

theorem upstream_down (x : G p) : reduce p x = down p x := by
  change ((x.1.val : ZMod p),(x.2.val : ZMod p)) = (red p x.1,red p x.2)
  rw [← ZMod.natCast_zmod_val x.1, ← ZMod.natCast_zmod_val x.2]
  simp [red,ZMod.castHom_apply]

theorem label_edge_ncard (s : V p → G p) (hs : Function.RightInverse s (down p)) (u : V p) :
    (Set.range (label s hs u)).ncard = (Set.range (edge s u)).ncard := by
  let f (z : V p) := embed p z + edge s u 0
  have hi : Function.Injective f := fun _ _ h => embed_inj (add_right_cancel h)
  have eq : f '' Set.range (label s hs u) = Set.range (edge s u) := by
    rw [← Set.range_comp]
    congr 1
    funext x
    simp [f,label_spec]
  rw [← eq,hi.injOn.ncard_image]

theorem label_count (s : V p → G p) (hs : Function.RightInverse s (down p)) :
    (Set.range s-Set.range s).ncard = ∑ u, (Set.range (label s hs u)).ncard := by
  have ht : Function.RightInverse s (reduce p) := fun x => (upstream_down _).trans (hs x)
  rw [SquarePlaneUpstream.fiber_count p s ht]
  exact Finset.sum_congr rfl (fun u _ => (label_edge_ncard s hs u).symm)

theorem strict_spans (s : V p → G p) (hs : Function.RightInverse s (down p))
    (strict : (Set.range s - Set.range s).ncard < (2*p-1)^2) (u : V p) (hu : u ≠ 0) :
    ∀ w : V p, w ≠ 0 → ∃ x, determinant w (label s hs u x) ≠ 0 := by
  intro w hw
  by_contra! line
  exact strict.not_ge (collinear_bound s hs u hu w hw line)

theorem strict_min_three (s : V p → G p) (hs : Function.RightInverse s (down p))
    (strict : (Set.range s - Set.range s).ncard < (2*p-1)^2) (u : V p) (hu : u ≠ 0) :
    3 ≤ (Set.range (label s hs u)).ncard := by
  have spans := strict_spans s hs strict u hu
  obtain ⟨a,ha⟩ := spans (1,0) (by simp)
  let A := label s hs u a
  have hA : A ≠ 0 := by intro h; change determinant (1,0) A ≠ 0 at ha; simp [h,determinant] at ha
  obtain ⟨b,hb⟩ := spans A hA
  let B := label s hs u b
  change determinant A B ≠ 0 at hb
  have hB : B ≠ 0 := by intro h; simp [h,determinant] at hb
  have hab : A ≠ B := by intro h; simp [h,determinant,mul_comm] at hb
  have hc : ({0,A,B} : Set (V p)).ncard = 3 := Set.ncard_eq_three.mpr
    ⟨0,A,B,hA.symm,hB.symm,hab,rfl⟩
  rw [← hc]
  apply Set.ncard_le_ncard _ (Set.finite_range _)
  intro x hx
  rcases hx with h|h|h
  · exact ⟨0,(label_zero s hs u).trans h.symm⟩
  · exact ⟨a,h.symm⟩
  · exact ⟨b,h.symm⟩

/-- Pack pairwise nonparallel vectors greedily, charging at most p−1 points
for each parallel class removed. -/
theorem select_directions (n : ℕ) (W : Finset (V p)) (nz : ∀ x ∈ W, x ≠ 0)
    (large : n*(p-1) < W.card) :
    ∃ f : Fin (n+1) → V p, (∀ i, f i ∈ W) ∧
      ∀ i j, i ≠ j → determinant (f i) (f j) ≠ 0 := by
  classical
  induction n generalizing W with
  | zero =>
    obtain ⟨u,hu⟩ := Finset.card_pos.mp (by simpa using large)
    exact ⟨fun _ => u,fun _ => hu,fun i j hij => (hij (Fin.ext (by omega))).elim⟩
  | succ n ih =>
    obtain ⟨u,hu⟩ := Finset.card_pos.mp (Nat.zero_le _ |>.trans_lt large)
    let S := W.filter (fun x => determinant u x = 0)
    let T := W.filter (fun x => determinant u x ≠ 0)
    have hs : S ⊆ ((Finset.univ : Finset (ZMod p)).erase 0).image (fun a => a • u) := by
      intro x hx
      obtain ⟨hxw,hd⟩ := Finset.mem_filter.mp hx
      obtain ⟨t,he⟩ := scalar_of_det_zero (nz u hu) hd
      apply Finset.mem_image.mpr
      refine ⟨t,Finset.mem_erase.mpr ⟨?_,Finset.mem_univ _⟩,he.symm⟩
      intro ht
      exact nz x hxw (by simpa [ht] using he)
    have bound := (Finset.card_le_card hs).trans Finset.card_image_le
    simp [Finset.card_erase_of_mem,ZMod.card] at bound
    have hsplit : S.card + T.card = W.card := Finset.card_filter_add_card_filter_not _
    have ht : n*(p-1) < T.card := by rw [Nat.succ_mul] at large; omega
    obtain ⟨g, hg, hpair⟩ := ih T (fun x hx => nz x (Finset.mem_filter.mp hx).1) ht
    refine ⟨Fin.cons u g, ?_, ?_⟩
    · exact Fin.cases hu (fun i => (Finset.mem_filter.mp (hg i)).1)
    · intro i j
      refine Fin.cases ?_ (fun a => ?_) i <;> refine Fin.cases ?_ (fun b => ?_) j
      · simp
      · exact fun _ => (Finset.mem_filter.mp (hg b)).2
      · intro _ h
        apply (Finset.mem_filter.mp (hg a)).2
        change determinant (g a) u = 0 at h
        unfold determinant at h ⊢
        linear_combination -h
      · exact fun h => hpair a b (fun he => h (congrArg Fin.succ he))

theorem five_triangles (s : V p → G p) (hs : Function.RightInverse s (down p))
    (strict : (Set.range s - Set.range s).ncard < (2*p-1)^2) :
    ∃ f : Fin 5 → V p, (∀ i, f i ≠ 0 ∧ (Set.range (label s hs (f i))).ncard = 3) ∧
      ∀ i j, i ≠ j → determinant (f i) (f j) ≠ 0 := by
  classical
  let c (u : V p) := (Set.range (label s hs u)).ncard
  let U := (Finset.univ : Finset (V p)).erase 0
  let W := U.filter (fun u => c u = 3)
  have hsize : 4*(p-1) < W.card := by
    by_contra! hle
    apply strict.not_ge
    rw [label_count s hs]
    apply SquarePlaneUpstream.compensation p (Fact.out : Nat.Prime p).two_le c
    · rw [show c 0 = (Set.range (edge s 0)).ncard from label_edge_ncard s hs 0]
      simp [edge]
    · change (∑ u ∈ U, (4-c u)) ≤ _
      have eq : (∑ u ∈ U, (4-c u)) = W.card := by
        change _ = (U.filter _).card
        rw [Finset.card_filter]
        apply Finset.sum_congr rfl
        intro u hu
        have hm := strict_min_three s hs strict u (Finset.mem_erase.mp hu).1
        change 3 ≤ c u at hm
        split_ifs <;> omega
      omega
  obtain ⟨f,hf,hi⟩ := select_directions 4 W (fun x hx =>
    (Finset.mem_erase.mp (Finset.mem_filter.mp hx).1).1) hsize
  exact ⟨f,fun i => ⟨(Finset.mem_erase.mp (Finset.mem_filter.mp (hf i)).1).1,
    (Finset.mem_filter.mp (hf i)).2⟩,hi⟩

end SquarePlaneLabels

namespace SquarePlaneLabels
open scoped Pointwise
variable {p : ℕ} [Fact p.Prime]

theorem strict_prime_ge_five (s : V p → G p) (hs : Function.RightInverse s (down p)) (ho : Odd p)
    (strict : (Set.range s - Set.range s).ncard < (2*p-1)^2) : 5 ≤ p := by
  by_contra! hp
  have hp3 : p = 3 := by obtain ⟨k,hk⟩ := ho; have := (Fact.out : Nat.Prime p).two_le; omega
  subst p
  rw [label_count s hs] at strict
  let U := (Finset.univ : Finset (V 3)).erase 0
  have lc : ∀ u ∈ U, 3 ≤ (Set.range (label s hs u)).ncard :=
    fun u hu => strict_min_three s hs (by rwa [label_count s hs]) u (Finset.mem_erase.mp hu).1
  have lo := Finset.sum_le_sum lc
  have hU : U.card = 8 := by simp [U,V,Fintype.card_prod,ZMod.card]
  have h0 : 0 < (Set.range (label s hs 0)).ncard :=
    (Set.ncard_pos (Set.finite_range _)).mpr (Set.range_nonempty _)
  have total := Finset.sum_erase_add (Finset.univ : Finset (V 3))
    (fun u => (Set.range (label s hs u)).ncard) (Finset.mem_univ 0)
  change (∑ u ∈ U, _) + _ = _ at total
  norm_num [Finset.sum_const,hU,nsmul_eq_mul] at lo
  omega

end SquarePlaneLabels

namespace SquarePlaneLabels
open scoped Pointwise
variable {p : ℕ} [Fact p.Prime]

structure TriangleData (p : ℕ) where
  t : V p
  a : V p
  b : V p
  indep : determinant a b ≠ 0

def TriangleData.points (T : TriangleData p) := triangle T.t T.a T.b

def unsigned {A : Type*} [AddCommGroup A] [DecidableEq A] (a : A) : Finset A := {a,-a}

theorem unsigned_eq {A : Type*} [AddCommGroup A] [DecidableEq A] (a b : A) :
    unsigned a = unsigned b ↔ a = b ∨ a = -b := by
  constructor
  · intro h
    have ha : a ∈ unsigned a := Finset.mem_insert_self _ _
    simpa [h,unsigned] using (show a ∈ unsigned b from h ▸ ha)
  · rintro (rfl|rfl)
    · rfl
    · simp [unsigned,Finset.pair_comm]

def TriangleData.chords (T : TriangleData p) : Finset (Finset (V p)) :=
  {unsigned T.a, unsigned T.b, unsigned (T.b-T.a)}

theorem TriangleData.det_ne_rev (T : TriangleData p) : determinant T.b T.a ≠ 0 := by
  intro h
  apply T.indep
  unfold determinant at h ⊢
  linear_combination -h

theorem TriangleData.chords_size (T : TriangleData p) : T.chords.card = 3 := by
  have h := T.indep
  have a : unsigned T.a ≠ unsigned T.b := by
    intro eq
    rcases (unsigned_eq _ _).mp eq with eq|eq <;> apply h <;> rw [eq] <;>
      simp [determinant,mul_comm]
  have b : unsigned T.b ≠ unsigned (T.b-T.a) := by
    intro eq
    rcases (unsigned_eq _ _).mp eq with eq|eq <;>
      have x := congrArg Prod.fst eq <;> have y := congrArg Prod.snd eq <;>
      simp only [Prod.fst_neg,Prod.fst_sub,Prod.snd_neg,Prod.snd_sub] at x y <;>
      apply h <;> unfold determinant <;>
      first | linear_combination (norm := ring1) T.b.2*x-T.b.1*y |
        linear_combination (norm := ring1) T.b.1*y-T.b.2*x
  have c : unsigned T.a ≠ unsigned (T.b-T.a) := by
    intro eq
    rcases (unsigned_eq _ _).mp eq with eq|eq <;>
      have x := congrArg Prod.fst eq <;> have y := congrArg Prod.snd eq <;>
      simp only [Prod.fst_neg,Prod.fst_sub,Prod.snd_neg,Prod.snd_sub] at x y <;>
      apply h <;> unfold determinant <;>
      first | linear_combination (norm := ring1) T.a.2*x-T.a.1*y |
        linear_combination (norm := ring1) T.a.1*y-T.a.2*x
  simp [TriangleData.chords,a,b,c]

theorem TriangleData.chord_on {T : TriangleData p} {w : V p}
    (h : unsigned w ∈ T.chords) :
    ∃ t z, T.points = triangle t w z ∧
      (determinant w z = determinant T.a T.b ∨ determinant w z = -determinant T.a T.b) := by
  simp only [TriangleData.chords,Finset.mem_insert,Finset.mem_singleton,unsigned_eq] at h
  have perm (a b c : V p) : ({a,b,c} : Set (V p)) = {a,c,b} := by
    ext x; simp only [Set.mem_insert_iff,Set.mem_singleton_iff]; tauto
  rcases h with (rfl|rfl)|(rfl|rfl)|(rfl|rfl)
  · exact ⟨T.t,T.b,rfl,Or.inl rfl⟩
  · refine ⟨T.t+T.a,T.b-T.a,?_,Or.inr ?_⟩
    · ext x; simp [TriangleData.points,triangle,add_assoc,add_comm,add_left_comm,sub_eq_add_neg,
        or_assoc,or_comm,or_left_comm]
    · simp [determinant]; ring
  · exact ⟨T.t,T.a,perm _ _ _,Or.inr (by unfold determinant; ring)⟩
  · refine ⟨T.t+T.b,T.a-T.b,?_,Or.inl ?_⟩
    · ext x; simp [TriangleData.points,triangle,add_assoc,add_comm,add_left_comm,sub_eq_add_neg,
        or_assoc,or_comm,or_left_comm]
    · simp [determinant]; ring
  · refine ⟨T.t+T.a,-T.a,?_,Or.inl ?_⟩
    · ext x; simp [TriangleData.points,triangle,add_assoc,add_comm,add_left_comm,sub_eq_add_neg,
        or_assoc,or_comm,or_left_comm]
    · simp [determinant]; ring
  · refine ⟨T.t+T.b,-T.b,?_,Or.inr ?_⟩
    · ext x; simp [TriangleData.points,triangle,add_assoc,add_comm,add_left_comm,sub_eq_add_neg,
        or_assoc,or_comm,or_left_comm]
    · simp [determinant]; ring

theorem realize_triangle (s : V p → G p) (hs : Function.RightInverse s (down p))
    (strict : (Set.range s-Set.range s).ncard < (2*p-1)^2) (u : V p) (hu : u ≠ 0)
    (three : (Set.range (label s hs u)).ncard = 3) :
    ∃ T : TriangleData p, T.points = Set.range (label s hs u) := by
  obtain ⟨x,y,z,hxy,hxz,hyz,H⟩ := Set.ncard_eq_three.mp three
  let a := y-x
  let b := z-x
  have ha : a ≠ 0 := sub_ne_zero.mpr hxy.symm
  have heq : Set.range (label s hs u) = triangle x a b := by
    rw [H]; simp [triangle,a,b]
  have indep : determinant a b ≠ 0 := by
    intro h
    have inLine (w : V p) (hw : w ∈ triangle x a b) : detMap a w = detMap a x := by
      rcases hw with rfl|rfl|hw
      · rfl
      · rw [map_add]; simp [detMap,determinant,mul_comm]
      · change w = x+b at hw
        rw [hw,map_add,show detMap a b = 0 from h,add_zero]
    have zeroin : (0 : V p) ∈ triangle x a b := heq ▸ ⟨0,label_zero s hs u⟩
    have hz := inLine _ zeroin
    rw [map_zero] at hz
    obtain ⟨t,ht⟩ := strict_spans s hs strict u hu a ha
    exact ht ((inLine _ (heq ▸ Set.mem_range_self t)).trans hz.symm)
  exact ⟨⟨x,a,b,indep⟩,heq.symm⟩

end SquarePlaneLabels

namespace SquarePlaneLabels
variable {p : ℕ} [Fact p.Prime]

theorem unsigned_neg (w : V p) : unsigned (-w) = unsigned w := (unsigned_eq _ _).mpr (Or.inr rfl)

theorem TriangleData.chord_of_diff (T : TriangleData p) {x y : V p}
    (hx : x ∈ T.points) (hy : y ∈ T.points) (hne : x-y ≠ 0) :
    unsigned (x-y) ∈ T.chords := by
  simp only [TriangleData.points,triangle,Set.mem_insert_iff,Set.mem_singleton_iff] at hx hy
  simp only [TriangleData.chords,Finset.mem_insert,Finset.mem_singleton,unsigned_eq]
  rcases hx with rfl|rfl|rfl <;> rcases hy with rfl|rfl|rfl <;>
    first | exact (hne (sub_self _)).elim | solve | abel | left; left; abel1 |
      left; right; abel1 | right; left; left; abel1 | right; left; right; abel1 |
      right; right; left; abel1 | right; right; right; abel1

theorem TriangleData.mem_of_chord {T : TriangleData p} {w : V p}
    (h : unsigned w ∈ T.chords) : ∃ a ∈ T.points, ∃ b ∈ T.points, a-b = w := by
  obtain ⟨t,z,eq,_⟩ := T.chord_on h
  rw [eq]
  exact ⟨t+w,Or.inr (Or.inl rfl), t,Or.inl rfl,add_sub_cancel_left _ _⟩

theorem TriangleData.shared_flat {A : Type*} [AddCommGroup A] (s : V p → G p)
    (hs : Function.RightInverse s (down p)) (u v : V p) (T U : TriangleData p)
    (ht : Set.range (label s hs u) = T.points) (hu : Set.range (label s hs v) = U.points)
    (π : V p →+ A) (kill : ∀ w, unsigned w ∈ T.chords → unsigned w ∈ U.chords → π w = 0) :
    ∀ x, π (label s hs u (x+v)) = π (label s hs u x) := by
  intro x
  apply sub_eq_zero.mp
  rw [← map_sub]
  by_cases h : label s hs u (x+v) - label s hs u x = 0
  · rw [h,map_zero]
  apply kill
  · exact T.chord_of_diff (ht ▸ Set.mem_range_self _) (ht ▸ Set.mem_range_self _) h
  · rw [label_curl s hs u v x] at h ⊢
    exact U.chord_of_diff (hu ▸ Set.mem_range_self _) (hu ▸ Set.mem_range_self _) h

end SquarePlaneLabels

/-! Incidence counting in the last step of the triangular direction argument. -/

namespace SquarePlaneChordIncidence

/-- Among five three-element chord sets meeting pairwise, three share a chord. -/
theorem common_in_three {A : Type*} [DecidableEq A] (c : Fin 5 → Finset A)
    (size : ∀ i, (c i).card = 3)
    (meet : ∀ i j, i ≠ j → ∃ w, w ∈ c i ∧ w ∈ c j) :
    ∃ i j k : Fin 5, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ ∃ w, w ∈ c i ∧ w ∈ c j ∧ w ∈ c k := by
  classical
  have hits (i : Fin 4) := meet 0 i.succ (Fin.succ_ne_zero i).symm
  choose f hf hg using hits
  have repeatHit : ¬Function.Injective f := by
    intro hi
    have hc := Finset.card_le_card_of_injOn f
      (s := (Finset.univ : Finset (Fin 4))) (t := c 0) (fun i _ => hf i) hi.injOn
    simp [size] at hc
  obtain ⟨i,j,he,hne⟩ := Function.not_injective_iff.mp repeatHit
  exact ⟨0,i.succ,j.succ,(Fin.succ_ne_zero _).symm,(Fin.succ_ne_zero _).symm,
    fun h => hne (Fin.succ_injective _ h),f i,hf i,hg i,he ▸ hg j⟩

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

def unitEdge (w a : G) : Finset G := {a,a+w}

theorem meeting_starts (w a b : G)
    (hm : ∃ x, x ∈ unitEdge w a ∧ x ∈ unitEdge w b) :
    a = b ∨ a = b+w ∨ a = b-w := by
  obtain ⟨x,hx,hy⟩ := hm
  simp only [unitEdge,Finset.mem_insert,Finset.mem_singleton] at hx hy
  rcases hx with rfl|rfl <;> rcases hy with h|h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (eq_sub_of_add_eq h))
  · exact Or.inl (add_right_cancel h)

/-- Three pairwise intersecting edges of a cycle with step w cannot all be
distinct when w and 3w are nonzero. -/
theorem cycle_no_three (w a b c : G) (hw : w ≠ 0) (h3 : 3 • w ≠ 0)
    (hab : ∃ x, x ∈ unitEdge w a ∧ x ∈ unitEdge w b)
    (hac : ∃ x, x ∈ unitEdge w a ∧ x ∈ unitEdge w c)
    (hbc : ∃ x, x ∈ unitEdge w b ∧ x ∈ unitEdge w c) :
    a = b ∨ a = c ∨ b = c := by
  have e₁ := meeting_starts w a b hab
  have e₂ := meeting_starts w a c hac
  have e₃ := meeting_starts w b c hbc
  by_contra! h
  rcases e₁ with e₁|e₁|e₁ <;> rcases e₂ with e₂|e₂|e₂ <;>
    rcases e₃ with e₃|e₃|e₃ <;>
    first | exact h.1 e₁ | exact h.2.1 e₂ | exact h.2.2 e₃ |
      (apply hw; linear_combination (norm := (abel_nf <;> done)) e₁-e₂+e₃) |
      (apply hw; linear_combination (norm := (abel_nf <;> done)) -e₁+e₂-e₃) |
      (apply h3; linear_combination (norm := (abel_nf <;> done)) e₁-e₂+e₃) |
      (apply h3; linear_combination (norm := (abel_nf <;> done)) -e₁+e₂-e₃)

end SquarePlaneChordIncidence

namespace SquarePlaneLabels
open SquarePlaneChordIncidence
variable {p : ℕ} [Fact p.Prime]

theorem TriangleData.chord_ne_zero (T : TriangleData p) {w : V p} (h : unsigned w ∈ T.chords) :
    w ≠ 0 := by
  intro hz
  obtain ⟨t,z,_,hw⟩ := T.chord_on h
  have hn : determinant w z ≠ 0 := by rcases hw with h|h <;> simp [h,T.indep]
  exact hn (by simp [hz,determinant])

theorem TriangleData.chord_repr (T : TriangleData p) {c : Finset (V p)} (hc : c ∈ T.chords) :
    ∃ w, c = unsigned w := by
  rcases Finset.mem_insert.mp hc with h|hh
  · exact ⟨_,h⟩
  rcases Finset.mem_insert.mp hh with h|h
  · exact ⟨_,h⟩
  · exact ⟨_,Finset.mem_singleton.mp h⟩

theorem TriangleData.chords_of_points {T U : TriangleData p} (h : T.points = U.points) :
    T.chords = U.chords := by
  have mono (T U : TriangleData p) (he : T.points = U.points) : T.chords ⊆ U.chords := by
    intro c hc
    obtain ⟨w,rfl⟩ := T.chord_repr hc
    obtain ⟨a,ha,b,hb,hsub⟩ := T.mem_of_chord hc
    rw [← hsub] at hc ⊢
    exact U.chord_of_diff (he ▸ ha) (he ▸ hb) (T.chord_ne_zero hc)
  exact Finset.Subset.antisymm (mono T U h) (mono U T h.symm)

theorem TriangleData.chords_of_base (T : TriangleData p) {t w z : V p}
    (he : T.points = triangle t w z) (hn : determinant w z ≠ 0) :
    T.chords = {unsigned w,unsigned z,unsigned (z-w)} :=
  TriangleData.chords_of_points (U := ⟨t,w,z,hn⟩) he

theorem square_det_self (w : V p) : determinant w w = 0 := by simp [determinant,mul_comm]

theorem common_det_of_two (T U : TriangleData p) {w : V p} (hw : unsigned w ∈ T.chords)
    (hu : unsigned w ∈ U.chords) (extra : ∃ c ∈ T.chords, c ∈ U.chords ∧ c ≠ unsigned w) :
    unsigned (determinant T.a T.b) = unsigned (determinant U.a U.b) := by
  obtain ⟨c,ct,cu,cw⟩ := extra
  obtain ⟨v,rfl⟩ := T.chord_repr ct
  have calcD (A : TriangleData p) (h₁ : unsigned w ∈ A.chords) (h₂ : unsigned v ∈ A.chords) :
      unsigned (determinant w v) = unsigned (determinant A.a A.b) := by
    obtain ⟨t,z,pts,hz⟩ := A.chord_on h₁
    have hn : determinant w z ≠ 0 := by rcases hz with h|h <;> simp [h,A.indep]
    have detz := (unsigned_eq _ _).mpr hz
    rw [← detz]
    rw [A.chords_of_base pts hn,Finset.mem_insert,Finset.mem_insert,Finset.mem_singleton] at h₂
    rcases h₂ with h|h|h
    · exact (cw h).elim
    · rcases (unsigned_eq _ _).mp h with h|h
      · rw [h]
      · apply (unsigned_eq _ _).mpr; right; rw [h]; simp [determinant]; ring
    · rcases (unsigned_eq _ _).mp h with h|h
      · apply (unsigned_eq _ _).mpr; left; rw [h]; simp [determinant]; ring
      · apply (unsigned_eq _ _).mpr; right; rw [h]; simp [determinant]; ring
  exact (calcD T hw ct).symm.trans (calcD U hu cu)

structure Oriented (T : TriangleData p) (w : V p) (D : ZMod p) (a : V p) : Prop where
  det : determinant w a = D
  chords : T.chords = {unsigned w,unsigned a,unsigned (a+w)}
  vertices : ∃ t, T.points = triangle t w (a+w) ∨ T.points = triangle t w (-a)

theorem orient (T : TriangleData p) {w : V p} (hw : unsigned w ∈ T.chords)
    (D : ZMod p) (hd : unsigned (determinant T.a T.b) = unsigned D) : ∃ a, Oriented T w D a := by
  obtain ⟨t,z,pts,hz⟩ := T.chord_on hw
  have hn : determinant w z ≠ 0 := by rcases hz with h|h <;> simp [h,T.indep]
  have chords := T.chords_of_base pts hn
  rcases (unsigned_eq _ _).mp (((unsigned_eq _ _).mpr hz).trans hd) with h|h
  · refine ⟨z-w,?_,?_,⟨t,Or.inl ?_⟩⟩
    · rw [← h]; unfold determinant; simp; ring
    · rw [chords,sub_add_cancel,Finset.pair_comm (unsigned z) (unsigned (z-w))]
    · simpa using pts
  · refine ⟨-z,?_,?_,⟨t,Or.inr ?_⟩⟩
    · change (detMap w) (-z) = D
      rw [map_neg,show (detMap w) z = -D from h,neg_neg]
    · rw [chords,unsigned_neg,show -z+w = -(z-w) by abel,unsigned_neg]
    · simpa using pts

theorem edge_meet_of_chord {T U : TriangleData p} {w a b : V p} {D : ZMod p}
    (twoD : D ≠ -D) (ha : Oriented T w D a) (hb : Oriented U w D b)
    (extra : ∃ c ∈ T.chords, c ∈ U.chords ∧ c ≠ unsigned w) :
    ∃ x, x ∈ unitEdge w a ∧ x ∈ unitEdge w b := by
  obtain ⟨c,ct,cu,cw⟩ := extra
  have get (T : TriangleData p) (a : V p) (h : Oriented T w D a) (hc : c ∈ T.chords) :
      ∃ x ∈ unitEdge w a, c = unsigned x ∧ detMap w x = D := by
    rw [h.chords,Finset.mem_insert,Finset.mem_insert,Finset.mem_singleton] at hc
    rcases hc with e|e|e
    · exact (cw e).elim
    · exact ⟨a,Finset.mem_insert_self _ _,e,h.det⟩
    · refine ⟨a+w,Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _)),e,?_⟩
      rw [map_add,show detMap w a = D from h.det,show detMap w w = 0 from square_det_self w,add_zero]
  obtain ⟨x,hx,ex,dx⟩ := get T a ha ct
  obtain ⟨y,hy,ey,dy⟩ := get U b hb cu
  rcases (unsigned_eq _ _).mp (ex.symm.trans ey) with eq|eq
  · exact ⟨x,hx,eq ▸ hy⟩
  · rw [eq,map_neg,dy] at dx
    exact (twoD dx.symm).elim

end SquarePlaneLabels

/-! Window images of the projected edge words in the one-shared-chord case. -/

namespace SquarePlaneMixedWindows

variable {p : ℕ} [Fact p.Prime]

/-- Invariance under any nonzero shift on the prime cycle forces constancy. -/
theorem eq_const_of_shift {A : Type*} (f : ZMod p → A) {k : ZMod p} (hk : k ≠ 0)
    (hf : ∀ x, f (x+k) = f x) (x y : ZMod p) : f x = f y := by
  have orbit (n : ℕ) : f (x + n*k) = f x := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.cast_succ, add_mul, one_mul, ← add_assoc, hf, ih]
  have h := orbit ((y-x)/k).val
  rw [ZMod.natCast_zmod_val, div_mul_cancel₀ _ hk, add_sub_cancel] at h
  exact h.symm

variable {A : Type*} [AddCommGroup A]

def window (f : ZMod p → A) (k : ℕ) (x : ZMod p) : A :=
  ∑ t ∈ Finset.range k, f (x+t)

theorem window_shift (f : ZMod p → A) (k : ℕ) (x : ZMod p) :
    window f k (x+1) - window f k x = f (x+k) - f x := by
  induction k with
  | zero => simp [window]
  | succ k ih =>
    simp only [window, Finset.sum_range_succ] at ih ⊢
    rw [Nat.cast_succ, show x+(k+1) = x+1+k by ring]
    abel_nf at ih ⊢
    grind

/-- The original spacing occurs as an actual difference in every nontrivial
window image, with either sign reoriented to the prescribed spacing. -/
theorem window_pair (f : ZMod p → A) (b d : A)
    (binary : ∀ x, f x = b ∨ f x = b+d)
    (varies : ∃ x y, f x ≠ f y) (k : ℕ) (hk : (k : ZMod p) ≠ 0) :
    ∃ x y, window f k y = window f k x + d := by
  obtain ⟨x, hx⟩ : ∃ x, f (x+k) ≠ f x := by
    by_contra! all
    obtain ⟨u,v,huv⟩ := varies
    exact huv (eq_const_of_shift f hk all u v)
  have h := window_shift f k x
  rcases binary x with h₁ | h₁ <;> rcases binary (x+k) with h₂ | h₂
  · exact False.elim (hx (h₂.trans h₁.symm))
  · refine ⟨x,x+1,?_⟩
    rw [h₁,h₂] at h
    abel_nf at h ⊢
    grind
  · refine ⟨x+1,x,?_⟩
    rw [h₁,h₂] at h
    abel_nf at h ⊢
    grind
  · exact False.elim (hx (h₂.trans h₁.symm))

/-- Two independently varying window sums contain the four corners of the
additive parallelogram determined by their two binary spacings. -/
theorem mixed_rectangle (f g : ZMod p → A) (b c d e : A)
    (hf : ∀ x, f x = b ∨ f x = b+d) (hg : ∀ x, g x = c ∨ g x = c+e)
    (vf : ∃ x y, f x ≠ f y) (vg : ∃ x y, g x ≠ g y)
    (k l : ℕ) (hk : (k : ZMod p) ≠ 0) (hl : (l : ZMod p) ≠ 0) :
    ∃ a : A, {a, a+d, a+e, a+d+e} ⊆
      Set.range (fun t : ZMod p × ZMod p => window f k t.1 + window g l t.2) := by
  obtain ⟨x,y,hx⟩ := window_pair f b d hf vf k hk
  obtain ⟨u,v,hu⟩ := window_pair g c e hg vg l hl
  refine ⟨window f k x + window g l u, ?_⟩
  intro t ht
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
  rcases ht with rfl|rfl|rfl|rfl
  · exact ⟨(x,u),rfl⟩
  · exact ⟨(y,u),by dsimp; rw [hx]; abel⟩
  · exact ⟨(x,v),by dsimp; rw [hu]; abel⟩
  · exact ⟨(y,v),by dsimp; rw [hx,hu]; abel⟩

end SquarePlaneMixedWindows

namespace SquarePlaneMixedWindows
open scoped Pointwise
variable {p : ℕ} [Fact p.Prime] {A : Type*} [AddCommGroup A]

def dx (s : ZMod p × ZMod p → A) (i j : ZMod p) : A :=
  s (i+1,j) - s (i,j)

def dy (s : ZMod p × ZMod p → A) (i j : ZMod p) : A :=
  s (i,j+1) - s (i,j)

theorem commute (s : ZMod p × ZMod p → A) (i j : ZMod p) :
    dx s i (j+1) - dx s i j = dy s (i+1) j - dy s i j := by
  unfold dx dy
  abel

def displacements (s : ZMod p × ZMod p → A) (k l : ℕ) : Set A :=
  Set.range (fun t : ZMod p × ZMod p => s (t.1+k,t.2+l) - s t)

/-- If the projected horizontal derivative has zero vertical derivative, the
same is true with axes exchanged. Every mixed displacement then splits into
independently variable horizontal and vertical window sums. -/
theorem displacements_eq (s : ZMod p × ZMod p → A)
    (h : ∀ i j, dx s i (j+1) = dx s i j) (k l : ℕ) :
    displacements s k l = Set.range (fun t : ZMod p × ZMod p =>
      window (fun x => dx s x 0) k t.1 + window (fun y => dy s 0 y) l t.2) := by
  have cx (i j : ZMod p) : dx s i j = dx s i 0 :=
    eq_const_of_shift _ one_ne_zero (h i) j 0
  have cy (i j : ZMod p) : dy s i j = dy s 0 j := by
    apply eq_const_of_shift (fun i => dy s i j) one_ne_zero _ i 0
    intro x
    have e := commute s x j
    rw [h, sub_self] at e
    exact sub_eq_zero.mp e.symm
  have alongX (i j : ZMod p) (n : ℕ) :
      s (i+n,j) - s (i,j) = window (fun x => dx s x 0) n i := by
    induction n with
    | zero => simp [window]
    | succ n ih =>
      rw [Nat.cast_succ, ← add_assoc]
      simp only [window, Finset.sum_range_succ] at ih ⊢
      rw [← ih, ← cx (i+n) j]
      unfold dx
      abel
  have alongY (i j : ZMod p) (n : ℕ) :
      s (i,j+n) - s (i,j) = window (fun y => dy s 0 y) n j := by
    induction n with
    | zero => simp [window]
    | succ n ih =>
      rw [Nat.cast_succ, ← add_assoc]
      simp only [window, Finset.sum_range_succ] at ih ⊢
      rw [← ih, ← cy i (j+n)]
      unfold dy
      abel
  apply congrArg Set.range
  funext t
  rw [← alongX t.1 t.2 k, ← alongY (t.1+k) t.2 l]
  abel

theorem four_corners {a d e : A} (hd : d ≠ 0) (he : e ≠ 0)
    (hne : d ≠ e) (hopp : d ≠ -e) : ({a,a+d,a+e,a+d+e} : Set A).ncard = 4 := by
  classical
  have hde : d+e ≠ 0 := fun h => hopp (eq_neg_of_add_eq_zero_left h)
  rw [add_assoc]
  simp [Set.ncard_insert_of_notMem, hd, he, hne, hde, add_comm]

theorem at_least_three {a d e : A} (hd : d ≠ 0) (he : e ≠ 0)
    (hdouble : d+d ≠ 0) : 3 ≤ ({a,a+d,a+e,a+d+e} : Set A).ncard := by
  classical
  by_cases hn : d=e
  · subst e
    have hc : ({a,a+d,a+(d+d)} : Set A).ncard = 3 := by
      simp [Set.ncard_insert_of_notMem, hd, hdouble]
    rw [← hc]
    apply Set.ncard_le_ncard _ (by simp)
    simp [add_assoc]
  · have hc : ({a,a+d,a+e} : Set A).ncard = 3 := by
      simp [Set.ncard_insert_of_notMem, hd, he, hn]
    rw [← hc]
    exact Set.ncard_le_ncard (by intro x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto)

theorem projected_window_bounds [Finite A] (s : ZMod p × ZMod p → A)
    (h : ∀ i j, dx s i (j+1) = dx s i j) (b c d e : A)
    (hf : ∀ x, dx s x 0 = b ∨ dx s x 0 = b+d)
    (hg : ∀ y, dy s 0 y = c ∨ dy s 0 y = c+e)
    (vf : ∃ x y, dx s x 0 ≠ dx s y 0) (vg : ∃ x y, dy s 0 x ≠ dy s 0 y)
    (hd : d ≠ 0) (he : e ≠ 0) (hdouble : d+d ≠ 0)
    (k l : ℕ) (hk : (k : ZMod p) ≠ 0) (hl : (l : ZMod p) ≠ 0) :
    3 ≤ (displacements s k l).ncard ∧
    (d ≠ e → d ≠ -e → 4 ≤ (displacements s k l).ncard) := by
  rw [displacements_eq s h]
  obtain ⟨a,ha⟩ := mixed_rectangle _ _ b c d e hf hg vf vg k l hk hl
  have hsize := Set.ncard_le_ncard ha
  refine ⟨(at_least_three hd he hdouble).trans hsize, ?_⟩
  intro hn ho
  simpa only [four_corners hd he hn ho] using hsize

end SquarePlaneMixedWindows

/-! Connecting binary window images in a quotient of the *label* plane to
the actual displacement labels. The words can have nonzero cycle sums. -/

namespace SquarePlaneLabels
open SquarePlaneMixedWindows

variable {p : ℕ} [Fact p.Prime]

def indexPoint (u v : V p) (i j : ZMod p) : V p := i • u + j • v

theorem index_x (u v : V p) (i j : ZMod p) (n : ℕ) :
    indexPoint u v i j + n • u = indexPoint u v (i+n) j := by
  rw [indexPoint,indexPoint,add_smul,Nat.cast_smul_eq_nsmul]; abel

theorem index_y (u v : V p) (i j : ZMod p) (n : ℕ) :
    indexPoint u v i j + n • v = indexPoint u v i (j+n) := by
  rw [indexPoint,indexPoint,add_smul,Nat.cast_smul_eq_nsmul]; abel

noncomputable def block (s : V p → G p) (hs : Function.RightInverse s (down p)) (u x : V p) (n : ℕ) :
    V p := ∑ i ∈ Finset.range n, label s hs u (x+i • u)

theorem embed_block (s : V p → G p) (hs : Function.RightInverse s (down p)) (u x : V p) (n : ℕ) :
    embed p (block s hs u x n) = edge s (n • u) x - n • edge s u 0 := by
  simp only [block,map_sum,label_spec,Finset.sum_sub_distrib,cycle_edges,Finset.sum_const,
    Finset.card_range]
  rfl

theorem mixed_label_formula (s : V p → G p) (hs : Function.RightInverse s (down p))
    (u v x : V p) (k l : ℕ) :
    label s hs (k • u+l • v) x =
      (block s hs u x k + block s hs v (x+k • u) l) -
      (block s hs u 0 k + block s hs v (k • u) l) := by
  apply embed_inj
  simp only [label_spec,map_sub,map_add,embed_block,edge,zero_add,add_assoc]
  abel

variable {A : Type*} [AddCommGroup A]

/-- The range over the input grid of mixed projected labels, translated by
the two window sums at the origin, is the sum of the independent windows. -/
theorem projected_label_grid (s : V p → G p) (hs : Function.RightInverse s (down p))
    (u v : V p) (π : V p →+ A)
    (flat : ∀ x, π (label s hs u (x+v)) = π (label s hs u x)) (k l : ℕ) :
    let f := fun i => π (label s hs u (indexPoint u v i 0))
    let g := fun j => π (label s hs v (indexPoint u v 0 j))
    ∀ i j, π (label s hs (k • u+l • v) (indexPoint u v i j)) =
      (window f k i + window g l j) - (window f k 0 + window g l 0) := by
  intro f g
  have other (x : V p) : π (label s hs v (x+u)) = π (label s hs v x) := by
    have he := congrArg π (label_curl s hs u v x)
    rw [map_sub,map_sub,flat,sub_self] at he
    exact sub_eq_zero.mp he.symm
  have hX (i j : ZMod p) : π (label s hs u (indexPoint u v i j)) = f i := by
    apply eq_const_of_shift (fun y => π (label s hs u (indexPoint u v i y))) one_ne_zero _ j 0
    intro y
    have eq := index_y u v i y 1
    simp only [one_smul,Nat.cast_one] at eq
    rw [← eq, flat]
  have hY (i j : ZMod p) : π (label s hs v (indexPoint u v i j)) = g j := by
    apply eq_const_of_shift (fun x => π (label s hs v (indexPoint u v x j))) one_ne_zero _ i 0
    intro x
    have eq := index_x u v x j 1
    simp only [one_smul,Nat.cast_one] at eq
    rw [← eq, other]
  have bx (i j : ZMod p) : π (block s hs u (indexPoint u v i j) k) = window f k i := by
    simp only [block,map_sum,index_x,hX,window]
  have byy (i j : ZMod p) : π (block s hs v (indexPoint u v i j) l) = window g l j := by
    simp only [block,map_sum,index_y,hY,window]
  have zero : indexPoint u v 0 0 = 0 := by simp [indexPoint]
  have baseX : π (block s hs u 0 k) = window f k 0 := by simpa [zero] using bx 0 0
  have baseY : π (block s hs v (k • u) l) = window g l 0 := by
    simpa [indexPoint,Nat.cast_smul_eq_nsmul] using byy (k : ZMod p) 0
  intro i j
  rw [mixed_label_formula,map_sub,map_add,map_add,bx,index_x,byy,baseX,baseY]

end SquarePlaneLabels

namespace SquarePlaneLabels
open SquarePlaneMixedWindows
variable {p : ℕ} [Fact p.Prime] {A : Type*} [AddCommGroup A]

/-- A projected binary pair directly forces the three- and four-value alternatives
for the actual mixed displacement labels. The fixed path translation is
removed by an injective translation; exactness of the projected words is never
assumed. -/
theorem mixed_label_bounds (s : V p → G p) (hs : Function.RightInverse s (down p))
    (u v : V p) (π : V p →+ A)
    (flat : ∀ x, π (label s hs u (x+v)) = π (label s hs u x)) (b c d e : A)
    (k l : ℕ) (hk : (k : ZMod p) ≠ 0) (hl : (l : ZMod p) ≠ 0) :
    let f := fun i => π (label s hs u (indexPoint u v i 0))
    let g := fun j => π (label s hs v (indexPoint u v 0 j))
    (∀ i, f i = b ∨ f i = b+d) → (∀ j, g j = c ∨ g j = c+e) →
    (∃ x y, f x ≠ f y) → (∃ x y, g x ≠ g y) → d ≠ 0 → e ≠ 0 →
    let N := (Set.range (fun x => π (label s hs (k • u + l • v) x))).ncard
    (d+d ≠ 0 → 3 ≤ N) ∧ (d ≠ e → d ≠ -e → 4 ≤ N) := by
  intro f g hf hg vf vg hd he N
  obtain ⟨a,ha⟩ := mixed_rectangle f g b c d e hf hg vf vg k l hk hl
  let W := Set.range (fun t : ZMod p × ZMod p => window f k t.1 + window g l t.2)
  let C := window f k 0 + window g l 0
  let L := Set.range (fun x => π (label s hs (k • u+l • v) x))
  have subset : W ⊆ (fun z => z+C) '' L := by
    rintro _ ⟨⟨i,j⟩,rfl⟩
    refine ⟨_, Set.mem_range_self (indexPoint u v i j), ?_⟩
    change π (label s hs _ _) + C = _
    rw [projected_label_grid s hs u v π flat k l i j]
    exact sub_add_cancel _ _
  have hi : Function.Injective (fun z : A => z+C) := fun _ _ => add_right_cancel
  have bound := Set.ncard_le_ncard (ha.trans subset)
    ((Set.finite_range (fun x => π (label s hs (k • u+l • v) x))).image (fun z => z+C))
  rw [hi.injOn.ncard_image] at bound
  exact ⟨fun hh => (at_least_three hd he hh).trans bound,
    fun hn ho => (four_corners (a:=a) hd he hn ho) ▸ bound⟩

end SquarePlaneLabels

namespace SquarePlaneLabels
open SquarePlaneMixedWindows
open scoped Pointwise
variable {p : ℕ} [Fact p.Prime]

theorem index_columns (u v : V p) (i j : ZMod p) :
    indexPoint u v i j = columns u v (i,j) := rfl

theorem range_mixed_windows {A : Type*} [AddCommGroup A]
    (s : V p → G p) (hs : Function.RightInverse s (down p)) (u v : V p)
    (hind : determinant u v ≠ 0) (π : V p →+ A)
    (flat : ∀ x, π (label s hs u (x+v)) = π (label s hs u x)) (k l : ℕ) :
    let f := fun i => π (label s hs u (indexPoint u v i 0))
    let g := fun j => π (label s hs v (indexPoint u v 0 j))
    let L := Set.range (fun x => π (label s hs (k • u+l • v) x))
    L = (fun z => z - (window f k 0 + window g l 0)) ''
      (Set.range (window f k) + Set.range (window g l)) := by
  intro f g L
  have onto := Finite.surjective_of_injective (columns_inj_of_det hind)
  ext z
  constructor
  · rintro ⟨x,rfl⟩
    obtain ⟨⟨i,j⟩,rfl⟩ := onto x
    refine ⟨_, Set.add_mem_add (Set.mem_range_self i) (Set.mem_range_self j), ?_⟩
    exact (projected_label_grid s hs u v π flat k l i j).symm
  · rintro ⟨_,⟨_,⟨i,rfl⟩,_,⟨j,rfl⟩,rfl⟩,rfl⟩
    exact ⟨_,projected_label_grid s hs u v π flat k l i j⟩

theorem same_mix_count {A : Type*} [AddCommGroup A]
    (s : V p → G p) (hs : Function.RightInverse s (down p)) (u v : V p)
    (hind : determinant u v ≠ 0) (π : V p →+ A)
    (flat : ∀ x, π (label s hs u (x+v)) = π (label s hs u x)) (k l : ℕ) :
    let f := fun i => π (label s hs u (indexPoint u v i 0))
    let g := fun j => π (label s hs v (indexPoint u v 0 j))
    (Set.range (fun x => π (label s hs (k • u+l • v) x))).ncard =
      (Set.range (window f k) + Set.range (window g l)).ncard := by
  rw [range_mixed_windows s hs u v hind π flat k l]
  exact Set.InjOn.ncard_image (fun a _ b _ he => sub_left_inj.mp he)

theorem cauchy_plane (A B : Set (V p)) (hA : A.Nonempty) (hB : B.Nonempty) :
    min p (A.ncard+B.ncard-1) ≤ (A+B).ncard := by
  classical
  have lo : (p : ℕ∞) ≤ AddMonoid.minOrder (V p) := by
    apply AddMonoid.le_minOrder.mpr
    intro a ha _
    rw [addOrderOf_eq_prime (p_smul_zero a) ha]
  have h := cauchy_davenport_minOrder_add (s := A.toFinset) (t := B.toFinset)
    (Set.toFinset_nonempty.mpr hA) (Set.toFinset_nonempty.mpr hB)
  have e := (min_le_min_right _ lo).trans h
  simpa only [min_le_iff,Nat.cast_le, ← Set.toFinset_add, ← Set.ncard_eq_toFinset_card'] using e

theorem mixed_full_lower (s : V p → G p) (hs : Function.RightInverse s (down p))
    (strict : (Set.range s - Set.range s).ncard < (2*p-1)^2)
    (u v : V p) (hind : determinant u v ≠ 0)
    (flat : ∀ x, label s hs u (x+v) = label s hs u x)
    (k l : ℕ) (hk : (k : ZMod p) ≠ 0) (hl : (l : ZMod p) ≠ 0) (hp : 5 ≤ p) :
    5 ≤ (Set.range (label s hs (k • u+l • v))).ncard := by
  let f := fun i => label s hs u (indexPoint u v i 0)
  let g := fun j => label s hs v (indexPoint u v 0 j)
  have counts (m n : ℕ) : (Set.range (label s hs (m • u+n • v))).ncard =
      (Set.range (window f m) + Set.range (window g n)).ncard :=
    same_mix_count s hs u v hind (AddMonoidHom.id _) flat m n
  have hu : u ≠ 0 := by intro h; simp [h,determinant] at hind
  have hv : v ≠ 0 := by intro h; simp [h,determinant] at hind
  have nz (z : V p) (hz : z ≠ 0) (m : ℕ) (hm : (m : ZMod p) ≠ 0) : m • z ≠ 0 := by
    rw [← Nat.cast_smul_eq_nsmul (ZMod p)]
    exact smul_ne_zero hm hz
  have h₁ := strict_min_three s hs strict (k • u) (nz _ hu _ hk)
  have h₂ := strict_min_three s hs strict (l • v) (nz _ hv _ hl)
  have c₁ := counts k 0
  have c₂ := counts 0 l
  have zw (h : ZMod p → V p) : Set.range (window h 0) = (0 : Set (V p)) := by
    have he : window h 0 = fun _ => 0 := by funext x; simp [window]
    rw [he, Set.range_const]; rfl
  simp only [zero_smul,add_zero,zero_add,zw] at c₁ c₂
  have A : 3 ≤ (Set.range (window f k)).ncard := c₁ ▸ h₁
  have B : 3 ≤ (Set.range (window g l)).ncard := c₂ ▸ h₂
  rw [counts]
  have h := cauchy_plane (Set.range (window f k)) (Set.range (window g l))
    (Set.range_nonempty _) (Set.range_nonempty _)
  omega

end SquarePlaneLabels

namespace SquarePlaneLabels
open scoped Pointwise
open SquarePlaneMixedWindows
variable {p : ℕ} [Fact p.Prime]

theorem mixed_indices {u v w : V p} (uv : determinant u v ≠ 0)
    (uw : determinant u w ≠ 0) (vw : determinant v w ≠ 0) :
    ∃ k l : ℕ, (k : ZMod p) ≠ 0 ∧ (l : ZMod p) ≠ 0 ∧ k • u + l • v = w := by
  obtain ⟨⟨i,j⟩,he⟩ := (Finite.surjective_of_injective (columns_inj_of_det uv)) w
  change i • u + j • v = w at he
  refine ⟨i.val,j.val,?_,?_,?_⟩
  · rw [ZMod.natCast_zmod_val]
    intro ez
    apply vw
    rw [← he,ez,zero_smul,zero_add]
    simp [determinant]; ring
  · rw [ZMod.natCast_zmod_val]
    intro ez
    apply uw
    rw [← he,ez,zero_smul,add_zero]
    simp [determinant]; ring
  · simpa only [← Nat.cast_smul_eq_nsmul (ZMod p),ZMod.natCast_zmod_val] using he

theorem chord_intersects (s : V p → G p) (hs : Function.RightInverse s (down p)) (hp : 5 ≤ p)
    (strict : (Set.range s-Set.range s).ncard < (2*p-1)^2)
    (u v w : V p) (uv : determinant u v ≠ 0) (uw : determinant u w ≠ 0)
    (vw : determinant v w ≠ 0) (T U : TriangleData p)
    (ht : Set.range (label s hs u) = T.points) (hu : Set.range (label s hs v) = U.points)
    (hw : (Set.range (label s hs w)).ncard = 3) :
    ∃ c, c ∈ T.chords ∧ c ∈ U.chords := by
  by_contra! disj
  have flat := TriangleData.shared_flat s hs u v T U ht hu (AddMonoidHom.id _)
    (fun z hz hz' => (disj _ hz hz').elim)
  obtain ⟨k,l,hk,hl,he⟩ := mixed_indices uv uw vw
  have n := mixed_full_lower s hs strict u v uv flat k l hk hl hp
  rw [he,hw] at n
  omega

theorem TriangleData.projection_pair (T : TriangleData p) {w : V p} (hw : unsigned w ∈ T.chords) :
    ∃ b d : ZMod p, d ≠ 0 ∧ unsigned d = unsigned (determinant T.a T.b) ∧
      (detMap w) '' T.points = {b,b+d} := by
  obtain ⟨t,z,ht,hz⟩ := T.chord_on hw
  let d := determinant w z
  have hd : d ≠ 0 := by rcases hz with h|h <;> simp [d,h,T.indep]
  refine ⟨detMap w t,d,hd,(unsigned_eq _ _).mpr hz,?_⟩
  rw [ht]
  have zw : detMap w w = 0 := by simp [detMap,determinant,mul_comm]
  simp only [triangle,Set.image_insert_eq,Set.image_singleton,map_add,zw,add_zero,Set.insert_idem]
  rfl

theorem axial_ranges {A : Type*} [AddCommGroup A] (s : V p → G p)
    (hs : Function.RightInverse s (down p)) (u v : V p) (hind : determinant u v ≠ 0)
    (π : V p →+ A) (flat : ∀ x, π (label s hs u (x+v)) = π (label s hs u x)) :
    Set.range (fun i => π (label s hs u (indexPoint u v i 0))) = π '' Set.range (label s hs u) ∧
    Set.range (fun j => π (label s hs v (indexPoint u v 0 j))) = π '' Set.range (label s hs v) := by
  have cy (x : V p) : π (label s hs v (x+u)) = π (label s hs v x) := by
    have e := congrArg π (label_curl s hs u v x)
    rw [map_sub,map_sub,flat,sub_self] at e
    exact sub_eq_zero.mp e.symm
  have onto := Finite.surjective_of_injective (columns_inj_of_det hind)
  constructor
  · ext z
    constructor
    · rintro ⟨i,rfl⟩; exact ⟨_,Set.mem_range_self _,rfl⟩
    · rintro ⟨_,⟨x,rfl⟩,rfl⟩
      obtain ⟨⟨i,j⟩,rfl⟩ := onto x
      refine ⟨i,eq_const_of_shift (fun j => π (label s hs u (indexPoint u v i j))) one_ne_zero ?_ 0 j⟩
      intro z
      have h := index_y u v i z 1
      simp only [one_smul,Nat.cast_one] at h
      rw [← h,flat]
  · ext z
    constructor
    · rintro ⟨j,rfl⟩; exact ⟨_,Set.mem_range_self _,rfl⟩
    · rintro ⟨_,⟨x,rfl⟩,rfl⟩
      obtain ⟨⟨i,j⟩,rfl⟩ := onto x
      refine ⟨j,eq_const_of_shift (fun i => π (label s hs v (indexPoint u v i j))) one_ne_zero ?_ 0 i⟩
      intro z
      have h := index_x u v z j 1
      simp only [one_smul,Nat.cast_one] at h
      rw [← h,cy]

theorem binary_of_range {A I : Type*} [AddCommGroup A] (f : I → A) {b d : A} (hd : d ≠ 0)
    (he : Set.range f = {b,b+d}) : (∀ x, f x = b ∨ f x = b+d) ∧ ∃ x y, f x ≠ f y := by
  constructor
  · intro x
    have hx := Set.mem_range_self (f := f) x
    rwa [he] at hx
  · obtain ⟨x,hx⟩ : b ∈ Set.range f := he ▸ Or.inl rfl
    obtain ⟨y,hy⟩ : b+d ∈ Set.range f := he ▸ Or.inr rfl
    exact ⟨x,y,by rw [hx,hy]; simp [hd]⟩

theorem single_chord_obstruction (s : V p → G p) (hs : Function.RightInverse s (down p)) (hp : 5 ≤ p)
    (u v w : V p) (uv : determinant u v ≠ 0) (uw : determinant u w ≠ 0)
    (vw : determinant v w ≠ 0) (T U W : TriangleData p)
    (ht : Set.range (label s hs u) = T.points) (hu : Set.range (label s hs v) = U.points)
    (hw : Set.range (label s hs w) = W.points) (hthree : W.points.ncard = 3)
    (z : V p) (zt : unsigned z ∈ T.chords) (zu : unsigned z ∈ U.chords)
    (only : ∀ c ∈ T.chords, c ∈ U.chords → c = unsigned z) :
    unsigned (determinant T.a T.b) = unsigned (determinant U.a U.b) ∧ unsigned z ∉ W.chords := by
  let π := detMap z
  have flat := TriangleData.shared_flat s hs u v T U ht hu π (by
    intro a ha hb
    rcases (unsigned_eq _ _).mp (only _ ha hb) with rfl|rfl <;> simp [π,detMap,determinant,mul_comm])
  obtain ⟨b,d,hd,hdt,htp⟩ := T.projection_pair zt
  obtain ⟨c,e,he,heu,hup⟩ := U.projection_pair zu
  obtain ⟨rf,rg⟩ := axial_ranges s hs u v uv π flat
  rw [ht,htp] at rf
  rw [hu,hup] at rg
  obtain ⟨bf,vf⟩ := binary_of_range _ hd rf
  obtain ⟨bg,vg⟩ := binary_of_range _ he rg
  obtain ⟨k,l,hk,hl,hm⟩ := mixed_indices uv uw vw
  obtain ⟨three,four⟩ := mixed_label_bounds s hs u v π flat b c d e k l hk hl bf bg vf vg hd he
  rw [hm] at three four
  have rc : Set.range (fun x => π (label s hs w x)) = π '' W.points := by rw [← hw,← Set.range_comp]; rfl
  rw [rc] at three four
  have bound : (π '' W.points).ncard ≤ 3 := hthree ▸ Set.ncard_image_le
  constructor
  · rw [← hdt,← heu]
    by_contra hne
    have hde : ¬(d=e ∨ d= -e) := fun h => hne ((unsigned_eq _ _).mpr h)
    have bad := four (fun h => hde (Or.inl h)) (fun h => hde (Or.inr h))
    omega
  · intro hz
    obtain ⟨b',d',hd',_,eq⟩ := W.projection_pair hz
    have nz : (2 : ZMod p) ≠ 0 := by
      intro hz
      exact (Nat.not_dvd_of_pos_of_lt (by omega : 0 < 2) (by omega : 2 < p))
        ((ZMod.natCast_eq_zero_iff 2 p).mp hz)
    have htwo : d+d ≠ 0 := by rw [← two_mul]; exact mul_ne_zero nz hd
    have bad := three htwo
    change 3 ≤ ((detMap z) '' W.points).ncard at bad
    rw [eq] at bad
    have diff : b' ≠ b'+d' := by simp [hd']
    rw [Set.ncard_pair diff] at bad
    omega

end SquarePlaneLabels

namespace SquarePlaneLabels
open SquarePlaneChordIncidence
open scoped Pointwise
variable {p : ℕ} [Fact p.Prime]

theorem reverse_label (s : V p → G p) (hs : Function.RightInverse s (down p)) (u x : V p) :
    label s hs (-u) x = label s hs u (-u) - label s hs u (x-u) := by
  apply embed_inj
  rw [map_sub,label_spec,label_spec,label_spec]
  simp only [edge,neg_add_cancel,zero_add,sub_add_cancel,sub_eq_add_neg]
  abel

theorem oriented_axis (s : V p → G p) (hs : Function.RightInverse s (down p))
    (u : V p) (T : TriangleData p) (ht : Set.range (label s hs u) = T.points)
    {w a : V p} {D : ZMod p} (o : Oriented T w D a) :
    ∃ u' t, (u' = u ∨ u' = -u) ∧ ∀ x, label s hs u' x ∈ triangle t w (a+w) := by
  obtain ⟨t,pts|pts⟩ := o.vertices
  · exact ⟨u,t,Or.inl rfl,fun x => pts ▸ ht ▸ Set.mem_range_self x⟩
  · let b := label s hs u (-u)
    refine ⟨-u,b-t-w,Or.inr rfl,?_⟩
    intro x
    have mem : label s hs u (x-u) ∈ triangle t w (-a) := pts ▸ ht ▸ Set.mem_range_self _
    rw [reverse_label]
    change b-label s hs u (x-u) ∈ _
    simp only [triangle,Set.mem_insert_iff,Set.mem_singleton_iff] at mem ⊢
    rcases mem with h|h|h <;> rw [h]
    · exact Or.inr (Or.inl (by abel))
    · exact Or.inl (by abel)
    · exact Or.inr (Or.inr (by abel))

theorem nonzero_double {D : ZMod p} (hp : 5 ≤ p) (hd : D ≠ 0) : D ≠ -D := by
  have hn : (2 : ZMod p) ≠ 0 := fun h =>
    (Nat.not_dvd_of_pos_of_lt (by omega : 0 < 2) (by omega : 2 < p)) ((ZMod.natCast_eq_zero_iff 2 p).mp h)
  intro eq
  apply mul_ne_zero hn hd
  linear_combination eq

theorem nonzero_triple {w : V p} (hp : 5 ≤ p) (hw : w ≠ 0) : 3 • w ≠ 0 := by
  have hn : ((3 : ℕ) : ZMod p) ≠ 0 := fun h =>
    (Nat.not_dvd_of_pos_of_lt (by omega : 0 < 3) (by omega : 3 < p)) ((ZMod.natCast_eq_zero_iff 3 p).mp h)
  rw [← Nat.cast_smul_eq_nsmul (ZMod p)]
  exact smul_ne_zero hn hw

theorem aligned_directions (s : V p → G p) (hs : Function.RightInverse s (down p)) (ho : Odd p)
    (strict : (Set.range s-Set.range s).ncard < (2*p-1)^2) :
    ∃ u v P Q t z : V p, determinant u v ≠ 0 ∧ determinant P Q ≠ 0 ∧
      (∀ x, label s hs u x ∈ triangle t P Q) ∧ (∀ x, label s hs v x ∈ triangle z P Q) := by
  classical
  have hp := strict_prime_ge_five s hs ho strict
  obtain ⟨f,hf,hi⟩ := five_triangles s hs strict
  have tri (i : Fin 5) := realize_triangle s hs strict (f i) (hf i).1 (hf i).2
  choose T ht using tri
  have size (i : Fin 5) : (T i).points.ncard = 3 := (ht i) ▸ (hf i).2
  have meet (i j : Fin 5) (hne : i ≠ j) : ∃ c, c ∈ (T i).chords ∧ c ∈ (T j).chords := by
    have chooseThird : ∀ a b : Fin 5, ∃ k : Fin 5, a ≠ k ∧ b ≠ k := by decide
    obtain ⟨k,hik,hjk⟩ := chooseThird i j
    exact chord_intersects s hs hp strict _ _ _ (hi i j hne) (hi i k hik) (hi j k hjk)
      _ _ (ht i).symm (ht j).symm (hf k).2
  obtain ⟨i,j,k,hij,hik,hjk,c,hci,hcj,hck⟩ :=
    common_in_three (fun i => (T i).chords) (fun i => (T i).chords_size) meet
  obtain ⟨w,rfl⟩ := (T i).chord_repr hci
  have hw := (T i).chord_ne_zero hci
  have extra (i j k : Fin 5) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
      (ci : unsigned w ∈ (T i).chords) (cj : unsigned w ∈ (T j).chords)
      (ck : unsigned w ∈ (T k).chords) :
      ∃ e ∈ (T i).chords, e ∈ (T j).chords ∧ e ≠ unsigned w := by
    by_contra! flat
    have only (e) (a : e ∈ (T i).chords) (b : e ∈ (T j).chords) := flat e a b
    exact (single_chord_obstruction s hs hp _ _ _ (hi i j hij) (hi i k hik) (hi j k hjk)
      _ _ _ (ht i).symm (ht j).symm (ht k).symm (size k) w ci cj only).2 ck
  have eij := extra i j k hij hik hjk hci hcj hck
  have eik := extra i k j hik hij hjk.symm hci hck hcj
  have ejk := extra j k i hjk hij.symm hik.symm hcj hck hci
  let D := determinant (T i).a (T i).b
  have hn : D ≠ 0 := (T i).indep
  obtain ⟨a,ha⟩ := orient (T i) hci D rfl
  obtain ⟨b,hb⟩ := orient (T j) hcj D (common_det_of_two _ _ hci hcj eij).symm
  obtain ⟨c,hc⟩ := orient (T k) hck D (common_det_of_two _ _ hci hck eik).symm
  have diff := nonzero_double hp hn
  have e := cycle_no_three w a b c hw (nonzero_triple hp hw)
    (edge_meet_of_chord diff ha hb eij) (edge_meet_of_chord diff ha hc eik)
    (edge_meet_of_chord diff hb hc ejk)
  have finish (i j : Fin 5) (hij : i ≠ j) (a : V p)
      (oi : Oriented (T i) w D a) (oj : Oriented (T j) w D a) :
      ∃ u v P Q t z : V p, determinant u v ≠ 0 ∧ determinant P Q ≠ 0 ∧
      (∀ x, label s hs u x ∈ triangle t P Q) ∧ (∀ x, label s hs v x ∈ triangle z P Q) := by
    obtain ⟨u,t,hu,ut⟩ := oriented_axis s hs _ _ (ht i).symm oi
    obtain ⟨v,z,hv,vz⟩ := oriented_axis s hs _ _ (ht j).symm oj
    have hdet := hi i j hij
    refine ⟨u,v,w,a+w,t,z,?_,?_,ut,vz⟩
    · rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> intro h <;> apply hdet <;>
        unfold determinant at h ⊢ <;> try simp only [Prod.fst_neg,Prod.snd_neg] at h
      all_goals
        first | linear_combination (norm := ring1) h | linear_combination (norm := ring1) -h
    · change detMap w (a+w) ≠ 0
      rw [map_add,show detMap w a = D from oi.det,show detMap w w = 0 from square_det_self _,add_zero]
      exact hn
  rcases e with rfl|rfl|rfl
  · exact finish i j hij _ ha hb
  · exact finish i k hik _ ha hc
  · exact finish j k hjk _ hb hc

end SquarePlaneLabels

/-! The two remaining inputs are stated as explicit hypotheses. This is a
scratch composition lemma for the original upstream type. -/
namespace SquarePlaneLabels
open SquarePlaneRectification
open scoped Pointwise
open OMA.S_arxiv_2606_27961 (reduce)

theorem target_of_alignment_and_lattice
    (align : ∀ (p : ℕ) [Fact p.Prime], Odd p → ∀ s : V p → G p,
      ∀ hs : Function.RightInverse s (down p),
      (Set.range s-Set.range s).ncard < (2*p-1)^2 →
      ∃ u v P Q t z : V p, determinant u v ≠ 0 ∧ determinant P Q ≠ 0 ∧
        (∀ x, label s hs u x ∈ triangle t P Q) ∧ (∀ x, label s hs v x ∈ triangle z P Q))
    (lattice : ∀ p : ℕ, p.Prime → Odd p → ∀ S : Set (ℤ × ℤ), S.Finite →
      Set.BijOn (reduceLattice p) S Set.univ → (2*p-1)^2 ≤ (S-S).ncard) :
    type_of% @OMA.S_arxiv_2606_27961.main := by
  intro p hp ho
  letI : Fact p.Prime := ⟨hp⟩
  refine ⟨SquarePlaneUpstream.box p hp.two_le, ?_⟩
  rintro _ ⟨T,hT,rfl⟩
  have all (x : V p) : ∃ t ∈ T, reduce p t = x := hT.surjOn (Set.mem_univ x)
  choose s hmem hs using all
  have hT' : T = Set.range s := by
    ext t
    constructor
    · intro ht
      exact ⟨reduce p t,hT.injOn (hmem _) ht (hs _)⟩
    · rintro ⟨x,rfl⟩; exact hmem x
  have hdown : Function.RightInverse s (down p) := fun x => (upstream_down _).symm.trans (hs x)
  rw [hT']
  by_contra! strict
  obtain ⟨u,v,P,Q,t,z,huv,hPQ,hu,hv⟩ := align p ho s hdown strict
  have p5 := strict_prime_ge_five s hdown ho strict
  obtain ⟨S,fin,bij,hcard⟩ := rectified_of_aligned s hdown (by omega) ho u v P Q t z huv hPQ hu hv
  exact strict.not_ge (hcard ▸ lattice p hp ho S fin bij)

end SquarePlaneLabels

namespace SquarePlaneLabels
open scoped Pointwise
open SquarePlaneRectification
open OMA.S_arxiv_2606_27961 (reduce)

/-- The full finite-to-lattice implication in the original finite coordinates. -/
theorem rectify_counterexample (p : ℕ) (hp : p.Prime) (ho : Odd p)
    (T : Set (G p)) (ht : Set.BijOn (reduce p) T Set.univ)
    (strict : (T-T).ncard < (2*p-1)^2) : ∃ S : Set (ℤ × ℤ), S.Finite ∧
      Set.BijOn (reduceLattice p) S Set.univ ∧ (T-T).ncard = (S-S).ncard := by
  letI : Fact p.Prime := ⟨hp⟩
  have all (x : V p) : ∃ t ∈ T, reduce p t = x := ht.surjOn (Set.mem_univ x)
  choose s hmem hs using all
  have eq : T = Set.range s := by
    ext t
    constructor
    · exact fun hm => ⟨reduce p t,ht.injOn (hmem _) hm (hs _)⟩
    · rintro ⟨x,rfl⟩; exact hmem x
  rw [eq] at strict ⊢
  have hd : Function.RightInverse s (down p) := fun x => (upstream_down _).symm.trans (hs x)
  obtain ⟨u,v,P,Q,t,z,h₁,h₂,h₃,h₄⟩ := aligned_directions s hd ho strict
  have p5 := strict_prime_ge_five s hd ho strict
  exact rectified_of_aligned s hd (by omega) ho u v P Q t z h₁ h₂ h₃ h₄

/-- Only the sharp lattice inequality remains as a hypothesis. -/
theorem target_of_lattice
    (lattice : ∀ p : ℕ, p.Prime → Odd p → ∀ S : Set (ℤ × ℤ), S.Finite →
      Set.BijOn (reduceLattice p) S Set.univ → (2*p-1)^2 ≤ (S-S).ncard) :
    type_of% @OMA.S_arxiv_2606_27961.main :=
  target_of_alignment_and_lattice (fun _ _ ho s hs strict => aligned_directions s hs ho strict) lattice

end SquarePlaneLabels

namespace SquarePlaneLattice
open scoped Pointwise
open SquarePlaneLabels (determinant scalar_of_det_zero V)
open SquarePlaneRectification (reduceLattice)

abbrev Lattice := ℤ × ℤ

def lineRow (A : Finset Lattice) (a b : Lattice) :=
  A.filter (fun x => determinant (b-a) (x-a) = 0)

def LineCap (p : ℕ) (A : Finset Lattice) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, a ≠ b → (lineRow A a b).card ≤ p

theorem lineCap_mono {p : ℕ} {A B : Finset Lattice} (h : LineCap p A) (hsub : B ⊆ A) :
    LineCap p B := by
  intro a ha b hb hab
  exact (Finset.card_le_card (Finset.filter_subset_filter _ hsub)).trans
    (h a (hsub ha) b (hsub hb) hab)

theorem reduce_det (p : ℕ) (a b : Lattice) :
    determinant (reduceLattice p a) (reduceLattice p b) = (determinant a b : ℤ) := by
  simp [determinant,reduceLattice]

/-- Any two different points have different residues. Thus their difference
already gives a nonzero direction modulo p, avoiding primitive lattice vectors. -/
theorem lineCap_of_inj {p : ℕ} [Fact p.Prime] (A : Finset Lattice)
    (hinj : Set.InjOn (reduceLattice p) (A : Set Lattice)) : LineCap p A := by
  classical
  intro a ha b hb hab
  let r := reduceLattice p
  let u := r b - r a
  have hne : u ≠ 0 := fun h => hab (hinj hb ha (sub_eq_zero.mp h)).symm
  let line := (Finset.univ : Finset (ZMod p)).image (fun t => r a+t • u)
  have hcard : line.card ≤ p := Finset.card_image_le.trans (by simp [ZMod.card])
  apply le_trans _ hcard
  apply Finset.card_le_card_of_injOn r
  · intro x hx
    have hdet := (Finset.mem_filter.mp hx).2
    have he : determinant u (r x-r a) = 0 := by
      change determinant (reduceLattice p b-reduceLattice p a)
        (reduceLattice p x-reduceLattice p a) = 0
      rw [← map_sub,← map_sub,reduce_det,hdet,Int.cast_zero]
    obtain ⟨t,ht⟩ := scalar_of_det_zero hne he
    exact Finset.mem_image.mpr ⟨t,Finset.mem_univ _,by rw [← ht]; abel⟩
  · exact fun _ hx _ hy he => hinj (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hy).1 he

theorem lattice_of_planar
    (planar : ∀ (p : ℕ) (A : Finset Lattice), 2 ≤ p → A.Nonempty → A.card ≤ p^2 →
      LineCap p A → 4*A.card+1 ≤ (A-A).card+4*p)
    (p : ℕ) (hp : p.Prime) (S : Set Lattice) (hf : S.Finite)
    (hS : Set.BijOn (reduceLattice p) S Set.univ) : (2*p-1)^2 ≤ (S-S).ncard := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  let A := hf.toFinset
  have hA : (A : Set Lattice) = S := hf.coe_toFinset
  have num : A.card = p^2 := by
    have hc := hS.ncard_eq
    simpa [← hA,Set.ncard_univ,Nat.card_eq_fintype_card,Fintype.card_prod,ZMod.card,pow_two] using hc
  have hn : A.Nonempty := Finset.card_pos.mp (num ▸ pow_pos hp.pos 2)
  have h := planar p A hp.two_le hn num.le (lineCap_of_inj A (hA ▸ hS.injOn))
  have diff : ((A-A : Finset Lattice) : Set Lattice) = S-S := by rw [Finset.coe_sub,hA]
  rw [← diff,Set.ncard_coe_finset]
  rw [num] at h
  have hh : 1 ≤ 2*p := by have := hp.two_le; omega
  have e := Nat.sub_add_cancel hh
  nlinarith [congrArg (fun n : ℕ => n^2) e]

end SquarePlaneLattice

namespace SquarePlaneLattice
open scoped Pointwise

noncomputable def row (A : Finset Lattice) (f : Lattice →+ ℝ) (v : ℝ) :=
  A.filter (fun x => f x = v)

noncomputable def deleteRow (A : Finset Lattice) (f : Lattice →+ ℝ) (v : ℝ) :=
  A.filter (fun x => f x ≠ v)

def Supports (A : Finset Lattice) (f : Lattice →+ ℝ) (lo hi : ℝ) : Prop :=
  lo < hi ∧ (∀ x ∈ A, lo ≤ f x ∧ f x ≤ hi) ∧ (row A f lo).Nonempty ∧ (row A f hi).Nonempty

theorem sub_card_swap (X Y : Finset Lattice) : (X-Y).card = (Y-X).card := by
  have he : -(X-Y) = Y-X := by
    ext z
    simp only [Finset.mem_neg',Finset.mem_sub]
    constructor
    · rintro ⟨a,ha,b,hb,h⟩
      exact ⟨b,hb,a,ha,by rw [← neg_sub, h, neg_neg]⟩
    · rintro ⟨a,ha,b,hb,h⟩
      exact ⟨b,hb,a,ha,by rw [← h,neg_sub]⟩
  rw [← he,Finset.card_neg]

theorem row_delete_cost (A : Finset Lattice) (f : Lattice →+ ℝ) (lo hi : ℝ) (sup : Supports A f lo hi) :
    let X := row A f lo
    let Y := row A f hi
    let B := deleteRow A f lo
    (B-B).card+2*(X-Y).card ≤ (A-A).card := by
  intro X Y B
  have hx (x : Lattice) (h : x ∈ X-Y) : f x = lo-hi := by
    obtain ⟨a,ha,b,hb,rfl⟩ := Finset.mem_sub.mp h
    rw [map_sub,(Finset.mem_filter.mp ha).2,(Finset.mem_filter.mp hb).2]
  have hy (x : Lattice) (h : x ∈ Y-X) : f x = hi-lo := by
    obtain ⟨a,ha,b,hb,rfl⟩ := Finset.mem_sub.mp h
    rw [map_sub,(Finset.mem_filter.mp ha).2,(Finset.mem_filter.mp hb).2]
  have mid (x : Lattice) (h : x ∈ B-B) : lo-hi < f x ∧ f x < hi-lo := by
    obtain ⟨a,ha,b,hb,rfl⟩ := Finset.mem_sub.mp h
    obtain ⟨am,an⟩ := Finset.mem_filter.mp ha
    obtain ⟨bm,bn⟩ := Finset.mem_filter.mp hb
    have ab := sup.2.1 a am
    have bb := sup.2.1 b bm
    rw [map_sub]
    have aL := lt_of_le_of_ne ab.1 (Ne.symm an)
    have bL := lt_of_le_of_ne bb.1 (Ne.symm bn)
    constructor <;> linarith [ab.2,bb.2]
  have sep : Disjoint (X-Y) (Y-X) := Finset.disjoint_left.mpr (fun {x} h₁ h₂ => by
    have := hx x h₁; have := hy x h₂; linarith [sup.1])
  have sepB : Disjoint (B-B) ((X-Y) ∪ (Y-X)) := Finset.disjoint_left.mpr (fun {x} h₁ h₂ => by
    have hh := mid x h₁
    rcases Finset.mem_union.mp h₂ with h|h
    · have := hx x h; linarith [hh.1]
    · have := hy x h; linarith [hh.2])
  have sx : X ⊆ A := Finset.filter_subset _ _
  have sy : Y ⊆ A := Finset.filter_subset _ _
  have sb : B ⊆ A := Finset.filter_subset _ _
  have sub : (B-B) ∪ ((X-Y) ∪ (Y-X)) ⊆ A-A :=
    Finset.union_subset (Finset.sub_subset_sub sb sb)
      (Finset.union_subset (Finset.sub_subset_sub sx sy) (Finset.sub_subset_sub sy sx))
  have le := Finset.card_le_card sub
  rw [Finset.card_union_of_disjoint sepB,Finset.card_union_of_disjoint sep,sub_card_swap Y X] at le
  omega

theorem supports_flip {A : Finset Lattice} {f : Lattice →+ ℝ} {lo hi : ℝ}
    (h : Supports A f lo hi) : Supports A (-f) (-hi) (-lo) := by
  refine ⟨neg_lt_neg h.1, fun x hx => ⟨neg_le_neg (h.2.1 x hx).2,neg_le_neg (h.2.1 x hx).1⟩,?_,?_⟩
  · simpa [row] using h.2.2.2
  · simpa [row] using h.2.2.1

theorem row_card_sub (X Y : Finset Lattice) (hx : X.Nonempty) (hy : Y.Nonempty) :
    X.card + Y.card - 1 ≤ (X-Y).card := by
  have h := cauchy_davenport_of_isAddTorsionFree hx (s := X) (t := -Y) (by simpa using hy)
  simpa [sub_eq_add_neg] using h

def PlanarBound (p : ℕ) (A : Finset Lattice) : Prop := 4*A.card+1 ≤ (A-A).card+4*p

theorem stall_cost {p : ℕ} {A : Finset Lattice} (bad : ¬PlanarBound p A)
    (smaller : ∀ B ⊆ A, B.Nonempty → B.card < A.card → PlanarBound p B)
    (f : Lattice →+ ℝ) (lo hi : ℝ) (h : Supports A f lo hi) :
    (row A f lo-row A f hi).card < 2*(row A f lo).card := by
  let B := deleteRow A f lo
  let X := row A f lo
  have split : X.card+B.card = A.card := Finset.card_filter_add_card_filter_not _
  have pos := Finset.card_pos.mpr h.2.2.1
  have hb : B.Nonempty := by
    obtain ⟨a,ha⟩ := h.2.2.2
    obtain ⟨am,ae⟩ := Finset.mem_filter.mp ha
    exact ⟨a,Finset.mem_filter.mpr ⟨am,ae ▸ h.1.ne.symm⟩⟩
  have hB := smaller B (Finset.filter_subset _ _) hb (by change 0 < X.card at pos; omega)
  have cost := row_delete_cost A f lo hi h
  change (B-B).card+2*(X-row A f hi).card ≤ _ at cost
  change ¬4*A.card+1 ≤ (A-A).card+4*p at bad
  change 4*B.card+1 ≤ (B-B).card+4*p at hB
  change (X-row A f hi).card < 2*X.card
  omega

/-- Every opposite pair of support rows of a minimal obstruction has equal
size m and a difference set of exactly 2m−1 points. -/
theorem stalled_rows {p : ℕ} {A : Finset Lattice} (bad : ¬PlanarBound p A)
    (smaller : ∀ B ⊆ A, B.Nonempty → B.card < A.card → PlanarBound p B)
    (f : Lattice →+ ℝ) (lo hi : ℝ) (h : Supports A f lo hi) :
    (row A f lo).card = (row A f hi).card ∧
    (row A f lo-row A f hi).card = 2*(row A f lo).card-1 := by
  have h₁ := stall_cost bad smaller f lo hi h
  have h₂ := stall_cost bad smaller (-f) (-hi) (-lo) (supports_flip h)
  have r₁ : row A (-f) (-hi) = row A f hi := by simp [row]
  have r₂ : row A (-f) (-lo) = row A f lo := by simp [row]
  rw [r₁,r₂,sub_card_swap (row A f hi) (row A f lo)] at h₂
  have low := row_card_sub _ _ h.2.2.1 h.2.2.2
  omega

end SquarePlaneLattice

namespace SquarePlaneLattice
open scoped Pointwise

variable {G : Type*} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]

/-- The first row followed by the last column is a monotone path whose
image exhausts the sumset in the critical cardinality case. -/
theorem initial_row (X Y : Finset G) (hx : X.Nonempty) (hy : Y.Nonempty)
    (critical : (X+Y).card = X.card+Y.card-1) :
    X.image (fun x => x+Y.min' hy) =
      (X+Y).filter (fun z => z ≤ X.max' hx + Y.min' hy) := by
  classical
  let a := X.max' hx
  let b := Y.min' hy
  let L := X.image (fun x => x+b)
  let R := Y.image (fun y => a+y)
  have hL (z) (h : z ∈ L) : z ≤ a+b := by
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp h
    exact add_le_add_left (X.le_max' _ hx) _
  have hR (z) (h : z ∈ R) : a+b ≤ z := by
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp h
    exact add_le_add_right (Y.min'_le _ hy) _
  have ha : a ∈ X := X.max'_mem hx
  have hb : b ∈ Y := Y.min'_mem hy
  have atL : a+b ∈ L := Finset.mem_image.mpr ⟨a,ha,rfl⟩
  have atR : a+b ∈ R := Finset.mem_image.mpr ⟨b,hb,rfl⟩
  have meet : L ∩ R = {a+b} := by
    ext z
    constructor
    · intro hz
      obtain ⟨l,r⟩ := Finset.mem_inter.mp hz
      exact Finset.mem_singleton.mpr (le_antisymm (hL _ l) (hR _ r))
    · intro hz
      have eq := Finset.mem_singleton.mp hz
      exact eq ▸ Finset.mem_inter.mpr ⟨atL,atR⟩
  have hcl : L.card = X.card := Finset.card_image_of_injective _ (fun _ _ => add_right_cancel)
  have hcr : R.card = Y.card := Finset.card_image_of_injective _ (fun _ _ => add_left_cancel)
  have reach : L ∪ R = X+Y := by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      rcases Finset.mem_union.mp hz with hl|hr
      · obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hl
        exact Finset.add_mem_add hx hb
      · obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hr
        exact Finset.add_mem_add ha hy
    · have n := Finset.card_union_add_card_inter L R
      rw [meet,Finset.card_singleton,hcl,hcr] at n
      omega
  change L = (X+Y).filter (fun z => z ≤ a+b)
  rw [← reach]
  ext z
  constructor
  · exact fun h => Finset.mem_filter.mpr ⟨Finset.mem_union_left _ h,hL _ h⟩
  · intro h
    obtain ⟨hu,hle⟩ := Finset.mem_filter.mp h
    rcases Finset.mem_union.mp hu with hl|hr
    · exact hl
    · exact (le_antisymm hle (hR _ hr)) ▸ atL

theorem critical_equal_rows (X Y : Finset G) (hx : X.Nonempty) (hy : Y.Nonempty)
    (same : X.card = Y.card) (critical : (X+Y).card = X.card+Y.card-1) :
    ∃ c : G, X = Y.image (fun y => c+y) := by
  classical
  have left := initial_row X Y hx hy critical
  have right := initial_row Y X hy hx (by simpa [add_comm] using critical)
  rw [add_comm Y X] at right
  let L := X.image (fun x => x+Y.min' hy)
  let R := Y.image (fun y => y+X.min' hx)
  have lc : L.card = X.card := Finset.card_image_of_injective _ (fun _ _ => add_right_cancel)
  have rc : R.card = Y.card := Finset.card_image_of_injective _ (fun _ _ => add_right_cancel)
  have eq : L = R := by
    rcases le_total (X.max' hx + Y.min' hy) (Y.max' hy + X.min' hx) with h|h
    · apply Finset.eq_of_subset_of_card_le _ (by omega)
      change X.image _ ⊆ Y.image _
      rw [left,right]
      intro z hz
      obtain ⟨hm,hl⟩ := Finset.mem_filter.mp hz
      exact Finset.mem_filter.mpr ⟨hm,hl.trans h⟩
    · symm
      apply Finset.eq_of_subset_of_card_le _ (by omega)
      change Y.image _ ⊆ X.image _
      rw [left,right]
      intro z hz
      obtain ⟨hm,hl⟩ := Finset.mem_filter.mp hz
      exact Finset.mem_filter.mpr ⟨hm,hl.trans h⟩
  use X.min' hx-Y.min' hy
  ext x
  constructor
  · intro hx'
    have hl : x+Y.min' hy ∈ L := Finset.mem_image.mpr ⟨x,hx',rfl⟩
    obtain ⟨y,hy',he⟩ := Finset.mem_image.mp (eq ▸ hl : x+Y.min' hy ∈ R)
    exact Finset.mem_image.mpr ⟨y,hy',by linear_combination (norm := abel) he⟩
  · intro he
    obtain ⟨y,hy',rfl⟩ := Finset.mem_image.mp he
    have hr : y+X.min' hx ∈ R := Finset.mem_image.mpr ⟨y,hy',rfl⟩
    obtain ⟨x,hx',he⟩ := Finset.mem_image.mp (eq ▸ hr : y+X.min' hx ∈ L)
    have q : x = X.min' hx-Y.min' hy+y := by linear_combination (norm := abel) he
    exact q ▸ hx'

/-- Critical opposite support rows in the lattice reflect onto one another. -/
theorem reflect_rows (X Y : Finset Lattice) (hx : X.Nonempty) (hy : Y.Nonempty)
    (same : X.card = Y.card) (critical : (X-Y).card = 2*X.card-1) :
    ∃ c : Lattice, X = Y.image (fun y => c-y) := by
  let U : Finset (Lex Lattice) := X
  let V : Finset (Lex Lattice) := -Y
  have hV : V.Nonempty := by change (-Y).Nonempty; simpa using hy
  have hvCard : V.card = Y.card := Finset.card_neg _
  have hcrit : (U+V).card = U.card+V.card-1 := by
    change (X+ -Y).card = X.card + V.card-1
    rw [← sub_eq_add_neg,hvCard,← same,← two_mul,critical]
  obtain ⟨c,h⟩ := critical_equal_rows U V hx hV (same.trans hvCard.symm) hcrit
  use ofLex c
  change X = (-Y).image (fun y : Lattice => ofLex c+y) at h
  rw [h,← Finset.image_neg_eq_neg,Finset.image_image]
  simp [Function.comp_def,sub_eq_add_neg]

end SquarePlaneLattice

namespace SquarePlaneLattice
open Filter Topology

noncomputable def bottom (A : Finset Lattice) (f : Lattice →+ ℝ) :=
  A.filter (fun x => ∀ y ∈ A, f x ≤ f y)

noncomputable def topFace (A : Finset Lattice) (f : Lattice →+ ℝ) := bottom A (-f)

theorem top_mem {A : Finset Lattice} {f : Lattice →+ ℝ} {x : Lattice} :
    x ∈ topFace A f ↔ x ∈ A ∧ ∀ y ∈ A, f y ≤ f x := by simp only [topFace,bottom,Finset.mem_filter,AddMonoidHom.neg_apply,neg_le_neg_iff]

theorem bot_mem {A : Finset Lattice} {f : Lattice →+ ℝ} {x : Lattice} :
    x ∈ bottom A f ↔ x ∈ A ∧ ∀ y ∈ A, f x ≤ f y := Finset.mem_filter

theorem bottom_nonempty {A : Finset Lattice} (h : A.Nonempty) (f : Lattice →+ ℝ) :
    (bottom A f).Nonempty := by
  obtain ⟨x,hx,hmin⟩ := Finset.exists_min_image A f h
  exact ⟨x,bot_mem.mpr ⟨hx,hmin⟩⟩

def mirror (c : Lattice) (X : Finset Lattice) := X.image (fun x => c-x)

theorem mirror_mem {c x : Lattice} {X : Finset Lattice} : x ∈ mirror c X ↔ c-x ∈ X := by
  constructor
  · rintro h
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp h
    simpa using hy
  · intro h
    exact Finset.mem_image.mpr ⟨_,h,sub_sub_cancel _ _⟩

theorem mirror_center_unique {c d : Lattice} {X : Finset Lattice} (hx : X.Nonempty)
    (eq : mirror c X = mirror d X) : c = d := by
  have total (q : Lattice) : (∑ z ∈ mirror q X, z) = X.card • q - ∑ x ∈ X, x := by
    rw [mirror,Finset.sum_image,Finset.sum_sub_distrib,Finset.sum_const]
    exact fun _ _ _ _ => sub_right_inj.mp
  have he := congrArg (fun s : Finset Lattice => ∑ z ∈ s, z) eq
  rw [total,total,sub_left_inj] at he
  exact nsmul_right_injective (Finset.card_pos.mpr hx).ne' he

theorem support_reflection {p : ℕ} {A : Finset Lattice} (hA : A.Nonempty)
    (bad : ¬PlanarBound p A) (smaller : ∀ B ⊆ A, B.Nonempty → B.card < A.card → PlanarBound p B)
    (f : Lattice →+ ℝ) (varies : ∃ x ∈ A, ∃ y ∈ A, f x ≠ f y) :
    ∃ c, bottom A f = mirror c (topFace A f) := by
  obtain ⟨x,hx⟩ := bottom_nonempty hA f
  obtain ⟨y,hy⟩ := bottom_nonempty hA (-f)
  have hmin := bot_mem.mp hx
  have hmax := top_mem.mp (show y ∈ topFace A f from hy)
  have lt : f x < f y := by
    obtain ⟨i,hi,j,hj,hne⟩ := varies
    have il := hmin.2 i hi; have ih := hmax.2 i hi
    have jl := hmin.2 j hj; have jh := hmax.2 j hj
    rcases lt_or_gt_of_ne hne with e|e <;> linarith
  have s : Supports A f (f x) (f y) := ⟨lt,fun z hz => ⟨hmin.2 z hz,hmax.2 z hz⟩,
    ⟨x,Finset.mem_filter.mpr ⟨hmin.1,rfl⟩⟩,⟨y,Finset.mem_filter.mpr ⟨hmax.1,rfl⟩⟩⟩
  obtain ⟨cnt,crit⟩ := stalled_rows bad smaller f _ _ s
  obtain ⟨c,hc⟩ := reflect_rows _ _ s.2.2.1 s.2.2.2 cnt crit
  have bl : bottom A f = row A f (f x) := by
    ext z
    rw [bot_mem,row,Finset.mem_filter]
    constructor
    · exact fun ⟨hz,m⟩ => ⟨hz,le_antisymm (m x hmin.1) (hmin.2 z hz)⟩
    · exact fun ⟨hz,e⟩ => ⟨hz,fun v hv => e ▸ hmin.2 v hv⟩
  have tu : topFace A f = row A f (f y) := by
    ext z
    rw [top_mem,row,Finset.mem_filter]
    constructor
    · exact fun ⟨hz,m⟩ => ⟨hz,le_antisymm (hmax.2 z hz) (m y hmax.1)⟩
    · exact fun ⟨hz,e⟩ => ⟨hz,fun v hv => e ▸ hmax.2 v hv⟩
  exact ⟨c,by rw [bl,tu]; exact hc⟩

/-- Refining a pair of opposite support faces preserves its reflection center. -/
theorem refined_reflection (A : Finset Lattice) (hA : A.Nonempty)
    (f g : Lattice →+ ℝ) (c : Lattice) (symm : bottom A f = mirror c (topFace A f))
    (bl : bottom A g ⊆ bottom A f) (tu : topFace A g ⊆ topFace A f) :
    bottom A g = mirror c (topFace A g) := by
  obtain ⟨l,hl⟩ := bottom_nonempty hA g
  obtain ⟨u,hu⟩ := bottom_nonempty hA (-g)
  have hu' : u ∈ topFace A g := hu
  have down (x) (hx : x ∈ topFace A f) : c-x ∈ bottom A f := by
    rw [symm,mirror_mem,sub_sub_cancel]; exact hx
  have up (x) (hx : x ∈ bottom A f) : c-x ∈ topFace A f := mirror_mem.mp (symm ▸ hx)
  have cen : g l+g u = g c := by
    have L := (bot_mem.mp hl).2 _ (bot_mem.mp (down _ (tu hu'))).1
    have U := (top_mem.mp hu').2 _ (top_mem.mp (up _ (bl hl))).1
    rw [map_sub] at L U
    linarith
  ext x
  rw [mirror_mem]
  constructor
  · intro hx
    have xm := (top_mem.mp (up _ (bl hx))).1
    have same := le_antisymm ((bot_mem.mp hx).2 _ (bot_mem.mp hl).1) ((bot_mem.mp hl).2 _ (bot_mem.mp hx).1)
    refine top_mem.mpr ⟨xm,fun z hz => ?_⟩
    rw [map_sub,same]
    linarith [(top_mem.mp hu').2 z hz]
  · intro hx
    have xm := (bot_mem.mp (down _ (tu hx))).1
    rw [sub_sub_cancel] at xm
    have same := le_antisymm ((top_mem.mp hu').2 _ (top_mem.mp hx).1) ((top_mem.mp hx).2 _ (top_mem.mp hu').1)
    rw [map_sub] at same
    exact bot_mem.mpr ⟨xm,fun z hz => by linarith [(bot_mem.mp hl).2 z hz]⟩

theorem bottom_stable {A : Finset Lattice} {F : ℝ → Lattice →+ ℝ}
    (cont : ∀ x, Continuous (fun t => F t x)) (t : ℝ) :
    ∀ᶠ r in 𝓝 t, bottom A (F r) ⊆ bottom A (F t) := by
  have each (x : Lattice) (_hx : x ∈ A) : ∀ᶠ r in 𝓝 t, x ∈ bottom A (F r) → x ∈ bottom A (F t) := by
    by_cases h : x ∈ bottom A (F t)
    · exact Eventually.of_forall (fun _ _ => h)
    rw [bot_mem,not_and] at h
    obtain ⟨y,hy,less⟩ := by simpa only [not_forall,Classical.not_imp,not_le] using h _hx
    filter_upwards [((cont y).continuousAt.eventually_lt (cont x).continuousAt less)] with r hr hm
    exact (hr.not_ge ((bot_mem.mp hm).2 y hy)).elim
  filter_upwards [(A.eventually_all).mpr each] with r hr x hx
  exact hr x (bot_mem.mp hx).1 hx

theorem shared_center_along {A : Finset Lattice} (hA : A.Nonempty) (F : ℝ → Lattice →+ ℝ)
    (cont : ∀ x, Continuous (fun t => F t x)) (center : ℝ → Lattice)
    (symm : ∀ t, bottom A (F t) = mirror (center t) (topFace A (F t))) :
    ∀ t, center t = center 0 := by
  have localConst : IsLocallyConstant center := by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro t
    filter_upwards [bottom_stable cont t,
      bottom_stable (A := A) (F := fun r => -F r) (fun x => (cont x).neg) t] with r bot top
    exact mirror_center_unique (bottom_nonempty hA (-(F r)))
      ((symm r).symm.trans (refined_reflection A hA _ _ _ (symm t) bot top))
  exact fun t => localConst.apply_eq_of_preconnectedSpace t 0

end SquarePlaneLattice

namespace SquarePlaneLattice
open scoped Pointwise
open SquarePlaneLabels (determinant)

noncomputable def normal (a b : ℝ) : Lattice →+ ℝ where
  toFun x := a*x.1 + b*x.2
  map_zero' := by simp
  map_add' x y := by simp; ring

theorem obstruction_spans {p : ℕ} (hp : 2 ≤ p) (A : Finset Lattice) (hA : A.Nonempty)
    (cap : LineCap p A) (bad : ¬PlanarBound p A) :
    ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A, determinant (y-x) (z-x) ≠ 0 := by
  obtain ⟨x,hx⟩ := hA
  have pos : 0 < (A-A).card := Finset.card_pos.mpr ⟨x-x,Finset.sub_mem_sub hx hx⟩
  have large : p < A.card := by unfold PlanarBound at bad; omega
  obtain ⟨a,b,ha,hb,hab⟩ := Finset.one_lt_card_iff.mp (by omega : 1 < A.card)
  have hc := cap a ha b hb hab
  by_contra! trivialPlane
  have he : lineRow A a b = A := Finset.filter_eq_self.mpr (fun z hz => trivialPlane a ha b hb z hz)
  rw [he] at hc
  omega

theorem normal_varies {A : Finset Lattice}
    (span : ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A, determinant (y-x) (z-x) ≠ 0)
    (a b : ℝ) (nz : a ≠ 0 ∨ b ≠ 0) : ∃ x ∈ A, ∃ y ∈ A, normal a b x ≠ normal a b y := by
  obtain ⟨x,hx,y,hy,z,hz,hd⟩ := span
  by_contra! equal
  have dy := equal y hy x hx
  have dz := equal z hz x hx
  let u := y-x
  let v := z-x
  have detne : ((determinant u v : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hd
  have du : a*(u.1 : ℝ)+b*u.2 = 0 := by simp [u,normal] at dy ⊢; linear_combination dy
  have dv : a*(v.1 : ℝ)+b*v.2 = 0 := by simp [v,normal] at dz ⊢; linear_combination dz
  rcases nz with ha|hb
  · apply mul_ne_zero ha detne
    unfold determinant
    push_cast
    linear_combination v.2*du-u.2*dv
  · apply mul_ne_zero hb detne
    unfold determinant
    push_cast
    linear_combination u.1*dv-v.1*du

noncomputable def boundaryRows (A : Finset Lattice) : Finset Lattice := by
  classical
  exact A.filter (fun x => ∃ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) ∧ x ∈ topFace A (normal a b))

theorem boundary_mem {A : Finset Lattice} {x : Lattice} : x ∈ boundaryRows A ↔
    ∃ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) ∧ x ∈ topFace A (normal a b) := by
  classical
  rw [boundaryRows,Finset.mem_filter]
  exact ⟨And.right,fun h => ⟨by obtain ⟨a,b,_,hx⟩ := h; exact (top_mem.mp hx).1,h⟩⟩

theorem normal_neg (a b : ℝ) : normal (-a) (-b) = -normal a b := by
  ext x
  simp [normal]
  ring

/-- A single center works for every support normal of a cardinality-minimal
failure. The conclusion concerns the exposed boundary points of A. -/
theorem symmetric_boundary {p : ℕ} (hp : 2 ≤ p) (A : Finset Lattice) (hA : A.Nonempty)
    (cap : LineCap p A) (bad : ¬PlanarBound p A)
    (small : ∀ B ⊆ A, B.Nonempty → B.card < A.card → PlanarBound p B) :
    ∃ c : Lattice, (∀ a b : ℝ, a ≠ 0 ∨ b ≠ 0 →
      bottom A (normal a b) = mirror c (topFace A (normal a b))) ∧
      boundaryRows A = mirror c (boundaryRows A) := by
  classical
  have vary := normal_varies (obstruction_spans hp A hA cap bad)
  let chooseC (a b : ℝ) := if h : ∃ c, bottom A (normal a b) = mirror c (topFace A (normal a b))
    then h.choose else (0 : Lattice)
  have spec (a b : ℝ) (hn : a ≠ 0 ∨ b ≠ 0) :
      bottom A (normal a b) = mirror (chooseC a b) (topFace A (normal a b)) := by
    have h := support_reflection hA bad small (normal a b) (vary a b hn)
    simpa only [chooseC,dif_pos h] using h.choose_spec
  have h₁ (a : ℝ) (ha : a ≠ 0) (b : ℝ) : chooseC a b = chooseC a 0 :=
    shared_center_along hA (fun t => normal a t) (fun x => by simp only [normal,AddMonoidHom.coe_mk,ZeroHom.coe_mk]; fun_prop)
      (chooseC a) (fun t => spec _ _ (Or.inl ha)) b
  have h₂ (b : ℝ) (hb : b ≠ 0) (a : ℝ) : chooseC a b = chooseC 0 b :=
    shared_center_along hA (fun t => normal t b) (fun x => by simp only [normal,AddMonoidHom.coe_mk,ZeroHom.coe_mk]; fun_prop)
      (fun t => chooseC t b) (fun t => spec _ _ (Or.inr hb)) a
  let c := chooseC 1 0
  have cst (a b : ℝ) (hn : a ≠ 0 ∨ b ≠ 0) : chooseC a b = c := by
    rcases hn with ha|hb
    · exact (h₁ a ha b).trans ((h₁ a ha 1).symm.trans ((h₂ 1 one_ne_zero a).trans
        ((h₂ 1 one_ne_zero 1).symm.trans (h₁ 1 one_ne_zero 1))))
    · exact (h₂ b hb a).trans ((h₂ b hb 1).symm.trans (h₁ 1 one_ne_zero b))
  have refl (a b : ℝ) (hn : a ≠ 0 ∨ b ≠ 0) :
      bottom A (normal a b) = mirror c (topFace A (normal a b)) := cst a b hn ▸ spec a b hn
  refine ⟨c,refl,?_⟩
  have preserve (x : Lattice) (hx : x ∈ boundaryRows A) : c-x ∈ boundaryRows A := by
    obtain ⟨a,b,hn,hx⟩ := boundary_mem.mp hx
    apply boundary_mem.mpr
    refine ⟨-a,-b,by simpa using hn,?_⟩
    rw [topFace,normal_neg,neg_neg,refl _ _ hn,mirror_mem,sub_sub_cancel]
    exact hx
  ext x
  rw [mirror_mem]
  exact ⟨preserve x,fun h => by simpa using preserve (c-x) h⟩

end SquarePlaneLattice

/-! Uniqueness of unordered transverse boundary decompositions for a
centrally symmetric planar convex polygon, using only supporting inequalities.
Normals of each pair are ordered by positive determinant. -/

namespace SquarePlaneBoundary
abbrev Pt := ℝ × ℝ

def det (a b : Pt) : ℝ := a.1*b.2-a.2*b.1
def dot (a b : Pt) : ℝ := a.1*b.1+a.2*b.2

theorem dot_sub (n a b : Pt) : dot n (a-b) = dot n a-dot n b := by simp [dot]; ring

theorem dot_add (n a b : Pt) : dot n (a+b) = dot n a+dot n b := by simp [dot]; ring

theorem det_sub (n a b : Pt) : det n (a-b) = det n a-det n b := by simp [det]; ring

theorem bracket (n m v h : Pt) :
    dot m h * dot n v - dot n h * dot m v = det n m * det v h := by
  unfold det dot
  ring

theorem ordered_normal_height (n m v h : Pt) (hnm : 0 < det n m)
    (hn : 0 < dot n v) (hm : 0 < dot m v)
    (hx : dot n h ≤ 0) (hy : 0 ≤ dot m h) : 0 ≤ det v h := by
  apply nonneg_of_mul_nonneg_right (a := det n m) _ hnm
  rw [← bracket]
  exact sub_nonneg.mpr ((mul_nonpos_of_nonpos_of_nonneg hx hm.le).trans (mul_nonneg hy hn.le))

/-- If a+b and x+y are equal boundary sums, a,b,x,y lie on exposed edges,
and both pairs have independent supporting normals, ordering by the normal
determinant makes the summands identical. Positivity against v is established
below from central symmetry and strict interior of the transverse edges. -/
theorem unique_ordered (a b x y v n m r s : Pt) (total : a+b=x+y)
    (nm : 0 < det n m) (rs : 0 < det r s)
    (nv : 0 < dot n v) (mv : 0 < dot m v) (rv : 0 < dot r v) (sv : 0 < dot s v)
    (nx : dot n x ≤ dot n a) (my : dot m y ≤ dot m b)
    (ra : dot r a ≤ dot r x) (sb : dot s b ≤ dot s y) : a=x ∧ b=y := by
  have rel : x-a=b-y := by linear_combination (norm := abel) -total
  have rel' : a-x=y-b := by linear_combination (norm := abel) total
  have hn : dot n (x-a) ≤ 0 := by rw [dot_sub]; linarith
  have hm : 0 ≤ dot m (x-a) := by rw [rel,dot_sub]; linarith
  have hr : dot r (a-x) ≤ 0 := by rw [dot_sub]; linarith
  have hs : 0 ≤ dot s (a-x) := by rw [rel',dot_sub]; linarith
  have h₁ := ordered_normal_height _ _ _ _ nm nv mv hn hm
  have h₂ := ordered_normal_height _ _ _ _ rs rv sv hr hs
  rw [det_sub] at h₁ h₂
  have hzero : det v (x-a)=0 := by rw [det_sub]; linarith
  have hnonzero : v ≠ 0 := by intro e; simp [e,dot] at nv
  have parallel : ∃ t : ℝ, x-a = t • v := by
    let w := x-a
    change det v w = 0 at hzero
    unfold det at hzero
    by_cases hz : v.1 = 0
    · have vy : v.2 ≠ 0 := fun h => hnonzero (Prod.ext hz h)
      have wx : w.1 = 0 := by
        rw [hz,zero_mul,zero_sub,neg_eq_zero] at hzero
        exact (mul_eq_zero.mp hzero).resolve_left vy
      exact ⟨w.2/v.2,Prod.ext (by change w.1 = (w.2/v.2)*v.1; simp [hz,wx]) (div_mul_cancel₀ _ vy).symm⟩
    · refine ⟨w.1/v.1, Prod.ext (div_mul_cancel₀ _ hz).symm ?_⟩
      change w.2 = w.1/v.1*v.2
      field_simp
      linear_combination hzero
  obtain ⟨t,he⟩ := parallel
  have scale (q : Pt) : dot q (x-a) = t * dot q v := by rw [he]; simp [dot]; ring
  rw [scale] at hn hm
  have ht := nonpos_of_mul_nonpos_left hn nv
  have ht' := nonneg_of_mul_nonneg_left hm mv
  have xa : x=a := sub_eq_zero.mp (by simpa [le_antisymm ht ht'] using he)
  exact ⟨xa.symm,add_left_cancel (xa ▸ total)⟩

def lerp (a b : Pt) (t : ℝ) : Pt := (1-t) • a + t • b

theorem dot_lerp (n a b : Pt) (t : ℝ) : dot n (lerp a b t) =
    (1-t)*dot n a+t*dot n b := by simp [dot,lerp]; ring

/-- If a is supported by n, b lies strictly inside an edge of a different
direction, and the reflected endpoints satisfy the same bound as a, then
the displacement a+b−c has strictly positive normal component. -/
theorem transverse_positive (n a l r c : Pt) (t : ℝ) (ht : 0<t) (ht' : t<1)
    (hl : dot n (c-l) ≤ dot n a) (hr : dot n (c-r) ≤ dot n a)
    (sep : dot n l ≠ dot n r) : 0 < dot n (a+lerp l r t-c) := by
  rw [dot_sub,dot_add,dot_lerp]
  rw [dot_sub] at hl hr
  rcases lt_or_gt_of_ne sep with h|h
  · nlinarith [mul_pos ht (sub_pos.mpr h)]
  · nlinarith [mul_pos (sub_pos.mpr ht') (sub_pos.mpr h)]

end SquarePlaneBoundary

namespace SquarePlaneBoundary
open scoped Pointwise
abbrev Edge := Pt × Pt

/-- Consecutive samples on a supporting line, sorted by a fixed generic
projection. Collinear subdivisions are included. -/
structure Supported (D : Finset Pt) (w : Pt) (e : Edge) (n : Pt) : Prop where
  left_mem : e.1 ∈ D
  right_mem : e.2 ∈ D
  increasing : dot w e.1 < dot w e.2
  normal_ne : n ≠ 0
  level : dot n e.2 = dot n e.1
  support : ∀ z ∈ D, dot n z ≤ dot n e.1
  consecutive : ∀ z ∈ D, dot n z = dot n e.1 → ¬ (dot w e.1 < dot w z ∧ dot w z < dot w e.2)

theorem lerp_height {n a b : Pt} {t : ℝ} (same : dot n b = dot n a) :
    dot n (lerp a b t) = dot n a := by rw [dot_lerp,same]; ring

theorem lerp_above {w a b : Pt} {t : ℝ} (order : dot w a < dot w b) (ht : 0 < t) :
    dot w a < dot w (lerp a b t) := by rw [dot_lerp]; nlinarith [mul_pos ht (sub_pos.mpr order)]

theorem lerp_below {w a b : Pt} {t : ℝ} (order : dot w a < dot w b) (ht : t < 1) :
    dot w (lerp a b t) < dot w b := by rw [dot_lerp]; nlinarith [mul_pos (sub_pos.mpr ht) (sub_pos.mpr order)]

theorem lerp_support {n a b : Pt} {H t : ℝ} (ha : dot n a ≤ H) (hb : dot n b ≤ H)
    (ht : 0 ≤ t) (ht' : t ≤ 1) : dot n (lerp a b t) ≤ H := by
  rw [dot_lerp]
  nlinarith [mul_nonneg (sub_nonneg.mpr ht') (sub_nonneg.mpr ha),mul_nonneg ht (sub_nonneg.mpr hb)]

theorem lerp_support_eq {n a b : Pt} {H t : ℝ} (ha : dot n a ≤ H) (hb : dot n b ≤ H)
    (ht : 0 < t) (ht' : t < 1) (he : dot n (lerp a b t) = H) :
    dot n a = H ∧ dot n b = H := by
  rw [dot_lerp] at he
  constructor
  · apply ha.eq_of_not_lt
    intro h
    nlinarith [mul_pos (sub_pos.mpr ht') (sub_pos.mpr h),mul_nonneg ht.le (sub_nonneg.mpr hb)]
  · apply hb.eq_of_not_lt
    intro h
    nlinarith [mul_nonneg (sub_nonneg.mpr ht'.le) (sub_nonneg.mpr ha),mul_pos ht (sub_pos.mpr h)]

theorem elementary_unique {D : Finset Pt} {w n r : Pt} {e f : Edge}
    (ew : Set.InjOn (dot w) (D : Set Pt)) (he : Supported D w e n) (hf : Supported D w f r)
    {t u : ℝ} (ht : 0<t) (ht' : t<1) (hu : 0<u) (hu' : u<1)
    (eq : lerp e.1 e.2 t = lerp f.1 f.2 u) : e=f := by
  have ef := lerp_support_eq (he.support _ hf.left_mem) (he.support _ hf.right_mem) hu hu'
    (eq ▸ lerp_height (t:=t) he.level)
  have fe := lerp_support_eq (hf.support _ he.left_mem) (hf.support _ he.right_mem) ht ht'
    (eq.symm ▸ lerp_height (t:=u) hf.level)
  have l₁ := lerp_above he.increasing ht
  have h₁ := lerp_below he.increasing ht'
  have l₂ := lerp_above hf.increasing hu
  have h₂ := lerp_below hf.increasing hu'
  rw [eq] at l₁ h₁
  apply Prod.ext
  · apply ew he.left_mem hf.left_mem
    apply le_antisymm <;> apply le_of_not_gt <;> intro bad
    · exact hf.consecutive _ he.left_mem fe.1 ⟨bad,l₁.trans h₂⟩
    · exact he.consecutive _ hf.left_mem ef.1 ⟨bad,l₂.trans h₁⟩
  · apply ew he.right_mem hf.right_mem
    apply le_antisymm <;> apply le_of_not_gt <;> intro bad
    · exact he.consecutive _ hf.right_mem ef.2 ⟨l₁.trans h₂,bad⟩
    · exact hf.consecutive _ he.right_mem fe.2 ⟨l₂.trans h₁,bad⟩

/-- Nonparallel supporting normals detect strict variation along the other edge. -/
theorem transverse_levels {D : Finset Pt} {w n m : Pt} {e : Edge}
    (he : Supported D w e m) (nm : det n m ≠ 0) : dot n e.1 ≠ dot n e.2 := by
  intro h
  have dm : dot m (e.2-e.1) = 0 := by rw [dot_sub,he.level,sub_self]
  have dn : dot n (e.2-e.1) = 0 := by rw [dot_sub,h,sub_self]
  have zero (v : Pt) : det v (e.2-e.1) = 0 := by
    have q := bracket n m v (e.2-e.1)
    rw [dm,dn,zero_mul,zero_mul,sub_self] at q
    exact (mul_eq_zero.mp q.symm).resolve_left nm
  have z₁ := zero (0,1)
  have z₂ := zero (1,0)
  simp [det] at z₁ z₂
  have same : e.2 = e.1 := Prod.ext (by linarith) (by linarith)
  exact he.increasing.ne (congrArg (dot w) same.symm)

end SquarePlaneBoundary

namespace SquarePlaneBoundary
open scoped Pointwise

structure Tile (D : Finset Pt) (w : Pt) where
  e : Edge
  f : Edge
  n : Pt
  m : Pt
  es : Supported D w e n
  fs : Supported D w f m
  ordered : 0 < det n m

def OpenTile {D : Finset Pt} {w : Pt} (T : Tile D w) (x : Pt) : Prop :=
  ∃ t : ℝ, ∃ u : ℝ, 0 < t ∧ t < 1 ∧ 0 < u ∧ u < 1 ∧ x=lerp T.e.1 T.e.2 t + lerp T.f.1 T.f.2 u

theorem det_flip (n m : Pt) : det m n = -det n m := by unfold det; ring

theorem tile_separation {D : Finset Pt} {w c x : Pt} (ew : Set.InjOn (dot w) (D : Set Pt))
    (symm : ∀ z ∈ D, c-z ∈ D) (T U : Tile D w) (hT : OpenTile T x) (hU : OpenTile U x) :
    T.e=U.e ∧ T.f=U.f := by
  obtain ⟨t,u,ht,ht',hu,hu',h⟩ := hT
  obtain ⟨a,b,ha,ha',hb,hb',h'⟩ := hU
  have positive (S : Tile D w) (i j : ℝ) (hi : 0 < i) (hi' : i < 1) (hj : 0 < j) (hj' : j < 1)
      (sum : x=lerp S.e.1 S.e.2 i + lerp S.f.1 S.f.2 j) :
      0 < dot S.n (x-c) ∧ 0 < dot S.m (x-c) := by
    have hn := lerp_height (t:=i) S.es.level
    have hm := lerp_height (t:=j) S.fs.level
    rw [sum]
    constructor
    · apply transverse_positive _ _ _ _ _ j hj hj'
      · rw [hn]; exact S.es.support _ (symm _ S.fs.left_mem)
      · rw [hn]; exact S.es.support _ (symm _ S.fs.right_mem)
      · exact transverse_levels S.fs S.ordered.ne'
    · rw [add_comm]
      apply transverse_positive _ _ _ _ _ i hi hi'
      · rw [hm]; exact S.fs.support _ (symm _ S.es.left_mem)
      · rw [hm]; exact S.fs.support _ (symm _ S.es.right_mem)
      · exact transverse_levels S.es (by rw [det_flip]; exact neg_ne_zero.mpr S.ordered.ne')
  have P := positive T t u ht ht' hu hu' h
  have Q := positive U a b ha ha' hb hb' h'
  have bound {e f : Edge} {n m : Pt} (se : Supported D w e n) (sf : Supported D w f m)
      {i j : ℝ} (hj : 0 < j) (hj' : j < 1) : dot n (lerp f.1 f.2 j) ≤ dot n (lerp e.1 e.2 i) := by
    rw [lerp_height se.level]
    exact lerp_support (se.support _ sf.left_mem) (se.support _ sf.right_mem) hj.le hj'.le
  obtain ⟨E,F⟩ := unique_ordered _ _ _ _ (x-c) _ _ _ _ (h.symm.trans h') T.ordered U.ordered
    P.1 P.2 Q.1 Q.2 (bound T.es U.es ha ha') (bound T.fs U.fs hb hb')
    (bound U.es T.es ht ht') (bound U.fs T.fs hu hu')
  exact ⟨elementary_unique ew T.es U.es ht ht' ha ha' E,elementary_unique ew T.fs U.fs hu hu' hb hb' F⟩

theorem normals_ext {n m a b : Pt} (nm : det n m ≠ 0)
    (hn : dot n a = dot n b) (hm : dot m a = dot m b) : a=b := by
  have van (v : Pt) : det v (a-b) = 0 := by
    have h := bracket n m v (a-b)
    rw [dot_sub,dot_sub,hn,hm,sub_self,sub_self,zero_mul,zero_mul,sub_self] at h
    exact (mul_eq_zero.mp h.symm).resolve_left nm
  have h := van (0,1); have k := van (1,0)
  simp [det] at h k
  exact Prod.ext (by linarith) (by linarith)

theorem dot_smul (n e : Pt) (t : ℝ) : dot n (t • e) = t*dot n e := by simp [dot]; ring

/-- Coordinates of a direction along the two primal edge vectors. -/
theorem tile_coordinates {D : Finset Pt} {w : Pt} (T : Tile D w) (v : Pt)
    (hn : dot T.n v ≠ 0) (hm : dot T.m v ≠ 0) :
    ∃ a b : ℝ, a ≠ 0 ∧ b ≠ 0 ∧ a • (T.e.2-T.e.1)+b • (T.f.2-T.f.1)=v := by
  let E := T.e.2-T.e.1
  let F := T.f.2-T.f.1
  have ef : dot T.n E = 0 := by rw [show E=T.e.2-T.e.1 from rfl,dot_sub,T.es.level,sub_self]
  have fg : dot T.m F = 0 := by rw [show F=T.f.2-T.f.1 from rfl,dot_sub,T.fs.level,sub_self]
  have me : dot T.m E ≠ 0 := by
    rw [show E=T.e.2-T.e.1 from rfl,dot_sub,sub_ne_zero]
    exact (transverse_levels T.es (by rw [det_flip]; exact neg_ne_zero.mpr T.ordered.ne')).symm
  have nf : dot T.n F ≠ 0 := by
    rw [show F=T.f.2-T.f.1 from rfl,dot_sub,sub_ne_zero]
    exact (transverse_levels T.fs T.ordered.ne').symm
  refine ⟨dot T.m v / dot T.m E,dot T.n v / dot T.n F,div_ne_zero hm me,div_ne_zero hn nf,?_⟩
  apply normals_ext T.ordered.ne'
  · rw [dot_add,dot_smul,dot_smul,ef,mul_zero,zero_add,div_mul_cancel₀ _ nf]
  · rw [dot_add,dot_smul,dot_smul,fg,mul_zero,add_zero,div_mul_cancel₀ _ me]

/-- The endpoint from which a sufficiently small positive step along the signed
edge direction enters the relative interior. -/
theorem inward_segment (e : Edge) (a : ℝ) (ha : a ≠ 0) :
    ∃ z : Pt, (z=e.1 ∨ z=e.2) ∧ ∃ d : ℝ, 0 < d ∧ ∀ s : ℝ, 0 < s → s < d →
      ∃ t : ℝ, 0 < t ∧ t < 1 ∧ z + s • (a • (e.2-e.1)) = lerp e.1 e.2 t := by
  rcases lt_or_gt_of_ne ha with neg|pos
  · refine ⟨e.2,Or.inr rfl,-1/a,div_pos_of_neg_of_neg (by norm_num) neg,?_⟩
    intro s hs hsd
    have q := (lt_div_iff_of_neg neg).mp hsd
    refine ⟨1+s*a,by linarith,by linarith [mul_neg_of_pos_of_neg hs neg],?_⟩
    ext <;> simp [lerp] <;> ring
  · refine ⟨e.1,Or.inl rfl,1/a,one_div_pos.mpr pos,?_⟩
    intro s hs hsd
    refine ⟨s*a,mul_pos hs pos,(lt_div_iff₀ pos).mp hsd,?_⟩
    ext <;> simp [lerp] <;> ring

theorem inward_corner {D : Finset Pt} {w : Pt} (T : Tile D w) (v : Pt)
    (hn : dot T.n v ≠ 0) (hm : dot T.m v ≠ 0) :
    ∃ z ∈ D+D, ∃ d : ℝ, 0 < d ∧ ∀ s : ℝ, 0 < s → s < d → OpenTile T (z+s • v) := by
  obtain ⟨a,b,ha,hb,coord⟩ := tile_coordinates T v hn hm
  obtain ⟨i,hi,l,hl,ei⟩ := inward_segment T.e a ha
  obtain ⟨j,hj,r,hr,ej⟩ := inward_segment T.f b hb
  have im : i ∈ D := hi.elim (fun h => h ▸ T.es.left_mem) (fun h => h ▸ T.es.right_mem)
  have jm : j ∈ D := hj.elim (fun h => h ▸ T.fs.left_mem) (fun h => h ▸ T.fs.right_mem)
  refine ⟨i+j,Finset.add_mem_add im jm,min l r,lt_min hl hr,?_⟩
  intro s hs hsd
  obtain ⟨t,ht,ht',et⟩ := ei s hs (lt_min_iff.mp hsd).1
  obtain ⟨u,hu,hu',eu⟩ := ej s hs (lt_min_iff.mp hsd).2
  refine ⟨t,u,ht,ht',hu,hu',?_⟩
  rw [← et,← eu,←coord,smul_add]
  abel

/-- A finite family of nonzero normals admits a common nonorthogonal vector. -/
theorem generic_vector (N : Finset Pt) : ∃ v : Pt, ∀ n ∈ N, n ≠ 0 → dot n v ≠ 0 := by
  classical
  obtain ⟨z,hz⟩ := Infinite.exists_notMem_finset (N.image (fun n => -n.1/n.2))
  refine ⟨(1,z),?_⟩
  intro n hn hne he
  change n.1*1+n.2*z=0 at he
  by_cases b : n.2=0
  · exact hne (Prod.ext (by simpa [b] using he) b)
  · apply hz
    refine Finset.mem_image.mpr ⟨n,hn,?_⟩
    apply (div_eq_iff b).mpr
    linarith [mul_comm z n.2]

theorem generic_projection (D : Finset Pt) : ∃ w : Pt, Set.InjOn (dot w) (D : Set Pt) := by
  obtain ⟨w,hw⟩ := generic_vector (D-D)
  refine ⟨w,?_⟩
  intro x hx y hy eq
  by_contra ne
  apply hw (x-y) (Finset.sub_mem_sub hx hy) (sub_ne_zero.mpr ne)
  have h : dot w (x-y) = 0 := by rw [dot_sub,eq,sub_self]
  simpa [dot,mul_comm] using h

/-- Each ordered nonparallel pair accounts for a distinct actual sum of
two boundary samples, even at nonconforming tile junctions. -/
theorem tiles_le_sums {D : Finset Pt} {w c : Pt} (ew : Set.InjOn (dot w) (D : Set Pt))
    (symm : ∀ z ∈ D, c-z ∈ D) (F : Finset (Edge × Edge))
    (witness : ∀ k ∈ F, ∃ T : Tile D w, T.e=k.1 ∧ T.f=k.2) : F.card ≤ (D+D).card := by
  classical
  choose T E G using fun k : F => witness k k.property
  obtain ⟨v,hv⟩ := generic_vector ((Finset.univ.image (fun k : F => (T k).n)) ∪
    (Finset.univ.image (fun k : F => (T k).m)))
  have select (k : F) := inward_corner (T k) v
    (hv _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩)) (T k).es.normal_ne)
    (hv _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩)) (T k).fs.normal_ne)
  choose z zin d dpos meets using select
  have inj : Function.Injective z := by
    intro i j eq
    let s := min (d i) (d j)/2
    have pos := lt_min (dpos i) (dpos j)
    have hs : 0 < s := half_pos pos
    have small := half_lt_self pos
    have hi := meets i s hs (small.trans_le (min_le_left _ _))
    have hj := meets j s hs (small.trans_le (min_le_right _ _))
    rw [← eq] at hj
    obtain ⟨e,f⟩ := tile_separation ew symm _ _ hi hj
    apply Subtype.ext
    exact Prod.ext ((E i).symm.trans (e.trans (E j))) ((G i).symm.trans (f.trans (G j)))
  simpa using (Finset.card_le_card_of_injOn z (t:=D+D) (s:=Finset.univ)
    (fun k _ => zin k) inj.injOn)

end SquarePlaneBoundary

namespace SquarePlaneBoundary
def axis : Pt := (1,0)
@[simp] theorem dot_axis (z : Pt) : dot axis z = z.1 := by simp [dot,axis]

noncomputable def slope (a b : Pt) : ℝ := (b.2-a.2)/(b.1-a.1)
def roofNormal (k : ℝ) : Pt := (-k,1)
@[simp] theorem roof_dot (k : ℝ) (z : Pt) : dot (roofNormal k) z=z.2-k*z.1 := by simp [roofNormal,dot]; ring

noncomputable def upper (D : Finset Pt) := by
  classical
  exact D.filter (fun x => ∃ k : ℝ, ∀ z ∈ D,
  dot (roofNormal k) z ≤ dot (roofNormal k) x)

theorem roof_iff_slope {x z : Pt} (k : ℝ) (hx : x.1 < z.1) :
    dot (roofNormal k) z ≤ dot (roofNormal k) x ↔ slope x z ≤ k := by
  simp only [slope,roof_dot,div_le_iff₀ (sub_pos.mpr hx)]
  constructor <;> intro h <;> linarith

theorem roof_eq_slope {x z : Pt} (k : ℝ) (hx : x.1 < z.1) :
    dot (roofNormal k) z = dot (roofNormal k) x ↔ slope x z = k := by
  simp only [slope,roof_dot,div_eq_iff (sub_ne_zero.mpr hx.ne')]
  constructor <;> intro h <;> linarith

/-- Each sampled upper hull point other than the rightmost starts an elementary
upper edge. Maximize secant slope to its right and take the nearest tie. -/
theorem next_upper {D : Finset Pt} {x : Pt} (gx : Set.InjOn (dot axis) (D : Set Pt))
    (hx : x ∈ upper D) (later : ∃ y ∈ D, x.1 < y.1) :
    ∃ y : Pt, Supported D axis (x,y) (roofNormal (slope x y)) := by
  classical
  obtain ⟨xm,k,hk⟩ := Finset.mem_filter.mp hx
  let R := D.filter (fun y => x.1 < y.1)
  obtain ⟨z,hz,ltz⟩ := later
  have hR : R.Nonempty := ⟨z,Finset.mem_filter.mpr ⟨hz,ltz⟩⟩
  obtain ⟨u,hu,high⟩ := Finset.exists_max_image R (slope x) hR
  let U := R.filter (fun y => slope x y = slope x u)
  obtain ⟨y,hy,near⟩ := Finset.exists_min_image U Prod.fst ⟨u,Finset.mem_filter.mpr ⟨hu,rfl⟩⟩
  obtain ⟨yr,ys⟩ := Finset.mem_filter.mp hy
  obtain ⟨ym,lt⟩ := Finset.mem_filter.mp yr
  have le := (roof_iff_slope k lt).mp (hk y ym)
  refine ⟨y,xm,ym,by simpa using lt,by intro e; have := congrArg Prod.snd e; norm_num [roofNormal] at this,
    (roof_eq_slope _ lt).mpr rfl,?_,?_⟩
  · intro q hq
    rcases lt_trichotomy x.1 q.1 with pos|eq|neg
    · exact (roof_iff_slope _ pos).mpr ((high q (Finset.mem_filter.mpr ⟨hq,pos⟩)).trans_eq ys.symm)
    · have e := gx xm hq (by simpa only [dot_axis] using eq)
      rw [e]
    · have hh := hk q hq
      simp only [roof_dot] at hh ⊢
      nlinarith [mul_nonneg (sub_nonneg.mpr le) (sub_nonneg.mpr neg.le)]
  · intro q hq eq hbetween
    obtain ⟨ql,qr⟩ := hbetween
    simp only [dot_axis] at ql qr
    have qm : q ∈ U := Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hq,ql⟩,
      ((roof_eq_slope _ ql).mp eq).trans ys⟩
    exact qr.not_ge (near q qm)

/-- Reflecting an elementary upper edge gives an elementary lower edge, with
the two endpoints reversed so the projection is still increasing. -/
def reflectEdge (c : Pt) (e : Edge) : Edge := (c-e.2,c-e.1)

theorem reflect_twice (c : Pt) (e : Edge) : reflectEdge c (reflectEdge c e)=e := by
  simp [reflectEdge]

theorem reflect_supported {D : Finset Pt} {w c n : Pt} {e : Edge}
    (symm : ∀ z ∈ D, c-z ∈ D) (he : Supported D w e n) :
    Supported D w (reflectEdge c e) (-n) := by
  have flip (p : Pt) : dot (-n) p = -dot n p := by simp [dot]; ring
  refine ⟨symm _ he.right_mem,symm _ he.left_mem,?_,neg_ne_zero.mpr he.normal_ne,?_,?_,?_⟩
  · simp only [reflectEdge,dot_sub]; linarith [he.increasing]
  · simp only [reflectEdge,flip,dot_sub,he.level]
  · intro q hq
    have h := he.support _ (symm q hq)
    simp only [reflectEdge,flip,dot_sub,he.level] at h ⊢
    linarith
  · intro q hq eq h
    apply he.consecutive _ (symm q hq)
    · simp only [reflectEdge,flip,dot_sub,he.level] at eq ⊢
      linarith
    · simp only [reflectEdge,dot_sub] at h ⊢
      constructor <;> linarith [h.1,h.2]

theorem chosen_upper_edges {D : Finset Pt} (gx : Set.InjOn (dot axis) (D : Set Pt))
    (hD : D.Nonempty) :
    ∃ E : Finset Edge, (upper D).card ≤ E.card+1 ∧ Set.InjOn Prod.fst (E : Set Edge) ∧
      ∀ e ∈ E, Supported D axis e (roofNormal (slope e.1 e.2)) := by
  classical
  obtain ⟨r,hr,last⟩ := Finset.exists_max_image D Prod.fst hD
  let S := (upper D).erase r
  have existNext (x : S) : ∃ y, Supported D axis (x.val,y) (roofNormal (slope x.val y)) := by
    obtain ⟨ne,hu⟩ := Finset.mem_erase.mp x.property
    have xm := (Finset.mem_filter.mp hu).1
    have lt : x.val.1 < r.1 := (last _ xm).lt_of_ne (fun e => ne (gx xm hr (by simpa using e)))
    exact next_upper gx hu ⟨r,hr,lt⟩
  choose y hy using existNext
  let f (x : S) : Edge := (x.val,y x)
  let E := Finset.univ.image f
  have fi : Function.Injective f := fun x z e => Subtype.ext (congrArg Prod.fst e)
  have ec : E.card = S.card := by simp [E,Finset.card_image_of_injective _ fi]
  refine ⟨E,?_,?_,?_⟩
  · rw [ec]
    by_cases hm : r ∈ upper D
    · exact (Finset.card_erase_add_one hm).symm.le
    · simp [S,Finset.erase_eq_of_notMem hm]
  · intro e he g hg eq
    obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp he
    obtain ⟨z,_,rfl⟩ := Finset.mem_image.mp hg
    exact congrArg f (Subtype.ext eq)
  · intro e he
    obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp he
    exact hy x

end SquarePlaneBoundary

namespace SquarePlaneSweep
open SquarePlaneBoundary
abbrev Pt := SquarePlaneBoundary.Pt

noncomputable def chord (a b : Pt) (s : ℝ) : ℝ := a.2+slope a b*(s-a.1)
noncomputable def mid (a b : Pt) : Pt := ((a.1+b.1)/2,(a.2+b.2)/2)

theorem chord_left (a b : Pt) : chord a b a.1=a.2 := by simp [chord]
theorem slope_mul {a b : Pt} (ab : a.1 < b.1) : slope a b*(b.1-a.1)=b.2-a.2 := by
  exact div_mul_cancel₀ _ (sub_ne_zero.mpr ab.ne')
theorem chord_right {a b : Pt} (ab : a.1 < b.1) : chord a b b.1=b.2 := by
  simp only [chord,slope_mul ab]; ring

theorem chord_mid (a b x y : Pt) : chord a b (mid x y).1=(chord a b x.1+chord a b y.1)/2 := by
  simp [mid,chord]; ring

/-- A continuous chain graph through knots in strictly increasing abscissa.
Constant extension outside its domain makes deletion a local operation. -/
noncomputable def graph : List Pt → ℝ → ℝ
  | [], _ => 0
  | [a], _ => a.2
  | a::b::xs,s => if s ≤ a.1 then a.2 else if s ≤ b.1 then chord a b s else graph (b::xs) s

def Ordered (xs : List Pt) := xs.Pairwise (fun a b => a.1 < b.1)

theorem graph_left (x : Pt) (xs : List Pt) (s : ℝ) (h : s ≤ x.1) : graph (x::xs) s=x.2 := by
  cases xs <;> simp [graph,h]

theorem graph_step {a b : Pt} {xs : List Pt} {s : ℝ} (ab : a.1 < b.1) :
    graph (a::b::xs) s = if s < a.1 then a.2 else if s < b.1 then chord a b s else graph (b::xs) s := by
  rcases lt_trichotomy s a.1 with l|e|r
  · simp [graph,l,l.le]
  · subst s; simp [graph,ab,chord_left]
  · rcases lt_trichotomy s b.1 with h|e|h
    · simp [graph,r.not_ge,r.not_gt,h,h.le]
    · subst s; simp [graph,r.not_ge,r.not_gt,chord_right ab,graph_left b xs b.1 le_rfl]
    · rw [graph]; simp [r.not_ge,r.not_gt,h.not_ge,h.not_gt]

theorem graph_segment {a b : Pt} {xs : List Pt} {s : ℝ} (ab : a.1 < b.1)
    (l : a.1 ≤ s) (r : s ≤ b.1) : graph (a::b::xs) s=chord a b s := by
  rcases l.eq_or_lt with e|h
  · subst s; rw [graph_left _ _ _ le_rfl,chord_left]
  · rw [graph,if_neg h.not_ge,if_pos r]

theorem slope_valley {a b c : Pt} (ab : a.1 < b.1) (bc : b.1 < c.1)
    (valley : b.2 < chord a c b.1) : slope a b < slope a c ∧ slope a c < slope b c := by
  have lab := slope_mul ab
  have lac := slope_mul (ab.trans bc)
  have lbc := slope_mul bc
  unfold chord at valley
  constructor
  · apply lt_of_mul_lt_mul_right (a := b.1-a.1) (by nlinarith) (sub_nonneg.mpr ab.le)
  · apply lt_of_mul_lt_mul_right (a := c.1-b.1) (by nlinarith) (sub_nonneg.mpr bc.le)

theorem valley_band {a b c : Pt} (ab : a.1 < b.1) (bc : b.1 < c.1)
    (valley : b.2 < chord a c b.1) {s : ℝ} (l : a.1 < s) (r : s < c.1) :
    chord a b s < chord a c s ∧ chord b c s < chord a c s := by
  obtain ⟨u,v⟩ := slope_valley ab bc valley
  have ac := slope_mul (ab.trans bc)
  have bc' := slope_mul bc
  unfold chord
  constructor
  · nlinarith [mul_pos (sub_pos.mpr u) (sub_pos.mpr l)]
  · nlinarith [mul_pos (sub_pos.mpr v) (sub_pos.mpr r)]


theorem valley_old {a b c : Pt} (ab : a.1 < b.1) (bc : b.1 < c.1)
    (valley : b.2 < chord a c b.1) {s : ℝ} (lb : a.1 ≤ s) (ub : s ≤ c.1) (xs : List Pt) :
    graph (a::b::c::xs) s=max (chord a b s) (chord b c s) := by
  have u := (slope_valley ab bc valley).1.trans (slope_valley ab bc valley).2
  have eq := slope_mul ab
  by_cases h : s ≤ b.1
  · rw [graph_segment ab lb h,max_eq_left]
    unfold chord
    nlinarith [mul_nonneg (sub_nonneg.mpr u.le) (sub_nonneg.mpr h)]
  · have h' := lt_of_not_ge h
    rw [graph,if_neg (ab.trans h').not_ge,if_neg h,graph_segment bc h'.le ub,max_eq_right]
    unfold chord
    nlinarith [mul_nonneg (sub_nonneg.mpr u.le) (sub_nonneg.mpr h'.le)]

/-- Exact geometric effect of deleting an internal strict valley. Outside the
open interval the two graphs agree; inside, the old V is the maximum of its
two extended side lines and the new graph is the chord. -/
def Change (old new : List Pt) (a b c : Pt) : Prop := ∀ s : ℝ,
  (a.1 < s ∧ s < c.1 → graph old s=max (chord a b s) (chord b c s) ∧ graph new s=chord a c s) ∧
  (¬(a.1 < s ∧ s < c.1) → graph old s=graph new s)

theorem delete_change {a b c : Pt} (xs : List Pt) (ab : a.1 < b.1) (bc : b.1 < c.1)
    (v : b.2 < chord a c b.1) : Change (a::b::c::xs) (a::c::xs) a b c := by
  intro s
  constructor
  · rintro ⟨l,r⟩
    exact ⟨valley_old ab bc v l.le r.le xs,graph_segment (ab.trans bc) l.le r.le⟩
  · intro h
    by_cases l : s ≤ a.1
    · rw [graph_left _ _ _ l,graph_left _ _ _ l]
    · have r : c.1 ≤ s := le_of_not_gt (fun hs => h ⟨lt_of_not_ge l,hs⟩)
      have br := bc.trans_le r
      rw [graph_step ab,graph_step bc,graph_step (ab.trans bc)]
      simp [br.not_gt,(ab.trans br).not_gt,not_lt.mpr r]

theorem change_prepend {a b c t x : Pt} {xs ys : List Pt}
    (tx : t.1 < x.1) (xa : x.1 ≤ a.1)
    (h : Change (x::xs) (x::ys) a b c) : Change (t::x::xs) (t::x::ys) a b c := by
  intro s
  rw [graph_step tx,graph_step tx]
  constructor
  · rintro ⟨l,r⟩
    have q := xa.trans_lt l
    simpa [q.not_gt,(tx.trans q).not_gt] using (h s).1 ⟨l,r⟩
  · intro out
    simp only [(h s).2 out]

end SquarePlaneSweep

namespace SquarePlaneSweep
open SquarePlaneBoundary

def crossing (g h : ℝ → ℝ) (z : Pt) := g z.1 < z.2 ∧ z.2 ≤ h z.1
noncomputable def above (L : List Pt) (D : Finset Pt) := D.filter (fun z => graph L z.1 < z.2)
noncomputable def gain (L K : List Pt) (D : Finset Pt) := by
  classical
  exact D.filter (crossing (graph L) (graph K))

theorem change_mono {L K : List Pt} {a b c : Pt} (h : Change L K a b c)
    (ab : a.1 < b.1) (bc : b.1 < c.1) (v : b.2 < chord a c b.1) (s : ℝ) :
    graph L s ≤ graph K s := by
  by_cases inside : a.1 < s ∧ s < c.1
  · obtain ⟨lo,hi⟩ := (h s).1 inside
    rw [lo,hi,max_le_iff]
    exact And.imp le_of_lt le_of_lt (valley_band ab bc v inside.1 inside.2)
  · exact ((h s).2 inside).le

theorem crossing_range {L K : List Pt} {a b c z : Pt} (h : Change L K a b c)
    (hz : crossing (graph L) (graph K) z) : a.1 < z.1 ∧ z.1 < c.1 := by
  by_contra outside
  exact hz.1.not_ge (((h z.1).2 outside).symm ▸ hz.2)

theorem midpoint_crossing {L K : List Pt} {a b c : Pt} (h : Change L K a b c)
    (ab : a.1 < b.1) (bc : b.1 < c.1) (v : b.2 < chord a c b.1) :
    crossing (graph L) (graph K) (mid a c) := by
  have l : a.1 < (mid a c).1 := by simp [mid]; linarith
  have r : (mid a c).1 < c.1 := by simp [mid]; linarith
  have e := (h _).1 ⟨l,r⟩
  have roof : chord a c (mid a c).1=(mid a c).2 := by
    rw [chord_mid,chord_left,chord_right (ab.trans bc)]; rfl
  have V := valley_band ab bc v l r
  exact ⟨by rw [e.1,← roof,max_lt_iff]; exact V,by rw [e.2,roof]⟩

theorem swept_averages {L K : List Pt} {a b c x : Pt} (h : Change L K a b c)
    (ab : a.1 < b.1) (bc : b.1 < c.1) (v : b.2 < chord a c b.1)
    (hx : crossing (graph L) (graph K) x) :
    crossing (graph L) (graph K) (mid a x) ∧ crossing (graph L) (graph K) (mid c x) := by
  have range := crossing_range h hx
  obtain ⟨old,new⟩ := (h _).1 range
  obtain ⟨xl,xr⟩ := max_lt_iff.mp (old ▸ hx.1)
  have top : x.2 ≤ chord a c x.1 := new ▸ hx.2
  have step (z : Pt) (za : a.1 ≤ z.1) (zc : z.1 ≤ c.1)
      (side1 : chord a b z.1 ≤ z.2) (side2 : chord b c z.1 ≤ z.2)
      (ceiling : z.2 ≤ chord a c z.1) : crossing (graph L) (graph K) (mid z x) := by
    have l : a.1 < (mid z x).1 := by simp [mid]; linarith [range.1]
    have r : (mid z x).1 < c.1 := by simp [mid]; linarith [range.2]
    obtain ⟨lo,hi⟩ := (h _).1 ⟨l,r⟩
    unfold crossing
    rw [lo,hi,max_lt_iff,chord_mid,chord_mid,chord_mid]
    simp only [mid]
    exact ⟨⟨by linarith,by linarith⟩,by linarith⟩
  have la := valley_old ab bc v (le_refl a.1) (ab.trans bc).le []
  rw [graph_left _ _ _ le_rfl] at la
  have lc := valley_old ab bc v (ab.trans bc).le (le_refl c.1) []
  rw [graph_step ab,if_neg (ab.trans bc).not_gt,if_neg bc.not_gt,
    graph_segment bc bc.le le_rfl,chord_right bc] at lc
  exact ⟨step a le_rfl (ab.trans bc).le ((le_max_left _ _).trans_eq la.symm)
    ((le_max_right _ _).trans_eq la.symm) (chord_left _ _).symm.le,
    step c (ab.trans bc).le le_rfl ((le_max_left _ _).trans_eq lc.symm)
    (chord_right bc).le (chord_right (ab.trans bc)).symm.le⟩

theorem mid_inj (a : Pt) : Function.Injective (mid a) := by
  intro x y eq
  apply Prod.ext
  · have h := congrArg Prod.fst eq; simp [mid] at h; linarith
  · have h := congrArg Prod.snd eq; simp [mid] at h; linarith

/-- The central midpoint separates the two injective endpoint families by
abscissa. This count works on a single segment as well as on a swept band. -/
theorem midpoint_count (a c : Pt) (G R : Finset Pt)
    (range : ∀ x ∈ G, a.1 < x.1 ∧ x.1 < c.1) (center : mid a c ∈ R)
    (members : ∀ x ∈ G, mid a x ∈ R ∧ mid c x ∈ R) : 2*G.card+1 ≤ R.card := by
  classical
  let P := G.image (mid a)
  let Q := G.image (mid c)
  have left (x : Pt) (hx : x ∈ P) : x.1 < (mid a c).1 := by
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hx
    simp only [mid]
    linarith [(range z hz).2]
  have right (x : Pt) (hx : x ∈ Q) : (mid a c).1 < x.1 := by
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hx
    simp only [mid]
    linarith [(range z hz).1]
  have dis : Disjoint P Q := Finset.disjoint_left.mpr (fun _ h k => (left _ h).not_gt (right _ k))
  have absent : mid a c ∉ P ∪ Q := by
    intro h
    exact (Finset.mem_union.mp h).elim (fun j => (left _ j).false) (fun j => (right _ j).false)
  have subset : insert (mid a c) (P ∪ Q) ⊆ R := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl|s
    · exact center
    rcases Finset.mem_union.mp s with l|r
    · obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp l; exact (members x hx).1
    · obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp r; exact (members x hx).2
  have cnt := Finset.card_le_card subset
  rw [Finset.card_insert_of_notMem absent,Finset.card_union_of_disjoint dis,
    show P.card=G.card from Finset.card_image_of_injective _ (mid_inj a),
    show Q.card=G.card from Finset.card_image_of_injective _ (mid_inj c)] at cnt
  omega

theorem above_card_split {L K : List Pt} {a b c : Pt} (h : Change L K a b c)
    (ab : a.1 < b.1) (bc : b.1 < c.1) (v : b.2 < chord a c b.1) (D : Finset Pt) :
    (above L D).card=(gain L K D).card+(above K D).card := by
  classical
  have cover : above L D = gain L K D ∪ above K D := by
    ext x
    simp only [above,gain,crossing,Finset.mem_filter,Finset.mem_union]
    have := change_mono h ab bc v x.1
    constructor
    · rintro ⟨mem,lt⟩
      rcases le_or_gt x.2 (graph K x.1) with le|gt
      · exact Or.inl ⟨mem,lt,le⟩
      · exact Or.inr ⟨mem,gt⟩
    · rintro (⟨mem,lt,_⟩|⟨mem,gt⟩)
      · exact ⟨mem,lt⟩
      · exact ⟨mem,this.trans_lt gt⟩
  have dis : Disjoint (gain L K D) (above K D) := Finset.disjoint_left.mpr
    (by intro z hz hy; exact (Finset.mem_filter.mp hy).2.not_ge (show crossing (graph L) (graph K) z from (Finset.mem_filter.mp hz).2).2)
  rw [cover,Finset.card_union_of_disjoint dis]

theorem band_count {L K : List Pt} {a b c : Pt} (h : Change L K a b c)
    (ab : a.1 < b.1) (bc : b.1 < c.1) (v : b.2 < chord a c b.1) (E H : Finset Pt)
    (center : mid a c ∈ H) (sums : ∀ x ∈ E, mid a x ∈ H ∧ mid c x ∈ H) :
    2*(gain L K E).card+1 ≤ (gain L K H).card := by
  classical
  apply midpoint_count a c
  · intro x hx; exact crossing_range h (Finset.mem_filter.mp hx).2
  · exact Finset.mem_filter.mpr ⟨center,midpoint_crossing h ab bc v⟩
  · intro x hx
    obtain ⟨mem,swept⟩ := Finset.mem_filter.mp hx
    obtain ⟨aa,cc⟩ := swept_averages h ab bc v swept
    exact ⟨Finset.mem_filter.mpr ⟨(sums x mem).1,aa⟩,Finset.mem_filter.mpr ⟨(sums x mem).2,cc⟩⟩

end SquarePlaneSweep

namespace SquarePlaneSweep
open SquarePlaneBoundary

def edges : List Pt → List Edge
  | [] => []
  | [_] => []
  | a::b::xs => (a,b)::edges (b::xs)

def NoValleys (L : List Pt) := ∀ (P : List Pt) (a b c : Pt) (Q : List Pt),
  L=P++a::b::c::Q → chord a c b.1 ≤ b.2

def Majorizes (L : List Pt) := ∀ e ∈ edges L, ∀ z ∈ L, z.2 ≤ chord e.1 e.2 z.1

theorem chord_diff (a b : Pt) (s t : ℝ) : chord a b s-chord a b t=slope a b*(s-t) := by
  unfold chord; ring

theorem slope_peak {a b c : Pt} (ab : a.1 < b.1) (bc : b.1 < c.1)
    (peak : chord a c b.1 ≤ b.2) : slope b c ≤ slope a b := by
  have h₁ := slope_mul ab; have h₂ := slope_mul bc; have h₃ := slope_mul (ab.trans bc)
  unfold chord at peak
  have l : slope a c ≤ slope a b := le_of_mul_le_mul_right (a:=b.1-a.1) (by nlinarith) (sub_pos.mpr ab)
  have r : slope b c ≤ slope a c := le_of_mul_le_mul_right (a:=c.1-b.1) (by nlinarith) (sub_pos.mpr bc)
  exact r.trans l

theorem noValleys_tail {a : Pt} {L : List Pt} (h : NoValleys (a::L)) : NoValleys L := by
  intro P x y z Q eq
  exact h (a::P) x y z Q (congrArg (List.cons a) eq)

theorem terminal_roofs (a b : Pt) (xs : List Pt) (ord : Ordered (a::b::xs))
    (nv : NoValleys (a::b::xs)) : Majorizes (a::b::xs) ∧
      ∀ e ∈ edges (a::b::xs), slope e.1 e.2 ≤ slope a b := by
  induction xs generalizing a b with
  | nil =>
    have ab := (List.pairwise_cons.mp ord).1 _ (List.mem_singleton_self _)
    constructor
    · intro e mem z hz
      simp only [edges,List.mem_singleton] at mem
      subst e
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
      rcases hz with rfl|rfl <;> simp [chord_left,chord_right ab]
    · intro e he; simp only [edges,List.mem_singleton] at he; subst e; rfl
  | cons c xs ih =>
    obtain ⟨first,sorted⟩ := List.pairwise_cons.mp ord
    obtain ⟨old,topped⟩ := ih b c sorted (noValleys_tail nv)
    have ab := first b (by simp)
    have bc := (List.pairwise_cons.mp sorted).1 c (by simp)
    have peak := slope_peak ab bc (nv [] a b c xs rfl)
    constructor
    · intro e he z hz
      rcases List.mem_cons.mp he with eq|h
      · subst e
        rcases List.mem_cons.mp hz with rfl|inTail
        · simp [chord_left]
        have zb : b.1 ≤ z.1 := by
          rcases List.mem_cons.mp inTail with rfl|rest
          · rfl
          · exact ((List.pairwise_cons.mp sorted).1 z rest).le
        have low := old (b,c) (List.mem_cons_self) z inTail
        have inc := mul_nonneg (sub_nonneg.mpr peak) (sub_nonneg.mpr zb)
        have endA := chord_right ab
        have endB := chord_left b c
        linarith [chord_diff a b z.1 b.1,chord_diff b c z.1 b.1]
      · rcases List.mem_cons.mp hz with rfl|inTail
        · have bound := old e h b (by simp)
          have sl := (topped e h).trans peak
          have ab' := slope_mul ab
          nlinarith [chord_diff e.1 e.2 z.1 b.1,mul_nonneg (sub_nonneg.mpr sl) (sub_pos.mpr ab).le]
        · exact old e h z inTail
    · intro e he
      rcases List.mem_cons.mp he with rfl|h
      · rfl
      · exact (topped e h).trans peak

theorem graph_mem {L : List Pt} (ord : Ordered L) {z : Pt} (hz : z ∈ L) : graph L z.1=z.2 := by
  induction L with
  | nil => simp at hz
  | cons a L ih =>
    rcases List.mem_cons.mp hz with rfl|mem
    · exact graph_left _ _ _ le_rfl
    · cases L with
      | nil => simp at mem
      | cons b L =>
        obtain ⟨first,sorted⟩ := List.pairwise_cons.mp ord
        have ab := first b (by simp)
        have za := first z mem
        have zb : b.1 ≤ z.1 := by
          rcases List.mem_cons.mp mem with rfl|tail
          · rfl
          · exact ((List.pairwise_cons.mp sorted).1 z tail).le
        rw [graph_step ab,if_neg za.not_gt,if_neg zb.not_gt]
        exact ih sorted mem

def InDomain (L : List Pt) (s : ℝ) := (∃ x ∈ L, x.1 ≤ s) ∧ ∃ y ∈ L, s ≤ y.1

theorem graph_edge (a b : Pt) (L : List Pt) (ord : Ordered (a::b::L)) {s : ℝ}
    (inside : InDomain (a::b::L) s) :
    ∃ e ∈ edges (a::b::L), graph (a::b::L) s=chord e.1 e.2 s := by
  induction L generalizing a b with
  | nil =>
    obtain ⟨⟨x,hx,l⟩,⟨y,hy,r⟩⟩ := inside
    have ab := (List.pairwise_cons.mp ord).1 b (by simp)
    refine ⟨(a,b),List.mem_cons_self,graph_segment ab ?_ ?_⟩
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl|rfl <;> linarith
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl|rfl <;> linarith
  | cons c L ih =>
    obtain ⟨⟨x,hx,l⟩,⟨y,hy,r⟩⟩ := inside
    obtain ⟨first,sorted⟩ := List.pairwise_cons.mp ord
    have ab := first b (by simp)
    by_cases le : s ≤ b.1
    · refine ⟨(a,b),List.mem_cons_self,graph_segment ab ?_ le⟩
      rcases List.mem_cons.mp hx with rfl|mem
      · exact l
      · exact (first _ mem).le.trans l
    · have gt := lt_of_not_ge le
      have alt : y ∈ b::c::L := (List.mem_cons.mp hy).resolve_left (fun ey => by subst y; linarith)
      -- b itself is the left witness on the shorter interval.
      obtain ⟨e,he,eq⟩ := ih b c sorted ⟨⟨b,by simp,gt.le⟩,⟨y,alt,r⟩⟩
      exact ⟨e,List.mem_cons_of_mem _ he,by rw [graph_step ab,if_neg (ab.trans gt).not_gt,if_neg gt.not_gt,eq]⟩

end SquarePlaneSweep

namespace SquarePlaneSweep
open SquarePlaneBoundary

def Covers (L : List Pt) (D : Finset Pt) : Prop := ∀ z ∈ D, InDomain L z.1 ∧
  ∀ k : ℝ, ∃ i ∈ L, dot (roofNormal k) z ≤ dot (roofNormal k) i

theorem prefix_change (P Q : List Pt) {a b c : Pt} (ord : Ordered (P++a::b::c::Q))
    (ab : a.1 < b.1) (bc : b.1 < c.1) (v : b.2 < chord a c b.1) :
    Change (P++a::b::c::Q) (P++a::c::Q) a b c := by
  induction P with
  | nil => exact delete_change Q ab bc v
  | cons x P ih =>
    obtain ⟨first,tail⟩ := List.pairwise_cons.mp ord
    have h := ih tail
    cases P with
    | nil => exact change_prepend (first a (by simp)) le_rfl h
    | cons t P =>
      exact change_prepend (first t (by simp)) ((List.pairwise_cons.mp tail).1 a (by simp)).le h

theorem cover_delete (P Q : List Pt) {a b c : Pt} (ab : a.1 < b.1) (bc : b.1 < c.1)
    (v : b.2 < chord a c b.1) {D : Finset Pt} (cover : Covers (P++a::b::c::Q) D) :
    Covers (P++a::c::Q) D := by
  let K := P++a::c::Q
  have am : a ∈ K := by simp [K]
  have cm : c ∈ K := by simp [K]
  have cases' {z : Pt} (h : z ∈ P++a::b::c::Q) : z ∈ K ∨ z=b := by simp [K] at *; tauto
  have saved (k : ℝ) : ∃ q ∈ K, dot (roofNormal k) b ≤ dot (roofNormal k) q := by
    by_cases le : k ≤ slope a c
    · refine ⟨c,cm,?_⟩
      simp only [roof_dot]
      unfold chord at v
      nlinarith [slope_mul (ab.trans bc),mul_nonneg (sub_nonneg.mpr le) (sub_nonneg.mpr bc.le)]
    · refine ⟨a,am,?_⟩
      simp only [roof_dot]
      unfold chord at v
      nlinarith [mul_nonneg (sub_nonneg.mpr (le_of_not_ge le)) (sub_nonneg.mpr ab.le)]
  intro z hz
  obtain ⟨⟨⟨i,hi,l⟩,⟨j,hj,r⟩⟩,bound⟩ := cover z hz
  constructor
  · constructor
    · rcases cases' hi with h|rfl
      · exact ⟨i,h,l⟩
      · exact ⟨_,am,ab.le.trans l⟩
    · rcases cases' hj with h|rfl
      · exact ⟨j,h,r⟩
      · exact ⟨_,cm,r.trans bc.le⟩
  · intro k
    obtain ⟨i,hi,le⟩ := bound k
    rcases cases' hi with h|rfl
    · exact ⟨i,h,le⟩
    · obtain ⟨q,hq,save⟩ := saved k
      exact ⟨q,hq,le.trans save⟩

theorem terminal_majorant {a b : Pt} {L : List Pt} (ord : Ordered (a::b::L))
    (nv : NoValleys (a::b::L)) {s : ℝ} (dom : InDomain (a::b::L) s) :
    ∃ k : ℝ, ∀ z ∈ a::b::L, z.2 ≤ graph (a::b::L) s+k*(z.1-s) := by
  obtain ⟨e,he,eq⟩ := graph_edge a b L ord dom
  have good := (terminal_roofs a b L ord nv).1 e he
  refine ⟨slope e.1 e.2,?_⟩
  intro z hz
  rw [eq]
  linarith [chord_diff e.1 e.2 z.1 s,good z hz]

theorem terminal_count {C E : Finset Pt} {L : List Pt} (ord : Ordered L) (two : 2 ≤ L.length)
    (nv : NoValleys L) (subset : ∀ z ∈ L, z ∈ C) (cover : Covers L (C∪E)) :
    L.length ≤ (upper C).card ∧ above L E=∅ := by
  classical
  obtain ⟨a,b,Q,rfl⟩ : ∃ a b Q, L=a::b::Q := by
    cases L with
    | nil => simp at two
    | cons a L => cases L <;> simp_all
  let L := a::b::Q
  have roof (s : ℝ) (dom : InDomain L s) : ∃ k : ℝ, ∀ z ∈ C∪E,
      z.2 ≤ graph L s+k*(z.1-s) := by
    obtain ⟨k,hk⟩ := terminal_majorant ord nv dom
    refine ⟨k,?_⟩
    intro z hz
    obtain ⟨i,hi,le⟩ := (cover z hz).2 k
    have h := hk i hi
    simp only [roof_dot] at le
    linarith
  have us : L.toFinset ⊆ upper C := by
    intro z h
    have hz := List.mem_toFinset.mp h
    have zc := subset z hz
    obtain ⟨k,hk⟩ := roof z.1 (cover z (Finset.mem_union_left _ zc)).1
    have g := graph_mem ord hz
    refine Finset.mem_filter.mpr ⟨zc,k,?_⟩
    intro y hy
    have le := hk y (Finset.mem_union_left _ hy)
    simp only [roof_dot]
    change graph L z.1=z.2 at g
    linarith
  have nodup : L.Nodup := ord.imp (fun {x y} h e => h.ne (congrArg Prod.fst e))
  constructor
  · change L.length ≤ _
    simpa only [List.toFinset_card_of_nodup nodup] using Finset.card_le_card us
  · apply Finset.eq_empty_iff_forall_notMem.mpr
    intro z hz
    obtain ⟨mem,lt⟩ := Finset.mem_filter.mp hz
    have m : z ∈ C∪E := Finset.mem_union_right _ mem
    obtain ⟨k,hk⟩ := roof z.1 (cover z m).1
    have le := hk z m
    simp only [sub_self,mul_zero,add_zero] at le
    exact lt.not_ge le

/-- Sweep through every strict valley. Each removal uses one independent new
chord midpoint, in addition to two sums per newly covered noncommon point. -/
theorem upper_sweep (C E H : Finset Pt) (sums : ∀ x ∈ C, ∀ y ∈ C∪E, mid x y ∈ H)
    (L : List Pt) (ord : Ordered L) (two : 2 ≤ L.length) (subset : ∀ z ∈ L, z ∈ C)
    (cover : Covers L (C∪E)) :
    L.length + 2*(above L E).card ≤ (upper C).card+(above L H).card := by
  classical
  by_cases nv : NoValleys L
  · have done := terminal_count ord two nv subset cover
    rw [done.2]; simp only [Finset.card_empty,mul_zero,add_zero]
    exact done.1.trans (Nat.le_add_right _ _)
  · simp only [NoValleys,not_forall] at nv
    obtain ⟨P,a,b,c,Q,fail⟩ := nv
    obtain ⟨eq,v⟩ := fail
    subst L
    have rest : Ordered (a::b::c::Q) := (List.pairwise_append.mp ord).2.1
    have ab := (List.pairwise_cons.mp rest).1 b (by simp)
    have bc := (List.pairwise_cons.mp (List.pairwise_cons.mp rest).2).1 c (by simp)
    let K := P++a::c::Q
    have sub : K.Sublist (P++a::b::c::Q) := (List.append_sublist_append_left P).mpr
      (((List.Sublist.refl (c::Q)).cons b).cons_cons a)
    have vs := lt_of_not_ge v
    have ch := prefix_change P Q ord ab bc vs
    have ac := subset a (by simp)
    have cc := subset c (by simp)
    have add := band_count ch ab bc vs E H (sums a ac c (Finset.mem_union_left _ cc)) (fun x hx =>
      ⟨sums a ac x (Finset.mem_union_right _ hx),sums c cc x (Finset.mem_union_right _ hx)⟩)
    have splitE := above_card_split ch ab bc vs E
    have splitH := above_card_split ch ab bc vs H
    have ih := upper_sweep C E H sums K (ord.sublist sub) (by simp [K]; omega)
      (fun z hz => subset z (sub.subset hz)) (cover_delete P Q ab bc vs cover)
    change (P++a::b::c::Q).length+2*(above _ E).card ≤ _+_ 
    simp only [K,List.length_append,List.length_cons] at ih ⊢
    omega
termination_by L.length
decreasing_by simp_all [K]

end SquarePlaneSweep

namespace SquarePlaneSweep
open SquarePlaneBoundary

noncomputable def onChain (L : List Pt) (D : Finset Pt) := by
  classical
  exact D.filter (fun z => InDomain L z.1 ∧ z.2=graph L z.1)

noncomputable def onSegment (a b : Pt) (D : Finset Pt) := D.filter (fun z =>
  a.1 < z.1 ∧ z.1 < b.1 ∧ z.2=chord a b z.1)

theorem domain_head {a : Pt} {L : List Pt} {s : ℝ} (ord : Ordered (a::L))
    (dom : InDomain (a::L) s) : a.1 ≤ s := by
  obtain ⟨x,hx,le⟩ := dom.1
  rcases List.mem_cons.mp hx with rfl|mem
  · exact le
  · exact ((List.pairwise_cons.mp ord).1 x mem).le.trans le

theorem chain_split {a b : Pt} {L : List Pt} (ord : Ordered (a::b::L)) (D : Finset Pt) :
    (onChain (a::b::L) D).card =
      (if a ∈ D then 1 else 0)+(onSegment a b D).card+(onChain (b::L) D).card := by
  classical
  let S := onSegment a b D
  let K := onChain (b::L) D
  let A := D.filter (·=a)
  have ab := (List.pairwise_cons.mp ord).1 b (by simp)
  have proper (z : Pt) (hz : z ∈ K) : b.1 ≤ z.1 :=
    domain_head (List.pairwise_cons.mp ord).2 (Finset.mem_filter.mp hz).2.1
  have cover : onChain (a::b::L) D = A ∪ S ∪ K := by
    ext z
    constructor
    · intro h
      obtain ⟨mem,range,eq⟩ := Finset.mem_filter.mp h
      have minA := domain_head ord range
      rcases minA.eq_or_lt with e|gt
      · have h1 : z=a := Prod.ext e.symm (eq.trans (graph_left _ _ _ e.symm.le))
        exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨mem,h1⟩))
      · by_cases lt : z.1 < b.1
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr
            ⟨mem,gt,lt,eq.trans (graph_segment ab gt.le lt.le)⟩))
        · have fromB : b.1 ≤ z.1 := le_of_not_gt lt
          obtain ⟨y,hy,ub⟩ := range.2
          have tail : y ∈ b::L := (List.mem_cons.mp hy).resolve_left (fun ha => by subst y; linarith)
          rw [graph_step ab,if_neg gt.not_gt,if_neg lt] at eq
          exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨mem,⟨⟨b,by simp,fromB⟩,y,tail,ub⟩,eq⟩)
    · intro h
      rcases Finset.mem_union.mp h with j|j
      · rcases Finset.mem_union.mp j with am|sm
        · obtain ⟨mem,rfl⟩ := Finset.mem_filter.mp am
          exact Finset.mem_filter.mpr ⟨mem,⟨⟨_,by simp,le_rfl⟩,_,by simp,le_rfl⟩,(graph_left _ _ _ le_rfl).symm⟩
        · obtain ⟨mem,l,r,eq⟩ := Finset.mem_filter.mp sm
          exact Finset.mem_filter.mpr ⟨mem,⟨⟨a,by simp,l.le⟩,b,by simp,r.le⟩,
            eq.trans (graph_segment ab l.le r.le).symm⟩
      · obtain ⟨mem,⟨⟨i,hi,lo⟩,⟨k,hk,ub⟩⟩,eq⟩ := Finset.mem_filter.mp j
        have lower := proper z j
        refine Finset.mem_filter.mpr ⟨mem,⟨⟨i,List.mem_cons_of_mem _ hi,lo⟩,k,List.mem_cons_of_mem _ hk,ub⟩,?_⟩
        rw [graph_step ab,if_neg (ab.trans_le lower).not_gt,if_neg lower.not_gt]
        exact eq
  have d₁ : Disjoint A S := by
    rw [Finset.disjoint_left]
    intro z ha hs
    obtain ⟨_,rfl⟩ := Finset.mem_filter.mp ha
    exact (Finset.mem_filter.mp hs).2.1.false
  have d₂ : Disjoint (A ∪ S) K := by
    rw [Finset.disjoint_left]
    intro z hz hk
    have p := proper z hk
    rcases Finset.mem_union.mp hz with m|m
    · obtain ⟨_,rfl⟩ := Finset.mem_filter.mp m
      exact ab.not_ge p
    · exact (Finset.mem_filter.mp m).2.2.1.not_ge p
  rw [cover,Finset.card_union_of_disjoint d₂,Finset.card_union_of_disjoint d₁]
  by_cases ha : a ∈ D <;> simp [A,S,K,Finset.filter_eq',ha]

theorem segment_count {a b : Pt} (ab : a.1 < b.1) (E H : Finset Pt) (center : mid a b ∈ H)
    (sums : ∀ z ∈ E, mid a z ∈ H ∧ mid b z ∈ H) :
    2*(onSegment a b E).card+1 ≤ (onSegment a b H).card := by
  apply midpoint_count a b
  · intro x hx; have h := (Finset.mem_filter.mp hx).2; exact ⟨h.1,h.2.1⟩
  · apply Finset.mem_filter.mpr
    refine ⟨center,by simp [mid]; linarith,by simp [mid]; linarith,?_⟩
    rw [chord_mid,chord_left,chord_right ab]; rfl
  · intro x hx
    obtain ⟨mem,l,r,eq⟩ := Finset.mem_filter.mp hx
    have put (z : Pt) (lower : a.1 ≤ z.1) (upper : z.1 ≤ b.1) (on : z.2=chord a b z.1)
        (inH : mid z x ∈ H) : mid z x ∈ onSegment a b H := by
      apply Finset.mem_filter.mpr
      refine ⟨inH,by simp [mid]; linarith,by simp [mid]; linarith,?_⟩
      rw [chord_mid,← on,← eq]; rfl
    exact ⟨put a le_rfl ab.le (chord_left _ _).symm (sums x mem).1,
      put b ab.le le_rfl (chord_right ab).symm (sums x mem).2⟩

theorem chain_single (a : Pt) (D : Finset Pt) :
    (onChain [a] D).card = if a ∈ D then 1 else 0 := by
  classical
  have h : onChain [a] D = D.filter (·=a) := by
    ext z
    rw [onChain,Finset.mem_filter,Finset.mem_filter]
    simp only [InDomain,List.mem_singleton,exists_eq_left,graph]
    constructor
    · rintro ⟨m,⟨l,r⟩,e⟩; exact ⟨m,Prod.ext (le_antisymm r l) e⟩
    · rintro ⟨m,rfl⟩; simp [m]
  by_cases ha : a ∈ D <;> simp [h,Finset.filter_eq',ha]

theorem mid_self (x : Pt) : mid x x=x := by ext <;> simp [mid] <;> ring

theorem baseline (a : Pt) (L : List Pt) (ord : Ordered (a::L)) (C E H : Finset Pt)
    (subset : ∀ z ∈ a::L, z ∈ C) (dis : Disjoint C E)
    (sums : ∀ x ∈ C, ∀ y ∈ C∪E, mid x y ∈ H) :
    2*(a::L).length+2*(onChain (a::L) E).card ≤ (onChain (a::L) H).card+1 := by
  induction L generalizing a with
  | nil =>
    have ac := subset a (by simp)
    have ne := Finset.disjoint_left.mp dis ac
    have ah := sums a ac a (Finset.mem_union_left _ ac)
    simpa [chain_single,ne,mid_self a ▸ ah]
  | cons b L ih =>
    obtain ⟨first,sorted⟩ := List.pairwise_cons.mp ord
    have ac := subset a (by simp)
    have bc := subset b (by simp)
    have ne := Finset.disjoint_left.mp dis ac
    have ah := sums a ac a (Finset.mem_union_left _ ac)
    rw [mid_self] at ah
    have smaller := ih b sorted (fun z hz => subset z (List.mem_cons_of_mem _ hz))
    have diff := segment_count (first b (by simp)) E H (sums a ac b (Finset.mem_union_left _ bc))
      (fun z hz => ⟨sums a ac z (Finset.mem_union_right _ hz),sums b bc z (Finset.mem_union_right _ hz)⟩)
    rw [chain_split ord E,chain_split ord H,if_neg ne,if_pos ah,List.length_cons]
    omega

end SquarePlaneSweep

namespace SquarePlaneSweep
open SquarePlaneBoundary

def flip (x : Pt) : Pt := (x.1,-x.2)
theorem flip_flip (x : Pt) : flip (flip x)=x := by simp [flip]
theorem flip_inj : Function.Injective flip := Function.LeftInverse.injective flip_flip
theorem flip_mid (x y : Pt) : mid (flip x) (flip y)=flip (mid x y) := by ext <;> simp [flip,mid] <;> ring

theorem flip_graph (L : List Pt) (s : ℝ) : graph (L.map flip) s = -graph L s := by
  induction L with
  | nil => simp [graph]
  | cons a L ih =>
    cases L with
    | nil => simp [graph,flip]
    | cons b L =>
      simp only [List.map_cons] at ih ⊢
      rw [graph,graph]
      change (if s ≤ a.1 then -a.2 else if s ≤ b.1 then chord (flip a) (flip b) s else _) = _
      split_ifs <;> simp_all [chord,SquarePlaneBoundary.slope,flip] <;> ring

def Dominates (C D : Finset Pt) := ∀ z ∈ D, ∀ n : Pt, ∃ i ∈ C, dot n z ≤ dot n i

theorem flip_dominates {C D : Finset Pt} (h : Dominates C D) :
    Dominates (C.image flip) (D.image flip) := by
  intro z hz n
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨i,hi,le⟩ := h x hx (flip n)
  exact ⟨flip i,Finset.mem_image_of_mem _ hi,by simpa [dot,flip] using le⟩

theorem domination_cover {C D : Finset Pt} {L : List Pt} (h : Dominates C D)
    (mem : ∀ z, z ∈ L ↔ z ∈ C) : Covers L D := by
  intro z hz
  obtain ⟨lo,hl,low⟩ := h z hz (-1,0)
  obtain ⟨hi,hh,high⟩ := h z hz (1,0)
  refine ⟨⟨⟨lo,(mem _).mpr hl,by simpa [dot] using low⟩,hi,(mem _).mpr hh,by simpa [dot] using high⟩,?_⟩
  intro k
  obtain ⟨i,hc,le⟩ := h z hz (roofNormal k)
  exact ⟨i,(mem _).mpr hc,le⟩

theorem ordered_points (C : Finset Pt) (gx : Set.InjOn (dot axis) (C : Set Pt)) :
    ∃ L : List Pt, Ordered L ∧ L.length=C.card ∧ ∀ z, z ∈ L ↔ z ∈ C := by
  classical
  let X := C.image Prod.fst
  let y (s : ℝ) := if h : ∃ t : ℝ, (s,t) ∈ C then h.choose else 0
  let pt (s : ℝ) : Pt := (s,y s)
  have pin (s : ℝ) (hs : s ∈ X) : pt s ∈ C := by
    obtain ⟨⟨u,v⟩,mem,rfl⟩ := Finset.mem_image.mp hs
    have h : ∃ t : ℝ, (u,t) ∈ C := ⟨v,mem⟩
    simpa only [pt,y,dif_pos h] using h.choose_spec
  have card : X.card=C.card := Finset.card_image_of_injOn (fun x hx z hz e => gx hx hz (by simpa using e))
  refine ⟨X.sort.map pt,List.pairwise_map.mpr X.sortedLT_sort.pairwise,by simp [card],?_⟩
  intro z
  simp only [List.mem_map,Finset.mem_sort]
  constructor
  · rintro ⟨s,hs,rfl⟩; exact pin s hs
  · intro hz
    have xz := Finset.mem_image_of_mem Prod.fst hz
    exact ⟨z.1,xz,gx (pin _ xz) hz (by simp [pt])⟩

noncomputable def below (L : List Pt) (D : Finset Pt) := D.filter (fun z => z.2 < graph L z.1)
noncomputable def equalHeight (L : List Pt) (D : Finset Pt) := D.filter (fun z => z.2=graph L z.1)

theorem height_count (L : List Pt) (D : Finset Pt) :
    (above L D).card+(below L D).card+(equalHeight L D).card=D.card := by
  classical
  have h : above L D ∪ below L D ∪ equalHeight L D=D := by
    ext z
    simp only [above,below,equalHeight,Finset.mem_union,Finset.mem_filter]
    constructor
    · tauto
    · intro mem
      rcases lt_trichotomy z.2 (graph L z.1) with l|e|r <;> tauto
  have d₁ : Disjoint (above L D) (below L D) := by
    rw [Finset.disjoint_left]; intro z ha hb
    exact (Finset.mem_filter.mp ha).2.not_gt (Finset.mem_filter.mp hb).2
  have d₂ : Disjoint (above L D ∪ below L D) (equalHeight L D) := by
    rw [Finset.disjoint_left]; intro z hab he
    have eq := (Finset.mem_filter.mp he).2
    rcases Finset.mem_union.mp hab with ha|hb
    · exact (Finset.mem_filter.mp ha).2.ne' eq
    · exact (Finset.mem_filter.mp hb).2.ne eq
  rw [← Finset.card_union_of_disjoint d₁,← Finset.card_union_of_disjoint d₂,h]

theorem below_flip (L : List Pt) (D : Finset Pt) :
    (above (L.map flip) (D.image flip)).card=(below L D).card := by
  classical
  have eq : above (L.map flip) (D.image flip) = (below L D).image flip := by
    ext z
    simp only [above,Finset.mem_filter,Finset.mem_image,below]
    constructor
    · rintro ⟨⟨x,hx,rfl⟩,lt⟩
      rw [flip_graph] at lt
      exact ⟨x,⟨hx,neg_lt_neg_iff.mp lt⟩,rfl⟩
    · rintro ⟨x,⟨hx,lt⟩,rfl⟩
      exact ⟨⟨x,hx,rfl⟩,by rw [flip_graph]; exact neg_lt_neg lt⟩
  rw [eq,Finset.card_image_of_injective _ flip_inj]

/-- A planar common-hull estimate using two opposite sweeps. C is the common
sample and E the distinct extra samples; H contains all used averages. -/
theorem common_hull (C E H : Finset Pt) (gx : Set.InjOn (dot axis) (C : Set Pt)) (two : 2 ≤ C.card)
    (dom : Dominates C (C∪E)) (dis : Disjoint C E)
    (sums : ∀ x ∈ C, ∀ y ∈ C∪E, mid x y ∈ H) :
    4*C.card+2*E.card ≤ H.card+1+(upper C).card+(upper (C.image flip)).card := by
  classical
  obtain ⟨L,ord,len,mem⟩ := ordered_points C gx
  have cover := domination_cover dom mem
  have sub : ∀ z ∈ L, z ∈ C := fun z h => (mem z).mp h
  have sz : 2 ≤ L.length := len ▸ two
  have up := upper_sweep C E H sums L ord sz sub cover
  have flipmem (z : Pt) : z ∈ L.map flip ↔ z ∈ C.image flip := by
    simp only [List.mem_map,Finset.mem_image,mem]
  have flipdom := flip_dominates dom
  rw [Finset.image_union] at flipdom
  have down := upper_sweep (C.image flip) (E.image flip) (H.image flip) (by
    intro x hx y hy
    obtain ⟨i,ib,rfl⟩ := Finset.mem_image.mp hx
    rw [← Finset.image_union] at hy
    obtain ⟨j,jb,rfl⟩ := Finset.mem_image.mp hy
    rw [flip_mid]; exact Finset.mem_image_of_mem _ (sums i ib j jb))
    (L.map flip) (List.pairwise_map.mpr ord) (by simpa using sz) (fun z hz => (flipmem z).mp hz)
    (domination_cover flipdom flipmem)
  rw [List.length_map,below_flip,below_flip] at down
  have base : 2*L.length+2*(onChain L E).card ≤ (onChain L H).card+1 := by
    cases L with
    | nil => simp at sz
    | cons a xs => exact baseline a xs ord C E H sub dis sums
  have ee : onChain L E=equalHeight L E := by
    ext z
    simp only [onChain,equalHeight,Finset.mem_filter]
    exact ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,(cover _ (Finset.mem_union_right _ h.1)).1,h.2⟩⟩
  rw [ee] at base
  have hh : onChain L H ⊆ equalHeight L H := fun z hz =>
    Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hz).1,(Finset.mem_filter.mp hz).2.2⟩
  have hc := Finset.card_le_card hh
  have ec := height_count L E
  have hc' := height_count L H
  omega

end SquarePlaneSweep

namespace SquarePlaneBoundary
open scoped Pointwise
theorem ordered_pair_count {α : Type*} [DecidableEq α] (K : Finset α) (N : α → Pt) (q : ℕ)
    (cap : ∀ i ∈ K, (K.filter (fun j => det (N i) (N j)=0)).card ≤ q) :
    K.card*K.card ≤ 2*((K ×ˢ K).filter (fun e => 0 < det (N e.1) (N e.2))).card+q*K.card := by
  classical
  let P := K ×ˢ K
  let H := P.filter (fun e => 0 < det (N e.1) (N e.2))
  let L := P.filter (fun e => det (N e.1) (N e.2) < 0)
  let Z := P.filter (fun e => det (N e.1) (N e.2)=0)
  have lcount : L.card ≤ H.card := by
    apply Finset.card_le_card_of_injOn Prod.swap
    · intro z hz
      obtain ⟨mem,lt⟩ := Finset.mem_filter.mp hz
      obtain ⟨a,b⟩ := Finset.mem_product.mp mem
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨b,a⟩,by change 0 < det (N z.2) (N z.1); rw [det_flip]; linarith⟩
    · exact Prod.swap_injective.injOn
  have zcount : Z.card ≤ q*K.card := by
    apply Finset.card_le_mul_card_image_of_maps_to (f:=Prod.fst) (fun x hx => (Finset.mem_product.mp (Finset.mem_filter.mp hx).1).1)
    intro i hi
    apply le_trans _ (cap i hi)
    apply Finset.card_le_card_of_injOn Prod.snd
    · intro z hz
      obtain ⟨inZ,eq⟩ := Finset.mem_filter.mp hz
      obtain ⟨mem,zero⟩ := Finset.mem_filter.mp inZ
      exact Finset.mem_filter.mpr ⟨(Finset.mem_product.mp mem).2,eq ▸ zero⟩
    · intro a ha b hb e
      exact Prod.ext ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm) e
  have cover : P ⊆ H ∪ L ∪ Z := by
    intro z hz
    rcases lt_trichotomy 0 (det (N z.1) (N z.2)) with pos|eq|neg
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hz,pos⟩))
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hz,eq.symm⟩)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hz,neg⟩))
  have count := (Finset.card_le_card cover).trans (Finset.card_union_le _ _)
  have count' := Finset.card_union_le H L
  have pc : P.card=K.card*K.card := Finset.card_product _ _
  change _ ≤ 2*H.card+_
  omega

/-- The starting points of chosen upper edges at any one slope occupy at most
all but the rightmost point of one supporting line. -/
theorem upper_parallel_cap {D : Finset Pt} {E : Finset Edge} {p : ℕ}
    (cap : ∀ k h : ℝ, (D.filter (fun z => dot (roofNormal k) z = h)).card ≤ p)
    (inj : Set.InjOn Prod.fst (E : Set Edge))
    (sup : ∀ e ∈ E, Supported D axis e (roofNormal (slope e.1 e.2))) (k : ℝ) :
    (E.filter (fun e => slope e.1 e.2=k)).card ≤ p-1 := by
  classical
  let G := E.filter (fun e => slope e.1 e.2=k)
  change G.card ≤ p-1
  by_cases hG : G.Nonempty
  · obtain ⟨e,he⟩ := hG
    have supported (f : Edge) (hf : f ∈ G) : Supported D axis f (roofNormal k) := by
      obtain ⟨fm,eq⟩ := Finset.mem_filter.mp hf
      exact eq ▸ sup f fm
    let h := dot (roofNormal k) e.1
    let R := D.filter (fun z => dot (roofNormal k) z=h)
    have hs := supported e he
    obtain ⟨r,hr,last⟩ := Finset.exists_max_image R Prod.fst ⟨e.1,Finset.mem_filter.mpr ⟨hs.left_mem,rfl⟩⟩
    have starts (f : Edge) (hf : f ∈ G) : f.1 ∈ R.erase r := by
      have sf := supported f hf
      have eq := le_antisymm (hs.support _ sf.left_mem) (sf.support _ hs.left_mem)
      have fr : f.2 ∈ R := Finset.mem_filter.mpr ⟨sf.right_mem,sf.level.trans eq⟩
      have inc := sf.increasing
      simp only [dot_axis] at inc
      have lt := inc.trans_le (last f.2 fr)
      exact Finset.mem_erase.mpr ⟨fun zz => lt.ne (congrArg Prod.fst zz),Finset.mem_filter.mpr ⟨sf.left_mem,eq⟩⟩
    have num := Finset.card_le_card_of_injOn Prod.fst starts (inj.mono (Finset.filter_subset _ _))
    have rc := cap k h
    have split := Finset.card_erase_add_one hr
    change R.card ≤ p at rc
    omega
  · simp [Finset.not_nonempty_iff_eq_empty.mp hG]

theorem slope_reflect (c : Pt) (e : Edge) : slope (reflectEdge c e).1 (reflectEdge c e).2 = slope e.1 e.2 := by
  simp only [slope,reflectEdge,Prod.fst_sub,Prod.snd_sub]
  congr 1 <;> ring

/-- If an upper edge is also a reflected upper edge, all samples would lie on
its line. Full dimension rules this out. -/
theorem reflected_disjoint {D : Finset Pt} {E : Finset Edge} {c : Pt}
    (symm : ∀ z ∈ D, c-z ∈ D)
    (varies : ∀ k : ℝ, ∃ x ∈ D, ∃ y ∈ D, dot (roofNormal k) x ≠ dot (roofNormal k) y)
    (sup : ∀ e ∈ E, Supported D axis e (roofNormal (slope e.1 e.2))) :
    Disjoint E (E.image (reflectEdge c)) := by
  rw [Finset.disjoint_left]
  intro f hf hfi
  obtain ⟨e,he,eq⟩ := Finset.mem_image.mp hfi
  subst f
  have a := sup _ hf
  rw [slope_reflect] at a
  have b := reflect_supported symm (sup e he)
  obtain ⟨x,hx,y,hy,ne⟩ := varies (slope e.1 e.2)
  have lo (z : Pt) (hz : z ∈ D) := b.support z hz
  have hi (z : Pt) (hz : z ∈ D) := a.support z hz
  have flip (u v : Pt) : dot (-u) v = -dot u v := by simp [dot]; ring
  exact ne (le_antisymm ((hi x hx).trans (by simpa only [flip,neg_le_neg_iff] using lo y hy))
    ((hi y hy).trans (by simpa only [flip,neg_le_neg_iff] using lo x hx)))

end SquarePlaneBoundary

namespace SquarePlaneBoundary
open scoped Pointwise

/-- The large-boundary branch, including the enumeration of the elementary
segments and all unordered transverse pairs. -/
theorem many_upper_sums {p : ℕ} {D : Finset Pt} {c : Pt} (hp : 2 ≤ p)
    (gx : Set.InjOn (dot axis) (D : Set Pt)) (hD : D.Nonempty)
    (symm : ∀ z ∈ D, c-z ∈ D)
    (varies : ∀ k : ℝ, ∃ x ∈ D, ∃ y ∈ D, dot (roofNormal k) x ≠ dot (roofNormal k) y)
    (cap : ∀ k h : ℝ, (D.filter (fun z => dot (roofNormal k) z = h)).card ≤ p)
    (large : 2*p ≤ (upper D).card) : (2*p-1)^2 ≤ (D+D).card := by
  classical
  obtain ⟨E,num,inj,sup⟩ := chosen_upper_edges gx hD
  let R := reflectEdge c
  have ri : Function.Injective R := fun _ _ eq => by simpa only [R,reflect_twice] using congrArg R eq
  let K := E ∪ E.image R
  let k (e : Edge) := slope e.1 e.2
  let N (e : Edge) := if e ∈ E then roofNormal (k e) else -roofNormal (k e)
  have kc : K.card=2*E.card := by
    rw [show K=E ∪ E.image R from rfl,Finset.card_union_of_disjoint (reflected_disjoint symm varies sup),
      Finset.card_image_of_injective _ ri,two_mul]
  have S (e : Edge) (he : e ∈ K) : Supported D axis e (N e) := by
    by_cases h : e ∈ E
    · simpa only [N,if_pos h,k] using sup e h
    · obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp ((Finset.mem_union.mp he).resolve_left h)
      simpa only [N,if_neg h,k,R,slope_reflect] using reflect_supported symm (sup f hf)
  have same (i j : Edge) (eq : det (N i) (N j)=0) : k j=k i := by
    by_cases a : i ∈ E <;> by_cases b : j ∈ E <;> simp [N,a,b,det,roofNormal] at eq <;> linarith
  have parallel (i : Edge) (_ : i ∈ K) :
      (K.filter (fun j => det (N i) (N j)=0)).card ≤ 2*(p-1) := by
    let H := E.filter (fun j => k j=k i)
    have sub : K.filter (fun j => det (N i) (N j)=0) ⊆ H ∪ H.image R := by
      intro j hj
      obtain ⟨mem,zero⟩ := Finset.mem_filter.mp hj
      have eq := same i j zero
      rcases Finset.mem_union.mp mem with first|second
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨first,eq⟩)
      · obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp second
        simp only [k,R,slope_reflect] at eq
        exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨f,Finset.mem_filter.mpr ⟨hf,eq⟩,rfl⟩)
    have bound : H.card ≤ p-1 := upper_parallel_cap cap inj sup (k i)
    have cnt := (Finset.card_le_card sub).trans (Finset.card_union_le _ _)
    rw [Finset.card_image_of_injective _ ri] at cnt
    omega
  let F := (K ×ˢ K).filter (fun e => 0 < det (N e.1) (N e.2))
  have cnt := ordered_pair_count K N _ parallel
  change K.card*K.card ≤ 2*F.card+2*(p-1)*K.card at cnt
  have C : F.card ≤ (D+D).card := by
    apply tiles_le_sums gx symm
    intro e he
    obtain ⟨mem,pos⟩ := Finset.mem_filter.mp he
    obtain ⟨a,b⟩ := Finset.mem_product.mp mem
    exact ⟨⟨e.1,e.2,N e.1,N e.2,S _ a,S _ b,pos⟩,rfl,rfl⟩
  have size : 4*p-2 ≤ K.card := by omega
  have size' : 2*(p-1)+2*p ≤ K.card := by omega
  have mul1 := Nat.mul_le_mul_left K.card size'
  have mul2 := Nat.mul_le_mul_left (2*p) size
  have h1 : 2*p-1+1=2*p := by omega
  have h2 : 4*p-2+2=4*p := by omega
  nlinarith [congrArg (fun x : ℕ => x^2) h1,congrArg (fun x : ℕ => x*(2*p)) h2]

end SquarePlaneBoundary

namespace SquarePlaneBoundary
open scoped Pointwise
open SquarePlaneSweep (flip mid Dominates common_hull)

theorem upper_flip_le {C : Finset Pt} {c : Pt} (symm : ∀ x ∈ C, c-x ∈ C) :
    (upper (C.image flip)).card ≤ (upper C).card := by
  classical
  let back (z : Pt) := c-flip z
  have fi : Function.Injective back := fun _ _ eq => SquarePlaneSweep.flip_inj (sub_right_inj.mp eq)
  apply Finset.card_le_card_of_injOn back _ fi.injOn
  intro z hz
  obtain ⟨zm,k,hk⟩ := Finset.mem_filter.mp hz
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp zm
  have val : back (flip i)=c-i := by simp [back,SquarePlaneSweep.flip_flip]
  rw [val]
  refine Finset.mem_filter.mpr ⟨symm i hi,-k,?_⟩
  intro y hy
  have h := hk (flip (c-y)) (Finset.mem_image_of_mem _ (symm _ hy))
  simp only [roof_dot,SquarePlaneSweep.flip,Prod.snd_sub,Prod.fst_sub] at h ⊢
  linarith

noncomputable def reflected (c : Pt) (A : Finset Pt) := A.image (c-·)

theorem reflected_mem {c x : Pt} {A : Finset Pt} : x ∈ reflected c A ↔ c-x ∈ A := by
  constructor
  · rintro h
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp h; simpa using hy
  · intro h; exact Finset.mem_image.mpr ⟨_,h,sub_sub_cancel _ _⟩

/-- Combine the two planar counts on the centrally symmetric intersection
of A with its reflection. Hull domination is the only needed symmetry of A. -/
theorem planar_count {p : ℕ} (hp : 2 ≤ p) (A : Finset Pt) (c : Pt)
    (gx : Set.InjOn (dot axis) (A : Set Pt))
    (dom : Dominates (A ∩ reflected c A) (A ∪ reflected c A))
    (varies : ∀ k : ℝ, ∃ x ∈ A ∩ reflected c A, ∃ y ∈ A ∩ reflected c A,
      dot (roofNormal k) x ≠ dot (roofNormal k) y)
    (cap : ∀ k h : ℝ, (A.filter (fun z => dot (roofNormal k) z = h)).card ≤ p)
    (size : A.card ≤ p^2) : 4*A.card+1 ≤ (A-A).card+4*p := by
  classical
  let B := reflected c A
  let C := A ∩ B
  let E := (A ∪ B) \ C
  let half (v : Pt) : Pt := (v.1/2,v.2/2)
  let H := (A-A).image (fun x => half (c+x))
  have cs : C ⊆ A := Finset.inter_subset_left
  have symm (x : Pt) (hx : x ∈ C) : c-x ∈ C := by
    obtain ⟨xa,xb⟩ := Finset.mem_inter.mp hx
    exact Finset.mem_inter.mpr ⟨reflected_mem.mp xb,reflected_mem.mpr (by simpa using xa)⟩
  obtain ⟨u,hu,v,hv,ne⟩ := varies 0
  have two : 2 ≤ C.card := Finset.one_lt_card_iff.mpr ⟨u,v,hu,hv,fun e => ne (congrArg _ e)⟩
  have proj := gx.mono (show (C : Set Pt) ⊆ (A : Set Pt) from cs)
  have put (x : Pt) (hx : x ∈ A) (y : Pt) (hy : y ∈ B) : ∃ d ∈ A-A, x+y=c+d := by
    refine ⟨x-(c-y),Finset.sub_mem_sub hx (reflected_mem.mp hy),?_⟩
    abel
  by_cases many : 2*p ≤ (upper C).card
  · have bound := many_upper_sums hp proj ⟨u,hu⟩ symm varies (fun k h =>
      (Finset.card_le_card (Finset.filter_subset_filter _ cs)).trans (cap k h)) many
    have num : (C+C).card ≤ (A-A).card := by
      apply Finset.card_le_card_of_injOn (fun z => z-c) _ (sub_left_injective.injOn)
      intro z hz
      obtain ⟨x,hx,y,hy,rfl⟩ := Finset.mem_add.mp hz
      obtain ⟨d,hd,eq⟩ := put x (cs hx) y (Finset.mem_inter.mp hy).2
      change x+y-c ∈ A-A
      simpa [eq] using hd
    have e : 2*p-1+1=2*p := by omega
    nlinarith [congrArg (fun x : ℕ => x^2) e]
  · have un : C∪E=A∪B := by
      ext z; simp only [C,E,Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff]; tauto
    have dis : Disjoint C E := Finset.disjoint_left.mpr (fun _ h g => (Finset.mem_sdiff.mp g).2 h)
    have counted := common_hull C E H proj two (un ▸ dom) dis (by
      intro x hx y hy
      rw [un] at hy
      have pair : ∃ d ∈ A-A, x+y=c+d := by
        rcases Finset.mem_union.mp hy with ha|hb
        · simpa only [add_comm y x] using put y ha x (Finset.mem_inter.mp hx).2
        · exact put x (cs hx) y hb
      obtain ⟨d,hd,eq⟩ := pair
      refine Finset.mem_image.mpr ⟨d,hd,?_⟩
      rw [← eq]; rfl)
    have small := upper_flip_le symm
    have nc := Finset.card_union_add_card_inter A B
    have ec := Finset.card_union_of_disjoint dis
    rw [un] at ec
    have bc : B.card=A.card := Finset.card_image_of_injective _ (fun _ _ => sub_right_inj.mp)
    change (A∪B).card+C.card=A.card+B.card at nc
    have Hc : H.card ≤ (A-A).card := Finset.card_image_le
    omega

end SquarePlaneBoundary

namespace SquarePlaneLattice
open scoped Pointwise
open SquarePlaneBoundary (Pt dot roofNormal axis reflected reflected_mem)
open SquarePlaneSweep (Dominates)
open SquarePlaneLabels (determinant)

noncomputable def chart (t : ℝ) : Lattice →+ Pt where
  toFun z := ((z.1 : ℝ)+t*z.2,z.2)
  map_zero' := by simp
  map_add' x y := by ext <;> simp <;> ring

theorem chart_injective (t : ℝ) : Function.Injective (chart t) := by
  intro x y h
  have a := congrArg Prod.fst h
  have b := congrArg Prod.snd h
  change (x.1 : ℝ)+t*x.2 = (y.1 : ℝ)+t*y.2 at a
  change (x.2 : ℝ) = y.2 at b
  rw [b,add_left_inj] at a
  exact Prod.ext (by exact_mod_cast a) (by exact_mod_cast b)

theorem chart_generic (A : Finset Lattice) : ∃ t : ℝ,
    Set.InjOn (dot axis) (A.image (chart t) : Set Pt) := by
  classical
  obtain ⟨t,ht⟩ := Infinite.exists_notMem_finset ((A-A).image (fun z => -(z.1 : ℝ)/z.2))
  refine ⟨t,?_⟩
  intro x hx y hy e
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hy
  apply congrArg (chart t)
  simp only [SquarePlaneBoundary.dot_axis] at e
  change (i.1 : ℝ)+t*i.2=(j.1 : ℝ)+t*j.2 at e
  by_cases eq : i.2=j.2
  · rw [eq,add_left_inj] at e
    exact Prod.ext (by exact_mod_cast e) eq
  · exfalso
    apply ht
    refine Finset.mem_image.mpr ⟨i-j,Finset.sub_mem_sub hi hj,?_⟩
    have nz : ((i.2 : ℝ)-j.2) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr eq
    simp only [Prod.fst_sub,Prod.snd_sub,Int.cast_sub]
    apply (div_eq_iff nz).mpr
    linarith

theorem chart_height (t : ℝ) (n : Pt) (z : Lattice) :
    dot n (chart t z) = normal n.1 (n.1*t+n.2) z := by
  simp [dot,normal,chart]; ring

theorem chart_normal_ne {n : Pt} (hn : n ≠ 0) (t : ℝ) : n.1 ≠ 0 ∨ n.1*t+n.2 ≠ 0 := by
  by_contra! both
  exact hn (Prod.ext both.1 (by simpa [both.1] using both.2))

theorem normal_cap {p : ℕ} (hp : 2 ≤ p) {A : Finset Lattice} (cap : LineCap p A)
    (a b h : ℝ) (nz : a ≠ 0 ∨ b ≠ 0) :
    (A.filter (fun z => normal a b z=h)).card ≤ p := by
  classical
  let R := A.filter (fun z => normal a b z=h)
  change R.card ≤ p
  by_contra! bad
  obtain ⟨i,j,him,hjm,ne⟩ := Finset.one_lt_card_iff.mp (by omega : 1 < R.card)
  have mem (x : Lattice) (hx : x ∈ R) := (Finset.mem_filter.mp hx).1
  have sub : R ⊆ lineRow A i j := by
    intro z hz
    apply Finset.mem_filter.mpr
    refine ⟨mem _ hz,?_⟩
    by_contra nd
    obtain ⟨x,hx,y,hy,nxy⟩ := normal_varies (A:=R) ⟨i,him,j,hjm,z,hz,nd⟩ a b nz
    exact nxy ((Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm)
  exact bad.not_ge ((Finset.card_le_card sub).trans (cap i (mem _ him) j (mem _ hjm) ne))

theorem chart_cap {p : ℕ} (hp : 2 ≤ p) (A : Finset Lattice) (cap : LineCap p A)
    (t k h : ℝ) : ((A.image (chart t)).filter (fun z => dot (roofNormal k) z=h)).card ≤ p := by
  let n := roofNormal k
  have nz : n ≠ 0 := by intro e; have := congrArg Prod.snd e; norm_num [n,roofNormal] at this
  have sub : (A.image (chart t)).filter (fun z => dot n z=h) ⊆
      (A.filter (fun z => normal n.1 (n.1*t+n.2) z=h)).image (chart t) := by
    intro z hz
    obtain ⟨mem,lev⟩ := Finset.mem_filter.mp hz
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp mem
    exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hx,(chart_height t n x).symm.trans lev⟩)
  exact (Finset.card_le_card sub).trans (Finset.card_image_le.trans (normal_cap hp cap _ _ _ (chart_normal_ne nz t)))

/-- Every support maximum of the image and of its reflection is attained by
a point of their intersection. -/
theorem common_max {A : Finset Lattice} (hA : A.Nonempty) (c : Lattice)
    (symm : ∀ a b : ℝ, a ≠ 0 ∨ b ≠ 0 → bottom A (normal a b)=mirror c (topFace A (normal a b)))
    (t : ℝ) (n : Pt) (hn : n ≠ 0) :
    ∃ i ∈ A.image (chart t) ∩ reflected (chart t c) (A.image (chart t)),
      ∀ z ∈ A.image (chart t) ∪ reflected (chart t c) (A.image (chart t)), dot n z ≤ dot n i := by
  let f := normal n.1 (n.1*t+n.2)
  obtain ⟨x,hx,maxi⟩ := Finset.exists_max_image A f hA
  have top : x ∈ topFace A f := top_mem.mpr ⟨hx,maxi⟩
  have bot : c-x ∈ bottom A f := by
    rw [show bottom A f=mirror c (topFace A f) from symm _ _ (chart_normal_ne hn t),mirror_mem,sub_sub_cancel]; exact top
  have b := bot_mem.mp bot
  refine ⟨chart t x,Finset.mem_inter.mpr ⟨Finset.mem_image_of_mem _ hx,reflected_mem.mpr ?_⟩,?_⟩
  · rw [←map_sub]; exact Finset.mem_image_of_mem _ b.1
  · intro z hz
    rcases Finset.mem_union.mp hz with left|right
    · obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp left
      simp only [chart_height]
      exact maxi y hy
    · obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp right
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hq
      rw [←map_sub,chart_height,chart_height]
      have lower := b.2 y hy
      rw [map_sub] at lower
      change f (c-y) ≤ f x
      rw [map_sub]; linarith

end SquarePlaneLattice

namespace SquarePlaneLattice
open scoped Pointwise
open SquarePlaneBoundary (Pt dot axis roofNormal reflected)
open SquarePlaneSweep (Dominates)

theorem hereditary_plane (p : ℕ) (A : Finset Lattice) (hp : 2 ≤ p)
    (hA : A.Nonempty) (size : A.card ≤ p^2) (cap : LineCap p A) : PlanarBound p A := by
  classical
  by_contra bad
  have small (B : Finset Lattice) (sub : B ⊆ A) (hn : B.Nonempty) (lt : B.card < A.card) :
      PlanarBound p B := hereditary_plane p B hp hn ((Finset.card_le_card sub).trans size) (lineCap_mono cap sub)
  obtain ⟨c,symm,_⟩ := symmetric_boundary hp A hA cap bad small
  obtain ⟨t,gx⟩ := chart_generic A
  let R := A.image (chart t)
  let B := reflected (chart t c) R
  let C := R∩B
  have common (n : Pt) (hn : n ≠ 0) : ∃ i ∈ C, ∀ z ∈ R∪B, dot n z ≤ dot n i := common_max hA c symm t n hn
  obtain ⟨i,hi,_⟩ := common (1,0) (by intro h; have := congrArg Prod.fst h; norm_num at this)
  have dom : Dominates C (R∪B) := by
    intro z hz n
    by_cases h : n=0
    · exact ⟨i,hi,by simp [h,dot]⟩
    · obtain ⟨j,hj,b⟩ := common n h; exact ⟨j,hj,b z hz⟩
  have spans := obstruction_spans hp A hA cap bad
  have vary (k : ℝ) : ∃ x ∈ C, ∃ y ∈ C, dot (roofNormal k) x ≠ dot (roofNormal k) y := by
    let n := roofNormal k
    have nz : n ≠ 0 := by intro e; have := congrArg Prod.snd e; norm_num [n,roofNormal] at this
    obtain ⟨u,hu,high⟩ := common n nz
    obtain ⟨v,hv,low⟩ := common (-n) (neg_ne_zero.mpr nz)
    refine ⟨u,hu,v,hv,?_⟩
    intro eq
    have same (z : Lattice) (hz : z ∈ A) : dot n (chart t z)=dot n u := by
      have mem : chart t z ∈ R∪B := Finset.mem_union_left _ (Finset.mem_image_of_mem _ hz)
      apply le_antisymm (high _ mem)
      have rev := low _ mem
      have neg (q : Pt) : dot (-n) q = -dot n q := by simp [dot]; ring
      rw [neg,neg,neg_le_neg_iff] at rev
      exact eq ▸ rev
    obtain ⟨a,ha,b,hb,ne⟩ := normal_varies spans _ _ (chart_normal_ne nz t)
    exact ne ((chart_height t n a).symm.trans ((same a ha).trans ((same b hb).symm.trans (chart_height t n b))))
  have rc : R.card=A.card := Finset.card_image_of_injective _ (chart_injective t)
  have calcR := SquarePlaneBoundary.planar_count hp R (chart t c) gx dom vary (chart_cap hp A cap t) (rc ▸ size)
  have diff : R-R=(A-A).image (chart t) := by
    ext z
    constructor
    · intro hz
      obtain ⟨u,hu,v,hv,rfl⟩ := Finset.mem_sub.mp hz
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hv
      rw [← map_sub]
      exact Finset.mem_image_of_mem _ (Finset.sub_mem_sub ha hb)
    · intro hz
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨a,ha,b,hb,rfl⟩ := Finset.mem_sub.mp hv
      rw [map_sub]
      exact Finset.sub_mem_sub (Finset.mem_image_of_mem _ ha) (Finset.mem_image_of_mem _ hb)
  rw [rc,diff,Finset.card_image_of_injective _ (chart_injective t)] at calcR
  exact bad calcR
termination_by A.card

end SquarePlaneLattice

theorem OMA.solution : type_of% @OMA.S_arxiv_2606_27961.main := by
  apply SquarePlaneLabels.target_of_lattice
  intro p hp _ S hS ht
  exact SquarePlaneLattice.lattice_of_planar SquarePlaneLattice.hereditary_plane p hp S hS ht
