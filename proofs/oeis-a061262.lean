import OMAStatements.S_oeis_a061262

/-!
# Disproof of Cloitre's growth conjecture in OEIS A061262

The identity `(2i + 1)^2 = 8 * T_i + 1` converts triangular representations
to odd square representations. Scaled reflections over four distinct lines
modulo 3 amplify the number of odd square representations from an explicit
finite starting set. The resulting distinct signed triples outnumber
`48 * sqrt m` for arbitrarily large representation counts at `m`.
-/

namespace OMA.S_oeis_a061262
open Finset

private structure Vec where
  x : ℤ
  y : ℤ
  z : ℤ
  deriving DecidableEq

private theorem vec_ext {u v : Vec}
    (hx : u.x = v.x) (hy : u.y = v.y) (hz : u.z = v.z) : u = v := by
  rcases u with ⟨x, y, z⟩
  rcases v with ⟨a, b, c⟩
  rw [Vec.mk.injEq]
  exact ⟨hx, hy, hz⟩

private def norm (u : Vec) : ℤ := u.x^2 + u.y^2 + u.z^2

private def oddVec (u : Vec) : Prop := u.x % 2 = 1 ∧ u.y % 2 = 1 ∧ u.z % 2 = 1

private def prim (u : Vec) : Prop := u.x % 3 ≠ 0 ∨ u.y % 3 ≠ 0 ∨ u.z % 3 ≠ 0

private instance (u : Vec) : Decidable (prim u) := by
  unfold prim
  infer_instance

private abbrev Sign₂ := Bool × Bool
private abbrev Sign₃ := Bool × Bool × Bool

private def sign (b : Bool) : ℤ := if b then 1 else -1

private def dot (v : Sign₂) (u : Vec) : ℤ := u.x + sign v.1 * u.y + sign v.2 * u.z

private def reflect (v : Sign₂) (u : Vec) : Vec :=
  ⟨3*u.x - 2*dot v u, 3*u.y - 2*(sign v.1*dot v u), 3*u.z - 2*(sign v.2*dot v u)⟩

private def scale (u : Vec) : Vec := ⟨3*u.x, 3*u.y, 3*u.z⟩

private theorem norm_reflect (v : Sign₂) (u : Vec) :
    norm (reflect v u) = 9 * norm u := by
  rcases v with ⟨s,t⟩
  cases s <;> cases t <;> simp [norm, reflect, dot, sign] <;> ring

private theorem reflect_injective (v : Sign₂) : Function.Injective (reflect v) := by
  have h (u : Vec) : reflect v (reflect v u) = ⟨9*u.x,9*u.y,9*u.z⟩ := by
    rcases v with ⟨s,t⟩
    cases s <;> cases t <;> apply vec_ext <;> simp [reflect, dot, sign] <;> ring
  intro u w huv
  have hh := congrArg (reflect v) huv
  rw [h, h] at hh
  apply vec_ext
  · have := congrArg Vec.x hh
    change 9 * u.x = 9 * w.x at this
    omega
  · have := congrArg Vec.y hh
    change 9 * u.y = 9 * w.y at this
    omega
  · have := congrArg Vec.z hh
    change 9 * u.z = 9 * w.z at this
    omega

private theorem scale_injective : Function.Injective scale := by
  intro u w huw
  rw [scale, scale, Vec.mk.injEq] at huw
  apply vec_ext <;> omega

private theorem odd_reflect (v : Sign₂) (u : Vec) (h : oddVec u) :
    oddVec (reflect v u) := by
  rcases h with ⟨hx,hy,hz⟩
  unfold oddVec
  simp only [reflect]
  constructor
  · omega
  constructor <;> omega

private theorem odd_scale (u : Vec) (h : oddVec u) : oddVec (scale u) := by
  rcases h with ⟨hx,hy,hz⟩
  unfold oddVec
  simp only [scale]
  constructor
  · omega
  constructor <;> omega

private theorem norm_scale (u : Vec) : norm (scale u) = 9 * norm u := by
  simp only [norm, scale]
  ring

private theorem not_prim_scale (u : Vec) : ¬ prim (scale u) := by
  simp [prim, scale]

private def admissible (u : Vec) (v : Sign₂) := dot v u % 3 ≠ 0

private instance (u : Vec) (v : Sign₂) : Decidable (admissible u v) := inferInstanceAs (Decidable (_ ≠ _))

private theorem reflect_x_mod (v : Sign₂) (u : Vec) :
    (reflect v u).x % 3 = dot v u % 3 := by
  simp only [reflect]
  omega

private theorem prim_reflect (u : Vec) (v : Sign₂) (h : admissible u v) :
    prim (reflect v u) := Or.inl (reflect_x_mod v u ▸ h)

private theorem reflect_eq_sign {u w : Vec} {v s : Sign₂} (hd : admissible u v)
    (he : reflect v u = reflect s w) : v = s := by
  have hx := congrArg (fun q : Vec => q.x % 3) he
  have hy := congrArg (fun q : Vec => q.y % 3) he
  have hz := congrArg (fun q : Vec => q.z % 3) he
  rw [reflect_x_mod, reflect_x_mod] at hx
  unfold admissible at hd
  rcases v with ⟨va,vb⟩
  rcases s with ⟨sa,sb⟩
  have h₁ : va = sa := by
    cases va <;> cases sa <;> simp only [reflect, sign, Bool.false_eq_true, if_false,
      if_true] at hy ⊢ <;> omega
  have h₂ : vb = sb := by
    cases vb <;> cases sb <;> simp only [reflect, sign, Bool.false_eq_true, if_false,
      if_true] at hz ⊢ <;> omega
  rw [h₁,h₂]

private def good (u : Vec) : Finset Sign₂ := univ.filter (admissible u)

private def modVec (u : Vec) : Vec := ⟨u.x%3,u.y%3,u.z%3⟩

private theorem good_mod (u : Vec) : good u = good (modVec u) := by
  ext v
  simp only [good, mem_filter, mem_univ, true_and, admissible]
  rcases v with ⟨s,t⟩
  cases s <;> cases t <;> simp [dot, modVec, sign] <;> omega

private theorem prim_mod (u : Vec) : prim u ↔ prim (modVec u) := by
  simp [prim, modVec]

private theorem norm_mod (u : Vec) : norm (modVec u) % 3 = norm u % 3 := by
  exact (((Int.mod_modEq u.x 3).pow 2).add ((Int.mod_modEq u.y 3).pow 2)).add
    ((Int.mod_modEq u.z 3).pow 2)

private def residueTriple (a b c : Fin 3) : Vec := ⟨a.val, b.val, c.val⟩

private theorem modVec_eq_residue (u : Vec) : ∃ a b c : Fin 3, modVec u = residueTriple a b c := by
  refine ⟨⟨(u.x%3).toNat,by omega⟩, ⟨(u.y%3).toNat,by omega⟩, ⟨(u.z%3).toNat,by omega⟩, ?_⟩
  apply vec_ext <;> simp [residueTriple, modVec] <;> omega

private theorem good_base_check :
    ∀ a b c : Fin 3, norm (residueTriple a b c)%3 = 1 →
      (good (residueTriple a b c)).card = 4 := by decide +kernel

private theorem good_step_check :
    ∀ a b c : Fin 3, norm (residueTriple a b c)%3 = 0 → prim (residueTriple a b c) →
      (good (residueTriple a b c)).card = 3 := by decide +kernel

private theorem card_good_base (u : Vec) (h : norm u % 3 = 1) :
    (good u).card = 4 := by
  obtain ⟨a,b,c,he⟩ := modVec_eq_residue u
  rw [good_mod, he]
  apply good_base_check
  rwa [← he, norm_mod]

private theorem card_good_step (u : Vec) (h : norm u % 3 = 0) (hp : prim u) :
    (good u).card = 3 := by
  obtain ⟨a,b,c,he⟩ := modVec_eq_residue u
  rw [good_mod, he]
  apply good_step_check
  · rwa [← he, norm_mod]
  · rw [← he]
    exact (prim_mod u).mp hp

private def move (s : Finset Vec) : Finset Vec :=
  (s.sigma good).image fun p => reflect p.2 p.1

private theorem card_move (s : Finset Vec) (k : ℕ) (h : ∀ u ∈ s, (good u).card = k) :
    (move s).card = s.card * k := by
  unfold move
  rw [card_image_iff.mpr ?_, card_sigma, sum_congr rfl h, sum_const, Nat.nsmul_eq_mul]
  intro p hp q _hq he
  change reflect p.2 p.1 = reflect q.2 q.1 at he
  have hpg : admissible p.1 p.2 :=
    (mem_filter.mp (mem_sigma.mp hp).2).2
  have hsv : p.2 = q.2 := reflect_eq_sign hpg he
  have hu : p.1 = q.1 := reflect_injective q.2 (by rwa [hsv] at he)
  rcases p with ⟨p,v⟩
  rcases q with ⟨q,w⟩
  dsimp at hu hsv
  subst q
  subst w
  rfl

private theorem move_props (s : Finset Vec) (m : ℤ)
    (h : ∀ u ∈ s, oddVec u ∧ norm u = m) :
    ∀ u ∈ move s, oddVec u ∧ norm u = 9*m ∧ prim u := by
  intro u hu
  obtain ⟨p,hp,rfl⟩ := mem_image.mp hu
  obtain ⟨hps,hpg⟩ := mem_sigma.mp hp
  exact ⟨odd_reflect _ _ (h _ hps).1,
    (norm_reflect _ _).trans (congrArg (9*·) (h _ hps).2),
    prim_reflect _ _ (mem_filter.mp hpg).2⟩

private def moveAll (all new : Finset Vec) : Finset Vec := all.image scale ∪ move new

private theorem card_moveAll (all new : Finset Vec) :
    (moveAll all new).card = all.card + (move new).card := by
  have hd : Disjoint (all.image scale) (move new) := by
    apply disjoint_left.mpr
    intro u hu hnew
    obtain ⟨w,_,rfl⟩ := mem_image.mp hu
    obtain ⟨p,hp,he⟩ := mem_image.mp hnew
    exact not_prim_scale w (he ▸ prim_reflect _ _ (mem_filter.mp (mem_sigma.mp hp).2).2)
  simp [moveAll, card_union_of_disjoint hd, card_image_of_injective _ scale_injective]

private theorem moveAll_props (all new : Finset Vec) (m : ℤ)
    (ha : ∀ u ∈ all, oddVec u ∧ norm u = m)
    (hb : ∀ u ∈ new, oddVec u ∧ norm u = m) :
    ∀ u ∈ moveAll all new, oddVec u ∧ norm u = 9*m := by
  intro u hu
  rcases mem_union.mp hu with h | h
  · obtain ⟨w,hw,rfl⟩ := mem_image.mp h
    exact ⟨odd_scale _ (ha _ hw).1, (norm_scale _).trans (congrArg (9*·) (ha _ hw).2)⟩
  · exact ⟨(move_props _ _ hb _ h).1, (move_props _ _ hb _ h).2.1⟩


/- The signed coordinate permutations account for at most 48 ordered
representations per unordered one. For a strictly increasing positive
triple the 48 images are all distinct. -/

private def permute (i : Fin 6) (u : Vec) : Vec :=
  match i.val with
  | 0 => u
  | 1 => ⟨u.x,u.z,u.y⟩
  | 2 => ⟨u.y,u.x,u.z⟩
  | 3 => ⟨u.y,u.z,u.x⟩
  | 4 => ⟨u.z,u.x,u.y⟩
  | _ => ⟨u.z,u.y,u.x⟩

private def signed (s : Sign₃) (u : Vec) : Vec :=
  ⟨sign s.1 * u.x, sign s.2.1 * u.y, sign s.2.2 * u.z⟩

private def absVec (u : Vec) : Vec := ⟨|u.x|, |u.y|, |u.z|⟩

private def posVec (u : Vec) : Prop := 0 < u.x ∧ 0 < u.y ∧ 0 < u.z

private def strictSeed (u : Vec) : Prop := 0 < u.x ∧ u.x < u.y ∧ u.y < u.z

private instance (u : Vec) : Decidable (strictSeed u) := by
  unfold strictSeed
  infer_instance

private instance (u : Vec) : Decidable (oddVec u) := by
  unfold oddVec
  infer_instance

private theorem strict_pos {u : Vec} (h : strictSeed u) : posVec u := by
  obtain ⟨h₁,h₂,h₃⟩ := h
  exact ⟨h₁, h₁.trans h₂, (h₁.trans h₂).trans h₃⟩

private theorem abs_pos {u : Vec} (h : posVec u) : absVec u = u := by
  obtain ⟨h₁,h₂,h₃⟩ := h
  apply vec_ext <;> simp [absVec, abs_of_pos h₁, abs_of_pos h₂, abs_of_pos h₃]

private theorem abs_signed (s : Sign₃) (u : Vec) : absVec (signed s u) = absVec u := by
  have h (b : Bool) : |sign b| = 1 := by cases b <;> simp [sign]
  apply vec_ext <;> simp [absVec, signed, abs_mul, h]

private theorem norm_signed (s : Sign₃) (u : Vec) : norm (signed s u) = norm u := by
  have h (b : Bool) : sign b ^ 2 = 1 := by cases b <;> norm_num [sign]
  simp [norm, signed, mul_pow, h]

private theorem odd_signed (s : Sign₃) (u : Vec) (h : oddVec u) :
    oddVec (signed s u) := by
  obtain ⟨hx,hy,hz⟩ := h
  rcases s with ⟨b,c,d⟩
  cases b <;> cases c <;> cases d <;> simp [oddVec, signed, sign] <;> omega

private theorem norm_permute (i : Fin 6) (u : Vec) : norm (permute i u) = norm u := by
  fin_cases i <;> simp [norm, permute] <;> ring

private theorem odd_permute (i : Fin 6) (u : Vec) : oddVec (permute i u) ↔ oddVec u := by
  fin_cases i <;> simp [oddVec, permute] <;> tauto

private theorem pos_permute (i : Fin 6) (u : Vec) : posVec (permute i u) ↔ posVec u := by
  fin_cases i <;> simp [posVec, permute] <;> tauto

private theorem permute_inj_strict {i j : Fin 6} {u v : Vec}
    (hu : strictSeed u) (hv : strictSeed v)
    (h : permute i u = permute j v) : u = v ∧ i = j := by
  rcases hu with ⟨_,hux,huy⟩
  rcases hv with ⟨_,hvx,hvy⟩
  have h₁ := congrArg Vec.x h
  have h₂ := congrArg Vec.y h
  have h₃ := congrArg Vec.z h
  clear h
  fin_cases i <;> fin_cases j <;>
    simp [permute] at h₁ h₂ h₃ ⊢
  all_goals try (exfalso; omega)
  all_goals apply vec_ext <;> omega

private theorem signed_inj {s t : Sign₃} {u : Vec} (hu : posVec u)
    (h : signed s u = signed t u) : s = t := by
  have scalar {b c : Bool} {x : ℤ} (hx : 0 < x)
      (he : sign b * x = sign c * x) : b = c := by
    cases b <;> cases c <;> simp [sign] at he ⊢ <;> omega
  exact Prod.ext (scalar hu.1 (congrArg Vec.x h))
    (Prod.ext (scalar hu.2.1 (congrArg Vec.y h)) (scalar hu.2.2 (congrArg Vec.z h)))

private def decorated (s : Finset Vec) : Finset (Vec × Fin 6 × Sign₃) := s ×ˢ univ ×ˢ univ

private def expandOne (d : Vec × Fin 6 × Sign₃) : Vec := signed d.2.2 (permute d.2.1 d.1)

private def expand (s : Finset Vec) : Finset Vec := (decorated s).image expandOne

private theorem card_expand (s : Finset Vec) (h : ∀ u ∈ s, strictSeed u) :
    (expand s).card = 48 * s.card := by
  have hi : Set.InjOn expandOne (decorated s) := by
    intro p hp q hq hEq
    have hps : p.1 ∈ s := (mem_product.mp hp).1
    have hqs : q.1 ∈ s := (mem_product.mp hq).1
    have hpp := (pos_permute p.2.1 p.1).mpr (strict_pos (h _ hps))
    have hqp := (pos_permute q.2.1 q.1).mpr (strict_pos (h _ hqs))
    have habs := congrArg absVec hEq
    simp only [expandOne, abs_signed, abs_pos hpp, abs_pos hqp] at habs
    obtain ⟨hv,hperm⟩ := permute_inj_strict (h _ hps) (h _ hqs) habs
    have hsign := signed_inj hpp (by simpa [expandOne, habs] using hEq)
    exact Prod.ext hv (Prod.ext hperm hsign)
  rw [expand, card_image_iff.mpr hi]
  simp [decorated, card_product, mul_comm]

private theorem expand_props (s : Finset Vec) (m : ℤ)
    (h : ∀ u ∈ s, oddVec u ∧ norm u = m) :
    ∀ u ∈ expand s, oddVec u ∧ norm u = m := by
  intro u hu
  obtain ⟨p,hp,rfl⟩ := mem_image.mp hu
  have hz := h _ (mem_product.mp hp).1
  exact ⟨odd_signed _ _ ((odd_permute _ _).mpr hz.1),
    (norm_signed _ _).trans ((norm_permute _ _).trans hz.2)⟩

private def seed : Finset Vec := {
  ⟨3,11,393⟩, ⟨3,57,389⟩, ⟨3,97,381⟩, ⟨3,141,367⟩,
  ⟨3,151,363⟩, ⟨3,209,333⟩, ⟨3,227,321⟩, ⟨3,277,279⟩,
  ⟨7,9,393⟩, ⟨7,69,387⟩, ⟨7,177,351⟩, ⟨7,243,309⟩,
  ⟨21,237,313⟩, ⟨27,75,385⟩, ⟨27,115,375⟩, ⟨27,133,369⟩,
  ⟨27,171,353⟩, ⟨27,231,317⟩, ⟨27,263,291⟩, ⟨29,63,387⟩,
  ⟨29,207,333⟩, ⟨33,61,387⟩, ⟨33,273,281⟩, ⟨43,87,381⟩,
  ⟨43,159,357⟩, ⟨47,51,387⟩, ⟨47,273,279⟩, ⟨57,117,371⟩,
  ⟨57,129,367⟩, ⟨57,231,313⟩, ⟨61,153,357⟩, ⟨61,243,303⟩,
  ⟨63,209,327⟩, ⟨65,177,345⟩, ⟨69,123,367⟩, ⟨75,173,345⟩,
  ⟨75,205,327⟩, ⟨75,223,315⟩, ⟨81,153,353⟩, ⟨81,267,277⟩,
  ⟨87,111,367⟩, ⟨87,227,309⟩, ⟨87,263,279⟩, ⟨93,119,363⟩,
  ⟨93,219,313⟩, ⟨97,231,303⟩, ⟨101,183,333⟩, ⟨101,237,297⟩,
  ⟨105,177,335⟩, ⟨117,133,351⟩, ⟨117,177,331⟩, ⟨117,201,317⟩,
  ⟨119,183,327⟩, ⟨123,165,335⟩, ⟨123,169,333⟩, ⟨129,223,297⟩,
  ⟨133,243,279⟩, ⟨147,153,331⟩, ⟨147,173,321⟩, ⟨153,249,263⟩,
  ⟨155,177,315⟩, ⟨159,177,313⟩, ⟨165,225,277⟩, ⟨171,237,263⟩,
  ⟨173,231,267⟩, ⟨177,205,285⟩, ⟨177,237,259⟩, ⟨195,205,273⟩,
  ⟨195,227,255⟩, ⟨207,223,249⟩}

set_option maxRecDepth 4096 in
private theorem card_seed : seed.card = 70 := by decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_properties :
    ∀ u ∈ seed, strictSeed u ∧ oddVec u ∧ norm u = 154579 := by decide +kernel

private def stage : ℕ → ℕ
  | 0 => 19322
  | k + 1 => 9 * stage k + 3

private def generations (base : Finset Vec) : ℕ → Finset Vec × Finset Vec
  | 0 => (base, base)
  | k + 1 => let p := generations base k
             (moveAll p.1 p.2, move p.2)

private theorem norm_seed_mod {u : Vec} (h : norm u = 154579) : norm u % 3 = 1 :=
  (congrArg (fun n : ℤ => n % 3) h).trans (by decide)

private theorem norm_base_prim (u : Vec) (h : norm u % 3 = 1) : prim u := by
  by_contra hn
  simp only [prim, not_or, not_not] at hn
  have hz : norm (modVec u) = 0 := by simp [norm, modVec, hn.1, hn.2.1, hn.2.2]
  have hm := norm_mod u
  rw [hz, h] at hm
  norm_num at hm

private theorem generations_properties (base : Finset Vec)
    (hbase : ∀ u ∈ base, oddVec u ∧ norm u = 154579) (k : ℕ) :
    (∀ u ∈ (generations base k).1, oddVec u ∧ norm u = (8 * stage k + 3 : ℤ)) ∧
    (∀ u ∈ (generations base k).2, oddVec u ∧ norm u = (8 * stage k + 3 : ℤ) ∧ prim u) := by
  induction k with
  | zero =>
    change (∀ u ∈ base, oddVec u ∧ norm u = 154579) ∧
      (∀ u ∈ base, oddVec u ∧ norm u = 154579 ∧ prim u)
    refine ⟨hbase, fun u hu => ?_⟩
    obtain ⟨ho,hq⟩ := hbase u hu
    exact ⟨ho,hq,norm_base_prim _ (norm_seed_mod hq)⟩
  | succ k ih =>
    have he : 9 * (8 * stage k + 3 : ℤ) = (8 * stage (k+1) + 3 : ℤ) := by
      simp [stage]; ring
    have ha := moveAll_props _ _ _ ih.1 (fun _ hu => ⟨(ih.2 _ hu).1,(ih.2 _ hu).2.1⟩)
    have hp := move_props _ _ (fun _ hu => ⟨(ih.2 _ hu).1,(ih.2 _ hu).2.1⟩)
    rw [he] at ha hp
    exact ⟨ha,hp⟩

private theorem generations_count (base : Finset Vec)
    (hbase : ∀ u ∈ base, oddVec u ∧ norm u = 154579) (hc : base.card = 3360) (k : ℕ) :
    (generations base (k+1)).1.card + 3360 = 6720 * 3 ^ (k+1) ∧
    (generations base (k+1)).2.card = 13440 * 3 ^ k := by
  induction k with
  | zero =>
    have hmov : (move base).card = base.card * 4 :=
      card_move base 4 fun u hu =>
        card_good_base u (norm_seed_mod (hbase u hu).2)
    constructor
    · change (moveAll base base).card + 3360 = 20160
      rw [card_moveAll, hmov, hc]
    · change (move base).card = 13440
      rw [hmov, hc]
  | succ k ih =>
    have hmov : (move (generations base (k+1)).2).card = (generations base (k+1)).2.card * 3 :=
      card_move (generations base (k+1)).2 3 fun u hu => by
        obtain ⟨_, hn, hp⟩ := (generations_properties base hbase (k+1)).2 u hu
        apply card_good_step u _ hp
        rw [hn, stage]
        push_cast
        omega
    constructor
    · change (moveAll (generations base (k+1)).1 (generations base (k+1)).2).card + 3360 =
        6720 * 3 ^ ((k+1)+1)
      rw [card_moveAll, hmov, ih.2, pow_succ (3:ℕ) (k+1), pow_succ (3:ℕ) k]
      have hprev := ih.1
      rw [pow_succ (3:ℕ) k] at hprev
      omega
    · change (move (generations base (k+1)).2).card = 13440 * 3 ^ (k+1)
      rw [hmov, ih.2, pow_succ (3:ℕ) k]
      ring

private theorem stage_exact (k : ℕ) :
    8 * stage k + 3 = 154579 * (3 ^ k)^2 := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [stage, pow_succ]
    calc
      8 * (9 * stage k + 3) + 3 = 9 * (8 * stage k + 3) := by ring
      _ = 154579 * (3 ^ k * 3) ^ 2 := by rw [ih]; ring

private lemma recover_sign (x : ℤ) : sign (decide (0 ≤ x)) * |x| = x := by
  by_cases hx : 0 ≤ x
  · simp [sign, hx, abs_of_nonneg hx]
  · simp [sign, hx, abs_of_neg (lt_of_not_ge hx)]

private lemma abs_odd_positive (x : ℤ) (hx : x % 2 = 1) : 0 < |x| ∧ |x| % 2 = 1 := by
  by_cases hs : 0 ≤ x
  · rw [abs_of_nonneg hs]
    omega
  · rw [abs_of_neg (lt_of_not_ge hs)]
    omega

private lemma sort_vec (u : Vec) :
    ∃ v : Vec, ∃ i : Fin 6, v.x ≤ v.y ∧ v.y ≤ v.z ∧ permute i v = u := by
  rcases u with ⟨x, y, z⟩
  by_cases hxy : x ≤ y
  · by_cases hyz : y ≤ z
    · exact ⟨⟨x, y, z⟩, 0, hxy, hyz, rfl⟩
    · by_cases hxz : x ≤ z
      · exact ⟨⟨x, z, y⟩, 1, hxz, by dsimp; omega, rfl⟩
      · exact ⟨⟨z, x, y⟩, 3, by dsimp; omega, hxy, rfl⟩
  · by_cases hxz : x ≤ z
    · exact ⟨⟨y, x, z⟩, 2, by dsimp; omega, hxz, rfl⟩
    · by_cases hyz : y ≤ z
      · exact ⟨⟨y, z, x⟩, 4, hyz, by dsimp; omega, rfl⟩
      · exact ⟨⟨z, y, x⟩, 5, by dsimp; omega, by dsimp; omega, rfl⟩

private def triIndex (a : ℕ) : ℕ := a * (a + 1) / 2

private lemma triIndex_ge (a : ℕ) : a ≤ triIndex a := by
  unfold triIndex
  rw [Nat.le_div_iff_mul_le (by decide : 0 < 2)]
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · decide
  · exact Nat.mul_le_mul_left _ (by omega)

private lemma sq_odd_from_tri (a : ℕ) : (2 * (a : ℤ) + 1) ^ 2 = 8 * (triIndex a : ℤ) + 1 := by
  have he : 2 ∣ a * (a + 1) := even_iff_two_dvd.mp (Nat.even_mul_succ_self a)
  have hn : a * (a + 1) = 2 * triIndex a := by
    exact (Nat.mul_div_cancel' he).symm
  have hi : (a : ℤ) * ((a : ℤ) + 1) = 2 * (triIndex a : ℤ) := by exact_mod_cast hn
  nlinarith only [hi]

private def waysTuples (m : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((range (m + 1) ×ˢ range (m + 1) ×ˢ range (m + 1)).filter fun t =>
    t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2 ∧ triIndex t.1 + triIndex t.2.1 + triIndex t.2.2 = m)

private def fromTriIndices (t : ℕ × ℕ × ℕ) : Vec :=
  ⟨2 * (t.1 : ℤ) + 1, 2 * (t.2.1 : ℤ) + 1, 2 * (t.2.2 : ℤ) + 1⟩

private lemma positive_odd_coordinate (x : ℤ) (hp : 0 < x) (ho : x % 2 = 1) :
    ∃ a : ℕ, x = 2 * (a : ℤ) + 1 := by
  exact ⟨((x - 1) / 2).toNat, by omega⟩

private lemma sorted_vec_mem_image (m : ℕ) (u : Vec)
    (hp : posVec u) (ho : oddVec u) (hs : norm u = 8 * (m : ℤ) + 3)
    (hxy : u.x ≤ u.y) (hyz : u.y ≤ u.z) : u ∈ (waysTuples m).image fromTriIndices := by
  obtain ⟨a, ha⟩ := positive_odd_coordinate u.x hp.1 ho.1
  obtain ⟨b, hb⟩ := positive_odd_coordinate u.y hp.2.1 ho.2.1
  obtain ⟨c, hc⟩ := positive_odd_coordinate u.z hp.2.2 ho.2.2
  have ht : triIndex a + triIndex b + triIndex c = m := by
    unfold norm at hs
    rw [ha, hb, hc, sq_odd_from_tri, sq_odd_from_tri, sq_odd_from_tri] at hs
    omega
  have ha' := triIndex_ge a
  have hb' := triIndex_ge b
  have hc' := triIndex_ge c
  refine mem_image.mpr ⟨(a,b,c), ?_, ?_⟩
  · have har : a < m + 1 := by omega
    have hbr : b < m + 1 := by omega
    have hcr : c < m + 1 := by omega
    apply mem_filter.mpr
    refine ⟨mem_product.mpr ⟨mem_range.mpr har,
      mem_product.mpr ⟨mem_range.mpr hbr, mem_range.mpr hcr⟩⟩,
      ?_, ?_, ht⟩
    · change a ≤ b
      omega
    · change b ≤ c
      omega
  · apply vec_ext
    · exact ha.symm
    · exact hb.symm
    · exact hc.symm

private theorem signed_ways_bound (m : ℕ) (s : Finset Vec)
    (hs : ∀ u ∈ s, oddVec u ∧ norm u = 8 * (m : ℤ) + 3) :
    s.card ≤ 48 * ways m := by
  let t := (waysTuples m).image fromTriIndices
  have hcover : s ⊆ expand t := by
    intro u hu
    obtain ⟨ho, hn⟩ := hs u hu
    have hx := abs_odd_positive u.x ho.1
    have hy := abs_odd_positive u.y ho.2.1
    have hz := abs_odd_positive u.z ho.2.2
    have hpabs : posVec (absVec u) := ⟨hx.1, hy.1, hz.1⟩
    have hoabs : oddVec (absVec u) := ⟨hx.2, hy.2, hz.2⟩
    have hnabs : norm (absVec u) = 8 * (m : ℤ) + 3 := by
      simpa only [norm, absVec, sq_abs] using hn
    obtain ⟨v, i, hxy, hyz, hperm⟩ := sort_vec (absVec u)
    have hvp : posVec v := (pos_permute i v).mp (hperm.symm ▸ hpabs)
    have hvo : oddVec v := (odd_permute i v).mp (hperm.symm ▸ hoabs)
    have hvn : norm v = 8 * (m : ℤ) + 3 := by
      rw [← norm_permute i v, hperm]
      exact hnabs
    have hvt : v ∈ t := sorted_vec_mem_image m v hvp hvo hvn hxy hyz
    let sg : Sign₃ := (decide (0 ≤ u.x), decide (0 ≤ u.y), decide (0 ≤ u.z))
    refine mem_image.mpr ⟨(v,i,sg), mem_product.mpr ⟨hvt, mem_univ _⟩, ?_⟩
    change signed sg (permute i v) = u
    rw [hperm]
    apply vec_ext
    · exact recover_sign u.x
    · exact recover_sign u.y
    · exact recover_sign u.z
  calc
    s.card ≤ (expand t).card := card_le_card hcover
    _ ≤ (decorated t).card := card_image_le
    _ = 48 * t.card := by simp [decorated, card_product, mul_comm]
    _ ≤ 48 * (waysTuples m).card := Nat.mul_le_mul_left _ card_image_le
    _ = 48 * ways m := rfl

end OMA.S_oeis_a061262

open OMA.S_oeis_a061262 in
/-- The eventual lower bound fails at arbitrarily large representation counts. -/
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a061262.main) := by
  rintro ⟨⟨N,hN⟩,_⟩
  let k := N + 4
  let m := stage (k + 1)
  let t : ℕ := 3 ^ (k + 1)
  let w := ways m
  have ht140 : 140 ≤ t := by
    have hh : (3:ℕ)^5 ≤ 3 ^ (k+1) :=
      Nat.pow_le_pow_right (by decide) (by dsimp [k]; omega)
    exact (by decide : 140 ≤ (3:ℕ)^5).trans hh
  have htN : N ≤ t := by
    have hp (k : ℕ) : k ≤ (3:ℕ)^k := by
      induction k with
      | zero => decide
      | succ k ih =>
        rw [pow_succ]
        have : 0 < (3:ℕ)^k := by positivity
        omega
    exact (by dsimp [k]; omega : N ≤ k+1).trans (hp _)
  let base := expand seed
  have hb : ∀ u ∈ base, oddVec u ∧ norm u = 154579 :=
    expand_props seed 154579 (fun _ hu => (seed_properties _ hu).2)
  have hbcard : base.card = 3360 := by
    change (expand seed).card = 3360
    rw [card_expand _ (fun _ hu => (seed_properties _ hu).1), card_seed]
  have hcard : (generations base (k+1)).1.card ≤ 48 * w :=
    signed_ways_bound m _ (generations_properties base hb (k+1)).1
  have hg : (generations base (k+1)).1.card + 3360 = 6720 * t :=
    (generations_count base hb hbcard k).1
  have hw : 279 * t ≤ 2 * w := by omega
  have hwN : N ≤ w := by omega
  have hsq : (279*t)^2 ≤ (2*w)^2 := by gcongr
  have hm : 8*m+3 = 154579*t^2 := stage_exact (k+1)
  have hlt : 4*m < (279*t)^2 := by
    have hprod : 154579*t^2 < (2*279^2)*t^2 :=
      Nat.mul_lt_mul_of_pos_right (by decide) (by positivity)
    have hr : (2*279^2)*t^2 = 2*(279*t)^2 := by ring
    rw [hr, ← hm] at hprod
    omega
  have he : (2*w)^2 = 4*w^2 := by ring
  have hm_lt : m < w^2 := by rw [he] at hsq; omega
  have ha : a w ≤ m := Nat.sInf_le (show m ∈ {u | ways u = w} from rfl)
  exact (hN _ hwN).1.not_ge (ha.trans hm_lt.le)

