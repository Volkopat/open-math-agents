import OMAStatements.S_oeis_a178352
import Mathlib

namespace GridTripleCount

abbrev Slope := Fin 9
abbrev Coordinate := Fin 6 × Fin 6 × Fin 6

def numerator (r : Slope) : ℕ := ![1, 1, 2, 1, 3, 1, 2, 3, 4] r

def denominator (r : Slope) : ℕ := ![2, 3, 3, 4, 4, 5, 5, 5, 5] r

def OnSlope (r : Slope) (c : Coordinate) : Prop :=
  (denominator r : ℤ) * (((c.2.1 : ℕ) : ℤ) - (c.1 : ℕ)) =
  (numerator r : ℤ) * (((c.2.2 : ℕ) : ℤ) - (c.1 : ℕ))

instance (r : Slope) : DecidablePred (OnSlope r) := by
  intro c
  unfold OnSlope
  infer_instance

abbrev Local (r : Slope) := {c : Coordinate // OnSlope r c}

def choices (r : Slope) : ℕ := ![18, 12, 12, 10, 10, 8, 8, 8, 8] r

theorem localCount : ∀ r : Slope, Fintype.card (Local r) = choices r := by decide

set_option maxRecDepth 4096 in
theorem between : ∀ c : Coordinate, (c.1 < c.2.1 ∧ c.2.1 < c.2.2) ∨
    (c.2.2 < c.2.1 ∧ c.2.1 < c.1) → ∃ r : Slope, OnSlope r c := by decide

private theorem noCollision : ∀ r s : Slope,
    (denominator r : ℤ) * (numerator s : ℤ) = (denominator s : ℤ) * (numerator r : ℤ) →
    r = s := by decide

theorem uniqueRatio (c : Coordinate) (hne : c.1 ≠ c.2.2) {r s : Slope}
    (hr : OnSlope r c) (hs : OnSlope s c) : r = s := by
  have hne' : (((c.2.2 : ℕ) : ℤ) - ((c.1 : ℕ) : ℤ)) ≠ 0 := by
    intro h
    apply hne
    apply Fin.ext
    omega
  have h : ((denominator r : ℤ) * (numerator s : ℤ) -
      (denominator s : ℤ) * (numerator r : ℤ)) *
      (((c.2.2 : ℕ) : ℤ) - ((c.1 : ℕ) : ℤ)) = 0 := by
    unfold OnSlope at hr hs
    linear_combination (denominator s : ℤ) * hr - (denominator r : ℤ) * hs
  exact noCollision r s (sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hne'))

private theorem positive : ∀ r : Slope, 0 < denominator r := by decide

theorem realRatio {r : Slope} {c : Coordinate} :
    OnSlope r c ↔
      ((c.2.1 : ℕ) : ℝ) =
        ((c.1 : ℕ) : ℝ) +
          ((numerator r : ℝ) / (denominator r : ℝ)) *
            (((c.2.2 : ℕ) : ℝ) - ((c.1 : ℕ) : ℝ)) := by
  have hp : (0 : ℝ) < denominator r := by exact_mod_cast positive r
  have bridge : OnSlope r c ↔
      (denominator r : ℝ) * (((c.2.1 : ℕ) : ℝ) - (c.1 : ℕ)) =
        (numerator r : ℝ) * (((c.2.2 : ℕ) : ℝ) - (c.1 : ℕ)) := by
    unfold OnSlope
    norm_cast
  rw [bridge]
  constructor <;> intro h
  · field_simp
    linarith
  · field_simp at h
    linarith

private theorem equalEnds {r : Slope} (t : Local r) (hends : t.val.1 = t.val.2.2) :
    t.val.1 = t.val.2.1 := by
  have ht := t.property
  unfold OnSlope at ht
  rw [← hends, sub_self, mul_zero] at ht
  have hden : (denominator r : ℤ) ≠ 0 := by exact_mod_cast (positive r).ne'
  have e := (mul_eq_zero.mp ht).resolve_left hden
  exact Fin.ext (by omega)

abbrev Diagonal (n : ℕ) (r : Slope) :=
  {v : Fin n → Local r // ∀ i, (v i).val.1 = (v i).val.2.2}

abbrev Proper (n : ℕ) (r : Slope) :=
  {v : Fin n → Local r // ¬ ∀ i, (v i).val.1 = (v i).val.2.2}

/-- Equal endpoints force all three entries of each coordinate to coincide. -/
private def diagonalEquiv (n : ℕ) (r : Slope) : Diagonal n r ≃ (Fin n → Fin 6) where
  toFun v i := (v.val i).val.1
  invFun f := ⟨fun i => ⟨(f i, f i, f i), by simp [OnSlope]⟩, fun _ => rfl⟩
  left_inv v := by
    apply Subtype.ext
    funext i
    apply Subtype.ext
    exact Prod.ext rfl (Prod.ext (equalEnds (v.val i) (v.property i)) (v.property i))
  right_inv _ := rfl

theorem properCount (n : ℕ) (r : Slope) :
    Fintype.card (Proper n r) = choices r ^ n - 6^n := by
  rw [Fintype.card_subtype_compl, Fintype.card_congr (diagonalEquiv n r),
    Fintype.card_fun, Fintype.card_fun, localCount, Fintype.card_fin, Fintype.card_fin]

private theorem choices_ge : ∀ r : Slope, 6 ≤ choices r := by decide

/-- The count ranges over both orders of the endpoints. -/
theorem total (n : ℕ) :
    (∑ r : Slope, (Fintype.card (Proper n r) : ℤ)) =
      4*8^n - 9*6^n + 2*12^n + 18^n + 2*10^n := by
  simp only [properCount, Nat.cast_sub (Nat.pow_le_pow_left (choices_ge _) _), Nat.cast_pow]
  simp [Fin.sum_univ_succ, choices]
  ring

end GridTripleCount

namespace GridTripleCount

open OMA.S_oeis_a178352

abbrev Point (n : ℕ) := Fin n → Fin 6

private theorem point_ext {n : ℕ} {a b : Point n}
    (h : ∀ i, toReal a i = toReal b i) : a = b := by
  funext i
  apply Fin.ext
  have e := h i
  unfold toReal at e
  exact_mod_cast e

private theorem affineParameter {n : ℕ} {a b c : Point n}
    (hc : Collinear ℝ (toReal '' ({a,b,c} : Set (Point n)))) (hac : a ≠ c) :
    ∃ t : ℝ, ∀ i, toReal b i = toReal a i + t * (toReal c i - toReal a i) := by
  have hbase : toReal a ∈ toReal '' ({a,b,c} : Set (Point n)) :=
    Set.mem_image_of_mem _ (by simp)
  obtain ⟨v,hv⟩ := (collinear_iff_of_mem hbase).mp hc
  obtain ⟨q,hq⟩ := hv (toReal c) (Set.mem_image_of_mem _ (by simp))
  obtain ⟨p,hp⟩ := hv (toReal b) (Set.mem_image_of_mem _ (by simp))
  have hne : q ≠ 0 := by
    intro hh
    subst q
    apply hac
    apply point_ext
    intro i
    simpa using congrFun hq.symm i
  refine ⟨p/q, fun i => ?_⟩
  have e := congrFun hq i
  have f := congrFun hp i
  change toReal c i = q * v i + toReal a i at e
  change toReal b i = p * v i + toReal a i at f
  rw [e,f]
  field_simp
  ring

def Ordered {n : ℕ} (a b c : Point n) : Prop :=
  ∃ t : ℝ, 0 < t ∧ t < 1 ∧ ∀ i, toReal b i = toReal a i + t * (toReal c i - toReal a i)

/-- Among three distinct collinear points, one point lies between the other two. -/
theorem orderedSet {n : ℕ} (S : Finset (Point n)) (hs : S.card = 3)
    (hc : Collinear ℝ (toReal '' (S : Set (Point n)))) :
    ∃ a b c : Point n, a ≠ c ∧ S = {a,b,c} ∧ Ordered a b c := by
  obtain ⟨a,b,c,hab,hac,hbc,hS⟩ := Finset.card_eq_three.mp hs
  have hcol : Collinear ℝ (toReal '' ({a,b,c} : Set (Point n))) := by
    simpa [hS] using hc
  obtain ⟨t,ht⟩ := affineParameter hcol hac
  have h0 : t ≠ 0 := by
    intro he
    subst t
    apply hab.symm
    apply point_ext
    intro i
    simpa using ht i
  have h1 : t ≠ 1 := by
    intro he
    subst t
    apply hbc
    apply point_ext
    intro i
    have h := ht i
    linarith
  by_cases hn : t < 0
  · refine ⟨b,a,c,hbc,?_, ⟨-t/(1-t), ?_, ?_, ?_⟩⟩
    · rw [hS]
      ext x
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    · exact div_pos (by linarith) (by linarith)
    · exact (div_lt_iff₀ (by linarith : 0 < 1-t)).mpr (by linarith)
    · intro i
      rw [ht i]
      field_simp [show 1-t ≠ 0 by linarith]
      ring
  by_cases hh : 1 < t
  · refine ⟨a,c,b,hab,?_, ⟨1/t, ?_, ?_, ?_⟩⟩
    · rw [hS]
      ext x
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    · exact div_pos one_pos (by linarith)
    · exact (div_lt_iff₀ (by linarith : 0 < t)).mpr (by linarith)
    · intro i
      rw [ht i]
      field_simp
      ring
  exact ⟨a,b,c,hac,hS,⟨t,lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm h0),
    lt_of_le_of_ne (le_of_not_gt hh) h1,ht⟩⟩

theorem coordinate_between {n : ℕ} {a b c : Point n} (h : Ordered a b c)
    {i : Fin n} (hi : a i ≠ c i) :
    (a i < b i ∧ b i < c i) ∨ (c i < b i ∧ b i < a i) := by
  obtain ⟨t,t0,t1,ht⟩ := h
  have he := ht i
  rcases lt_or_gt_of_ne hi with hlt | hgt
  · left
    have ep : toReal a i < toReal c i := by
      change ((a i : ℕ) : ℝ) < (c i : ℕ)
      exact_mod_cast hlt
    have p₁ : 0 < t * (toReal c i - toReal a i) := mul_pos t0 (sub_pos.mpr ep)
    have p₂ : 0 < (1-t) * (toReal c i - toReal a i) :=
      mul_pos (sub_pos.mpr t1) (sub_pos.mpr ep)
    have h₁ : toReal a i < toReal b i := by linarith
    have h₂ : toReal b i < toReal c i := by linarith
    unfold toReal at h₁ h₂
    exact ⟨by exact_mod_cast h₁,by exact_mod_cast h₂⟩
  · right
    have ep : toReal c i < toReal a i := by
      change ((c i : ℕ) : ℝ) < (a i : ℕ)
      exact_mod_cast hgt
    have p₁ : 0 < t * (toReal a i - toReal c i) := mul_pos t0 (sub_pos.mpr ep)
    have p₂ : 0 < (1-t) * (toReal a i - toReal c i) :=
      mul_pos (sub_pos.mpr t1) (sub_pos.mpr ep)
    have h₁ : toReal c i < toReal b i := by linarith
    have h₂ : toReal b i < toReal a i := by linarith
    unfold toReal at h₁ h₂
    exact ⟨by exact_mod_cast h₁,by exact_mod_cast h₂⟩

/-- A varying coordinate determines the common reduced slope of the triple. -/
theorem commonSlope {n : ℕ} {a b c : Point n} (h : Ordered a b c) (hne : a ≠ c) :
    ∃ r : Slope, ∀ i, OnSlope r (a i,b i,c i) := by
  have hv : ∃ i, a i ≠ c i := by
    by_contra! hn
    exact hne (funext hn)
  obtain ⟨i,hi⟩ := hv
  obtain ⟨r,hr⟩ := between (a i,b i,c i) (coordinate_between h hi)
  obtain ⟨t,_,_,ht⟩ := h
  have hh := realRatio.mp hr
  change toReal b i = toReal a i + ((numerator r : ℝ)/(denominator r : ℝ)) *
    (toReal c i - toReal a i) at hh
  have hd : toReal c i - toReal a i ≠ 0 := by
    intro he
    apply hi
    apply Fin.ext
    have hf := sub_eq_zero.mp he
    unfold toReal at hf
    exact_mod_cast hf.symm
  have ht' : t = (numerator r : ℝ)/(denominator r : ℝ) := by
    apply mul_right_cancel₀ hd
    linarith [ht i]
  refine ⟨r, fun j => realRatio.mpr ?_⟩
  rw [← ht']
  exact ht j

private theorem admissibleSlope : ∀ r : Slope, 0 < numerator r ∧ numerator r < denominator r := by
  decide

theorem ordered_of_slope {n : ℕ} {a b c : Point n} {r : Slope}
    (h : ∀ i, OnSlope r (a i,b i,c i)) : Ordered a b c := by
  obtain ⟨hn,hd⟩ := admissibleSlope r
  have hd' : (0:ℝ) < denominator r := by exact_mod_cast (hn.trans hd)
  have hn' : (0:ℝ) < numerator r := by exact_mod_cast hn
  have hlt : (numerator r:ℝ) < denominator r := by exact_mod_cast hd
  refine ⟨(numerator r:ℝ)/denominator r, div_pos hn' hd', ?_, ?_⟩
  · exact (div_lt_one hd').2 hlt
  · intro i
    exact realRatio.mp (h i)

theorem ordered_reverse {n : ℕ} {a b c : Point n} (h : Ordered a b c) :
    Ordered c b a := by
  obtain ⟨t,h₀,h₁,ht⟩ := h
  refine ⟨1-t,by linarith,by linarith,fun i => ?_⟩
  rw [ht i]
  ring

theorem collinear_of_ordered {n : ℕ} {a b c : Point n} (h : Ordered a b c) :
    Collinear ℝ (toReal '' ({a,b,c} : Set (Point n))) := by
  have hbase : toReal a ∈ toReal '' ({a,b,c} : Set (Point n)) :=
    Set.mem_image_of_mem _ (by simp)
  apply (collinear_iff_of_mem hbase).2
  obtain ⟨t,_,_,ht⟩ := h
  refine ⟨toReal c - toReal a, ?_⟩
  rintro _ ⟨x,hx,rfl⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with ha | hb | hc
  · subst x
    exact ⟨0,by simp⟩
  · subst x
    refine ⟨t,funext fun i => ?_⟩
    change toReal b i = t * (toReal c i-toReal a i)+toReal a i
    rw [add_comm,ht i]
  · subst x
    refine ⟨1,funext fun i => ?_⟩
    change toReal c i = 1 * (toReal c i-toReal a i)+toReal a i
    ring

end GridTripleCount

namespace GridTripleCount

open Classical OMA.S_oeis_a178352

abbrev Oriented (n : ℕ) := Σ r : Slope, Proper n r

abbrev CollinearSets (n : ℕ) :=
  {s : Finset (Point n) // s.card = 3 ∧ Collinear ℝ (toReal '' (s : Set (Point n)))}

def leftPoint {n : ℕ} (p : Oriented n) : Point n := fun i => (p.2.val i).val.1

def midPoint {n : ℕ} (p : Oriented n) : Point n := fun i => (p.2.val i).val.2.1

def rightPoint {n : ℕ} (p : Oriented n) : Point n := fun i => (p.2.val i).val.2.2

private theorem onSlope_at {n : ℕ} (p : Oriented n) (i : Fin n) :
    OnSlope p.1 (leftPoint p i, midPoint p i, rightPoint p i) := (p.2.val i).property

private theorem ends_ne {n : ℕ} (p : Oriented n) : leftPoint p ≠ rightPoint p := by
  intro h
  exact p.2.property (congrFun h)

private theorem ordered {n : ℕ} (p : Oriented n) :
    Ordered (leftPoint p) (midPoint p) (rightPoint p) := ordered_of_slope (onSlope_at p)

private theorem differing {n : ℕ} {a c : Point n} (h : a ≠ c) :
    ∃ i, a i ≠ c i := by
  by_contra! h'
  exact h (funext h')

private theorem all_distinct {n : ℕ} {a b c : Point n} (h : Ordered a b c) (hne : a ≠ c) :
    a ≠ b ∧ b ≠ c := by
  obtain ⟨i, hi⟩ := differing hne
  have horder := coordinate_between h hi
  constructor
  · intro he
    have hcoord := congrFun he i
    omega
  · intro he
    have hcoord := congrFun he i
    omega

private noncomputable def asSet {n : ℕ} (p : Oriented n) : CollinearSets n := by
  have h := all_distinct (ordered p) (ends_ne p)
  refine ⟨{leftPoint p, midPoint p, rightPoint p}, ?_, ?_⟩
  · exact Finset.card_eq_three.mpr ⟨_,_,_,h.1,ends_ne p,h.2,rfl⟩
  · simpa only [Finset.coe_insert, Finset.coe_singleton] using collinear_of_ordered (ordered p)

/-- A varying coordinate distinguishes the three points and identifies the middle. -/
private theorem same_order_or_reverse {n : ℕ} {a b c x y z : Point n}
    (habc : Ordered a b c) (hxyz : Ordered x y z) (hac : a ≠ c) (hxz : x ≠ z)
    (hs : ({a,b,c} : Finset (Point n)) = {x,y,z}) :
    (x = a ∧ y = b ∧ z = c) ∨ (x = c ∧ y = b ∧ z = a) := by
  obtain ⟨i,hi⟩ := differing hac
  have h₁ := coordinate_between habc hi
  have hx : x = a ∨ x = b ∨ x = c := by
    have hm : x ∈ ({a,b,c} : Finset (Point n)) := by rw [hs]; simp
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
  have hy : y = a ∨ y = b ∨ y = c := by
    have hm : y ∈ ({a,b,c} : Finset (Point n)) := by rw [hs]; simp
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
  have hz : z = a ∨ z = b ∨ z = c := by
    have hm : z ∈ ({a,b,c} : Finset (Point n)) := by rw [hs]; simp
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
  have hxzi : x i ≠ z i := by
    intro he
    apply hxz
    rcases hx with hx|hx|hx <;> rcases hz with hz|hz|hz <;>
      subst x <;> subst z <;> first | rfl | omega
  have h₂ := coordinate_between hxyz hxzi
  rcases hx with hx|hx|hx <;> rcases hy with hy|hy|hy <;> rcases hz with hz|hz|hz <;>
    subst x <;> subst y <;> subst z <;>
    first | exact Or.inl ⟨rfl,rfl,rfl⟩ | exact Or.inr ⟨rfl,rfl,rfl⟩ | omega

private theorem oriented_ext {n : ℕ} {p q : Oriented n}
    (h₁ : leftPoint p = leftPoint q) (h₂ : midPoint p = midPoint q)
    (h₃ : rightPoint p = rightPoint q) : p = q := by
  obtain ⟨i,hi⟩ := differing (ends_ne p)
  have hh := onSlope_at q i
  rw [← h₁, ← h₂, ← h₃] at hh
  have hs := uniqueRatio _ hi (onSlope_at p i) hh
  obtain ⟨r,p⟩ := p
  obtain ⟨s,q⟩ := q
  change r = s at hs
  subst s
  congr 1
  apply Subtype.ext
  funext j
  apply Subtype.ext
  exact Prod.ext (congrFun h₁ j) (Prod.ext (congrFun h₂ j) (congrFun h₃ j))

private theorem exists_representation {n : ℕ} {a b c : Point n}
    (h : Ordered a b c) (hne : a ≠ c) :
    ∃ p : Oriented n, leftPoint p = a ∧ midPoint p = b ∧ rightPoint p = c := by
  obtain ⟨r,hr⟩ := commonSlope h hne
  exact ⟨⟨r,⟨fun i => ⟨(a i,b i,c i),hr i⟩, fun he => hne (funext he)⟩⟩,rfl,rfl,rfl⟩

private noncomputable def direction {n : ℕ} (a c : Point n) : Bool :=
  decide ((Fintype.equivFin (Point n) a).val < (Fintype.equivFin (Point n) c).val)

private theorem direction_ne_reverse {n : ℕ} {a c : Point n} (h : a ≠ c) :
    direction a c ≠ direction c a := by
  have hd : (Fintype.equivFin (Point n) a).val ≠ (Fintype.equivFin (Point n) c).val :=
    fun he => h ((Fintype.equivFin (Point n)).injective (Fin.ext he))
  rcases lt_or_gt_of_ne hd with hlt | hgt
  · unfold direction
    simp [hlt, not_lt_of_ge hlt.le]
  · unfold direction
    simp [hgt, not_lt_of_ge hgt.le]

/-- Each unordered collinear triple has two possible endpoint orders. -/
private noncomputable def orientedEquiv (n : ℕ) : Oriented n ≃ CollinearSets n × Bool := by
  let f : Oriented n → CollinearSets n × Bool :=
    fun p => (asSet p, direction (leftPoint p) (rightPoint p))
  apply Equiv.ofBijective f
  constructor
  · intro p q h
    have hs : ({leftPoint p, midPoint p, rightPoint p} : Finset (Point n)) =
        {leftPoint q, midPoint q, rightPoint q} := congrArg (fun z => z.1.val) h
    have hd : direction (leftPoint p) (rightPoint p) = direction (leftPoint q) (rightPoint q) :=
      congrArg Prod.snd h
    rcases same_order_or_reverse (ordered p) (ordered q) (ends_ne p) (ends_ne q) hs with
      ⟨ha,hb,hc⟩ | ⟨ha,_,hc⟩
    · exact oriented_ext ha.symm hb.symm hc.symm
    · rw [ha,hc] at hd
      exact (direction_ne_reverse (ends_ne p) hd).elim
  · rintro ⟨s,d⟩
    obtain ⟨a,b,c,hac,hs,habc⟩ := orderedSet s.val s.property.1 s.property.2
    by_cases hd : direction a c = d
    · obtain ⟨p,ha,hb,hc⟩ := exists_representation habc hac
      refine ⟨p,Prod.ext (Subtype.ext ?_) ?_⟩
      · change ({leftPoint p, midPoint p, rightPoint p} : Finset (Point n)) = s.val
        rw [ha,hb,hc,hs]
      · change direction (leftPoint p) (rightPoint p) = d
        rwa [ha,hc]
    · obtain ⟨p,hc,hb,ha⟩ := exists_representation (ordered_reverse habc) hac.symm
      refine ⟨p, Prod.ext (Subtype.ext ?_) ?_⟩
      · change ({leftPoint p, midPoint p, rightPoint p} : Finset (Point n)) = s.val
        rw [hc,hb,ha,hs]
        ext x
        simp only [Finset.mem_insert, Finset.mem_singleton]
        tauto
      · change direction (leftPoint p) (rightPoint p) = d
        rw [hc,ha]
        have hn := direction_ne_reverse hac
        cases h : direction a c <;> cases h' : direction c a <;> cases d <;> simp_all

theorem count_grid (n : ℕ) :
    2*(a n : ℤ) = 4*8^n - 9*6^n + 2*12^n + 18^n + 2*10^n := by
  have hcard := Fintype.card_congr (orientedEquiv n)
  rw [Fintype.card_sigma, Fintype.card_prod, Fintype.card_bool] at hcard
  have hset : Fintype.card (CollinearSets n) = a n := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_coe_set_eq _
  rw [hset] at hcard
  have hcast := congrArg (fun k : ℕ => (k : ℤ)) hcard
  push_cast at hcast
  rw [total] at hcast
  linear_combination -hcast

end GridTripleCount

theorem OMA.solution : type_of% @OMA.S_oeis_a178352.main := GridTripleCount.count_grid