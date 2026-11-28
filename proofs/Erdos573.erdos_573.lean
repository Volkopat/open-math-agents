import FormalConjectures.ErdosProblems.«573»
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# A counterexample to the triangle–four-cycle asymptotic

The construction is due to Will Howe, Grant Huffman, Jensen Kohlmeyer, and
Liam Kruer. The finite-field coordinate used for the label tests can be any
surjective linear functional to the prime field.

https://hexagonmath.org/2611.00749v1
-/

namespace OMA.Erdos573Proof

open Filter Asymptotics SimpleGraph
open scoped Topology

private theorem extremal_ge {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : ∀ k ∈ ({3, 4} : Set ℕ), (cycleGraph k).Free G) :
    G.edgeFinset.card ≤ Erdos573.cycleExtremalNumber {3, 4} (Fintype.card V) := by
  classical
  let e := Fintype.equivFin V
  let H := G.map e.toEmbedding
  have eh : G ≃g H := SimpleGraph.Iso.map e G
  have hf (k : ℕ) (hk : k ∈ ({3, 4} : Set ℕ)) : (cycleGraph k).Free H := by
    intro c
    exact h k hk ⟨eh.symm.toCopy.comp c.some⟩
  rw [eh.card_edgeFinset_eq]
  have hmem : H ∈ Finset.univ.filter (fun H : SimpleGraph (Fin (Fintype.card V)) =>
      ∀ k ∈ ({3, 4} : Set ℕ), (cycleGraph k).Free H) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,hf⟩
  have hb := Finset.le_sup
    (f := fun H : SimpleGraph (Fin (Fintype.card V)) => H.edgeFinset.card) hmem
  simpa only [Erdos573.cycleExtremalNumber, SimpleGraph.edgeFinset_card,
    ← Nat.card_eq_fintype_card] using hb

private theorem rpow_three_halves {x : ℝ} (hx : 0 ≤ x) :
    x ^ (3 / 2 : ℝ) = (Real.sqrt x)^3 := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx]
  congr 1
  norm_num

private theorem strict_excess :
    (1 + (1 / 100000 : ℝ)) * (Real.sqrt ((1307 * 659 : ℝ) / 2))^3 <
      (428874 * 659 : ℝ) := by
  let r := Real.sqrt ((1307 * 659 : ℝ) / 2)
  have hr : r^2 = (1307 * 659 : ℝ) / 2 := Real.sq_sqrt (by positivity)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  change (1 + (1 / 100000 : ℝ)) * r^3 < (428874 * 659 : ℝ)
  have hsq : ((1 + (1 / 100000 : ℝ)) * r^3)^2 < (428874 * 659 : ℝ)^2 := by
    calc
      _ = (1 + (1 / 100000 : ℝ))^2 * (r^2)^3 := by ring
      _ < _ := by rw [hr]; norm_num
  exact (sq_lt_sq₀ (by positivity) (by positivity)).mp hsq

/-- The exact finite construction only needs to supply an unbounded sequence of
scales with these vertex and edge bounds. -/
private theorem disproved_by_counts (n t : ℕ → ℕ)
    (hn : Tendsto n atTop atTop) (ht : Tendsto t atTop atTop)
    (hsize : ∀ i, n i ≤ 1307 * 659 * (t i)^2)
    (hedge : ∀ i, 428875 * 659 * (t i)^3 - 658 * 659 * (t i)^2 ≤
      Erdos573.cycleExtremalNumber {3, 4} (n i)) :
    ¬ (type_of% @Erdos573.erdos_573) := by
  intro h
  have hnonzero : ∀ᶠ m : ℕ in atTop, ((m : ℝ)/2) ^ (3 / 2 : ℝ) ≠ 0 := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
    have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    exact ne_of_gt (Real.rpow_pos_of_pos (by positivity) _)
  have hratio := (isEquivalent_iff_tendsto_one hnonzero).mp h
  have hub := (hratio.comp hn).eventually_lt_const (show (1 : ℝ) < 1 + 1/100000 by norm_num)
  obtain ⟨i,hi,hi₁,hi₂⟩ := (hub.and ((tendsto_atTop.mp ht 658).and (tendsto_atTop.mp hn 1))).exists
  change ((Erdos573.cycleExtremalNumber {3, 4} (n i) : ℝ) /
    ((n i : ℝ)/2) ^ (3 / 2 : ℝ)) < 1 + 1/100000 at hi
  have hmpos : 0 < (n i : ℝ) := by exact_mod_cast (show 0 < n i by omega)
  have htpos : (0 : ℝ) < t i := by exact_mod_cast (show 0 < t i by omega)
  have hdivpos : (0 : ℝ) < (n i : ℝ) / 2 := by positivity
  have hE := (div_lt_iff₀ (Real.rpow_pos_of_pos hdivpos _)).mp hi
  rw [rpow_three_halves hdivpos.le] at hE
  have hprod : 658 * (t i)^2 ≤ (t i)^3 := by
    rw [show (t i)^3 = t i * (t i)^2 by ring]
    exact Nat.mul_le_mul_right ((t i)^2) hi₁
  have hlow : 428874 * 659 * (t i)^3 ≤ Erdos573.cycleExtremalNumber {3, 4} (n i) := by
    have h := hedge i
    exact (Nat.le_sub_of_add_le (by nlinarith)).trans h
  have hlowR : (428874 * 659 : ℝ) * (t i : ℝ)^3 ≤
      Erdos573.cycleExtremalNumber {3, 4} (n i) := by exact_mod_cast hlow
  have hsizeR : (n i : ℝ) ≤ (1307 * 659 : ℝ) * (t i : ℝ)^2 := by
    exact_mod_cast hsize i
  have hroot : Real.sqrt ((n i : ℝ)/2) ≤ Real.sqrt ((1307 * 659 : ℝ) / 2) * t i := by
    calc
      _ ≤ Real.sqrt (((1307 * 659 : ℝ) / 2) * (t i : ℝ)^2) :=
        Real.sqrt_le_sqrt (by linarith)
      _ = _ := by rw [Real.sqrt_mul (by positivity),Real.sqrt_sq htpos.le]
  have hb := pow_le_pow_left₀ (Real.sqrt_nonneg _) hroot 3
  rw [mul_pow] at hb
  have hupper := hE.trans_le (mul_le_mul_of_nonneg_left hb (by norm_num))
  rw [← mul_assoc] at hupper
  have bad := hlowR.trans hupper.le
  exact (not_le_of_gt strict_excess) (le_of_mul_le_mul_right bad (by positivity))

private instance prime659 : Fact (Nat.Prime 659) := ⟨by norm_num⟩
private abbrev K := ZMod 659

private def smallLabel (i : Fin 7) : K := (i.val + 1 : ℕ)

private def multiplierNat : Fin 47 → ℕ :=
  ![1, 14, 15, 24, 31, 41, 43, 44, 46, 47, 50, 53, 57, 63, 73, 80, 83, 85, 91,
    108, 118, 128, 136, 139, 145, 156, 173, 185, 190, 194, 196, 198, 207, 210,
    214, 223, 225, 232, 262, 274, 286, 296, 299, 302, 304, 323, 325]

private def multiplier (j : Fin 47) : K := (multiplierNat j : K)

private def signedMultiplier (j : Fin 47) (side : Bool) : K :=
  if side then -multiplier j else multiplier j

set_option maxRecDepth 4096 in
private theorem multiplier_bounds (j : Fin 47) : 1 ≤ multiplierNat j ∧ multiplierNat j ≤ 325 := by
  revert j
  decide

private theorem multiplier_val (j : Fin 47) : (multiplier j).val = multiplierNat j := by
  rw [multiplier, ZMod.val_natCast, Nat.mod_eq_of_lt]
  have hj := (multiplier_bounds j).2
  omega

private theorem multiplier_ne_zero (j : Fin 47) : multiplier j ≠ 0 := by
  intro h
  have he := congrArg ZMod.val h
  rw [multiplier_val,ZMod.val_zero] at he
  have hj := (multiplier_bounds j).1
  omega

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem multiplier_pow (j : Fin 47) : multiplier j ^ 94 = 1 := by
  revert j
  decide

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4096 in
private theorem multiplierNat_injective : Function.Injective multiplierNat := by
  decide

private theorem multiplier_injective : Function.Injective multiplier := by
  intro i j h
  apply multiplierNat_injective
  simpa only [multiplier_val] using congrArg ZMod.val h

private theorem multiplier_not_neg (i j : Fin 47) : multiplier i ≠ -multiplier j := by
  intro h
  have hadd : multiplier i + multiplier j = 0 := (eq_neg_iff_add_eq_zero).mp h
  have hcast : (↑(multiplierNat i + multiplierNat j) : K) = 0 := by
    simpa only [Nat.cast_add,multiplier] using hadd
  have hv := congrArg ZMod.val hcast
  rw [ZMod.val_natCast, ZMod.val_zero, Nat.mod_eq_of_lt] at hv
  · have hi := (multiplier_bounds i).1
    omega
  · have hi := (multiplier_bounds i).2
    have hj := (multiplier_bounds j).2
    omega

private theorem signedMultiplier_pow (j : Fin 47) (b : Bool) : signedMultiplier j b ^ 94 = 1 := by
  cases b
  · exact multiplier_pow j
  · change (-multiplier j)^94 = 1
    rw [Even.neg_pow (by decide : Even 94),multiplier_pow]

private theorem signedMultiplier_inj {j k : Fin 47} {b c : Bool}
    (h : signedMultiplier j b = signedMultiplier k c) : j = k ∧ b = c := by
  cases b <;> cases c
  · exact ⟨multiplier_injective h,rfl⟩
  · exact (multiplier_not_neg j k h).elim
  · exact (multiplier_not_neg k j h.symm).elim
  · exact ⟨multiplier_injective (neg_injective h),rfl⟩

private theorem smallLabel_ne_zero (i : Fin 7) : smallLabel i ≠ 0 := by
  revert i
  decide

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4096 in
private theorem smallLabel_pow_inj : Function.Injective (fun i => smallLabel i ^ 94) := by
  decide

/-- The multiplicative labels distinguish all signed leaf parts and their seven fibers. -/
private theorem signed_label_inj {j k : Fin 47} {b c : Bool} {u v : Fin 7}
    (h : signedMultiplier j b * smallLabel u = signedMultiplier k c * smallLabel v) :
    j = k ∧ b = c ∧ u = v := by
  have hp := congrArg (fun x : K => x^94) h
  simp only [mul_pow,signedMultiplier_pow,one_mul] at hp
  have huv := smallLabel_pow_inj hp
  subst v
  obtain ⟨hj,hb⟩ := signedMultiplier_inj (mul_right_cancel₀ (smallLabel_ne_zero u) h)
  exact ⟨hj,hb,rfl⟩

private abbrev FieldAt (h : ℕ) := GaloisField 659 (h + 1)
private abbrev Tail (h : ℕ) := Fin h → K

private noncomputable def coordinates (h : ℕ) : FieldAt h ≃ₗ[K] (Fin (h+1) → K) :=
  (Module.finBasisOfFinrankEq K (FieldAt h) (GaloisField.finrank 659 (by omega))).equivFun

private noncomputable def mark (h : ℕ) : FieldAt h →ₗ[K] K :=
  (LinearMap.proj 0).comp (coordinates h).toLinearMap

private noncomputable def lift (h : ℕ) (a : K) (v : Tail h) : FieldAt h :=
  (coordinates h).symm (Fin.cons a v)

private theorem mark_lift (h : ℕ) (a : K) (v : Tail h) : mark h (lift h a v) = a := by
  change (coordinates h ((coordinates h).symm (Fin.cons a v))) 0 = a
  rw [LinearEquiv.apply_symm_apply]
  simp

private theorem lift_inj {h : ℕ} {a b : K} {v w : Tail h} (he : lift h a v = lift h b w) :
    a = b ∧ v = w := by
  have hc := (coordinates h).symm.injective he
  constructor
  · simpa only [Fin.cons_zero] using congrFun hc (0 : Fin (h+1))
  · funext i
    simpa only [Fin.cons_succ] using congrFun hc i.succ

private theorem lift_ne_zero {h : ℕ} {a : K} {v : Tail h} (ha : a ≠ 0) :
    lift h a v ≠ 0 := by
  intro hz
  apply ha
  rw [← mark_lift h a v,hz,map_zero]

private noncomputable def splitField (h : ℕ) : K × Tail h ≃ FieldAt h :=
  (Fin.consEquiv (fun _ : Fin (h+1) => K)).trans (coordinates h).symm.toEquiv

private theorem mark_split (h : ℕ) (a : K × Tail h) : mark h (splitField h a) = a.1 :=
  mark_lift h a.1 a.2

private theorem field_card (h : ℕ) : Nat.card (FieldAt h) = 659 ^ (h + 1) :=
  GaloisField.card 659 (h+1) (by omega)

private def allowed (a : K) : Prop := 1 ≤ a.val ∧ a.val ≤ 10

private instance (a : K) : Decidable (allowed a) := inferInstanceAs (Decidable (_ ∧ _))

private theorem allowed_small (u : Fin 7) : allowed (smallLabel u) := by
  revert u
  decide

private theorem allowed_zero : ¬ allowed (0 : K) := by decide

private abbrev Root (h : ℕ) := {r : FieldAt h // r ≠ 0 ∧ ¬ allowed (mark h r)}

private abbrev Part := Fin 47 × Bool
private abbrev Leaf (h : ℕ) := Part × Fin 7 × Tail h
private abbrev Vertex (h : ℕ) := (Root h × FieldAt h) ⊕ (Leaf h × FieldAt h)

private theorem signedMultiplier_ne_zero (i : Fin 47) (b : Bool) : signedMultiplier i b ≠ 0 := by
  rcases b with _ | _
  · exact multiplier_ne_zero i
  · exact neg_ne_zero.mpr (multiplier_ne_zero i)

private theorem signedMultiplier_opposite {i j : Fin 47} {b c : Bool}
    (hi : i = j) (hb : b ≠ c) :
    signedMultiplier j c = -signedMultiplier i b := by
  subst j
  cases b <;> cases c <;> simp_all [signedMultiplier]

private noncomputable def leafValue {h : ℕ} (l : Leaf h) : FieldAt h :=
  lift h (smallLabel l.2.1) l.2.2

private noncomputable def factor {h : ℕ} (l : Leaf h) : FieldAt h :=
  algebraMap K (FieldAt h) (signedMultiplier l.1.1 l.1.2)

private theorem factor_ne_zero {h : ℕ} (l : Leaf h) : factor l ≠ 0 :=
  (map_ne_zero (algebraMap K (FieldAt h))).mpr (signedMultiplier_ne_zero l.1.1 l.1.2)

private theorem factor_opposite {h : ℕ} {l m : Leaf h} (hi : l.1.1 = m.1.1) (hb : l.1.2 ≠ m.1.2) :
    factor m = -factor l := by
  simp only [factor,signedMultiplier_opposite hi hb,map_neg]

private noncomputable def leafSlope {h : ℕ} (l : Leaf h) : FieldAt h :=
  (factor l * leafValue l)⁻¹

private theorem value_ne_zero {h : ℕ} (l : Leaf h) : leafValue l ≠ 0 :=
  lift_ne_zero (smallLabel_ne_zero l.2.1)

private theorem leafSlope_ne_zero {h : ℕ} (l : Leaf h) : leafSlope l ≠ 0 :=
  inv_ne_zero (mul_ne_zero (factor_ne_zero l) (value_ne_zero l))

private theorem value_allowed {h : ℕ} (l : Leaf h) : allowed (mark h (leafValue l)) := by
  rw [leafValue,mark_lift]
  exact allowed_small _

private theorem mark_factor_mul {h : ℕ} (l : Leaf h) (x : FieldAt h) :
    mark h (factor l * x) = signedMultiplier l.1.1 l.1.2 * mark h x := by
  rw [factor,← Algebra.smul_def,map_smul]
  rfl

private theorem leafSlope_inj {h : ℕ} : Function.Injective (@leafSlope h) := by
  intro l m he
  have ht : factor l * leafValue l = factor m * leafValue m := inv_injective he
  have hmark := congrArg (mark h) ht
  simp only [mark_factor_mul,leafValue,mark_lift] at hmark
  obtain ⟨hj,hb,hu⟩ := signed_label_inj hmark
  have hf : factor l = factor m := by simp [factor,hj,hb]
  rw [← hf] at ht
  have hv := mul_left_cancel₀ (factor_ne_zero l) ht
  have htail := (lift_inj hv).2
  exact Prod.ext (Prod.ext hj hb) (Prod.ext hu htail)

private def opposite {h : ℕ} (l m : Leaf h) : Prop :=
  l.1.1 = m.1.1 ∧ l.1.2 ≠ m.1.2

private theorem opposite_symm {h : ℕ} {l m : Leaf h} (hm : opposite l m) : opposite m l :=
  ⟨hm.1.symm,Ne.symm hm.2⟩

private theorem opposite_same {h : ℕ} {l m n : Leaf h}
    (hl : opposite l m) (hr : opposite m n) : l.1 = n.1 := by
  have hb : l.1.2 = n.1.2 := by
    revert hl hr
    unfold opposite
    cases l.1.2 <;> cases m.1.2 <;> cases n.1.2 <;> simp
  exact Prod.ext (hl.1.trans hr.1) hb

private noncomputable def AdjAt {h : ℕ} : Vertex h → Vertex h → Prop
  | .inl (r,x), .inr (l,y) => y = x + r.val⁻¹ * leafSlope l
  | .inr (l,y), .inl (r,x) => y = x + r.val⁻¹ * leafSlope l
  | .inr (l,y), .inr (m,z) => opposite l m ∧
      allowed (smallLabel l.2.1 + smallLabel m.2.1) ∧
      z = y + factor l * leafSlope l * leafSlope m
  | .inl _, .inl _ => False

private theorem AdjAt_symm {h : ℕ} : ∀ {v w : Vertex h}, AdjAt v w → AdjAt w v := by
  intro v w hadj
  rcases v with ⟨r,x⟩ | ⟨l,y⟩ <;> rcases w with ⟨s,z⟩ | ⟨m,z⟩
  · exact hadj
  · exact hadj
  · exact hadj
  · obtain ⟨ho,ha,he⟩ := hadj
    refine ⟨opposite_symm ho,by simpa only [add_comm] using ha,?_⟩
    rw [factor_opposite ho.1 ho.2,he]
    ring

private noncomputable def graphAt (h : ℕ) : SimpleGraph (Vertex h) where
  Adj := AdjAt
  symm := ⟨fun _ _ => AdjAt_symm⟩
  loopless := by
    constructor
    rintro (⟨r,x⟩ | ⟨l,y⟩) hv
    · exact hv
    · exact hv.1.2 rfl

private theorem root_leaf_triangle {h : ℕ} (r : Root h) (l m : Leaf h) (x y z : FieldAt h)
    (hxy : AdjAt (.inl (r,x)) (.inr (l,y))) (hxz : AdjAt (.inl (r,x)) (.inr (m,z)))
    (hyz : AdjAt (.inr (l,y)) (.inr (m,z))) : False := by
  change y = x + r.val⁻¹ * leafSlope l at hxy
  change z = x + r.val⁻¹ * leafSlope m at hxz
  have ho := hyz.1
  have ha := hyz.2.1
  have he := hyz.2.2
  have hd : r.val⁻¹ * leafSlope m - r.val⁻¹ * leafSlope l =
      factor l * leafSlope l * leafSlope m := by linear_combination he + hxy - hxz
  have hcancel : r.val⁻¹ * ((leafSlope l)⁻¹ - (leafSlope m)⁻¹) = factor l := by
    calc
      _ = (r.val⁻¹ * leafSlope m - r.val⁻¹ * leafSlope l) *
          (leafSlope l)⁻¹ * (leafSlope m)⁻¹ := by
            field_simp [leafSlope_ne_zero]
      _ = _ := by rw [hd]; field_simp [leafSlope_ne_zero]
  simp only [leafSlope,inv_inv,factor_opposite ho.1 ho.2] at hcancel
  have hone : r.val⁻¹ * (leafValue l + leafValue m) = 1 := by
    apply mul_left_cancel₀ (factor_ne_zero l)
    linear_combination hcancel
  have hr : r.val = leafValue l + leafValue m := by
    apply mul_left_cancel₀ (inv_ne_zero r.property.1)
    rw [inv_mul_cancel₀ r.property.1,hone]
  apply r.property.2
  simpa only [hr,map_add,leafValue,mark_lift] using ha

private theorem triangle_free {h : ℕ} {u v w : Vertex h}
    (huv : AdjAt u v) (huw : AdjAt u w) (hvw : AdjAt v w) : False := by
  rcases u with ⟨r,x⟩ | ⟨l,x⟩ <;> rcases v with ⟨s,y⟩ | ⟨m,y⟩ <;>
    rcases w with ⟨t,z⟩ | ⟨n,z⟩
  · exact huv
  · exact huv
  · exact huw
  · exact root_leaf_triangle r m n x y z huv huw hvw
  · exact hvw
  · exact root_leaf_triangle s l n y x z huv hvw huw
  · exact root_leaf_triangle t l m z x y huw hvw huv
  · have he := congrArg Prod.snd (opposite_same huv.1 hvw.1)
    exact huw.1.2 he

private theorem common_line_unique {F : Type*} [Field F] {a b x y u v z w : F}
    (hne : ¬ (a = b ∧ x = y))
    (hzu : z = x + a * u) (hzv : z = y + b * u)
    (hwu : w = x + a * v) (hwv : w = y + b * v) : u = v ∧ z = w := by
  have hab : a ≠ b := by
    intro he
    apply hne
    refine ⟨he,?_⟩
    rw [he] at hzu
    linear_combination hzv - hzu
  have hp : (a-b)*(u-v) = 0 := by linear_combination hzv - hzu + hwu - hwv
  have huv := sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left (sub_ne_zero.mpr hab))
  subst v
  exact ⟨rfl,hzu.trans hwu.symm⟩

private theorem root_neighbors_unique {h : ℕ} {r s : Root h} {x y : FieldAt h}
    (hne : (r,x) ≠ (s,y)) {v w : Vertex h}
    (h₁ : AdjAt (.inl (r,x)) v) (h₂ : AdjAt (.inl (s,y)) v)
    (h₃ : AdjAt (.inl (r,x)) w) (h₄ : AdjAt (.inl (s,y)) w) :
    v = w := by
  rcases v with ⟨t,z⟩ | ⟨l,z⟩
  · exact h₁.elim
  rcases w with ⟨t,w⟩ | ⟨m,w⟩
  · exact h₃.elim
  have hdiff : ¬ (r.val⁻¹ = s.val⁻¹ ∧ x = y) := by
    rintro ⟨hr,hxy⟩
    exact hne (Prod.ext (Subtype.ext (inv_injective hr)) hxy)
  obtain ⟨hs,hi⟩ := common_line_unique hdiff h₁ h₂ h₃ h₄
  exact congrArg Sum.inr (Prod.ext (leafSlope_inj hs) hi)

private theorem divisor_slope {h : ℕ} {l m : Leaf h} (ho : opposite l m) :
    -factor l * leafSlope m = (leafValue m)⁻¹ := by
  rw [← factor_opposite ho.1 ho.2,leafSlope,mul_inv_rev]
  field_simp [factor_ne_zero m]

private noncomputable def lineOf {h : ℕ} (l : Leaf h) :
    Vertex h → FieldAt h × FieldAt h
  | .inl (r,z) => (r.val⁻¹,z)
  | .inr (m,z) => (-factor l * leafSlope m,z)

private theorem factor_same {h : ℕ} {l m : Leaf h} (he : l.1 = m.1) :
    factor l = factor m := by
  unfold factor
  rw [he]

private theorem rowOnLine {h : ℕ} {l m : Leaf h} (hp : l.1 = m.1)
    {y : FieldAt h} {w : Vertex h} (ha : AdjAt (.inr (m,y)) w) :
    (lineOf l w).2 = y + leafSlope m * (-(lineOf l w).1) := by
  rcases w with ⟨r,z⟩ | ⟨s,z⟩
  · change y = z + r.val⁻¹ * leafSlope m at ha
    change z = y + leafSlope m * (-(r.val⁻¹))
    linear_combination -ha
  · have hz := ha.2.2
    change z = y + leafSlope m * (-(-factor l * leafSlope s))
    rw [factor_same hp]
    linear_combination hz

private theorem no_root_leaf_line_eq {h : ℕ} {l m : Leaf h} (ho : opposite l m)
    (r : Root h) (he : r.val⁻¹ = -factor l * leafSlope m) : False := by
  rw [divisor_slope ho] at he
  have hr := inv_injective he
  exact r.property.2 (hr ▸ value_allowed m)

private theorem lineOf_inj {h : ℕ} {l : Leaf h} {x : FieldAt h} {v w : Vertex h}
    (hv : AdjAt (.inr (l,x)) v) (hw : AdjAt (.inr (l,x)) w)
    (he : lineOf l v = lineOf l w) : v = w := by
  have ht := congrArg Prod.fst he
  have hy := congrArg Prod.snd he
  rcases v with ⟨r,y⟩ | ⟨m,y⟩ <;> rcases w with ⟨s,z⟩ | ⟨n,z⟩
  · exact congrArg Sum.inl (Prod.ext (Subtype.ext (inv_injective ht)) hy)
  · exact (no_root_leaf_line_eq hw.1 r ht).elim
  · exact (no_root_leaf_line_eq hv.1 s ht.symm).elim
  · change -factor l * leafSlope m = -factor l * leafSlope n at ht
    have hs := mul_left_cancel₀ (neg_ne_zero.mpr (factor_ne_zero l)) ht
    exact congrArg Sum.inr (Prod.ext (leafSlope_inj hs) hy)

private theorem leaf_neighbors_unique {h : ℕ} {l m : Leaf h} (hp : l.1 = m.1)
    {x y : FieldAt h} (hne : (l,x) ≠ (m,y)) {v w : Vertex h}
    (h₁ : AdjAt (.inr (l,x)) v) (h₂ : AdjAt (.inr (m,y)) v)
    (h₃ : AdjAt (.inr (l,x)) w) (h₄ : AdjAt (.inr (m,y)) w) : v = w := by
  have hdiff : ¬ (leafSlope l = leafSlope m ∧ x = y) := by
    rintro ⟨hl,hx⟩
    exact hne (Prod.ext (leafSlope_inj hl) hx)
  obtain ⟨hf,hs⟩ := common_line_unique hdiff (rowOnLine rfl h₁) (rowOnLine hp h₂)
    (rowOnLine rfl h₃) (rowOnLine hp h₄)
  exact lineOf_inj h₁ h₃ (Prod.ext (neg_injective hf) hs)

private def tag {h : ℕ} : Vertex h → Option Part
  | .inl _ => none
  | .inr (l,_) => some l.1

private theorem common_neighbor_unique {h : ℕ} {u w v z : Vertex h}
    (htag : tag u = tag w) (hne : u ≠ w)
    (huv : AdjAt u v) (hwv : AdjAt w v) (huz : AdjAt u z) (hwz : AdjAt w z) :
    v = z := by
  rcases u with ⟨r,x⟩ | ⟨l,x⟩ <;> rcases w with ⟨s,y⟩ | ⟨m,y⟩
  · exact root_neighbors_unique (fun he => hne (congrArg Sum.inl he)) huv hwv huz hwz
  · simp [tag] at htag
  · simp [tag] at htag
  · exact leaf_neighbors_unique (Option.some.inj htag)
      (fun he => hne (congrArg Sum.inr he)) huv hwv huz hwz

private theorem tag_across_leaf {h : ℕ} {l : Leaf h} {y : FieldAt h}
    {v z : Vertex h} (hv : AdjAt (.inr (l,y)) v) (hz : AdjAt (.inr (l,y)) z)
    (hne : tag v ≠ none) (hne' : tag z ≠ none) : tag v = tag z := by
  rcases v with r | ⟨m,x⟩ <;> rcases z with s | ⟨n,w⟩
  · exact (hne rfl).elim
  · exact (hne rfl).elim
  · exact (hne' rfl).elim
  · exact congrArg some (opposite_same (opposite_symm hv.1) hz.1)

private theorem cycle_tag {h : ℕ} {u v w z : Vertex h}
    (huv : AdjAt u v) (hvw : AdjAt v w) (hwz : AdjAt w z) (hzu : AdjAt z u) :
    tag u = tag w ∨ tag v = tag z := by
  rcases u with r | ⟨l,x⟩ <;> rcases w with s | ⟨m,y⟩
  · exact Or.inl rfl
  · right
    apply tag_across_leaf (AdjAt_symm hvw) hwz
    · rintro hv
      cases v with
      | inl => exact huv
      | inr a => rcases a with ⟨a,b⟩; simp [tag] at hv
    · rintro hz
      cases z with
      | inl => exact hzu
      | inr a => rcases a with ⟨a,b⟩; simp [tag] at hz
  · right
    apply tag_across_leaf huv (AdjAt_symm hzu)
    · rintro hv
      cases v with
      | inl => exact hvw
      | inr a => rcases a with ⟨a,b⟩; simp [tag] at hv
    · rintro hz
      cases z with
      | inl => exact hwz
      | inr a => rcases a with ⟨a,b⟩; simp [tag] at hz
  · rcases v with t | ⟨n,a⟩
    · rcases z with t' | ⟨n',b⟩
      · exact Or.inr rfl
      · exact Or.inl (congrArg some (opposite_same (AdjAt_symm hzu).1 (AdjAt_symm hwz).1))
    · exact Or.inl (congrArg some (opposite_same huv.1 hvw.1))

private theorem quadrilateral_free {h : ℕ} {u v w z : Vertex h}
    (huw : u ≠ w) (hvz : v ≠ z)
    (huv : AdjAt u v) (hvw : AdjAt v w) (hwz : AdjAt w z) (hzu : AdjAt z u) :
    False := by
  rcases cycle_tag huv hvw hwz hzu with htag | htag
  · exact hvz (common_neighbor_unique htag huw huv (AdjAt_symm hvw) (AdjAt_symm hzu) hwz)
  · exact huw (common_neighbor_unique htag hvz (AdjAt_symm huv) hzu hvw (AdjAt_symm hwz))

private theorem graphAt_free (h k : ℕ) (hk : k ∈ ({3,4} : Set ℕ)) :
    (cycleGraph k).Free (graphAt h) := by
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hk
  rcases hk with rfl | rfl <;> rintro ⟨c⟩
  · exact triangle_free
      (c.toHom.map_adj (show (cycleGraph 3).Adj 0 1 by decide))
      (c.toHom.map_adj (show (cycleGraph 3).Adj 0 2 by decide))
      (c.toHom.map_adj (show (cycleGraph 3).Adj 1 2 by decide))
  · exact quadrilateral_free
      (fun he => (show (0 : Fin 4) ≠ 2 by decide) (c.injective he))
      (fun he => (show (1 : Fin 4) ≠ 3 by decide) (c.injective he))
      (c.toHom.map_adj (show (cycleGraph 4).Adj 0 1 by decide))
      (c.toHom.map_adj (show (cycleGraph 4).Adj 1 2 by decide))
      (c.toHom.map_adj (show (cycleGraph 4).Adj 2 3 by decide))
      (c.toHom.map_adj (show (cycleGraph 4).Adj 3 0 by decide))

private abbrev LabelPair := {uv : Fin 7 × Fin 7 // allowed (smallLabel uv.1 + smallLabel uv.2)}
private abbrev RootEdge (h : ℕ) := Root h × Leaf h × FieldAt h
private abbrev LeafEdge (h : ℕ) := Fin 47 × LabelPair × Tail h × Tail h × FieldAt h

private noncomputable def rootEdge {h : ℕ} (r : Root h) (l : Leaf h) (x : FieldAt h) :
    (graphAt h).edgeSet :=
  ⟨s(.inl (r,x), .inr (l,x + r.val⁻¹ * leafSlope l)),rfl⟩

private noncomputable def pairedEdge {h : ℕ} (j : Fin 47) (uv : LabelPair)
    (a b : Tail h) (y : FieldAt h) : (graphAt h).edgeSet :=
  let l : Leaf h := ((j,false),uv.val.1,a)
  let m : Leaf h := ((j,true),uv.val.2,b)
  ⟨s(.inr (l,y), .inr (m,y + factor l * leafSlope l * leafSlope m)),
    ⟨⟨rfl,Bool.false_ne_true⟩,uv.property,rfl⟩⟩

private noncomputable def edgeOf {h : ℕ} : RootEdge h ⊕ LeafEdge h → (graphAt h).edgeSet
  | .inl (r,l,x) => rootEdge r l x
  | .inr (j,uv,a,b,y) => pairedEdge j uv a b y

private theorem edgeOf_inj {h : ℕ} : Function.Injective (@edgeOf h) := by
  intro x y he
  have hh := congrArg Subtype.val he
  rcases x with ⟨r,l,x₀⟩ | ⟨i,p,a,b,x₀⟩ <;> rcases y with ⟨s,m,y₀⟩ | ⟨j,q,c,d,y₀⟩
  · simp only [edgeOf,rootEdge,Sym2.eq_iff,Sum.inl.injEq,Sum.inr.injEq,
      Sum.inl_ne_inr,Prod.mk.injEq,false_and,or_false] at hh
    obtain ⟨⟨hr,hx⟩,hl,_⟩ := hh
    subst s; subst y₀; subst m
    rfl
  · simp [edgeOf,rootEdge,pairedEdge] at hh
  · simp [edgeOf,rootEdge,pairedEdge] at hh
  · simp only [edgeOf,pairedEdge,Sym2.eq_iff,Sum.inr.injEq] at hh
    rcases hh with ⟨hpos,hneg⟩ | ⟨hswap,_⟩
    · have hi : i = j := congrArg (fun v : Leaf h × FieldAt h => v.1.1.1) hpos
      have hu : p.val.1 = q.val.1 := congrArg (fun v : Leaf h × FieldAt h => v.1.2.1) hpos
      have hv : p.val.2 = q.val.2 := congrArg (fun v : Leaf h × FieldAt h => v.1.2.1) hneg
      have ha : a = c := congrArg (fun v : Leaf h × FieldAt h => v.1.2.2) hpos
      have hb : b = d := congrArg (fun v : Leaf h × FieldAt h => v.1.2.2) hneg
      have hx : x₀ = y₀ := congrArg Prod.snd hpos
      have hp : p = q := Subtype.ext (Prod.ext hu hv)
      subst j; subst q; subst c; subst d; subst y₀
      rfl
    · exact (Bool.false_ne_true (congrArg (fun v : Leaf h × FieldAt h => v.1.1.2) hswap)).elim

private theorem edgeOf_surj {h : ℕ} : Function.Surjective (@edgeOf h) := by
  rintro ⟨e,he⟩
  induction e using Sym2.inductionOn with
  | _ v w =>
    change AdjAt v w at he
    rcases v with ⟨r,x⟩ | ⟨l,y⟩ <;> rcases w with ⟨s,z⟩ | ⟨m,z⟩
    · exact he.elim
    · refine ⟨.inl (r,m,x),Subtype.ext ?_⟩
      have hz : z = x + r.val⁻¹ * leafSlope m := he
      change _ = s(Sum.inl (r,x),Sum.inr (m,z))
      exact Sym2.eq_iff.mpr (Or.inl ⟨rfl,congrArg (fun v => Sum.inr (m,v)) hz.symm⟩)
    · refine ⟨.inl (s,l,z),Subtype.ext ?_⟩
      have hy : y = z + s.val⁻¹ * leafSlope l := he
      change _ = s(Sum.inr (l,y),Sum.inl (s,z))
      exact Sym2.eq_iff.mpr (Or.inr ⟨rfl,congrArg (fun v => Sum.inr (l,v)) hy.symm⟩)
    · rcases l with ⟨⟨i,b⟩,u,a⟩
      rcases m with ⟨⟨j,c⟩,v,d⟩
      have hij : i = j := he.1.1
      have hbc : b ≠ c := he.1.2
      subst j
      cases b <;> cases c
      · exact (hbc rfl).elim
      · refine ⟨.inr (i,⟨(u,v),he.2.1⟩,a,d,y),Subtype.ext ?_⟩
        have hz := he.2.2
        change _ = s(Sum.inr (((i,false),u,a),y),Sum.inr (((i,true),v,d),z))
        exact Sym2.eq_iff.mpr (Or.inl ⟨rfl,congrArg (fun w => Sum.inr (((i,true),v,d),w)) hz.symm⟩)
      · have hrev := AdjAt_symm he
        refine ⟨.inr (i,⟨(v,u),hrev.2.1⟩,d,a,z),Subtype.ext ?_⟩
        have hy := hrev.2.2
        change _ = s(Sum.inr (((i,true),u,a),y),Sum.inr (((i,false),v,d),z))
        exact Sym2.eq_iff.mpr (Or.inr ⟨rfl,congrArg (fun w => Sum.inr (((i,true),u,a),w)) hy.symm⟩)
      · exact (hbc rfl).elim

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem outside_card : Nat.card {a : K // ¬ allowed a} = 649 := by
  rw [Nat.card_eq_fintype_card]
  decide

set_option maxRecDepth 4096 in
private theorem allowed_pair_card : Nat.card LabelPair = 39 := by
  rw [Nat.card_eq_fintype_card]
  decide

private theorem tail_card (h : ℕ) : Nat.card (Tail h) = 659 ^ h := by
  rw [Nat.card_eq_fintype_card,Fintype.card_fun,Fintype.card_fin,ZMod.card]

private theorem root_card (h : ℕ) : Nat.card (Root h) + 1 = 649 * 659 ^ h := by
  classical
  let R₀ := {r : FieldAt h // ¬ allowed (mark h r)}
  let origin : R₀ := ⟨0,by simpa only [map_zero] using allowed_zero⟩
  let e : {a : K // ¬ allowed a} × Tail h ≃ R₀ :=
    Equiv.prodSubtypeFstEquivSubtypeProd.symm.trans
      ((splitField h).subtypeEquiv (fun a => by rw [mark_split]))
  let e' : {r : R₀ // r ≠ origin} ≃ Root h :=
    (Equiv.subtypeEquivRight (fun r => show r ≠ origin ↔ r.val ≠ 0 by
      constructor
      · exact fun hr hz => hr (Subtype.ext hz)
      · exact fun hr hz => hr (congrArg Subtype.val hz))).trans
      ((Equiv.subtypeSubtypeEquivSubtypeInter (fun r : FieldAt h => ¬ allowed (mark h r))
        (fun r => r ≠ 0)).trans (Equiv.subtypeEquivRight (fun _ => and_comm)))
  calc
    _ = Nat.card (Option (Root h)) := by
      letI : Fintype (Root h) := Fintype.ofFinite _
      simp only [Nat.card_eq_fintype_card,Fintype.card_option]
    _ = Nat.card R₀ := Nat.card_congr ((Equiv.optionCongr e'.symm).trans (Equiv.optionSubtypeNe origin))
    _ = _ := by rw [← Nat.card_congr e,Nat.card_prod,tail_card,outside_card]

private def scale (h : ℕ) : ℕ := 659 ^ h

private theorem scale_pos (h : ℕ) : 0 < scale h := by
  unfold scale
  positivity

private theorem field_card_scale (h : ℕ) : Nat.card (FieldAt h) = 659 * scale h := by
  rw [field_card,pow_succ,scale,mul_comm]

private theorem tail_card_scale (h : ℕ) : Nat.card (Tail h) = scale h := tail_card h

private theorem bool_card : Nat.card Bool = 2 := by simp [Nat.card_eq_fintype_card]

private theorem leaf_card (h : ℕ) : Nat.card (Leaf h) = 658 * scale h := by
  simp only [Leaf,Part,Nat.card_prod,Nat.card_fin,bool_card,tail_card_scale]
  ring

private theorem vertex_card (h : ℕ) :
    Nat.card (Vertex h) = Nat.card (Root h) * (659 * scale h) +
      (658 * scale h) * (659 * scale h) := by
  change Nat.card ((Root h × FieldAt h) ⊕ (Leaf h × FieldAt h)) = _
  rw [Nat.card_sum,Nat.card_prod,Nat.card_prod,leaf_card,field_card_scale]

private theorem vertex_grows (h : ℕ) : scale h ≤ Nat.card (Vertex h) := by
  have hz := scale_pos h
  rw [vertex_card]
  have hm := Nat.mul_le_mul_left (658 * scale h) (show 1 ≤ 659 * scale h by omega)
  rw [mul_one] at hm
  omega

private theorem vertex_bound (h : ℕ) : Nat.card (Vertex h) ≤ 1307 * 659 * (scale h)^2 := by
  have hr : Nat.card (Root h) + 1 = 649 * scale h := root_card h
  have hc : Nat.card (Vertex h) + 659 * scale h = 1307 * 659 * (scale h)^2 := by
    rw [vertex_card]
    calc
      _ = (Nat.card (Root h) + 1) * (659 * scale h) +
          (658 * scale h) * (659 * scale h) := by ring
      _ = _ := by rw [hr]; ring
  omega

private theorem edge_count (h : ℕ) :
    Nat.card (graphAt h).edgeSet = 428875 * 659 * (scale h)^3 - 658 * 659 * (scale h)^2 := by
  have he := Nat.card_congr (Equiv.ofBijective (@edgeOf h) ⟨edgeOf_inj,edgeOf_surj⟩)
  have hr : Nat.card (Root h) + 1 = 649 * scale h := root_card h
  have hc : Nat.card (graphAt h).edgeSet + 658 * 659 * (scale h)^2 = 428875 * 659 * (scale h)^3 := by
    rw [← he]
    simp only [RootEdge,LeafEdge,Leaf,Part,Nat.card_sum,Nat.card_prod,Nat.card_fin,bool_card,
      allowed_pair_card,tail_card_scale,field_card_scale]
    calc
      _ = (Nat.card (Root h) + 1) * (658 * scale h * (659 * scale h)) +
          47 * 39 * (scale h)^2 * (659 * scale h) := by ring
      _ = _ := by rw [hr]; ring
  omega

private theorem construction_bounds (h : ℕ) :
    428875 * 659 * (scale h)^3 - 658 * 659 * (scale h)^2 ≤
      Erdos573.cycleExtremalNumber {3,4} (Nat.card (Vertex h)) := by
  classical
  letI : Fintype (Vertex h) := Fintype.ofFinite (Vertex h)
  have hE := extremal_ge (graphAt h) (graphAt_free h)
  rwa [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card,
    edge_count, ← Nat.card_eq_fintype_card] at hE

theorem counterexample : ¬ (type_of% @Erdos573.erdos_573) := by
  have ht : Tendsto scale atTop atTop := tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < (659 : ℕ))
  have hn : Tendsto (fun h => Nat.card (Vertex h)) atTop atTop :=
    tendsto_atTop_mono vertex_grows ht
  exact disproved_by_counts (fun h => Nat.card (Vertex h)) scale hn ht vertex_bound construction_bounds

end OMA.Erdos573Proof

theorem OMA.disproof : ¬ (type_of% @Erdos573.erdos_573) := OMA.Erdos573Proof.counterexample
