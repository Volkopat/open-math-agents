import FormalConjectures.Paper.BurningNumberConjecture
import Mathlib

/-!
A proof of the asymptotic burning-number bound of Norin and Turcotte.

A diameter path gives each vertex of a tree a position and a height.
Counting vertices above the path gives one- and two-ball covers of small
pieces. For fixed nonnegative prices on radius intervals, choose the
radius that minimises cumulative price divided by squared radius. The
resulting cover has bounded price and uses a bounded number of balls.
Prices depend on the bins already used. At each step we remove the chosen
fragment and bound the increase in the sum of squared bin overloads. A final
ball covers the remainder. The bin counts give distinct ignition rounds.
-/

namespace BurningNumberConjecture.Proof
section
open SimpleGraph
lemma path_dist {V : Type} {G : SimpleGraph V} (hG : G.IsTree)
    {a b : V} {p : G.Walk a b} (hp : p.IsPath) : p.length = G.dist a b := by
  obtain ⟨q,hq,e⟩ := hG.connected.exists_path_of_dist a b
  rwa [(hG.existsUnique_path _ _).unique hp hq]

end

section
open SimpleGraph

variable {V : Type} [Fintype V] {G : SimpleGraph V} {x y : V}

def Tag (G : SimpleGraph V) (x y v : V) (d i h : ℕ) : Prop :=
  i ≤ d ∧ G.dist x v = i+h ∧ G.dist y v = d-i+h

lemma Tag.unique {v : V} {d i h j k : ℕ} (a : Tag G x y v d i h)
    (b : Tag G x y v d j k) : (i,h) = (j,k) := by unfold Tag at *; congr 1 <;> omega

lemma tag_getVert (ht : G.IsTree) {p : G.Walk x y} (hp : p.IsPath) {i : ℕ} (hi : i ≤ p.length) :
    Tag G x y (p.getVert i) p.length i 0 := by
  simpa [Tag,hi,Walk.take_length,Walk.drop_length,Nat.min_eq_left hi] using
    And.intro (path_dist ht (hp.take i)).symm (path_dist ht (hp.drop i).reverse).symm

/-- A point attaching to a diameter path at index i and height h has
witnesses of all heights below h at that same index. -/
theorem coordinates (ht : G.IsTree) (p : G.Walk x y) (hp : p.IsPath) :
    ∀ v, ∃ i h, Tag G x y v p.length i h ∧ G.dist (p.getVert i) v ≤ h ∧
      ∀ k ≤ h, ∃ w, Tag G x y w p.length i k := by
  classical
  intro v
  obtain ⟨q,hq⟩ := ht.connected.exists_isPath v x
  induction q with
  | @nil u =>
    have tag := tag_getVert ht hp (i := 0) (by omega)
    simp only [Walk.getVert_zero] at tag
    exact ⟨0,0,tag,by simp,fun k hk => ⟨u,by simpa [show k=0 by omega] using tag⟩⟩
  | @cons v u x e q ih =>
    by_cases hv : v ∈ p.support
    · obtain ⟨i,eq,hi⟩ := Walk.mem_support_iff_exists_getVert.mp hv
      have tag := tag_getVert ht hp hi
      rw [eq] at tag
      exact ⟨i,0,tag,by simp [eq],fun k hk => ⟨v,by simpa [show k=0 by omega] using tag⟩⟩
    obtain ⟨hq',fresh⟩ := (Walk.cons_isPath_iff _ _).mp hq
    obtain ⟨i,h,⟨hi,hx,hy⟩,hd,chain⟩ := ih p hp hq'
    let b := (p.reverse.append q.reverse).toPath
    have hb := b.prop.concat (fun hw => ?_) e.symm
    case refine_1 =>
      have := (p.reverse.append q.reverse).support_toPath_subset_support hw
      simp_all [Walk.mem_support_append_iff]
    have tag : Tag G x y v p.length i (h+1) := by
      have h1 := path_dist ht hq.reverse
      have h2 := path_dist ht hq'.reverse
      have h3 := path_dist ht hb
      simp only [Walk.length_reverse,Walk.length_cons,Walk.length_concat,path_dist ht b.prop] at h1 h2 h3
      unfold Tag; omega
    exact ⟨i,h+1,tag,ht.connected.dist_triangle.trans (Nat.add_le_add hd
      (dist_eq_one_iff_adj.mpr e.symm).le),fun k hk => by
        by_cases eq : k=h+1
        · exact ⟨_,eq ▸ tag⟩
        · exact chain k (by omega)⟩

end


section
open SimpleGraph BurningNumberConjecture

/- Rounding a position on a path down to a vertex costs at most one round.
The scheduler restores this round when it passes from cost to graph distance. -/
variable {V : Type} {T : SimpleGraph V}

noncomputable def cost (T : SimpleGraph V) (u v : V) : ℝ := (T.dist u v : ℝ)-1

theorem centre_on_walk {a b : V} (p : T.Walk a b) (hc : T.Connected) (x : ℝ) :
    ∃ c : V, ∀ j : ℕ, ∀ w : V,
      cost T c w ≤ |x - j| + T.dist (p.getVert j) w := by
  have seg {i j : ℕ} (h : i ≤ j) : (T.dist (p.getVert i) (p.getVert j) : ℝ) ≤ (j : ℝ)-i := by
    let q := (p.drop i).take (j-i)
    have eq : (p.drop i).getVert (j-i) = p.getVert j := by rw [p.drop_getVert, Nat.add_sub_of_le h]
    rw [← Nat.cast_sub h, ← eq]
    exact_mod_cast (dist_le q).trans (show q.length ≤ j-i by simp [q, Walk.take_length])
  have move (i j : ℕ) (v : V) :
      (T.dist (p.getVert i) v : ℝ) ≤ |(i : ℝ)-j| + T.dist (p.getVert j) v := by
    have dom (a b : ℕ) : (T.dist (p.getVert a) (p.getVert b) : ℝ) ≤ |(a:ℝ)-b| := by
      wlog h : a ≤ b generalizing a b
      · rw [SimpleGraph.dist_comm,abs_sub_comm]; exact this _ _ (by omega)
      rw [abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast h)),neg_sub]
      exact seg h
    exact (Nat.cast_le (α := ℝ)).mpr hc.dist_triangle |>.trans (by push_cast; linarith [dom i j])
  let n := ⌊x⌋₊
  refine ⟨p.getVert n, fun j w => ?_⟩
  have step := move n j w
  change (T.dist (p.getVert n) w : ℝ)-1 ≤ _
  by_cases hx : 0 ≤ x
  · have lo : (n:ℝ) ≤ x := Nat.floor_le hx
    have hi : x < (n:ℝ)+1 := Nat.lt_floor_add_one x
    grind [abs_eq_max_neg]
  · have hn : n = 0 := Nat.floor_eq_zero.mpr (by linarith)
    rw [hn,Nat.cast_zero] at step
    rw [hn]
    grind [abs_eq_max_neg]

end

section
open SimpleGraph

/- The physical parameters needed to apply the normalized local profile. -/
def HasPieceProfiles {V W : Type} (dist : W → V → ℝ) (l L : ℝ) : Prop :=
  ∃ m B : ℝ, 0 ≤ m ∧ m ≤ l/2 ∧ B ≤ 2*m ∧ 2*m+B = L ∧
    (∃ u : W, ∀ v, dist u v ≤ B) ∧
    (∀ t ≥ m, ∀ s ≥ 0, B ≤ s+t →
      ∃ u w : W, ∀ v, dist u v ≤ s ∨ dist w v ≤ t)

end

section
open SimpleGraph

inductive Branch {V : Type} (G : SimpleGraph V) : V → Type
  | root (v : V) : Branch G v
  | join {u v : V} (e : G.Adj u v) (a : Branch G u) (b : Branch G v) : Branch G u

variable {V : Type} {G : SimpleGraph V} {r : V}

def Branch.size : {r : V} → Branch G r → ℕ
  | _, .root _ => 0
  | _, .join _ a b => a.size+b.size+1

def Branch.vertices [DecidableEq V] : {r : V} → Branch G r → Finset V
  | r, .root _ => {r}
  | _, .join _ a b => a.vertices ∪ b.vertices

lemma Branch.root_mem [DecidableEq V] (t : Branch G r) : r ∈ t.vertices := by
  induction t <;> simp_all [vertices]

lemma Branch.card [DecidableEq V] (t : Branch G r) : t.vertices.card ≤ t.size+1 := by
  induction t with
  | root => simp [vertices,size]
  | join e a b ha hb =>
    exact (Finset.card_union_le ..).trans (by dsimp [size]; omega)

lemma Branch.connected [DecidableEq V] (t : Branch G r) :
    (G.induce (↑t.vertices : Set V)).Connected := by
  induction t with
  | root v => rw [connected_iff_exists_forall_reachable]
              refine ⟨⟨v,by simp [vertices]⟩,fun ⟨w,hw⟩ => ?_⟩
              obtain rfl : w = v := by simpa [vertices] using hw
              exact Reachable.rfl
  | join e a b ha hb =>
    rw [show (↑(join e a b).vertices : Set V) = ↑a.vertices ∪ ↑b.vertices by ext; simp [vertices]]
    exact connected_induce_union ha.preconnected hb.preconnected a.root_mem b.root_mem e

lemma Branch.dist_le [DecidableEq V] (t : Branch G r) {u v : V} (hu : u ∈ t.vertices)
    (hv : v ∈ t.vertices) : G.dist u v ≤ t.size := by
  classical
  obtain ⟨p,hp⟩ := t.connected.exists_isPath ⟨u,hu⟩ ⟨v,hv⟩
  have h := hp.length_lt
  have num : Fintype.card (↑t.vertices : Set V) = t.vertices.card := Fintype.card_coe _
  rw [num] at h
  have hd := SimpleGraph.dist_le (p.map (Embedding.induce _).toHom)
  simp only [Walk.length_map] at hd
  exact hd.trans (by have := t.card; omega)

def Minimal [DecidableEq V] (l : ℕ) (t : Σ r, Branch G r) : Prop :=
  l ≤ t.2.size ∧ t.2.size ≤ 2*l ∧ ∀ x ∈ t.2.vertices, ∀ y ∈ t.2.vertices, ∀ z ∈ t.2.vertices,
    G.dist x y ≤ l ∨ G.dist x z ≤ l ∨ G.dist y z ≤ l

end
section
open SimpleGraph

/- A connected induced subgraph of a tree contains its ambient geodesics. -/
theorem tree_induce_dist {V : Type} {G : SimpleGraph V} (ht : G.IsTree)
    {S : Set V} (hc : (G.induce S).Connected) (x y : S) :
    (G.induce S).dist x y = G.dist x.val y.val := by
  obtain ⟨p,hp,hd⟩ := (hc x y).exists_path_of_dist
  let f := Embedding.induce (G := G) S
  calc
    _ = p.length := hd.symm
    _ = (p.map f.toHom).length := (p.length_map _).symm
    _ = _ := path_dist ht (hp.map f.injective : (p.map f.toHom).IsPath)

/- One- and two-ball profiles for the actual fragment of the spanning-tree
decomposition. All centres and distances are in the ambient tree. -/
set_option maxHeartbeats 600000 in
theorem branch_piece_profiles {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (ht : G.IsTree) {l : ℕ} (u : Σ r, Branch G r) (hu : Minimal l u) :
    HasPieceProfiles (fun (c : V) (v : (↑u.2.vertices : Set V)) => cost G c v.val) l u.2.size := by
  classical
  obtain ⟨_,hcap,close⟩ := hu
  let S : Set V := ↑u.2.vertices
  let P := G.induce S
  have hc : P.Connected := u.2.connected
  have tree : P.IsTree := ⟨hc,ht.isAcyclic.induce S⟩
  let L : ℝ := u.2.size
  have hsize : (Fintype.card S : ℝ) ≤ L+1 := by
    dsimp [L]; exact_mod_cast (show Fintype.card S ≤ u.2.size+1 from (Fintype.card_coe _).le.trans u.2.card)
  have cap : L ≤ 2*l := by dsimp [L]; exact_mod_cast hcap
  let _ := hc.nonempty
  obtain ⟨x,y,hd⟩ := P.exists_dist_eq_diam
  obtain ⟨p,path,plen⟩ := hc.exists_path_of_dist x y
  choose j h tag dist chain using coordinates tree p path
  have bounds (v) : h v ≤ j v ∧ j v + h v ≤ p.length := by
    have left := P.dist_le_diam (P.connected_iff_ediam_ne_top.mp hc) (u := x) (v := v)
    have right := P.dist_le_diam (P.connected_iff_ediam_ne_top.mp hc) (u := y) (v := v)
    obtain ⟨_,_,_⟩ := tag v
    omega
  obtain ⟨u,_,hu⟩ := Finset.exists_max_image Finset.univ h Finset.univ_nonempty
  let z := min (h u) (Fintype.card S-(p.length+h u+1))
  have points (v : S) (k : ℕ) (hk : k ≤ h v) : ∃ t, (j t,h t) = (j v,k) := by
    obtain ⟨t,ht⟩ := chain v k hk
    exact ⟨t,(tag t).unique ht⟩
  choose a ha using fun n : Fin (h u) => points u (n+1) n.isLt
  have on (k : Fin (p.length+1)) : (j (p.getVert k),h (p.getVert k)) = (k.val,0) := by
    exact (tag _).unique (tag_getVert tree path (by omega))
  have pack (v) (s : ℕ) (hs : s ≤ h v) (sep : j u = j v → s=0) : p.length+h u+s+1 ≤ Fintype.card S := by
    choose b hb using fun n : Fin s => points v (n+1) (n.isLt.trans_le hs)
    let f : Fin (p.length+1) ⊕ (Fin (h u) ⊕ Fin s) → S := Sum.elim (fun n => p.getVert n) (Sum.elim a b)
    have inj : Function.Injective f := by
      intro m n e
      have hh := congrArg (fun v => (j v,h v)) e
      rcases m with m | m | m <;> rcases n with n | n | n <;>
        simp [f,on,ha,hb] at hh ⊢ <;> first | exact Fin.ext (by omega) | grind
    have := Fintype.card_le_of_injective _ inj
    simp only [Fintype.card_sum,Fintype.card_fin] at this; omega
  have base := pack u 0 (Nat.zero_le _) (fun _ => rfl)
  have hcard : p.length+h u+z+1 ≤ Fintype.card S := by dsimp [z]; omega
  let H := h u
  let I := j u
  obtain ⟨hle,hright⟩ := bounds u
  have hz : z ≤ H := min_le_left ..
  have short := close x x.prop y y.prop u u.prop
  obtain ⟨_,dx,dy⟩ := tag u
  simp only [P,tree_induce_dist ht hc] at plen dx dy
  have short' : H + min I (p.length-I) ≤ l := by dsimp [I,H]; omega
  let D : ℝ := p.length
  let i : ℝ := I
  have mass : D+(H:ℝ)+z ≤ L := by
    have := Nat.cast_le (α := ℝ).mpr hcard
    dsimp [D]; push_cast at this; linarith
  have hi : (H:ℝ) ≤ i := Nat.cast_le.mpr hle
  have hj : i+(H:ℝ) ≤ D := by dsimp [i,D]; exact_mod_cast hright
  have hz' := Nat.cast_le (α := ℝ).mpr hz
  have hshort : (H:ℝ)+min i (D-i) ≤ l := by
    have := Nat.cast_le (α := ℝ).mpr short'
    push_cast [Nat.cast_sub (show I ≤ p.length by omega)] at this
    exact this
  let m := max (L/4) (((H:ℝ)+min i (D-i))/2)
  let B := L-2*m
  have head : (H:ℝ)+min i (D-i) ≤ 2*m := by dsimp [m]; grind
  have space : D/2+z ≤ B := by dsimp [B,m]; grind
  let q := p.map (Embedding.induce (G := G) S).toHom
  let centre (s : ℝ) := (centre_on_walk q ht.connected s).choose
  have bound (s : ℝ) (v : S) : cost G (centre s) v.val ≤ |s-j v|+h v := by
    apply ((centre_on_walk q ht.connected _).choose_spec (j v) v.val).trans
    apply add_le_add le_rfl
    exact_mod_cast (show G.dist (q.getVert (j v)) v.val ≤ h v by
      rw [show q.getVert (j v) = (p.getVert (j v)).val from Walk.getVert_map ..,← tree_induce_dist ht hc]
      exact dist v)
  have geom (v) : (h v : ℝ) ≤ j v ∧ (j v : ℝ)+h v ≤ D := by
    obtain ⟨k,e⟩ := bounds v
    exact ⟨by exact_mod_cast k,by dsimp [D]; exact_mod_cast e⟩
  refine ⟨m,B,?_,?_,?_,by dsimp [B]; ring,⟨centre (D/2),fun v => ?_⟩,?_⟩
  · dsimp [m]; grind
  · dsimp [m]; grind
  · dsimp [B,m]; grind
  · obtain ⟨lo,hi⟩ := geom v; have b := bound (D/2) v; clear * - lo hi b space; grind only [abs_eq_max_neg,max_def]
  intro t ht s hs hsum
  let flip (x : ℝ) := if i ≤ D-i then x else D-x
  refine ⟨centre (flip (D-(B-t))),centre (flip t),fun v => ?_⟩
  by_cases htip : j v = I
  · right
    have k : (j v : ℝ) = i := by dsimp [i]; exact_mod_cast htip
    have h := Nat.cast_le (α := ℝ).mpr (hu v (Finset.mem_univ _))
    have b := bound (flip t) v
    clear * - b k h head hi hj ht
    dsimp [flip] at *
    grind [abs_eq_max_neg]
  · have low := Nat.cast_le (α := ℝ).mpr (show h v ≤ z from
      le_min (hu _ (by simp)) (by have := pack v (h v) le_rfl (fun he => (htip he.symm).elim); omega))
    obtain ⟨lo,hi⟩ := geom v
    have right := bound (flip (D-(B-t))) v
    have left := bound (flip t) v
    clear * - low lo hi right left hsum space
    by_cases side : i ≤ D-i <;> simp [flip,side] at right left ⊢ <;>
      grind only [abs_eq_max_neg,max_def]

end
section

/- A pair of adjacent uniform intervals of nondecreasing density is a
nonnegative mixture of two uniforms ending at one, tested against arbitrary
masses of the full range and of the upper interval. -/
lemma tail_decomposition {a b : ℝ} (hab : a < b) (hb : b < 1) (h : 1-b ≤ b-a) :
    ∃ α β : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ α*(1+a)+β*(1+b) = a+2*b+1 ∧
      ∀ u v : ℝ, (u-v)/(b-a)+v/(1-b) = α*(u/(1-a))+β*(v/(1-b)) := by
  have h1 := sub_pos.mpr hab
  have h2 := sub_pos.mpr hb
  have h3 := sub_pos.mpr (hab.trans hb)
  refine ⟨(1-a)/(b-a), 1-(1-b)/(b-a), by positivity,
    sub_nonneg.mpr ((div_le_one h1).mpr h), ?_, fun u v => ?_⟩ <;> field_simp <;> ring

end
section
open SimpleGraph BurningNumberConjecture
variable {V : Type} {T : SimpleGraph V}
variable {Q : Type} (bin : Q → ℝ → ℝ)

/- The histogram counts the radii of a list of balls covering the specified vertices. -/
def Attain (T : SimpleGraph V) (S : Set V) (R : ℝ) : Set (Q → ℝ) :=
  {x | ∃ bs : List (ℝ × V), (∀ p ∈ bs, p.1 ∈ Set.Icc 0 R) ∧
    (∀ v ∈ S, ∃ p ∈ bs, cost T p.2 v ≤ p.1) ∧
    ∀ q, x q = (bs.map (fun p => bin q p.1)).sum}

lemma attainable_mono {S : Set V} {R R' : ℝ} (hr : R ≤ R') :
    Attain bin T S R ⊆ Attain bin T S R' := by
  rintro x ⟨bs,hs,hcov,hist⟩
  exact ⟨bs,fun p hp => ⟨(hs p hp).1,(hs p hp).2.trans hr⟩,hcov,hist⟩

lemma attainable_add {S Z A : Set V} {R : ℝ} {x y : Q → ℝ}
    (hx : x ∈ Attain bin T S R) (hy : y ∈ Attain bin T Z R) (sub : A ⊆ S ∪ Z) :
    x+y ∈ Attain bin T A R := by
  obtain ⟨xs,hxs,hxc,hxi⟩ := hx
  obtain ⟨ys,hys,hyc,hyi⟩ := hy
  refine ⟨xs++ys,fun p h => (List.mem_append.mp h).elim (hxs p) (hys p),
    fun v h => ?_,fun q => by simp [hxi,hyi]⟩
  have hv := sub h
  rcases hv with h|h
  · obtain ⟨p,h,hp⟩ := hxc v h
    exact ⟨p,List.mem_append_left _ h,hp⟩
  · obtain ⟨p,h,hp⟩ := hyc v h
    exact ⟨p,List.mem_append_right _ h,hp⟩

end
section
open MeasureTheory Set
open scoped unitInterval

/- The uniform parameter on the closed unit interval has its canonical probability measure. -/
private lemma unit_mean (f : ℝ → ℝ) :
    (∫ y : I, f y) = ∫ y in (0:ℝ)..1, f y := by
  rw [integral_subtype measurableSet_Icc f, intervalIntegral.integral_of_le zero_le_one,
    setIntegral_congr_set Ioc_ae_eq_Icc]

noncomputable def bin (u v : ℝ) : ℝ → ℝ := (Ioc u v).indicator 1

/- Length of the intersection of (a,b] with the bin (u,v]. -/
def overlap (a b u v : ℝ) := max 0 (min b v - max a u)

lemma integral_bin {a b : ℝ} (hab : a ≤ b) (u v : ℝ) :
    (∫ x in a..b, bin u v x) = overlap a b u v := by
  rw [intervalIntegral.integral_of_le hab, bin, integral_indicator_one measurableSet_Ioc,
    Measure.real, Measure.restrict_apply measurableSet_Ioc, Set.inter_comm, Set.Ioc_inter_Ioc,
    Real.volume_Ioc, ENNReal.toReal_ofReal']
  exact max_comm ..

lemma bin_measurable (u v : ℝ) : Measurable (bin u v) :=
  measurable_const.indicator measurableSet_Ioc

lemma bin_mem (u v x : ℝ) : bin u v x ∈ Icc (0:ℝ) 1 := by
  by_cases h : x ∈ Ioc u v <;> simp [bin, h]

/- Both affine orientations carry the uniform parameter to the same interval law. -/
theorem affine_bin_means {a b : ℝ} (h : a < b) (u v : ℝ) :
    (∫ y : I, bin u v (a + (y:ℝ)*(b-a))) = overlap a b u v / (b-a) ∧
    (∫ y : I, bin u v (b - (y:ℝ)*(b-a))) = overlap a b u v / (b-a) := by
  have hu := intervalIntegral.integral_comp_add_mul (a := 0) (b := 1) (bin u v) (sub_ne_zero.mpr h.ne') a
  have hd := intervalIntegral.integral_comp_sub_mul (a := 0) (b := 1) (bin u v) (sub_ne_zero.mpr h.ne') b
  constructor
  · rw [unit_mean (fun y => bin u v (a + y*(b-a)))]
    simpa [mul_comm, smul_eq_mul, div_eq_mul_inv, integral_bin h.le] using hu
  · rw [unit_mean (fun y => bin u v (b - y*(b-a)))]
    simpa [mul_comm, smul_eq_mul, div_eq_mul_inv, integral_bin h.le] using hd

lemma int_bin (u v : ℝ) (g : I → ℝ) (hg : Measurable g) :
    Integrable (fun y => bin u v (g y)) volume :=
  (memLp_of_bounded (Filter.Eventually.of_forall (fun y => bin_mem u v (g y)))
    ((bin_measurable u v).comp hg).aestronglyMeasurable 1).integrable le_rfl

/- Subtract adjacent overlap lengths to use the upper-tail mixture identity. -/
theorem overlap_split {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (u v : ℝ) :
    overlap a b u v = overlap a c u v - overlap b c u v := by
  have hi : Integrable (bin u v) volume :=
    (integrable_indicator_iff measurableSet_Ioc).mpr (integrableOn_const (by simp [Real.volume_Ioc]))
  have h := intervalIntegral.integral_add_adjacent_intervals
    (a := a) (b := b) (c := c) hi.intervalIntegrable hi.intervalIntegrable
  rw [integral_bin hab, integral_bin hbc, integral_bin (hab.trans hbc)] at h
  linarith

end
section
open SimpleGraph MeasureTheory Finset Set
open scoped Pointwise unitInterval
variable {V Q : Type} [Fintype Q] {G : SimpleGraph V} (lo hi : Q → ℝ)

lemma bin_scale {R : ℝ} (hR : 0 < R) (u v t : ℝ) :
    bin u v (R*t) = bin (u/R) (v/R) t := by
  have hm : R*t ∈ Ioc u v ↔ t ∈ Ioc (u/R) (v/R) := by
    simp only [Set.mem_Ioc,div_lt_iff₀ hR,le_div_iff₀ hR,mul_comm R t]
  simp only [bin,Set.indicator,hm,Pi.one_apply]

lemma overlap_scale {R : ℝ} (hR : 0 < R) (a b u v : ℝ) :
    overlap a b (u/R) (v/R) = overlap (R*a) (R*b) u v / R := by
  apply (eq_div_iff hR.ne').mpr
  simp only [overlap,max_mul_of_nonneg _ _ hR.le,min_mul_of_nonneg _ _ hR.le,sub_mul,
    div_mul_cancel₀ _ hR.ne',zero_mul]
  rw [mul_comm a R,mul_comm b R]

/- The price of a uniform radius drawn from the upper interval, tested against the bin prices. -/
noncomputable def tailPrice (w : Q → ℝ) (R a : ℝ) : ℝ :=
  ∑ q, w q*(overlap a 1 (lo q/R) (hi q/R)/(1-a))

def Law (G : SimpleGraph V) (S : Set V) (R δ moment : ℝ) : Prop :=
  ∀ (w : Q → ℝ) (Y : ℝ), 0 ≤ Y →
    (∀ a ∈ Icc 0 (1-δ), tailPrice lo hi w R a ≤ (1+a)*Y) →
    ∃ x ∈ Attain (fun q => bin (lo q) (hi q)) G S R ∩ {x | ∀ q, x q ∈ Set.Icc (0:ℝ) 2}, ∑ q, w q*x q ≤ moment*Y

lemma tail_mass {R a : ℝ} (hr : 0 < R) (ha : 0 ≤ a) (ha' : a ≤ 1) (u v : ℝ) :
    overlap a 1 (u/R) (v/R) = overlap 0 R u v/R - overlap 0 (R*a) u v/R := by
  rw [overlap_scale hr,mul_one,overlap_split (a := 0) (b := R*a) (c := R)
    (mul_nonneg hr.le ha) (by nlinarith [mul_le_mul_of_nonneg_left ha' hr.le]) u v]
  ring

end

section
open MeasureTheory Set

lemma mean_offer {Ω Q : Type} [MeasurableSpace Ω] [Fintype Q]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → Q → ℝ) {C : Set (Q → ℝ)}
    (hC : ∀ ω, f ω ∈ C) (hint : ∀ q, Integrable (fun ω => f ω q) μ) :
    ∀ w : Q → ℝ, ∃ x ∈ C, ∑ q, w q*x q ≤ ∑ q, w q*(∫ ω, f ω q ∂μ) := by
  intro w
  have hi q := (hint q).const_mul (w q)
  obtain ⟨ω,hω⟩ := exists_le_integral (integrable_finsetSum Finset.univ (fun q _ => hi q))
  exact ⟨f ω,hC ω,by simpa [integral_finsetSum _ (fun q _ => hi q),integral_const_mul] using hω⟩

end
section
open SimpleGraph MeasureTheory Set Finset
open scoped unitInterval
variable {V Q : Type} [Fintype V] [Fintype Q] [DecidableEq V] {G : SimpleGraph V}

private lemma affine_ranges {a b : ℝ} (h : a ≤ b) (y : I) :
    a+(y:ℝ)*(b-a) ∈ Set.Icc a b ∧ b-(y:ℝ)*(b-a) ∈ Set.Icc a b := by
  have := mul_nonneg y.prop.1 (sub_nonneg.mpr h)
  have := mul_le_mul_of_nonneg_right y.prop.2 (sub_nonneg.mpr h)
  exact ⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩⟩

private lemma scaled_radius {r x : ℝ} (hr : 0 ≤ r) (hx : x ∈ Set.Icc 0 1) : r*x ∈ Set.Icc 0 r :=
  ⟨mul_nonneg hr hx.1,by simpa using mul_le_mul_of_nonneg_left hx.2 hr⟩

private lemma single_law (lo hi : Q → ℝ) {S : Set V} {R δ : ℝ} (hr : 0 < R)
    (hd : 0 < δ) (hd' : δ ≤ 1/2) (one : ∀ t ∈ Set.Icc (1-δ) 1,
      ∃ c : V, ∀ v ∈ S, cost G c v ≤ R*t) : Law lo hi G S R δ (2-δ) := by
  classical
  let f (y : I) := 1-δ+(y:ℝ)*δ
  let X (y : I) (q : Q) := bin (lo q/R) (hi q/R) (f y)
  have hX (y : I) : X y ∈ Attain (fun q => bin (lo q) (hi q)) G S R ∩ {x | ∀ q, x q ∈ Set.Icc (0:ℝ) 2} := by
    have h : f y ∈ Set.Icc (1-δ) 1 := by simpa [f] using
        (affine_ranges (show 1-δ ≤ 1 by linarith) y).1
    obtain ⟨c,hc⟩ := one _ h
    refine ⟨⟨[(R*f y,c)],?_,?_,fun q => by simp [X,bin_scale hr]⟩,fun q =>
      ⟨(bin_mem _ _ _).1,((bin_mem _ _ _).2).trans (by norm_num)⟩⟩
    · simpa using scaled_radius hr.le ⟨by linarith [h.1],h.2⟩
    · intro v hv
      exact ⟨(R*f y,c),by simp,hc v hv⟩
  have hx := mean_offer volume X hX (fun q =>
    int_bin (lo q/R) (hi q/R) f (by dsimp [f]; fun_prop))
  intro w Y hy tail
  obtain ⟨x,hx,hb⟩ := hx w
  refine ⟨x,hx,hb.trans ?_⟩
  have eq q : (∫ y : I, X y q) = overlap (1-δ) 1 (lo q/R) (hi q/R) / δ := by
    simpa [X,f] using (affine_bin_means (a := 1-δ) (b := 1) (by linarith) (lo q/R) (hi q/R)).1
  simp_rw [eq]
  simpa [tailPrice,show 1+(1-δ)=2-δ by ring] using tail (1-δ) ⟨by linarith,le_rfl⟩

theorem piece_law (lo hi : Q → ℝ) (ht : G.IsTree) {R δ : ℝ}
    (hr : 0 < R) (hd : 0 < δ) (hd' : δ ≤ 1/2)
    {l : ℕ} (he : (l:ℝ) = 2*R*(1-δ)) (u : Σ r, Branch G r) (hu : Minimal l u) :
    Law lo hi G (↑u.2.vertices : Set V) R δ ((u.2.size:ℝ)/R+2*δ) := by
  classical
  have low : 2*(1-δ) ≤ (u.2.size:ℝ)/R := (le_div_iff₀ hr).mpr (by
    rw [mul_right_comm,← he]; exact_mod_cast hu.1)
  obtain ⟨m₀,B₀,_,hm₀,hB₀,heq,one,two⟩ := branch_piece_profiles ht u hu
  simp only [Subtype.forall] at one two
  let m := m₀/R
  let B := B₀/R
  have hm : m ≤ 1-δ := (div_le_iff₀ hr).mpr (by linarith [hm₀,he])
  have hB : B ≤ 2*m := by dsimp [B,m]; field_simp; linarith
  have hL : 2*m+B = u.2.size/R := by dsimp [B,m]; rw [← heq]; ring
  by_cases short : B ≤ 1-δ
  · have law := single_law lo hi hr hd hd' (S := (↑u.2.vertices : Set V)) (by
      intro t ht'
      obtain ⟨c,hc⟩ := one
      have ht := (div_le_iff₀ hr).mp (short.trans ht'.1)
      exact ⟨c,fun v hv => by linarith only [hc v hv,ht,mul_comm t R]⟩)
    intro w Y hY tail
    obtain ⟨x,hx,h⟩ := law w Y hY tail
    exact ⟨x,hx,h.trans (mul_le_mul_of_nonneg_right (by linarith) hY)⟩
  · let a := max 0 (B-1)
    let b := max m (1/2)
    have bounds : 0 ≤ a ∧ m ≤ b ∧ b ≤ 1-δ ∧ b < 1 ∧ 1-b ≤ b-a ∧ a < b ∧
        a+2*b+1 ≤ (u.2.size:ℝ)/R+2*δ  := by
      simp only [a,b,max_def]
      split_ifs <;> (repeat' constructor) <;> linarith
    obtain ⟨ha,mb,hb,hb1,hw,hab,hm⟩ := bounds
    let s (y : I) := b-(y:ℝ)*(b-a)
    let t (y : I) := b+(y:ℝ)*(1-b)
    let X (y : I) (q : Q) := bin (lo q/R) (hi q/R) (s y) + bin (lo q/R) (hi q/R) (t y)
    have hX (y : I) : X y ∈ Attain (fun q => bin (lo q) (hi q)) G (↑u.2.vertices) R ∩ {x | ∀ q, x q ∈ Set.Icc (0:ℝ) 2} := by
      have hs := (affine_ranges hab.le y).2
      have ht := (affine_ranges hb1.le y).1
      change s y ∈ Set.Icc a b at hs
      change t y ∈ Set.Icc b 1 at ht
      have hsy : s y ∈ Set.Icc 0 1 := ⟨ha.trans hs.1,hs.2.trans hb1.le⟩
      have hty : t y ∈ Set.Icc 0 1 := ⟨(ha.trans hab.le).trans ht.1,ht.2⟩
      have width := mul_le_mul_of_nonneg_right y.prop.2 (by linarith : 0 ≤ 2*b-a-1)
      obtain ⟨d,c,hc⟩ := two (t y*R) ((div_le_iff₀ hr).mp (mb.trans ht.1))
        (s y*R) (mul_nonneg hsy.1 hr.le) (by
          rw [← add_mul]; apply (div_le_iff₀ hr).mp
          change B ≤ s y+t y
          have hbase : B ≤ a+1 := by dsimp [a]; grind
          dsimp [s,t]; linarith)
      refine ⟨⟨[(R*s y,d),(R*t y,c)],?_,?_,fun q => by simp [X,bin_scale hr]⟩,fun q =>
        ⟨add_nonneg (bin_mem _ _ _).1 (bin_mem _ _ _).1, by
          dsimp [X]; linarith [(bin_mem (lo q/R) (hi q/R) (s y)).2,(bin_mem (lo q/R) (hi q/R) (t y)).2]⟩⟩
      · intro z hz
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
        rcases hz with rfl|rfl
        · exact scaled_radius hr.le hsy
        · exact scaled_radius hr.le hty
      · intro v hv
        simpa [or_comm,mul_comm] using hc v hv
    have si q := int_bin (lo q/R) (hi q/R) s (by dsimp [s]; fun_prop)
    have ti q := int_bin (lo q/R) (hi q/R) t (by dsimp [t]; fun_prop)
    have HX := mean_offer volume X hX (fun q => (si q).add (ti q))
    obtain ⟨α,β,hα,hβ,hmean,hbin⟩ := tail_decomposition hab hb1 hw
    intro w Y hY tail
    obtain ⟨x,hx,hcost⟩ := HX w
    refine ⟨x,hx,hcost.trans ?_⟩
    calc
      _ = α*tailPrice lo hi w R a + β*tailPrice lo hi w R b := by
        simp only [tailPrice,Finset.mul_sum,←Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro q _
        rw [show (∫ y, X y q) = _ from (integral_add (si q) (ti q)).trans
          (congrArg₂ (·+·) (affine_bin_means hab (lo q/R) (hi q/R)).2 (affine_bin_means hb1 _ _).1)]
        rw [overlap_split hab.le hb1.le,hbin]; ring
      _ ≤ (a+2*b+1)*Y := by
        rw [←hmean,add_mul,mul_assoc,mul_assoc]
        exact add_le_add (mul_le_mul_of_nonneg_left (tail a ⟨ha,hab.le.trans hb⟩) hα)
          (mul_le_mul_of_nonneg_left (tail b ⟨ha.trans hab.le,hb⟩) hβ)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hY

end

section
open SimpleGraph BurningNumberConjecture

theorem burn_of_scheduled_pieces {V : Type} {J : Type*} {T G : SimpleGraph V} (hTG : T ≤ G)
    (hc : T.Connected) {K : ℕ} (t : J ↪ Fin K) (c : J → V)
    (r : J → ℝ) (ht : ∀ j, ⌈r j⌉₊ + (t j : ℕ) < K)
    (hcover : ∀ v, ∃ j, cost T (c j) v ≤ r j) :
    burningNumber G ≤ K+1 := by
  let f := t.trans (Fin.castLEEmb (show K ≤ K+1 by omega))
  let ignite := Function.extend f (fun j => (c j)) (fun _ => Classical.choice hc.nonempty)
  refine Nat.sInf_le ⟨ignite,fun v => ?_⟩
  obtain ⟨j,hj⟩ := hcover v
  refine ⟨f j,?_,?_⟩ <;> rw [show ignite (f j) = (c j) from f.injective.extend_apply ..]
  · exact (hc.preconnected _ _).mono hTG
  · have hceil := Nat.le_ceil (r j)
    change (T.dist (c j) v : ℝ)-1 ≤ r j at hj
    have hh : T.dist (c j) v ≤ ⌈r j⌉₊+1 := by exact_mod_cast (show (T.dist (c j) v : ℝ) ≤ ⌈r j⌉₊+1 by linarith)
    have hanti := (hc.preconnected (c j) v).dist_anti hTG
    have := ht j
    change G.dist (c j) v + (t j : ℕ) < K+1
    omega

end

section
open Finset



/- Assign disjoint blocks of d rounds to the radius bins, largest radii first. -/
theorem exists_rounds_of_bins {I : Type*} [Fintype I] {Q d : ℕ}
    (b : I → Fin Q) (r : I → ℕ) (hr : ∀ i, r i ≤ (b i + 1 : ℕ) * d)
    (hb : ∀ q, (univ.filter (fun i => b i = q)).card ≤ d) :
    ∃ f : I ↪ Fin (Q*d + d), ∀ i, r i + (f i : ℕ) < Q*d + d := by
  classical
  let u (k : Fin Q) : {i // b i = k} ↪ Fin d := Classical.choice
    (Function.Embedding.nonempty_of_card_le (by simpa [Fintype.card_subtype] using hb k))
  let t := (Equiv.sigmaFiberEquiv b).symm.toEmbedding.trans
    ((Function.Embedding.sigmaMap (β' := fun _ => Fin d) Fin.revPerm.toEmbedding u).trans
    ((Equiv.sigmaEquivProd _ _).trans finProdFinEquiv).toEmbedding)
  refine ⟨t.trans (Fin.castLEEmb (by omega)), fun i => ?_⟩
  let j := u (b i) ⟨i,rfl⟩
  change r i + ((j : ℕ) + d * ((b i).rev : ℕ)) < Q*d + d
  have hh : ((b i).rev : ℕ) + ((b i : ℕ) + 1) = Q := by have := (b i).isLt; simp [Fin.rev]
  have := congrArg (fun x => x*d) hh
  have := hr i
  have := j.isLt
  nlinarith

end

section

lemma adaptive_parameters {ε : ℝ} (he : 0 < ε) :
    ∃ q : ℕ, ∃ ξ η : ℝ, 0 < ξ ∧ 0 < η ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∃ d : ℕ,
      0 < d ∧ 2/ξ ≤ (d:ℝ) ∧
      let R : ℝ := ((q+1)*d : ℕ)
      ((1+ξ)*d/R^2)*(n:ℝ)+1 ≤ (1-η)*d ∧
      (q+1:ℕ)*((2+4*(1+ξ))^2/d)*(n:ℝ) ≤ (η*d)^2 ∧
      (((q+1)*d+d+1:ℕ):ℝ) ≤ (1+ε)*Real.sqrt n := by
  obtain ⟨q,hq⟩ := exists_nat_gt (4/ε)
  have hp : 0 < (q:ℝ) := lt_trans (by positivity) hq
  have hqε := (div_lt_iff₀ he).mp hq
  let Q : ℝ := q+1
  let η := 1/(2*Q)
  let W := 2+4*(1+1/(q:ℝ))
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hη : 0 < η := by dsimp [η]; positivity
  let C := max (2*Q) (Q*W^2*q^2/η^2)
  have hC : 2*Q ≤ C := le_max_left ..
  obtain ⟨N,hN⟩ := exists_nat_gt (2*((Q+1)*(C+1)+1)/ε)
  refine ⟨q,1/q,η,by positivity,hη,N^2,fun n hn => ?_⟩
  let s := Real.sqrt n
  have hs : (N:ℝ) ≤ s := Real.le_sqrt_of_sq_le (by exact_mod_cast hn)
  have hs₀ : 0 ≤ s := Real.sqrt_nonneg _
  let d := ⌈s/q+C⌉₊
  have lo : s/q+C ≤ (d:ℝ) := Nat.le_ceil _
  have hi : (d:ℝ) < s/q+C+1 := Nat.ceil_lt_add_one (by linarith [div_nonneg hs₀ hp.le])
  have big : C ≤ (d:ℝ) := by linarith [div_nonneg hs₀ hp.le]
  have hd : 0 < (d:ℝ) := by linarith
  have key : (n:ℝ) ≤ ((q:ℝ)*d)^2 := by
    rw [← Real.sq_sqrt (show 0 ≤ (n:ℝ) by positivity)]
    apply pow_le_pow_left₀ hs₀ _ 2
    rw [mul_comm]; exact (div_le_iff₀ hp).mp (by linarith)
  refine ⟨d,by exact_mod_cast hd,by simpa [div_div_eq_mul_div] using
    (show 2*(q:ℝ) ≤ d by dsimp [Q] at hC; linarith),?_,?_,?_⟩
  · push_cast
    change ((1+1/(q:ℝ))*d/(Q*d)^2)*n+1 ≤ (1-η)*d
    have unit : 1 ≤ (d:ℝ)/(2*Q) := (le_div_iff₀ (by positivity)).mpr (by linarith)
    apply (add_le_add (mul_le_mul_of_nonneg_left key (by positivity)) unit).trans_eq
    dsimp [η,Q]; field_simp; ring
  · push_cast
    change Q*(W^2/d)*(n:ℝ) ≤ (η*d)^2
    have budget := (div_le_iff₀ (sq_pos_of_pos hη)).mp ((le_max_right ..).trans big)
    apply (mul_le_mul_of_nonneg_left key (by positivity)).trans
    calc
      _ = Q*W^2*q^2*d := by field_simp
      _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_right budget hd.le]
  · have hconst := (div_lt_iff₀ he).mp (hN.trans_le hs)
    have hratio := mul_le_mul_of_nonneg_right (le_of_lt hqε) (div_nonneg hs₀ hp.le)
    have hdiv : (q:ℝ)*(s/q) = s := by field_simp
    have H := mul_lt_mul_of_pos_left hi (by positivity : 0 < Q+1)
    push_cast
    change Q*(d:ℝ)+d+1 ≤ (1+ε)*s
    dsimp [Q] at *
    linear_combination (norm := ring_nf) (2:ℝ)⁻¹*hconst.le + H.le + (1/2:ℝ)*hratio + (1+ε/2)*hdiv <;> norm_num

end

section
open Set

def gridLo {q : ℕ} (d : ℕ) (k : Fin (q+1)) : ℝ := if k = 0 then -1 else (k:ℕ)*d
def gridHi {q : ℕ} (d : ℕ) (k : Fin (q+1)) : ℝ := ((k:ℕ)+1 : ℕ)*d

lemma grid_pick {q d : ℕ} {r : ℝ} (hr : 0 ≤ r) (hR : r ≤ (((q+1)*d : ℕ):ℝ)) :
    ∃ k : Fin (q+1), r ≤ gridHi d k ∧
      ∀ t : Fin (q+1), bin (gridLo d t) (gridHi d t) r = if k=t then 1 else 0 := by
  classical
  have hex : ∃ n : ℕ, r ≤ (((n+1)*d:ℕ):ℝ) := ⟨q,hR⟩
  let k : Fin (q+1) := ⟨Nat.find hex, Nat.lt_succ_iff.mpr (Nat.find_min' hex hR)⟩
  have iff (t : Fin (q+1)) : k=t ↔ r ∈ Ioc (gridLo d t) (gridHi d t) := by
    rw [← Fin.val_inj,show k.val = Nat.find hex by rfl,Nat.find_eq_iff]
    change (_ ∧ _) ↔ _ < r ∧ _
    by_cases ht : t=0
    · subst t; simp [gridLo,gridHi]; grind
    · have hpos : 0 < t.val := Nat.pos_of_ne_zero (fun h => ht (Fin.ext h))
      simp only [gridLo,if_neg ht,gridHi]
      push_cast
      constructor
      · rintro ⟨hu,hl⟩
        have := hl (t.val-1) (by omega)
        rw [← Nat.cast_one (R := ℝ), ← Nat.cast_add,Nat.sub_add_cancel hpos] at this
        exact ⟨by exact lt_of_not_ge (by simpa using this),hu⟩
      · rintro ⟨hl,hu⟩
        refine ⟨hu,fun n hn => not_le.mpr (lt_of_le_of_lt ?_ hl)⟩
        exact_mod_cast Nat.mul_le_mul_right d hn
  refine ⟨k,((iff k).mp rfl).2,fun t => ?_⟩
  simp [bin, Set.indicator, ← iff]

lemma overlap_grid_le {q d : ℕ} (k : Fin (q+1)) (R : ℝ) :
    overlap 0 R (gridLo d k) (gridHi d k) ≤ d := by
  unfold overlap
  apply max_le (Nat.cast_nonneg _)
  by_cases h : k = 0
  · subst k; simpa [gridLo, gridHi] using (min_le_right R (d:ℝ))
  · exact (sub_le_sub (min_le_right ..) (le_max_right ..)).trans (by
      simp [gridHi,gridLo,h,add_mul])

end

/- Build a rooted description of a spanning tree, then split it into small
connected pieces. The remaining fragment always contains the attachment vertex. -/

section
open SimpleGraph
variable {V : Type} {G : SimpleGraph V} {r : V}
lemma Branch.attach [DecidableEq V] (t : Branch G r) {u v : V}
    (hu : u ∈ t.vertices) (e : G.Adj u v) :
    ∃ t' : Branch G r, t'.size = t.size+1 ∧ t'.vertices = insert v t.vertices := by
  induction t with
  | root r =>
    have eq : u = r := by simpa [vertices] using hu
    subst u
    exact ⟨.join e (.root _) (.root _),rfl,by ext; simp [vertices,or_comm]⟩
  | join ab a b ia ib =>
    rcases Finset.mem_union.mp hu with h | h
    · obtain ⟨q,hq,hv⟩ := ia h
      exact ⟨.join ab q b,by simp [size,hq]; omega,by ext; simp [vertices,hv] <;> tauto⟩
    · obtain ⟨q,hq,hv⟩ := ib h
      exact ⟨.join ab a q,by simp [size,hq] <;> omega,by ext; simp [vertices,hv] <;> tauto⟩

lemma spanning [Fintype V] [DecidableEq V] (hc : G.Connected) (r : V) :
    ∃ t : Branch G r, t.vertices = Finset.univ ∧ t.size+1 = Fintype.card V := by
  classical
  suffices grow : ∀ t : Branch G r, t.size+1 = t.vertices.card →
      ∃ b : Branch G r, b.vertices = Finset.univ ∧ b.size+1 = Fintype.card V from
    grow (.root r) (by simp [Branch.size,Branch.vertices])
  intro t ht
  generalize hM : Fintype.card V - t.vertices.card = m
  induction m using Nat.strong_induction_on generalizing t with
  | h m ih =>
    by_cases hall : t.vertices = Finset.univ
    · exact ⟨t,hall,by simpa [hall] using ht⟩
    obtain ⟨v,hv⟩ := not_forall.mp (fun he => hall (Finset.eq_univ_of_forall he))
    obtain ⟨p⟩ := hc r v
    obtain ⟨e,_,ha,hb⟩ := p.exists_boundary_dart (↑t.vertices) t.root_mem hv
    obtain ⟨q,hq,hv'⟩ := t.attach ha e.adj
    have hcard : q.vertices.card = t.vertices.card + 1 := by rw [hv', Finset.card_insert_of_notMem hb]
    have := Finset.card_le_univ q.vertices
    exact ih _ (by omega) q (by omega) rfl

end
section
open SimpleGraph
variable {V : Type} [DecidableEq V] {G : SimpleGraph V} {r : V}

lemma peel (t : Branch G r) {l : ℕ} (hl : 0 < l) (hsize : l ≤ t.size) :
    ∃ (rest : Branch G r) (u : Σ v, Branch G v), Minimal l u ∧ rest.size+u.2.size=t.size ∧
      ∀ x ∈ t.vertices, x ∈ rest.vertices ∨ x ∈ u.2.vertices := by
  induction t with
  | root => simp [Branch.size] at hsize; omega
  | join e a b ia ib =>
    by_cases ha : l ≤ a.size
    · obtain ⟨w,u,hm,hs,hc⟩ := ia ha
      refine ⟨.join e w b,u,hm,by dsimp [Branch.size]; omega,?_⟩
      simp only [Branch.vertices,Finset.mem_union]; grind
    by_cases hb : l ≤ b.size
    · obtain ⟨w,u,hm,hs,hc⟩ := ib hb
      refine ⟨.join e a w,u,hm,by dsimp [Branch.size]; omega,?_⟩
      simp only [Branch.vertices,Finset.mem_union]; grind
    refine ⟨.root _,⟨_,.join e a b⟩,⟨hsize,by dsimp [Branch.size]; omega,?_⟩,by simp [Branch.size],fun _ h => Or.inr h⟩
    intro x hx y hy z hz
    have left : ∀ v ∈ a.vertices, ∀ w ∈ a.vertices, G.dist v w ≤ l :=
      fun _ h _ h' => (a.dist_le h h').trans (by omega)
    have right : ∀ v ∈ b.vertices, ∀ w ∈ b.vertices, G.dist v w ≤ l :=
      fun _ h _ h' => (b.dist_le h h').trans (by omega)
    simp only [Branch.vertices,Finset.mem_union] at hx hy hz
    grind

lemma short_branch_ball [Fintype V] (ht : G.IsTree) (t : Branch G r) {R : ℝ} (h : (t.size:ℝ) ≤ 2*R) :
    ∃ c : V, ∀ v ∈ t.vertices, cost G c v ≤ R := by
  have hm : Minimal t.size ⟨r,t⟩ :=
    ⟨le_rfl,by change t.size ≤ 2*t.size; omega,fun _ hx _ hy _ _ => Or.inl (t.dist_le hx hy)⟩
  obtain ⟨m,B,_,_,hle,heq,⟨c,hc⟩,_⟩ := branch_piece_profiles ht ⟨r,t⟩ hm
  exact ⟨c,fun v hv => (hc ⟨v,hv⟩).trans (by change 2*m+B = (t.size:ℝ) at heq; linarith)⟩

end

section
open Finset SimpleGraph Set
lemma first_bin {q d : ℕ} (k : Fin (q+1)) {s : ℝ} (hs : 0 ≤ s) (h : s ≤ d) :
    overlap 0 s (gridLo d k) (gridHi d k) = if k=0 then s else 0 := by
  by_cases hk : k = 0
  · subst k; simp [overlap,gridLo,gridHi,min_eq_left h,max_eq_right hs]
  have hk' : 1 ≤ k.val := Nat.pos_of_ne_zero (fun h => hk (Fin.ext h))
  have cut : (d:ℝ) ≤ (k:ℕ)*d := by exact_mod_cast (Nat.le_mul_of_pos_left d hk')
  simp only [if_neg hk]
  unfold overlap gridLo; simp only [if_neg hk]; apply max_eq_left
  exact sub_nonpos.mpr ((min_le_left ..).trans (h.trans (cut.trans (le_max_right ..))))

/- Select the cut after pricing the bins. Only the selected fragment is removed. -/
theorem priced_peel {V : Type} [Fintype V] [DecidableEq V] {T : SimpleGraph V} {v : V}
    (ht : T.IsTree) (t : Branch T v) {q d : ℕ} (hd : 0 < d) {R ξ : ℝ}
    (hdR : (d:ℝ) ≤ R) (hξ : 0 < ξ) (resolution : 2/ξ ≤ d)
    (big : 2*R ≤ t.size) (w : Fin (q+1) → ℝ) (hw : ∀ k, 0 ≤ w k) :
    ∃ (rest : Branch T v) (u : Σ r, Branch T r) (x : Fin (q+1) → ℝ),
      rest.size+u.2.size=t.size ∧ d ≤ u.2.size ∧ (u.2.size:ℝ) ≤ 4*R ∧
      (∀ z ∈ t.vertices, z ∈ rest.vertices ∨ z ∈ u.2.vertices) ∧
      x ∈ Attain (fun k => bin (gridLo d k) (gridHi d k)) T (↑u.2.vertices) R ∧ (∀ k, x k ∈ Set.Icc 0 2) ∧
      (∑ k, w k*x k) ≤ ∑ k, w k*((1+ξ)*d/R^2*u.2.size) := by
  classical
  let M (s : ℝ) := ∑ k, w k*overlap 0 s (gridLo d k) (gridHi d k)
  let F (s : ℝ) := M s/s^2
  have hd' : 0 < (d:ℝ) := by exact_mod_cast hd
  have small (s : ℝ) (hz : 0 ≤ s) (hsd : s ≤ d) : M s = w 0*s := by
    simp [M, first_bin (q := q) (d := d) _ hz hsd, mul_ite]
  have cont : Continuous M := by dsimp [M,overlap]; fun_prop
  obtain ⟨r,hr,hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hdR)
    (f := F) (cont.continuousOn.div (continuousOn_id.pow 2)
      (fun s hs => (sq_pos_of_pos (hd'.trans_le hs.1)).ne'))
  have hr' := hd'.trans_le hr.1
  have best (s : ℝ) (hs : 0 < s) (hsR : s ≤ R) : F r ≤ F s := by
    by_cases h : (d:ℝ) ≤ s
    · exact hmin ⟨h,hsR⟩
    refine (hmin (left_mem_Icc.mpr hdR)).trans ?_
    dsimp [F]; rw [small _ hd'.le le_rfl,small _ hs.le (le_of_not_ge h)]
    simpa only [sq,←div_div,mul_div_cancel_right₀ _ hd'.ne',mul_div_cancel_right₀ _ hs.ne'] using
      (div_le_div_of_nonneg_left (hw 0) hs (le_of_not_ge h))
  have hm : 0 ≤ M r := sum_nonneg (fun k _ => mul_nonneg (hw k) (le_max_left ..))
  have h₁ : (1:ℝ) ≤ d := by exact_mod_cast hd

  let l := ⌈2*r⌉₊-1
  have pos : 0 < 2*r := by positivity
  have succ : (l:ℝ)+1 = ⌈2*r⌉₊ := by
    exact_mod_cast Nat.sub_add_cancel (Nat.ceil_pos.mpr pos)
  let δ := (2*r-l)/(2*r)
  have low := Nat.le_ceil (2*r)
  have high := Nat.ceil_lt_add_one (a := 2*r) pos.le
  have hδ : 0 < δ := div_pos (by linarith) pos
  have bound : δ ≤ 1/(2*r) := div_le_div_of_nonneg_right (by linarith) pos.le
  have cut : (l:ℝ) = 2*r*(1-δ) := by dsimp [δ]; field_simp; ring
  have hhalf : δ ≤ 1/2 := bound.trans ((div_le_iff₀ pos).mpr (by linarith [h₁.trans hr.1]))
  have hl : 0 < l := by exact_mod_cast (show (0:ℝ) < l by linarith [h₁.trans hr.1])

  have hbig : l ≤ t.size := by exact_mod_cast (show (l:ℝ) ≤ t.size by linarith [hr.2])
  obtain ⟨rest,u,hmn,hsize,hcov⟩ := peel t hl hbig
  have hslo : (l:ℝ) ≤ u.2.size := by exact_mod_cast hmn.1
  have hshi : (u.2.size:ℝ) ≤ 2*l := by exact_mod_cast hmn.2.1
  have hlo : r ≤ u.2.size := by linarith [h₁.trans hr.1]
  have hhi : (u.2.size:ℝ) ≤ 4*r := by linarith
  have ratio : 1 ≤ (u.2.size:ℝ)/r := (le_div_iff₀ hr').mpr (by linarith)
  have law := piece_law (gridLo (q := q) d) (gridHi d) ht hr' hδ hhalf cut u hmn
  obtain ⟨y,hy,hcost⟩ := law w (M r/r) (div_nonneg hm hr'.le) (fun a ha => by
      have h1 : 0 < 1-a := by linarith [ha.2]
      have ha1 : a ≤ 1 := by linarith
      have lower : (M r)*a^2 ≤ M (r*a) := by
        rcases ha.1.eq_or_lt with hz|hp
        · rw [←hz,mul_zero,zero_pow (by decide),mul_zero,small 0 le_rfl hd'.le,mul_zero]
        · have h := best (r*a) (mul_pos hr' hp)
            ((show r*a ≤ r by simpa using mul_le_mul_of_nonneg_left ha1 hr'.le).trans hr.2)
          change M r/r^2 ≤ M (r*a)/(r*a)^2 at h
          field_simp at h
          exact h
      have eq : tailPrice (gridLo d) (gridHi d) w r a = (M r/r-M (r*a)/r)/(1-a) := by
        unfold tailPrice; simp_rw [tail_mass hr' ha.1 ha1]
        dsimp [M]; rw [Finset.sum_div,Finset.sum_div,←sum_sub_distrib,Finset.sum_div]
        apply sum_congr rfl; intro k _; ring
      rw [eq,div_le_iff₀ h1]; field_simp; nlinarith only [lower])

  have mom : (u.2.size:ℝ)/r+2*δ ≤ (1+ξ)*(u.2.size:ℝ)/r := by
    have hh := (div_le_iff₀ hξ).mp (resolution.trans hr.1)
    have hδξ : 2*δ ≤ ξ := by
      apply le_of_mul_le_mul_right (a := r) _ hr'
      nlinarith only [(le_div_iff₀ pos).mp bound,hh]
    rw [mul_div_assoc]
    nlinarith only [hδξ,mul_le_mul_of_nonneg_left ratio hξ.le]
  refine ⟨rest,u,y,hsize,by exact_mod_cast hr.1.trans hlo,by linarith [hr.2],hcov,
    attainable_mono _ hr.2 hy.1,hy.2,hcost.trans ?_⟩
  calc
    _ ≤ ((1+ξ)*(u.2.size:ℝ)/r)*(M r/r) := mul_le_mul_of_nonneg_right mom (div_nonneg hm hr'.le)
    _ = ((1+ξ)*(u.2.size:ℝ))*F r := by dsimp [F]; ring
    _ ≤ ((1+ξ)*(u.2.size:ℝ))*F R := mul_le_mul_of_nonneg_left (hmin (right_mem_Icc.mpr hdR))
      (by positivity)

    _ = ∑ k, w k*((1+ξ)*u.2.size*overlap 0 R (gridLo d k) (gridHi d k)/R^2) := by
      dsimp [F,M]; rw [← mul_div_assoc,Finset.mul_sum,Finset.sum_div]
      apply sum_congr rfl; intro k _; ring
    _ ≤ _ := sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (by
      calc
        _ ≤ (1+ξ)*u.2.size*d/R^2 := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
          (overlap_grid_le _ R) (by positivity)) (sq_nonneg _)
        _ = _ := by ring) (hw k))

end
/- Price each bin at twice its current positive overload. The price bound pays
for the linear term in the change of the squared overload. Each step charges
its quadratic error to the size of the fragment that was removed. -/
open Finset in
theorem select_peels {S : Type*} {Q : ℕ} (μ : S → ℕ) (W : S → Set (Fin Q → ℝ))
    {β γ : ℝ} (hβ : 0 ≤ β) (hγ : 0 ≤ γ)
    (peel : ∀ s (w : Fin Q → ℝ), (∀ k, 0 ≤ w k) →
      (∃ v ∈ W s, ∀ k, v k ≤ 1) ∨
      ∃ t, μ t < μ s ∧ ∃ z : Fin Q → ℝ, (∀ y ∈ W t, z+y ∈ W s) ∧
        let l : ℝ := (μ s-μ t : ℕ)
        (∑ k, w k*z k) ≤ ∑ k, w k*(β*l) ∧ ∀ k, (z k-β*l)^2 ≤ γ*l)
    (s : S) : ∃ y ∈ W s, ∀ k, (max 0 (y k-β*μ s-1))^2 ≤ Q*γ*μ s := by
  classical
  let score (D : Fin Q → ℝ) := ∑ k, (max 0 (D k))^2
  let rec aux (s : S) (D : Fin Q → ℝ) : ∃ y ∈ W s,
      score (fun k => D k+y k-β*μ s-1) ≤ score D + Q*γ*μ s := by
    let w k := 2*max 0 (D k)
    rcases peel s w (fun k => mul_nonneg (by norm_num) (le_max_left ..)) with ⟨v,hv,h⟩ | ⟨t,ht,z,glue,price,err⟩
    · refine ⟨v,hv,(sum_le_sum (s := univ) (fun k _ => (sq_le_sq₀ (le_max_left 0 _) (le_max_left 0 _)).mpr
        (max_le_max_left 0 (show D k+v k-β*μ s-1 ≤ D k by linarith [h k,mul_nonneg hβ (Nat.cast_nonneg (μ s))])))).trans ?_⟩
      exact le_add_of_nonneg_right (by positivity)
    · let l : ℝ := (μ s-μ t : ℕ)
      have mass : l+(μ t:ℝ) = μ s := by dsimp [l]; exact_mod_cast Nat.sub_add_cancel ht.le
      let D' k := D k+(z k-β*l)
      have each k : (max 0 (D' k))^2 ≤ (max 0 (D k))^2+w k*z k-w k*(β*l)+γ*l := by
        let u := max 0 (D k)
        have hh : (max 0 (D' k))^2 ≤ (u+(z k-β*l))^2 := by
          by_cases hp : 0 ≤ D' k
          · rw [max_eq_right hp]; apply (sq_le_sq₀ hp _).mpr <;> dsimp [D',u] at * <;> linarith [le_max_right 0 (D k)]
          · rw [max_eq_left (le_of_not_ge hp),zero_pow (by decide : 2 ≠ 0)]; exact sq_nonneg _
        change _ ≤ u^2 + 2*u*z k-2*u*(β*l)+γ*l
        have e : (z k-β*l)^2 ≤ γ*l := err k
        nlinarith only [hh,e]
      have hstep := sum_le_sum (s := univ) (fun k _ => each k)
      simp only [sum_add_distrib,sum_sub_distrib,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at hstep
      change (∑ k, w k*z k) ≤ ∑ k, w k*(β*l) at price
      obtain ⟨y,hy,h⟩ := aux t D'
      refine ⟨z+y,glue y hy,?_⟩
      have eq : (fun k => D k+(z+y) k-β*(μ s)-1) = (fun k => D' k+y k-β*μ t-1) := by
        funext k; dsimp [D']; rw [← mass]; ring
      rw [eq]
      apply h.trans
      dsimp only [score]
      rw [← mass]
      linarith only [hstep,price]
  termination_by μ s
  obtain ⟨y,hy,h⟩ := aux s 0
  simp only [score,Pi.zero_apply,zero_add,max_self,zero_pow (by decide : 2 ≠ 0),sum_const_zero] at h
  exact ⟨y,hy,fun k => (single_le_sum (fun j _ => sq_nonneg (max 0 (y j-β*μ s-1))) (mem_univ k)).trans h⟩

section
open Finset SimpleGraph BurningNumberConjecture

lemma burn_of_grid_attain {V : Type} {T G : SimpleGraph V} (hTG : T ≤ G) (hc : T.Connected)
    {q d : ℕ} {x : Fin (q+1) → ℝ}
    (hx : x ∈ Attain (fun k => bin (gridLo d k) (gridHi d k)) T Set.univ ((q+1)*d : ℕ))
    (cap : ∀ k, x k ≤ d) : burningNumber G ≤ (q+1)*d+d+1 := by
  classical
  obtain ⟨bs,inside,cover,hist⟩ := hx
  let r (j : Fin bs.length) := (bs.get j).1
  choose label high bins using fun j : Fin bs.length =>
    grid_pick (q := q) (d := d) (inside _ (List.get_mem bs j)).1 (inside _ (List.get_mem bs j)).2
  have sum_map (f : ℝ × V → ℝ) : ∑ j : Fin bs.length, f (bs.get j) = (bs.map f).sum := by
    rw [← List.sum_ofFn]; change (List.ofFn (f ∘ bs.get)).sum = _
    rw [← List.map_ofFn,List.ofFn_get]
  obtain ⟨t,ht⟩ := exists_rounds_of_bins label (fun j => ⌈r j⌉₊)
    (fun j => Nat.ceil_le.mpr (by simpa [gridHi,r] using high j)) (by
      intro k
      have val : ((univ.filter (fun j => label j = k)).card : ℝ) = x k := by
        rw [hist k,←sum_map,card_filter]; push_cast
        exact sum_congr rfl (fun j _ => (bins j k).symm)
      exact_mod_cast val.le.trans (cap k))
  apply burn_of_scheduled_pieces hTG hc t (fun j => (bs.get j).2) r ht
  intro v
  obtain ⟨z,hz,h⟩ := cover v trivial
  obtain ⟨j,rfl⟩ := List.get_of_mem hz
  exact ⟨j,h⟩

end

section
open Finset SimpleGraph Set
theorem adaptive_cover {V : Type} [Fintype V] [DecidableEq V] {T : SimpleGraph V} {root : V}
    (ht : T.IsTree) (t : Branch T root) {q d : ℕ} (hd : 0 < d) {R ξ : ℝ}
    (hdR : (d:ℝ) ≤ R) (hξ : 0 < ξ) (resolution : 2/ξ ≤ d) :
    ∃ y : Fin (q+1) → ℝ, y ∈ Attain (fun k => bin (gridLo d k) (gridHi d k)) T
      (↑t.vertices) R ∧ ∀ k, (max 0 (y k-((1+ξ)*d/R^2)*t.size-1))^2 ≤
        (q+1:ℕ)*((2+4*(1+ξ))^2/d)*t.size := by
  classical
  let β := (1+ξ)*d/R^2
  let C := 2+4*(1+ξ)
  let F (k : Fin (q+1)) := bin (gridLo d k) (gridHi d k)
  let W (s : Branch T root) := Attain F T (↑s.vertices) R
  have hd' : 0 < (d:ℝ) := by exact_mod_cast hd
  have hR := hd'.trans_le hdR
  have hβ : 0 ≤ β := by dsimp [β]; positivity
  apply select_peels Branch.size W hβ (γ := C^2/d) (by positivity) ?_ t
  intro s w hw
  by_cases big : 2*R ≤ s.size
  · right
    obtain ⟨rest,u,z,size,low,high,cover,hz,range,price⟩ := priced_peel ht s hd hdR hξ resolution big w hw
    refine ⟨rest,by omega,z,?_,?_⟩
    · exact fun y hy => attainable_add F hz hy (fun v hv => (cover v hv).symm)
    · dsimp only
      rw [show s.size-rest.size = u.2.size by omega]
      refine ⟨price,fun k => ?_⟩
      have hz' := range k
      have bl : 0 ≤ β*u.2.size := mul_nonneg hβ (Nat.cast_nonneg _)
      have bh : β*u.2.size ≤ 4*(1+ξ) := by
        dsimp [β]; rw [div_mul_eq_mul_div,div_le_iff₀ (sq_pos_of_pos hR)]
        have H := mul_le_mul hdR high (Nat.cast_nonneg _) hR.le
        nlinarith only [mul_le_mul_of_nonneg_left H (by linarith : 0 ≤ 1+ξ)]
      have hsq : (z k-β*u.2.size)^2 ≤ C^2 := by
        apply sq_le_sq' <;> dsimp [C] <;> linarith [hz'.1,hz'.2]
      apply hsq.trans
      rw [div_mul_eq_mul_div,le_div_iff₀ hd']
      exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr low) (sq_nonneg _)
  · left
    obtain ⟨c,hc⟩ := short_branch_ball ht s (le_of_not_ge big)
    refine ⟨fun k => F k R,⟨[(R,c)],by simp [hR.le],?_,fun k => by simp⟩,fun k => (bin_mem _ _ _).2⟩
    exact fun v hv => ⟨(R,c),by simp,hc v hv⟩
end

end BurningNumberConjecture.Proof
open BurningNumberConjecture.Proof BurningNumberConjecture SimpleGraph Finset

theorem OMA.solution : type_of% @BurningNumberConjecture.burning_number_conjecture.variants.norin_turcotte := by
  classical
  intro ε he
  obtain ⟨q,ξ,η,hξ,hη,n₀,hN⟩ := adaptive_parameters he
  refine ⟨n₀,fun V _ G hc hn => ?_⟩
  obtain ⟨T,hTG,hT⟩ := hc.exists_isTree_le
  obtain ⟨t,ht,hs⟩ := spanning hT.connected (Classical.choice hc.nonempty)
  obtain ⟨d,hd,res,mean,variance,time⟩ := hN (Fintype.card V) hn
  let R := (q+1)*d
  have hd' : 0 < (d:ℝ) := by exact_mod_cast hd
  have hdR : (d:ℝ) ≤ R := by exact_mod_cast (Nat.le_mul_of_pos_left d (Nat.succ_pos q))
  obtain ⟨y,hy,cap⟩ := adaptive_cover (R := R) (q := q) hT t hd hdR hξ res
  rw [ht,Finset.coe_univ] at hy
  apply (Nat.cast_le (α := ℝ).mpr (burn_of_grid_attain hTG hT.connected hy ?_)).trans time
  intro k
  have hs' : (t.size:ℝ) ≤ Fintype.card V := Nat.cast_le.mpr (by omega)
  have weighted := (add_le_add (mul_le_mul_of_nonneg_left hs'
    (by positivity : 0 ≤ (1+ξ)*d/(R:ℝ)^2)) (le_refl 1)).trans mean
  have herr := (cap k).trans ((mul_le_mul_of_nonneg_left hs' (by positivity)).trans variance)
  have hcap := (le_max_right 0 _).trans (le_of_sq_le_sq herr (mul_pos hη hd').le)
  linarith only [hcap,weighted]
