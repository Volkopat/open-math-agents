import FormalConjectures.ErdosProblems.«89»

-- Reduction of Erdos89.erdos_89. Credit: @wispiANt
open Filter Finset EuclideanGeometry

namespace OMA.R_Erdos89_erdos_89_R2

/-- Bisector incidence estimate for configurations with at most K points
on any affine line. -/
def H1 : Prop :=
  ∀ (S : Finset ℝ²) (K : ℕ),
    (∀ a b c : ℝ, (a ≠ 0 ∨ b ≠ 0) →
      (S.filter fun p => a*p 0+b*p 1=c).card ≤ K) →
    S.card ≤ (K+1)*(distinctDistances S+1)

/-- Packing problem for disjoint collinear blocks. If each block contains
k points and the family covers at most exp(k²) points, bound the number
of blocks by a constant times the number of distances in their union plus one.
Assume that any collection of at most k lines or circles contains fewer than
half the points of the union. At each pin, retain any subset B containing at least half the targets outside
its block. The shell-weighted count within B must exceed k times its size. Each anchor contributes the
integer part of t(t−1)/(s−2), or zero for shells of size at most two.
After deleting any target pairs
with at most k² deletions per distinct pin pair and discarding up to k target
directions at each first endpoint, rich bisectors must still
contribute more than twice k times the square of the union size. Equal-length
directed segment pairs must exceed k times the cube of the union size after
excluding any k complex rotation factors. -/
def H2 : Prop :=
  ∃ C : ℕ, ∀ (k : ℕ) (F : Finset (Finset ℝ²)), 0 < k →
    (F : Set (Finset ℝ²)).PairwiseDisjoint id →
    (∀ T ∈ F, T.card = k ∧ ∃ a b c : ℝ, (a ≠ 0 ∨ b ≠ 0) ∧ ∀ p ∈ T, a*p 0+b*p 1=c) →
    ((F.biUnion id).card : ℝ) ≤ Real.exp ((k : ℝ)^2) →
    (∀ G : Finset (Finset ℝ²), G.card ≤ k →
      (∀ T ∈ G, T ⊆ F.biUnion id ∧ (Collinear ℝ (T : Set ℝ²) ∨ Cospherical (T : Set ℝ²))) →
      2*(G.biUnion id).card < (F.biUnion id).card) →
    (∀ T ∈ F, ∀ p ∈ T,
      let G := F.erase T
      ∀ B ⊆ G.biUnion id, (G.biUnion id).card ≤ 2*B.card →
      k*B.card < ∑ U ∈ G, ∑ x ∈ U.filter (· ∈ B),
        let s := (B.filter fun y => dist p y = dist p x).card
        let t := ((B \ U).filter fun y => dist p y = dist p x).card
        t*(t-1)/(s-2)) →
    (let S := F.biUnion id
      let W := fun x y : ℝ² => S.filter fun p => dist p y = dist p x
      ∀ G : ℝ² → Finset ℝ², (∀ x ∈ S, G x ⊆ S.erase x) →
        (∀ r ∈ S.offDiag, (∑ x ∈ S, ((G x).filter fun y => r ∈ (W x y).offDiag).card) ≤ k^2) →
        ∀ H : ℝ² → Finset ℝ², (∀ x ∈ S, H x ⊆ S.erase x \ G x) →
          (∀ x ∈ S, ∃ J : Finset (Finset ℝ²), J.card ≤ k ∧ H x ⊆ J.biUnion id ∧
            ∀ T ∈ J, Collinear ℝ (insert x (T : Set ℝ²))) →
          2*k*S.card^2 < ∑ x ∈ S, ∑ y ∈ (S.erase x \ G x) \ H x, if k < (W x y).card then (W x y).card else 0) →
    (let S := F.biUnion id
      let z := fun p : ℝ² => Complex.mk (p 0) (p 1)
      let E := S.offDiag
      let f := fun e t : ℝ² × ℝ² => (z t.2-z t.1)/(z e.2-z e.1)
      ∀ A : Finset ℂ, A.card ≤ k → k*S.card^3 <
        ∑ e ∈ E, (E.filter fun t => dist t.1 t.2 = dist e.1 e.2 ∧ f e t ∉ A).card) →
    F.card ≤ C * (distinctDistances (F.biUnion id)+1)

section Bisectors

private theorem pin_count {α γ : Type*} [DecidableEq γ] (B : Finset α)
    (D : Finset γ) (f : α → γ) (hf : ∀ x ∈ B, f x ∈ D) :
    B.card^2 ≤ D.card * (∑ x ∈ B, ∑ y ∈ B, if f y = f x then 1 else 0) := by
  classical
  let m (r : γ) := (B.filter fun y => f y = r).card
  have hsum : B.card = ∑ r ∈ D, m r := card_eq_sum_card_fiberwise hf
  have he : (∑ r ∈ D, m r ^ 2) = ∑ x ∈ B, m (f x) := by
    rw [← sum_fiberwise_of_maps_to hf (fun x => m (f x))]
    apply sum_congr rfl
    intro r _
    calc
      m r ^ 2 = ∑ _x ∈ B.filter (fun x => f x = r), m r := by simp [m,pow_two]
      _ = _ := sum_congr rfl fun x hx => by rw [(mem_filter.mp hx).2]
  simp only [sum_boole, Nat.cast_id]
  change B.card^2 ≤ D.card * ∑ x ∈ B, m (f x)
  rw [← he, hsum]
  exact sq_sum_le_card_mul_sum_sq

/-- A bound on pins on each bisector controls the number of cross-values. -/
private theorem cross_bound {α β γ : Type*} [DecidableEq γ] (A : Finset α) (B : Finset β)
    (D : Finset γ) (f : α → β → γ) (K : ℕ)
    (hc : ∀ p ∈ A, ∀ x ∈ B, f p x ∈ D)
    (hb : ∀ x ∈ B, ∀ y ∈ B, y ≠ x → (A.filter fun p => f p y = f p x).card ≤ K) :
    A.card * B.card^2 ≤ D.card * (B.card * (A.card + (B.card-1)*K)) := by
  classical
  let c (p : α) (x y : β) : ℕ := if f p y = f p x then 1 else 0
  have hrow (x : β) (hx : x ∈ B) :
      (∑ y ∈ B, ∑ p ∈ A, c p x y) ≤ A.card + (B.card-1)*K := by
    rw [← sum_erase_add B (fun y => ∑ p ∈ A, c p x y) hx]
    have h : (∑ y ∈ B.erase x, ∑ p ∈ A, c p x y) ≤ ∑ _y ∈ B.erase x, K :=
      sum_le_sum fun y hy => by simpa [c] using hb x hx y (mem_of_mem_erase hy) (ne_of_mem_erase hy)
    simpa [c,card_erase_of_mem hx,Nat.add_comm] using Nat.add_le_add_right h A.card
  calc
    _ = ∑ _p ∈ A, B.card^2 := by simp
    _ ≤ ∑ p ∈ A, D.card * (∑ x ∈ B, ∑ y ∈ B, c p x y) :=
      sum_le_sum fun p hp => pin_count B D (f p) (hc p hp)
    _ = D.card * (∑ x ∈ B, ∑ y ∈ B, ∑ p ∈ A, c p x y) := by
      rw [← mul_sum, sum_comm (s := A) (t := B)]
      congr 1
      exact sum_congr rfl fun _ _ => sum_comm
    _ ≤ D.card * (∑ _x ∈ B, (A.card + (B.card-1)*K)) :=
      Nat.mul_le_mul_left _ (sum_le_sum hrow)
    _ = _ := by simp

private theorem self_bound {α β : Type*} [DecidableEq β] (S : Finset α)
    (D : Finset β) (f : α → α → β) (K : ℕ)
    (hm : ∀ p ∈ S, ∀ x ∈ S, f p x ∈ D)
    (hb : ∀ x ∈ S, ∀ y ∈ S, y ≠ x → (S.filter fun p => f p y = f p x).card ≤ K) :
    S.card ≤ D.card*(K+1) := by
  have hh := cross_bound S S D f K hm hb
  by_cases hn : S.card = 0
  · simp [hn]
  have hpos := Nat.pos_of_ne_zero hn
  have hsmall : S.card-1 ≤ S.card := Nat.sub_le _ _
  have hstrong : S.card*(S.card*S.card) ≤
      S.card * (S.card * (D.card * (K+1))) := by
    calc
      _ = S.card*S.card^2 := by ring
      _ ≤ _ := hh
      _ ≤ D.card*(S.card*(S.card+S.card*K)) := by gcongr
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left (Nat.le_of_mul_le_mul_left hstrong hpos) hpos


/-- H1 follows by counting pairs of targets equidistant from each pin.
The pins for each distinct pair lie on a single perpendicular bisector. -/
theorem sparse_estimate : H1 := by
  intro S K hl
  classical
  let D := insert 0 (distanceSet S)
  have hm (p) (hp : p ∈ S) (x) (hx : x ∈ S) : dist p x ∈ D := by
    by_cases he : p = x
    · simp [he,D]
    · exact mem_insert_of_mem (mem_image.mpr ⟨(p,x), mem_offDiag.mpr ⟨hp,hx,he⟩,rfl⟩)
  have hb (x) (_hx : x ∈ S) (y) (_hy : y ∈ S) (hne : y ≠ x) :
      (S.filter fun p => dist p y = dist p x).card ≤ K := by
    let a := 2*(y 0-x 0)
    let b := 2*(y 1-x 1)
    let c := y 0^2+y 1^2-(x 0^2+x 1^2)
    have hcoeff : a ≠ 0 ∨ b ≠ 0 := by
      by_contra! h
      apply hne
      ext i
      fin_cases i <;> simp_all [a,b,sub_eq_zero]
    apply le_trans (card_le_card (t := S.filter fun p => a*p 0+b*p 1=c) ?_) (hl a b c hcoeff)
    intro p hp
    obtain ⟨hp,he⟩ := mem_filter.mp hp
    refine mem_filter.mpr ⟨hp,?_⟩
    have he' := congrArg (fun r : ℝ => r^2) he
    simp only [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq, sq_abs] at he'
    dsimp [a,b,c]
    linear_combination -he'
  have hc := self_bound S D dist K hm hb
  have hD : D.card ≤ distinctDistances S+1 := card_insert_le _ _
  exact hc.trans (by rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ hD)

end Bisectors

private theorem extract_blocks (S : Finset ℝ²) (k : ℕ) (hk : 0 < k) :
    ∃ F : Finset (Finset ℝ²), (F : Set (Finset ℝ²)).PairwiseDisjoint id ∧
      (∀ T ∈ F, T.card = k ∧ ∃ a b c : ℝ, (a ≠ 0 ∨ b ≠ 0) ∧ ∀ p ∈ T, a*p 0+b*p 1=c) ∧
      F.biUnion id ⊆ S ∧ ∀ a b c : ℝ, (a ≠ 0 ∨ b ≠ 0) →
        ((S \ F.biUnion id).filter fun p => a*p 0+b*p 1=c).card < k := by
  classical
  let blocks := S.powerset.filter fun T => T.card = k ∧
    ∃ a b c : ℝ, (a ≠ 0 ∨ b ≠ 0) ∧ ∀ p ∈ T, a*p 0+b*p 1=c
  let families := blocks.powerset.filter fun F : Finset (Finset ℝ²) => (F : Set (Finset ℝ²)).PairwiseDisjoint id
  have hempty : ∅ ∈ families := by simp [families]
  obtain ⟨F,hF,hmax⟩ := exists_max_image families Finset.card ⟨_,hempty⟩
  obtain ⟨hblocks,hdis⟩ := mem_filter.mp hF
  have hsub := mem_powerset.mp hblocks
  refine ⟨F,hdis,fun T hT => (mem_filter.mp (hsub hT)).2,?_,?_⟩
  · intro x hx
    obtain ⟨T,hT,hx⟩ := mem_biUnion.mp hx
    exact mem_powerset.mp (mem_filter.mp (hsub hT)).1 hx
  · intro a b c hab
    by_contra! h
    obtain ⟨T,hT,hsize⟩ := exists_subset_card_eq h
    have hR : T ⊆ S \ F.biUnion id := hT.trans (filter_subset ..)
    have hblock : T ∈ blocks := mem_filter.mpr ⟨mem_powerset.mpr (hR.trans sdiff_subset),
      hsize,a,b,c,hab,fun p hp => (mem_filter.mp (hT hp)).2⟩
    have hsep (U) (hU : U ∈ F) : Disjoint T U := by
      apply disjoint_left.mpr
      intro x hx hxu
      exact (mem_sdiff.mp (hR hx)).2 (mem_biUnion.mpr ⟨U,hU,hxu⟩)
    have hfresh : T ∉ F := by
      intro hmem
      obtain ⟨x,hx⟩ := card_pos.mp (hsize ▸ hk : 0 < T.card)
      exact disjoint_left.mp (hsep T hmem) hx hx
    have hnew : insert T F ∈ families := by
      refine mem_filter.mpr ⟨mem_powerset.mpr (insert_subset hblock hsub),?_⟩
      rw [coe_insert]
      exact (Set.pairwiseDisjoint_insert_of_notMem hfresh).mpr ⟨hdis,hsep⟩
    have := hmax _ hnew
    rw [card_insert_of_notMem hfresh] at this
    omega

private theorem distances_mono {S T : Finset ℝ²} (h : S ⊆ T) :
    distinctDistances S ≤ distinctDistances T := by
  apply card_le_card
  intro r hr
  obtain ⟨⟨x,y⟩,hxy,rfl⟩ := mem_image.mp hr
  obtain ⟨hx,hy,hne⟩ := mem_offDiag.mp hxy
  exact mem_image.mpr ⟨(x,y),mem_offDiag.mpr ⟨h hx,h hy,hne⟩,rfl⟩

/-- A positive-distance fiber on a line or circle through its pin has at most two points.
The pin itself is excluded, which also handles circles of radius zero. -/
private theorem fiber_card_le_two (curve : Set ℝ²) (p : ℝ²) (hp : p ∈ curve)
    (hcurve : Collinear ℝ curve ∨ Cospherical curve)
    (s : Finset ℝ²) (r : ℝ)
    (hs : ∀ x ∈ s, x ∈ curve ∧ x ≠ p ∧ dist x p = r) : #s ≤ 2 := by
  by_contra! h
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.mp h
  obtain ⟨haC, hap, har⟩ := hs a ha
  obtain ⟨hbC, _, hbr⟩ := hs b hb
  obtain ⟨hcC, _, hcr⟩ := hs c hc
  rcases hcurve with hline | ⟨o, R, hcircle⟩
  · have hcos : Cospherical (s : Set ℝ²) := ⟨p, r, fun x hx => (hs x hx).2.2⟩
    have hind := hcos.affineIndependent_of_mem_of_ne ha hb hc hab hac hbc
    apply (affineIndependent_iff_not_collinear_set.mp hind)
    exact hline.subset (by simp [Set.insert_subset_iff, haC, hbC, hcC])
  · have hpo : p ≠ o := by
      rintro rfl
      have hzero : R = 0 := by simpa using (hcircle p hp).symm
      exact hap (dist_eq_zero.mp ((hcircle a haC).trans hzero))
    have hdim : Module.finrank ℝ ℝ² = 2 := finrank_euclideanSpace_fin
    rcases eq_of_dist_eq_of_dist_eq_of_finrank_eq_two hdim hpo hab
        har hbr hcr (hcircle a haC) (hcircle b hbC) (hcircle c hcC) with he | he
    · exact hac he.symm
    · exact hbc he.symm

private theorem card_on_curve (P : Finset ℝ²) (curve : Set ℝ²)
    (hcurve : Collinear ℝ curve ∨ Cospherical curve) (s : Finset ℝ²)
    (hsP : s ⊆ P) (hsC : ∀ x ∈ s, x ∈ curve) :
    #s ≤ 2 * distinctDistances P + 1 := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | ⟨p, hp⟩
  · simp
  have hmap : ∀ x ∈ s.erase p, dist x p ∈ distanceSet P := by
    intro x hx
    exact Finset.mem_image.mpr ⟨(x, p), Finset.mem_offDiag.mpr
      ⟨hsP (mem_of_mem_erase hx), hsP hp, ne_of_mem_erase hx⟩, rfl⟩
  have h := Finset.card_le_mul_card_image_of_maps_to hmap 2 (by
    intro r _
    apply fiber_card_le_two curve p (hsC p hp) hcurve _ r
    intro x hx
    obtain ⟨hx, hr⟩ := mem_filter.mp hx
    exact ⟨hsC x (mem_of_mem_erase hx), ne_of_mem_erase hx, hr⟩)
  change #(s.erase p) ≤ 2 * distinctDistances P at h
  rw [← card_erase_add_one hp]
  exact Nat.add_le_add_right h 1

/-- Count blocks when at most k collinear or cospherical pieces contain half
the points. Their distance values are measured in the entire union. -/
private theorem curve_packing (k : ℕ) (hk : 0 < k) (F G : Finset (Finset ℝ²))
    (hdis : (F : Set (Finset ℝ²)).PairwiseDisjoint id)
    (hsize : ∀ T ∈ F, T.card = k) (hg : G.card ≤ k)
    (hpieces : ∀ T ∈ G, T ⊆ F.biUnion id ∧
      (Collinear ℝ (T : Set ℝ²) ∨ Cospherical (T : Set ℝ²)))
    (hhalf : (F.biUnion id).card ≤ 2*(G.biUnion id).card) :
    F.card ≤ 4*distinctDistances (F.biUnion id)+2 := by
  classical
  let S := F.biUnion id
  let D := distinctDistances S
  have hcov : (G.biUnion id).card ≤ k*(2*D+1) := calc
    _ ≤ ∑ T ∈ G, T.card := card_biUnion_le
    _ ≤ ∑ _T ∈ G, (2*D+1) := by
      apply sum_le_sum
      intro T hT
      obtain ⟨hsub,hcurve⟩ := hpieces T hT
      exact card_on_curve S (T : Set ℝ²) hcurve T hsub (fun _ hx => hx)
    _ ≤ _ := by simpa using Nat.mul_le_mul_right (2*D+1) hg
  have hs : S.card = F.card*k := by
    dsimp [S]; rw [card_biUnion hdis]
    calc
      _ = ∑ _T ∈ F, k := sum_congr rfl fun T hT => hsize T hT
      _ = _ := by simp
  change F.card ≤ 4*D+2
  apply Nat.le_of_mul_le_mul_right _ hk
  calc
    _ = S.card := hs.symm
    _ ≤ 2*(G.biUnion id).card := hhalf
    _ ≤ 2*(k*(2*D+1)) := Nat.mul_le_mul_left _ hcov
    _ = _ := by ring

/-- The row bound after discounting repeated intermediates. Nat division
rounds down and gives zero on shells of size at most two. -/
private theorem shell_row (s t k : ℕ) (hk : 0 < k) (hs : s ≤ k+t) :
    s ≤ 2*k + t*(t-1)/(s-2) := by
  by_cases small : s ≤ 2*k
  · exact small.trans (Nat.le_add_right _ _)
  obtain ⟨u,hu⟩ := Nat.exists_eq_add_of_le (show 2*k+1 ≤ s by omega)
  have ht : k+1+u ≤ t := by omega
  have ht' : k+u ≤ t-1 := by omega
  have hd : 0 < s-2 := by omega
  have hb : (u+1)*(s-2) ≤ t*(t-1) := by
    apply le_trans _ (Nat.mul_le_mul ht ht')
    have h := Nat.sub_add_cancel (show 2 ≤ s by omega)
    nlinarith [congrArg (fun a : ℕ => a*u) h,congrArg (fun a : ℕ => a*u) hu,
      Nat.mul_le_mul_right k hk]
  have := (Nat.le_div_iff_mul_le hd).mpr hb
  omega

/-- A sum on a retained point set can be evaluated one disjoint block at a time. -/
private theorem clipped_sum {α : Type*} [DecidableEq α] (G : Finset (Finset α))
    (B : Finset α) (hd : (G : Set (Finset α)).PairwiseDisjoint id)
    (hs : B ⊆ G.biUnion id) (f : α → ℕ) :
    (∑ U ∈ G, ∑ x ∈ U.filter (· ∈ B), f x) = ∑ x ∈ B, f x := by
  have he : ((G.biUnion id).filter (· ∈ B)) = B := by
    ext x
    exact ⟨fun h => (mem_filter.mp h).2, fun h => mem_filter.mpr ⟨hs h,h⟩⟩
  calc
    _ = ∑ x ∈ G.biUnion id, (if x ∈ B then f x else 0) := by
      simp only [sum_filter]
      exact (sum_biUnion hd).symm
    _ = _ := by rw [← sum_filter, he]

/-- If the retained targets carry a 1/q fraction of the block mass, a pin
energy bound on that subset controls the original number of blocks. -/
private theorem retained_blocks (q k g n d : ℕ) (hk : 0 < k)
    (hmass : g*k ≤ q*n) (henergy : n^2 ≤ d*(3*k*n)) : g ≤ (3*q)*d := by
  by_cases hz : n = 0
  · rw [hz, Nat.mul_zero] at hmass
    have h := (mul_eq_zero.mp (Nat.eq_zero_of_le_zero hmass)).resolve_right hk.ne'
    simp [h]
  have he : n*n ≤ (3*k*d)*n := calc
    _ = n^2 := by ring
    _ ≤ _ := henergy
    _ = _ := by ring
  have hn := Nat.le_of_mul_le_mul_right he (Nat.pos_of_ne_zero hz)
  have hb : g*k ≤ ((3*q)*d)*k := calc
    _ ≤ q*n := hmass
    _ ≤ q*(3*k*d) := Nat.mul_le_mul_left q hn
    _ = _ := by ring
  exact Nat.le_of_mul_le_mul_right hb hk

/-- A low shell-weighted count at one pin bounds the total number of blocks. -/
private theorem trimmed_pin_packing (k : ℕ) (hk : 0 < k) (F : Finset (Finset ℝ²))
    (hdis : (F : Set (Finset ℝ²)).PairwiseDisjoint id) (hsize : ∀ T ∈ F, T.card = k)
    (T : Finset ℝ²) (hT : T ∈ F) (p : ℝ²) (hp : p ∈ T) :
    let G := F.erase T
    ∀ B ⊆ G.biUnion id, (G.biUnion id).card ≤ 2*B.card →
    (∑ U ∈ G, ∑ x ∈ U.filter (· ∈ B),
        let s := (B.filter fun y => dist p y = dist p x).card
        let t := ((B \ U).filter fun y => dist p y = dist p x).card
        t*(t-1)/(s-2)) ≤ k*B.card →
    F.card ≤ 6*distinctDistances (F.biUnion id)+1 := by
  classical
  intro G B hsub hhalf hlow
  let S := F.biUnion id
  let D := distanceSet S
  have hG : (G : Set (Finset ℝ²)).PairwiseDisjoint id :=
    hdis.subset (by exact_mod_cast erase_subset T F)
  have hcard : (G.biUnion id).card = G.card*k := by
    rw [card_biUnion hG]
    calc
      _ = ∑ _U ∈ G, k := sum_congr rfl fun U hU => hsize U (mem_of_mem_erase hU)
      _ = _ := by simp
  have hmap (x) (hx : x ∈ B) : dist p x ∈ D := by
    obtain ⟨U,hU,hxU⟩ := mem_biUnion.mp (hsub hx)
    have hUT := mem_erase.mp hU
    have hne : p ≠ x := fun he => (Finset.disjoint_left.mp
      (hdis hUT.2 hT hUT.1) hxU) (he ▸ hp)
    exact mem_image.mpr ⟨(p,x),mem_offDiag.mpr ⟨mem_biUnion.mpr ⟨T,hT,hp⟩,
      mem_biUnion.mpr ⟨U,hUT.2,hxU⟩,hne⟩,rfl⟩
  let same := fun x y : ℝ² => dist p y = dist p x
  have row (U) (hU : U ∈ G) (x : ℝ²) :
      (B.filter (same x)).card ≤ k+((B \ U).filter (same x)).card := by
    have hs : B.filter (same x) ⊆ U ∪ ((B \ U).filter (same x)) := by
      intro y hy
      obtain ⟨hy,he⟩ := mem_filter.mp hy
      by_cases h : y ∈ U
      · exact mem_union_left _ h
      · exact mem_union_right _ (mem_filter.mpr ⟨mem_sdiff.mpr ⟨hy,h⟩,he⟩)
    exact (card_le_card hs).trans ((card_union_le _ _).trans_eq (by rw [hsize U (mem_of_mem_erase hU)]))
  let weight := fun (U : Finset ℝ²) (x : ℝ²) =>
    let s := (B.filter (same x)).card
    let t := ((B \ U).filter (same x)).card
    t*(t-1)/(s-2)
  change (∑ U ∈ G, ∑ x ∈ U.filter (· ∈ B), weight U x) ≤ k*B.card at hlow
  have energy : (∑ x ∈ B, (B.filter (same x)).card) ≤ 3*k*B.card := by
    rw [← clipped_sum G B hG hsub]
    calc
      _ ≤ ∑ U ∈ G, ∑ x ∈ U.filter (· ∈ B), (2*k+weight U x) :=
        sum_le_sum fun U hU => sum_le_sum fun x _ => shell_row _ _ k hk (row U hU x)
      _ = B.card*(2*k) + ∑ U ∈ G, ∑ x ∈ U.filter (· ∈ B), weight U x := by
        simp only [sum_add_distrib]
        congr 1
        simpa using (clipped_sum G B hG hsub (fun _ => 2*k))
      _ ≤ B.card*(2*k) + k*B.card := Nat.add_le_add_left hlow _
      _ = _ := by ring
  have hc := pin_count B D (dist p) hmap
  simp only [sum_boole, Nat.cast_id] at hc
  change B.card^2 ≤ D.card * (∑ x ∈ B, (B.filter (same x)).card) at hc
  have hblocks : G.card ≤ 6*D.card :=
    retained_blocks 2 k G.card B.card D.card hk (hcard ▸ hhalf)
      (hc.trans (Nat.mul_le_mul_left _ energy))
  have hF : G.card+1 = F.card := card_erase_add_one hT
  change F.card ≤ 6*D.card+1
  omega

/-- Sum pinned collision counts, charging distinct ordered target pairs only
when their perpendicular bisector contains more than k pins. -/
private theorem rich_bisector_bound (S : Finset ℝ²) (k L : ℕ) (hk : 0 < k) :
    let w := fun x y : ℝ² => (S.filter fun p => dist p y = dist p x).card
    (∑ x ∈ S, ∑ y ∈ S.erase x, if k < w x y then w x y else 0) ≤ L*k*S.card^2 →
    S.card ≤ (L+2)*k*(distinctDistances S+1) := by
  classical
  intro w hrich
  let n := S.card
  let D := insert 0 (distanceSet S)
  let c := fun p x y : ℝ² => if dist p y = dist p x then 1 else (0:ℕ)
  have hm (p) (hp : p ∈ S) (x) (hx : x ∈ S) : dist p x ∈ D := by
    by_cases he : p = x
    · simp [he,D]
    · exact mem_insert_of_mem (mem_image.mpr ⟨(p,x),mem_offDiag.mpr ⟨hp,hx,he⟩,rfl⟩)
  have hpins : n^3 ≤ D.card * ∑ x ∈ S, ∑ y ∈ S, w x y := calc
    _ = ∑ _p ∈ S, n^2 := by simp [n,pow_succ,Nat.mul_comm]
    _ ≤ ∑ p ∈ S, D.card * (∑ x ∈ S, ∑ y ∈ S, c p x y) :=
      sum_le_sum fun p hp => pin_count S D (dist p) (hm p hp)
    _ = D.card * (∑ x ∈ S, ∑ y ∈ S, ∑ p ∈ S, c p x y) := by
      rw [← mul_sum, sum_comm (s := S) (t := S)]
      congr 1
      exact sum_congr rfl fun _ _ => sum_comm
    _ = _ := by simp [c,w]
  let heavy := fun x y : ℝ² => if k < w x y then w x y else 0
  have row (x) (hx : x ∈ S) :
      (∑ y ∈ S, w x y) ≤ n + (n-1)*k + ∑ y ∈ S.erase x, heavy x y := by
    rw [← sum_erase_add S (w x) hx]
    have h : (∑ y ∈ S.erase x, w x y) ≤ ∑ y ∈ S.erase x, (k+heavy x y) := by
      apply sum_le_sum
      intro y _
      dsimp [heavy]
      split <;> omega
    have hd : w x x = n := by simp [w,n]
    simp only [sum_add_distrib,sum_const,smul_eq_mul,card_erase_of_mem hx] at h
    change _ ≤ (n-1)*k + _ at h
    omega
  have mass : (∑ x ∈ S, ∑ y ∈ S, w x y) ≤ (L+2)*k*n^2 := calc
    _ ≤ ∑ x ∈ S, (n+(n-1)*k + ∑ y ∈ S.erase x, heavy x y) := sum_le_sum row
    _ = n*(n+(n-1)*k) + ∑ x ∈ S, ∑ y ∈ S.erase x, heavy x y := by simp [n,sum_add_distrib,Nat.mul_add]
    _ ≤ n*(n+n*k) + L*k*n^2 := Nat.add_le_add (by gcongr; exact Nat.sub_le ..) hrich
    _ = n^2 + (L+1)*k*n^2 := by ring
    _ ≤ (L+2)*k*n^2 := by nlinarith [Nat.mul_le_mul_right (n^2) hk]
  by_cases hn : n = 0
  · change n ≤ _; simp [hn]
  have h : n*n^2 ≤ ((L+2)*k*D.card)*n^2 := calc
    _ = n^3 := by ring
    _ ≤ _ := hpins.trans (Nat.mul_le_mul_left _ mass)
    _ = _ := by ring
  exact (Nat.le_of_mul_le_mul_right h (pow_pos (Nat.pos_of_ne_zero hn) 2)).trans
    (Nat.mul_le_mul_left _ (card_insert_le _ _))

/-- Delete any selection of ordered target pairs in which each pair of distinct
pins occurs at most k² times. Its rich-bisector incidence mass is at most kn². -/
private theorem low_multiplicity_mass (S : Finset ℝ²) (k : ℕ) (hk : 0 < k)
    (G : ℝ² → Finset ℝ²) :
    let W := fun x y : ℝ² => S.filter fun p => dist p y = dist p x
    (∀ r ∈ S.offDiag, (∑ x ∈ S, ((G x).filter fun y => r ∈ (W x y).offDiag).card) ≤ k^2) →
    (∑ x ∈ S, ∑ y ∈ G x, if k < (W x y).card then (W x y).card else 0) ≤ k*S.card^2 := by
  classical
  intro W hcap
  let m := fun x y : ℝ² => if k < (W x y).card then (W x y).card else 0
  let I := fun (r : ℝ² × ℝ²) (x y : ℝ²) => if r ∈ (W x y).offDiag then 1 else (0:ℕ)
  have hpair (x y : ℝ²) : k*m x y ≤ ∑ r ∈ S.offDiag, I r x y := by
    have hsub : (W x y).offDiag ⊆ S.offDiag := by
      intro r hr
      obtain ⟨h₁,h₂,hne⟩ := mem_offDiag.mp hr
      exact mem_offDiag.mpr ⟨(mem_filter.mp h₁).1,(mem_filter.mp h₂).1,hne⟩
    have he : (S.offDiag.filter fun r => r ∈ (W x y).offDiag) = (W x y).offDiag := by
      ext r; simp only [mem_filter]; exact ⟨And.right,fun h => ⟨hsub h,h⟩⟩
    simp only [I,sum_boole,Nat.cast_id,he,offDiag_card]
    dsimp [m]
    split
    · rename_i h
      have hle := Nat.mul_le_mul_right (W x y).card (show k+1 ≤ (W x y).card from h)
      rw [Nat.add_mul,one_mul] at hle
      omega
    · simp
  have hc (r) (hr : r ∈ S.offDiag) : (∑ x ∈ S, ∑ y ∈ G x, I r x y) ≤ k^2 := by
    simpa only [I,sum_boole,Nat.cast_id] using hcap r hr
  have htotal : k*(∑ x ∈ S, ∑ y ∈ G x, m x y) ≤ k*(k*S.card^2) := calc
    _ = ∑ x ∈ S, ∑ y ∈ G x, k*m x y := by simp only [mul_sum]
    _ ≤ ∑ x ∈ S, ∑ y ∈ G x, ∑ r ∈ S.offDiag, I r x y :=
      sum_le_sum fun x _ => sum_le_sum fun y _ => hpair x y
    _ = ∑ r ∈ S.offDiag, ∑ x ∈ S, ∑ y ∈ G x, I r x y := by
      rw [sum_comm (s := S.offDiag) (t := S)]
      exact sum_congr rfl fun _ _ => sum_comm
    _ ≤ ∑ _r ∈ S.offDiag, k^2 := sum_le_sum hc
    _ ≤ S.card^2*k^2 := by
      simp only [sum_const,smul_eq_mul,offDiag_card,pow_two]
      exact Nat.mul_le_mul_right _ (Nat.sub_le ..)
    _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left htotal hk

/-- On one target line through x, a circle about p contains at most one target
other than x at the same distance as x. -/
private theorem line_partner (p x : ℝ²) (T : Finset ℝ²)
    (hl : Collinear ℝ (insert x (T : Set ℝ²))) :
    ((T.erase x).filter fun y => dist p y = dist p x).card ≤ 1 := by
  classical
  apply card_le_one.mpr
  intro a ha b hb
  obtain ⟨ha,hea⟩ := mem_filter.mp ha
  obtain ⟨hb,heb⟩ := mem_filter.mp hb
  obtain ⟨hax,ha⟩ := mem_erase.mp ha
  obtain ⟨hbx,hb⟩ := mem_erase.mp hb
  by_contra hab
  let E : Set ℝ² := {z | dist z p = dist x p}
  have hcos : Cospherical E := ⟨p,dist x p,fun _ h => h⟩
  have hi := hcos.affineIndependent_of_mem_of_ne (show x ∈ E from rfl)
    (show a ∈ E by simpa [E,dist_comm] using hea)
    (show b ∈ E by simpa [E,dist_comm] using heb) hax.symm hbx.symm hab
  exact (affineIndependent_iff_not_collinear_set.mp hi)
    (hl.subset (by simp [Set.insert_subset_iff,ha,hb]))

/-- Up to k target directions at each endpoint contribute at most kn² rich
incidences. The directions can vary independently with the first endpoint. -/
private theorem direction_mass (S : Finset ℝ²) (k : ℕ) (H : ℝ² → Finset ℝ²)
    (hne : ∀ x ∈ S, x ∉ H x)
    (hc : ∀ x ∈ S, ∃ J : Finset (Finset ℝ²), J.card ≤ k ∧ H x ⊆ J.biUnion id ∧
      ∀ T ∈ J, Collinear ℝ (insert x (T : Set ℝ²))) :
    let w := fun x y : ℝ² => (S.filter fun p => dist p y = dist p x).card
    (∑ x ∈ S, ∑ y ∈ H x, if k < w x y then w x y else 0) ≤ k*S.card^2 := by
  classical
  intro w
  have row (x) (hx : x ∈ S) (p : ℝ²) :
      ((H x).filter fun y => dist p y = dist p x).card ≤ k := by
    obtain ⟨J,hJ,hsub,hline⟩ := hc x hx
    let piece := fun T : Finset ℝ² => (T.erase x).filter fun y => dist p y = dist p x
    have hs : (H x).filter (fun y => dist p y = dist p x) ⊆ J.biUnion piece := by
      intro y hy
      obtain ⟨hy,he⟩ := mem_filter.mp hy
      obtain ⟨T,hT,hyT⟩ := mem_biUnion.mp (hsub hy)
      have hyx : y ≠ x := fun h => hne x hx (h ▸ hy)
      exact mem_biUnion.mpr ⟨T,hT,mem_filter.mpr ⟨mem_erase.mpr ⟨hyx,hyT⟩,he⟩⟩
    exact (card_le_card hs).trans ((card_biUnion_le_card_mul J piece 1
      (fun T hT => line_partner p x T (hline T hT))).trans (by simpa using hJ))
  calc
    _ ≤ ∑ x ∈ S, ∑ y ∈ H x, w x y := by
      apply sum_le_sum; intro x hx; apply sum_le_sum; intro y hy; split <;> omega
    _ = ∑ x ∈ S, ∑ p ∈ S, ((H x).filter fun y => dist p y = dist p x).card := by
      apply sum_congr rfl
      intro x hx
      simpa only [w,sum_boole,Nat.cast_id] using
        (sum_comm (s := H x) (t := S) (f := fun y p => if dist p y = dist p x then 1 else (0:ℕ)))
    _ ≤ ∑ _x ∈ S, ∑ _p ∈ S, k := sum_le_sum fun x hx => sum_le_sum fun p _ => row x hx p
    _ = _ := by simp; ring

/-- With one factor and one corresponding endpoint fixed, the image of the
second endpoint is unique. Thus k factors account for at most kn matches per
source segment, including all translations when factor one is selected. -/
private theorem rotation_bound (S : Finset ℝ²) (k : ℕ) (hk : 0 < k) (A : Finset ℂ)
    (hA : A.card ≤ k) :
    let z := fun p : ℝ² => Complex.mk (p 0) (p 1)
    let E := S.offDiag
    let f := fun e t : ℝ² × ℝ² => (z t.2-z t.1)/(z e.2-z e.1)
    (∑ e ∈ E, (E.filter fun t => dist t.1 t.2 = dist e.1 e.2 ∧ f e t ∉ A).card) ≤ k*S.card^3 →
      S.card ≤ 2*k*(distinctDistances S+1) := by
  classical
  intro z E f hrest
  let n := S.card
  let D := distanceSet S
  have inj : Function.Injective z := by
    intro x y h
    have h₀ := congrArg Complex.re h
    have h₁ := congrArg Complex.im h
    ext i
    fin_cases i
    · exact h₀
    · exact h₁
  have row (e : ℝ² × ℝ²) (he : e ∈ E) :
      (E.filter fun t => dist t.1 t.2 = dist e.1 e.2).card ≤ k*n +
        (E.filter fun t => dist t.1 t.2 = dist e.1 e.2 ∧ f e t ∉ A).card := by
    let U := E.filter fun t => f e t ∈ A
    have hnz : z e.2-z e.1 ≠ 0 := sub_ne_zero.mpr (inj.ne (mem_offDiag.mp he).2.2.symm)
    have hu : U.card ≤ (A ×ˢ S).card := by
      apply card_le_card_of_injOn (fun t => (f e t,t.1))
      · intro t ht
        obtain ⟨ht,ha⟩ := mem_filter.mp ht
        exact mem_product.mpr ⟨ha,(mem_offDiag.mp ht).1⟩
      · intro t ht u hu heq
        have h₁ : t.1 = u.1 := congrArg Prod.snd heq
        have h₂ : (z t.2-z t.1)/(z e.2-z e.1) = (z u.2-z u.1)/(z e.2-z e.1) := congrArg Prod.fst heq
        have he' := (div_left_inj' hnz).mp h₂
        rw [h₁] at he'
        exact Prod.ext h₁ (inj (sub_left_inj.mp he'))
    have hs : (E.filter fun t => dist t.1 t.2 = dist e.1 e.2) ⊆
        U ∪ (E.filter fun t => dist t.1 t.2 = dist e.1 e.2 ∧ f e t ∉ A) := by
      intro t ht
      obtain ⟨ht,hd⟩ := mem_filter.mp ht
      by_cases h : f e t ∈ A
      · exact mem_union_left _ (mem_filter.mpr ⟨ht,h⟩)
      · exact mem_union_right _ (mem_filter.mpr ⟨ht,hd,h⟩)
    rw [card_product] at hu
    exact (card_le_card hs).trans ((card_union_le ..).trans
      (Nat.add_le_add_right (hu.trans (Nat.mul_le_mul_right _ hA)) _))
  have hE : E.card + n = n*n := by
    dsimp [E,n]; rw [offDiag_card,Nat.sub_add_cancel]
    exact Nat.le_mul_self _
  have hc := pin_count E D (fun e => dist e.1 e.2)
    (fun e he => mem_image.mpr ⟨e,he,rfl⟩)
  simp only [sum_boole,Nat.cast_id] at hc
  have hsum : (∑ e ∈ E, (E.filter fun t => dist t.1 t.2 = dist e.1 e.2).card) ≤ 2*k*n^3 := calc
    _ ≤ _ := sum_le_sum row
    _ = E.card*(k*n) + (∑ e ∈ E, (E.filter fun t =>
        dist t.1 t.2 = dist e.1 e.2 ∧ f e t ∉ A).card) := by simp [sum_add_distrib]
    _ ≤ (n*n)*(k*n) + k*n^3 := Nat.add_le_add (Nat.mul_le_mul_right _ (by omega)) hrest
    _ = _ := by ring
  have hs := hc.trans (Nat.mul_le_mul_left D.card hsum)
  by_cases hn : n = 0
  · change n ≤ _; simp [hn]
  have hsq := congrArg (fun v : ℕ => v^2) hE
  have hlin := congrArg (fun v : ℕ => v*n) hE
  have hpow : n*n^3 ≤ (2*k*D.card+2)*n^3 := by
    nlinarith only [hs,hsq,hlin,Nat.zero_le (n^2)]
  have h := Nat.le_of_mul_le_mul_right hpow (pow_pos (Nat.pos_of_ne_zero hn) 3)
  change n ≤ 2*k*(D.card+1)
  rw [Nat.mul_add,Nat.mul_one]
  omega

/-- The remaining packing case implies the unrestricted block estimate. -/
private theorem packing_from_curves (packing : H2) :
  ∃ C : ℕ, ∀ (k : ℕ) (F : Finset (Finset ℝ²)), 0 < k →
    (F : Set (Finset ℝ²)).PairwiseDisjoint id →
    (∀ T ∈ F, T.card = k ∧ ∃ a b c : ℝ, (a ≠ 0 ∨ b ≠ 0) ∧ ∀ p ∈ T, a*p 0+b*p 1=c) →
    ((F.biUnion id).card : ℝ) ≤ Real.exp ((k : ℝ)^2) →
    F.card ≤ C * (distinctDistances (F.biUnion id)+1) := by
  classical
  obtain ⟨C,pack⟩ := packing
  refine ⟨max C 6,?_⟩
  intro k F hk hdis hline hcap
  by_cases spread : (∀ G : Finset (Finset ℝ²), G.card ≤ k →
      (∀ T ∈ G, T ⊆ F.biUnion id ∧ (Collinear ℝ (T : Set ℝ²) ∨ Cospherical (T : Set ℝ²))) →
      2*(G.biUnion id).card < (F.biUnion id).card)
  · by_cases many : (∀ T ∈ F, ∀ p ∈ T,
      let G := F.erase T
      ∀ B ⊆ G.biUnion id, (G.biUnion id).card ≤ 2*B.card →
      k*B.card < ∑ U ∈ G, ∑ x ∈ U.filter (· ∈ B),
        let s := (B.filter fun y => dist p y = dist p x).card
        let t := ((B \ U).filter fun y => dist p y = dist p x).card
        t*(t-1)/(s-2))
    · by_cases persistent : (let S := F.biUnion id
      let W := fun x y : ℝ² => S.filter fun p => dist p y = dist p x
      ∀ G : ℝ² → Finset ℝ², (∀ x ∈ S, G x ⊆ S.erase x) →
        (∀ r ∈ S.offDiag, (∑ x ∈ S, ((G x).filter fun y => r ∈ (W x y).offDiag).card) ≤ k^2) →
        ∀ H : ℝ² → Finset ℝ², (∀ x ∈ S, H x ⊆ S.erase x \ G x) →
          (∀ x ∈ S, ∃ J : Finset (Finset ℝ²), J.card ≤ k ∧ H x ⊆ J.biUnion id ∧
            ∀ T ∈ J, Collinear ℝ (insert x (T : Set ℝ²))) →
          2*k*S.card^2 < ∑ x ∈ S, ∑ y ∈ (S.erase x \ G x) \ H x, if k < (W x y).card then (W x y).card else 0)
      · by_cases rotations : (let S := F.biUnion id
      let z := fun p : ℝ² => Complex.mk (p 0) (p 1)
      let E := S.offDiag
      let f := fun e t : ℝ² × ℝ² => (z t.2-z t.1)/(z e.2-z e.1)
      ∀ A : Finset ℂ, A.card ≤ k → k*S.card^3 <
        ∑ e ∈ E, (E.filter fun t => dist t.1 t.2 = dist e.1 e.2 ∧ f e t ∉ A).card)
        · exact (pack k F hk hdis hline hcap spread many persistent rotations).trans
            (Nat.mul_le_mul_right _ (le_max_left C 6))
        dsimp only at rotations
        push Not at rotations
        obtain ⟨A,hA,hrem⟩ := rotations
        have hb := rotation_bound (F.biUnion id) k hk A hA hrem
        have hs : (F.biUnion id).card = F.card*k := by
          rw [card_biUnion hdis]
          calc
            _ = ∑ _T ∈ F, k := sum_congr rfl fun T hT => (hline T hT).1
            _ = _ := by simp
        rw [hs,Nat.mul_right_comm 2 k] at hb
        exact (Nat.le_of_mul_le_mul_right hb hk).trans
          (Nat.mul_le_mul_right _ (by omega : 2 ≤ max C 6))
      let S := F.biUnion id
      let W := fun x y : ℝ² => S.filter fun p => dist p y = dist p x
      let m := fun x y : ℝ² => if k < (W x y).card then (W x y).card else 0
      dsimp only at persistent
      push Not at persistent
      obtain ⟨G,hsub,hcapG,H,hsubH,hcovH,hrest⟩ := persistent
      have hlow := low_multiplicity_mass S k hk G hcapG
      change (∑ x ∈ S, ∑ y ∈ G x, m x y) ≤ k*S.card^2 at hlow
      have hdir := direction_mass S k H (fun x hx h =>
        (mem_erase.mp (mem_sdiff.mp (hsubH x hx h)).1).1 rfl) hcovH
      change (∑ x ∈ S, ∑ y ∈ H x, m x y) ≤ k*S.card^2 at hdir
      change (∑ x ∈ S, ∑ y ∈ (S.erase x \ G x) \ H x, m x y) ≤ 2*k*S.card^2 at hrest
      have hsplit : (∑ x ∈ S, ∑ y ∈ S.erase x \ G x, m x y) =
          (∑ x ∈ S, ∑ y ∈ (S.erase x \ G x) \ H x, m x y) + ∑ x ∈ S, ∑ y ∈ H x, m x y := by
        rw [← sum_add_distrib]
        exact sum_congr rfl fun x hx => (sum_sdiff (hsubH x hx)).symm
      have he : (∑ x ∈ S, ∑ y ∈ S.erase x, m x y) =
          (∑ x ∈ S, ∑ y ∈ S.erase x \ G x, m x y) + ∑ x ∈ S, ∑ y ∈ G x, m x y := by
        rw [← sum_add_distrib]
        exact sum_congr rfl fun x hx => (sum_sdiff (hsub x hx)).symm
      have htotal : (∑ x ∈ S, ∑ y ∈ S.erase x, m x y) ≤ 4*k*S.card^2 := by
        rw [he,hsplit,Nat.mul_assoc]
        rw [Nat.mul_assoc] at hrest
        omega
      have hb := rich_bisector_bound S k 4 hk htotal
      have hs : S.card = F.card*k := by
        dsimp [S]; rw [card_biUnion hdis]
        calc
          _ = ∑ _T ∈ F, k := sum_congr rfl fun T hT => (hline T hT).1
          _ = _ := by simp
      change S.card ≤ 6*k*(distinctDistances S+1) at hb
      rw [hs,Nat.mul_right_comm 6 k] at hb
      exact (Nat.le_of_mul_le_mul_right hb hk).trans
        (Nat.mul_le_mul_right _ (le_max_right C 6))
    dsimp only at many
    push Not at many
    obtain ⟨T,hT,p,hp,B,hsub,hhalf,hlow⟩ := many
    have h := trimmed_pin_packing k hk F hdis (fun U hU => (hline U hU).1) T hT p hp B hsub hhalf
    have hh := h (by simpa using hlow)
    exact hh.trans ((by omega : 6*distinctDistances (F.biUnion id)+1 ≤
      6*(distinctDistances (F.biUnion id)+1)).trans (Nat.mul_le_mul_right _ (le_max_right C 6)))
  push Not at spread
  obtain ⟨G,hg,hpieces,hhalf⟩ := spread
  have h := curve_packing k hk F G hdis (fun T hT => (hline T hT).1) hg hpieces hhalf
  exact h.trans ((by omega : 4*distinctDistances (F.biUnion id)+2 ≤
    4*(distinctDistances (F.biUnion id)+1)).trans (Nat.mul_le_mul_right _ (by omega : 4 ≤ max C 6)))

private theorem finite_bound (sparse : H1) (packing : H2) :
    ∃ C : ℕ, ∀ (S : Finset ℝ²) (k : ℕ), 0 < k → (S.card : ℝ) ≤ Real.exp ((k : ℝ)^2) →
      S.card ≤ k*(C+1)*(distinctDistances S+1) := by
  classical
  obtain ⟨C,pack⟩ := packing_from_curves packing
  refine ⟨C,?_⟩
  intro S k hk hsize
  obtain ⟨F,hdis,hline,hsub,hres⟩ := extract_blocks S k hk
  let U := F.biUnion id
  have hu : U.card = F.card*k := by
    rw [show U=F.biUnion id from rfl,card_biUnion hdis]
    calc
      _ = ∑ _T ∈ F, k := sum_congr rfl fun T hT => (hline T hT).1
      _ = _ := by simp
  have hpack := pack k F hk hdis hline ((by exact_mod_cast card_le_card hsub : (U.card:ℝ) ≤ S.card).trans hsize)
  have hp : F.card ≤ C*(distinctDistances S+1) :=
    hpack.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right (distances_mono hsub) 1))
  have hr := sparse (S \ U) (k-1) (fun a b c h => by dsimp only [U]; have := hres a b c h; omega)
  rw [Nat.sub_add_cancel hk] at hr
  have hleft := hr.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right (distances_mono sdiff_subset) 1))
  calc
    S.card = (S \ U).card + U.card := (card_sdiff_add_card_eq_card hsub).symm
    _ ≤ k*(distinctDistances S+1) + (C*(distinctDistances S+1))*k := by
      rw [hu]; exact Nat.add_le_add hleft (Nat.mul_le_mul_right _ hp)
    _ = _ := by ring

theorem main : H1 → H2 → type_of% @Erdos89.erdos_89 := by
  classical
  intro sparse packing
  obtain ⟨C,hfinite⟩ := finite_bound sparse packing
  apply Asymptotics.IsBigO.of_bound (4*((C:ℝ)+1))
  filter_upwards [eventually_ge_atTop (⌈Real.exp 1⌉₊+2)] with n hn
  have hn2 : 2 ≤ n := by omega
  have hnpos : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hexp : Real.exp 1 ≤ (n:ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (by omega : ⌈Real.exp 1⌉₊ ≤ n))
  have hlog : 1 ≤ Real.log (n:ℝ) := by simpa using Real.log_le_log (Real.exp_pos _) hexp
  let z := Real.sqrt (Real.log n)
  have hz : 1 ≤ z := by simpa [z] using Real.sqrt_le_sqrt hlog
  let k := ⌈z⌉₊
  have hceil : z ≤ (k:ℝ) := Nat.le_ceil _
  have hk : 0 < k := by exact_mod_cast (zero_lt_one.trans_le (hz.trans hceil))
  have hround : (k:ℝ) ≤ 2*z := by
    have h := Nat.ceil_lt_add_one (zero_le_one.trans hz)
    dsimp [k]; linarith
  have hcap : (n:ℝ) ≤ Real.exp ((k:ℝ)^2) := by
    rw [← Real.exp_log hnpos]
    apply Real.exp_le_exp.mpr
    have he : z^2 = Real.log n := Real.sq_sqrt (zero_le_one.trans hlog)
    nlinarith [mul_nonneg (sub_nonneg.mpr hceil) (by positivity : 0 ≤ (k:ℝ)+z)]
  obtain ⟨S₀,h₀⟩ := Infinite.exists_subset_card_eq ℝ² n
  obtain ⟨S,hS,hD⟩ := Nat.sInf_mem (show
    {d : ℕ | ∃ S : Finset ℝ², S.card=n ∧ distinctDistances S=d}.Nonempty from ⟨_,S₀,h₀,rfl⟩)
  change distinctDistances S = minimalDistinctDistances ℝ² n at hD
  have hfb := hfinite S k hk (hS ▸ hcap)
  have hd : 0 < distinctDistances S := by
    obtain ⟨x,hx,y,hy,hxy⟩ := one_lt_card.mp (by omega : 1 < S.card)
    exact card_pos.mpr ⟨_,mem_image.mpr ⟨(x,y),mem_offDiag.mpr ⟨hx,hy,hxy⟩,rfl⟩⟩
  let D : ℝ := distinctDistances S
  have hd' : (1:ℝ) ≤ D := by dsimp [D]; exact_mod_cast (show 1 ≤ distinctDistances S from hd)
  rw [hS] at hfb
  have hh : (n:ℝ) ≤ (k:ℝ)*((C:ℝ)+1)*(D+1) := by dsimp [D]; exact_mod_cast hfb
  change ‖(n:ℝ)/z‖ ≤ 4*((C:ℝ)+1)*‖(minimalDistinctDistances ℝ² n : ℝ)‖
  rw [← hD,Real.norm_eq_abs,abs_of_nonneg (by positivity),Real.norm_eq_abs,Nat.abs_cast,
    div_le_iff₀ (zero_lt_one.trans_le hz)]
  change (n:ℝ) ≤ 4*((C:ℝ)+1)*D*z
  calc
    _ ≤ _ := hh
    _ ≤ (2*z)*((C:ℝ)+1)*(2*D) := by gcongr; linarith
    _ = _ := by ring

end OMA.R_Erdos89_erdos_89_R2
