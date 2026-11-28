import OMAReductions.R_Erdos89_erdos_89_R1

-- Reduction of Erdos89.erdos_89.R1.H2. Credit: @wispiANt
open Filter Finset EuclideanGeometry

namespace OMA.R_Erdos89_erdos_89_R1_H2_R1

/-- Packing for squarefree diagonal forms. Count disjoint collinear k-point
blocks using all form values realized on their union, including cross-block
differences. Any k lines cover less than half the union. Every subset containing
at least half the points must satisfy the width condition in every normalized
tilted model: when its height is positive, its squared width exceeds d times
its height times k.
The constant is independent of the form and the block size. -/
def H1 : Prop :=
  ∃ C : ℕ, ∀ (d k : ℕ) (F : Finset (Finset (ℤ × ℤ))), 0 < d → Squarefree d → 0 < k →
    (F : Set (Finset (ℤ × ℤ))).PairwiseDisjoint id →
    (∀ T ∈ F, T.card = k ∧ ∃ a b c : ℤ, (a ≠ 0 ∨ b ≠ 0) ∧ ∀ p ∈ T, a*p.1+b*p.2=c) →
    ((F.biUnion id).card : ℝ) ≤ Real.exp ((k : ℝ)^2) →
    (∀ G : Finset (Finset (ℤ × ℤ)), G.card ≤ k →
      (∀ T ∈ G, T ⊆ F.biUnion id ∧ ∃ a b c : ℤ, (a ≠ 0 ∨ b ≠ 0) ∧ ∀ p ∈ T, a*p.1+b*p.2=c) →
      2*(G.biUnion id).card < (F.biUnion id).card) →
    (let S := F.biUnion id
     (∀ A : Finset (ℤ × ℤ), A ⊆ S → S.card ≤ 2*A.card → ∀ a b : ℤ, (a ≠ 0 ∨ b ≠ 0) →
      let R := A.image (fun p : ℤ × ℤ => (a*p.1-(d:ℤ)*b*p.2, b*p.1+a*p.2))
      ∀ (g : ℤ) (o : ℤ × ℤ) (B : Finset (ℤ × ℤ)), 0 < g →
        B.image (fun z : ℤ × ℤ => (g*z.1+o.1,g*z.2+o.2)) = R →
        ∀ p ∈ B, ∀ t ∈ B, p.2 < t.2 →
        ∃ z ∈ B, ∃ u ∈ B, (d:ℤ)*(t.2-p.2)*k < (z.1-u.1)^2)) →
    let q := fun z : ℤ × ℤ => z.1^2+(d:ℤ)*z.2^2
    F.card ≤ C * (((F.biUnion id).offDiag.image fun xy => q (xy.1-xy.2)).card+1)

/-- Extremal comparison. A positive fraction of the points can be matched by
an integer configuration under some positive definite integral form, within the
original budget of distinct distances. Only cardinalities are compared. -/
def H2 : Prop :=
  ∃ K : ℕ, 0 < K ∧ ∃ N₀ : ℕ,
    ∀ P : Finset {p : ℝ² // ∀ i : Fin 2, IsIntegral ℤ (p i)}, N₀ ≤ P.card →
      ∃ a b c : ℤ, 0 < a ∧ b^2 < 4*a*c ∧ ∃ S : Finset (ℤ × ℤ),
        S.card ≤ P.card ∧ P.card ≤ K * S.card ∧
        let q := fun z : ℤ × ℤ => a*z.1^2 + b*z.1*z.2 + c*z.2^2
        (S.offDiag.image fun xy => q (xy.1 - xy.2)).card ≤ distinctDistances P

section Arithmetic

/-- A single integral linear embedding works for every finite subset. It preserves
the entire set of form values on distinct pairs up to one common scaling. -/
private theorem squarefree_model (a b c : ℤ) (ha : 0 < a) (hdisc : b^2 < 4*a*c) :
    let values := fun (q : ℤ × ℤ → ℤ) (T : Finset (ℤ × ℤ)) => T.offDiag.image fun xy => q (xy.1-xy.2)
    ∃ d : ℕ, 0 < d ∧ Squarefree d ∧ ∃ F : ℤ × ℤ → ℤ × ℤ, Function.Injective F ∧
      ∀ S : Finset (ℤ × ℤ), (S.image F).card = S.card ∧
        values (fun z => z.1^2 + (d : ℤ)*z.2^2) (S.image F) =
          (values (fun z => a*z.1^2 + b*z.1*z.2 + c*z.2^2) S).image (4*a * ·) := by
  intro values
  have hp : 0 < 4*a*c - b^2 := by omega
  obtain ⟨d,r,hd,hr,he,hsq⟩ := Nat.sq_mul_squarefree_of_pos (show 0 < (4*a*c-b^2).toNat by omega)
  have he' : (r : ℤ)^2 * d = 4*a*c - b^2 := by
    simpa only [Nat.cast_mul, Nat.cast_pow, Int.toNat_of_nonneg hp.le] using
      congrArg (fun n : ℕ => (n : ℤ)) he
  let F (p : ℤ × ℤ) : ℤ × ℤ := (2*a*p.1+b*p.2, (r:ℤ)*p.2)
  have hinj : Function.Injective F := by
    rintro ⟨x,y⟩ ⟨u,v⟩ h
    have hxy := congrArg Prod.fst h
    have hyv := congrArg Prod.snd h
    change (r:ℤ)*y = (r:ℤ)*v at hyv
    have : y = v := mul_left_cancel₀ (by exact_mod_cast hr.ne') hyv
    subst v
    change 2*a*x+b*y = 2*a*u+b*y at hxy
    exact Prod.ext (mul_left_cancel₀ (by positivity : 2*a ≠ 0) (add_right_cancel hxy)) rfl
  refine ⟨d, hd, hsq, F, hinj, fun S => ⟨Finset.card_image_of_injective _ hinj, ?_⟩⟩
  let Q := fun z : ℤ × ℤ => a*z.1^2 + b*z.1*z.2 + c*z.2^2
  let D := fun z : ℤ × ℤ => z.1^2 + (d:ℤ)*z.2^2
  have hval (p t : ℤ × ℤ) : D (F p - F t) = 4*a*Q (p-t) := by
    dsimp [D, F, Q]
    linear_combination (p.2-t.2)^2 * he'
  have mem_values (q : ℤ × ℤ → ℤ) (T : Finset (ℤ × ℤ)) (w : ℤ) :
      w ∈ values q T ↔ ∃ p ∈ T, ∃ t ∈ T, p ≠ t ∧ q (p-t) = w := by
    constructor
    · intro h
      obtain ⟨⟨p,t⟩, hpt, hval⟩ := Finset.mem_image.mp h
      obtain ⟨hp, ht, hne⟩ := Finset.mem_offDiag.mp hpt
      exact ⟨p,hp,t,ht,hne,hval⟩
    · rintro ⟨p,hp,t,ht,hne,hval⟩
      exact Finset.mem_image.mpr ⟨(p,t), Finset.mem_offDiag.mpr ⟨hp,ht,hne⟩, hval⟩
  ext w
  change w ∈ values D (S.image F) ↔ w ∈ (values Q S).image _
  rw [mem_values, Finset.mem_image]
  constructor
  · rintro ⟨u, hu, v, hv, hne, rfl⟩
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hv
    exact ⟨_, (mem_values ..).mpr ⟨p,hp,t,ht,fun e => hne (congrArg F e),rfl⟩,
      (hval p t).symm⟩
  · rintro ⟨w,hw,rfl⟩
    obtain ⟨p,hp,t,ht,hne,rfl⟩ := (mem_values ..).mp hw
    exact ⟨_,Finset.mem_image_of_mem F hp,_,Finset.mem_image_of_mem F ht,hinj.ne hne,hval p t⟩

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


/-- A configuration with at most K points on each affine line already has
at least n/(K+1)-1 distinct nonzero values. The coefficient is uniform in d. -/
private theorem sparse_lines_bound (d : ℤ) (hd : 0 < d) (S : Finset (ℤ × ℤ)) (K : ℕ)
    (hl : ∀ a b c : ℤ, (a ≠ 0 ∨ b ≠ 0) →
      (S.filter fun p => a*p.1 + b*p.2 = c).card ≤ K) :
    let q := fun z : ℤ × ℤ => z.1^2+(d:ℤ)*z.2^2
    S.card ≤ (K+1)*((S.offDiag.image fun xy => q (xy.1-xy.2)).card+1) := by
  classical
  intro q
  let V := S.offDiag.image fun xy => q (xy.1-xy.2)
  let D := insert 0 V
  have hm (p) (hp : p ∈ S) (x) (hx : x ∈ S) : q (x-p) ∈ D := by
    by_cases he : x = p
    · simp [he,q,D]
    · exact mem_insert_of_mem (mem_image.mpr ⟨(x,p), mem_offDiag.mpr ⟨hx,hp,he⟩,rfl⟩)
  have hb (x) (_hx : x ∈ S) (y) (_hy : y ∈ S) (hne : y ≠ x) :
      (S.filter fun p => q (y-p) = q (x-p)).card ≤ K := by
    have bisector (p : ℤ × ℤ) : q (y-p) = q (x-p) ↔
        2*(y.1-x.1)*p.1 + 2*d*(y.2-x.2)*p.2 = q y-q x := by
      dsimp [q]
      constructor <;> intro h <;> linear_combination -h
    simp_rw [bisector]
    apply hl
    by_cases h : y.1 = x.1
    · right
      have ht : y.2 ≠ x.2 := fun e => hne (Prod.ext h e)
      exact mul_ne_zero (mul_ne_zero (by decide) hd.ne') (sub_ne_zero.mpr ht)
    · exact Or.inl (mul_ne_zero (by decide) (sub_ne_zero.mpr h))
  have hc := self_bound S D (fun p x => q (x-p)) K hm hb
  have hD : D.card ≤ V.card+1 := card_insert_le _ _
  exact hc.trans (by rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ hD)

private theorem extract_blocks (S : Finset (ℤ × ℤ)) (k : ℕ) (hk : 0 < k) :
    ∃ F : Finset (Finset (ℤ × ℤ)), (F : Set (Finset (ℤ × ℤ))).PairwiseDisjoint id ∧
      (∀ T ∈ F, T.card = k ∧ ∃ a b c : ℤ, (a ≠ 0 ∨ b ≠ 0) ∧ ∀ p ∈ T, a*p.1+b*p.2=c) ∧
      F.biUnion id ⊆ S ∧ ∀ a b c : ℤ, (a ≠ 0 ∨ b ≠ 0) →
        ((S \ F.biUnion id).filter fun p => a*p.1+b*p.2=c).card < k := by
  classical
  let blocks := S.powerset.filter fun T => T.card = k ∧
    ∃ a b c : ℤ, (a ≠ 0 ∨ b ≠ 0) ∧ ∀ p ∈ T, a*p.1+b*p.2=c
  let families := blocks.powerset.filter fun F : Finset (Finset (ℤ × ℤ)) => (F : Set (Finset (ℤ × ℤ))).PairwiseDisjoint id
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

private theorem value_mono {S T : Finset (ℤ × ℤ)} (h : S ⊆ T) (q : ℤ × ℤ → ℤ) :
    (S.offDiag.image fun xy => q (xy.1-xy.2)).card ≤
      (T.offDiag.image fun xy => q (xy.1-xy.2)).card := by
  apply card_le_card
  intro n hn
  obtain ⟨⟨x,y⟩,hxy,rfl⟩ := mem_image.mp hn
  obtain ⟨hx,hy,hne⟩ := mem_offDiag.mp hxy
  exact mem_image.mpr ⟨(x,y),mem_offDiag.mpr ⟨h hx,h hy,hne⟩,rfl⟩

/-- A pin at an endpoint of a lattice line distinguishes all its other points. -/
private theorem line_value_bound (d : ℤ) (hd : 0 < d) (S T : Finset (ℤ × ℤ))
    (hsub : T ⊆ S) (a b c : ℤ) (hab : a ≠ 0 ∨ b ≠ 0)
    (hl : ∀ p ∈ T, a*p.1+b*p.2=c) :
    let q := fun z : ℤ × ℤ => z.1^2+d*z.2^2
    T.card ≤ (S.offDiag.image fun xy => q (xy.1-xy.2)).card + 1 := by
  classical
  intro q
  obtain h | h := T.eq_empty_or_nonempty
  · simp [h]
  let t := fun p : ℤ × ℤ => b*p.1-a*p.2
  obtain ⟨o,ho,hmin⟩ := T.exists_min_image t h
  let L := a^2+b^2
  let W := b^2+d*a^2
  have hL : 0 < L := by dsimp [L]; rcases hab with ha|hb <;> positivity
  have hW : 0 < W := by dsimp [W]; rcases hab with ha|hb <;> positivity
  have hx (p) (hp : p ∈ T) : L*(p.1-o.1)=b*(t p-t o) := by
    dsimp [L,t]; linear_combination a*(hl p hp - hl o ho)
  have hy (p) (hp : p ∈ T) : L*(p.2-o.2)= -a*(t p-t o) := by
    dsimp [L,t]; linear_combination b*(hl p hp - hl o ho)
  have norm (p) (hp : p ∈ T) : L^2*q (p-o) = W*(t p-t o)^2 := by
    change L^2*((p.1-o.1)^2+d*(p.2-o.2)^2) = _
    calc
      _ = (L*(p.1-o.1))^2+d*(L*(p.2-o.2))^2 := by ring
      _ = _ := by rw [hx p hp,hy p hp]; dsimp [W]; ring
  have hinj : Set.InjOn (fun p => q (p-o)) (T : Set (ℤ × ℤ)) := by
    intro p hp r hr he
    change q (p-o) = q (r-o) at he
    have hs := (norm p hp).symm.trans ((congrArg (L^2 * ·) he).trans (norm r hr))
    have hs' := mul_left_cancel₀ hW.ne' hs
    have ht : t p-t o = t r-t o := by
      have h1 := hmin p hp
      have h2 := hmin r hr
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs' with hh|hh <;> omega
    have ex := (hx p hp).trans ((congrArg (b * ·) ht).trans (hx r hr).symm)
    have ey := (hy p hp).trans ((congrArg (-a * ·) ht).trans (hy r hr).symm)
    exact Prod.ext (by have := mul_left_cancel₀ hL.ne' ex; omega)
      (by have := mul_left_cancel₀ hL.ne' ey; omega)
  have hmap : (T.erase o).image (fun p => q (p-o)) ⊆
      S.offDiag.image (fun xy => q (xy.1-xy.2)) := by
    intro v hv
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hv
    obtain ⟨hne,hp'⟩ := mem_erase.mp hp
    exact mem_image.mpr ⟨(p,o),mem_offDiag.mpr ⟨hsub hp',hsub ho,hne⟩,rfl⟩
  have hh := card_le_card hmap
  rw [card_image_of_injOn (hinj.mono (by exact_mod_cast erase_subset o T))] at hh
  have := card_erase_add_one ho
  omega

private lemma separated {u v h k d H : ℤ} (hd : 0 < d) (hH : 0 < H)
    (K : ℕ) (hK : 0 < K) (hu : u^2 ≤ d*H*K) (hh : H ≤ 2*h) (hk : (K:ℤ) ≤ k-h) :
    u^2+d*h^2 < v^2+d*k^2 := by
  have hKz : (0:ℤ) < K := by exact_mod_cast hK
  have hg : (K:ℤ)*(H+1) ≤ (k-h)*(k+h) := by
    have h₁ := hk
    have h₂ : H+1 ≤ k+h := by omega
    have := mul_le_mul_of_nonneg_right h₁ (by omega : 0 ≤ k+h)
    exact (mul_le_mul_of_nonneg_left h₂ hKz.le).trans this
  have : (0:ℤ) < d*K := mul_pos hd hKz
  have := mul_le_mul_of_nonneg_left hg hd.le
  nlinarith [sq_nonneg v]

/-- Points on one side of the pin, at least half the specified height away. -/
private theorem far_pin_bound (d H : ℤ) (K : ℕ) (hK : 0 < K) (hd : 0 < d) (hH : 0 < H)
    (S T : Finset (ℤ × ℤ)) (p : ℤ × ℤ) (hp : p ∈ S) (hsub : T ⊆ S)
    (hx : ∀ z ∈ T, (z.1-p.1)^2 ≤ d*H*K)
    (hfar : (∀ z ∈ T, H ≤ 2*(z.2-p.2)) ∨ (∀ z ∈ T, H ≤ 2*(p.2-z.2))) :
    T.card ≤ (2*K)*(S.offDiag.image fun xy => (fun z : ℤ × ℤ => z.1^2+d*z.2^2) (xy.1-xy.2)).card := by
  classical
  have hKz : (0:ℤ) < K := by exact_mod_cast hK
  let tag (z : ℤ × ℤ) : Fin K := ⟨(z.2-p.2).natAbs % K, Nat.mod_lt _ hK⟩
  let F (z : ℤ × ℤ) := ((fun z : ℤ × ℤ => z.1^2+d*z.2^2) (z-p), decide (p.1 ≤ z.1), tag z)
  have hgap (z) (hz : z ∈ T) : H ≤ 2*|z.2-p.2| := by
    rcases hfar with hf|hf <;> specialize hf z hz <;> cases abs_cases (z.2-p.2) <;> omega
  have hcard : T.card ≤ ((S.offDiag.image fun xy => (fun z : ℤ × ℤ => z.1^2+d*z.2^2) (xy.1-xy.2)) ×ˢ (univ : Finset (Bool × Fin K))).card := by
    apply card_le_card_of_injOn F
    · intro z hz
      apply mem_product.mpr
      have hne : z ≠ p := by
        intro hzEq
        have hg := hgap z hz
        rw [hzEq] at hg
        simp at hg
        omega
      exact ⟨mem_image.mpr ⟨(z,p),mem_offDiag.mpr ⟨hsub hz,hp,hne⟩,rfl⟩, mem_univ _⟩
    · intro z hz w hw he
      have eqv := congrArg Prod.fst he
      change (z.1-p.1)^2+d*(z.2-p.2)^2 = (w.1-p.1)^2+d*(w.2-p.2)^2 at eqv
      have e : (z.1-p.1)^2+d*|z.2-p.2|^2 = (w.1-p.1)^2+d*|w.2-p.2|^2 := by simpa using eqv
      have htag := congrArg (fun v : ℤ × Bool × Fin K => (v.2.2 : ℕ)) he
      change (z.2-p.2).natAbs % K = (w.2-p.2).natAbs % K at htag
      have hmod : |z.2-p.2| % (K:ℤ) = |w.2-p.2| % (K:ℤ) := by
        simpa only [Int.natCast_mod, Int.natCast_natAbs] using congrArg (fun n : ℕ => (n:ℤ)) htag
      have gap {j k : ℤ} (hlt : j < k) (heq : j % K = k % K) : (K:ℤ) ≤ k-j := by
        apply Int.le_of_dvd (by omega)
        exact Int.dvd_of_emod_eq_zero (by rw [Int.sub_emod, heq]; simp)
      have heights : |z.2-p.2| = |w.2-p.2| := by
        rcases lt_trichotomy |z.2-p.2| |w.2-p.2| with h|h|h
        · exact False.elim ((separated hd hH K hK (hx z hz) (hgap z hz) (gap h hmod)).ne e)
        · exact h
        · exact False.elim ((separated hd hH K hK (hx w hw) (hgap w hw) (gap h hmod.symm)).ne e.symm)
      have hs := congrArg (fun v : ℤ × Bool × Fin K => v.2.1) he
      change decide (p.1 ≤ z.1) = decide (p.1 ≤ w.1) at hs
      have hs' : (p.1 ≤ z.1) ↔ (p.1 ≤ w.1) := by simpa using hs
      rw [heights] at e
      have hsquares := sq_eq_sq_iff_eq_or_eq_neg.mp (add_right_cancel e)
      apply Prod.ext
      · rcases hsquares with h|h <;> omega
      · rcases hfar with hf|hf <;> have hz' := hf z hz <;> have hw' := hf w hw <;>
          cases abs_cases (z.2-p.2) <;> cases abs_cases (w.2-p.2) <;> omega
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hcard

/-- Two pins in rows separated by H give a cardinal bound whenever the squared
horizontal span is at most K times dH. -/
private theorem two_extreme_rows_bound (K : ℕ) (hK : 0 < K) (d : ℤ) (hd : 0 < d) (S : Finset (ℤ × ℤ))
    (p t : ℤ × ℤ) (hp : p ∈ S) (ht : t ∈ S) (hh : p.2 < t.2)
    (hwidth : ∀ z ∈ S, ∀ u ∈ S, (z.1-u.1)^2 ≤ d*(t.2-p.2)*K) :
    S.card ≤ 4*K*(S.offDiag.image fun xy => (fun z : ℤ × ℤ => z.1^2+d*z.2^2) (xy.1-xy.2)).card := by
  let H := t.2-p.2
  let P := S.filter fun z => H ≤ 2*(z.2-p.2)
  let T := S.filter fun z => ¬ H ≤ 2*(z.2-p.2)
  have hP := far_pin_bound d H K hK hd (by dsimp [H]; omega) S P p hp (filter_subset ..)
    (fun z hz => hwidth z (mem_filter.mp hz).1 p hp)
    (Or.inl fun z hz => (mem_filter.mp hz).2)
  have hT := far_pin_bound d H K hK hd (by dsimp [H]; omega) S T t ht (filter_subset ..)
    (fun z hz => hwidth z (mem_filter.mp hz).1 t ht)
    (Or.inr fun z hz => by have hz' := (mem_filter.mp hz).2; dsimp [H] at *; omega)
  have hc : P.card + T.card = S.card := card_filter_add_card_filter_not ..
  calc
    _ = P.card + T.card := hc.symm
    _ ≤ _ := add_le_add hP hT
    _ = _ := by ring

/-- Multiplication by a nonzero integral element scales all values of the diagonal
form by its positive norm, preserving both cardinalities. -/
private theorem tilted_values (d a b : ℤ) (hd : 0 < d) (hab : a ≠ 0 ∨ b ≠ 0)
    (o : ℤ × ℤ) (S : Finset (ℤ × ℤ)) :
    let f := fun p : ℤ × ℤ => (a*p.1-d*b*p.2+o.1, b*p.1+a*p.2+o.2)
    let q := fun z : ℤ × ℤ => z.1^2+d*z.2^2
    let V := fun T : Finset (ℤ × ℤ) => T.offDiag.image fun xy => q (xy.1-xy.2)
    (S.image f).card = S.card ∧ (V (S.image f)).card = (V S).card := by
  classical
  intro f q V
  let m := a^2+d*b^2
  have hm : 0 < m := by dsimp [m]; rcases hab with ha|hb <;> positivity
  have scale (p r : ℤ × ℤ) : q (f p-f r) = m*q (p-r) := by
    dsimp [q,f,m]; ring
  have inj : Function.Injective f := by
    intro p r h
    have hx := congrArg Prod.fst h
    have hy := congrArg Prod.snd h
    dsimp [f] at hx hy
    have e₁ : m*(p.1-r.1)=0 := by dsimp [m]; linear_combination a*hx+d*b*hy
    have e₂ : m*(p.2-r.2)=0 := by dsimp [m]; linear_combination a*hy-b*hx
    exact Prod.ext (sub_eq_zero.mp ((mul_eq_zero.mp e₁).resolve_left hm.ne'))
      (sub_eq_zero.mp ((mul_eq_zero.mp e₂).resolve_left hm.ne'))
  refine ⟨card_image_of_injective _ inj,?_⟩
  have hv : V (S.image f) = (V S).image (m * ·) := by
    ext v
    constructor
    · intro h
      obtain ⟨⟨p,r⟩,hpr,rfl⟩ := mem_image.mp h
      obtain ⟨hp,hr,hne⟩ := mem_offDiag.mp hpr
      obtain ⟨p,hp0,rfl⟩ := mem_image.mp hp
      obtain ⟨r,hr0,rfl⟩ := mem_image.mp hr
      exact mem_image.mpr ⟨q (p-r),mem_image.mpr ⟨(p,r),
        mem_offDiag.mpr ⟨hp0,hr0,fun he => hne (congrArg f he)⟩,rfl⟩,(scale p r).symm⟩
    · intro h
      obtain ⟨v,hv,rfl⟩ := mem_image.mp h
      obtain ⟨⟨p,r⟩,hpr,rfl⟩ := mem_image.mp hv
      obtain ⟨hp,hr,hne⟩ := mem_offDiag.mp hpr
      exact mem_image.mpr ⟨(f p,f r),mem_offDiag.mpr ⟨mem_image_of_mem _ hp,
        mem_image_of_mem _ hr,inj.ne hne⟩,scale p r⟩
  rw [hv,card_image_of_injective _ (mul_right_injective₀ hm.ne')]

/-- Transfer a value bound on a positive fraction of the points to the block count. -/
private theorem packing_of_dense_subset (F : Finset (Finset (ℤ × ℤ))) (k : ℕ) (hk : 0 < k)
    (hdis : (F : Set (Finset (ℤ × ℤ))).PairwiseDisjoint id)
    (hcard : ∀ T ∈ F, T.card = k) (A : Finset (ℤ × ℤ)) (q : ℤ × ℤ → ℤ)
    (L C : ℕ) (hsub : A ⊆ F.biUnion id) (hdense : (F.biUnion id).card ≤ L*A.card)
    (hbound : A.card ≤ C*k*(A.offDiag.image fun xy => q (xy.1-xy.2)).card) :
    F.card ≤ (L*C)*((F.biUnion id).offDiag.image fun xy => q (xy.1-xy.2)).card := by
  classical
  let D := fun T : Finset (ℤ × ℤ) => (T.offDiag.image fun xy => q (xy.1-xy.2)).card
  have hsize : (F.biUnion id).card = F.card*k := by
    rw [card_biUnion hdis]
    calc
      _ = ∑ _T ∈ F, k := sum_congr rfl fun T hT => (hcard T hT)
      _ = _ := by simp
  apply Nat.le_of_mul_le_mul_right _ hk
  calc
    F.card*k = (F.biUnion id).card := hsize.symm
    _ ≤ L*A.card := hdense
    _ ≤ L*(C*k*D A) := Nat.mul_le_mul_left _ hbound
    _ ≤ L*(C*k*D (F.biUnion id)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (value_mono hsub q))
    _ = _ := by dsimp [D]; ring

/-- Two rows certify the packing bound for a union of disjoint equal-size blocks from a normalized subset carrying a fraction of the points. -/
private theorem narrow_packing (d a b : ℤ) (hd : 0 < d) (hab : a ≠ 0 ∨ b ≠ 0) (k : ℕ) (hk : 0 < k)
    (F : Finset (Finset (ℤ × ℤ))) (hdis : (F : Set (Finset (ℤ × ℤ))).PairwiseDisjoint id)
    (hcard : ∀ T ∈ F, T.card = k) :
    let S := F.biUnion id
    ∀ (L : ℕ) (A : Finset (ℤ × ℤ)), A ⊆ S → S.card ≤ L*A.card →
    let R := A.image (fun p : ℤ × ℤ => (a*p.1-(d:ℤ)*b*p.2, b*p.1+a*p.2))
    ∀ (g : ℤ) (o : ℤ × ℤ) (B : Finset (ℤ × ℤ)), 0 < g →
      B.image (fun z : ℤ × ℤ => (g*z.1+o.1,g*z.2+o.2)) = R →
      ∀ p ∈ B, ∀ t ∈ B, p.2 < t.2 →
      (∀ z ∈ B, ∀ u ∈ B, (z.1-u.1)^2 ≤ d*(t.2-p.2)*k) →
      F.card ≤ (L*4)*(S.offDiag.image fun xy => (fun z : ℤ × ℤ => z.1^2+d*z.2^2) (xy.1-xy.2)).card := by
  classical
  intro S L A hsub hdense R g o B hg hmodel p hp t ht hpt hw
  let V := fun T : Finset (ℤ × ℤ) => (T.offDiag.image fun xy =>
    ((xy.1-xy.2).1)^2+d*((xy.1-xy.2).2)^2).card
  have hTilt : R.card = A.card ∧ V R = V A := by
    simpa [R,V] using tilted_values d a b hd hab (0,0) A
  have hScale : R.card = B.card ∧ V R = V B := by
    rw [← hmodel]
    simpa [V] using tilted_values d g 0 hd (Or.inl hg.ne') o B
  have h := two_extreme_rows_bound k hk d hd B p t hp ht hpt hw
  change B.card ≤ 4*k*V B at h
  rw [← hScale.1, hTilt.1, ← hScale.2, hTilt.2] at h
  exact packing_of_dense_subset F k hk hdis hcard A (fun z => z.1^2+d*z.2^2)
    L 4 hsub hdense h

/-- The wide-union estimate implies the previous spread-only hypothesis. -/
private theorem packing_from_width (packing : H1) :
  ∃ C : ℕ, ∀ (d k : ℕ) (F : Finset (Finset (ℤ × ℤ))), 0 < d → Squarefree d → 0 < k →
    (F : Set (Finset (ℤ × ℤ))).PairwiseDisjoint id →
    (∀ T ∈ F, T.card = k ∧ ∃ a b c : ℤ, (a ≠ 0 ∨ b ≠ 0) ∧ ∀ p ∈ T, a*p.1+b*p.2=c) →
    ((F.biUnion id).card : ℝ) ≤ Real.exp ((k : ℝ)^2) →
    (∀ G : Finset (Finset (ℤ × ℤ)), G.card ≤ k →
      (∀ T ∈ G, T ⊆ F.biUnion id ∧ ∃ a b c : ℤ, (a ≠ 0 ∨ b ≠ 0) ∧ ∀ p ∈ T, a*p.1+b*p.2=c) →
      2*(G.biUnion id).card < (F.biUnion id).card) →
    let q := fun z : ℤ × ℤ => z.1^2+(d:ℤ)*z.2^2
    F.card ≤ C * (((F.biUnion id).offDiag.image fun xy => q (xy.1-xy.2)).card+1) := by
  classical
  obtain ⟨C,pack⟩ := packing
  refine ⟨max C 8,?_⟩
  intro d k F hd hsq hk hdis hline hsize hspread q
  let S := F.biUnion id
  let D := (S.offDiag.image fun xy => q (xy.1-xy.2)).card
  change F.card ≤ max C 8 * (D+1)
  by_cases hw : (∀ A : Finset (ℤ × ℤ), A ⊆ S → S.card ≤ 2*A.card → ∀ a b : ℤ, (a ≠ 0 ∨ b ≠ 0) →
      let R := A.image (fun p : ℤ × ℤ => (a*p.1-(d:ℤ)*b*p.2, b*p.1+a*p.2))
      ∀ (g : ℤ) (o : ℤ × ℤ) (B : Finset (ℤ × ℤ)), 0 < g →
        B.image (fun z : ℤ × ℤ => (g*z.1+o.1,g*z.2+o.2)) = R →
        ∀ p ∈ B, ∀ t ∈ B, p.2 < t.2 →
        ∃ z ∈ B, ∃ u ∈ B, (d:ℤ)*(t.2-p.2)*k < (z.1-u.1)^2)
  · exact (pack d k F hd hsq hk hdis hline hsize hspread hw).trans
      (Nat.mul_le_mul_right _ (le_max_left C 8))
  push Not at hw
  obtain ⟨A,hsub,hdense,a,b,hab,hbad⟩ := hw
  dsimp only at hbad
  push Not at hbad
  obtain ⟨g,o,B,hg,hmodel,p,hp,t,ht,hpt,hwidth⟩ := hbad
  have h : F.card ≤ 8*D := narrow_packing d a b (by exact_mod_cast hd) hab k hk F hdis
    (fun T hT => (hline T hT).1) 2 A hsub hdense g o B hg hmodel p hp t ht hpt hwidth
  exact h.trans (Nat.mul_le_mul (le_max_right C 8) (Nat.le_succ D))

private theorem packing_from_spread (packing : H1) :
  ∃ C : ℕ, ∀ (d k : ℕ) (F : Finset (Finset (ℤ × ℤ))), 0 < d → Squarefree d → 0 < k →
    (F : Set (Finset (ℤ × ℤ))).PairwiseDisjoint id →
    (∀ T ∈ F, T.card = k ∧ ∃ a b c : ℤ, (a ≠ 0 ∨ b ≠ 0) ∧ ∀ p ∈ T, a*p.1+b*p.2=c) →
    ((F.biUnion id).card : ℝ) ≤ Real.exp ((k : ℝ)^2) →
    let q := fun z : ℤ × ℤ => z.1^2+(d:ℤ)*z.2^2
    F.card ≤ C * (((F.biUnion id).offDiag.image fun xy => q (xy.1-xy.2)).card+1) := by
  classical
  obtain ⟨C,pack⟩ := packing_from_width packing
  refine ⟨max C 2,?_⟩
  intro d k F hd hsq hk hdis hline hsize q
  let S := F.biUnion id
  let D := (S.offDiag.image fun xy => q (xy.1-xy.2)).card
  change F.card ≤ max C 2 * (D+1)
  by_cases spread : ∀ G : Finset (Finset (ℤ × ℤ)), G.card ≤ k →
      (∀ T ∈ G, T ⊆ S ∧ ∃ a b c : ℤ, (a ≠ 0 ∨ b ≠ 0) ∧ ∀ p ∈ T, a*p.1+b*p.2=c) →
      2*(G.biUnion id).card < S.card
  · exact (pack d k F hd hsq hk hdis hline hsize spread).trans
      (Nat.mul_le_mul_right _ (le_max_left C 2))
  push Not at spread
  obtain ⟨G,hkG,hG,hhalf⟩ := spread
  have hcov : (G.biUnion id).card ≤ k*(D+1) := calc
    _ ≤ ∑ T ∈ G, T.card := card_biUnion_le
    _ ≤ ∑ _T ∈ G, (D+1) := by
      apply sum_le_sum
      intro T hT
      obtain ⟨hsub,a,b,c,hab,hl⟩ := hG T hT
      exact line_value_bound d (by exact_mod_cast hd) S T hsub a b c hab hl
    _ ≤ _ := by simpa using Nat.mul_le_mul_right (D+1) hkG
  have hcard : S.card = F.card*k := by
    dsimp [S]; rw [card_biUnion hdis]
    calc
      _ = ∑ _T ∈ F, k := sum_congr rfl fun T hT => (hline T hT).1
      _ = _ := by simp
  have hprod : F.card*k ≤ (2*(D+1))*k := calc
    _ = S.card := hcard.symm
    _ ≤ 2*(G.biUnion id).card := hhalf
    _ ≤ 2*(k*(D+1)) := Nat.mul_le_mul_left 2 hcov
    _ = _ := by ring
  exact (Nat.le_of_mul_le_mul_right hprod hk).trans (Nat.mul_le_mul_right _ (le_max_right C 2))

private theorem diagonal_bound (packing : H1) :
    ∃ C : ℕ, ∀ (d : ℕ) (S : Finset (ℤ × ℤ)) (k : ℕ), 0 < d → Squarefree d →
      0 < k → (S.card : ℝ) ≤ Real.exp ((k : ℝ)^2) →
      let q := fun z : ℤ × ℤ => z.1^2+(d:ℤ)*z.2^2
      S.card ≤ k*(C+1)*((S.offDiag.image fun xy => q (xy.1-xy.2)).card+1) := by
  classical
  obtain ⟨C,pack⟩ := packing_from_spread packing
  refine ⟨C,?_⟩
  intro d S k hd hsq hk hsize q
  let D := fun T : Finset (ℤ × ℤ) => (T.offDiag.image fun xy => q (xy.1-xy.2)).card
  obtain ⟨F,hdis,hline,hsub,hres⟩ := extract_blocks S k hk
  let U := F.biUnion id
  have hu : U.card = F.card*k := by
    rw [show U=F.biUnion id from rfl,card_biUnion hdis]
    calc
      _ = ∑ _T ∈ F, k := sum_congr rfl fun T hT => (hline T hT).1
      _ = _ := by simp
  have hpack : F.card ≤ C*(D U+1) := pack d k F hd hsq hk hdis hline
    ((by exact_mod_cast card_le_card hsub : (U.card:ℝ) ≤ S.card).trans hsize)
  have hp := hpack.trans (Nat.mul_le_mul_left C (Nat.add_le_add_right (value_mono hsub q) 1))
  have hr : (S \ U).card ≤ (k-1+1)*(D (S \ U)+1) :=
    sparse_lines_bound d (by exact_mod_cast hd) (S \ U) (k-1) (fun a b c h => by
      dsimp only [U]; have := hres a b c h; omega)
  rw [Nat.sub_add_cancel hk] at hr
  have hleft := hr.trans (Nat.mul_le_mul_left k (Nat.add_le_add_right (value_mono sdiff_subset q) 1))
  change S.card ≤ k*(C+1)*(D S+1)
  calc
    _ = (S \ U).card+U.card := (card_sdiff_add_card_eq_card hsub).symm
    _ ≤ k*(D S+1) + (C*(D S+1))*k := by rw [hu]; exact Nat.add_le_add hleft (Nat.mul_le_mul_right _ hp)
    _ = _ := by ring

/-- Recover the uniform arithmetic estimate on all positive definite integral
forms from the squarefree block-packing hypothesis. -/
theorem arithmetic_bound (packing : H1) :
∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ a b c : ℤ, 0 < a → b^2 < 4*a*c →
    ∀ S : Finset (ℤ × ℤ), N ≤ S.card →
      let q := fun z : ℤ × ℤ => a*z.1^2 + b*z.1*z.2 + c*z.2^2
      (S.card : ℝ) ≤ C * Real.sqrt (Real.log S.card) *
        ((S.offDiag.image fun xy => q (xy.1 - xy.2)).card : ℝ) := by
  classical
  obtain ⟨C,hC⟩ := diagonal_bound packing
  refine ⟨4*((C:ℝ)+1),by positivity,⌈Real.exp 1⌉₊+2,?_⟩
  intro a b c ha hd S hn Q
  let V := fun (q : ℤ × ℤ → ℤ) (T : Finset (ℤ × ℤ)) => T.offDiag.image fun xy => q (xy.1-xy.2)
  obtain ⟨d,hd',hsq,F,_,hF⟩ := squarefree_model a b c ha hd
  obtain ⟨hsize,hvals⟩ := hF S
  let q := fun z : ℤ × ℤ => z.1^2+(d:ℤ)*z.2^2
  change V q (S.image F) = (V Q S).image (4*a * ·) at hvals
  have hcard := congrArg Finset.card hvals
  rw [card_image_of_injective _ (mul_right_injective₀ (by positivity : 4*a ≠ 0))] at hcard
  have hexp : Real.exp 1 ≤ (S.card:ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (by omega : ⌈Real.exp 1⌉₊ ≤ S.card))
  have hlog : 1 ≤ Real.log (S.card:ℝ) := by simpa using Real.log_le_log (Real.exp_pos _) hexp
  let z := Real.sqrt (Real.log S.card)
  have hz : 1 ≤ z := by simpa [z] using Real.sqrt_le_sqrt hlog
  let k := ⌈z⌉₊
  have hceil : z ≤ (k:ℝ) := Nat.le_ceil _
  have hk : 0 < k := by exact_mod_cast (zero_lt_one.trans_le (hz.trans hceil))
  have hround : (k:ℝ) ≤ 2*z := by
    have h := Nat.ceil_lt_add_one (zero_le_one.trans hz)
    dsimp [k]; linarith
  have hcap : (S.card:ℝ) ≤ Real.exp ((k:ℝ)^2) := by
    have hpos : 0 < (S.card:ℝ) := by exact_mod_cast (by omega : 0<S.card)
    rw [← Real.exp_log hpos]
    apply Real.exp_le_exp.mpr
    have he : z^2 = Real.log S.card := Real.sq_sqrt (zero_le_one.trans hlog)
    nlinarith [mul_nonneg (sub_nonneg.mpr hceil) (by positivity : 0 ≤ (k:ℝ)+z)]
  have hn' := hC d (S.image F) k hd' hsq hk (by rwa [hsize])
  change (S.image F).card ≤ k*(C+1)*((V q (S.image F)).card+1) at hn'
  rw [hsize,hcard] at hn'
  have hp : 0 < (V Q S).card := by
    obtain ⟨x,hx,y,hy,hne⟩ := one_lt_card.mp (by omega : 1 < S.card)
    exact card_pos.mpr ⟨_,mem_image.mpr ⟨(x,y),mem_offDiag.mpr ⟨hx,hy,hne⟩,rfl⟩⟩
  let D : ℝ := (V Q S).card
  have hD : 1 ≤ D := by dsimp [D]; exact_mod_cast (show 1 ≤ (V Q S).card from hp)
  change (S.card:ℝ) ≤ 4*((C:ℝ)+1)*z*D
  calc
    _ ≤ (k:ℝ)*((C:ℝ)+1)*(D+1) := by dsimp [D]; exact_mod_cast hn'
    _ ≤ (2*z)*((C:ℝ)+1)*(2*D) := by gcongr; linarith
    _ = _ := by ring

end Arithmetic

theorem main : H1 → H2 → OMA.R_Erdos89_erdos_89_R1.H2 := by
  classical
  rintro packing ⟨K, hK, N₀, hcompare⟩
  obtain ⟨C,hC,N,hcount⟩ := arithmetic_bound packing
  let X := {p : ℝ² // ∀ i : Fin 2, IsIntegral ℤ (p i)}
  let f (j : ℕ) : X := ⟨EuclideanSpace.single 0 (j : ℝ), by
    intro i
    fin_cases i <;> simp <;> first | exact isIntegral_natCast .. | exact isIntegral_zero⟩
  have : Infinite X := Infinite.of_injective f (by
    intro i j hij
    simpa [f] using congrArg (fun p : X => p.val 0) hij)
  apply Asymptotics.IsBigO.of_bound ((K : ℝ) * C)
  filter_upwards [eventually_ge_atTop (max N₀ (K * (N + 2) + 2))] with n hn
  obtain ⟨P₀, h₀⟩ := Infinite.exists_subset_card_eq X n
  obtain ⟨P, hP, hD⟩ := Nat.sInf_mem (show
    {d : ℕ | ∃ P : Finset X, P.card = n ∧ distinctDistances P = d}.Nonempty
    from ⟨_, P₀, h₀, rfl⟩)
  change distinctDistances P = minimalDistinctDistances X n at hD
  obtain ⟨a, b, c, ha, hd, S, hs, hsize, hbudget⟩ :=
    hcompare P (hP ▸ (le_max_left _ _).trans hn)
  rw [hP] at hs hsize
  have hlarge := (le_max_right _ _).trans hn
  have hmin : N + 2 ≤ S.card := by
    exact Nat.le_of_mul_le_mul_left (by omega : K * (N+2) ≤ K * S.card) hK
  have harith := hcount a b c ha hd S (by omega)
  dsimp only at harith hbudget
  have hlog : Real.sqrt (Real.log S.card) ≤ Real.sqrt (Real.log n) :=
    Real.sqrt_le_sqrt (Real.log_le_log (by exact_mod_cast (by omega : 0 < S.card))
      (by exact_mod_cast hs))
  have hn' : 1 < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
  have hpos := Real.sqrt_pos.2 (Real.log_pos hn')
  change ‖(n : ℝ) / Real.sqrt (Real.log n)‖ ≤
    (K : ℝ) * C * ‖(minimalDistinctDistances X n : ℝ)‖
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.norm_eq_abs, Nat.abs_cast,
    div_le_iff₀ hpos]
  calc
    (n : ℝ) ≤ (K : ℝ) * S.card := by exact_mod_cast hsize
    _ ≤ (K : ℝ) * (C * Real.sqrt (Real.log S.card) * _) :=
      mul_le_mul_of_nonneg_left harith (by positivity)
    _ ≤ (K : ℝ) * (C * Real.sqrt (Real.log n) * (distinctDistances P : ℝ)) := by
      gcongr
    _ = _ := by rw [hD]; ring

end OMA.R_Erdos89_erdos_89_R1_H2_R1
