import OMAStatements.S_oeis_a304312
import Mathlib

namespace OMA.S_oeis_a304312

open PowerSeries BigOperators

/-- Reachability in a `k`-input finite automaton `δ` on `Fin n`. -/
private def Reach {k n : ℕ} (δ : Fin n → Fin k → Fin n) : Fin n → Fin n → Prop :=
  Relation.ReflTransGen (fun a b => ∃ i : Fin k, δ a i = b)

/-- A nonempty subset `B ⊆ Fin n` is a sink strongly connected component of `δ` if it is
closed under all transitions and every vertex in `B` can reach every other vertex in `B`. -/
private def IsSinkSCC {k n : ℕ} (δ : Fin n → Fin k → Fin n) (B : Finset (Fin n)) : Prop :=
  B.Nonempty ∧
  (∀ u ∈ B, ∀ i : Fin k, δ u i ∈ B) ∧
  (∀ u ∈ B, ∀ v ∈ B, Reach δ u v)

/-- If `B` is closed under `δ`, then any vertex reachable from `B` stays in `B`. -/
private lemma reach_mem_of_closed {k n : ℕ} {δ : Fin n → Fin k → Fin n} {B : Finset (Fin n)}
    (hB : ∀ x ∈ B, ∀ i : Fin k, δ x i ∈ B) {x y : Fin n} (hx : x ∈ B) (hxy : Reach δ x y) :
    y ∈ B := by
  induction hxy with
  | refl => exact hx
  | tail _ hstep ih =>
      obtain ⟨i, hi⟩ := hstep
      rw [← hi]; exact hB _ ih i

/-- If `δ₁` and `δ₂` agree on a `δ₁`-closed set `B`, then reachability from `B` is preserved. -/
private lemma reach_congr_on_closed {k n : ℕ} {δ₁ δ₂ : Fin n → Fin k → Fin n} {B : Finset (Fin n)}
    (hB : ∀ x ∈ B, ∀ i : Fin k, δ₁ x i ∈ B)
    (heq : ∀ x ∈ B, ∀ i : Fin k, δ₁ x i = δ₂ x i)
    {x y : Fin n} (hx : x ∈ B) (hxy : Reach δ₁ x y) : Reach δ₂ x y := by
  induction hxy with
  | refl => exact Relation.ReflTransGen.refl
  | tail h1 hstep ih =>
      have hmid : _ ∈ B := reach_mem_of_closed hB hx h1
      obtain ⟨i, hi⟩ := hstep
      exact Relation.ReflTransGen.tail ih ⟨i, (heq _ hmid i).symm.trans hi⟩

/-- `IsSinkSCC` depends only on the restriction of `δ` to `B`. -/
private lemma isSinkSCC_congr {k n : ℕ} {δ₁ δ₂ : Fin n → Fin k → Fin n} {B : Finset (Fin n)}
    (heq : ∀ x ∈ B, ∀ i : Fin k, δ₁ x i = δ₂ x i) :
    IsSinkSCC δ₁ B ↔ IsSinkSCC δ₂ B := by
  constructor
  · intro ⟨hne, hcl, hsc⟩
    refine ⟨hne, fun u hu i => by rw [← heq u hu i]; exact hcl u hu i,
      fun u hu v hv => reach_congr_on_closed hcl heq hu (hsc u hu v hv)⟩
  · intro ⟨hne, hcl, hsc⟩
    refine ⟨hne, fun u hu i => by rw [heq u hu i]; exact hcl u hu i,
      fun u hu v hv => reach_congr_on_closed hcl (fun x hx i => (heq x hx i).symm) hu (hsc u hu v hv)⟩

/-- Any two sink SCCs of `δ` that share a vertex are equal. -/
private lemma isSinkSCC_eq_of_inter {k n : ℕ} {δ : Fin n → Fin k → Fin n}
    {B₁ B₂ : Finset (Fin n)} (h₁ : IsSinkSCC δ B₁) (h₂ : IsSinkSCC δ B₂)
    {u : Fin n} (hu₁ : u ∈ B₁) (hu₂ : u ∈ B₂) : B₁ = B₂ := by
  ext v
  constructor
  · intro hv; exact reach_mem_of_closed h₂.2.1 hu₂ (h₁.2.2 u hu₁ v hv)
  · intro hv; exact reach_mem_of_closed h₁.2.1 hu₁ (h₂.2.2 u hu₂ v hv)

/-- Every `k`-input automaton on `Fin n` (`n ≥ 1`) has at least one sink SCC. -/
private lemma exists_isSinkSCC {k n : ℕ} (hn : 1 ≤ n) (δ : Fin n → Fin k → Fin n) :
    ∃ B : Finset (Fin n), IsSinkSCC δ B := by
  classical
  let R : Fin n → Finset (Fin n) := fun u => Finset.univ.filter (fun v => Reach δ u v)
  have hne : (Finset.univ : Finset (Fin n)).Nonempty :=
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  obtain ⟨u₀, _, hu₀⟩ := Finset.exists_min_image Finset.univ (fun u => (R u).card) hne
  refine ⟨R u₀, ?_, ?_, ?_⟩
  · exact ⟨u₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Relation.ReflTransGen.refl⟩⟩
  · intro x hx i
    have hrx : Reach δ u₀ x := (Finset.mem_filter.mp hx).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Relation.ReflTransGen.tail hrx ⟨i, rfl⟩⟩
  · intro x hx y hy
    have hrx : Reach δ u₀ x := (Finset.mem_filter.mp hx).2
    have hsub : R x ⊆ R u₀ := by
      intro z hz
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrx.trans (Finset.mem_filter.mp hz).2⟩
    have heq : R x = R u₀ :=
      Finset.eq_of_subset_of_card_le hsub (hu₀ x (Finset.mem_univ x))
    rw [← heq] at hy
    exact (Finset.mem_filter.mp hy).2

/-- The finite set of all sink SCCs of `δ`. -/
private noncomputable def sinkSCCs {k n : ℕ} (δ : Fin n → Fin k → Fin n) : Finset (Finset (Fin n)) :=
  by classical exact Finset.univ.filter (IsSinkSCC δ)

/-- A good SCC-partitioned automaton on a subset `U ⊆ Fin n`: a partition `P` of `U` into
nonempty pairwise-disjoint blocks together with a transition map `f` (canonical outside `U`)
making every block `B ∈ P` a sink SCC of `f`. -/
private def IsGoodStruct {k n : ℕ} (U : Finset (Fin n))
    (x : Finset (Finset (Fin n)) × (Fin n → Fin k → Fin n)) : Prop :=
  (∀ B ∈ x.1, B.Nonempty) ∧
  (x.1 : Set (Finset (Fin n))).PairwiseDisjoint id ∧
  x.1.biUnion id = U ∧
  (∀ u, u ∉ U → ∀ i : Fin k, x.2 u i = u) ∧
  (∀ B ∈ x.1, IsSinkSCC x.2 B)

/-- Signed count `W U = ∑_{(P, f) ∈ GoodStruct U} (-1)^|P|`. -/
private noncomputable def W {k n : ℕ} (U : Finset (Fin n)) : ℤ := by
  classical
  exact ∑ x ∈ (Finset.univ.filter (IsGoodStruct (k := k) U)), (-1 : ℤ) ^ x.1.card

/-- `w k m = W (univ : Finset (Fin m))`. -/
private noncomputable def w (k m : ℕ) : ℤ :=
  W (k := k) (Finset.univ : Finset (Fin m))

/-- Number of transition maps `f : Fin n → Fin k → Fin n` that are canonical outside `B` and make
`B` a sink SCC equals `numLabeledSC k B.card`. -/
private lemma card_sinkSCC_on_subset {k n : ℕ} (B : Finset (Fin n)) (hB : B.Nonempty) :
    by classical
    exact (Finset.univ.filter (fun f : Fin n → Fin k → Fin n =>
      (∀ u, u ∉ B → ∀ i : Fin k, f u i = u) ∧ IsSinkSCC f B)).card = numLabeledSC k B.card := by
  classical
  let e : Fin B.card ≃ B := (Fintype.equivFinOfCardEq (Fintype.card_coe B)).symm
  rw [← Fintype.card_subtype, numLabeledSC]
  refine Fintype.card_congr
    { toFun := fun ⟨f, _, hsc⟩ =>
        ⟨fun a i => e.symm ⟨f (e a).1 i, hsc.2.1 (e a).1 (e a).2 i⟩, fun u v => ?_⟩
      invFun := fun ⟨δ, hδ⟩ =>
        ⟨fun x i => if hx : x ∈ B then (e (δ (e.symm ⟨x, hx⟩) i)).1 else x,
          fun u hu i => by simp [hu],
          ⟨hB, fun u hu i => by simp [hu], fun u hu v hv => ?_⟩⟩
      left_inv := ?_
      right_inv := ?_ }
  · have hreach : Reach f (e u).1 (e v).1 := hsc.2.2 (e u).1 (e u).2 (e v).1 (e v).2
    have hgen : ∀ a b : Fin n, Reach f a b → ∀ (ha : a ∈ B) (hb : b ∈ B),
        Reach (fun x i => e.symm ⟨f (e x).1 i, hsc.2.1 (e x).1 (e x).2 i⟩)
          (e.symm ⟨a, ha⟩) (e.symm ⟨b, hb⟩) := by
      intro a b hab
      induction hab with
      | refl => intro ha hb; exact Relation.ReflTransGen.refl
      | tail h1 hstep ih =>
          intro ha hb
          have hmid : _ ∈ B := reach_mem_of_closed hsc.2.1 ha h1
          obtain ⟨i, hi⟩ := hstep
          refine Relation.ReflTransGen.tail (ih ha hmid) ⟨i, ?_⟩
          apply e.injective; apply Subtype.ext; simp [hi]
    simpa [Reach] using hgen (e u).1 (e v).1 hreach (e u).2 (e v).2
  · have hreach : Reach δ (e.symm ⟨u, hu⟩) (e.symm ⟨v, hv⟩) := hδ _ _
    have hgen : ∀ a b : Fin B.card, Reach δ a b →
        Reach (fun x i => if hx : x ∈ B then (e (δ (e.symm ⟨x, hx⟩) i)).1 else x) (e a).1 (e b).1 := by
      intro a b hab
      induction hab with
      | refl => exact Relation.ReflTransGen.refl
      | tail _ hstep ih =>
          obtain ⟨i, hi⟩ := hstep
          exact Relation.ReflTransGen.tail ih ⟨i, by simp [hi]⟩
    simpa using hgen (e.symm ⟨u, hu⟩) (e.symm ⟨v, hv⟩) hreach
  · intro ⟨f, hcan, hsc⟩
    apply Subtype.ext; funext x i
    by_cases hx : x ∈ B <;> simp [hx, hcan]
  · intro ⟨δ, hδ⟩
    apply Subtype.ext; funext a i; simp

/-- Transporting a `GoodStruct` from `U ⊆ Fin n` to `Fin U.card` along `e : Fin U.card ≃ U`. -/
private lemma W_eq_w_card {k n : ℕ} (U : Finset (Fin n)) : W (k := k) U = w k U.card := by
  classical
  let e : Fin U.card ≃ U := (Fintype.equivFinOfCardEq (Fintype.card_coe U)).symm
  let toP : Finset (Finset (Fin n)) → Finset (Finset (Fin U.card)) :=
    fun P => P.image (fun B => Finset.univ.filter (fun a : Fin U.card => (e a).1 ∈ B))
  let toF : (Fin n → Fin k → Fin n) → (Fin U.card → Fin k → Fin U.card) :=
    fun f a i => if h : f (e a).1 i ∈ U then e.symm ⟨f (e a).1 i, h⟩ else a
  let ofP : Finset (Finset (Fin U.card)) → Finset (Finset (Fin n)) :=
    fun Q => Q.image (fun C => C.image (fun a => (e a).1))
  let ofF : (Fin U.card → Fin k → Fin U.card) → (Fin n → Fin k → Fin n) :=
    fun g u i => if h : u ∈ U then (e (g (e.symm ⟨u, h⟩) i)).1 else u
  have hsub_biUnion : ∀ {P : Finset (Finset (Fin n))}, P.biUnion id = U → ∀ B ∈ P, B ⊆ U := by
    intro P hP B hB u hu; rw [← hP]; exact Finset.mem_biUnion.mpr ⟨B, hB, hu⟩
  have hB_round : ∀ B : Finset (Fin n), B ⊆ U →
      (Finset.univ.filter (fun a : Fin U.card => (e a).1 ∈ B)).image (fun a => (e a).1) = B := by
    intro B hBU; ext u; simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨a, ha, rfl⟩; exact ha
    · intro hu; exact ⟨e.symm ⟨u, hBU hu⟩, by simpa using hu, by simp⟩
  have hC_round : ∀ C : Finset (Fin U.card),
      Finset.univ.filter (fun a : Fin U.card => (e a).1 ∈ C.image (fun b => (e b).1)) = C := by
    intro C; ext a; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨b, hb, hba⟩
      have : b = a := e.injective (Subtype.ext hba)
      rwa [← this]
    · intro ha; exact ⟨a, ha, rfl⟩
  unfold w W
  refine Finset.sum_nbij (fun x => (toP x.1, toF x.2)) ?_ ?_ ?_ ?_
  · -- Maps `GoodStruct U` into `GoodStruct univ`
    intro ⟨P, f⟩ hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    obtain ⟨hne, hdisj, hbiU, hcan, hscc⟩ := hx
    have hfU : ∀ u ∈ U, ∀ i : Fin k, f u i ∈ U := by
      intro u hu i
      rw [← hbiU] at hu
      obtain ⟨B, hBP, huB⟩ := Finset.mem_biUnion.mp hu
      exact hsub_biUnion hbiU B hBP ((hscc B hBP).2.1 u huB i)
    refine ⟨?_, ?_, ?_, fun _ hu => absurd (Finset.mem_univ _) hu, ?_⟩
    · intro C hC
      obtain ⟨B, hBP, rfl⟩ := Finset.mem_image.mp hC
      obtain ⟨u, huB⟩ := hne B hBP
      exact ⟨e.symm ⟨u, hsub_biUnion hbiU B hBP huB⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using huB⟩⟩
    · intro C₁ hC₁ C₂ hC₂ hne12
      obtain ⟨B₁, hB₁, rfl⟩ := Finset.mem_image.mp hC₁
      obtain ⟨B₂, hB₂, rfl⟩ := Finset.mem_image.mp hC₂
      have hBne : B₁ ≠ B₂ := fun h => hne12 (by subst h; rfl)
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro a ha₁ ha₂
      have h1 : (e a).1 ∈ B₁ := (Finset.mem_filter.mp ha₁).2
      have h2 : (e a).1 ∈ B₂ := (Finset.mem_filter.mp ha₂).2
      exact Finset.disjoint_left.mp (hdisj hB₁ hB₂ hBne) h1 h2
    · ext a; simp only [toP, Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ, iff_true, id_eq]
      have haU : (e a).1 ∈ P.biUnion id := hbiU.symm ▸ (e a).2
      obtain ⟨B, hBP, haB⟩ := Finset.mem_biUnion.mp haU
      exact ⟨_, ⟨B, hBP, rfl⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, haB⟩⟩
    · intro C hC
      obtain ⟨B, hBP, rfl⟩ := Finset.mem_image.mp hC
      obtain ⟨hBne, hBcl, hBsc⟩ := hscc B hBP
      refine ⟨?_, ?_, ?_⟩
      · obtain ⟨u, huB⟩ := hBne
        exact ⟨e.symm ⟨u, hsub_biUnion hbiU B hBP huB⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using huB⟩⟩
      · intro a ha i
        have haB : (e a).1 ∈ B := (Finset.mem_filter.mp ha).2
        have hfaB : f (e a).1 i ∈ B := hBcl (e a).1 haB i
        have hfaU : f (e a).1 i ∈ U := hsub_biUnion hbiU B hBP hfaB
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [toF, hfaU, hfaB]⟩
      · intro a ha b hb
        have haB : (e a).1 ∈ B := (Finset.mem_filter.mp ha).2
        have hbB : (e b).1 ∈ B := (Finset.mem_filter.mp hb).2
        have hgen : ∀ x y : Fin n, Reach f x y → ∀ (hx : x ∈ B) (hy : y ∈ B),
            Reach (toF f) (e.symm ⟨x, hsub_biUnion hbiU B hBP hx⟩)
              (e.symm ⟨y, hsub_biUnion hbiU B hBP hy⟩) := by
          intro x y hxy
          induction hxy with
          | refl => intro _ _; exact Relation.ReflTransGen.refl
          | @tail b' c' h1 hstep ih =>
              intro hx hy
              have hmid : b' ∈ B := reach_mem_of_closed hBcl hx h1
              obtain ⟨i, hi⟩ := hstep
              refine Relation.ReflTransGen.tail (ih hx hmid) ⟨i, ?_⟩
              have hUmid : c' ∈ U := hsub_biUnion hbiU B hBP hy
              simp [toF, hi, hUmid]
        simpa using hgen (e a).1 (e b).1 (hBsc _ haB _ hbB) haB hbB
  · -- Injectivity on `GoodStruct U`
    intro ⟨P₁, f₁⟩ hx₁ ⟨P₂, f₂⟩ hx₂ hEq
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx₁ hx₂
    have hPeq : toP P₁ = toP P₂ := congrArg Prod.fst hEq
    have hFeq : toF f₁ = toF f₂ := congrArg Prod.snd hEq
    have hP12 : P₁ = P₂ := by
      have h1 : ofP (toP P₁) = P₁ := by
        ext B; simp only [ofP, toP, Finset.mem_image]
        constructor
        · rintro ⟨_, ⟨B', hB', rfl⟩, rfl⟩
          rwa [hB_round B' (hsub_biUnion hx₁.2.2.1 B' hB')]
        · intro hB; exact ⟨_, ⟨B, hB, rfl⟩, hB_round B (hsub_biUnion hx₁.2.2.1 B hB)⟩
      have h2 : ofP (toP P₂) = P₂ := by
        ext B; simp only [ofP, toP, Finset.mem_image]
        constructor
        · rintro ⟨_, ⟨B', hB', rfl⟩, rfl⟩
          rwa [hB_round B' (hsub_biUnion hx₂.2.2.1 B' hB')]
        · intro hB; exact ⟨_, ⟨B, hB, rfl⟩, hB_round B (hsub_biUnion hx₂.2.2.1 B hB)⟩
      rw [← h1, hPeq, h2]
    have hF12 : f₁ = f₂ := by
      funext u i
      by_cases hu : u ∈ U
      · have h1U : f₁ u i ∈ U := by
          rw [← hx₁.2.2.1] at hu; obtain ⟨B, hBP, huB⟩ := Finset.mem_biUnion.mp hu
          exact hsub_biUnion hx₁.2.2.1 B hBP ((hx₁.2.2.2.2 B hBP).2.1 u huB i)
        have h2U : f₂ u i ∈ U := by
          rw [← hx₂.2.2.1] at hu; obtain ⟨B, hBP, huB⟩ := Finset.mem_biUnion.mp hu
          exact hsub_biUnion hx₂.2.2.1 B hBP ((hx₂.2.2.2.2 B hBP).2.1 u huB i)
        have h := congrFun (congrFun hFeq (e.symm ⟨u, hu⟩)) i
        simp only [toF, Equiv.apply_symm_apply, h1U, h2U, ↓reduceDIte] at h
        have h' := congrArg (fun a => (e a).1) h
        simpa using h'
      · exact (hx₁.2.2.2.1 u hu i).trans (hx₂.2.2.2.1 u hu i).symm
    exact Prod.ext hP12 hF12
  · -- Surjectivity onto `GoodStruct univ`
    intro ⟨Q, g⟩ hy
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hy
    obtain ⟨hne, hdisj, hbiU, _, hscc⟩ := hy
    refine ⟨(ofP Q, ofF g), ?_, ?_⟩
    · simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨?_, ?_, ?_, fun u hu i => by simp [ofF, hu], ?_⟩
      · intro B hB; obtain ⟨C, hCQ, rfl⟩ := Finset.mem_image.mp hB
        obtain ⟨a, haC⟩ := hne C hCQ
        exact ⟨(e a).1, Finset.mem_image.mpr ⟨a, haC, rfl⟩⟩
      · intro B₁ hB₁ B₂ hB₂ hne12
        obtain ⟨C₁, hC₁, rfl⟩ := Finset.mem_image.mp hB₁
        obtain ⟨C₂, hC₂, rfl⟩ := Finset.mem_image.mp hB₂
        have hCne : C₁ ≠ C₂ := fun h => hne12 (by subst h; rfl)
        change Disjoint _ _
        rw [Finset.disjoint_left]
        intro u hu₁ hu₂
        obtain ⟨a₁, ha₁, rfl⟩ := Finset.mem_image.mp hu₁
        obtain ⟨a₂, ha₂, h21⟩ := Finset.mem_image.mp hu₂
        have heq : a₂ = a₁ := e.injective (Subtype.ext h21)
        subst heq
        exact Finset.disjoint_left.mp (hdisj hC₁ hC₂ hCne) ha₁ ha₂
      · ext u; simp only [ofP, Finset.mem_biUnion, id_eq]
        constructor
        · rintro ⟨B, hB, huB⟩
          obtain ⟨C, _, rfl⟩ := Finset.mem_image.mp hB
          obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp huB
          exact (e a).2
        · intro hu
          have hmem : e.symm ⟨u, hu⟩ ∈ Q.biUnion id := by rw [hbiU]; exact Finset.mem_univ _
          obtain ⟨C, hCQ, haC⟩ := Finset.mem_biUnion.mp hmem
          exact ⟨_, Finset.mem_image.mpr ⟨C, hCQ, rfl⟩,
            Finset.mem_image.mpr ⟨e.symm ⟨u, hu⟩, haC, by simp⟩⟩
      · intro B hB; obtain ⟨C, hCQ, rfl⟩ := Finset.mem_image.mp hB
        obtain ⟨hCne, hCcl, hCsc⟩ := hscc C hCQ
        refine ⟨?_, ?_, ?_⟩
        · obtain ⟨a, haC⟩ := hCne; exact ⟨(e a).1, Finset.mem_image.mpr ⟨a, haC, rfl⟩⟩
        · intro u hu i
          obtain ⟨a, haC, rfl⟩ := Finset.mem_image.mp hu
          simp only [ofF, (e a).2, ↓reduceDIte, Subtype.coe_eta, Equiv.symm_apply_apply]
          exact Finset.mem_image.mpr ⟨g a i, hCcl a haC i, rfl⟩
        · intro u hu v hv
          obtain ⟨a, haC, rfl⟩ := Finset.mem_image.mp hu
          obtain ⟨b, hbC, rfl⟩ := Finset.mem_image.mp hv
          have hgen : ∀ x y : Fin U.card, Reach g x y → Reach (ofF g) (e x).1 (e y).1 := by
            intro x y hxy
            induction hxy with
            | refl => exact Relation.ReflTransGen.refl
            | tail _ hstep ih =>
                obtain ⟨i, hi⟩ := hstep
                exact Relation.ReflTransGen.tail ih ⟨i, by simp [ofF, (e _).2, hi]⟩
          exact hgen a b (hCsc a haC b hbC)
    · apply Prod.ext
      · ext C; simp only [toP, ofP, Finset.mem_image]
        constructor
        · rintro ⟨_, ⟨C', hC', rfl⟩, rfl⟩; rwa [hC_round C']
        · intro hC; exact ⟨_, ⟨C, hC, rfl⟩, hC_round C⟩
      · funext a i; simp [toF, ofF, (e a).2]
  · -- Preserves `(-1)^P.card`!
    intro ⟨P, f⟩ hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    have hcard : (toP P).card = P.card := by
      refine Finset.card_image_of_injOn fun B₁ hB₁ B₂ hB₂ hEq => ?_
      have h1 := hB_round B₁ (hsub_biUnion hx.2.2.1 B₁ hB₁)
      have h2 := hB_round B₂ (hsub_biUnion hx.2.2.1 B₂ hB₂)
      rw [← h1, hEq, h2]
    simp [hcard]

/-- Base case: `w k 0 = 1`. -/
private lemma w_zero (k : ℕ) : w k 0 = 1 := by
  classical
  unfold w W
  have hsing : Finset.univ.filter (IsGoodStruct (k := k) (Finset.univ : Finset (Fin 0))) =
      {(∅, fun u _ => u)} := by
    ext ⟨P, f⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Prod.mk.injEq]
    constructor
    · intro ⟨hne, _, _, _, _⟩
      refine ⟨?_, funext fun u => Fin.elim0 u⟩
      ext B; simp only [Finset.notMem_empty, iff_false]
      intro hBP; obtain ⟨u, _⟩ := hne B hBP; exact Fin.elim0 u
    · rintro ⟨rfl, rfl⟩
      exact ⟨fun _ h => absurd h (Finset.notMem_empty _), by simp, by ext u; exact Fin.elim0 u,
        fun u => Fin.elim0 u, fun _ h => absurd h (Finset.notMem_empty _)⟩
  rw [hsing, Finset.sum_singleton, Finset.card_empty, pow_zero]

/-- Recurrence for `w`: for `m ≥ 1`,
`w k m = - ∑ j ∈ Finset.Icc 1 m, C(m - 1, j - 1) * numLabeledSC k j * w k (m - j)`. -/
private lemma w_rec (k m : ℕ) (hm : 1 ≤ m) :
    w k m = - ∑ j ∈ Finset.Icc 1 m,
      ((Nat.choose (m - 1) (j - 1) : ℕ) : ℤ) * ((numLabeledSC k j : ℕ) : ℤ) * w k (m - j) := by
  classical
  let z0 : Fin m := ⟨0, by omega⟩
  -- Every `(P, f) ∈ GoodStruct univ` has a unique block `B ∈ P` containing `z0`.
  -- Group `GoodStruct univ` by the block `B` containing `z0`!
  let S0 : Finset (Finset (Fin m)) := Finset.univ.filter (fun B : Finset (Fin m) => z0 ∈ B)
  have hpart : w k m = ∑ B ∈ S0,
      ∑ x ∈ (Finset.univ.filter (fun x : Finset (Finset (Fin m)) × (Fin m → Fin k → Fin m) =>
        IsGoodStruct (k := k) Finset.univ x ∧ B ∈ x.1)), (-1 : ℤ) ^ x.1.card := by
    unfold w W
    rw [← Finset.sum_biUnion]
    · congr 1; ext ⟨P, f⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, S0]
      constructor
      · intro hx
        have hz : z0 ∈ P.biUnion id := by rw [hx.2.2.1]; exact Finset.mem_univ _
        obtain ⟨B, hBP, hzB⟩ := Finset.mem_biUnion.mp hz
        exact ⟨B, hzB, hx, hBP⟩
      · rintro ⟨_, _, hx, _⟩; exact hx
    · intro B₁ hB₁ B₂ hB₂ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro ⟨P, f⟩ h1 h2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      have hz₁ : z0 ∈ B₁ := (Finset.mem_filter.mp hB₁).2
      have hz₂ : z0 ∈ B₂ := (Finset.mem_filter.mp hB₂).2
      exact Finset.disjoint_left.mp (h1.1.2.1 h1.2 h2.2 hne) hz₁ hz₂
  -- For each fixed `B ∈ S0`, the inner sum factors as `- numLabeledSC k B.card * W (univ \ B)`!
  have hinner : ∀ B ∈ S0,
      ∑ x ∈ (Finset.univ.filter (fun x : Finset (Finset (Fin m)) × (Fin m → Fin k → Fin m) =>
        IsGoodStruct (k := k) Finset.univ x ∧ B ∈ x.1)), (-1 : ℤ) ^ x.1.card =
      -((numLabeledSC k B.card : ℕ) : ℤ) * w k (m - B.card) := by
    intro B hB
    have hzB : z0 ∈ B := (Finset.mem_filter.mp hB).2
    have hBne : B.Nonempty := ⟨z0, hzB⟩
    let Fc : Finset (Fin m → Fin k → Fin m) :=
      Finset.univ.filter (fun f => (∀ u, u ∉ B → ∀ i : Fin k, f u i = u) ∧ IsSinkSCC f B)
    let Gc : Finset (Finset (Finset (Fin m)) × (Fin m → Fin k → Fin m)) :=
      Finset.univ.filter (IsGoodStruct (k := k) (Finset.univ \ B))
    have hbij : ∑ x ∈ (Finset.univ.filter (fun x : Finset (Finset (Fin m)) × (Fin m → Fin k → Fin m) =>
          IsGoodStruct (k := k) Finset.univ x ∧ B ∈ x.1)), (-1 : ℤ) ^ x.1.card =
        ∑ y ∈ Fc ×ˢ Gc, -((-1 : ℤ) ^ y.2.1.card) := by
      refine Finset.sum_nbij (fun x =>
          (fun u i => if u ∈ B then x.2 u i else u,
           (x.1.erase B, fun u i => if u ∈ B then u else x.2 u i))) ?_ ?_ ?_ ?_
      · intro ⟨P, f⟩ hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
        obtain ⟨⟨hne, hdisj, hbiU, _, hscc⟩, hBP⟩ := hx
        rw [Finset.mem_product]
        constructor
        · simp only [Fc, Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨fun u hu i => by simp [hu], ?_⟩
          exact (isSinkSCC_congr fun u hu i => by simp [hu]).mpr (hscc B hBP)
        · simp only [Gc, Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨fun B' hB' => hne B' (Finset.mem_of_mem_erase hB'),
            hdisj.subset (Finset.erase_subset B P), ?_,
            fun u hu i => by
              have huB : u ∈ B := by
                simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, not_not] at hu; exact hu
              simp [huB],
            fun B' hB' => ?_⟩
          · ext u
            simp only [Finset.mem_biUnion, Finset.mem_erase, id_eq, Finset.mem_sdiff, Finset.mem_univ, true_and]
            constructor
            · rintro ⟨B', ⟨hB'ne, hB'P⟩, huB'⟩
              intro huB
              exact Finset.disjoint_left.mp (hdisj hB'P hBP hB'ne) huB' huB
            · intro huB
              have huU : u ∈ P.biUnion id := by rw [hbiU]; exact Finset.mem_univ _
              obtain ⟨B', hB'P, huB'⟩ := Finset.mem_biUnion.mp huU
              exact ⟨B', ⟨fun h => huB (h ▸ huB'), hB'P⟩, huB'⟩
          · have hB'ne : B' ≠ B := (Finset.mem_erase.mp hB').1
            have hB'P : B' ∈ P := (Finset.mem_erase.mp hB').2
            have hdis : Disjoint B' B := hdisj hB'P hBP hB'ne
            exact (isSinkSCC_congr fun u hu i => by
              have huB : u ∉ B := Finset.disjoint_left.mp hdis hu
              simp [huB]).mpr (hscc B' hB'P)
      · intro ⟨P₁, f₁⟩ hx₁ ⟨P₂, f₂⟩ hx₂ hEq
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx₁ hx₂
        have h1 := congrArg Prod.fst hEq
        have h2 := congrArg (fun z => z.2.1) hEq
        have h3 := congrArg (fun z => z.2.2) hEq
        dsimp only at h1 h2 h3
        apply Prod.ext
        · dsimp only; rw [← Finset.insert_erase hx₁.2, ← Finset.insert_erase hx₂.2, h2]
        · funext u i
          by_cases hu : u ∈ B
          · have := congrFun (congrFun h1 u) i; simpa [hu] using this
          · have := congrFun (congrFun h3 u) i; simpa [hu] using this
      · intro ⟨fB, ⟨Q, fR⟩⟩ hy
        rw [Finset.mem_coe, Finset.mem_product] at hy
        obtain ⟨hfB, hQR⟩ := hy
        simp only [Fc, Gc, Finset.mem_filter, Finset.mem_univ, true_and] at hfB hQR
        have hBnotQ : B ∉ Q := by
          intro hBQ
          have hsub : B ⊆ Finset.univ \ B := by
            rw [← hQR.2.2.1]; intro u hu; exact Finset.mem_biUnion.mpr ⟨B, hBQ, hu⟩
          exact (Finset.mem_sdiff.mp (hsub hzB)).2 hzB
        let f : Fin m → Fin k → Fin m := fun u i => if u ∈ B then fB u i else fR u i
        refine ⟨(insert B Q, f), ?_, ?_⟩
        · simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_insert, true_or, and_true]
          refine ⟨?_, ?_, ?_, fun _ h => absurd (Finset.mem_univ _) h, ?_⟩
          · intro B' hB'
            rcases Finset.mem_insert.mp hB' with rfl | hB'Q
            · exact hBne
            · exact hQR.1 B' hB'Q
          · rw [Finset.coe_insert]
            refine Set.pairwiseDisjoint_insert.mpr ⟨hQR.2.1, fun B' hB'Q _ => ?_⟩
            rw [Finset.disjoint_left]
            intro u huB huB'
            have : u ∈ Finset.univ \ B := by
              rw [← hQR.2.2.1]; exact Finset.mem_biUnion.mpr ⟨B', hB'Q, huB'⟩
            exact (Finset.mem_sdiff.mp this).2 huB
          · rw [Finset.biUnion_insert, id_eq, hQR.2.2.1, Finset.union_sdiff_of_subset (Finset.subset_univ B)]
          · intro B' hB'
            rcases Finset.mem_insert.mp hB' with rfl | hB'Q
            · exact (isSinkSCC_congr fun u hu i => by simp [f, hu]).mpr hfB.2
            · refine (isSinkSCC_congr fun u hu i => ?_).mpr (hQR.2.2.2.2 B' hB'Q)
              have huB : u ∉ B := by
                have : u ∈ Finset.univ \ B := by
                  rw [← hQR.2.2.1]; exact Finset.mem_biUnion.mpr ⟨B', hB'Q, hu⟩
                exact (Finset.mem_sdiff.mp this).2
              simp [f, huB]
        · refine Prod.ext (funext fun u => funext fun i => ?_) (Prod.ext (Finset.erase_insert hBnotQ) (funext fun u => funext fun i => ?_))
          · by_cases hu : u ∈ B
            · simp [f, hu]
            · simp [hu, hfB.1 u hu i]
          · by_cases hu : u ∈ B
            · dsimp only; rw [if_pos hu]; exact (hQR.2.2.2.1 u (by simp [hu]) i).symm
            · simp [f, hu]
      · intro ⟨P, f⟩ hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
        dsimp only
        rw [← Finset.card_erase_add_one hx.2, pow_succ]; ring
    rw [hbij, Finset.sum_product]
    dsimp only
    rw [Finset.sum_const, nsmul_eq_mul]
    have hFc : Fc.card = numLabeledSC k B.card := card_sinkSCC_on_subset B hBne
    have hGc : ∑ y ∈ Gc, -((-1 : ℤ) ^ y.1.card) = - W (k := k) (Finset.univ \ B) := by
      rw [Finset.sum_neg_distrib]; rfl
    rw [hFc, hGc, W_eq_w_card, Finset.card_sdiff_of_subset (Finset.subset_univ B), Finset.card_univ, Fintype.card_fin]
    ring
  rw [hpart]
  trans ∑ B ∈ S0, (-(((numLabeledSC k B.card : ℕ) : ℤ) * w k (m - B.card)))
  · exact Finset.sum_congr rfl fun B hB => by rw [hinner B hB]; ring
  rw [Finset.sum_neg_distrib]
  congr 1
  have hgroup : ∑ B ∈ S0, ((numLabeledSC k B.card : ℕ) : ℤ) * w k (m - B.card) =
      ∑ j ∈ Finset.Icc 1 m,
        ∑ B ∈ S0.filter (fun B => B.card = j), ((numLabeledSC k j : ℕ) : ℤ) * w k (m - j) := by
    have h1 : ∑ B ∈ S0, ((numLabeledSC k B.card : ℕ) : ℤ) * w k (m - B.card) =
        ∑ j ∈ Finset.Icc 1 m,
          ∑ B ∈ S0.filter (fun B => B.card = j), ((numLabeledSC k B.card : ℕ) : ℤ) * w k (m - B.card) := by
      rw [← Finset.sum_biUnion]
      · congr 1; ext B
        simp only [Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_filter]
        constructor
        · intro hB
          have hzB : z0 ∈ B := (Finset.mem_filter.mp hB).2
          have hpos : 1 ≤ B.card := Finset.card_pos.mpr ⟨z0, hzB⟩
          have hle : B.card ≤ m := by simpa using Finset.card_le_univ B
          exact ⟨B.card, ⟨hpos, hle⟩, hB, rfl⟩
        · rintro ⟨_, _, hB, _⟩; exact hB
      · intro j₁ _ j₂ _ hne
        change Disjoint _ _
        rw [Finset.disjoint_left]
        intro B h1 h2
        exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
    rw [h1]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun B hB => ?_
    rw [(Finset.mem_filter.mp hB).2]
  rw [hgroup]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : (S0.filter (fun B => B.card = j)).card = Nat.choose (m - 1) (j - 1) := by
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hbij : (S0.filter (fun B => B.card = j)).card =
        ((Finset.univ.erase z0).powersetCard (j - 1)).card := by
      refine Finset.card_bij (fun B _ => B.erase z0) ?_ ?_ ?_
      · intro B hB
        simp only [S0, Finset.mem_filter, Finset.mem_univ, true_and] at hB
        rw [Finset.mem_powersetCard]
        exact ⟨Finset.erase_subset_erase z0 (Finset.subset_univ B), by
          rw [Finset.card_erase_of_mem hB.1, hB.2]⟩
      · intro B₁ hB₁ B₂ hB₂ hEq
        simp only [S0, Finset.mem_filter, Finset.mem_univ, true_and] at hB₁ hB₂
        rw [← Finset.insert_erase hB₁.1, ← Finset.insert_erase hB₂.1, hEq]
      · intro T hT
        rw [Finset.mem_powersetCard] at hT
        have hznot : z0 ∉ T := fun hz => (Finset.mem_erase.mp (hT.1 hz)).1 rfl
        refine ⟨insert z0 T, ?_, Finset.erase_insert hznot⟩
        simp only [S0, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, true_or]
        rw [Finset.card_insert_of_notMem hznot, hT.2]; omega
    rw [hbij, Finset.card_powersetCard, Finset.card_erase_of_mem (Finset.mem_univ z0),
        Finset.card_univ, Fintype.card_fin]
  rw [hcard]; ring

/-- Robinson's sink-SCC inclusion-exclusion identity:
for every `n ≥ 1`, `∑_{j=0}^n C(n, j) * w k j * n^(k * (n - j)) = 0`. -/
private lemma sinkSCC_inclusion_exclusion (k n : ℕ) (hn : 1 ≤ n) :
    ∑ j ∈ Finset.range (n + 1),
      ((Nat.choose n j : ℕ) : ℤ) * w k j * ((n : ℤ) ^ (k * (n - j))) = 0 := by
  classical
  -- Step 1: Rewrite as a sum over all subsets `U : Finset (Fin n)` of `W U * n^(k * (n - U.card))`.
  have hstep1 : ∑ j ∈ Finset.range (n + 1),
        ((Nat.choose n j : ℕ) : ℤ) * w k j * ((n : ℤ) ^ (k * (n - j))) =
      ∑ U : Finset (Fin n), W (k := k) U * ((n : ℤ) ^ (k * (n - U.card))) := by
    have hgroup : ∑ U : Finset (Fin n), W (k := k) U * ((n : ℤ) ^ (k * (n - U.card))) =
        ∑ j ∈ Finset.range (n + 1),
          ∑ U ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun U => U.card = j),
            w k j * ((n : ℤ) ^ (k * (n - j))) := by
      have h1 : ∑ U : Finset (Fin n), W (k := k) U * ((n : ℤ) ^ (k * (n - U.card))) =
          ∑ j ∈ Finset.range (n + 1),
            ∑ U ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun U => U.card = j),
              W (k := k) U * ((n : ℤ) ^ (k * (n - U.card))) := by
        rw [← Finset.sum_biUnion]
        · congr 1; ext U; simp only [Finset.mem_univ, Finset.mem_biUnion, Finset.mem_range,
            Finset.mem_filter, true_and, true_iff]
          exact ⟨U.card, Nat.lt_succ_of_le (by simpa using Finset.card_le_univ U), rfl⟩
        · intro j₁ _ j₂ _ hne
          change Disjoint _ _
          rw [Finset.disjoint_left]
          intro U h1 h2
          exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
      rw [h1]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun U hU => ?_
      rw [W_eq_w_card, (Finset.mem_filter.mp hU).2]
    rw [hgroup]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have hcard : ((Finset.univ : Finset (Finset (Fin n))).filter (fun U => U.card = j)).card =
        Nat.choose n j := by
      have : (Finset.univ : Finset (Finset (Fin n))).filter (fun U => U.card = j) =
          (Finset.univ : Finset (Fin n)).powersetCard j := by
        ext U; simp [Finset.mem_powersetCard]
      rw [this, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
    rw [hcard]; ring
  rw [hstep1]
  -- Step 2: Expand `W U * n^(k * (n - U.card))` as a sum over `(P, δ)` where `P ⊆ sinkSCCs δ`!
  have hstep2 : ∑ U : Finset (Fin n), W (k := k) U * ((n : ℤ) ^ (k * (n - U.card))) =
      ∑ δ : Fin n → Fin k → Fin n, ∑ P ∈ (sinkSCCs δ).powerset, (-1 : ℤ) ^ P.card := by
    -- Express the LHS as a sum over the sigma type `(U, (P, f), g)` where `g : {u // u ∉ U} → Fin k → Fin n`
    have hLHS : ∀ U : Finset (Fin n),
        W (k := k) U * ((n : ℤ) ^ (k * (n - U.card))) =
        ∑ x ∈ (Finset.univ.filter (IsGoodStruct (k := k) U)) ×ˢ
              (Finset.univ : Finset ({u : Fin n // u ∉ U} → Fin k → Fin n)),
          (-1 : ℤ) ^ x.1.1.card := by
      intro U
      rw [Finset.sum_product, W, Finset.sum_mul]
      refine Finset.sum_congr rfl fun x _ => ?_
      dsimp only
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fun,
          Fintype.card_fin, Fintype.card_fin, Fintype.card_subtype_compl, Fintype.card_fin,
          Fintype.card_coe, ← pow_mul, nsmul_eq_mul, mul_comm]
      push_cast; rfl
    simp_rw [hLHS]
    have hsigL : ∑ U : Finset (Fin n),
        ∑ x ∈ (Finset.univ.filter (IsGoodStruct (k := k) U)) ×ˢ
              (Finset.univ : Finset ({u : Fin n // u ∉ U} → Fin k → Fin n)),
          (-1 : ℤ) ^ x.1.1.card =
        ∑ s ∈ (Finset.univ : Finset (Finset (Fin n))).sigma
            (fun U => (Finset.univ.filter (IsGoodStruct (k := k) U)) ×ˢ
              (Finset.univ : Finset ({u : Fin n // u ∉ U} → Fin k → Fin n))),
          (-1 : ℤ) ^ s.2.1.1.card := Finset.sum_sigma' _ _ _
    have hsigR : ∑ δ : Fin n → Fin k → Fin n, ∑ P ∈ (sinkSCCs δ).powerset, (-1 : ℤ) ^ P.card =
        ∑ s ∈ (Finset.univ : Finset (Fin n → Fin k → Fin n)).sigma (fun δ => (sinkSCCs δ).powerset),
          (-1 : ℤ) ^ s.2.card := Finset.sum_sigma' _ _ _
    rw [hsigL, hsigR]
    refine Finset.sum_nbij
      (fun s => ⟨fun u i => if h : u ∈ s.1 then s.2.1.2 u i else s.2.2 ⟨u, h⟩ i, s.2.1.1⟩)
      ?_ ?_ ?_ ?_
    · intro ⟨U, ⟨⟨P, f⟩, g⟩⟩ hs
      simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_product, Finset.mem_filter,
        true_and, and_true] at hs ⊢
      rw [Finset.mem_powerset]
      intro B hBP
      simp only [sinkSCCs, Finset.mem_filter, Finset.mem_univ, true_and]
      have hBU : B ⊆ U := by intro u hu; rw [← hs.2.2.1]; exact Finset.mem_biUnion.mpr ⟨B, hBP, hu⟩
      exact (isSinkSCC_congr fun u hu i => by simp [hBU hu]).mpr (hs.2.2.2.2 B hBP)
    · intro ⟨U₁, ⟨⟨P₁, f₁⟩, g₁⟩⟩ hs₁ ⟨U₂, ⟨⟨P₂, f₂⟩, g₂⟩⟩ hs₂ hEq
      simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_univ, Finset.mem_product,
        Finset.mem_filter, true_and, and_true] at hs₁ hs₂
      have hPeq : P₁ = P₂ := by
        have := congrArg Sigma.snd hEq; simpa using this
      have hUeq : U₁ = U₂ := by rw [← hs₁.2.2.1, ← hs₂.2.2.1, hPeq]
      subst hUeq; subst hPeq
      have hδeq : (fun u i => if h : u ∈ U₁ then f₁ u i else g₁ ⟨u, h⟩ i) =
          (fun u i => if h : u ∈ U₁ then f₂ u i else g₂ ⟨u, h⟩ i) := by
        have := congrArg Sigma.fst hEq; simpa using this
      have hf : f₁ = f₂ := by
        funext u i
        by_cases hu : u ∈ U₁
        · have := congrFun (congrFun hδeq u) i; simpa [hu] using this
        · exact (hs₁.2.2.2.1 u hu i).trans (hs₂.2.2.2.1 u hu i).symm
      have hg : g₁ = g₂ := by
        funext ⟨u, hu⟩ i
        have := congrFun (congrFun hδeq u) i; simpa [hu] using this
      subst hf; subst hg; rfl
    · intro ⟨δ, P⟩ hy
      simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_univ, Finset.mem_powerset,
        true_and] at hy
      let U : Finset (Fin n) := P.biUnion id
      let f : Fin n → Fin k → Fin n := fun u i => if u ∈ U then δ u i else u
      let g : {u : Fin n // u ∉ U} → Fin k → Fin n := fun u i => δ u.1 i
      refine ⟨⟨U, ⟨(P, f), g⟩⟩, ?_, ?_⟩
      · simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_univ, Finset.mem_product,
          Finset.mem_filter, true_and, and_true]
        refine ⟨?_, ?_, rfl, fun u hu i => by simp [f, hu], ?_⟩
        · intro B hBP; exact (Finset.mem_filter.mp (hy hBP)).2.1
        · intro B₁ hB₁ B₂ hB₂ hne
          change Disjoint _ _
          rw [Finset.disjoint_left]
          intro u hu₁ hu₂
          exact hne (isSinkSCC_eq_of_inter (Finset.mem_filter.mp (hy hB₁)).2
            (Finset.mem_filter.mp (hy hB₂)).2 hu₁ hu₂)
        · intro B hBP
          have hBU : B ⊆ U := fun u hu => Finset.mem_biUnion.mpr ⟨B, hBP, hu⟩
          exact (isSinkSCC_congr fun u hu i => by simp [f, hBU hu]).mpr (Finset.mem_filter.mp (hy hBP)).2
      · refine Sigma.ext ?_ (by simp)
        funext u i; by_cases hu : u ∈ U <;> simp [f, g, hu]
    · intro _ _; rfl
  rw [hstep2]
  -- Step 3: For every `δ`, `(sinkSCCs δ).Nonempty`, so `∑ P ∈ (sinkSCCs δ).powerset, (-1)^P.card = 0`!
  refine Finset.sum_eq_zero fun δ _ => ?_
  obtain ⟨B₀, hB₀⟩ := exists_isSinkSCC (k := k) hn δ
  have hne : (sinkSCCs δ).Nonempty := ⟨B₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hB₀⟩⟩
  have hpos : 0 < (sinkSCCs δ).card := Finset.card_pos.mpr hne
  have hpow : ∑ P ∈ (sinkSCCs δ).powerset, (-1 : ℤ) ^ P.card =
      ((-1 : ℤ) + 1) ^ (sinkSCCs δ).card := by
    rw [add_pow]
    have hgroup : ∑ P ∈ (sinkSCCs δ).powerset, (-1 : ℤ) ^ P.card =
        ∑ j ∈ Finset.range ((sinkSCCs δ).card + 1),
          ∑ P ∈ (sinkSCCs δ).powersetCard j, (-1 : ℤ) ^ j := by
      have h1 : ∑ P ∈ (sinkSCCs δ).powerset, (-1 : ℤ) ^ P.card =
          ∑ j ∈ Finset.range ((sinkSCCs δ).card + 1),
            ∑ P ∈ (sinkSCCs δ).powersetCard j, (-1 : ℤ) ^ P.card := by
        rw [← Finset.sum_biUnion]
        · congr 1; ext P; simp only [Finset.mem_powerset, Finset.mem_biUnion, Finset.mem_range,
            Finset.mem_powersetCard]
          constructor
          · intro hP; exact ⟨P.card, Nat.lt_succ_of_le (Finset.card_le_card hP), hP, rfl⟩
          · rintro ⟨_, _, hP, _⟩; exact hP
        · intro j₁ _ j₂ _ hne12
          change Disjoint _ _
          rw [Finset.disjoint_left]; intro P h1 h2
          exact hne12 ((Finset.mem_powersetCard.mp h1).2.symm.trans (Finset.mem_powersetCard.mp h2).2)
      rw [h1]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun P hP => ?_
      rw [(Finset.mem_powersetCard.mp hP).2]
    rw [hgroup]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul, one_pow, mul_one]
    ring
  rw [hpow, neg_add_cancel, zero_pow (by omega)]

/-- General theorem for any `k ≥ 1`: if `F * invF = 1`, `coeff 0 F = 1`, and
`[x^n] exp(n^k x) * invF = 0` for all `n ≥ 1`, then `[x^(n-1)] (F' * invF) = numLabeledSC k n / (n-1)!`. -/
private theorem main_general (k : ℕ) :
    ∀ F invF : PowerSeries ℚ,
      F * invF = 1 →
      PowerSeries.coeff 0 F = 1 →
      (∀ n : ℕ, 1 ≤ n →
        PowerSeries.coeff n (PowerSeries.rescale ((n ^ k : ℕ) : ℚ) (PowerSeries.exp ℚ) * invF) = 0) →
      ∀ n : ℕ, 1 ≤ n →
        PowerSeries.coeff (n - 1) (PowerSeries.derivative ℚ F * invF) =
          (numLabeledSC k n : ℚ) / ((Nat.factorial (n - 1) : ℕ) : ℚ) := by
  intro F invF hFinv hF0 hEq
  -- Step 1: Define `invG = ∑ (w k n / n!) * x^n` and `S = ∑_{n≥1} (numLabeledSC k n / n!) * x^n`.
  let invG : PowerSeries ℚ := PowerSeries.mk fun n => (w k n : ℚ) / ((Nat.factorial n : ℕ) : ℚ)
  let S : PowerSeries ℚ := PowerSeries.mk fun n =>
    if n = 0 then 0 else (numLabeledSC k n : ℚ) / ((Nat.factorial n : ℕ) : ℚ)
  have hinvG0 : PowerSeries.coeff 0 invG = 1 := by
    simp [invG, w_zero]
  have hinvF0 : PowerSeries.coeff 0 invF = 1 := by
    have h0 := congrArg (PowerSeries.coeff 0) hFinv
    rw [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_zero, Finset.sum_singleton,
        hF0, one_mul, PowerSeries.coeff_one, if_pos rfl] at h0
    exact h0
  -- Step 2: Show `invG` satisfies the exact same `[x^n] exp(n^k x) * invG = 0` equation!
  have hinvG_eq : ∀ n : ℕ, 1 ≤ n →
      PowerSeries.coeff n (PowerSeries.rescale ((n ^ k : ℕ) : ℚ) (PowerSeries.exp ℚ) * invG) = 0 := by
    intro n hn
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun a b => PowerSeries.coeff a (PowerSeries.rescale ((n ^ k : ℕ) : ℚ) (PowerSeries.exp ℚ)) *
          PowerSeries.coeff b invG)]
    have hrew : ∑ j ∈ Finset.range (n + 1),
        PowerSeries.coeff (n - j) (PowerSeries.rescale ((n ^ k : ℕ) : ℚ) (PowerSeries.exp ℚ)) *
          PowerSeries.coeff j invG =
        (1 / ((Nat.factorial n : ℕ) : ℚ)) *
          (∑ j ∈ Finset.range (n + 1),
            ((Nat.choose n j : ℕ) : ℚ) * (w k j : ℚ) * (((n : ℚ) ^ (k * (n - j))))) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      rw [PowerSeries.coeff_rescale, PowerSeries.coeff_exp, PowerSeries.coeff_mk]
      have hch := Nat.choose_mul_factorial_mul_factorial hjn
      have hchq : ((Nat.choose n j : ℕ) : ℚ) * ((Nat.factorial j : ℕ) : ℚ) *
          ((Nat.factorial (n - j) : ℕ) : ℚ) = ((Nat.factorial n : ℕ) : ℚ) := by
        exact_mod_cast hch
      have hfn : ((Nat.factorial n : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
      have hfj : ((Nat.factorial j : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
      have hfnj : ((Nat.factorial (n - j) : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n - j))
      have halg : ∀ x : ℚ, algebraMap ℚ ℚ x = x := fun _ => rfl
      rw [halg, Nat.cast_pow, ← pow_mul]
      field_simp [hfn, hfj, hfnj]
      rw [← hchq]; ring
    have hsum_flip : ∑ a ∈ Finset.range (n + 1),
        PowerSeries.coeff a (PowerSeries.rescale ((n ^ k : ℕ) : ℚ) (PowerSeries.exp ℚ)) *
          PowerSeries.coeff (n - a) invG =
        ∑ j ∈ Finset.range (n + 1),
        PowerSeries.coeff (n - j) (PowerSeries.rescale ((n ^ k : ℕ) : ℚ) (PowerSeries.exp ℚ)) *
          PowerSeries.coeff j invG := by
      refine Finset.sum_nbij (fun a => n - a) ?_ ?_ ?_ ?_
      · intro a ha; simp only [Finset.mem_range] at ha ⊢; omega
      · intro a ha b hb hab; simp only [Finset.mem_coe, Finset.mem_range] at ha hb; dsimp only at hab; omega
      · intro j hj; simp only [Finset.mem_coe, Finset.mem_range] at hj
        exact ⟨n - j, Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega)), by dsimp only; omega⟩
      · intro a ha; simp only [Finset.mem_range] at ha; rw [show n - (n - a) = a by omega]
    rw [hsum_flip, hrew]
    have hIE : (∑ j ∈ Finset.range (n + 1),
        ((Nat.choose n j : ℕ) : ℚ) * (w k j : ℚ) * ((n : ℚ) ^ (k * (n - j)))) = 0 := by
      exact_mod_cast sinkSCC_inclusion_exclusion k n hn
    rw [hIE, mul_zero]
  -- Step 3: Uniqueness -> `invF = invG`!
  have hinv_eq : invF = invG := by
    apply PowerSeries.ext
    intro n
    induction n using Nat.strong_induction_on with
    | h N ih =>
      by_cases hN0 : N = 0
      · subst hN0; rw [hinvF0, hinvG0]
      have hN1 : 1 ≤ N := by omega
      have h1 := hEq N hN1
      have h2 := hinvG_eq N hN1
      rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (fun a b => PowerSeries.coeff a (PowerSeries.rescale ((N ^ k : ℕ) : ℚ) (PowerSeries.exp ℚ)) *
            PowerSeries.coeff b invF), Finset.sum_range_succ'] at h1
      rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (fun a b => PowerSeries.coeff a (PowerSeries.rescale ((N ^ k : ℕ) : ℚ) (PowerSeries.exp ℚ)) *
            PowerSeries.coeff b invG), Finset.sum_range_succ'] at h2
      have hsum : ∑ j ∈ Finset.range N,
          PowerSeries.coeff (j + 1) (PowerSeries.rescale ((N ^ k : ℕ) : ℚ) (PowerSeries.exp ℚ)) *
            PowerSeries.coeff (N - (j + 1)) invF =
          ∑ j ∈ Finset.range N,
          PowerSeries.coeff (j + 1) (PowerSeries.rescale ((N ^ k : ℕ) : ℚ) (PowerSeries.exp ℚ)) *
            PowerSeries.coeff (N - (j + 1)) invG := by
        refine Finset.sum_congr rfl fun j hj => ?_
        have hjN : j < N := Finset.mem_range.mp hj
        rw [ih (N - (j + 1)) (by omega)]
      rw [hsum] at h1
      have halg : ∀ x : ℚ, algebraMap ℚ ℚ x = x := fun _ => rfl
      simp only [Nat.sub_zero, PowerSeries.coeff_rescale, PowerSeries.coeff_exp, pow_zero,
        Nat.factorial_zero, Nat.cast_one, div_one, halg, one_mul] at h1 h2
      linarith
  -- Step 4: Show `derivative ℚ invG = -(derivative ℚ S) * invG` from `w_rec`!
  have hderiv_invG : PowerSeries.derivative ℚ invG = -(PowerSeries.derivative ℚ S) * invG := by
    apply PowerSeries.ext; intro r
    rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mk, neg_mul, map_neg,
        PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (fun a b => PowerSeries.coeff a (PowerSeries.derivative ℚ S) * PowerSeries.coeff b invG)]
    have hw : (w k (r + 1) : ℚ) = - ∑ j ∈ Finset.Icc 1 (r + 1),
        ((Nat.choose r (j - 1) : ℕ) : ℚ) * ((numLabeledSC k j : ℕ) : ℚ) * (w k (r + 1 - j) : ℚ) := by
      have h := w_rec k (r + 1) (by omega)
      simp only [Nat.add_sub_cancel] at h
      exact_mod_cast h
    rw [hw]
    have hIcc : ∑ j ∈ Finset.Icc 1 (r + 1),
          ((Nat.choose r (j - 1) : ℕ) : ℚ) * ((numLabeledSC k j : ℕ) : ℚ) * (w k (r + 1 - j) : ℚ) =
        ∑ a ∈ Finset.range (r + 1),
          ((Nat.choose r a : ℕ) : ℚ) * ((numLabeledSC k (a + 1) : ℕ) : ℚ) * (w k (r - a) : ℚ) := by
      refine Finset.sum_nbij (fun j => j - 1) ?_ ?_ ?_ ?_
      · intro j hj; simp only [Finset.mem_Icc, Finset.mem_range] at hj ⊢; omega
      · intro a ha b hb hab; simp only [Finset.mem_coe, Finset.mem_Icc] at ha hb; dsimp only at hab; omega
      · intro a ha; simp only [Finset.mem_coe, Finset.mem_range] at ha
        exact ⟨a + 1, Finset.mem_coe.mpr (Finset.mem_Icc.mpr ⟨by omega, by omega⟩), by dsimp only; omega⟩
      · intro j hj; simp only [Finset.mem_Icc] at hj
        rw [show j - 1 + 1 = j by omega, show r - (j - 1) = r + 1 - j by omega]
    rw [hIcc, neg_div, neg_mul, Finset.sum_div, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun a ha => ?_
    have har : a ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
    rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mk, if_neg (Nat.succ_ne_zero a),
        PowerSeries.coeff_mk]
    have hch := Nat.choose_mul_factorial_mul_factorial har
    have hchq : ((Nat.choose r a : ℕ) : ℚ) * ((Nat.factorial a : ℕ) : ℚ) *
        ((Nat.factorial (r - a) : ℕ) : ℚ) = ((Nat.factorial r : ℕ) : ℚ) := by
      exact_mod_cast hch
    have hfr1 : ((Nat.factorial (r + 1) : ℕ) : ℚ) = ((r : ℚ) + 1) * ((Nat.factorial r : ℕ) : ℚ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hfa1 : ((Nat.factorial (a + 1) : ℕ) : ℚ) = ((a : ℚ) + 1) * ((Nat.factorial a : ℕ) : ℚ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hr1 : (r : ℚ) + 1 ≠ 0 := by positivity
    have ha1 : (a : ℚ) + 1 ≠ 0 := by positivity
    have hfr : ((Nat.factorial r : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero r)
    have hfa : ((Nat.factorial a : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero a)
    have hfra : ((Nat.factorial (r - a) : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (r - a))
    rw [hfr1, hfa1]
    field_simp [hr1, ha1, hfr, hfa, hfra]
    linear_combination (numLabeledSC k (a + 1) : ℚ) * (w k (r - a) : ℚ) * hchq
  -- Step 5: From `F * invF = 1`, `F' * invF = - F * invF' = - F * (- S' * invF) = S'`!
  have hlogderiv : PowerSeries.derivative ℚ F * invF = PowerSeries.derivative ℚ S := by
    have h0 : PowerSeries.derivative ℚ (F * invF) = 0 := by
      rw [hFinv]; exact Derivation.map_one_eq_zero _
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, mul_comm invF] at h0
    have h1 : PowerSeries.derivative ℚ F * invF = -(F * PowerSeries.derivative ℚ invF) := by
      linear_combination h0
    rw [h1, hinv_eq, hderiv_invG, ← hinv_eq]
    calc -(F * (-PowerSeries.derivative ℚ S * invF))
      _ = PowerSeries.derivative ℚ S * (F * invF) := by ring
      _ = PowerSeries.derivative ℚ S := by rw [hFinv, mul_one]
  intro n hn
  rw [hlogderiv, PowerSeries.coeff_derivative, show n - 1 + 1 = n by omega,
      PowerSeries.coeff_mk, if_neg (by omega)]
  have hfn : ((Nat.factorial n : ℕ) : ℚ) = (((n - 1 : ℕ) : ℚ) + 1) * ((Nat.factorial (n - 1) : ℕ) : ℚ) := by
    have h : Nat.factorial n = n * Nat.factorial (n - 1) := by
      rw [show n = (n - 1) + 1 by omega, Nat.factorial_succ, show n - 1 + 1 = n by omega]
    have hq : ((Nat.factorial n : ℕ) : ℚ) = (n : ℚ) * ((Nat.factorial (n - 1) : ℕ) : ℚ) := by
      exact_mod_cast h
    rw [hq, show (n : ℚ) = ((n - 1 : ℕ) : ℚ) + 1 by
      have : n = (n - 1) + 1 := by omega
      exact_mod_cast this]
  have hpos : (((n - 1 : ℕ) : ℚ) + 1) ≠ 0 := by positivity
  have hfm : ((Nat.factorial (n - 1) : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  rw [hfn]; field_simp [hpos, hfm]

theorem main_proof :
    ∀ F invF : PowerSeries ℚ,
      F * invF = 1 →
      PowerSeries.coeff 0 F = 1 →
      (∀ n : ℕ, 1 ≤ n →
        PowerSeries.coeff n (PowerSeries.rescale ((n ^ 2 : ℕ) : ℚ) (PowerSeries.exp ℚ) * invF) = 0) →
      ∀ n : ℕ, 1 ≤ n →
        PowerSeries.coeff (n - 1) (PowerSeries.derivative ℚ F * invF) =
          (numLabeledSC 2 n : ℚ) / ((Nat.factorial (n - 1) : ℕ) : ℚ) :=
  main_general 2

end OMA.S_oeis_a304312

theorem OMA.solution : type_of% @OMA.S_oeis_a304312.main :=
  OMA.S_oeis_a304312.main_proof
