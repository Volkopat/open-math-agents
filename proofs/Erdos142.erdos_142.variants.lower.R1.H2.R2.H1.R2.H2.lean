import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R2_H1_R2
import Mathlib
/-
Erdos 142, step lower.R1.H2.R1.H2: fixed positive density forces a k-term progression (k >= 4)
once the interval is long enough, in the log-log form of the reduction.
Mathematics: E. Szemeredi (1975). Formal proof bundled from a port of the Szemeredi
formalization in plby/lean-proofs (src/latest/ErdosProblems, commit 8822f7dd; Apache-2.0,
copyright Boris Alexeev; formal authors credited there). The bridge to the formal-conjectures
definitions is new. Names are shortened to fit the 512 KiB limit.
-/
section
namespace ag
open scoped BigOperators
end ag
end
section
namespace av.ag
open scoped BigOperators
noncomputable def mean {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  𝔼 x, f x
def aN {α : Type*} [DecidableEq α]
    (A : Finset α) (x : α) : ℝ :=
  if x ∈ A then 1 else 0
@[simp]
theorem cG {α : Type*} [DecidableEq α]
    {A : Finset α} {x : α} (hx : x ∈ A) :
    aN A x = 1 := by
  simp [aN, hx]
@[simp]
theorem cj {α : Type*} [DecidableEq α]
    {A : Finset α} {x : α} (hx : x ∉ A) :
    aN A x = 0 := by
  simp [aN, hx]
theorem iM {α : Type*}
    [Fintype α] [DecidableEq α] (A : Finset α) :
    mean (aN A) =
      (A.card : ℝ) / Fintype.card α := by
  rw [mean, Fintype.expect_eq_sum_div_card]
  simp [aN]
@[simp]
theorem Be {α : Type*} [Fintype α] [IsEmpty α] (f : α → ℝ) :
    mean f = 0 := by
  simp [mean]
@[simp]
theorem ml {α : Type*} [Fintype α] [Nonempty α] (c : ℝ) :
    mean (fun _ : α => c) = c := by
  exact Fintype.expect_const c
theorem tX {α : Type*} [Fintype α] (f g : α → ℝ) :
    mean (fun x => f x + g x) = mean f + mean g := by
  exact Finset.expect_add_distrib Finset.univ f g
theorem zI {α : Type*} [Fintype α] (f g : α → ℝ) :
    mean (fun x => f x - g x) = mean f - mean g := by
  exact Finset.expect_sub_distrib Finset.univ f g
theorem k0 {α : Type*} [Fintype α] (c : ℝ) (f : α → ℝ) :
    mean (fun x => c * f x) = c * mean f := by
  exact (Finset.mul_expect Finset.univ f c).symm
theorem o9 {α : Type*} [Fintype α] {f : α → ℝ}
    (hf : ∀ x, 0 ≤ f x) : 0 ≤ mean f := by
  rw [mean, Fintype.expect_eq_sum_div_card]
  exact div_nonneg (Finset.sum_nonneg fun x _ => hf x) (Nat.cast_nonneg _)
theorem mm {α : Type*} [Fintype α] {f g : α → ℝ}
    (ri : ∀ x, f x ≤ g x) : mean f ≤ mean g := by
  rw [mean, mean, Fintype.expect_eq_sum_div_card, Fintype.expect_eq_sum_div_card]
  exact div_le_div_of_nonneg_right
    (Finset.sum_le_sum fun x _ => ri x) (Nat.cast_nonneg _)
theorem sv {α : Type*} [Fintype α] [Nonempty α]
    {f : α → ℝ} {c : ℝ} (hf : ∀ x, f x ≤ c) :
    mean f ≤ c := by
  simpa using mm (f := f) (g := fun _ => c) hf
noncomputable def fq {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β → ℝ) : ℝ :=
  mean (fun x => mean (f x))
theorem zJ {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β → ℝ) :
    fq f = fq (fun y x => f x y) := by
  exact Finset.expect_comm Finset.univ Finset.univ f
end av.ag
end
section
namespace av.ag
open scoped BigOperators
theorem pZ
    {α β : Type*} [Fintype α] [Fintype β]
    (F : α → β → ℝ) :
    mean (fun p : α × β => F p.1 p.2) = fq F := by
  simpa [mean, fq] using
    (Finset.expect_product'
      (Finset.univ : Finset α) (Finset.univ : Finset β) F)
end av.ag
end
section
namespace av.ag
theorem uD
    {Ω : Type*} [Fintype Ω]
    (u v : Ω → ℝ) :
    mean (fun x => u x * v x) ^ 2 ≤
      mean (fun x => u x ^ 2) *
        mean (fun x => v x ^ 2) := by
  simpa [mean] using
    (Finset.expect_mul_sq_le_sq_mul_sq
      (Finset.univ : Finset Ω) u v)
theorem tY
    {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) :
    mean f ^ 2 =
      mean (fun p : Ω × Ω => f p.1 * f p.2) := by
  calc
    mean f ^ 2 = mean f * mean f := pow_two _
    _ = fq (fun x y => f x * f y) := by
      unfold fq mean
      exact
        Finset.expect_mul_expect
          Finset.univ Finset.univ f f
    _ = mean (fun p : Ω × Ω => f p.1 * f p.2) :=
      (pZ fun x y => f x * f y).symm
theorem rZ
    {X Y : Type*} [Fintype X] [Fintype Y]
    (F : X → Y → ℝ) :
    mean (fun x => mean (F x) ^ 2) =
      fq (fun x => fun p : Y × Y =>
        F x p.1 * F x p.2) := by
  unfold fq
  apply congrArg mean
  funext x
  exact tY (F x)
end av.ag
end
section
namespace av.ag
open scoped BigOperators
structure ah
    (J K : Type*) [DecidableEq J] [DecidableEq K]
    (H : Finset (Finset J)) where
  edges : Finset (Finset K)
  projection : K → J
  cW :
    ∀ g ∈ edges, Set.InjOn projection (g : Set K)
  c4 :
    ∀ g ∈ edges, g.image projection ∈ H
namespace ah
variable {J K G : Type*}
  [DecidableEq J] [DecidableEq K]
  {H : Finset (Finset J)}
def a6
    (B : ah J K H) : Prop :=
  ∀ ⦃g⦄, g ∈ B.edges →
    ∀ ⦃f⦄, f ⊆ g → f ∈ B.edges
def order (B : ah J K H) : ℕ :=
  B.edges.sup Finset.card
theorem mn
    (B : ah J K H)
    {g : Finset K} (hg : g ∈ B.edges) :
    g.card ≤ B.order := by
  exact Finset.le_sup hg
def cK
    (B : ah J K H) (g₀ : Finset K) :
    ah J K H where
  edges := B.edges.erase g₀
  projection := B.projection
  cW := by
    intro g hg
    exact B.cW g
      (Finset.mem_of_mem_erase hg)
  c4 := by
    intro g hg
    exact B.c4 g
      (Finset.mem_of_mem_erase hg)
@[simp]
theorem xY
    (B : ah J K H) (g₀ : Finset K) :
    (B.cK g₀).edges = B.edges.erase g₀ :=
  rfl
theorem sX
    (B : ah J K H) (g₀ : Finset K) :
    (B.cK g₀).order ≤ B.order := by
  unfold order cK
  apply Finset.sup_le
  intro g hg
  exact B.mn (Finset.mem_of_mem_erase hg)
theorem oa
    (B : ah J K H)
    (dv : B.a6)
    {g₀ : Finset K} (_hg₀ : g₀ ∈ B.edges)
    (d3 : ∀ g ∈ B.edges, g.card ≤ g₀.card) :
    (B.cK g₀).a6 := by
  intro g hg f ri
  have iq : g ∈ B.edges :=
    Finset.mem_of_mem_erase hg
  have BR : f ∈ B.edges :=
    dv iq ri
  apply Finset.mem_erase.mpr
  refine ⟨?_, BR⟩
  intro D8
  subst f
  have CL : g.card ≤ g₀.card :=
    d3 g iq
  have heq : g₀ = g :=
    Finset.eq_of_subset_of_card_le ri CL
  exact (Finset.mem_erase.mp hg).1 heq.symm
def bo
    (g : Finset K) (x : K → G) :
    ({v : K // v ∈ g} → G) :=
  fun v => x v.1
noncomputable def cp
    (B : ah J K H)
    {g : Finset K} (hg : g ∈ B.edges) :
    {v : K // v ∈ g} ≃
      {j : J // j ∈ g.image B.projection} := by
  classical
  apply Equiv.ofBijective
    (fun v : {v : K // v ∈ g} =>
      (⟨B.projection v.1,
        Finset.mem_image.mpr ⟨v.1, v.2, rfl⟩⟩ :
        {j : J // j ∈ g.image B.projection}))
  constructor
  · intro v w BS
    apply Subtype.ext
    apply B.cW g hg v.2 w.2
    exact congrArg Subtype.val BS
  · intro j
    obtain ⟨v, hv, y0⟩ :=
      Finset.mem_image.mp j.2
    refine ⟨⟨v, hv⟩, ?_⟩
    apply Subtype.ext
    exact y0
noncomputable def ds
    (B : ah J K H)
    {g : Finset K} (hg : g ∈ B.edges)
    (y : {v : K // v ∈ g} → G) :
    ({j : J // j ∈ g.image B.projection} → G) :=
  fun j => y ((B.cp hg).symm j)
abbrev cM
    (J G : Type*) :=
  (e : Finset J) → ({j : J // j ∈ e} → G) → ℝ
def eI
    (H : Finset (Finset J))
    (A : cM J G) : Prop :=
  ∀ e ∈ H, ∀ y, 0 ≤ A e y ∧ A e y ≤ 1
noncomputable def ao
    (B : ah J K H)
    (A : cM J G) :
    (g : Finset K) → ({v : K // v ∈ g} → G) → ℝ := by
  classical
  intro g y
  by_cases hg : g ∈ B.edges
  · exact A (g.image B.projection)
      (B.ds hg y)
  · exact 1
@[simp]
theorem b4
    (B : ah J K H)
    (A : cM J G)
    {g : Finset K} (hg : g ∈ B.edges)
    (y : {v : K // v ∈ g} → G) :
    B.ao A g y =
      A (g.image B.projection)
        (B.ds hg y) := by
  classical
  simp [ao, hg]
theorem dR
    (B : ah J K H)
    (A : cM J G)
    (hA : eI H A)
    {g : Finset K} (hg : g ∈ B.edges)
    (y : {v : K // v ∈ g} → G) :
    0 ≤ B.ao A g y ∧
      B.ao A g y ≤ 1 := by
  rw [B.b4 A hg y]
  exact hA _ (B.c4 g hg) _
def gA
    (B : ah J K H)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ) : Prop :=
  ∀ g ∈ B.edges, ∀ y, 0 ≤ A g y ∧ A g y ≤ 1
theorem en
    (B : ah J K H)
    (A : cM J G)
    (hA : eI H A) :
    B.gA
      (B.ao A) := by
  intro g hg y
  exact B.dR A hA hg y
noncomputable def cy
    (B : ah J K H)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    (x : K → G) : ℝ :=
  ∏ g ∈ B.edges, A g (bo g x)
noncomputable def a7
    [Fintype K] [Fintype G]
    (B : ah J K H)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ) : ℝ :=
  mean (B.cy A)
theorem vj
    (B : ah J K H)
    {A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ}
    (hA : B.gA A)
    (x : K → G) :
    0 ≤ B.cy A x := by
  unfold cy
  exact Finset.prod_nonneg fun g hg =>
    (hA g hg (bo g x)).1
theorem mo
    [Fintype K] [Fintype G]
    (B : ah J K H)
    {A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ}
    (hA : B.gA A) :
    0 ≤ B.a7 A :=
  o9 (B.vj hA)
theorem gA.cK
    (B : ah J K H)
    {A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ}
    (hA : B.gA A)
    (g₀ : Finset K) :
    (B.cK g₀).gA A := by
  intro g hg y
  exact hA g (Finset.mem_of_mem_erase hg) y
noncomputable def d4
    (B : ah J K H)
    (g₀ : Finset K)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    (x : K → G) : ℝ :=
  (B.cK g₀).cy A x
noncomputable def bf
    [Fintype K] [Fintype G]
    (B : ah J K H)
    (g₀ : Finset K)
    (q : ({v : K // v ∈ g₀} → G) → ℝ)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ) : ℝ :=
  mean (fun x : K → G =>
    q (bo g₀ x) * B.d4 g₀ A x)
theorem lV
    [Fintype K] [Fintype G]
    (B : ah J K H)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges) :
    B.a7 A =
      B.bf g₀ (A g₀) A := by
  unfold a7 bf d4
  apply congrArg mean
  funext x
  exact
    (Finset.mul_prod_erase B.edges
      (fun g => A g (bo g x)) hg₀).symm
theorem tq
    [Fintype K] [Fintype G]
    (B : ah J K H)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    (p : ℝ)
    (b c : ({v : K // v ∈ g₀} → G) → ℝ)
    (yx : ∀ y, A g₀ y = p + b y + c y) :
    B.a7 A =
      p * (B.cK g₀).a7 A +
        B.bf g₀ b A +
        B.bf g₀ c A := by
  rw [B.lV A hg₀]
  unfold bf a7
  calc
    mean (fun x : K → G =>
        A g₀ (bo g₀ x) *
          B.d4 g₀ A x) =
        mean (fun x : K → G =>
          p * B.d4 g₀ A x +
            b (bo g₀ x) *
              B.d4 g₀ A x +
            c (bo g₀ x) *
              B.d4 g₀ A x) := by
      apply congrArg mean
      funext x
      rw [yx]
      ring
    _ =
        mean (fun x : K → G =>
          p * B.d4 g₀ A x) +
          mean (fun x : K → G =>
            b (bo g₀ x) *
              B.d4 g₀ A x) +
          mean (fun x : K → G =>
            c (bo g₀ x) *
              B.d4 g₀ A x) := by
      rw [tX, tX]
    _ =
        p * (B.cK g₀).a7 A +
          B.bf g₀ b A +
          B.bf g₀ c A := by
      rw [k0]
      rfl
theorem uE
    [Fintype K] [Fintype G]
    (B : ah J K H)
    (g₀ : Finset K)
    (p : ℝ)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ) :
    B.bf g₀ (fun _ => p) A =
      p * (B.cK g₀).a7 A := by
  unfold bf a7
  rw [← k0]
  rfl
abbrev bd (g : Finset K) :=
  {v : K // v ∉ g}
noncomputable def f6 (g : Finset K) :
    {v : K // v ∈ g} ⊕ bd g ≃ K :=
  Equiv.sumCompl fun v : K => v ∈ g
noncomputable def bF
    (g : Finset K) :
    (K → G) ≃
      (({v : K // v ∈ g} → G) ×
        (bd g → G)) :=
  (Equiv.piCongrLeft (fun _ : K => G)
      (f6 g)).symm.trans
    (Equiv.sumPiEquivProdPi
      (fun _ : {v : K // v ∈ g} ⊕
        bd g => G))
@[simp]
theorem wj
    (g : Finset K) (x : K → G) :
    (bF g x).1 = bo g x := by
  funext v
  simp [bF, f6, bo]
@[simp]
theorem fA
    (g : Finset K)
    (y : {v : K // v ∈ g} → G)
    (z : bd g → G) :
    bo g ((bF g).symm (y, z)) = y := by
  rw [← wj]
  simp
theorem sD
    [Fintype K] [Fintype G]
    (g : Finset K) (f : (K → G) → ℝ) :
    mean f =
      fq (fun y : {v : K // v ∈ g} → G =>
        fun z : bd g → G =>
          f ((bF g).symm (y, z))) := by
  calc
    mean f =
        mean (fun p :
          ({v : K // v ∈ g} → G) ×
            (bd g → G) =>
              f ((bF g).symm p)) := by
      unfold mean
      apply Fintype.expect_equiv (bF g)
      intro x
      simp
    _ = _ := by
      simpa only [Prod.eta] using
        (pZ
          (fun y : {v : K // v ∈ g} → G =>
            fun z : bd g → G =>
              f ((bF g).symm (y, z))))
noncomputable def d5
    (B : ah J K H)
    (g₀ : Finset K)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    (y : {v : K // v ∈ g₀} → G)
    (z : bd g₀ → G) : ℝ :=
  B.d4 g₀ A
    ((bF g₀).symm (y, z))
noncomputable def iN
    [Fintype K] [Fintype G]
    (B : ah J K H)
    (g₀ : Finset K)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    (y : {v : K // v ∈ g₀} → G) : ℝ :=
  mean (B.d5 g₀ A y)
theorem mq
    [Fintype K] [Fintype G]
    (B : ah J K H)
    (g₀ : Finset K)
    (q : ({v : K // v ∈ g₀} → G) → ℝ)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ) :
    B.bf g₀ q A =
      mean (fun y =>
        q y * B.iN g₀ A y) := by
  unfold bf
  rw [sD g₀]
  unfold fq iN d5
  apply congrArg mean
  funext y
  simp only [fA]
  rw [k0]
noncomputable def eW
    [Fintype G]
    (B : ah J K H)
    (g₀ : Finset K)
    (q : ({v : K // v ∈ g₀} → G) → ℝ)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    (z : bd g₀ → G) : ℝ :=
  mean (fun y =>
    q y * B.d5 g₀ A y z)
theorem l4
    [Fintype K] [Fintype G]
    (B : ah J K H)
    (g₀ : Finset K)
    (q : ({v : K // v ∈ g₀} → G) → ℝ)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ) :
    B.bf g₀ q A =
      mean (B.eW g₀ q A) := by
  unfold bf
  rw [sD g₀, zJ]
  unfold eW d5 fq
  apply congrArg mean
  funext z
  apply congrArg mean
  funext y
  change
    q (bo g₀
        ((bF g₀).symm (y, z))) *
        B.d4 g₀ A
          ((bF g₀).symm (y, z)) =
      q y *
        B.d4 g₀ A
          ((bF g₀).symm (y, z))
  rw [fA]
theorem qB
    [Fintype K] [Fintype G] [Nonempty G]
    (B : ah J K H)
    (g₀ : Finset K)
    (q : ({v : K // v ∈ g₀} → G) → ℝ)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    {ε : ℝ}
    (yy :
      ∀ z, |B.eW g₀ q A z| ≤ ε) :
    |B.bf g₀ q A| ≤ ε := by
  rw [B.l4]
  calc
    |mean (B.eW g₀ q A)| ≤
        mean (fun z =>
          |B.eW g₀ q A z|) :=
      Finset.abs_expect_le Finset.univ _
    _ ≤ mean (fun _z : bd g₀ → G => ε) :=
      mm yy
    _ = ε := ml _
noncomputable def dA
    [Fintype K] [Fintype G]
    (B : ah J K H)
    (g₀ : Finset K)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ) : ℝ :=
  mean (fun y =>
    B.iN g₀ A y ^ 2)
theorem r0
    [Fintype K] [Fintype G]
    (B : ah J K H)
    (g₀ : Finset K)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ) :
    0 ≤ B.dA g₀ A :=
  o9 fun _ => sq_nonneg _
theorem pa
    [Fintype K] [Fintype G]
    (B : ah J K H)
    (g₀ : Finset K)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ) :
    B.dA g₀ A =
      fq (fun y :
          {v : K // v ∈ g₀} → G =>
        fun z :
          (bd g₀ → G) ×
            (bd g₀ → G) =>
          B.d5 g₀ A y z.1 *
            B.d5 g₀ A y z.2) := by
  unfold dA iN
  exact rZ
    (B.d5 g₀ A)
theorem l5
    [Fintype K] [Fintype G]
    (B : ah J K H)
    (g₀ : Finset K)
    (q : ({v : K // v ∈ g₀} → G) → ℝ)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ) :
    B.bf g₀ q A ^ 2 ≤
      mean (fun y => q y ^ 2) *
        B.dA g₀ A := by
  rw [B.mq]
  exact uD q
    (B.iN g₀ A)
end ah
end av.ag
end
section
namespace av.ag
open scoped BigOperators
namespace ah
variable {J K G : Type*}
  [DecidableEq J] [DecidableEq K]
  {H : Finset (Finset J)}
abbrev bs (g₀ : Finset K) :=
  {v : K // v ∈ g₀} ⊕ (Bool × bd g₀)
def dw
    (g₀ : Finset K) :
    bs g₀ → K
  | Sum.inl v => v.1
  | Sum.inr v => v.2.1
def bH
    (g₀ : Finset K) (copy : Bool) (v : K) :
    bs g₀ :=
  if hv : v ∈ g₀ then
    Sum.inl ⟨v, hv⟩
  else
    Sum.inr ⟨copy, ⟨v, hv⟩⟩
@[simp]
theorem zK
    (g₀ : Finset K) (copy : Bool) (v : K) :
    dw g₀
        (bH g₀ copy v) = v := by
  by_cases hv : v ∈ g₀ <;>
    simp [bH, dw, hv]
theorem sY
    (g₀ : Finset K) (copy : Bool) :
    Function.Injective (bH g₀ copy) := by
  intro v w BS
  have h :=
    congrArg (dw g₀) BS
  simpa using h
def eH
    (g₀ : Finset K)
    (y : {v : K // v ∈ g₀} → G)
    (z : (bd g₀ → G) ×
      (bd g₀ → G)) :
    bs g₀ → G
  | Sum.inl v => y v
  | Sum.inr (false, v) => z.1 v
  | Sum.inr (true, v) => z.2 v
def ob
    (g₀ : Finset K) :
    (bs g₀ → G) ≃
      (({v : K // v ∈ g₀} → G) ×
        ((bd g₀ → G) ×
          (bd g₀ → G))) where
  toFun x :=
    (fun v => x (Sum.inl v),
      (fun v => x (Sum.inr (false, v)),
        fun v => x (Sum.inr (true, v))))
  invFun p := eH g₀ p.1 p.2
  left_inv x := by
    funext v
    rcases v with v | ⟨copy, v⟩
    · rfl
    · cases copy <;> rfl
  right_inv p := by
    rcases p with ⟨y, Ge, Hj⟩
    rfl
theorem sZ
    [Fintype K] [Fintype G]
    (g₀ : Finset K)
    (f : (bs g₀ → G) → ℝ) :
    mean f =
      fq (fun y : {v : K // v ∈ g₀} → G =>
        fun z :
          (bd g₀ → G) ×
            (bd g₀ → G) =>
          f (eH g₀ y z)) := by
  calc
    mean f =
        mean (fun p :
          ({v : K // v ∈ g₀} → G) ×
            ((bd g₀ → G) ×
              (bd g₀ → G)) =>
          f ((ob g₀).symm p)) := by
      unfold mean
      apply Fintype.expect_equiv
        (ob g₀)
      intro x
      simp
    _ = _ := by
      change
        mean (fun p :
          ({v : K // v ∈ g₀} → G) ×
            ((bd g₀ → G) ×
              (bd g₀ → G)) =>
          f (eH g₀ p.1 p.2)) =
        _
      exact
        pZ
          (fun y : {v : K // v ∈ g₀} → G =>
            fun z :
              (bd g₀ → G) ×
              (bd g₀ → G) =>
              f (eH g₀ y z))
@[simp]
theorem sE
    (g₀ : Finset K)
    (y : {v : K // v ∈ g₀} → G)
    (z : (bd g₀ → G) ×
      (bd g₀ → G))
    (v : K) :
    eH g₀ y z
        (bH g₀ false v) =
      (bF g₀).symm (y, z.1) v := by
  classical
  by_cases hv : v ∈ g₀
  · simp only [bH, dif_pos hv,
      eH]
    unfold bF
    convert
      (Equiv.piCongrLeft_sumInl
        (fun _ : K => G) (f6 g₀)
        y z.1 ⟨v, hv⟩).symm using 1 ;
      simp [f6]
  · simp only [bH, dif_neg hv,
      eH]
    unfold bF
    convert
      (Equiv.piCongrLeft_sumInr
        (fun _ : K => G) (f6 g₀)
        y z.1 ⟨v, hv⟩).symm using 1 ;
      simp [f6]
@[simp]
theorem s0
    (g₀ : Finset K)
    (y : {v : K // v ∈ g₀} → G)
    (z : (bd g₀ → G) ×
      (bd g₀ → G))
    (v : K) :
    eH g₀ y z
        (bH g₀ true v) =
      (bF g₀).symm (y, z.2) v := by
  classical
  by_cases hv : v ∈ g₀
  · simp only [bH, dif_pos hv,
      eH]
    unfold bF
    convert
      (Equiv.piCongrLeft_sumInl
        (fun _ : K => G) (f6 g₀)
        y z.2 ⟨v, hv⟩).symm using 1 ;
      simp [f6]
  · simp only [bH, dif_neg hv,
      eH]
    unfold bF
    convert
      (Equiv.piCongrLeft_sumInr
        (fun _ : K => G) (f6 g₀)
        y z.2 ⟨v, hv⟩).symm using 1 ;
      simp [f6]
def b5
    (g₀ : Finset K) (copy : Bool) (g : Finset K) :
    Finset (bs g₀) :=
  g.image (bH g₀ copy)
theorem pn
    (g₀ : Finset K) (copy : Bool)
    (g : Finset K) (v : K) (hv : v ∈ g) :
    bH g₀ copy v ∈
      b5 g₀ copy g :=
  Finset.mem_image.mpr ⟨v, hv, rfl⟩
@[simp]
theorem zL
    (g₀ : Finset K) (copy : Bool) (g : Finset K) :
    (b5 g₀ copy g).image
        (dw g₀) = g := by
  classical
  ext v
  constructor
  · intro hv
    obtain ⟨w, hw, vM⟩ := Finset.mem_image.mp hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
    have Gf : u = v := by
      simpa using vM
    exact Gf ▸ hu
  · intro hv
    exact
      Finset.mem_image.mpr
        ⟨bH g₀ copy v,
          pn g₀ copy g v hv, by simp⟩
@[simp]
theorem xm
    (g₀ : Finset K) (copy : Bool) (g : Finset K) :
    (b5 g₀ copy g).card = g.card := by
  rw [b5,
    Finset.card_image_of_injective _
      (sY g₀ copy)]
theorem jr
    (g₀ : Finset K) {g : Finset K}
    (hg : g ⊆ g₀) (copy copy' : Bool) :
    b5 g₀ copy g =
      b5 g₀ copy' g := by
  unfold b5
  apply Finset.image_congr
  intro v hv
  simp [bH, hg hv]
theorem nm
    (g₀ : Finset K) {g : Finset K}
    {v : K} (xZ : v ∈ g) (wk : v ∉ g₀) :
    b5 g₀ false g ≠
      b5 g₀ true g := by
  intro tZ
  have hv :
      bH g₀ false v ∈
        b5 g₀ true g := by
    rw [← tZ]
    exact pn g₀ false g v xZ
  obtain ⟨w, A0, vM⟩ :=
    Finset.mem_image.mp hv
  have Bf : w = v := by
    have := congrArg
      (dw g₀) vM
    simpa using this
  subst w
  simp [bH, wk] at vM
theorem pE
    (g₀ : Finset K) (g : Finset K) :
    b5 g₀ false g =
        b5 g₀ true g ↔
      g ⊆ g₀ := by
  constructor
  · intro tZ v xZ
    by_contra wk
    exact
      nm
        g₀ xZ wk tZ
  · intro hg
    exact jr
      g₀ hg false true
abbrev gh
    (B : ah J K H) (g₀ : Finset K) :=
  Bool × {g : Finset K // g ∈ (B.edges.erase g₀)}
def js
    (B : ah J K H) (g₀ : Finset K)
    (s : B.gh g₀) :
    Finset (bs g₀) :=
  b5 g₀ s.1 s.2.1
noncomputable def iP
    (B : ah J K H) (g₀ : Finset K)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    (x : bs g₀ → G) : ℝ :=
  ∏ s : B.gh g₀,
    A s.2.1 (fun v =>
      x (bH g₀ s.1 v.1))
theorem pb
    (B : ah J K H) (g₀ : Finset K)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    (y : {v : K // v ∈ g₀} → G)
    (z : (bd g₀ → G) ×
      (bd g₀ → G)) :
    B.iP g₀ A
        (eH g₀ y z) =
      B.d5 g₀ A y z.1 *
        B.d5 g₀ A y z.2 := by
  classical
  unfold iP
  rw [Fintype.prod_prod_type, Fintype.prod_bool]
  simp_rw [s0,
    sE]
  have zM :
      (∏ g : {g : Finset K //
          g ∈ B.edges.erase g₀},
        A g.1 (fun v =>
          (bF g₀).symm
            (y, z.1) v.1)) =
        ∏ g ∈ B.edges.erase g₀,
          A g (bo g
            ((bF g₀).symm
              (y, z.1))) := by
    calc
      _ = ∏ g : {g : Finset K //
            g ∈ B.edges.erase g₀},
          A g.1 (bo g.1
            ((bF g₀).symm
              (y, z.1))) := by
        apply Finset.prod_congr rfl
        intro g _hg
        apply congrArg (A g.1)
        rfl
      _ = _ :=
        Finset.prod_coe_sort
          (B.edges.erase g₀)
          (fun g => A g (bo g
            ((bF g₀).symm
              (y, z.1))))
  have E5 :
      (∏ g : {g : Finset K //
          g ∈ B.edges.erase g₀},
        A g.1 (fun v =>
          (bF g₀).symm
            (y, z.2) v.1)) =
        ∏ g ∈ B.edges.erase g₀,
          A g (bo g
            ((bF g₀).symm
              (y, z.2))) := by
    calc
      _ = ∏ g : {g : Finset K //
            g ∈ B.edges.erase g₀},
          A g.1 (bo g.1
            ((bF g₀).symm
              (y, z.2))) := by
        apply Finset.prod_congr rfl
        intro g _hg
        apply congrArg (A g.1)
        rfl
      _ = _ :=
        Finset.prod_coe_sort
          (B.edges.erase g₀)
          (fun g => A g (bo g
            ((bF g₀).symm
              (y, z.2))))
  rw [E5, zM]
  unfold d5 d4 cy
  rw [mul_comm]
  rfl
theorem kA
    [Fintype K] [Fintype G]
    (B : ah J K H) (g₀ : Finset K)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ) :
    B.dA g₀ A =
      mean (B.iP g₀ A) := by
  rw [B.pa]
  rw [sZ]
  simp_rw [B.pb]
def gG
    (B : ah J K H) (g₀ : Finset K) :
    Finset (Finset (bs g₀)) :=
  Finset.univ.image (B.js g₀)
theorem dV
    (B : ah J K H) (g₀ : Finset K)
    (d : Finset (bs g₀)) :
    d ∈ B.gG g₀ ↔
      ∃ (copy : Bool) (g : Finset K),
        g ∈ B.edges.erase g₀ ∧
          b5 g₀ copy g = d := by
  classical
  constructor
  · intro hd
    obtain ⟨s, _hs, Gg⟩ :=
      Finset.mem_image.mp hd
    exact ⟨s.1, s.2.1, s.2.2, Gg⟩
  · rintro ⟨copy, g, hg, rfl⟩
    exact
      Finset.mem_image.mpr
        ⟨(copy, ⟨g, hg⟩), Finset.mem_univ _, rfl⟩
def e6
    (B : ah J K H) (g₀ : Finset K) :
    bs g₀ → J :=
  fun v => B.projection (dw g₀ v)
@[simp]
theorem uF
    (B : ah J K H) (g₀ : Finset K)
    (copy : Bool) (v : K) :
    B.e6 g₀
        (bH g₀ copy v) =
      B.projection v := by
  simp [e6]
@[simp]
theorem kb
    (B : ah J K H) (g₀ : Finset K)
    (copy : Bool) (g : Finset K) :
    (b5 g₀ copy g).image
        (B.e6 g₀) =
      g.image B.projection := by
  classical
  ext j
  constructor
  · intro hj
    obtain ⟨v, hv, y0⟩ := Finset.mem_image.mp hj
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_image.mpr
      ⟨w, hw, by simpa using y0⟩
  · intro hj
    obtain ⟨v, hv, y0⟩ := Finset.mem_image.mp hj
    exact
      Finset.mem_image.mpr
        ⟨bH g₀ copy v,
          pn g₀ copy g v hv,
          by simpa using y0⟩
def aU
    (B : ah J K H) (g₀ : Finset K) :
    ah J (bs g₀) H where
  edges := B.gG g₀
  projection := B.e6 g₀
  cW := by
    intro d hd v hv w hw BS
    obtain ⟨copy, g, hg, rfl⟩ :=
      (B.dV g₀ d).1 hd
    obtain ⟨xo, E9, rfl⟩ :=
      Finset.mem_image.mp hv
    obtain ⟨w₀, uA, rfl⟩ :=
      Finset.mem_image.mp hw
    apply congrArg (bH g₀ copy)
    apply B.cW g
      (Finset.mem_of_mem_erase hg) E9 uA
    simpa using BS
  c4 := by
    intro d hd
    obtain ⟨copy, g, hg, rfl⟩ :=
      (B.dV g₀ d).1 hd
    rw [kb]
    exact B.c4 g
      (Finset.mem_of_mem_erase hg)
@[simp]
theorem uH
    (B : ah J K H) (g₀ : Finset K) :
    (B.aU g₀).edges =
      B.gG g₀ :=
  rfl
@[simp]
theorem oc
    (B : ah J K H) (g₀ : Finset K) :
    (B.aU g₀).projection =
      B.e6 g₀ :=
  rfl
theorem ts
    (B : ah J K H) (g₀ : Finset K)
    {d : Finset (bs g₀)}
    (hd : d ∈ (B.aU g₀).edges) :
    ∃ g ∈ B.edges.erase g₀, d.card = g.card := by
  obtain ⟨copy, g, hg, Dq⟩ :=
    (B.dV g₀ d).1 hd
  subst d
  exact ⟨g, hg, xm g₀ copy g⟩
theorem p0
    (B : ah J K H) (g₀ : Finset K) :
    (B.aU g₀).order ≤
      (B.cK g₀).order := by
  unfold order
  apply Finset.sup_le
  intro d hd
  obtain ⟨g, hg, Gh⟩ :=
    B.ts g₀ hd
  rw [Gh]
  exact (B.cK g₀).mn hg
theorem tM
    (B : ah J K H) (g₀ : Finset K) :
    (B.aU g₀).order ≤ B.order :=
  (B.p0 g₀).trans
    (B.sX g₀)
theorem vk
    (B : ah J K H) (g₀ : Finset K) :
    (B.gG g₀).card ≤
      2 * (B.edges.erase g₀).card := by
  unfold gG
  calc
    (Finset.univ.image
        (B.js g₀)).card ≤
        (Finset.univ :
          Finset (B.gh g₀)).card :=
      Finset.card_image_le
    _ = 2 * (B.edges.erase g₀).card := by
      simp [gh]
theorem ql
    (g₀ : Finset K) (copy : Bool)
    {g : Finset K}
    {d : Finset (bs g₀)}
    (hd : d ⊆ b5 g₀ copy g) :
    b5 g₀ copy
        (d.image (dw g₀)) = d := by
  classical
  ext v
  constructor
  · intro hv
    obtain ⟨w, hw, vM⟩ := Finset.mem_image.mp hv
    obtain ⟨u, hu, D9⟩ := Finset.mem_image.mp hw
    have Ea :
        bH g₀ copy
            (dw g₀ u) = u := by
      obtain ⟨t, ht, rfl⟩ :=
        Finset.mem_image.mp (hd hu)
      simp
    rw [← vM, ← D9, Ea]
    exact hu
  · intro hv
    have Eb :
        bH g₀ copy
            (dw g₀ v) = v := by
      obtain ⟨t, ht, rfl⟩ :=
        Finset.mem_image.mp (hd hv)
      simp
    exact Finset.mem_image.mpr
      ⟨dw g₀ v,
        Finset.mem_image.mpr ⟨v, hv, rfl⟩,
        Eb⟩
theorem qh
    (B : ah J K H) (g₀ : Finset K)
    (dv :
      (B.cK g₀).a6) :
    (B.aU g₀).a6 := by
  intro d hd f Fx
  obtain ⟨copy, g, hg, rfl⟩ :=
    (B.dV g₀ d).1 hd
  let h : Finset K :=
    f.image (dw g₀)
  have Dr : h ⊆ g := by
    intro v hv
    obtain ⟨w, hw, vM⟩ := Finset.mem_image.mp hv
    obtain ⟨u, hu, D9⟩ :=
      Finset.mem_image.mp (Fx hw)
    rw [← vM, ← D9]
    simpa using hu
  have hh : h ∈ B.edges.erase g₀ :=
    dv hg Dr
  have hlift :
      b5 g₀ copy h = f :=
    ql
      g₀ copy Fx
  rw [← hlift]
  exact
    (B.dV g₀
      (b5 g₀ copy h)).2
      ⟨copy, h, hh, rfl⟩
theorem qm
    (B : ah J K H)
    (dv : B.a6)
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    (d3 : ∀ g ∈ B.edges, g.card ≤ g₀.card) :
    (B.aU g₀).a6 :=
  B.qh g₀
    (B.oa
      dv hg₀ d3)
end ah
end av.ag
end
section
namespace av.ag
open scoped BigOperators
namespace ah
variable {J K G : Type*}
  [DecidableEq J] [DecidableEq K]
  {H : Finset (Finset J)}
def eX
    (H : Finset (Finset J))
    (A : cM J G) : Prop :=
  ∀ e ∈ H, ∀ y, A e y * A e y = A e y
def iD
    {α : Type*} {s t : Finset α} (h : s = t) :
    {a : α // a ∈ s} ≃ {a : α // a ∈ t} :=
  Equiv.cast
    (congrArg (fun u : Finset α => {a : α // a ∈ u}) h)
@[simp]
theorem kB
    {α : Type*} {s t : Finset α} (h : s = t)
    (a : {a : α // a ∈ t}) :
    ((iD h).symm a).1 = a.1 := by
  subst t
  rfl
theorem sw
    {α G' : Type*} {s t : Finset α} (h : s = t)
    (f : {a : α // a ∈ s} → G')
    (a : {a : α // a ∈ t}) :
    cast
        (congrArg
          (fun u : Finset α =>
            ({a : α // a ∈ u} → G'))
          h)
        f a =
      f ((iD h).symm a) := by
  subst t
  rfl
@[simp]
theorem kO
    (B : ah J K H)
    {g : Finset K} (hg : g ∈ B.edges)
    (v : {v : K // v ∈ g}) :
    ((B.cp hg) v).1 =
      B.projection v.1 := by
  rfl
theorem px
    {α β M : Type*} [DecidableEq β]
    [CommMonoid M]
    (s : Finset α) (f : α → β) (w : β → M)
    (hw : ∀ b ∈ s.image f, w b * w b = w b) :
    (∏ a ∈ s, w (f a)) =
      ∏ b ∈ s.image f, w b := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert a s ha ih =>
      have Gi :
          ∀ b ∈ s.image f, w b * w b = w b := by
        intro b hb
        exact hw b (by
          rw [Finset.image_insert]
          exact Finset.mem_insert_of_mem hb)
      rw [Finset.prod_insert ha, ih Gi,
        Finset.image_insert]
      by_cases Ds : f a ∈ s.image f
      · rw [Finset.insert_eq_of_mem Ds]
        calc
          w (f a) * ∏ b ∈ s.image f, w b =
              w (f a) *
                (w (f a) *
                  ∏ b ∈ (s.image f).erase (f a), w b) := by
            rw [Finset.mul_prod_erase (s.image f) w Ds]
          _ =
              w (f a) *
                ∏ b ∈ (s.image f).erase (f a), w b := by
            rw [← mul_assoc,
              hw (f a) (by
                rw [Finset.image_insert]
                exact Finset.mem_insert_self _ _)]
          _ = ∏ b ∈ s.image f, w b :=
            Finset.mul_prod_erase (s.image f) w Ds
      · rw [Finset.prod_insert Ds]
theorem kC
    (B : ah J K H) (g₀ : Finset K)
    (A : cM J G)
    (copy : Bool) {g : Finset K}
    (hg : g ∈ B.edges.erase g₀)
    (x : bs g₀ → G) :
    (B.aU g₀).ao A
        (b5 g₀ copy g)
        (bo (b5 g₀ copy g) x) =
      B.ao A g
        (fun v => x (bH g₀ copy v.1)) := by
  classical
  have iq : g ∈ B.edges :=
    Finset.mem_of_mem_erase hg
  have hd :
      b5 g₀ copy g ∈
        (B.aU g₀).edges := by
    exact
      (B.dV g₀
        (b5 g₀ copy g)).2
        ⟨copy, g, hg, rfl⟩
  rw [(B.aU g₀).b4
      A hd,
    B.b4 A iq]
  have fH :
      (b5 g₀ copy g).image
          (B.aU g₀).projection =
        g.image B.projection := by
    exact B.kb g₀ copy g
  let qY :
      (Σ e : Finset J,
        ({j : J // j ∈ e} → G)) :=
    ⟨(b5 g₀ copy g).image
        (B.aU g₀).projection,
      (B.aU g₀).ds hd
        (bo (b5 g₀ copy g) x)⟩
  let qZ :
      (Σ e : Finset J,
        ({j : J // j ∈ e} → G)) :=
    ⟨g.image B.projection,
      B.ds iq
        (fun v =>
          x (bH g₀ copy v.1))⟩
  change
    (fun p :
        (Σ e : Finset J,
          ({j : J // j ∈ e} → G)) =>
      A p.1 p.2) qY =
    (fun p :
        (Σ e : Finset J,
          ({j : J // j ∈ e} → G)) =>
      A p.1 p.2) qZ
  apply congrArg
    (fun p :
        (Σ e : Finset J,
          ({j : J // j ∈ e} → G)) =>
      A p.1 p.2)
  apply Sigma.ext fH
  apply heq_of_eqRec_eq
    (congrArg
      (fun e : Finset J =>
        ({j : J // j ∈ e} → G))
      fH)
  funext j
  change
    cast
        (congrArg
          (fun e : Finset J =>
            ({j : J // j ∈ e} → G))
          fH)
        qY.2 j =
      qZ.2 j
  rw [sw fH]
  let Bg :
      {j : J //
        j ∈ (b5 g₀ copy g).image
          (B.aU g₀).projection} :=
    (iD fH).symm j
  let v : {v : K // v ∈ g} :=
    (B.cp iq).symm j
  have Gj :
      (⟨B.projection v.1,
          Finset.mem_image.mpr ⟨v.1, v.2, rfl⟩⟩ :
        {j : J // j ∈ g.image B.projection}) = j := by
    exact
      (B.cp iq).apply_symm_apply j
  have BT :
      bH g₀ copy v.1 ∈
        b5 g₀ copy g :=
    pn g₀ copy g v.1 v.2
  have BU :
      ((B.aU g₀).cp hd).symm Bg =
        ⟨bH g₀ copy v.1, BT⟩ := by
    apply ((B.aU g₀).cp hd).injective
    rw [Equiv.apply_symm_apply]
    apply Subtype.ext
    calc
      Bg.1 = j.1 := by
        exact
          kB
            fH j
      _ = B.projection v.1 :=
        congrArg Subtype.val Gj.symm
      _ =
          (((B.aU g₀).cp hd)
            ⟨bH g₀ copy v.1,
              BT⟩).1 := by
        rw [kO,
          oc,
          uF]
  unfold qY qZ ds bo
  change
    x (((B.aU g₀).cp hd).symm
        Bg).1 =
      x (bH g₀ copy v.1)
  rw [BU]
noncomputable def fa
    (B : ah J K H) (g₀ : Finset K)
    (A : cM J G)
    (x : bs g₀ → G)
    (d : Finset (bs g₀)) : ℝ :=
  (B.aU g₀).ao A d
    (bo d x)
theorem nn
    (B : ah J K H) (g₀ : Finset K)
    (A : cM J G)
    (x : bs g₀ → G)
    (s : B.gh g₀) :
    B.fa g₀ A x
        (B.js g₀ s) =
      B.ao A s.2.1
        (fun v =>
          x (bH g₀ s.1 v.1)) := by
  exact
    B.kC
      g₀ A s.1 s.2.2 x
theorem qn
    (B : ah J K H) (g₀ : Finset K)
    (A : cM J G)
    (hA : eX H A)
    (x : bs g₀ → G)
    (d : Finset (bs g₀))
    (hd : d ∈ B.gG g₀) :
    B.fa g₀ A x d *
        B.fa g₀ A x d =
      B.fa g₀ A x d := by
  classical
  unfold fa
  rw [(B.aU g₀).b4
      A hd]
  exact hA _ ((B.aU g₀).c4 d hd) _
theorem ir
    (B : ah J K H) (g₀ : Finset K)
    (A : cM J G)
    (hA : eX H A)
    (x : bs g₀ → G) :
    B.iP g₀
        (B.ao A) x =
      (B.aU g₀).cy
        ((B.aU g₀).ao A) x := by
  classical
  unfold iP
  calc
    (∏ s : B.gh g₀,
        B.ao A s.2.1
          (fun v =>
            x (bH g₀ s.1 v.1))) =
        ∏ s : B.gh g₀,
          B.fa g₀ A x
            (B.js g₀ s) := by
      apply Finset.prod_congr rfl
      intro s _hs
      exact
        (B.nn
          g₀ A x s).symm
    _ =
        ∏ d ∈
            (Finset.univ :
              Finset (B.gh g₀)).image
                (B.js g₀),
          B.fa g₀ A x d := by
      apply px
      intro d hd
      apply B.qn
        g₀ A hA x d
      simpa [gG] using hd
    _ =
        (B.aU g₀).cy
          ((B.aU g₀).ao A) x := by
      rfl
theorem iu
    [Fintype K] [Fintype G]
    (B : ah J K H)
    (dv : B.a6)
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    (d3 : ∀ g ∈ B.edges, g.card ≤ g₀.card)
    (A : cM J G)
    (hA : eX H A) :
    B.dA g₀
        (B.ao A) =
      (B.aU g₀).a7
        ((B.aU g₀).ao A) := by
  have _hduplicateClosed :
      (B.aU g₀).a6 :=
    B.qm
      dv hg₀ d3
  rw [B.kA]
  unfold a7
  apply congrArg mean
  funext x
  exact
    B.ir
      g₀ A hA x
end ah
end av.ag
end
section
namespace av.ag
open scoped BigOperators
namespace ah
variable {J K : Type*}
  [DecidableEq J] [DecidableEq K]
  {H : Finset (Finset J)}
def iJ
    (B : ah J K H)
    (P : Finset K → Prop) [DecidablePred P] :
    ah J K H where
  edges := B.edges.filter P
  projection := B.projection
  cW := by
    intro g hg
    exact B.cW g
      (Finset.mem_filter.mp hg).1
  c4 := by
    intro g hg
    exact B.c4 g
      (Finset.mem_filter.mp hg).1
@[simp]
theorem rj
    (B : ah J K H)
    (P : Finset K → Prop) [DecidablePred P]
    (g : Finset K) :
    g ∈ (B.iJ P).edges ↔
      g ∈ B.edges ∧ P g := by
  simp [iJ]
theorem po
    (B : ah J K H)
    (P : Finset K → Prop) [DecidablePred P] :
    (B.iJ P).edges.card ≤ B.edges.card := by
  exact Finset.card_le_card (Finset.filter_subset _ _)
theorem s3
    (B : ah J K H)
    (P : Finset K → Prop) [DecidablePred P]
    (dv : B.a6)
    (hP : ∀ ⦃g⦄, P g →
      ∀ ⦃f⦄, f ⊆ g → P f) :
    (B.iJ P).a6 := by
  intro g hg f ri
  have hg' := (B.rj P g).1 hg
  exact (B.rj P f).2
    ⟨dv hg'.1 ri, hP hg'.2 ri⟩
def bu
    (B : ah J K H) (d : ℕ) :
    ah J K H :=
  B.iJ fun g => g.card < d
@[simp]
theorem t3
    (B : ah J K H) (d : ℕ) :
    (B.bu d).edges =
      B.edges.filter fun g => g.card < d :=
  rfl
@[simp]
theorem rC
    (B : ah J K H)
    (d : ℕ) (g : Finset K) :
    g ∈ (B.bu d).edges ↔
      g ∈ B.edges ∧ g.card < d := by
  simp [bu]
theorem vV
    (B : ah J K H)
    {d : ℕ} (hd : 0 < d) :
    (B.bu d).order < d := by
  unfold order
  rw [Finset.sup_lt_iff hd]
  intro g hg
  exact (Finset.mem_filter.mp hg).2
theorem t4
    (B : ah J K H) (d : ℕ) :
    (B.bu d).edges.card ≤ B.edges.card :=
  B.po _
theorem wZ
    (B : ah J K H)
    (dv : B.a6)
    (d : ℕ) :
    (B.bu d).a6 := by
  apply B.s3 _ dv
  intro g hg f ri
  exact (Finset.card_le_card ri).trans_lt hg
def a8
    (B : ah J K H) (g₀ : Finset K) :
    ah J K H :=
  B.iJ fun g => g ⊂ g₀
@[simp]
theorem vl
    (B : ah J K H) (g₀ : Finset K) :
    (B.a8 g₀).edges =
      B.edges.filter fun g => g ⊂ g₀ :=
  rfl
@[simp]
theorem c7
    (B : ah J K H)
    (g₀ g : Finset K) :
    g ∈ (B.a8 g₀).edges ↔
      g ∈ B.edges ∧ g ⊂ g₀ := by
  simp [a8]
theorem uu
    (B : ah J K H)
    {g₀ : Finset K} (hg₀ : g₀.Nonempty) :
    (B.a8 g₀).order < g₀.card := by
  unfold order
  rw [Finset.sup_lt_iff (Finset.card_pos.mpr hg₀)]
  intro g hg
  exact Finset.card_lt_card (Finset.mem_filter.mp hg).2
theorem sF
    (B : ah J K H) (g₀ : Finset K) :
    (B.a8 g₀).edges.card ≤ B.edges.card :=
  B.po _
theorem u1
    (B : ah J K H)
    (dv : B.a6)
    (g₀ : Finset K) :
    (B.a8 g₀).a6 := by
  apply B.s3 _ dv
  intro g hg f ri
  exact lt_of_le_of_lt ri hg
noncomputable def a0
    (B : ah J K H)
    (p : Finset J → ℝ) : ℝ :=
  ∏ g ∈ B.edges, p (g.image B.projection)
theorem lW
    (B : ah J K H)
    (p : Finset J → ℝ)
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges) :
    (B.cK g₀).a0 p *
        p (g₀.image B.projection) =
      B.a0 p := by
  classical
  unfold a0
  simp only [cK]
  rw [Finset.prod_erase_mul _ _ hg₀]
theorem u2
    (g₀ : Finset K) (copy : Bool) :
    Function.Injective (b5 g₀ copy) := by
  intro g h Fy
  have fH :=
    congrArg
      (Finset.image (dw g₀)) Fy
  simpa using fH
theorem s4
    (B : ah J K H) (g₀ : Finset K) :
    B.gG g₀ =
      (B.edges.erase g₀).image
          (b5 g₀ false) ∪
        (B.edges.erase g₀).image
          (b5 g₀ true) := by
  classical
  ext d
  constructor
  · intro hd
    obtain ⟨copy, g, hg, rfl⟩ :=
      (B.dV g₀ d).1 hd
    cases copy
    · exact Finset.mem_union_left _
        (Finset.mem_image.mpr ⟨g, hg, rfl⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨g, hg, rfl⟩)
  · intro hd
    rcases Finset.mem_union.mp hd with hd | hd
    · obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hd
      exact (B.dV g₀ _).2
        ⟨false, g, hg, rfl⟩
    · obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hd
      exact (B.dV g₀ _).2
        ⟨true, g, hg, rfl⟩
theorem sG
    (g₀ : Finset K) (s : Finset (Finset K)) :
    s.image (b5 g₀ true) \
        s.image (b5 g₀ false) =
      (s.filter fun g => ¬ g ⊆ g₀).image
        (b5 g₀ true) := by
  classical
  ext d
  constructor
  · intro hd
    have Ec :
        d ∈ s.image (b5 g₀ true) :=
      (Finset.mem_sdiff.mp hd).1
    obtain ⟨g, hg, Dq⟩ :=
      Finset.mem_image.mp Ec
    subst d
    apply Finset.mem_image.mpr
    refine ⟨g, Finset.mem_filter.mpr ⟨hg, ?_⟩, rfl⟩
    intro rD
    apply (Finset.mem_sdiff.mp hd).2
    apply Finset.mem_image.mpr
    refine ⟨g, hg, ?_⟩
    exact
      (jr
        g₀ rD false true)
  · intro hd
    obtain ⟨g, hg, Dq⟩ :=
      Finset.mem_image.mp hd
    subst d
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_image.mpr
      ⟨g, (Finset.mem_filter.mp hg).1, rfl⟩, ?_⟩
    intro zM
    obtain ⟨h, hh, Dr⟩ :=
      Finset.mem_image.mp zM
    have Fy : h = g := by
      have fH :=
        congrArg
          (Finset.image (dw g₀)) Dr
      simpa using fH
    subst h
    exact (Finset.mem_filter.mp hg).2
      ((pE
        g₀ g).1 Dr)
theorem od
    (B : ah J K H)
    (g₀ : Finset K) (copy : Bool)
    (s : Finset (Finset K))
    (p : Finset J → ℝ) :
    (∏ d ∈ s.image (b5 g₀ copy),
        p (d.image (B.e6 g₀))) =
      ∏ g ∈ s, p (g.image B.projection) := by
  classical
  rw [Finset.prod_image
    (u2 g₀ copy).injOn]
  simp
theorem qo
    (B : ah J K H)
    (g₀ : Finset K) (p : Finset J → ℝ) :
    (B.aU g₀).a0 p =
      (∏ g ∈ (B.edges.erase g₀).filter
          (fun g => g ⊆ g₀),
        p (g.image B.projection)) *
      ∏ g ∈ (B.edges.erase g₀).filter
          (fun g => ¬ g ⊆ g₀),
        (p (g.image B.projection)) ^ 2 := by
  classical
  let s := B.edges.erase g₀
  let first :=
    s.image (b5 g₀ false)
  let second :=
    s.image (b5 g₀ true)
  have s5 :
      (∏ g ∈ s.filter (fun g => g ⊆ g₀),
          p (g.image B.projection)) *
          (∏ g ∈ s.filter (fun g => ¬ g ⊆ g₀),
            p (g.image B.projection)) =
        ∏ g ∈ s, p (g.image B.projection) :=
    Finset.prod_filter_mul_prod_filter_not
      s (fun g => g ⊆ g₀)
        (fun g => p (g.image B.projection))
  calc
    (B.aU g₀).a0 p =
        ∏ d ∈ first ∪ second,
          p (d.image (B.e6 g₀)) := by
      unfold a0 first second
      simp only [uH,
        oc]
      rw [B.s4 g₀]
    _ = ∏ d ∈ first ∪ (second \ first),
          p (d.image (B.e6 g₀)) := by
      rw [Finset.union_sdiff_self_eq_union]
    _ =
        (∏ d ∈ first,
          p (d.image (B.e6 g₀))) *
        ∏ d ∈ second \ first,
          p (d.image (B.e6 g₀)) := by
      exact Finset.prod_union Finset.disjoint_sdiff
    _ =
        (∏ g ∈ s, p (g.image B.projection)) *
        ∏ g ∈ s.filter (fun g => ¬ g ⊆ g₀),
          p (g.image B.projection) := by
      unfold first second
      rw [sG]
      rw [B.od g₀ false]
      rw [B.od g₀ true]
    _ =
        ((∏ g ∈ s.filter (fun g => g ⊆ g₀),
            p (g.image B.projection)) *
          ∏ g ∈ s.filter (fun g => ¬ g ⊆ g₀),
            p (g.image B.projection)) *
        ∏ g ∈ s.filter (fun g => ¬ g ⊆ g₀),
          p (g.image B.projection) := by
      rw [s5]
    _ =
        (∏ g ∈ s.filter (fun g => g ⊆ g₀),
            p (g.image B.projection)) *
          ∏ g ∈ s.filter (fun g => ¬ g ⊆ g₀),
            (p (g.image B.projection)) ^ 2 := by
      rw [mul_assoc, ← Finset.prod_mul_distrib]
      simp only [pow_two]
    _ = _ := rfl
theorem mr
    (B : ah J K H)
    (g₀ : Finset K) (p : Finset J → ℝ) :
    ((B.bu g₀.card).aU g₀).a0 p =
      (B.a8 g₀).a0 p *
      ∏ g ∈ B.edges.filter
          (fun g => g.card < g₀.card ∧ ¬ g ⊆ g₀),
        (p (g.image B.projection)) ^ 2 := by
  classical
  rw [(B.bu g₀.card).qo g₀ p]
  have Ed :
      g₀ ∉ B.edges.filter (fun g => g.card < g₀.card) := by
    simp
  have rk :
      (B.edges.filter (fun g => g.card < g₀.card)).filter
          (fun g => g ⊆ g₀) =
        B.edges.filter (fun g => g ⊂ g₀) := by
    ext g
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨iq, oP⟩, rD⟩
      exact ⟨iq,
        Finset.ssubset_iff_subset_ne.mpr
          ⟨rD, fun CM => by
            subst g
            exact (Nat.lt_irrefl _ oP)⟩⟩
    · rintro ⟨iq, ot⟩
      exact ⟨⟨iq,
        Finset.card_lt_card ot⟩, ot.1⟩
  have wm :
      (B.edges.filter (fun g => g.card < g₀.card)).filter
          (fun g => ¬ g ⊆ g₀) =
        B.edges.filter
          (fun g => g.card < g₀.card ∧ ¬ g ⊆ g₀) := by
    ext g
    simp only [Finset.mem_filter]
    tauto
  simp only [bu, a8,
    iJ, a0]
  rw [Finset.erase_eq_of_notMem Ed,
    rk, wm]
end ah
end av.ag
end
section
namespace av.ag
open scoped BigOperators
namespace ah
variable {J K G : Type*}
  [DecidableEq J] [DecidableEq K]
  {H : Finset (Finset J)}
def qr
    {f g : Finset K} (ri : f ⊆ g)
    (y : {v : K // v ∈ g} → G) :
    {v : K // v ∈ f} → G :=
  fun v => y ⟨v.1, ri v.2⟩
omit [DecidableEq K] in
@[simp]
theorem s6
    {f g : Finset K} (ri : f ⊆ g)
    (x : K → G) :
    qr ri (bo g x) =
      bo f x := by
  rfl
noncomputable def cT
    (B : ah J K H) (g₀ : Finset K)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    (y : {v : K // v ∈ g₀} → G) : ℝ :=
  ∏ g :
      {g : Finset K //
        g ∈ (B.a8 g₀).edges},
    A g.1
      (qr
        (((B.c7 g₀ g.1).1
          g.2).2.1)
        y)
theorem gH
    (B : ah J K H) (g₀ : Finset K)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    (x : K → G) :
    B.cT g₀ A
        (bo g₀ x) =
      (B.a8 g₀).cy A x := by
  classical
  unfold cT
  calc
    (∏ g :
        {g : Finset K //
          g ∈ (B.a8 g₀).edges},
      A g.1
        (qr
          (((B.c7 g₀ g.1).1
            g.2).2.1)
          (bo g₀ x))) =
        ∏ g :
          {g : Finset K //
            g ∈ (B.a8 g₀).edges},
          A g.1 (bo g.1 x) := by
      apply Finset.prod_congr rfl
      intro g _hg
      apply congrArg (A g.1)
      exact s6 _ x
    _ =
        ∏ g ∈ (B.a8 g₀).edges,
          A g (bo g x) :=
      Finset.prod_coe_sort
        (B.a8 g₀).edges
        (fun g => A g (bo g x))
    _ = (B.a8 g₀).cy A x := by
      rfl
theorem k1
    (B : ah J K H) (g₀ : Finset K) :
    (B.a8 g₀).edges ⊆
      B.edges.erase g₀ := by
  intro g hg
  have hg' :=
    (B.c7 g₀ g).1 hg
  exact Finset.mem_erase.mpr
    ⟨hg'.2.ne, hg'.1⟩
def nB
    (B : ah J K H)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ) : Prop :=
  ∀ g ∈ B.edges, ∀ y,
    A g y * A g y = A g y
theorem ou
    (B : ah J K H)
    (A : cM J G)
    (hA : eX H A) :
    B.nB
      (B.ao A) := by
  intro g hg y
  rw [B.b4 A hg y]
  exact hA _ (B.c4 g hg) _
theorem l6
    {ι : Type*}
    (s t : Finset ι) (f : ι → ℝ)
    (Fz : s ⊆ t)
    (hf : ∀ i ∈ s, f i * f i = f i) :
    (∏ i ∈ s, f i) * (∏ i ∈ t, f i) =
      ∏ i ∈ t, f i := by
  classical
  induction s using Finset.induction_on generalizing t with
  | empty =>
      simp
  | @insert a s ha ih =>
      have Gk : a ∈ t :=
        Fz (Finset.mem_insert_self a s)
      have FL : s ⊆ t.erase a := by
        intro i hi
        exact Finset.mem_erase.mpr
          ⟨fun Gl => ha (Gl ▸ hi),
            Fz (Finset.mem_insert_of_mem hi)⟩
      have hf' :
          ∀ i ∈ s, f i * f i = f i := by
        intro i hi
        exact hf i (Finset.mem_insert_of_mem hi)
      rw [Finset.prod_insert ha]
      rw [← Finset.mul_prod_erase t f Gk]
      calc
        (f a * ∏ i ∈ s, f i) *
              (f a * ∏ i ∈ t.erase a, f i) =
            (f a * f a) *
              ((∏ i ∈ s, f i) *
                ∏ i ∈ t.erase a, f i) := by
          ring
        _ =
            f a *
              ((∏ i ∈ s, f i) *
                ∏ i ∈ t.erase a, f i) := by
          rw [hf a (Finset.mem_insert_self a s)]
        _ = f a * ∏ i ∈ t.erase a, f i := by
          rw [ih (t.erase a) FL hf']
theorem mX
    (B : ah J K H) (g₀ : Finset K)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    (hA : B.nB A)
    (x : K → G) :
    B.cT g₀ A
          (bo g₀ x) *
        B.d4 g₀ A x =
      B.d4 g₀ A x := by
  rw [B.gH]
  unfold d4 cy
  apply l6
    (B.a8 g₀).edges
    (B.edges.erase g₀)
    (fun g => A g (bo g x))
    (B.k1 g₀)
  intro g hg
  exact hA g
    (Finset.mem_of_mem_erase
      (B.k1 g₀ hg))
    (bo g x)
theorem lN
    [Fintype K] [Fintype G]
    (B : ah J K H) (g₀ : Finset K)
    (q : ({v : K // v ∈ g₀} → G) → ℝ)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    (hA : B.nB A) :
    B.bf g₀ q A =
      B.bf g₀
        (fun y =>
          q y *
            B.cT g₀ A y)
        A := by
  unfold bf
  apply congrArg mean
  funext x
  rw [mul_assoc,
    B.mX
      g₀ A hA x]
noncomputable def lq
    (B : ah J K H) (g₀ : Finset K)
    (p : Finset J → ℝ) : ℝ :=
  ∏ g ∈ B.edges.filter
      (fun g =>
        g.card < g₀.card ∧ ¬ g ⊆ g₀),
    p (g.image B.projection)
noncomputable def c3
    (B : ah J K H) (g₀ : Finset K)
    (p : Finset J → ℝ) : ℝ :=
  ∏ g ∈ (B.edges.erase g₀).filter
      (fun g => ¬ g.card < g₀.card),
    p (g.image B.projection)
theorem kc
    (B : ah J K H)
    {g : Finset K} (hg : g ∈ B.edges) :
    (g.image B.projection).card = g.card := by
  have fE :=
    Fintype.card_congr (B.cp hg)
  simpa using fE.symm
theorem es
    (B : ah J K H)
    (p : Finset J → ℝ)
    (hp : ∀ e ∈ H, 0 ≤ p e) :
    0 ≤ B.a0 p := by
  unfold a0
  exact Finset.prod_nonneg fun g hg =>
    hp _ (B.c4 g hg)
theorem j7
    (B : ah J K H) (g₀ : Finset K)
    (p : Finset J → ℝ) :
    (B.bu g₀.card).a0 p =
      (B.a8 g₀).a0 p *
        B.lq g₀ p := by
  classical
  let s :=
    B.edges.filter
      (fun g => g.card < g₀.card)
  have rk :
      s.filter (fun g => g ⊆ g₀) =
        B.edges.filter (fun g => g ⊂ g₀) := by
    ext g
    simp only [s, Finset.mem_filter]
    constructor
    · rintro ⟨⟨iq, oP⟩, rD⟩
      exact ⟨iq,
        Finset.ssubset_iff_subset_ne.mpr
          ⟨rD, fun CM => by
            subst g
            exact (Nat.lt_irrefl _ oP)⟩⟩
    · rintro ⟨iq, ot⟩
      exact ⟨⟨iq, Finset.card_lt_card ot⟩,
        ot.1⟩
  have wm :
      s.filter (fun g => ¬ g ⊆ g₀) =
        B.edges.filter
          (fun g =>
            g.card < g₀.card ∧ ¬ g ⊆ g₀) := by
    ext g
    simp only [s, Finset.mem_filter]
    tauto
  have s5 :=
    Finset.prod_filter_mul_prod_filter_not
      s (fun g => g ⊆ g₀)
        (fun g => p (g.image B.projection))
  unfold a0 lq
  simp only [t3, vl]
  rw [← rk, ← wm]
  exact s5.symm
theorem ld
    (B : ah J K H) (g₀ : Finset K)
    (p : Finset J → ℝ) :
    (B.a8 g₀).a0 p *
        ((B.bu g₀.card).aU g₀).a0 p =
      ((B.bu g₀.card).a0 p) ^ 2 := by
  rw [B.mr
    g₀ p]
  rw [Finset.prod_pow]
  rw [B.j7
    g₀ p]
  unfold lq
  ring
theorem mv
    (B : ah J K H) (g₀ : Finset K)
    (p : Finset J → ℝ) :
    (B.bu g₀.card).a0 p *
        B.c3 g₀ p =
      (B.cK g₀).a0 p := by
  classical
  have rE :
      (B.edges.erase g₀).filter
          (fun g => g.card < g₀.card) =
        B.edges.filter
          (fun g => g.card < g₀.card) := by
    ext g
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨⟨_hne, iq⟩, oP⟩
      exact ⟨iq, oP⟩
    · rintro ⟨iq, oP⟩
      exact ⟨⟨fun zN => by
        subst g
        exact Nat.lt_irrefl _ oP, iq⟩,
        oP⟩
  have s5 :=
    Finset.prod_filter_mul_prod_filter_not
      (B.edges.erase g₀)
      (fun g => g.card < g₀.card)
      (fun g => p (g.image B.projection))
  unfold a0 c3
  simp only [t3, xY]
  rw [← rE]
  exact s5
theorem ov
    (B : ah J K H)
    {g₀ g : Finset K}
    (d3 : ∀ f ∈ B.edges, f.card ≤ g₀.card)
    (hg :
      g ∈ (B.edges.erase g₀).filter
        (fun f => ¬ f.card < g₀.card)) :
    g.card = g₀.card := by
  have hg' := Finset.mem_filter.mp hg
  exact Nat.le_antisymm
    (d3 g (Finset.mem_of_mem_erase hg'.1))
    (Nat.le_of_not_gt hg'.2)
theorem rF
    (B : ah J K H) (g₀ : Finset K) :
    ((B.edges.erase g₀).filter
      (fun g => ¬ g.card < g₀.card)).card ≤
        (B.edges.erase g₀).card :=
  Finset.card_le_card (Finset.filter_subset _ _)
theorem sH
    (B : ah J K H)
    {g₀ : Finset K}
    (d3 : ∀ g ∈ B.edges, g.card ≤ g₀.card)
    (p : Finset J → ℝ) {a : ℝ}
    (ha : 0 ≤ a)
    (hp :
      ∀ e ∈ H, e.card = g₀.card →
        a ≤ p e) :
    a ^
          ((B.edges.erase g₀).filter
            (fun g => ¬ g.card < g₀.card)).card ≤
      B.c3 g₀ p := by
  classical
  unfold c3
  calc
    a ^
          ((B.edges.erase g₀).filter
            (fun g => ¬ g.card < g₀.card)).card =
        ∏ _g ∈
            (B.edges.erase g₀).filter
              (fun g => ¬ g.card < g₀.card),
          a := by
      simp
    _ ≤
        ∏ g ∈
            (B.edges.erase g₀).filter
              (fun g => ¬ g.card < g₀.card),
          p (g.image B.projection) := by
      apply Finset.prod_le_prod
      · intro g hg
        exact ha
      · intro g hg
        apply hp _ (B.c4 g
          (Finset.mem_of_mem_erase
            (Finset.mem_filter.mp hg).1))
        rw [B.kc
          (Finset.mem_of_mem_erase
            (Finset.mem_filter.mp hg).1)]
        exact B.ov
          d3 hg
theorem iv
    (B C : ah J K H)
    (A : cM J G)
    (iK : B.projection = C.projection)
    {g : Finset K}
    (iq : g ∈ B.edges) (Dt : g ∈ C.edges)
    (y : {v : K // v ∈ g} → G) :
    B.ao A g y =
      C.ao A g y := by
  classical
  rw [B.b4 A iq y,
    C.b4 A Dt y]
  have fH :
      g.image B.projection = g.image C.projection :=
    congrArg (fun q : K → J => g.image q) iK
  let qY :
      (Σ e : Finset J,
        ({j : J // j ∈ e} → G)) :=
    ⟨g.image B.projection,
      B.ds iq y⟩
  let qZ :
      (Σ e : Finset J,
        ({j : J // j ∈ e} → G)) :=
    ⟨g.image C.projection,
      C.ds Dt y⟩
  change
    (fun p :
        (Σ e : Finset J,
          ({j : J // j ∈ e} → G)) =>
      A p.1 p.2) qY =
    (fun p :
        (Σ e : Finset J,
          ({j : J // j ∈ e} → G)) =>
      A p.1 p.2) qZ
  apply congrArg
    (fun p :
        (Σ e : Finset J,
          ({j : J // j ∈ e} → G)) =>
      A p.1 p.2)
  apply Sigma.ext fH
  apply heq_of_eqRec_eq
    (congrArg
      (fun e : Finset J =>
        ({j : J // j ∈ e} → G))
      fH)
  funext j
  change
    cast
        (congrArg
          (fun e : Finset J =>
            ({j : J // j ∈ e} → G))
          fH)
        qY.2 j =
      qZ.2 j
  rw [sw fH]
  let jB :
      {j : J // j ∈ g.image B.projection} :=
    (iD fH).symm j
  let vB := (B.cp iq).symm jB
  let vC := (C.cp Dt).symm j
  have Gm : jB.1 = j.1 :=
    kB fH j
  have Gn :
      B.projection vB.1 = jB.1 := by
    exact congrArg Subtype.val
      ((B.cp iq).apply_symm_apply jB)
  have FM :
      C.projection vC.1 = j.1 := by
    exact congrArg Subtype.val
      ((C.cp Dt).apply_symm_apply j)
  have Go :
      B.projection vC.1 = j.1 := by
    rw [iK]
    exact FM
  have xq : vB.1 = vC.1 :=
    B.cW g iq
      vB.2 vC.2
      ((Gn.trans Gm).trans Go.symm)
  unfold qY qZ ds
  change y vB = y vC
  exact congrArg y (Subtype.ext xq)
theorem rG
    (B : ah J K H) (g₀ : Finset K) :
    (B.bu g₀.card).gG g₀ ⊆
      B.gG g₀ := by
  intro d hd
  obtain ⟨copy, g, hg, Dq⟩ :=
    ((B.bu g₀.card).dV
      g₀ d).1 hd
  apply (B.dV g₀ d).2
  refine ⟨copy, g, ?_, Dq⟩
  have wT :
      g ∈ (B.bu g₀.card).edges :=
    Finset.mem_of_mem_erase hg
  exact Finset.mem_erase.mpr
    ⟨(Finset.mem_erase.mp hg).1,
      ((B.rC g₀.card g).1
        wT).1⟩
theorem mY
    (B : ah J K H) (g₀ : Finset K)
    (A : cM J G)
    (hA : eI H A)
    (x : bs g₀ → G) :
    (B.aU g₀).cy
          ((B.aU g₀).ao A) x ≤
      ((B.bu g₀.card).aU g₀).cy
          (((B.bu g₀.card).aU g₀).ao A) x := by
  classical
  let C := B.aU g₀
  let D := (B.bu g₀.card).aU g₀
  have FA : D.edges ⊆ C.edges := by
    simpa [C, D] using
      B.rG g₀
  have iK : C.projection = D.projection := by
    rfl
  unfold cy
  calc
    (∏ d ∈ C.edges,
        C.ao A
          d (bo d x)) ≤
        ∏ d ∈ D.edges,
          C.ao A
            d (bo d x) := by
      apply Finset.prod_le_prod_of_subset_of_le_one
        FA
      · intro d hd
        exact
          (C.dR
            A hA hd (bo d x)).1
      · intro d hd _hdD
        exact
          (C.dR
            A hA hd (bo d x)).2
    _ =
        ∏ d ∈ D.edges,
          D.ao A
            d (bo d x) := by
      apply Finset.prod_congr rfl
      intro d hd
      exact C.iv
        D A iK (FA hd) hd (bo d x)
theorem mw
    [Fintype K] [Fintype G]
    (B : ah J K H)
    (dv : B.a6)
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    (d3 : ∀ g ∈ B.edges, g.card ≤ g₀.card)
    (A : cM J G)
    (wq : eI H A)
    (t5 : eX H A) :
    B.dA g₀
          (B.ao A) ≤
      ((B.bu g₀.card).aU g₀).a7
          (((B.bu g₀.card).aU g₀).ao A) := by
  rw [B.iu
    dv hg₀ d3 A t5]
  unfold a7
  apply mm
  intro x
  exact B.mY
    g₀ A wq x
theorem iH
    [Fintype K] [Fintype G] [Nonempty G]
    (B : ah J K H)
    (dv : B.a6)
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    (d3 : ∀ g ∈ B.edges, g.card ≤ g₀.card)
    (A : cM J G)
    (wq : eI H A)
    (t5 : eX H A)
    (q : ({v : K // v ∈ g₀} → G) → ℝ)
    {β : ℝ} (gr : 0 ≤ β)
    (vm :
      mean (fun y => q y ^ 2) ≤
        β *
          (B.a8 g₀).a7
            ((B.a8 g₀).ao A)) :
    |B.bf g₀ q
        (B.ao A)| ≤
      Real.sqrt
        ((β *
            (B.a8 g₀).a7
              ((B.a8 g₀).ao A)) *
          ((B.bu g₀.card).aU g₀).a7
              (((B.bu g₀.card).aU g₀).ao A)) := by
  let oQ :=
    (B.a8 g₀).a7
      ((B.a8 g₀).ao A)
  let kD :=
    ((B.bu g₀.card).aU g₀).a7
        (((B.bu g₀.card).aU g₀).ao A)
  have x0 : 0 ≤ oQ := by
    apply (B.a8 g₀).mo
    exact
      (B.a8 g₀).en
          A wq
  have DE : 0 ≤ kD := by
    apply
      ((B.bu g₀.card).aU g₀).mo
    exact
      ((B.bu g₀.card).aU g₀).en
          A wq
  have CN :
      0 ≤ B.dA g₀
        (B.ao A) :=
    B.r0 g₀
      (B.ao A)
  have yB :
      B.dA g₀
          (B.ao A) ≤
        kD :=
    B.mw
      dv hg₀ d3 A wq t5
  have Ee :
      B.bf g₀ q
          (B.ao A) ^ 2 ≤
        (β * oQ) * kD := by
    calc
      B.bf g₀ q
            (B.ao A) ^ 2 ≤
          mean (fun y => q y ^ 2) *
            B.dA g₀
              (B.ao A) :=
        B.l5
          g₀ q (B.ao A)
      _ ≤
          (β * oQ) *
            B.dA g₀
              (B.ao A) :=
        mul_le_mul_of_nonneg_right vm CN
      _ ≤ (β * oQ) * kD :=
        mul_le_mul_of_nonneg_left yB
          (mul_nonneg gr x0)
  have s7 :
      0 ≤ (β * oQ) * kD :=
    mul_nonneg (mul_nonneg gr x0) DE
  apply
    (sq_le_sq₀
      (abs_nonneg
        (B.bf g₀ q
          (B.ao A)))
      (Real.sqrt_nonneg _)).mp
  rw [sq_abs, Real.sq_sqrt s7]
  exact Ee
end ah
structure cX
    (α β μ : ℕ → ℝ) (τ : ℝ)
    (E : ℕ → ℕ → ℝ) : Prop where
  sV : ∀ d, 0 < α d
  density_le_one : ∀ d, α d ≤ 1
  vN : ∀ d, 0 ≤ β d
  u3 : 0 ≤ τ
  floor_pos : ∀ d, 0 < μ d
  y1 :
    ∀ ⦃i d : ℕ⦄, i ≤ d → μ d ≤ α i
  pF :
    ∀ d n, 0 ≤ E d n
  q0 :
    ∀ ⦃d d' n : ℕ⦄, d ≤ d' →
      E d n ≤ E d' n
  uB :
    ∀ ⦃d n n' : ℕ⦄, n ≤ n' →
      E d n ≤ E d n'
  step :
    ∀ d n,
      E (d + 1) n +
            Real.sqrt
                (β (d + 1) *
                  (1 + E d (n + 1)) *
                  (1 + E d (2 * (n + 1)))) /
              (α (d + 1)) ^ (n + 1) +
          τ / (μ (d + 1)) ^ (n + 1) ≤
        E (d + 1) (n + 1)
noncomputable def jM
    (α β μ : ℕ → ℝ) (τ : ℝ)
    (E : ℕ → ℕ → ℝ)
    (d n : ℕ) : ℝ :=
  Real.sqrt
        (β (d + 1) *
          (1 + E d (n + 1)) *
          (1 + E d (2 * (n + 1)))) /
      (α (d + 1)) ^ (n + 1) +
    τ / (μ (d + 1)) ^ (n + 1)
theorem cX.vn
    {α β μ : ℕ → ℝ} {τ : ℝ}
    {E : ℕ → ℕ → ℝ}
    (hE : cX α β μ τ E)
    (d n : ℕ) :
    E (d + 1) n +
        jM α β μ τ E d n ≤
      E (d + 1) (n + 1) := by
  simpa [jM, add_assoc] using hE.step d n
theorem cX.uv
    {α β μ : ℕ → ℝ} {τ : ℝ}
    {E : ℕ → ℕ → ℝ}
    (hE : cX α β μ τ E)
    (d n : ℕ) :
    0 ≤
      (1 + E d (n + 1)) *
        (1 + E d (2 * (n + 1))) := by
  exact mul_nonneg
    (by linarith [hE.pF d (n + 1)])
    (by linarith [hE.pF d (2 * (n + 1))])
end av.ag
end
section
namespace av.ag
open Filter Topology
noncomputable def kP
    (a t : ℝ) (lower : ℕ → ℝ) (n : ℕ) : ℝ :=
  Real.sqrt
        (t ^ 2 *
          (1 + lower (n + 1)) *
          (1 + lower (2 * (n + 1)))) /
      a ^ (n + 1) +
    t ^ 2 / a ^ (n + 1)
noncomputable def gl
    (a t : ℝ) (lower : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 =>
      gl a t lower n +
        kP a t lower n
end av.ag
end
section
namespace av.ag
open Filter Topology
def bh (α : ℕ → ℝ) : ℕ → ℝ
  | 0 => α 0
  | d + 1 => min (bh α d) (α (d + 1))
@[simp]
theorem xO (α : ℕ → ℝ) :
    bh α 0 = α 0 :=
  rfl
@[simp]
theorem lX (α : ℕ → ℝ) (d : ℕ) :
    bh α (d + 1) =
      min (bh α d) (α (d + 1)) :=
  rfl
theorem mx
    {α : ℕ → ℝ} (fX : ∀ d, 0 < α d) :
    ∀ d, 0 < bh α d := by
  intro d
  induction d with
  | zero => simpa using fX 0
  | succ d ih =>
      simpa using lt_min ih (fX (d + 1))
theorem r2
    (α : ℕ → ℝ) {i d : ℕ} (Du : i ≤ d) :
    bh α d ≤ α i := by
  induction d with
  | zero =>
      have hi : i = 0 := Nat.eq_zero_of_le_zero Du
      subst i
      exact le_rfl
  | succ d ih =>
      rw [lX]
      by_cases hi : i = d + 1
      · subst i
        exact min_le_right _ _
      · exact (min_le_left _ _).trans (ih (Nat.le_of_lt_succ (lt_of_le_of_ne Du hi)))
noncomputable def cL
    (α β μ : ℕ → ℝ) (τ : ℝ)
    (lower : ℕ → ℝ) (d n : ℕ) : ℝ :=
  Real.sqrt
        (β (d + 1) *
          (1 + lower (n + 1)) *
          (1 + lower (2 * (n + 1)))) /
      (α (d + 1)) ^ (n + 1) +
    τ / (μ (d + 1)) ^ (n + 1)
noncomputable def df
    (α β μ : ℕ → ℝ) (τ : ℝ)
    (d : ℕ) (lower : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 =>
      max (lower (n + 1))
        (df α β μ τ d lower n +
          cL α β μ τ lower d n)
noncomputable def a1
    (α β μ : ℕ → ℝ) (τ : ℝ) : ℕ → ℕ → ℝ
  | 0 => fun _ => 0
  | d + 1 =>
      df α β μ τ d
        (a1 α β μ τ d)
@[simp]
theorem tu
    (α β μ : ℕ → ℝ) (τ : ℝ) (d : ℕ) (lower : ℕ → ℝ) :
    df α β μ τ d lower 0 = 0 :=
  rfl
@[simp]
theorem f7
    (α β μ : ℕ → ℝ) (τ : ℝ) (d n : ℕ) (lower : ℕ → ℝ) :
    df α β μ τ d lower (n + 1) =
      max (lower (n + 1))
        (df α β μ τ d lower n +
          cL α β μ τ lower d n) :=
  rfl
@[simp]
theorem vW
    (α β μ : ℕ → ℝ) (τ : ℝ) (n : ℕ) :
    a1 α β μ τ 0 n = 0 :=
  rfl
@[simp]
theorem dx
    (α β μ : ℕ → ℝ) (τ : ℝ) (d n : ℕ) :
    a1 α β μ τ (d + 1) n =
      df α β μ τ d
        (a1 α β μ τ d) n :=
  rfl
theorem kE
    {α β μ : ℕ → ℝ} {τ : ℝ}
    (fX : ∀ d, 0 ≤ α d) (rl : ∀ d, 0 ≤ μ d)
    (iQ : 0 ≤ τ) (lower : ℕ → ℝ) (d n : ℕ) :
    0 ≤ cL α β μ τ lower d n := by
  unfold cL
  exact add_nonneg
    (div_nonneg (Real.sqrt_nonneg _) (pow_nonneg (fX _) _))
    (div_nonneg iQ (pow_nonneg (rl _) _))
theorem sI
    {α β μ : ℕ → ℝ} {τ : ℝ}
    (fX : ∀ d, 0 ≤ α d) (rl : ∀ d, 0 ≤ μ d)
    (iQ : 0 ≤ τ) (d : ℕ) (lower : ℕ → ℝ) :
    ∀ n, 0 ≤ df α β μ τ d lower n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [f7]
      exact le_max_of_le_right
        (add_nonneg ih
          (kE fX rl iQ lower d n))
theorem kF
    {α β μ : ℕ → ℝ} {τ : ℝ}
    (fX : ∀ d, 0 ≤ α d) (rl : ∀ d, 0 ≤ μ d)
    (iQ : 0 ≤ τ) :
    ∀ d n, 0 ≤ a1 α β μ τ d n := by
  intro d
  induction d with
  | zero =>
      intro n
      simp
  | succ d _ih =>
      intro n
      rw [dx]
      exact sI fX rl iQ d _ n
@[simp]
theorem wc
    (α β μ : ℕ → ℝ) (τ : ℝ) :
    ∀ d, a1 α β μ τ d 0 = 0 := by
  intro d
  cases d <;> simp
theorem iG
    {α β μ : ℕ → ℝ} {τ : ℝ}
    (fX : ∀ d, 0 ≤ α d) (rl : ∀ d, 0 ≤ μ d)
    (iQ : 0 ≤ τ) (d : ℕ) :
    Monotone (a1 α β μ τ d) := by
  apply monotone_nat_of_le_succ
  intro n
  cases d with
  | zero => simp
  | succ d =>
      rw [dx,
        dx,
        f7]
      exact le_max_of_le_right
        (le_add_of_nonneg_right
          (kE fX rl iQ _ d n))
theorem nY
    (α β μ : ℕ → ℝ) (τ : ℝ) (d n : ℕ) :
    a1 α β μ τ d n ≤
      a1 α β μ τ (d + 1) n := by
  cases n with
  | zero => simp
  | succ n =>
      rw [dx,
        f7]
      exact le_max_left _ _
theorem nD
    (α β μ : ℕ → ℝ) (τ : ℝ) (n : ℕ) :
    Monotone (fun d => a1 α β μ τ d n) := by
  apply monotone_nat_of_le_succ
  exact fun d => nY α β μ τ d n
theorem pc
    {α β : ℕ → ℝ} {τ : ℝ}
    (fX : ∀ d, 0 < α d) (rm : ∀ d, α d ≤ 1)
    (gr : ∀ d, 0 ≤ β d) (iQ : 0 ≤ τ) :
    cX α β
      (bh α) τ
      (a1 α β
        (bh α) τ) := by
  let μ := bh α
  have rl : ∀ d, 0 < μ d := mx fX
  refine
    { sV := fX
      density_le_one := rm
      vN := gr
      u3 := iQ
      floor_pos := rl
      y1 := ?_
      pF := kF
        (fun d => (fX d).le) (fun d => (rl d).le) iQ
      q0 := ?_
      uB := ?_
      step := ?_ }
  · intro i d Du
    exact r2 α Du
  · intro d d' n FN
    exact (nD α β μ τ n) FN
  · intro d n n' FO
    exact (iG
      (fun q => (fX q).le) (fun q => (rl q).le) iQ d) FO
  · intro d n
    have ow :
        df α β μ τ d
              (a1 α β μ τ d) n +
            cL α β μ τ
              (a1 α β μ τ d) d n ≤
          max (a1 α β μ τ d (n + 1))
            (df α β μ τ d
                (a1 α β μ τ d) n +
              cL α β μ τ
                (a1 α β μ τ d) d n) :=
      le_max_right _ _
    simp [μ, cL, add_assoc] at ow ⊢
@[simp]
theorem py
    (α μ : ℕ → ℝ) (d : ℕ) (lower : ℕ → ℝ)
    (rE : ∀ n, lower n = 0) :
    ∀ n,
      df α (fun _ => 0) μ 0 d lower n = 0 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [f7, ih]
      simp [cL, rE]
@[simp]
theorem uZ
    (α μ : ℕ → ℝ) :
    ∀ d n,
      a1 α (fun _ => 0) μ 0 d n = 0 := by
  intro d
  induction d with
  | zero =>
      intro n
      simp
  | succ d ih =>
      intro n
      rw [dx]
      exact py α μ d _ ih n
def aZ
    (bK bU d : ℕ) : ℕ :=
  (bU + 1) * 2 ^ (bK - d)
theorem nZ
    {bK bU d : ℕ} (hd : d < bK) :
    2 * aZ bK bU (d + 1) =
      aZ bK bU d := by
  have uI : bK - d = bK - (d + 1) + 1 := by
    omega
  simp only [aZ, uI, pow_succ]
  ring
theorem jN
    (bK bU d : ℕ) :
    aZ bK bU d ≤
      aZ bK bU 0 := by
  unfold aZ
  apply Nat.mul_le_mul_left
  exact (pow_right_monotone (by norm_num : (1 : ℕ) ≤ 2))
    (Nat.sub_le bK d)
theorem nE
    {α β μ : ℕ → ℝ} {τ B η : ℝ}
    (fX : ∀ d, 0 ≤ α d) (gr : ∀ d, 0 ≤ β d)
    (lower : ℕ → ℝ) (d n : ℕ)
    (oS : ∀ m, 0 ≤ lower m)
    (wu : lower (n + 1) ≤ B)
    (y2 : lower (2 * (n + 1)) ≤ B)
    (lf :
      Real.sqrt
            (β (d + 1) * (1 + B) * (1 + B)) /
          (α (d + 1)) ^ (n + 1) ≤ η / 2)
    (mZ :
      τ / (μ (d + 1)) ^ (n + 1) ≤ η / 2) :
    cL α β μ τ lower d n ≤ η := by
  have Dv : 0 ≤ 1 + lower (n + 1) := by
    linarith [oS (n + 1)]
  have x1 : 0 ≤ 1 + lower (2 * (n + 1)) := by
    linarith [oS (2 * (n + 1))]
  have Aq : 0 ≤ 1 + B := by
    linarith [oS (n + 1), wu]
  have xr :
      (1 + lower (n + 1)) * (1 + lower (2 * (n + 1))) ≤
        (1 + B) * (1 + B) := by
    exact mul_le_mul
      (by linarith)
      (by linarith)
      x1 Aq
  have s7 :
      β (d + 1) *
          (1 + lower (n + 1)) *
          (1 + lower (2 * (n + 1))) ≤
        β (d + 1) * (1 + B) * (1 + B) := by
    simpa [mul_assoc] using
      mul_le_mul_of_nonneg_left xr (gr (d + 1))
  have x2 :
      Real.sqrt
          (β (d + 1) *
            (1 + lower (n + 1)) *
            (1 + lower (2 * (n + 1)))) ≤
        Real.sqrt (β (d + 1) * (1 + B) * (1 + B)) :=
    Real.sqrt_le_sqrt s7
  have xc :
      Real.sqrt
            (β (d + 1) *
              (1 + lower (n + 1)) *
              (1 + lower (2 * (n + 1)))) /
          (α (d + 1)) ^ (n + 1) ≤ η / 2 :=
    (div_le_div_of_nonneg_right x2
      (pow_nonneg (fX (d + 1)) (n + 1))).trans lf
  unfold cL
  linarith
theorem np
    {α β μ : ℕ → ℝ} {τ η B : ℝ}
    (fX : ∀ d, 0 ≤ α d) (gr : ∀ d, 0 ≤ β d)
    (rl : ∀ d, 0 ≤ μ d) (iQ : 0 ≤ τ) (hη : 0 ≤ η)
    (bK : ℕ) (d1 : ℕ → ℕ)
    (vq : ∀ d, d < bK →
      2 * d1 (d + 1) ≤ d1 d)
    (hzero : ∀ d, d ≤ bK → d1 d ≤ d1 0)
    (xt :
      (bK : ℝ) * (d1 0 : ℝ) * η ≤ B)
    (lf : ∀ d, d < bK → ∀ n, n < d1 (d + 1) →
      Real.sqrt
            (β (d + 1) * (1 + B) * (1 + B)) /
          (α (d + 1)) ^ (n + 1) ≤ η / 2)
    (mZ : ∀ d, d < bK → ∀ n, n < d1 (d + 1) →
      τ / (μ (d + 1)) ^ (n + 1) ≤ η / 2) :
    ∀ d, d ≤ bK → ∀ n, n ≤ d1 d →
      a1 α β μ τ d n ≤
        (d : ℝ) * (d1 0 : ℝ) * η := by
  intro d hd
  induction d with
  | zero =>
      intro n hn
      simp
  | succ d ih =>
      have xu : d < bK := Nat.lt_of_succ_le hd
      let lower := a1 α β μ τ d
      have oS : ∀ m, 0 ≤ lower m :=
        kF fX rl iQ d
      have CO : d ≤ bK := Nat.le_of_lt xu
      have A1 :
          (d : ℝ) * (d1 0 : ℝ) * η ≤ B := by
        have Ef : (d : ℝ) ≤ bK := by exact_mod_cast CO
        have Gr : 0 ≤ (d1 0 : ℝ) := by positivity
        have oT : 0 ≤ (d1 0 : ℝ) * η := mul_nonneg Gr hη
        calc
          (d : ℝ) * (d1 0 : ℝ) * η =
              (d : ℝ) * ((d1 0 : ℝ) * η) := by ring
          _ ≤ (bK : ℝ) * ((d1 0 : ℝ) * η) :=
            mul_le_mul_of_nonneg_right Ef oT
          _ = (bK : ℝ) * (d1 0 : ℝ) * η := by ring
          _ ≤ B := xt
      have FQ : ∀ m, m ≤ d1 (d + 1) →
          df α β μ τ d lower m ≤
            (d : ℝ) * (d1 0 : ℝ) * η + (m : ℝ) * η := by
        intro m hm
        induction m with
        | zero =>
            simp only [tu, Nat.cast_zero, zero_mul,
              add_zero]
            exact mul_nonneg (mul_nonneg (by positivity) (by positivity)) hη
        | succ m Gs =>
            have FR : m ≤ d1 (d + 1) := Nat.le_trans (Nat.le_succ m) hm
            have Dw : m < d1 (d + 1) := Nat.lt_of_succ_le hm
            have BV : m + 1 ≤ d1 d := by
              have Bh := vq d xu
              omega
            have BW : 2 * (m + 1) ≤ d1 d := by
              have Bh := vq d xu
              omega
            have wv := ih CO (m + 1) BV
            have zP := ih CO (2 * (m + 1)) BW
            have wu : lower (m + 1) ≤ B := wv.trans A1
            have y2 : lower (2 * (m + 1)) ≤ B := zP.trans A1
            have tN :
                cL α β μ τ lower d m ≤ η :=
              nE fX gr lower d m
                oS wu y2
                (lf d xu m Dw) (mZ d xu m Dw)
            rw [f7]
            apply max_le
            · calc
                lower (m + 1) ≤
                    (d : ℝ) * (d1 0 : ℝ) * η := wv
                _ ≤ (d : ℝ) * (d1 0 : ℝ) * η +
                    ((m + 1 : ℕ) : ℝ) * η :=
                  le_add_of_nonneg_right (mul_nonneg (by positivity) hη)
            · calc
                df α β μ τ d lower m +
                      cL α β μ τ lower d m ≤
                    ((d : ℝ) * (d1 0 : ℝ) * η + (m : ℝ) * η) + η :=
                  add_le_add (Gs FR) tN
                _ = (d : ℝ) * (d1 0 : ℝ) * η +
                    ((m + 1 : ℕ) : ℝ) * η := by
                  push_cast
                  ring
      intro n hn
      rw [dx]
      have Bi := FQ n hn
      have Eg : n ≤ d1 0 := hn.trans (hzero (d + 1) hd)
      have Eh : (n : ℝ) ≤ d1 0 := by exact_mod_cast Eg
      have CP : (n : ℝ) * η ≤ (d1 0 : ℝ) * η :=
        mul_le_mul_of_nonneg_right Eh hη
      calc
        df α β μ τ d lower n ≤
            (d : ℝ) * (d1 0 : ℝ) * η + (n : ℝ) * η := Bi
        _ ≤ (d : ℝ) * (d1 0 : ℝ) * η +
            (d1 0 : ℝ) * η := add_le_add_right CP _
        _ = ((d + 1 : ℕ) : ℝ) * (d1 0 : ℝ) * η := by
          push_cast
          ring
theorem km
    {α β μ : ℕ → ℝ} {τ η B : ℝ}
    (fX : ∀ d, 0 ≤ α d) (gr : ∀ d, 0 ≤ β d)
    (rl : ∀ d, 0 ≤ μ d) (iQ : 0 ≤ τ) (hη : 0 ≤ η)
    (bK bU : ℕ)
    (xt :
      (bK : ℝ) *
          (aZ bK bU 0 : ℝ) * η ≤ B)
    (lf : ∀ d, d < bK → ∀ n,
      n < aZ bK bU (d + 1) →
      Real.sqrt
            (β (d + 1) * (1 + B) * (1 + B)) /
          (α (d + 1)) ^ (n + 1) ≤ η / 2)
    (mZ : ∀ d, d < bK → ∀ n,
      n < aZ bK bU (d + 1) →
      τ / (μ (d + 1)) ^ (n + 1) ≤ η / 2) :
    a1 α β μ τ bK (bU + 1) ≤
      (bK : ℝ) *
        (aZ bK bU 0 : ℝ) * η := by
  apply np fX gr rl iQ hη
    bK (aZ bK bU)
    (fun d hd => (nZ hd).le)
    (fun d _hd => jN bK bU d)
    xt lf mZ bK le_rfl (bU + 1)
  simp [aZ]
theorem h0
    {α β : ℕ → ℝ} {τ η : ℝ}
    (fX : ∀ d, 0 < α d) (rm : ∀ d, α d ≤ 1)
    (gr : ∀ d, 0 ≤ β d) (iQ : 0 ≤ τ) (hη : 0 ≤ η)
    (bK bU : ℕ)
    (xt :
      (bK : ℝ) *
          (aZ bK bU 0 : ℝ) * η ≤ 1)
    (zQ :
      (bK : ℝ) *
          (aZ bK bU 0 : ℝ) * η < 1 / 2)
    (lf : ∀ d, d < bK → ∀ n,
      n < aZ bK bU (d + 1) →
      Real.sqrt
            (β (d + 1) * (1 + (1 : ℝ)) * (1 + (1 : ℝ))) /
          (α (d + 1)) ^ (n + 1) ≤ η / 2)
    (mZ : ∀ d, d < bK → ∀ n,
      n < aZ bK bU (d + 1) →
      τ /
          (bh α (d + 1)) ^ (n + 1) ≤
        η / 2) :
    cX α β
        (bh α) τ
        (a1 α β
          (bh α) τ) ∧
      a1 α β
          (bh α) τ bK bU < 1 / 2 := by
  have rl : ∀ d, 0 ≤ bh α d :=
    fun d => (mx fX d).le
  have hbound :=
    km
      (fun d => (fX d).le) gr rl iQ hη bK bU
      xt lf mZ
  have fE :
      a1 α β
          (bh α) τ bK bU ≤
        a1 α β
          (bh α) τ bK (bU + 1) :=
    (iG
      (fun d => (fX d).le) rl iQ bK) (Nat.le_succ bU)
  exact ⟨pc fX rm gr iQ,
    (fE.trans hbound).trans_lt zQ⟩
end av.ag
end
section
namespace av.ag
open scoped BigOperators
theorem x3 {α κ : Type*}
    [Fintype α]
    (s : Finset κ) (f : κ → α → ℝ) :
    mean (fun x => ∑ q ∈ s, f q x) =
      ∑ q ∈ s, mean (f q) := by
  simpa [mean] using
    (Finset.expect_sum_comm
      (s := (Finset.univ : Finset α)) s
      (fun x q => f q x))
end av.ag
end
section
namespace av.ag
open scoped BigOperators
noncomputable def aq {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (f : Ω → ℝ) (x : Ω) : ℝ :=
  Finset.expect (P.part x) f
theorem r3 {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (f : Ω → ℝ) {x y : Ω}
    (u4 : P.part x = P.part y) :
    aq P f x = aq P f y := by
  rw [aq, aq, u4]
theorem cY {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (f : Ω → ℝ) {x y : Ω}
    (hy : y ∈ P.part x) :
    aq P f y = aq P f x := by
  apply r3
  apply P.part_eq_of_mem
  · simp
  · exact hy
theorem uK {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    {f : Ω → ℝ} (hf : ∀ x, 0 ≤ f x) (x : Ω) :
    0 ≤ aq P f x := by
  exact Finset.expect_nonneg fun y _ => hf y
theorem sx {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (f g : Ω → ℝ) (x : Ω) :
    aq P (fun y => f y - g y) x =
      aq P f x - aq P g x := by
  exact Finset.expect_sub_distrib (P.part x) f g
theorem vr {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (c : ℝ) (f : Ω → ℝ) (x : Ω) :
    aq P (fun y => c * f y) x =
      c * aq P f x := by
  exact (Finset.mul_expect (P.part x) f c).symm
theorem oe {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (f : Ω → ℝ) {s : Finset Ω} (hs : s ∈ P.parts) :
    ∑ x ∈ s, aq P f x = ∑ x ∈ s, f x := by
  calc
    ∑ x ∈ s, aq P f x =
        ∑ x ∈ s, Finset.expect s f := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [aq, P.part_eq_of_mem hs hx]
    _ = (s.card : ℝ) * Finset.expect s f := by
      simp
    _ = ∑ x ∈ s, f x := Finset.card_mul_expect s f
theorem vX {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (f : Ω → ℝ) :
    ∑ x, aq P f x = ∑ x, f x := by
  classical
  have x4 :
      P.parts.biUnion id = (Finset.univ : Finset Ω) :=
    P.biUnion_parts
  calc
    ∑ x, aq P f x =
        ∑ x ∈ P.parts.biUnion id, aq P f x := by
      exact Finset.sum_congr x4.symm fun _ _ => rfl
    _ =
        ∑ s ∈ P.parts, ∑ x ∈ s, aq P f x := by
      exact Finset.sum_biUnion P.disjoint
    _ = ∑ s ∈ P.parts, ∑ x ∈ s, f x := by
      apply Finset.sum_congr rfl
      intro s hs
      exact oe P f hs
    _ = ∑ x ∈ P.parts.biUnion id, f x :=
      (Finset.sum_biUnion P.disjoint).symm
    _ = ∑ x, f x := by
      exact Finset.sum_congr x4 fun _ _ => rfl
theorem iR {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (f : Ω → ℝ) :
    mean (aq P f) = mean f := by
  change (𝔼 x, aq P f x) = 𝔼 x, f x
  rw [Fintype.expect_eq_sum_div_card,
    Fintype.expect_eq_sum_div_card, vX P f]
theorem u5 {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (f : Ω → ℝ) (x : Ω) :
    aq P f x ^ 2 ≤
      aq P (fun y => f y ^ 2) x := by
  have h :=
    Finset.expect_mul_sq_le_sq_mul_sq
      (P.part x) f (fun _ : Ω => (1 : ℝ))
  simpa [aq,
    Finset.expect_const (s := P.part x) (by simp) (1 : ℝ)] using h
noncomputable def cq {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (f : Ω → ℝ) : ℝ :=
  mean fun x => aq P f x ^ 2
theorem uL {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (f : Ω → ℝ) :
    0 ≤ cq P f := by
  exact o9 fun x => sq_nonneg _
theorem tv {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (f : Ω → ℝ) :
    cq P f ≤ mean fun x => f x ^ 2 := by
  calc
    cq P f ≤
        mean (aq P fun x => f x ^ 2) :=
      mm fun x => u5 P f x
    _ = mean (fun x => f x ^ 2) :=
      iR P fun x => f x ^ 2
end av.ag
end
section
namespace av.ag
abbrev ab (Ω : Type*) [Fintype Ω] [DecidableEq Ω] :=
  Finpartition (Finset.univ : Finset Ω)
namespace ab
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
theorem gj {P Q : ab Ω}
    (h : P ≤ Q) (x : Ω) :
    P.part x ⊆ Q.part x := by
  obtain ⟨s, hs, uI⟩ :=
    h (P.part_mem.2 (Finset.mem_univ x))
  have zR : x ∈ s :=
    uI (P.mem_part (Finset.mem_univ x))
  rw [Q.part_eq_of_mem hs zR]
  exact uI
theorem pH {P Q : ab Ω} :
    P ≤ Q ↔ ∀ x, P.part x ⊆ Q.part x := by
  constructor
  · exact fun h x => gj h x
  · intro h s hs
    obtain ⟨x, hx⟩ := P.nonempty_of_mem_parts hs
    refine ⟨Q.part x, Q.part_mem.2 (Finset.mem_univ x), ?_⟩
    rw [← P.part_eq_of_mem hs hx]
    exact h x
def indiscrete : ab Ω :=
  ⊤
@[simp]
theorem uC (x : Ω) :
    (indiscrete : ab Ω).part x = Finset.univ := by
  change (⊤ : ab Ω).part x = Finset.univ
  have jO :
      (⊤ : ab Ω).part x ∈
        (⊤ : ab Ω).parts :=
    (⊤ : ab Ω).part_mem.2 (Finset.mem_univ x)
  exact Finset.mem_singleton.mp
    (Finpartition.parts_top_subset
      (Finset.univ : Finset Ω) jO)
def aO (P : ab Ω) : ℕ :=
  P.parts.card
noncomputable def representative
    (P : ab Ω) (a : P.parts) : Ω :=
  Classical.choose (P.nonempty_of_mem_parts a.2)
theorem jP
    (P : ab Ω) (a : P.parts) :
    P.representative a ∈ a.1 :=
  Classical.choose_spec (P.nonempty_of_mem_parts a.2)
@[simp]
theorem A3 [Nonempty Ω] :
    aO (indiscrete : ab Ω) = 1 := by
  let x : Ω := Classical.choice inferInstance
  have Fa :
      (Finset.univ : Finset Ω) ∈
        (⊤ : ab Ω).parts := by
    have hx :=
      (⊤ : ab Ω).part_mem.2
        (Finset.mem_univ x)
    change
      (indiscrete : ab Ω).part x ∈
        (indiscrete : ab Ω).parts at hx
    rw [uC] at hx
    exact hx
  have x4 :
      (⊤ : ab Ω).parts =
        {(Finset.univ : Finset Ω)} := by
    apply Finset.Subset.antisymm
    · exact Finpartition.parts_top_subset _
    · intro s hs
      rw [Finset.mem_singleton] at hs
      simpa [hs] using Fa
  simp [aO, indiscrete, x4]
def join (P Q : ab Ω) : ab Ω :=
  P ⊓ Q
theorem t8 (P Q : ab Ω) :
    join P Q ≤ P :=
  inf_le_left
theorem vO (P Q : ab Ω) :
    join P Q ≤ Q :=
  inf_le_right
theorem Ar {P Q R : ab Ω} :
    R ≤ join P Q ↔ R ≤ P ∧ R ≤ Q :=
  le_inf_iff
@[simp]
theorem y3 (P Q : ab Ω) (x : Ω) :
    (join P Q).part x = P.part x ∩ Q.part x := by
  apply Finpartition.part_eq_of_mem
  · rw [join, Finpartition.parts_inf]
    apply Finset.mem_erase.mpr
    constructor
    · exact Finset.nonempty_iff_ne_empty.mp ⟨x, by simp⟩
    · apply Finset.mem_image.mpr
      refine ⟨(P.part x, Q.part x), ?_, rfl⟩
      simp
  · simp
theorem wx (P Q : ab Ω) :
    aO (join P Q) ≤ aO P * aO Q := by
  change (P ⊓ Q).parts.card ≤ P.parts.card * Q.parts.card
  calc
    (P ⊓ Q).parts.card =
        (((P.parts ×ˢ Q.parts).image
          (fun st => st.1 ⊓ st.2)).erase ⊥).card :=
      congrArg Finset.card (Finpartition.parts_inf P Q)
    _ ≤
        ((P.parts ×ˢ Q.parts).image
          (fun st => st.1 ⊓ st.2)).card :=
      Finset.card_le_card (Finset.erase_subset _ _)
    _ ≤ (P.parts ×ˢ Q.parts).card :=
      Finset.card_image_le
    _ = P.parts.card * Q.parts.card :=
      Finset.card_product P.parts Q.parts
def kQ {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (P : ι → ab Ω) :
    ab Ω :=
  s.inf P
@[simp]
theorem xv {ι : Type*} [DecidableEq ι]
    (P : ι → ab Ω) :
    kQ ∅ P = indiscrete :=
  rfl
@[simp]
theorem w0 {ι : Type*} [DecidableEq ι]
    (a : ι) (s : Finset ι) (P : ι → ab Ω) :
    kQ (insert a s) P =
      join (P a) (kQ s P) := by
  simp [kQ, join]
theorem vt {ι : Type*} [DecidableEq ι]
    {s : Finset ι} (P : ι → ab Ω)
    {i : ι} (hi : i ∈ s) :
    kQ s P ≤ P i :=
  Finset.inf_le hi
theorem w1 {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {P : ι → ab Ω}
    {Q : ab Ω} :
    Q ≤ kQ s P ↔ ∀ i ∈ s, Q ≤ P i :=
  Finset.le_inf_iff
theorem qi {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (P : ι → ab Ω)
    (x y : Ω) :
    y ∈ (kQ s P).part x ↔
      ∀ i ∈ s, y ∈ (P i).part x := by
  classical
  induction s using Finset.induction with
  | empty =>
      rw [xv]
      simp
  | @insert a s ha ih =>
      simp only [w0, y3,
        Finset.mem_inter, Finset.mem_insert, forall_eq_or_imp,
        ih]
def generatedBy (F : Finset (Finset Ω)) : ab Ω :=
  Finpartition.atomise Finset.univ F
@[simp]
theorem fI (F : Finset (Finset Ω))
    (x y : Ω) :
    y ∈ (generatedBy F).part x ↔
      ∀ s ∈ F, (x ∈ s ↔ y ∈ s) := by
  classical
  let P : ab Ω := generatedBy F
  have hp : P.part x ∈ P.parts :=
    P.part_mem.2 (Finset.mem_univ x)
  have Ei :
      P.part x ∈
        (Finpartition.atomise
          (Finset.univ : Finset Ω) F).parts := by
    change
      (Finpartition.atomise
        (Finset.univ : Finset Ω) F).part x ∈
        (Finpartition.atomise
          (Finset.univ : Finset Ω) F).parts at hp
    exact hp
  obtain ⟨_, Q, hQ, x5⟩ :=
    Finpartition.mem_atomise.mp Ei
  have jO := Finset.ext_iff.mp x5
  have hx : x ∈ P.part x :=
    P.mem_part (Finset.mem_univ x)
  have zS := (jO x).2 hx
  simp only [Finset.mem_filter] at zS
  constructor
  · intro hy s hs
    have BX := (jO y).2 hy
    simp only [Finset.mem_filter] at BX
    exact (zS.2 s hs).symm.trans (BX.2 s hs)
  · intro ox
    apply (jO y).1
    simp only [Finset.mem_filter]
    refine ⟨Finset.mem_univ y, ?_⟩
    intro s hs
    exact (zS.2 s hs).trans (ox s hs)
theorem vu {F G : Finset (Finset Ω)}
    (Gt : F ⊆ G) :
    generatedBy G ≤ generatedBy F := by
  rw [pH]
  intro x y hy
  rw [fI] at hy ⊢
  intro s hs
  exact hy s (Gt hs)
theorem pq (F : Finset (Finset Ω)) :
    aO (generatedBy F) ≤ 2 ^ F.card := by
  exact Finpartition.card_atomise_le
def sJ {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (f : Ω → Λ) (Q : ab Λ) : Setoid Ω where
  r x y := Q.part (f x) = Q.part (f y)
  iseqv := {
    refl := fun _ => rfl
    symm := fun h => h.symm
    trans := fun h₁ h₂ => h₁.trans h₂ }
instance x6 {Λ : Type*}
    [Fintype Λ] [DecidableEq Λ]
    (f : Ω → Λ) (Q : ab Λ) :
    DecidableRel (sJ f Q) := by
  intro x y
  change Decidable (Q.part (f x) = Q.part (f y))
  infer_instance
def pullback {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (f : Ω → Λ) (Q : ab Λ) : ab Ω :=
  Finpartition.ofSetoid (sJ f Q)
@[simp]
theorem u7 {Λ : Type*}
    [Fintype Λ] [DecidableEq Λ]
    (f : Ω → Λ) (Q : ab Λ) (x y : Ω) :
    y ∈ (pullback f Q).part x ↔
      Q.part (f x) = Q.part (f y) := by
  change
    y ∈
        (Finpartition.ofSetoid
          (sJ f Q)).part x ↔
      Q.part (f x) = Q.part (f y)
  rw [Finpartition.mem_part_ofSetoid_iff_rel]
  rfl
theorem gb {Λ : Type*}
    [Fintype Λ] [DecidableEq Λ]
    (f : Ω → Λ) (Q : ab Λ) (x y : Ω) :
    y ∈ (pullback f Q).part x ↔
      f y ∈ Q.part (f x) := by
  rw [u7]
  constructor
  · intro h
    exact
      (Q.mem_part_iff_part_eq_part
        (Finset.mem_univ (f y))
        (Finset.mem_univ (f x))).2 h.symm
  · intro h
    exact
      ((Q.mem_part_iff_part_eq_part
        (Finset.mem_univ (f y))
        (Finset.mem_univ (f x))).1 h).symm
theorem zf {Λ : Type*}
    [Fintype Λ] [DecidableEq Λ]
    (f : Ω → Λ) {P Q : ab Λ}
    (h : P ≤ Q) :
    pullback f P ≤ pullback f Q := by
  rw [pH]
  intro x y hy
  rw [gb] at hy ⊢
  exact gj h (f x) hy
end ab
end av.ag
end
section
namespace av.ag
open scoped BigOperators
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
theorem p3
    (P Q : ab Ω) (s8 : P ≤ Q)
    (f : Ω → ℝ) {s : Finset Ω} (hs : s ∈ Q.parts) :
    ∑ x ∈ s, aq P f x = ∑ x ∈ s, f x := by
  let rn : Finset (Finset Ω) :=
    P.parts.filter (fun t => t ⊆ s)
  have BY : rn.biUnion id = s := by
    ext x
    constructor
    · intro hx
      obtain ⟨t, ht, Dx⟩ := Finset.mem_biUnion.mp hx
      exact (Finset.mem_filter.mp ht).2 Dx
    · intro zR
      obtain ⟨t, ht, Dx⟩ :=
        P.exists_mem (Finset.mem_univ x)
      obtain ⟨u, hu, FB⟩ := s8 ht
      have Gu : u = s :=
        Q.eq_of_mem_parts hu hs (FB Dx) zR
      have Gv : t ⊆ s := by
        simpa [Gu] using FB
      exact Finset.mem_biUnion.mpr
        ⟨t, Finset.mem_filter.mpr ⟨ht, Gv⟩, Dx⟩
  have y4 :
      (↑rn : Set (Finset Ω)).PairwiseDisjoint id := by
    apply Set.Pairwise.mono ?_ P.disjoint
    intro t ht
    exact (Finset.mem_filter.mp ht).1
  calc
    ∑ x ∈ s, aq P f x =
        ∑ x ∈ rn.biUnion id,
          aq P f x := by
      exact Finset.sum_congr BY.symm fun _ _ => rfl
    _ =
        ∑ t ∈ rn,
          ∑ x ∈ t, aq P f x :=
      Finset.sum_biUnion y4
    _ = ∑ t ∈ rn, ∑ x ∈ t, f x := by
      apply Finset.sum_congr rfl
      intro t ht
      exact oe P f
        (Finset.mem_filter.mp ht).1
    _ = ∑ x ∈ rn.biUnion id, f x :=
      (Finset.sum_biUnion y4).symm
    _ = ∑ x ∈ s, f x := by
      exact Finset.sum_congr BY fun _ _ => rfl
@[simp]
theorem s9
    (P Q : ab Ω) (s8 : P ≤ Q)
    (f : Ω → ℝ) (x : Ω) :
    aq Q (aq P f) x =
      aq Q f x := by
  change
    Finset.expect (Q.part x) (aq P f) =
      Finset.expect (Q.part x) f
  rw [Finset.expect_eq_sum_div_card,
    Finset.expect_eq_sum_div_card,
    p3 P Q s8 f
      (Q.part_mem.2 (Finset.mem_univ x))]
@[simp]
theorem p4
    (P Q : ab Ω) (s8 : P ≤ Q)
    (f : Ω → ℝ) (x : Ω) :
    aq P (aq Q f) x =
      aq Q f x := by
  rw [aq]
  calc
    Finset.expect (P.part x) (aq Q f) =
        Finset.expect (P.part x)
          (fun _ => aq Q f x) := by
      apply Finset.expect_congr rfl
      intro y hy
      exact cY Q f
        (ab.gj s8 x hy)
    _ = aq Q f x :=
      Finset.expect_const (by simp) _
theorem g6
    (P : ab Ω) (u v : Ω → ℝ) (x : Ω)
    (hv : ∀ y ∈ P.part x, v y = v x) :
    aq P (fun y => u y * v y) x =
      aq P u x * v x := by
  calc
    aq P (fun y => u y * v y) x =
        aq P (fun y => v x * u y) x := by
      rw [aq, aq]
      apply Finset.expect_congr rfl
      intro y hy
      rw [hv y hy]
      ring
    _ = v x * aq P u x :=
      vr P (v x) u x
    _ = aq P u x * v x := by
      ring
theorem n0
    (P : ab Ω) (u v : Ω → ℝ) (x : Ω) :
    aq P
        (fun y => u y * aq P v y) x =
      aq P u x * aq P v x := by
  apply g6
  intro y hy
  exact cY P v hy
theorem pI
    (P Q : ab Ω) (s8 : P ≤ Q)
    (f : Ω → ℝ) :
    mean (fun x =>
      aq P f x * aq Q f x) =
      mean (fun x => aq Q f x ^ 2) := by
  calc
    mean (fun x =>
        aq P f x * aq Q f x) =
        mean (aq Q (fun x =>
          aq P f x * aq Q f x)) :=
      (iR Q _).symm
    _ =
        mean (fun x =>
          aq Q (aq P f) x *
            aq Q f x) := by
      apply congrArg mean
      funext x
      exact n0
        Q (aq P f) f x
    _ =
        mean (fun x =>
          aq Q f x * aq Q f x) := by
      apply congrArg mean
      funext x
      rw [s9 P Q s8]
    _ = mean (fun x => aq Q f x ^ 2) := by
      apply congrArg mean
      funext x
      rw [pow_two]
theorem og
    (P Q : ab Ω) (s8 : P ≤ Q)
    (f : Ω → ℝ) :
    cq P f =
      cq Q f +
        mean (fun x =>
          (aq P f x -
            aq Q f x) ^ 2) := by
  have Ej :=
    pI P Q s8 f
  have Bk :
      mean (fun x =>
        (aq P f x -
          aq Q f x) ^ 2) =
        mean (fun x => aq P f x ^ 2) -
          2 * mean (fun x =>
            aq P f x * aq Q f x) +
          mean (fun x => aq Q f x ^ 2) := by
    calc
      mean (fun x =>
          (aq P f x -
            aq Q f x) ^ 2) =
          mean (fun x =>
            aq P f x ^ 2 -
              2 * (aq P f x *
                aq Q f x) +
              aq Q f x ^ 2) := by
        apply congrArg mean
        funext x
        ring
      _ =
          mean (fun x => aq P f x ^ 2) -
            2 * mean (fun x =>
              aq P f x * aq Q f x) +
            mean (fun x => aq Q f x ^ 2) := by
        rw [tX, zI, k0]
  change
    mean (fun x => aq P f x ^ 2) =
      mean (fun x => aq Q f x ^ 2) +
        mean (fun x =>
          (aq P f x -
            aq Q f x) ^ 2)
  rw [Bk, Ej]
  ring
theorem mz
    (P Q : ab Ω) (s8 : P ≤ Q)
    (f : Ω → ℝ) :
    cq P f - cq Q f =
      mean (fun x =>
        (aq P f x -
          aq Q f x) ^ 2) := by
  rw [og P Q s8 f]
  ring
theorem oy
    (P Q : ab Ω) (s8 : P ≤ Q)
    (f : Ω → ℝ) :
    cq Q f ≤ cq P f := by
  rw [og P Q s8 f]
  exact le_add_of_nonneg_right
    (o9 fun x => sq_nonneg _)
end av.ag
end
section
namespace av.ag
open scoped BigOperators
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
abbrev aW (Ω : Type*) [DecidableEq Ω] :=
  Finset Ω
namespace aW
def eval (A : aW Ω) : Ω → ℝ :=
  aN A
omit [Fintype Ω] in
@[simp]
theorem As (A : aW Ω) {x : Ω} (hx : x ∈ A) :
    A.eval x = 1 :=
  cG hx
omit [Fintype Ω] in
@[simp]
theorem x7 (A : aW Ω) {x : Ω} (hx : x ∉ A) :
    A.eval x = 0 :=
  cj hx
omit [Fintype Ω] in
theorem DG (A : aW Ω) (x : Ω) :
    A.eval x ^ 2 = A.eval x := by
  by_cases hx : x ∈ A <;> simp [hx]
omit [Fintype Ω] in
theorem At (A : aW Ω) (x : Ω) :
    A.eval x ≤ 1 := by
  by_cases hx : x ∈ A <;> simp [hx]
end aW
def dJ (P : ab Ω) (g : Ω → ℝ) : Prop :=
  ∀ x y, y ∈ P.part x → g y = g x
namespace dJ
theorem of_le {P Q : ab Ω} {g : Ω → ℝ}
    (s8 : P ≤ Q) (hg : dJ Q g) :
    dJ P g := by
  intro x y hy
  exact hg x y (ab.gj s8 x hy)
theorem aq (P : ab Ω) (f : Ω → ℝ) :
    dJ P (aq P f) := by
  intro x y hy
  exact cY P f hy
end dJ
theorem qC (A : aW Ω) :
    dJ
      (ab.generatedBy ({A} : Finset (Finset Ω))) A.eval := by
  intro x y hy
  have u4 : x ∈ A ↔ y ∈ A := by
    have ox :=
      (ab.fI
        ({A} : Finset (Finset Ω)) x y).1 hy
    exact ox A (by simp)
  by_cases hx : x ∈ A
  · have Ek : y ∈ A := u4.mp hx
    simp [hx, Ek]
  · have Ek : y ∉ A := by
      intro hy
      exact hx (u4.mpr hy)
    simp [hx, Ek]
structure aE (Ω : Type*) [Fintype Ω] [DecidableEq Ω] where
  partition : ab Ω
namespace aE
noncomputable def structured (S : aE Ω)
    (f : Ω → ℝ) : Ω → ℝ :=
  aq S.partition f
noncomputable def residual (S : aE Ω)
    (f : Ω → ℝ) : Ω → ℝ :=
  fun x => f x - S.structured f x
noncomputable def energy (S : aE Ω)
    (f : Ω → ℝ) : ℝ :=
  cq S.partition f
noncomputable def b2
    (S : aE Ω) (f : Ω → ℝ)
    (A : aW Ω) : ℝ :=
  mean fun x => S.residual f x * A.eval x
def ea (S : aE Ω)
    (A : aW Ω) : aE Ω where
  partition :=
    ab.join S.partition
      (ab.generatedBy ({A} : Finset (Finset Ω)))
theorem xd (S : aE Ω)
    (A : aW Ω) :
    (S.ea A).partition ≤ S.partition :=
  ab.t8 _ _
theorem rH (S : aE Ω)
    (A : aW Ω) :
    dJ (S.ea A).partition A.eval := by
  apply dJ.of_le
    (ab.vO S.partition
      (ab.generatedBy ({A} : Finset (Finset Ω))))
  exact qC A
theorem qD
    (S : aE Ω) (f : Ω → ℝ)
    (A : aW Ω) (x : Ω) :
    aq (S.ea A).partition (S.residual f) x =
      (S.ea A).structured f x - S.structured f x := by
  change
    aq (S.ea A).partition
        (fun y => f y - aq S.partition f y) x =
      aq (S.ea A).partition f x -
        aq S.partition f x
  rw [sx]
  rw [p4
    (S.ea A).partition S.partition (S.xd A)]
theorem gI
    (P : ab Ω) (u v : Ω → ℝ)
    (hv : dJ P v) :
    mean (fun x => u x * v x) =
      mean (fun x => aq P u x * v x) := by
  calc
    mean (fun x => u x * v x) =
        mean (aq P (fun x => u x * v x)) :=
      (iR P _).symm
    _ = mean (fun x => aq P u x * v x) := by
      apply congrArg mean
      funext x
      exact g6
        P u v x (hv x)
theorem p5
    (S : aE Ω) (f : Ω → ℝ)
    (A : aW Ω) :
    S.b2 f A =
      mean (fun x =>
        ((S.ea A).structured f x - S.structured f x) *
          A.eval x) := by
  rw [b2]
  calc
    mean (fun x => S.residual f x * A.eval x) =
        mean (fun x =>
          aq (S.ea A).partition (S.residual f) x *
            A.eval x) :=
      gI
        (S.ea A).partition (S.residual f) A.eval
        (S.rH A)
    _ = mean (fun x =>
        ((S.ea A).structured f x - S.structured f x) *
          A.eval x) := by
      apply congrArg mean
      funext x
      rw [S.qD f A x]
omit [DecidableEq Ω] in
theorem t9 (u v : Ω → ℝ) :
    mean (fun x => u x * v x) ^ 2 ≤
      mean (fun x => u x ^ 2) * mean (fun x => v x ^ 2) := by
  simpa [mean] using
    (Finset.expect_mul_sq_le_sq_mul_sq
      (Finset.univ : Finset Ω) u v)
theorem tO [Nonempty Ω]
    (A : aW Ω) :
    mean (fun x => A.eval x ^ 2) ≤ 1 := by
  apply sv
  intro x
  rw [A.DG x]
  exact A.At x
theorem rI
    (S : aE Ω) (f : Ω → ℝ)
    (A : aW Ω) :
    (S.ea A).energy f - S.energy f =
      mean (fun x =>
        ((S.ea A).structured f x - S.structured f x) ^ 2) := by
  simpa [energy, structured] using
    mz
      (S.ea A).partition S.partition (S.xd A) f
theorem nq [Nonempty Ω]
    (S : aE Ω) (f : Ω → ℝ)
    (A : aW Ω) :
    S.b2 f A ^ 2 ≤
      (S.ea A).energy f - S.energy f := by
  rw [S.p5 f A]
  let d : Ω → ℝ :=
    fun x => (S.ea A).structured f x - S.structured f x
  have Gw :
      mean (fun x => d x * A.eval x) ^ 2 ≤
        mean (fun x => d x ^ 2) *
          mean (fun x => A.eval x ^ 2) :=
    t9 d A.eval
  have hd : 0 ≤ mean (fun x => d x ^ 2) :=
    o9 fun x => sq_nonneg _
  have hA := tO A
  calc
    mean (fun x =>
        ((S.ea A).structured f x - S.structured f x) *
          A.eval x) ^ 2 =
        mean (fun x => d x * A.eval x) ^ 2 := rfl
    _ ≤ mean (fun x => d x ^ 2) *
        mean (fun x => A.eval x ^ 2) := Gw
    _ ≤ mean (fun x => d x ^ 2) := by
      nlinarith
    _ = (S.ea A).energy f - S.energy f := by
      exact (S.rI f A).symm
theorem rJ [Nonempty Ω]
    (S : aE Ω) (f : Ω → ℝ)
    (A : aW Ω) {ε : ℝ}
    (hε : 0 ≤ ε)
    (ua : ε ≤ |S.b2 f A|) :
    S.energy f + ε ^ 2 ≤ (S.ea A).energy f := by
  have Ga :
      ε ^ 2 ≤ S.b2 f A ^ 2 := by
    rw [sq_le_sq]
    simpa [abs_of_nonneg hε] using ua
  have tN :=
    S.nq f A
  linarith
end aE
end av.ag
end
section
namespace av.ag
open scoped BigOperators
def dc {G : Type*} {r : ℕ}
    (i : Fin r) (x : Fin r → G) : Fin (r - 1) → G := by
  cases r with
  | zero => exact Fin.elim0 i
  | succ n => exact fun j => x (i.succAbove j)
abbrev cU (G : Type*) (r : ℕ) :=
  (i : Fin r) → (Fin (r - 1) → G) → ℝ
def eC {G : Type*} {r : ℕ}
    (u : cU G r) : Prop :=
  (∀ i x, 0 ≤ u i x) ∧ (∀ i x, u i x ≤ 1)
theorem eC.nonneg
    {G : Type*} {r : ℕ} {u : cU G r}
    (hu : eC u) :
    ∀ i x, 0 ≤ u i x :=
  hu.1
theorem eC.le_one
    {G : Type*} {r : ℕ} {u : cU G r}
    (hu : eC u) :
    ∀ i x, u i x ≤ 1 :=
  hu.2
noncomputable def gd
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (f g : G → ℝ) (u : cU G r) : ℝ :=
  mean fun x : Fin r → G =>
    (f (∑ i, x i) - g (∑ i, x i)) *
      ∏ i, u i (dc i x)
def lu
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (f g : G → ℝ) (ε : ℝ) : Prop :=
  ∀ u : cU G r,
    (∀ i x, 0 ≤ u i x) →
    (∀ i x, u i x ≤ 1) →
    |gd r f g u| ≤ ε
@[simp]
theorem BM
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (f : G → ℝ) (u : cU G r) :
    gd r f f u = 0 := by
  simp [gd]
theorem vY
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (f g : G → ℝ) (u : cU G r) :
    gd r g f u = -gd r f g u := by
  calc
    gd r g f u =
        mean (fun x : Fin r → G =>
          (-1 : ℝ) *
            ((f (∑ i, x i) - g (∑ i, x i)) *
              ∏ i, u i (dc i x))) := by
      apply congrArg mean
      funext x
      ring
    _ = (-1 : ℝ) *
        mean (fun x : Fin r → G =>
          (f (∑ i, x i) - g (∑ i, x i)) *
            ∏ i, u i (dc i x)) :=
      k0 _ _
    _ = -gd r f g u := by
      simp [gd]
theorem lu.refl
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (f : G → ℝ) :
    lu r f f 0 := by
  intro u _ _
  simp
theorem lu.symm
    {G : Type*} [Fintype G] [AddCommGroup G]
    {r : ℕ} {f g : G → ℝ} {ε : ℝ}
    (h : lu r f g ε) :
    lu r g f ε := by
  intro u Gz GA
  rw [vY, abs_neg]
  exact h u Gz GA
end av.ag
end
section
namespace av.ag
open scoped BigOperators
def cN {G : Type*} {r : ℕ}
    (u : cU G r) (x : Fin r → G) : ℝ :=
  ∏ i, u i (dc i x)
end av.ag
end
section
namespace av.ag
open scoped Pointwise
def qW {Ω : Type*} (g : Ω → ℝ) : Prop :=
  (∀ x, 0 ≤ g x) ∧ ∀ x, g x ≤ 1
theorem qW.nonneg
    {Ω : Type*} {g : Ω → ℝ} (hg : qW g) :
    ∀ x, 0 ≤ g x :=
  hg.1
theorem qW.le_one
    {Ω : Type*} {g : Ω → ℝ} (hg : qW g) :
    ∀ x, g x ≤ 1 :=
  hg.2
end av.ag
end
section
namespace av.ag
open scoped BigOperators Polynomial
end av.ag
end
section
namespace av.ag
open scoped BigOperators Polynomial
def b6
    {κ : Type*} [Fintype κ]
    (p : κ → ℝ) (b : κ → Bool) : ℝ :=
  ∏ i, if b i then p i else 1 - p i
def hB {κ : Type*} (b : κ → Bool) (i : κ) : ℝ :=
  if b i then 1 else 0
theorem q2
    {κ : Type*} [Fintype κ]
    {p : κ → ℝ}
    (wz : ∀ i, 0 ≤ p i) (GC : ∀ i, p i ≤ 1)
    (b : κ → Bool) :
    0 ≤ b6 p b := by
  apply Finset.prod_nonneg
  intro i _
  by_cases hi : b i
  · simpa [hi] using wz i
  · simp only [hi, Bool.false_eq_true,
      ↓reduceIte]
    linarith [GC i]
theorem r4
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (p : κ → ℝ) :
    ∑ b : κ → Bool, b6 p b = 1 := by
  change
    (∑ b : κ → Bool,
      ∏ i, if b i then p i else 1 - p i) = 1
  calc
    (∑ b : κ → Bool,
        ∏ i, if b i then p i else 1 - p i) =
        ∏ i, ∑ bit : Bool,
          if bit then p i else 1 - p i :=
      (Fintype.prod_sum
        (fun i : κ => fun bit : Bool =>
          if bit then p i else 1 - p i)).symm
    _ = ∏ _i : κ, (1 : ℝ) := by
      apply Fintype.prod_congr
      intro i
      simp
    _ = 1 := by simp
theorem nG
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (p : κ → ℝ) (s : Finset κ) :
    ∑ b : κ → Bool,
        b6 p b *
          ∏ i ∈ s, hB b i =
      ∏ i ∈ s, p i := by
  calc
    (∑ b : κ → Bool,
        b6 p b *
          ∏ i ∈ s, hB b i) =
        ∑ b : κ → Bool,
          ∏ i,
            (if b i then p i else 1 - p i) *
              (if i ∈ s then hB b i else 1) := by
      apply Fintype.sum_congr
      intro b
      have pJ :
          (∏ i ∈ s, hB b i) =
            ∏ i, if i ∈ s then hB b i else 1 :=
        (Fintype.prod_ite_mem s
          (fun i => hB b i)).symm
      rw [b6, pJ]
      rw [← Finset.prod_mul_distrib]
    _ = ∏ i, ∑ bit : Bool,
          (if bit then p i else 1 - p i) *
            (if i ∈ s then
              (if bit then (1 : ℝ) else 0) else 1) :=
      (Fintype.prod_sum
        (fun i : κ => fun bit : Bool =>
          (if bit then p i else 1 - p i) *
            (if i ∈ s then
              (if bit then (1 : ℝ) else 0) else 1))).symm
    _ = ∏ i, if i ∈ s then p i else 1 := by
      apply Fintype.prod_congr
      intro i
      by_cases hi : i ∈ s <;> simp [hi]
    _ = ∏ i ∈ s, p i := by
      exact Fintype.prod_ite_mem s p
theorem nr
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ]
    (p : κ → ℝ) (e : ι ↪ κ) :
    ∑ b : κ → Bool,
        b6 p b *
          ∏ i : ι, hB b (e i) =
      ∏ i : ι, p (e i) := by
  simpa only [Finset.prod_map, Finset.mem_univ, true_and,
    Finset.coe_univ, Function.Embedding.coeFn_mk] using
    (nG p
      (Finset.univ.map e))
abbrev qt (G : Type*) (r : ℕ) :=
  Fin r × (Fin (r - 1) → G)
abbrev b7 (G : Type*) (r : ℕ) :=
  qt G r → Bool
def ck
    {G : Type*} {r : ℕ}
    (b : b7 G r) :
    cU G r :=
  fun i y => hB b ⟨i, y⟩
def cZ
    {G : Type*} {r : ℕ}
    (u : cU G r) :
    qt G r → ℝ :=
  fun q => u q.1 q.2
def mB
    {G : Type*} {r : ℕ} (x : Fin r → G) :
    Fin r ↪ qt G r where
  toFun i := ⟨i, dc i x⟩
  inj' := by
    intro i j h
    exact congrArg Prod.fst h
@[simp]
theorem pK
    {G : Type*} {r : ℕ} (x : Fin r → G) (i : Fin r) :
    mB x i =
      (i, dc i x) :=
  rfl
theorem r5
    {G : Type*} [Fintype G] [DecidableEq G] {r : ℕ}
    (u : cU G r) (x : Fin r → G) :
    cN u x =
      ∑ b : b7 G r,
        b6
            (cZ u) b *
          cN
            (ck b) x := by
  classical
  symm
  simpa [cN, cZ,
    ck,
    pK] using
    (nr
      (cZ u)
      (mB x))
end av.ag
end
section
namespace av.ag
open scoped BigOperators
noncomputable def dL
    {G : Type*} [Fintype G] [DecidableEq G] {r : ℕ}
    (b : b7 G r) :
    aW (Fin r → G) := by
  classical
  exact Finset.univ.filter fun x =>
    ∀ i, b ⟨i, dc i x⟩ = true
@[simp]
theorem tP
    {G : Type*} [Fintype G] [DecidableEq G] {r : ℕ}
    (b : b7 G r) (x : Fin r → G) :
    x ∈ dL b ↔
      ∀ i, b ⟨i, dc i x⟩ = true := by
  simp [dL]
theorem tw
    {G : Type*} [Fintype G] [DecidableEq G] {r : ℕ}
    (b : b7 G r) (x : Fin r → G) :
    (dL b).eval x =
      cN (ck b) x := by
  classical
  by_cases h : ∀ i, b ⟨i, dc i x⟩ = true
  · have hx : x ∈ dL b := by
      simp [dL, h]
    rw [aW.As _ hx]
    unfold cN
    symm
    apply Finset.prod_eq_one
    intro i _
    simp [ck, hB, h i]
  · have hx : x ∉ dL b := by
      simpa [dL] using h
    rw [aW.x7 _ hx]
    obtain ⟨i, hi⟩ := not_forall.mp h
    cases hb : b ⟨i, dc i x⟩ with
    | false =>
        unfold cN
        symm
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        simp [ck,
          hB, hb]
    | true =>
        exact (hi hb).elim
namespace aE
noncomputable def et
    {G : Type*} [Fintype G] [DecidableEq G] {r : ℕ}
    (S : aE (Fin r → G))
    (f : (Fin r → G) → ℝ) (u : cU G r) : ℝ :=
  mean fun x => S.residual f x * cN u x
theorem tx
    {G : Type*} [Fintype G] [DecidableEq G] {r : ℕ}
    (S : aE (Fin r → G))
    (f : (Fin r → G) → ℝ)
    (b : b7 G r) :
    S.et f
        (ck b) =
      S.b2 f (dL b) := by
  unfold et b2
  apply congrArg mean
  funext x
  rw [tw]
theorem qG
    {G : Type*} [Fintype G] [DecidableEq G] {r : ℕ}
    (S : aE (Fin r → G))
    (f : (Fin r → G) → ℝ) (u : cU G r) :
    S.et f u =
      ∑ b : b7 G r,
        b6
            (cZ u) b *
          S.et f
            (ck b) := by
  unfold et
  calc
    mean (fun x : Fin r → G =>
        S.residual f x * cN u x) =
        mean (fun x : Fin r → G =>
          ∑ b : b7 G r,
            b6
                (cZ u) b *
              (S.residual f x *
                cN
                  (ck b) x)) := by
      apply congrArg mean
      funext x
      rw [r5 u x,
        Finset.mul_sum]
      apply Fintype.sum_congr
      intro b
      ring
    _ =
        ∑ b : b7 G r,
          mean (fun x : Fin r → G =>
            b6
                (cZ u) b *
              (S.residual f x *
                cN
                  (ck b) x)) := by
      unfold mean
      exact Finset.expect_sum_comm Finset.univ Finset.univ _
    _ =
        ∑ b : b7 G r,
          b6
              (cZ u) b *
            mean (fun x : Fin r → G =>
              S.residual f x *
                cN
                  (ck b) x) := by
      apply Fintype.sum_congr
      intro b
      exact k0
        (b6
          (cZ u) b) _
    _ = _ := by
      rfl
def q3
    {G : Type*} [Fintype G] [DecidableEq G] {r : ℕ}
    (S : aE (Fin r → G))
    (f : (Fin r → G) → ℝ) (ε : ℝ) : Prop :=
  ∀ u : cU G r,
    eC u →
      |S.et f u| ≤ ε
end aE
end av.ag
end
section
namespace av.ag
open scoped BigOperators
variable {Ω ι : Type*}
  [Fintype Ω] [DecidableEq Ω]
namespace aE
end aE
end av.ag
end
section
namespace av.ag
end av.ag
end
section
namespace av.ag
open scoped BigOperators
abbrev al (k r : ℕ) :=
  Fin r ↪o Fin k
instance AD
    (k r : ℕ) : DecidableEq (al k r) :=
  Function.Injective.decidableEq
    (f := fun e : al k r => (e : Fin r → Fin k))
    DFunLike.coe_injective
def aI
    {G : Type*} {k r : ℕ}
    (e : al k r) (x : Fin k → G) :
    Fin r → G :=
  fun i => x (e i)
abbrev ec
    {k r : ℕ} (e : al k r) :=
  {v : Fin k // v ∉ Set.range e}
noncomputable def pd
    {k r : ℕ} (e : al k r) :
    Fin r ⊕ ec e ≃ Fin k :=
  (Equiv.sumCongr e.toEmbedding.toEquivRange
      (Equiv.refl (ec e))).trans
    (Equiv.sumCompl
      (fun v : Fin k => v ∈ Set.range e))
noncomputable def dM
    {G : Type*} {k r : ℕ} (e : al k r) :
    (Fin k → G) ≃
      ((Fin r → G) × (ec e → G)) :=
  (Equiv.piCongrLeft (fun _ : Fin k => G)
      (pd e)).symm.trans
    (Equiv.sumPiEquivProdPi
      (fun _ : Fin r ⊕ ec e => G))
@[simp]
theorem tQ
    {G : Type*} {k r : ℕ} (e : al k r)
    (x : Fin k → G) :
    (dM e x).1 =
      aI e x := by
  funext i
  simp [dM, pd,
    aI]
  rfl
def h3
    {G : Type*} {k r : ℕ}
    (e : al k r) (x : Fin k → G) :
    ec e → G :=
  fun v => x v.1
@[simp]
theorem nt
    {G : Type*} {k r : ℕ} (e : al k r)
    (y : Fin r → G)
    (z : ec e → G) :
    aI e
        ((dM e).symm (y, z)) = y := by
  rw [← tQ]
  simp
theorem va
    {G : Type*} [Fintype G] {k r : ℕ}
    (e : al k r) (f : (Fin k → G) → ℝ) :
    mean f =
      fq (fun y : Fin r → G =>
        fun z : ec e → G =>
          f ((dM e).symm (y, z))) := by
  calc
    mean f =
        mean (fun p :
          (Fin r → G) × (ec e → G) =>
            f ((dM e).symm p)) := by
      unfold mean
      apply Fintype.expect_equiv
        (dM e)
      intro x
      simp
    _ = _ := by
      simpa only [Prod.eta] using
        (pZ
          (fun y : Fin r → G =>
            fun z : ec e → G =>
              f ((dM e).symm (y, z))))
structure bQ
    (G : Type*) (k r : ℕ) where
  dt : al k r → (Fin r → G) → ℝ
namespace bQ
noncomputable def ko
    {G : Type*} {k r : ℕ}
    (H : bQ G k r)
    (x : Fin k → G) : ℝ :=
  ∏ e : al k r,
    H.dt e (aI e x)
noncomputable def gJ
    {G : Type*} [Fintype G] {k r : ℕ}
    (H : bQ G k r) : ℝ :=
  mean H.ko
end bQ
structure a2
    (G : Type*) (k r : ℕ) where
  edge : al k r → (Fin r → G) → Prop
namespace a2
def fj
    {G : Type*} {k r : ℕ}
    (H : a2 G k r)
    (x : Fin k → G) : Prop :=
  ∀ e, H.edge e (aI e x)
noncomputable def ij
    {G : Type*} [Fintype G] [DecidableEq G] {k r : ℕ}
    (H : a2 G k r) :
    Finset (Fin k → G) := by
  classical
  exact Finset.univ.filter H.fj
@[simp]
theorem kR
    {G : Type*} [Fintype G] [DecidableEq G] {k r : ℕ}
    (H : a2 G k r)
    (x : Fin k → G) :
    x ∈ H.ij ↔ H.fj x := by
  simp [ij]
noncomputable def cD
    {G : Type*} {k r : ℕ}
    (H : a2 G k r) :
    bQ G k r := by
  classical
  exact
    { dt := fun e y =>
        if H.edge e y then 1 else 0 }
theorem jt
    {G : Type*} {k r : ℕ}
    (H : a2 G k r)
    {x : Fin k → G} (hx : H.fj x) :
    H.cD.ko x = 1 := by
  classical
  unfold bQ.ko
  apply Finset.prod_eq_one
  intro e _he
  simp [cD, hx e]
theorem iw
    {G : Type*} {k r : ℕ}
    (H : a2 G k r)
    {x : Fin k → G} (hx : ¬H.fj x) :
    H.cD.ko x = 0 := by
  classical
  unfold bQ.ko
  obtain ⟨e, he⟩ := not_forall.mp hx
  apply Finset.prod_eq_zero (Finset.mem_univ e)
  simp [cD, he]
theorem tz
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (H : a2 G k r) :
    H.cD.gJ =
      (H.ij.card : ℝ) /
        Fintype.card (Fin k → G) := by
  rw [bQ.gJ]
  have CR :
      H.cD.ko =
        aN H.ij := by
    funext x
    by_cases hx : H.fj x
    · rw [H.jt hx,
        cG]
      exact (H.kR x).2 hx
    · rw [H.iw hx,
        cj]
      exact fun jO =>
        hx ((H.kR x).1 jO)
  rw [CR, iM]
abbrev bj
    {G : Type*} [DecidableEq G] (k r : ℕ) :=
  (e : al k r) → Finset (Fin r → G)
def IsCover
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (H : a2 G k r)
    (D : bj (G := G) k r) : Prop :=
  ∀ x, x ∈ H.ij →
    ∃ e, aI e x ∈ D e
noncomputable def eB
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (D : bj (G := G) k r)
    (e : al k r) : ℝ :=
  (D e).card / Fintype.card (Fin r → G)
end a2
def ep (k r : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ c : ℝ, 0 < c ∧
      ∀ (G : Type) [Fintype G] [DecidableEq G] [Nonempty G],
        ∀ H : a2 G k r,
          H.cD.gJ < c →
            ∃ D : a2.bj
                (G := G) k r,
              H.IsCover D ∧
                ∀ e, a2.eB D e ≤ ε
end av.ag
end
section
namespace av.ag
open scoped BigOperators
def gK {k N : ℕ} (a d : ZMod N) (j : Fin k) : ZMod N :=
  a + (j : ZMod N) * d
def cr (k N : ℕ) (f : ZMod N → ℝ)
    (a d : ZMod N) : ℝ :=
  ∏ j : Fin k, f (gK a d j)
noncomputable def eU (k N : ℕ) [NeZero N]
    (f : ZMod N → ℝ) : ℝ :=
  fq (fun a d => cr k N f a d)
theorem qH {k N : ℕ} {f : ZMod N → ℝ}
    (hf : ∀ x, 0 ≤ f x) (a d : ZMod N) :
    0 ≤ cr k N f a d := by
  exact Finset.prod_nonneg fun j _ => hf (gK a d j)
end av.ag
end
section
namespace av.ag
open scoped BigOperators
namespace tS
end tS
end av.ag
end
section
namespace av.ag
open scoped BigOperators
abbrev b9 {k : ℕ} (V : Fin k → Type*) (j : Fin k) :=
  (i : {i : Fin k // i ≠ j}) → V i.1
def bO {k : ℕ} {V : Fin k → Type*}
    (x : (i : Fin k) → V i) (j : Fin k) :
    b9 V j :=
  fun i => x i.1
structure cm {k : ℕ} (V : Fin k → Type*) where
  dt : (j : Fin k) → b9 V j → ℝ
namespace cm
def kp {k : ℕ} {V : Fin k → Type*}
    (H : cm V) (x : (i : Fin k) → V i) : ℝ :=
  ∏ j : Fin k, H.dt j (bO x j)
noncomputable def iT {k : ℕ} {V : Fin k → Type*}
    [∀ i, Fintype (V i)] (H : cm V) : ℝ :=
  mean H.kp
end cm
def f8 (k N : ℕ) (j : Fin k)
    (x : b9 (fun _ : Fin k => ZMod N) j) : ZMod N :=
  ∑ i : {i : Fin k // i ≠ j},
    (((i.1 : ℤ) - (j : ℤ) : ℤ) : ZMod N) * x i
def cS (k N : ℕ)
    (x : Fin k → ZMod N) : ZMod N :=
  ∑ i : Fin k, x i
def cw (k N : ℕ)
    (x : Fin k → ZMod N) : ZMod N :=
  ∑ i : Fin k, (i : ZMod N) * x i
theorem mD (k N : ℕ) (j : Fin k)
    (x : Fin k → ZMod N) :
    f8 k N j (bO x j) =
      cw k N x -
        (j : ZMod N) * cS k N x := by
  classical
  let f : Fin k → ZMod N :=
    fun i => (((i : ℤ) - (j : ℤ) : ℤ) : ZMod N) * x i
  have s5 :=
    Fintype.sum_subtype_add_sum_subtype (fun i : Fin k => i ≠ j) f
  have AG :
      (∑ i : {i : Fin k // ¬i ≠ j}, f i.1) = 0 := by
    apply Finset.sum_eq_zero
    intro i
    simp only [Finset.mem_univ, forall_const]
    have hij : i.1 = j := not_ne_iff.mp i.2
    rw [hij]
    simp [f]
  have hsum : (∑ i : {i : Fin k // i ≠ j}, f i.1) = ∑ i : Fin k, f i := by
    rw [AG, add_zero] at s5
    exact s5
  rw [f8]
  change (∑ i : {i : Fin k // i ≠ j}, f i.1) =
    cw k N x -
      (j : ZMod N) * cS k N x
  rw [hsum]
  simp only [cw, cS, f]
  push_cast
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib, Finset.mul_sum]
def rK (k N : ℕ) (f : ZMod N → ℝ) :
    cm (fun _ : Fin k => ZMod N) where
  dt j x := f (f8 k N j x)
theorem r6
    (k N : ℕ) (f : ZMod N → ℝ)
    (x : Fin k → ZMod N) :
    (rK k N f).kp x =
      cr k N f
        (cw k N x)
        (-cS k N x) := by
  apply Finset.prod_congr rfl
  intro j _
  change
    f (f8 k N j (bO x j)) =
      f (gK
        (cw k N x)
        (-cS k N x) j)
  congr 1
  rw [mD]
  simp [gK]
  ring
end av.ag
end
section
namespace av.ag
open scoped BigOperators
def p6 (r N : ℕ) (y : Fin r → ZMod N) : ZMod N :=
  ∑ i : Fin r, y i
def i8 (r N : ℕ) (y : Fin r → ZMod N) : ZMod N :=
  ∑ i : Fin r, (i.succ.succ : ZMod N) * y i
def dj (r N : ℕ) (a d : ZMod N)
    (y : Fin r → ZMod N) : Fin (r + 2) → ZMod N :=
  Fin.cases
    (i8 r N y - a - d - p6 r N y)
    (Fin.cases (a - i8 r N y) y)
@[simp]
theorem tb (r N : ℕ) (a d : ZMod N)
    (y : Fin r → ZMod N) :
    dj r N a d y 0 =
      i8 r N y - a - d - p6 r N y :=
  rfl
@[simp]
theorem tA (r N : ℕ) (a d : ZMod N)
    (y : Fin r → ZMod N) :
    dj r N a d y 1 =
      a - i8 r N y :=
  rfl
@[simp]
theorem q4 (r N : ℕ)
    (a d : ZMod N) (y : Fin r → ZMod N) (i : Fin r) :
    dj r N a d y i.succ.succ = y i :=
  rfl
theorem mE (r N : ℕ)
    (x : Fin (r + 2) → ZMod N) :
    cS (r + 2) N x =
      x 0 + x 1 +
        p6 r N (fun i => x i.succ.succ) := by
  simp [cS, p6, Fin.sum_univ_succ,
    add_assoc]
theorem hJ (r N : ℕ)
    (x : Fin (r + 2) → ZMod N) :
    cw (r + 2) N x =
      x 1 + i8 r N (fun i => x i.succ.succ) := by
  simp [cw, i8,
    Fin.sum_univ_succ]
@[simp]
theorem pL (r N : ℕ)
    (a d : ZMod N) (y : Fin r → ZMod N) :
    cS (r + 2) N
        (dj r N a d y) = -d := by
  rw [mE]
  simp
  ring
@[simp]
theorem oU (r N : ℕ)
    (a d : ZMod N) (y : Fin r → ZMod N) :
    cw (r + 2) N
        (dj r N a d y) = a := by
  rw [hJ]
  simp
def yG (r N : ℕ) :
    (Fin (r + 2) → ZMod N) ≃
      (ZMod N × ZMod N) × (Fin r → ZMod N) where
  toFun x :=
    ((cw (r + 2) N x,
      -cS (r + 2) N x),
      fun i => x i.succ.succ)
  invFun y := dj r N y.1.1 y.1.2 y.2
  left_inv x := by
    funext i
    refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun _ => rfl) i) i
    · change
        dj r N
            (cw (r + 2) N x)
            (-cS (r + 2) N x)
            (fun i => x i.succ.succ) 0 =
          x 0
      rw [tb,
        hJ,
        mE]
      ring
    · change
        dj r N
            (cw (r + 2) N x)
            (-cS (r + 2) N x)
            (fun i => x i.succ.succ) 1 =
          x 1
      rw [tA,
        hJ]
      ring
  right_inv y := by
    rcases y with ⟨⟨a, d⟩, tail⟩
    apply Prod.ext
    · apply Prod.ext
      · change
          cw (r + 2) N
              (dj r N a d tail) =
            a
        exact oU r N a d tail
      · change
          -cS (r + 2) N
              (dj r N a d tail) =
            d
        rw [pL]
        simp
    · funext i
      change dj r N a d tail i.succ.succ = tail i
      exact q4 r N a d tail i
theorem tT {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : α → ℝ) (g : β → ℝ)
    (h : ∀ x, f x = g (e x)) :
    mean f = mean g := by
  exact Fintype.expect_equiv e f g h
theorem y7 {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β → ℝ) :
    mean (fun p : α × β => f p.1 p.2) = fq f := by
  simpa [mean, fq] using
    (Finset.expect_product'
      (Finset.univ : Finset α) (Finset.univ : Finset β) f)
theorem zh {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty β] (f : α → ℝ) :
    mean (fun p : α × β => f p.1) = mean f := by
  calc
    mean (fun p : α × β => f p.1) =
        fq (fun a (_ : β) => f a) := by
      exact y7 (fun a (_ : β) => f a)
    _ = mean f := by
      simp [fq]
theorem mF
    (r N : ℕ) [NeZero N] (f : ZMod N → ℝ) :
    (rK (r + 2) N f).iT =
      eU (r + 2) N f := by
  rw [cm.iT, eU]
  calc
    mean (rK (r + 2) N f).kp =
        mean (fun x : Fin (r + 2) → ZMod N =>
          cr (r + 2) N f
            (cw (r + 2) N x)
            (-cS (r + 2) N x)) := by
      apply congrArg mean
      funext x
      exact r6 (r + 2) N f x
    _ =
        mean (fun y :
            (ZMod N × ZMod N) × (Fin r → ZMod N) =>
          cr (r + 2) N f y.1.1 y.1.2) := by
      apply tT (yG r N)
      intro x
      rfl
    _ =
        mean (fun p : ZMod N × ZMod N =>
          cr (r + 2) N f p.1 p.2) := by
      exact zh
        (fun p : ZMod N × ZMod N =>
          cr (r + 2) N f p.1 p.2)
    _ =
        fq (fun a d =>
          cr (r + 2) N f a d) := by
      exact y7
        (fun a d => cr (r + 2) N f a d)
end av.ag
end
section
namespace av.ag
open scoped BigOperators
end av.ag
end
section
namespace av.ag
open scoped BigOperators
noncomputable def finSuccAboveEquiv {n : ℕ} (j : Fin (n + 1)) :
    Fin n ≃ {i : Fin (n + 1) // i ≠ j} :=
  Equiv.ofBijective
    (fun t : Fin n => ⟨j.succAbove t, Fin.succAbove_ne j t⟩)
    ⟨by
      intro a b hab
      apply Fin.succAbove_right_injective
      exact congrArg Subtype.val hab,
    by
      intro i
      obtain ⟨t, ht⟩ := Fin.exists_succAbove_eq i.2
      exact ⟨t, Subtype.ext ht⟩⟩
noncomputable def cf
    {n : ℕ} {G : Type*}
    (j : Fin (n + 1))
    (y : Fin n → G) :
    b9 (fun _ : Fin (n + 1) => G) j :=
  fun i => y ((finSuccAboveEquiv j).symm i)
@[simp]
theorem xh
    {n : ℕ} {G : Type*}
    (j : Fin (n + 1))
    (y : Fin n → G)
    (t : Fin n) :
    cf j y
        (finSuccAboveEquiv j t) =
      y t := by
  simp [cf]
end av.ag
end
section
namespace av.ag
open scoped BigOperators
end av.ag
end
section
namespace av.ag
open scoped BigOperators
end av.ag
end
section
namespace av.ag
open scoped BigOperators
end av.ag
end
section
namespace av.ag
open scoped BigOperators
end av.ag
end
section
namespace av.ag
open scoped BigOperators
abbrev eg
    (G : Type*) [Fintype G] [DecidableEq G]
    (k r : ℕ) :=
  (e : al k r) →
    aE (Fin r → G)
end av.ag
end
section
namespace av.ag
namespace cb
end cb
end av.ag
end
section
namespace av.ag
open scoped BigOperators
structure aM {k : ℕ} (V : Fin k → Type*) where
  edge : (j : Fin k) → b9 V j → Prop
namespace aM
noncomputable def edgeFinset {k : ℕ} {V : Fin k → Type*}
    [∀ i, Fintype (V i)]
    (H : aM V) (j : Fin k) :
    Finset (b9 V j) := by
  classical
  exact Finset.univ.filter (H.edge j)
@[simp]
theorem mem_edgeFinset {k : ℕ} {V : Fin k → Type*}
    [∀ i, Fintype (V i)]
    (H : aM V) (j : Fin k)
    (x : b9 V j) :
    x ∈ H.edgeFinset j ↔ H.edge j x := by
  classical
  simp [edgeFinset]
noncomputable def ff {k : ℕ} {V : Fin k → Type*}
    [∀ i, Fintype (V i)]
    (H : aM V) :
    Finset ((i : Fin k) → V i) := by
  classical
  exact Finset.univ.filter fun x => ∀ j, H.edge j (bO x j)
@[simp]
theorem nC {k : ℕ} {V : Fin k → Type*}
    [∀ i, Fintype (V i)]
    (H : aM V) (x : (i : Fin k) → V i) :
    x ∈ H.ff ↔
      ∀ j, H.edge j (bO x j) := by
  classical
  simp [ff]
noncomputable def cD {k : ℕ} {V : Fin k → Type*}
    (H : aM V) : cm V := by
  classical
  exact
    { dt := fun j x => if H.edge j x then 1 else 0 }
@[simp]
theorem r7 {k : ℕ}
    {V : Fin k → Type*} (H : aM V)
    {j : Fin k} {x : b9 V j}
    (hx : H.edge j x) :
    H.cD.dt j x = 1 := by
  classical
  simp [cD, hx]
@[simp]
theorem k2 {k : ℕ}
    {V : Fin k → Type*} (H : aM V)
    {j : Fin k} {x : b9 V j}
    (hx : ¬H.edge j x) :
    H.cD.dt j x = 0 := by
  classical
  simp [cD, hx]
theorem pz {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    [∀ i, DecidableEq (V i)]
    (H : aM V) (x : (i : Fin k) → V i) :
    H.cD.kp x =
      aN H.ff x := by
  classical
  by_cases hx : x ∈ H.ff
  · have tZ :
        ∀ j, H.edge j (bO x j) :=
      (H.nC x).mp hx
    simp [cm.kp, cD,
      aN, hx, tZ]
  · have hnot :
        ¬∀ j, H.edge j (bO x j) := by
      simpa using hx
    push Not at hnot
    obtain ⟨j, hj⟩ := hnot
    have hzero :
        ∏ i : Fin k,
            H.cD.dt i (bO x i) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      exact k2 H hj
    rw [cm.kp, hzero]
    exact (cj hx).symm
theorem p8 {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    (H : aM V) :
    H.cD.iT =
      (H.ff.card : ℝ) /
        Fintype.card ((i : Fin k) → V i) := by
  classical
  rw [cm.iT]
  have CR :
      H.cD.kp =
        aN H.ff := by
    funext x
    exact pz H x
  rw [CR, iM]
def gR {k : ℕ} {V : Fin k → Type*}
    [∀ i, Fintype (V i)]
    (H : aM V)
    (bG : (j : Fin k) → Finset (b9 V j)) : Prop :=
  ∀ x ∈ H.ff,
    ∃ j, bO x j ∈ bG j
end aM
end av.ag
end
section
namespace av.ag
open scoped BigOperators
namespace aM
abbrev bj {k : ℕ} (V : Fin k → Type*) :=
  (j : Fin k) → Finset (b9 V j)
def fh {k : ℕ} {V : Fin k → Type*}
    (bG : bj V) : ℕ :=
  ∑ j, (bG j).card
def ik {k : ℕ} (V : Fin k → Type*)
    [∀ i, Fintype (V i)] : ℕ :=
  ∑ j, Fintype.card (b9 V j)
noncomputable def iU {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    (bG : bj V) (j : Fin k) : ℝ :=
  ((bG j).card : ℝ) /
    Fintype.card (b9 V j)
noncomputable def eO {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    (bG : bj V) : ℝ :=
  (fh bG : ℝ) / (ik V : ℝ)
end aM
end av.ag
end
section
namespace av.ag
open scoped BigOperators
namespace aE
end aE
end av.ag
end
section
namespace av.ag
namespace a2
end a2
namespace cb
end cb
end av.ag
end
section
namespace av.ag
open scoped BigOperators
def b3
    {G : Type*} {j : ℕ}
    (i : Fin (j + 1)) (x : Fin (j + 1) → G) :
    Fin j → G :=
  fun q => x (i.succAbove q)
def dH
    {k j : ℕ}
    (e : al k (j + 1)) (i : Fin (j + 1)) :
    al k j :=
  (Fin.succAboveOrderEmb i).trans e
@[simp]
theorem w3
    {G : Type*} {k j : ℕ}
    (e : al k (j + 1)) (i : Fin (j + 1))
    (x : Fin k → G) :
    aI (dH e i) x =
      b3 i (aI e x) :=
  rfl
abbrev af
    (G : Type*) [Fintype G] [DecidableEq G]
    (k j : ℕ) :=
  (e : al k j) → ab (Fin j → G)
def aP
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (aQ an : af G k j) : Prop :=
  ∀ e, aQ e ≤ an e
namespace aP
theorem refl
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : af G k j) :
    aP P P :=
  fun _ => le_rfl
theorem trans
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    {P Q R : af G k j}
    (s8 : aP P Q)
    (GD : aP Q R) :
    aP P R :=
  fun e => le_trans (s8 e) (GD e)
end aP
def fO
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : af G k j)
    (e : al k (j + 1)) (i : Fin (j + 1)) :
    ab (Fin (j + 1) → G) :=
  ab.pullback (b3 i)
    (P (dH e i))
def au
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : af G k j)
    (e : al k (j + 1)) :
    ab (Fin (j + 1) → G) :=
  ab.kQ
    (Finset.univ : Finset (Fin (j + 1)))
    (fO P e)
theorem pA
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : af G k j)
    (e : al k (j + 1)) (i : Fin (j + 1)) :
    au P e ≤
      fO P e i := by
  exact ab.vt
    (fO P e)
    (Finset.mem_univ i)
theorem gB
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    {aQ an : af G k j}
    (ya : aP aQ an)
    (e : al k (j + 1)) :
    au aQ e ≤
      au an e := by
  unfold au
  apply ab.w1.mpr
  intro i _
  exact le_trans
    (pA aQ e i)
    (ab.zf (b3 i)
      (ya (dH e i)))
theorem jC
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : af G k j)
    (e : al k (j + 1))
    (x y : Fin (j + 1) → G) :
    y ∈ (au P e).part x ↔
      ∀ i : Fin (j + 1),
        b3 i y ∈
          (P (dH e i)).part
            (b3 i x) := by
  rw [au,
    ab.qi]
  simp only [Finset.mem_univ, forall_const,
    fO,
    ab.gb]
noncomputable def fJ
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : af G k j)
    (e : al k (j + 1))
    (x : Fin (j + 1) → G) :
    (au P e).parts :=
  ⟨(au P e).part x,
    (au P e).part_mem.2
      (Finset.mem_univ x)⟩
noncomputable def eJ
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : af G k j)
    (e : al k (j + 1))
    (f : (Fin (j + 1) → G) → ℝ) :
    (Fin (j + 1) → G) → ℝ :=
  aq (au P e) f
structure aa
    (G : Type*) [Fintype G] [DecidableEq G]
    (k r : ℕ) where
  partition :
    (j : Fin (r + 1)) →
      (e : al k j.1) →
        ab (Fin j.1 → G)
namespace aa
def Dy
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : aa G k r)
    (j : ℕ) (hj : j ≤ r) :
    af G k j :=
  C.partition ⟨j, Nat.lt_succ_iff.mpr hj⟩
def boundary
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r j : ℕ}
    (C : aa G k r)
    (hj : j < r)
    (e : al k (j + 1)) :
    ab (Fin (j + 1) → G) :=
  au (C.Dy j (Nat.le_of_lt hj)) e
def db
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (aQ an : aa G k r) : Prop :=
  ∀ j e, aQ.partition j e ≤ an.partition j e
theorem db.refl
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : aa G k r) :
    C.db C :=
  fun _ _ => le_rfl
theorem db.trans
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C D E : aa G k r}
    (GF : C.db D) (GG : D.db E) :
    C.db E :=
  fun j e => le_trans (GF j e) (GG j e)
end aa
end av.ag
end
section
namespace av.ag
open scoped BigOperators
def aB
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (Q : ab Ω) (a : Q.parts) :
    Ω → ℝ :=
  aN a.1
@[simp]
theorem dg
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (Q : ab Ω) (a : Q.parts) {x : Ω}
    (hx : x ∈ a.1) :
    aB Q a x = 1 :=
  cG hx
@[simp]
theorem c0
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (Q : ab Ω) (a : Q.parts) {x : Ω}
    (hx : x ∉ a.1) :
    aB Q a x = 0 :=
  cj hx
theorem ng
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (Q : ab Ω) (a : Q.parts) (x : Ω) :
    0 ≤ aB Q a x := by
  by_cases hx : x ∈ a.1 <;> simp [hx]
theorem r8
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (Q : ab Ω) (a : Q.parts) (x : Ω) :
    aB Q a x ≤ 1 := by
  by_cases hx : x ∈ a.1 <;> simp [hx]
theorem kS
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (Q : ab Ω) (a : Q.parts) (x : Ω) :
    aB Q a x ^ 2 =
      aB Q a x := by
  by_cases hx : x ∈ a.1 <;> simp [hx]
theorem tC
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (Q : ab Ω) (x : Ω) :
    ∑ a : Q.parts, aB Q a x = 1 := by
  classical
  let ax : Q.parts :=
    ⟨Q.part x, Q.part_mem.2 (Finset.mem_univ x)⟩
  rw [Finset.sum_eq_single ax]
  · exact dg Q ax
      (Q.mem_part (Finset.mem_univ x))
  · intro b _hb GH
    apply c0
    intro GI
    have heq :
        b = ax := by
      apply Subtype.ext
      exact Q.eq_of_mem_parts b.2 ax.2 GI
        (Q.mem_part (Finset.mem_univ x))
    exact GH heq
  · intro B9
    exact (B9 (Finset.mem_univ ax)).elim
noncomputable def dQ
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P Q : ab Ω) : ℝ :=
  ∑ a : Q.parts,
    av.ag.cq P
      (aB Q a)
theorem tD
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P Q : ab Ω) :
    0 ≤ dQ P Q := by
  unfold dQ
  exact Finset.sum_nonneg fun a _ =>
    av.ag.uL P
      (aB Q a)
theorem tE
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    (P Q : ab Ω) :
    dQ P Q ≤ 1 := by
  unfold dQ
  calc
    (∑ a : Q.parts,
        av.ag.cq P
          (aB Q a)) ≤
        ∑ a : Q.parts,
          mean (fun x =>
            aB Q a x ^ 2) := by
      apply Finset.sum_le_sum
      intro a _
      exact tv P
        (aB Q a)
    _ =
        ∑ a : Q.parts,
          mean (aB Q a) := by
      apply Finset.sum_congr rfl
      intro a _
      apply congrArg mean
      funext x
      exact kS Q a x
    _ =
        mean (fun x =>
          ∑ a : Q.parts, aB Q a x) := by
      unfold mean
      exact
        (Finset.expect_sum_comm
          (Finset.univ : Finset Ω)
          (Finset.univ : Finset Q.parts)
          (fun x a => aB Q a x)).symm
    _ = mean (fun _x : Ω => (1 : ℝ)) := by
      apply congrArg mean
      funext x
      exact tC Q x
    _ = 1 := ml 1
theorem uc
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {P R : ab Ω} (En : P ≤ R)
    (Q : ab Ω) :
    dQ R Q ≤ dQ P Q := by
  unfold dQ
  apply Finset.sum_le_sum
  intro a _
  exact oy P R En
    (aB Q a)
theorem pe
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {P R : ab Ω} (En : P ≤ R)
    (Q : ab Ω) :
    dQ P Q - dQ R Q =
      ∑ a : Q.parts,
        mean (fun x =>
          (aq P (aB Q a) x -
            aq R (aB Q a) x) ^ 2) := by
  unfold dQ
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  exact mz P R En
    (aB Q a)
noncomputable def bI
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : af G k j)
    (e : al k (j + 1))
    (upper : ab (Fin (j + 1) → G)) : ℝ :=
  dQ (au lower e) upper
theorem ud
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : af G k j)
    (e : al k (j + 1))
    (upper : ab (Fin (j + 1) → G)) :
    0 ≤ bI lower e upper :=
  tD _ _
theorem ue
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (lower : af G k j)
    (e : al k (j + 1))
    (upper : ab (Fin (j + 1) → G)) :
    bI lower e upper ≤ 1 :=
  tE _ _
theorem m1
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    {aQ an : af G k j}
    (ya : aP aQ an)
    (e : al k (j + 1))
    (upper : ab (Fin (j + 1) → G)) :
    bI an e upper ≤
      bI aQ e upper := by
  exact uc
    (gB ya e) upper
theorem pP
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    {aQ an : af G k j}
    (ya : aP aQ an)
    (e : al k (j + 1))
    (upper : ab (Fin (j + 1) → G)) :
    bI aQ e upper -
        bI an e upper =
      ∑ a : upper.parts,
        mean (fun x =>
          (eJ aQ e
                (aB upper a) x -
            eJ an e
                (aB upper a) x) ^ 2) := by
  exact pe
    (gB ya e) upper
end av.ag
end
section
namespace av.ag
open scoped BigOperators
abbrev aS
    (G : Type*) (j : ℕ) :=
  (i : Fin (j + 1)) → (Fin j → G) → Bool
noncomputable def du
    {G : Type*} [Fintype G] [DecidableEq G]
    {j : ℕ}
    (b : aS G j)
    (i : Fin (j + 1)) :
    aW (Fin j → G) := by
  classical
  exact Finset.univ.filter fun z => b i z = true
@[simp]
theorem rq
    {G : Type*} [Fintype G] [DecidableEq G]
    {j : ℕ}
    (b : aS G j)
    (i : Fin (j + 1)) (z : Fin j → G) :
    z ∈ du b i ↔
      b i z = true := by
  simp [du]
noncomputable def bL
    {G : Type*} [Fintype G] [DecidableEq G]
    {j : ℕ}
    (b : aS G j) :
    aW (Fin (j + 1) → G) := by
  classical
  exact Finset.univ.filter fun x =>
    ∀ i, b i (b3 i x) = true
@[simp]
theorem jh
    {G : Type*} [Fintype G] [DecidableEq G]
    {j : ℕ}
    (b : aS G j)
    (x : Fin (j + 1) → G) :
    x ∈ bL b ↔
      ∀ i, b i (b3 i x) = true := by
  simp [bL]
noncomputable def ej
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (e : al k (j + 1))
    (b : aS G j)
    (g : al k j) :
    Finset (aW (Fin j → G)) := by
  classical
  exact
    ((Finset.univ : Finset (Fin (j + 1))).filter
      (fun i => dH e i = g)).image
      (fun i => du b i)
theorem iV
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (e : al k (j + 1))
    (b : aS G j)
    (i : Fin (j + 1)) :
    du b i ∈
      ej e b
        (dH e i) := by
  classical
  apply Finset.mem_image.mpr
  refine ⟨i, ?_, rfl⟩
  simp
noncomputable def bR
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : af G k j)
    (e : al k (j + 1))
    (b : aS G j) :
    af G k j :=
  fun g =>
    ab.join (P g)
      (ab.generatedBy
        (ej e b g))
theorem dW
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : af G k j)
    (e : al k (j + 1))
    (b : aS G j) :
    aP
      (bR P e b) P := by
  intro g
  exact ab.t8 _ _
theorem j8
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : af G k j)
    (e : al k (j + 1))
    (b : aS G j)
    (i : Fin (j + 1)) :
    bR P e b
          (dH e i) ≤
      ab.generatedBy
        ({du b i} :
          Finset (Finset (Fin j → G))) := by
  apply le_trans (ab.vO _ _)
  apply ab.vu
  intro A hA
  have FV : A = du b i := by
    simpa using hA
  subst A
  exact
    iV
      e b i
theorem ic
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : af G k j)
    (e : al k (j + 1))
    (b : aS G j)
    (i : Fin (j + 1))
    (x y : Fin j → G)
    (hy :
      y ∈
        (bR P e b
          (dH e i)).part x) :
    b i x = b i y := by
  have x5 :
      y ∈
        (ab.generatedBy
          ({du b i} :
            Finset (Finset (Fin j → G)))).part x :=
    ab.gj
      (j8
        P e b i) x hy
  have ox :=
    (ab.fI
      ({du b i} :
        Finset (Finset (Fin j → G))) x y).1 x5
      (du b i) (by simp)
  cases GJ : b i x <;> cases GK : b i y <;>
    simp [rq, GJ, GK] at ox ⊢
theorem kq
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : af G k j)
    (e : al k (j + 1))
    (b : aS G j) :
    au
        (bR P e b) e ≤
      ab.generatedBy
        ({bL b} :
          Finset (Finset (Fin (j + 1) → G))) := by
  rw [ab.pH]
  intro x y hy
  rw [ab.fI]
  intro A hA
  have FV : A = bL b := by
    simpa using hA
  subst A
  rw [jh,
    jh]
  have rk :=
    (jC
      (bR P e b)
      e x y).1 hy
  constructor
  · intro hx i
    have CS :=
      ic
        P e b i
        (b3 i x)
        (b3 i y)
        (rk i)
    exact CS ▸ hx i
  · intro yb i
    have CS :=
      ic
        P e b i
        (b3 i x)
        (b3 i y)
        (rk i)
    exact CS.symm ▸ yb i
theorem m2
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : af G k j)
    (e : al k (j + 1))
    (b : aS G j) :
      au
        (bR P e b) e ≤
      ((⟨au P e⟩ :
          aE (Fin (j + 1) → G)).ea
        (bL b)).partition := by
  apply ab.Ar.mpr
  constructor
  · exact gB
      (dW P e b) e
  · exact kq
      P e b
noncomputable def aH
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : af G k j)
    (upper : af G k (j + 1)) : ℝ :=
  ∑ e : al k (j + 1),
    bI lower e (upper e)
theorem nh
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : af G k j)
    (upper : af G k (j + 1)) :
    0 ≤ aH lower upper := by
  unfold aH
  exact Finset.sum_nonneg fun e _ =>
    ud lower e (upper e)
theorem mG
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (lower : af G k j)
    (upper : af G k (j + 1)) :
    aH lower upper ≤
      (Fintype.card (al k (j + 1)) : ℝ) := by
  unfold aH
  calc
    (∑ e : al k (j + 1),
        bI lower e (upper e)) ≤
        ∑ _e : al k (j + 1), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro e _
      exact ue lower e (upper e)
    _ = (Fintype.card (al k (j + 1)) : ℝ) := by
      simp
theorem te
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    {aQ an : af G k j}
    (ya : aP aQ an)
    (upper : af G k (j + 1)) :
    aH an upper ≤
      aH aQ upper := by
  unfold aH
  apply Finset.sum_le_sum
  intro e _
  exact m1 ya e (upper e)
theorem lO
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (lower : af G k j)
    (upper : af G k (j + 1))
    (e : al k (j + 1))
    (a : (upper e).parts)
    (b : aS G j)
    {ε : ℝ} (hε : 0 ≤ ε)
    (ua :
      ε ≤
        |aE.b2
          (⟨au lower e⟩ :
            aE (Fin (j + 1) → G))
            (aB (upper e) a)
            (bL b)|) :
    aH lower upper + ε ^ 2 ≤
      aH
        (bR lower e b)
        upper := by
  classical
  let aQ :=
    bR lower e b
  let S : aE (Fin (j + 1) → G) :=
    ⟨au lower e⟩
  have tN :
      S.energy (aB (upper e) a) + ε ^ 2 ≤
        (S.ea (bL b)).energy
          (aB (upper e) a) :=
    S.rJ
      (aB (upper e) a)
      (bL b) hε ua
  have CT :
      au aQ e ≤
        (S.ea (bL b)).partition := by
    exact m2
      lower e b
  have Fc :
      bI lower e (upper e) + ε ^ 2 ≤
        bI aQ e (upper e) := by
    unfold bI dQ
    let U : Finset (upper e).parts := Finset.univ
    have FC : a ∈ U := by simp [U]
    have z0 :
        ∑ c ∈ U.erase a,
            cq
              (au lower e)
              (aB (upper e) c) ≤
          ∑ c ∈ U.erase a,
            cq
              (au aQ e)
              (aB (upper e) c) := by
      apply Finset.sum_le_sum
      intro c _
      exact oy
        (au aQ e)
        (au lower e)
        (gB
          (dW
            lower e b) e)
        (aB (upper e) c)
    have DJ :
        cq
              (au lower e)
              (aB (upper e) a) +
            ε ^ 2 ≤
          cq
              (au aQ e)
              (aB (upper e) a) := by
      exact le_trans tN
        (oy
          (au aQ e)
          (S.ea (bL b)).partition
          CT
          (aB (upper e) a))
    change
      (∑ c ∈ U,
          cq
            (au lower e)
            (aB (upper e) c)) +
          ε ^ 2 ≤
        ∑ c ∈ U,
          cq
            (au aQ e)
            (aB (upper e) c)
    calc
      (∑ c ∈ U,
          cq
            (au lower e)
            (aB (upper e) c)) +
            ε ^ 2 =
          (∑ c ∈ U.erase a,
            cq
              (au lower e)
              (aB (upper e) c)) +
            (cq
              (au lower e)
              (aB (upper e) a) +
              ε ^ 2) := by
        rw [← Finset.sum_erase_add U _ FC]
        ring
      _ ≤
          (∑ c ∈ U.erase a,
            cq
              (au aQ e)
              (aB (upper e) c)) +
            cq
              (au aQ e)
              (aB (upper e) a) :=
        add_le_add z0 DJ
      _ =
          ∑ c ∈ U,
            cq
              (au aQ e)
              (aB (upper e) c) :=
        Finset.sum_erase_add U _ FC
  unfold aH
  let E : Finset (al k (j + 1)) := Finset.univ
  have FD : e ∈ E := by simp [E]
  have AL :
      ∑ d ∈ E.erase e,
          bI lower d (upper d) ≤
        ∑ d ∈ E.erase e,
          bI aQ d (upper d) := by
    apply Finset.sum_le_sum
    intro d _
    exact m1
      (dW
        lower e b)
      d (upper d)
  change
    (∑ d ∈ E, bI lower d (upper d)) +
        ε ^ 2 ≤
      ∑ d ∈ E, bI aQ d (upper d)
  calc
    (∑ d ∈ E, bI lower d (upper d)) +
          ε ^ 2 =
        (∑ d ∈ E.erase e,
          bI lower d (upper d)) +
        (bI lower e (upper e) + ε ^ 2) := by
      rw [← Finset.sum_erase_add E _ FD]
      ring
    _ ≤
        (∑ d ∈ E.erase e,
          bI aQ d (upper d)) +
        bI aQ e (upper e) :=
      add_le_add AL Fc
    _ =
        ∑ d ∈ E, bI aQ d (upper d) :=
      Finset.sum_erase_add E _ FD
def a3
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : af G k j)
    (upper : af G k (j + 1))
    (ε : ℝ) : Prop :=
  ∀ (e : al k (j + 1))
      (a : (upper e).parts)
      (b : aS G j),
    |aE.b2
        (⟨au lower e⟩ :
          aE (Fin (j + 1) → G))
        (aB (upper e) a)
        (bL b)| ≤ ε
theorem m3
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : af G k j)
    (upper : af G k (j + 1))
    {ε : ℝ}
    (h : ¬a3 lower upper ε) :
    ∃ (e : al k (j + 1))
        (a : (upper e).parts)
        (b : aS G j),
      ε <
        |aE.b2
          (⟨au lower e⟩ :
            aE (Fin (j + 1) → G))
          (aB (upper e) a)
          (bL b)| := by
  unfold a3 at h
  obtain ⟨e, he⟩ := not_forall.mp h
  obtain ⟨a, ha⟩ := not_forall.mp he
  obtain ⟨b, hb⟩ := not_forall.mp ha
  exact ⟨e, a, b, lt_of_not_ge hb⟩
structure tf
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : af G k j)
    (upper : af G k (j + 1))
    (ε : ℝ) where
  face : al k (j + 1)
  atom : (upper face).parts
  x9 : aS G j
  xf :
    ε <
      |aE.b2
        (⟨au lower face⟩ :
          aE (Fin (j + 1) → G))
        (aB (upper face) atom)
        (bL x9)|
noncomputable def fP
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : af G k j)
    (upper : af G k (j + 1))
    (ε : ℝ)
    (h : ¬a3 lower upper ε) :
    tf lower upper ε := by
  classical
  let hex :=
    m3
      lower upper h
  let e := Classical.choose hex
  let he := Classical.choose_spec hex
  let a := Classical.choose he
  let ha := Classical.choose_spec he
  let b := Classical.choose ha
  have x8 := Classical.choose_spec ha
  exact ⟨e, a, b, x8⟩
noncomputable def cH
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : af G k j)
    (upper : af G k (j + 1))
    (ε : ℝ) :
    af G k j := by
  classical
  exact
    if h : a3 lower upper ε then
      lower
    else
      let W :=
        fP lower upper ε h
      bR
        lower W.face W.x9
theorem oC
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : af G k j)
    (upper : af G k (j + 1))
    (ε : ℝ) :
    aP
      (cH lower upper ε)
      lower := by
  classical
  by_cases h :
      a3 lower upper ε
  · simpa [cH, h] using
      aP.refl lower
  · simp only [cH, dif_neg h]
    let W :=
      fP lower upper ε h
    exact dW
      lower W.face W.x9
theorem lg
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (lower : af G k j)
    (upper : af G k (j + 1))
    {ε : ℝ} (hε : 0 ≤ ε)
    (h : ¬a3 lower upper ε) :
    aH lower upper + ε ^ 2 ≤
      aH
        (cH lower upper ε)
        upper := by
  classical
  simp only [cH, dif_neg h]
  let W :=
    fP lower upper ε h
  exact lO
    lower upper W.face W.atom W.x9 hε
    (le_of_lt W.xf)
noncomputable def aX
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : af G k j)
    (upper : af G k (j + 1))
    (ε : ℝ) :
    ℕ → af G k j
  | 0 => lower
  | n + 1 =>
      cH
        (aX lower upper ε n)
        upper ε
@[simp]
theorem wD
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : af G k j)
    (upper : af G k (j + 1))
    (ε : ℝ) :
    aX lower upper ε 0 =
      lower :=
  rfl
@[simp]
theorem jR
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : af G k j)
    (upper : af G k (j + 1))
    (ε : ℝ) (n : ℕ) :
    aX lower upper ε (n + 1) =
      cH
        (aX lower upper ε n)
        upper ε :=
  rfl
theorem oV
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : af G k j)
    (upper : af G k (j + 1))
    (ε : ℝ) (n : ℕ) :
    aP
      (aX lower upper ε n)
      lower := by
  induction n with
  | zero =>
      exact aP.refl lower
  | succ n ih =>
      exact aP.trans
        (oC
          (aX lower upper ε n)
          upper ε)
        ih
theorem kH
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (lower : af G k j)
    (upper : af G k (j + 1))
    {ε : ℝ} {m : ℕ}
    (hε : 0 ≤ ε)
    (dP :
      (Fintype.card (al k (j + 1)) : ℝ) <
        (m : ℝ) * ε ^ 2) :
    ∃ n : ℕ, n < m ∧
      a3
        (aX
          lower upper ε n)
        upper ε := by
  by_contra dk
  have AM :
      ∀ n, n < m →
        ¬a3
          (aX
            lower upper ε n)
          upper ε := by
    intro n hn FW
    exact dk ⟨n, hn, FW⟩
  have Fd :
      ∀ n, n < m →
        aH
            (aX
              lower upper ε n)
            upper +
            ε ^ 2 ≤
          aH
            (aX
              lower upper ε (n + 1))
            upper := by
    intro n hn
    rw [jR]
    exact lg
      (aX
        lower upper ε n)
      upper hε (AM n hn)
  have Eo :
      ∀ n : ℕ,
        (∀ i, i < n →
          aH
              (aX
                lower upper ε i)
              upper +
              ε ^ 2 ≤
            aH
              (aX
                lower upper ε (i + 1))
              upper) →
        aH
            (aX
              lower upper ε 0)
            upper +
            (n : ℝ) * ε ^ 2 ≤
          aH
            (aX
              lower upper ε n)
            upper := by
    intro n
    induction n with
    | zero =>
        intro _
        simp
    | succ n ih =>
        intro hn
        have FE :=
          ih (fun i hi =>
            hn i (Nat.lt_trans hi (Nat.lt_succ_self n)))
        have ow := hn n (Nat.lt_succ_self n)
        calc
          aH
                (aX
                  lower upper ε 0)
                upper +
                (↑(Nat.succ n) : ℝ) * ε ^ 2 =
              (aH
                  (aX
                    lower upper ε 0)
                  upper +
                (n : ℝ) * ε ^ 2) +
                ε ^ 2 := by
            push_cast
            ring
          _ ≤
              aH
                  (aX
                    lower upper ε n)
                  upper +
                ε ^ 2 := by
            linarith
          _ ≤
              aH
                (aX
                  lower upper ε (n + 1))
                upper :=
            ow
  have Gb := Eo m Fd
  have Gc :
      0 ≤
        aH
          (aX
            lower upper ε 0)
          upper :=
    nh _ _
  have GM :
      aH
          (aX
            lower upper ε m)
          upper ≤
        (Fintype.card
          (al k (j + 1)) : ℝ) :=
    mG _ _
  linarith
theorem pQ
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (e : al k (j + 1))
    (b : aS G j)
    (g : al k j) :
    (ej e b g).card ≤
      j + 1 := by
  classical
  let I : Finset (Fin (j + 1)) :=
    (Finset.univ : Finset (Fin (j + 1))).filter
      (fun i => dH e i = g)
  calc
    (ej e b g).card ≤
        I.card := by
      exact Finset.card_image_le
    _ ≤ (Finset.univ : Finset (Fin (j + 1))).card := by
      exact Finset.card_le_card (Finset.filter_subset _ _)
    _ = j + 1 := by simp
theorem jS
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : af G k j)
    (e : al k (j + 1))
    (b : aS G j)
    (g : al k j) :
    ab.aO
        (bR P e b g) ≤
      2 ^ (j + 1) *
        ab.aO (P g) := by
  have Br :
      ab.aO
          (ab.generatedBy
            (ej e b g)) ≤
        2 ^ (j + 1) := by
    exact le_trans
      (ab.pq
        (ej e b g))
      (Nat.pow_le_pow_right (by decide)
        (pQ e b g))
  calc
    ab.aO
        (bR P e b g) ≤
        ab.aO (P g) *
          ab.aO
            (ab.generatedBy
              (ej e b g)) :=
      ab.wx _ _
    _ ≤
        ab.aO (P g) *
          2 ^ (j + 1) :=
      Nat.mul_le_mul_left _ Br
    _ =
        2 ^ (j + 1) *
          ab.aO (P g) :=
      Nat.mul_comm _ _
theorem l7
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : af G k j)
    (upper : af G k (j + 1))
    (ε : ℝ) (g : al k j) :
    ab.aO
        (cH
          lower upper ε g) ≤
      2 ^ (j + 1) *
        ab.aO (lower g) := by
  classical
  by_cases h :
      a3 lower upper ε
  · simp only [cH, dif_pos h]
    exact Nat.le_mul_of_pos_left _
      (by positivity : 0 < 2 ^ (j + 1))
  · simp only [cH, dif_neg h]
    let W :=
      fP lower upper ε h
    exact
      jS
        lower W.face W.x9 g
theorem mH
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : af G k j)
    (upper : af G k (j + 1))
    (ε : ℝ) (n : ℕ) (g : al k j) :
    ab.aO
        (aX
          lower upper ε n g) ≤
      (2 ^ (j + 1)) ^ n *
        ab.aO (lower g) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      calc
        ab.aO
            (aX
              lower upper ε (n + 1) g) ≤
            2 ^ (j + 1) *
              ab.aO
                (aX
                  lower upper ε n g) := by
          rw [jR]
          exact l7
            (aX
              lower upper ε n)
            upper ε g
        _ ≤
            2 ^ (j + 1) *
              ((2 ^ (j + 1)) ^ n *
                ab.aO (lower g)) :=
          Nat.mul_le_mul_left _ ih
        _ =
            (2 ^ (j + 1)) ^ (n + 1) *
              ab.aO (lower g) := by
          rw [pow_succ]
          ring
theorem eP
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (lower : af G k j)
    (upper : af G k (j + 1))
    {ε : ℝ} {m : ℕ}
    (hε : 0 ≤ ε)
    (dP :
      (Fintype.card (al k (j + 1)) : ℝ) <
        (m : ℝ) * ε ^ 2) :
    ∃ n : ℕ,
      ∃ aQ : af G k j,
        n < m ∧
        aP aQ lower ∧
        a3 aQ upper ε ∧
        ∀ g,
          ab.aO (aQ g) ≤
            (2 ^ (j + 1)) ^ n *
              ab.aO (lower g) := by
  obtain ⟨n, hn, dk⟩ :=
    kH
      lower upper hε dP
  exact
    ⟨n,
      aX lower upper ε n,
      hn,
      oV
        lower upper ε n,
      dk,
      mH
        lower upper ε n⟩
end av.ag
end
section
namespace av.ag
open scoped BigOperators
def g2
    {G : Type*} {j : ℕ}
    (b : b7 G (j + 1)) :
    aS G j :=
  fun i z => b ⟨i, z⟩
def dT
    {G : Type*} {j : ℕ}
    (b : aS G j) :
    b7 G (j + 1) :=
  fun q => b q.1 q.2
@[simp]
theorem jD
    {G : Type*} {j : ℕ}
    (b : b7 G (j + 1)) :
    dT
        (g2 b) = b := by
  funext q
  cases q
  rfl
@[simp]
theorem mI
    {G : Type*} {j : ℕ}
    (b : aS G j) :
    g2
        (dT b) = b := by
  funext i z
  rfl
def iW
    (G : Type*) (j : ℕ) :
    b7 G (j + 1) ≃
      aS G j where
  toFun := g2
  invFun := dT
  left_inv := jD
  right_inv := mI
@[simp]
theorem vQ
    {G : Type*} {j : ℕ}
    (b : b7 G (j + 1)) :
    dT
        ((iW G j) b) = b :=
  jD b
def dd
    {G : Type*} [Fintype G] {j : ℕ}
    (u : cU G (j + 1))
    (b : aS G j) : ℝ :=
  b6
    (cZ u)
    (dT b)
theorem tg
    {G : Type*} [Fintype G] [DecidableEq G]
    {j : ℕ}
    (u : cU G (j + 1)) :
    ∑ b : aS G j,
        dd u b = 1 := by
  classical
  calc
    (∑ b : aS G j,
        dd u b) =
        ∑ b : b7 G (j + 1),
          b6
            (cZ u) b := by
      symm
      exact
        Fintype.sum_equiv
          (iW G j)
          (fun b : b7 G (j + 1) =>
            b6
              (cZ u) b)
          (fun b : aS G j =>
            dd u b)
          (fun b => by simp [dd])
    _ = 1 :=
      r4
        (cZ u)
theorem rM
    {G : Type*} [Fintype G]
    {j : ℕ}
    (u : cU G (j + 1))
    (hu : eC u)
    (b : aS G j) :
    0 ≤ dd u b := by
  exact
    q2
      (p := cZ u)
      (fun q => hu.nonneg q.1 q.2)
      (fun q => hu.le_one q.1 q.2)
      (dT b)
theorem nI
    {G : Type*} {j : ℕ}
    (i : Fin (j + 1)) (x : Fin (j + 1) → G) :
    b3 i x = dc i x :=
  rfl
theorem kT
    {G : Type*} [Fintype G] [DecidableEq G]
    {j : ℕ}
    (b : aS G j) :
    bL b =
      dL (dT b) := by
  classical
  ext x
  rw [jh,
    tP]
  simp only [dT,
    nI]
namespace aE
theorem n2
    {G : Type*} [Fintype G] [DecidableEq G]
    {j : ℕ}
    (S : aE (Fin (j + 1) → G))
    (f : (Fin (j + 1) → G) → ℝ)
    (u : cU G (j + 1)) :
    S.et f u =
      ∑ b : aS G j,
        dd u b *
          S.b2 f
            (bL b) := by
  classical
  rw [S.qG]
  exact
    Fintype.sum_equiv
      (iW G j)
      (fun b : b7 G (j + 1) =>
        b6
            (cZ u) b *
          S.et f
            (ck b))
      (fun b : aS G j =>
        dd u b *
          S.b2 f
            (bL b))
      (fun b => by
        rw [S.tx]
        simp [dd,
          kT])
theorem m4
    {G : Type*} [Fintype G] [DecidableEq G]
    {j : ℕ}
    (S : aE (Fin (j + 1) → G))
    (f : (Fin (j + 1) → G) → ℝ)
    {ε : ℝ}
    (u : cU G (j + 1))
    (hu : eC u)
    (CV :
      ∀ b : aS G j,
        |S.b2 f
          (bL b)| ≤ ε) :
    |S.et f u| ≤ ε := by
  rw [S.n2]
  calc
    |∑ b : aS G j,
        dd u b *
          S.b2 f
            (bL b)| ≤
        ∑ b : aS G j,
          |dd u b *
            S.b2 f
              (bL b)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤
        ∑ b : aS G j,
          dd u b * ε := by
      apply Finset.sum_le_sum
      intro b _
      have hw : 0 ≤ dd u b :=
        rM u hu b
      rw [abs_mul, abs_of_nonneg hw]
      exact mul_le_mul_of_nonneg_left (CV b) hw
    _ = ε := by
      rw [← Finset.sum_mul,
        tg, one_mul]
end aE
def qu
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : af G k j)
    (upper : af G k (j + 1))
    (ε : ℝ) : Prop :=
  ∀ (e : al k (j + 1))
      (a : (upper e).parts),
    (⟨au lower e⟩ :
      aE (Fin (j + 1) → G)).q3
        (aB (upper e) a) ε
theorem a3.Ca
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    {lower : af G k j}
    {upper : af G k (j + 1)}
    {ε : ℝ}
    (dk :
      a3 lower upper ε) :
    qu
      lower upper ε := by
  intro e a u hu
  exact
    aE.m4
      (⟨au lower e⟩ :
        aE (Fin (j + 1) → G))
      (aB (upper e) a)
      u hu (fun b => dk e a b)
end av.ag
end
section
namespace av.ag
open scoped BigOperators
namespace aa
def bl
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : aa G k r) :
    af G k r :=
  C.partition (Fin.last r)
def ed
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : aa G k (r + 1)) :
    aa G k r where
  partition j := C.partition j.castSucc
def eF
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : aa G k r)
    (top : af G k (r + 1)) :
    aa G k (r + 1) where
  partition j :=
    Fin.lastCases top (fun i => C.partition i) j
def bb
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : aa G k r)
    (top : af G k r) :
    aa G k r where
  partition j :=
    Fin.lastCases top (fun i => C.partition i.castSucc) j
@[simp]
theorem Cc
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : aa G k r)
    (top : af G k (r + 1)) :
    (eF C top).bl = top := by
  simp [bl, eF]
@[simp]
theorem eY
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : aa G k r)
    (top : af G k r) :
    (bb C top).bl = top := by
  simp [bl, bb]
@[simp]
theorem aT
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : aa G k r)
    (top : af G k (r + 1))
    (j : Fin (r + 1)) :
    (eF C top).partition j.castSucc =
      C.partition j := by
  simp [eF]
@[simp]
theorem dB
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : aa G k r)
    (top : af G k (r + 1)) :
    (eF C top).partition (Fin.last (r + 1)) =
      top := by
  simp [eF]
@[simp]
theorem zj
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : aa G k (r + 1)) :
    eF C.ed C.bl = C := by
  cases C with
  | mk partition =>
      simp only [ed, bl, eF]
      congr 1
      funext j e
      cases j using Fin.lastCases <;>
        simp only [Fin.lastCases_last,
          Fin.lastCases_castSucc]
theorem g3
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {aQ an : aa G k r}
    {yK wE :
      af G k (r + 1)}
    (ya : aQ.db an)
    (m5 : aP yK wE) :
    (eF aQ yK).db
      (eF an wE) := by
  intro j e
  cases j using Fin.lastCases with
  | last =>
      simp only [eF, Fin.lastCases_last]
      change al k (r + 1) at e
      change yK e ≤ wE e
      exact m5 e
  | cast i =>
      simp only [eF, Fin.lastCases_castSucc]
      change al k i.1 at e
      change aQ.partition i e ≤ an.partition i e
      exact ya i e
theorem oD
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : aa G k r)
    (top : af G k r)
    (m5 : aP top C.bl) :
    (bb C top).db C := by
  intro j e
  cases j using Fin.lastCases with
  | last =>
      simp only [bb, Fin.lastCases_last]
      change al k r at e
      change top e ≤ C.partition (Fin.last r) e
      exact m5 e
  | cast i =>
      simp only [bb, Fin.lastCases_castSucc]
      exact le_rfl
end aa
structure ak
    (G : Type*) [Fintype G] [DecidableEq G]
    (k r : ℕ) where
  an : aa G k r
  aQ : aa G k r
  dy : aQ.db an
namespace ak
end ak
abbrev cV (r : ℕ) := Fin r → ℝ
def il
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : aa G k r)
    (ε : cV r) : Prop :=
  ∀ j : Fin r,
    a3
      (C.partition j.castSucc)
      (C.partition j.succ)
      (ε j)
end av.ag
end
section
namespace av.ag
open scoped BigOperators
def bx
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : ab Ω) (x : Ω) :
    P.parts :=
  ⟨P.part x, P.part_mem.2 (Finset.mem_univ x)⟩
@[simp]
theorem d6
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : ab Ω) (x : Ω) (a : P.parts) :
    bx P x = a ↔ x ∈ a.1 := by
  constructor
  · intro h
    rw [← h]
    exact P.mem_part (Finset.mem_univ x)
  · intro hx
    apply Subtype.ext
    exact P.part_eq_of_mem a.2 hx
theorem lY
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : ab Ω) (x y : Ω) :
    bx P y = bx P x ↔
      y ∈ P.part x := by
  rw [d6]
  rfl
theorem qK
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : ab Ω) (a : P.parts) :
    dJ P (aB P a) := by
  intro x y hy
  have u4 :
      bx P y = bx P x :=
    (lY P x y).2 hy
  by_cases hx : x ∈ a.1
  · have B9 : bx P x = a :=
      (d6 P x a).2 hx
    have Ep : bx P y = a := u4.trans B9
    have yb : y ∈ a.1 :=
      (d6 P y a).1 Ep
    simp [dg P a hx,
      dg P a yb]
  · have yb : y ∉ a.1 := by
      intro GN
      have Ep : bx P y = a :=
        (d6 P y a).2 GN
      have B9 : bx P x = a :=
        u4.symm.trans Ep
      exact hx ((d6 P x a).1 B9)
    simp [c0 P a hx,
      c0 P a yb]
def d7
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : ab Ω) (s : Finset P.parts) :
    Finset Ω :=
  s.biUnion fun a => a.1
@[simp]
theorem qL
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : ab Ω) (s : Finset P.parts) (x : Ω) :
    x ∈ d7 P s ↔
      ∃ a ∈ s, x ∈ a.1 := by
  simp [d7]
theorem e8
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : ab Ω) (s : Finset P.parts) (x : Ω) :
    x ∈ d7 P s ↔
      bx P x ∈ s := by
  constructor
  · intro hx
    obtain ⟨a, ha, Ce⟩ :=
      (qL P s x).1 hx
    have iX :
        bx P x = a :=
      (d6 P x a).2 Ce
    simpa [iX] using ha
  · intro hx
    exact
      (qL P s x).2
        ⟨bx P x, hx,
          P.mem_part (Finset.mem_univ x)⟩
theorem oX
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : ab Ω) (s : Finset P.parts) :
    dJ P
      (aN (d7 P s)) := by
  intro x y hy
  have u4 :
      bx P y = bx P x :=
    (lY P x y).2 hy
  have jO :
      y ∈ d7 P s ↔
        x ∈ d7 P s := by
    rw [e8,
      e8, u4]
  by_cases hx : x ∈ d7 P s
  · have yb : y ∈ d7 P s := jO.mpr hx
    simp [cG hx,
      cG yb]
  · have yb : y ∉ d7 P s :=
      fun h => hx (jO.mp h)
    simp [cj hx,
      cj yb]
theorem rr
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : ab Ω) (f : Ω → ℝ) (a : P.parts) :
    mean (fun x => f x * aB P a x) =
      aq P f (P.representative a) *
        mean (aB P a) := by
  rw [aE.gI
    P f (aB P a)
    (qK P a)]
  rw [← k0]
  apply congrArg mean
  funext x
  by_cases hx : x ∈ a.1
  · rw [dg P a hx,
      mul_one, mul_one]
    have vv :
        P.representative a ∈ P.part x := by
      rw [P.part_eq_of_mem a.2 hx]
      exact P.jP a
    exact
      (cY P f vv).symm
  · rw [c0 P a hx,
      mul_zero, mul_zero]
theorem kI
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : ab Ω) (f : Ω → ℝ) (a : P.parts)
    {β : ℝ}
    (gr : aq P f (P.representative a) ≤ β) :
    mean (fun x => f x * aB P a x) ≤
      β * mean (aB P a) := by
  rw [rr P f a]
  apply mul_le_mul_of_nonneg_right gr
  exact o9 fun x =>
    ng P a x
noncomputable def nJ
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : ab Ω) (f : Ω → ℝ) (α : ℝ) :
    Finset P.parts := by
  classical
  exact (Finset.univ : Finset P.parts).filter fun b =>
    aq P f (P.representative b) < α
noncomputable def cO
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : ab Ω) (f : Ω → ℝ) (α : ℝ) :
    Finset Ω :=
  d7 P (nJ P f α)
@[simp]
theorem jT
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : ab Ω) (f : Ω → ℝ) (α : ℝ)
    (x : Ω) :
    x ∈ cO P f α ↔
      aq P f x < α := by
  rw [cO,
    e8]
  simp only [nJ, Finset.mem_filter,
    Finset.mem_univ, true_and]
  have vv :
      P.representative (bx P x) ∈
        P.part x := by
    exact P.jP (bx P x)
  have heq :=
    cY P f vv
  rw [heq]
theorem lP
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    (P : ab Ω) (A : Finset Ω)
    {α : ℝ} (fX : 0 ≤ α) :
    mean (aN
      (A ∩ cO P (aN A) α)) ≤
      α := by
  rw [show
      aN
          (A ∩ cO P (aN A) α) =
        fun x =>
          aN A x *
            aN
              (cO
                P (aN A) α) x by
    funext x
    by_cases GO : x ∈ A <;>
      by_cases A7 :
        x ∈ cO P (aN A) α <;>
      simp [GO, A7]]
  rw [aE.gI
    P (aN A)
      (aN
        (cO P (aN A) α))
      (oX P
        (nJ P (aN A) α))]
  calc
    mean (fun x =>
        aq P (aN A) x *
          aN
            (cO P
              (aN A) α) x) ≤
        mean (fun _x : Ω => α) := by
      apply mm
      intro x
      by_cases hx :
          x ∈ cO P (aN A) α
      · rw [cG hx, mul_one]
        exact
          (jT
            P (aN A) α x).1 hx |>.le
      · rw [cj hx, mul_zero]
        exact fX
    _ = α := ml α
noncomputable def nK
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : ab Ω) (f : Ω → ℝ) (β : ℝ) :
    Finset P.parts := by
  classical
  exact (Finset.univ : Finset P.parts).filter fun b =>
    β < aq P f (P.representative b)
noncomputable def fZ
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : ab Ω) (f : Ω → ℝ) (β : ℝ) :
    Finset Ω :=
  d7 P (nK P f β)
@[simp]
theorem jU
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : ab Ω) (f : Ω → ℝ) (β : ℝ)
    (x : Ω) :
    x ∈ fZ P f β ↔
      β < aq P f x := by
  rw [fZ,
    e8]
  simp only [nK, Finset.mem_filter,
    Finset.mem_univ, true_and]
  have vv :
      P.representative (bx P x) ∈
        P.part x := by
    exact P.jP (bx P x)
  have heq :=
    cY P f vv
  rw [heq]
theorem mJ
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : ab Ω) (f : Ω → ℝ)
    (hf : ∀ x, 0 ≤ f x)
    {β : ℝ} (_hβ : 0 ≤ β) :
    β * mean (aN
        (fZ P f β)) ≤
      mean f := by
  rw [← k0]
  calc
    mean (fun x =>
        β * aN
          (fZ P f β) x) ≤
        mean (aq P f) := by
      apply mm
      intro x
      by_cases hx : x ∈ fZ P f β
      · rw [cG hx, mul_one]
        exact
          (jU P f β x).1 hx |>.le
      · rw [cj hx, mul_zero]
        exact uK P hf x
    _ = mean f := iR P f
noncomputable def th
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (aQ an upper : ab Ω)
    (a : upper.parts) (x : Ω) : ℝ :=
  aq aQ (aB upper a) x -
    aq an (aB upper a) x
noncomputable def iY
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (aQ an upper : ab Ω)
    (a : upper.parts) (x : Ω) : ℝ :=
  th aQ an upper a x ^ 2
theorem ti
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (aQ an upper : ab Ω)
    (a : upper.parts) (x : Ω) :
    0 ≤ iY aQ an upper a x :=
  sq_nonneg _
theorem qN
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (A B C : Finset Ω) :
    mean (aN (A ∩ (B ∪ C))) ≤
      mean (aN (A ∩ B)) +
        mean (aN C) := by
  rw [← tX]
  apply mm
  intro x
  by_cases hx : x ∈ A ∩ (B ∪ C)
  · rw [cG hx]
    rcases Finset.mem_union.mp (Finset.mem_inter.mp hx).2 with A7 | GQ
    · have FX : x ∈ A ∩ B :=
        Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).1, A7⟩
      rw [cG FX]
      exact le_add_of_nonneg_right
        (by
          by_cases Er : x ∈ C <;> simp [Er])
    · rw [cG GQ]
      exact le_add_of_nonneg_left
        (by
          by_cases CW : x ∈ A ∩ B <;> simp [CW])
  · rw [cj hx]
    exact add_nonneg
      (by
        by_cases CW : x ∈ A ∩ B <;> simp [CW])
      (by
        by_cases Er : x ∈ C <;> simp [Er])
noncomputable def eK
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (aQ an : af G k j)
    (e : al k (j + 1))
    (upper : ab (Fin (j + 1) → G))
    (a : upper.parts) (x : Fin (j + 1) → G) : ℝ :=
  th
    (au aQ e)
    (au an e)
    upper a x
noncomputable def qj
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (an : af G k j)
    (e : al k (j + 1))
    (b : (au an e).parts) : ℝ :=
  mean
    (aB
      (au an e) b)
noncomputable def nL
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (aQ an : af G k j)
    (e : al k (j + 1))
    (upper : ab (Fin (j + 1) → G))
    (a : upper.parts)
    (b : (au an e).parts) : ℝ :=
  mean fun x =>
    eK aQ an e upper a x ^ 2 *
      aB
        (au an e) b x
theorem rt
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (aQ an : af G k j)
    (e : al k (j + 1))
    (upper : ab (Fin (j + 1) → G))
    (a : upper.parts)
    (b : (au an e).parts)
    {β : ℝ}
    (gr :
      aq (au an e)
          (fun x =>
            eK
              aQ an e upper a x ^ 2)
          ((au an e).representative b) ≤
        β) :
    nL aQ an e upper a b ≤
      β * qj an e b := by
  exact
    kI
      (au an e)
      (fun x =>
        eK aQ an e upper a x ^ 2)
      b gr
def oj
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (aQ an : af G k j)
    (e : al k (j + 1))
    (upper : ab (Fin (j + 1) → G))
    (a : upper.parts) (x : Fin (j + 1) → G)
    (α β : ℝ) : Prop :=
  α ≤
      eJ an e
        (aB upper a) x ∧
    aq (au an e)
        (fun y => eK
          aQ an e upper a y ^ 2) x ≤
      β
theorem oj.oE
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (aQ an : af G k j)
    (e : al k (j + 1))
    (upper : ab (Fin (j + 1) → G))
    (a : upper.parts) (x : Fin (j + 1) → G)
    (α β : ℝ)
    (h5 :
      oj
        aQ an e upper a x α β) :
    nL
        aQ an e upper a
        (fJ an e x) ≤
      β *
        qj an e
          (fJ an e x) := by
  apply rt
  have vv :
      (au an e).representative
          (fJ an e x) ∈
        (au an e).part x := by
    exact
      (au an e).jP
        (fJ an e x)
  have heq :=
    cY
      (au an e)
      (fun y =>
        eK
          aQ an e upper a y ^ 2)
      vv
  rw [heq]
  exact h5.2
structure ai
    (G : Type*) [Fintype G] [DecidableEq G]
    (k r : ℕ) (C : aa G k r) where
  witness : Fin k → G
  atom :
    (j : Fin (r + 1)) →
      (e : al k j.1) →
        (C.partition j e).parts
  xA :
    ∀ (j : Fin (r + 1)) (e : al k j.1),
      aI e witness ∈ (atom j e).1
namespace ai
def yL
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} (C : aa G k r)
    (x : Fin k → G) :
    ai G k r C where
  witness := x
  atom j e :=
    bx (C.partition j e)
      (aI e x)
  xA j e :=
    (C.partition j e).mem_part
      (Finset.mem_univ (aI e x))
theorem jo
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} {C : aa G k r}
    (A : ai G k r C)
    (j : Fin (r + 1)) (e : al k j.1) :
    A.atom j e =
      bx (C.partition j e)
        (aI e A.witness) := by
  apply Subtype.ext
  exact
    ((C.partition j e).part_eq_of_mem
      (A.atom j e).2 (A.xA j e)).symm
end ai
end av.ag
end
section
namespace av.ag
open scoped BigOperators
namespace ak
noncomputable def cz
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : ak G k r)
    (j : Fin r) (e : al k (j.1 + 1)) : ℝ :=
  bI
      (P.aQ.partition j.castSucc) e
      (P.an.partition j.succ e) -
    bI
      (P.an.partition j.castSucc) e
      (P.an.partition j.succ e)
theorem qa
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : ak G k r)
    (j : Fin r) (e : al k (j.1 + 1)) :
    0 ≤ P.cz j e := by
  apply sub_nonneg.mpr
  exact m1
    (fun f => P.dy j.castSucc f)
    e (P.an.partition j.succ e)
noncomputable def fB
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : ak G k r)
    (j : Fin r) : ℝ :=
  aH
      (P.aQ.partition j.castSucc)
      (P.an.partition j.succ) -
    aH
      (P.an.partition j.castSucc)
      (P.an.partition j.succ)
theorem n3
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : ak G k r)
    (j : Fin r) :
    P.fB j =
      ∑ e : al k (j.1 + 1),
        P.cz j e := by
  unfold fB
    cz
    aH
  rw [Finset.sum_sub_distrib]
  rfl
end ak
end av.ag
end
section
namespace av.ag
open scoped BigOperators
namespace aE
end aE
def lh
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (T S : eg G k r) : Prop :=
  ∀ e, (T e).partition ≤ (S e).partition
theorem lh.refl
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (S : eg G k r) :
    lh S S :=
  fun _ => le_rfl
theorem lh.trans
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {U T S : eg G k r}
    (GR : lh U T)
    (GS : lh T S) :
    lh U S :=
  fun e => (GR e).trans (GS e)
theorem tF
    {G : Type*} [Fintype G] [Nonempty G]
    {k r : ℕ}
    (e : al k r)
    (f : (Fin r → G) → ℝ) :
    mean (fun x : Fin k → G =>
      f (aI e x)) = mean f := by
  rw [va e]
  unfold fq
  simp
end av.ag
end
section
namespace av.ag
open scoped BigOperators
theorem rP
    {ι Ω : Type*} [DecidableEq Ω]
    (s : Finset ι) (F : ι → Finset Ω) (x : Ω) :
    aN (s.biUnion F) x ≤
      ∑ i ∈ s, aN (F i) x := by
  by_cases hx : x ∈ s.biUnion F
  · obtain ⟨i, hi, Es⟩ := Finset.mem_biUnion.mp hx
    rw [cG hx]
    calc
      1 = aN (F i) x :=
        (cG Es).symm
      _ ≤ ∑ j ∈ s, aN (F j) x := by
        apply Finset.single_le_sum
          (s := s)
          (f := fun j => aN (F j) x)
        · intro j hj
          by_cases GU : x ∈ F j <;> simp [GU]
        · exact hi
  · rw [cj hx]
    exact Finset.sum_nonneg fun i _ => by
      by_cases Es : x ∈ F i <;> simp [Es]
theorem ke
    {ι Ω : Type*} [DecidableEq Ω]
    [Fintype Ω]
    (s : Finset ι) (F : ι → Finset Ω) :
    mean (aN (s.biUnion F)) ≤
      ∑ i ∈ s, mean (aN (F i)) := by
  calc
    mean (aN (s.biUnion F)) ≤
        mean (fun x => ∑ i ∈ s,
          aN (F i) x) :=
      mm (rP s F)
    _ = ∑ i ∈ s, mean (aN (F i)) :=
      x3 s (fun i => aN (F i))
abbrev ct (r : ℕ) :=
  (j : Fin r) ×' al r (j.1 + 1)
theorem qO
    {k s r : ℕ} (GV : s ≤ r) (Cf : r ≤ k)
    (f : al k s) :
    ∃ e : al k r, ∃ d : al r s,
      d.trans e = f := by
  classical
  let sf : Finset (Fin k) :=
    Finset.univ.map f.toEmbedding
  have CX : sf.card = s := by
    rw [show sf.card =
        (Finset.univ : Finset (Fin s)).card by
      exact Finset.card_map f.toEmbedding]
    simp
  have CY : sf ⊆ Finset.univ :=
    Finset.subset_univ sf
  obtain ⟨t, Fe, _ht_univ, ht⟩ :=
    Finset.exists_subsuperset_card_eq
      CY
      (by simpa [CX] using GV)
      (by simpa using Cf)
  let e : al k r :=
    t.orderEmbOfFin ht
  have Cg (i : Fin s) : f i ∈ t := by
    apply Fe
    exact Finset.mem_map.mpr
      ⟨i, Finset.mem_univ i, rfl⟩
  let ft : Fin s ↪o t :=
    OrderEmbedding.ofStrictMono
      (fun i => ⟨f i, Cg i⟩)
      (fun _ _ hij => f.strictMono hij)
  let d : al r s :=
    ft.trans (t.orderIsoOfFin ht).symm.toOrderEmbedding
  refine ⟨e, d, ?_⟩
  apply RelEmbedding.ext
  intro i
  change
    t.orderEmbOfFin ht
        ((t.orderIsoOfFin ht).symm
          ⟨f i, Cg i⟩) =
      f i
  rw [← Finset.coe_orderIsoOfFin_apply]
  simp
noncomputable def eL
    {G : Type*} [Fintype G] [DecidableEq G]
    {r j : ℕ}
    (d : al r j)
    (S : Finset (Fin j → G)) :
    Finset (Fin r → G) := by
  classical
  exact Finset.univ.filter fun y =>
    aI d y ∈ S
@[simp]
theorem ji
    {G : Type*} [Fintype G] [DecidableEq G]
    {r j : ℕ}
    (d : al r j)
    (S : Finset (Fin j → G))
    (y : Fin r → G) :
    y ∈ eL d S ↔
      aI d y ∈ S := by
  simp [eL]
theorem oF
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {r j : ℕ}
    (d : al r j)
    (S : Finset (Fin j → G)) :
    mean (aN
        (eL d S)) =
      mean (aN S) := by
  rw [show
      aN (eL d S) =
        fun y => aN S
          (aI d y) by
    funext y
    by_cases hy : aI d y ∈ S
    · rw [cG hy,
        cG]
      exact
        (ji d S y).2 hy
    · rw [cj hy,
        cj]
      exact fun h =>
        hy ((ji d S y).1 h)]
  exact tF d
    (aN S)
end av.ag
end
section
namespace av.ag
open scoped BigOperators
namespace ak
end ak
namespace ai
end ai
namespace ak
end ak
namespace ai
end ai
end av.ag
end
section
namespace av.ag
open scoped BigOperators
end av.ag
end
section
namespace av.ag
open scoped BigOperators
structure aj (k r : ℕ) where
  ay : Fin r
  face : al k (ay.1 + 1)
deriving DecidableEq
namespace aj
def equivSigma (k r : ℕ) :
    aj k r ≃
      Σ j : Fin r, al k (j.1 + 1) where
  toFun e := ⟨e.ay, e.face⟩
  invFun e := ⟨e.1, e.2⟩
  left_inv e := by cases e; rfl
  right_inv e := by cases e; rfl
noncomputable instance instFintype (k r : ℕ) :
    Fintype (aj k r) :=
  Fintype.ofEquiv
    (Σ j : Fin r, al k (j.1 + 1))
    (equivSigma k r).symm
def rank {k r : ℕ} (e : aj k r) : ℕ :=
  e.ay.1 + 1
@[simp]
theorem rank_pos {k r : ℕ} (e : aj k r) :
    0 < e.rank := by
  simp [rank]
noncomputable def boundary
    {k r : ℕ}
    (e : aj k r)
    (lx : 0 < e.ay.1)
    (i : Fin (e.ay.1 + 1)) :
    aj k r := by
  let j : Fin r :=
    ⟨e.ay.1 - 1,
      lt_of_le_of_lt (Nat.sub_le _ _) e.ay.2⟩
  refine ⟨j, ?_⟩
  have hj : j.1 + 1 = e.ay.1 := by
    simp only [j]
    omega
  exact hj ▸ dH e.face i
@[simp]
theorem wH
    {k r : ℕ}
    (e : aj k r)
    (lx : 0 < e.ay.1)
    (i : Fin (e.ay.1 + 1)) :
    (e.boundary lx i).ay.1 =
      e.ay.1 - 1 := by
  rfl
theorem xB
    {k r : ℕ}
    (e : aj k r)
    (lx : 0 < e.ay.1)
    (i : Fin (e.ay.1 + 1)) :
    (e.boundary lx i).rank < e.rank := by
  simp only [rank, wH]
  omega
end aj
def bX
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : aa G k r}
    (A : ai G k r C)
    (e : aj k r)
    (y : Fin (e.ay.1 + 1) → G) : ℝ :=
  aB
    (C.partition e.ay.succ e.face)
    (A.atom e.ay.succ e.face) y
theorem mL
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : aa G k r}
    (A : ai G k r C)
    (e : aj k r)
    (y : Fin (e.ay.1 + 1) → G) :
    0 ≤ bX A e y :=
  ng _ _ _
theorem mM
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : aa G k r}
    (A : ai G k r C)
    (e : aj k r)
    (y : Fin (e.ay.1 + 1) → G) :
    bX A e y ≤ 1 :=
  r8 _ _ _
noncomputable def bV
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : aa G k r}
    (A : ai G k r C)
    (s : Finset (aj k r))
    (x : Fin k → G) : ℝ :=
  ∏ e ∈ s,
    bX A e
      (aI e.face x)
noncomputable def fw
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : aa G k r}
    (A : ai G k r C)
    (s : Finset (aj k r)) : ℝ :=
  mean (bV A s)
noncomputable def c9
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : aa G k r}
    (A : ai G k r C) : ℝ :=
  fw A Finset.univ
theorem qP
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : aa G k r}
    (A : ai G k r C)
    (s : Finset (aj k r))
    (x : Fin k → G) :
    bV A s x ≤ 1 := by
  unfold bV
  apply Finset.prod_le_one
  · intro e he
    exact mL A e _
  · intro e he
    exact mM A e _
def aV
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : aa G k r)
    (e : aj k r) :
    af G k e.ay.1 :=
  C.partition e.ay.castSucc
theorem l8
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : ak G k r)
    (A : ai G k r P.aQ)
    (e : aj k r)
    (lx : 0 < e.ay.1)
    (i : Fin (e.ay.1 + 1))
    (x : Fin k → G)
    (sM :
      bX A (e.boundary lx i)
          (aI (e.boundary lx i).face x) ≠
        0) :
    b3 i (aI e.face x) ∈
      (aV P.an e
        (dH e.face i)).part
        (b3 i
          (aI e.face A.witness)) := by
  rcases e with ⟨⟨n, hn⟩, Bt⟩
  cases n with
  | zero =>
      simp at lx
  | succ n =>
      let f :=
        (⟨⟨n, by omega⟩,
            dH Bt i⟩ :
          aj k r)
      have Dz :
          aI f.face x ∈
            (A.atom f.ay.succ f.face).1 := by
        by_contra hnot
        exact sM
          (c0
            (P.aQ.partition f.ay.succ f.face)
            (A.atom f.ay.succ f.face) hnot)
      have iX :
          (A.atom f.ay.succ f.face).1 =
            (P.aQ.partition f.ay.succ f.face).part
              (aI f.face A.witness) := by
        exact congrArg Subtype.val
          (A.jo
            f.ay.succ f.face)
      rw [iX] at Dz
      have yN :
          aI f.face x ∈
            (P.an.partition f.ay.succ f.face).part
              (aI f.face A.witness) :=
        ab.gj
          (P.dy f.ay.succ f.face)
          (aI f.face A.witness) Dz
      let j : Fin (r + 1) :=
        ⟨n + 1, Nat.lt_succ_of_lt hn⟩
      have Hs : f.ay.succ = j := by
        apply Fin.ext
        rfl
      have CZ :
          aI f.face x ∈
            (P.an.partition j f.face).part
              (aI f.face A.witness) := by
        subst j
        exact yN
      simpa [f, j, aV,
        aa.Dy] using CZ
end av.ag
end
section
namespace av.ag
open scoped BigOperators
def ak.yO
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : ak G k r) :
    ak G k r where
  an := P.an
  aQ := P.an
  dy := aa.db.refl P.an
noncomputable def bq
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : ak G k r)
    (A : ai G k r P.an)
    (e : aj k r) : ℝ :=
  eJ
    (aV P.an e)
    e.face
    (aB
      (P.an.partition e.ay.succ e.face)
      (A.atom e.ay.succ e.face))
    (aI e.face A.witness)
noncomputable def ni
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : ak G k r)
    (A : ai G k r P.an)
    (e : aj k r)
    (y : Fin (e.ay.1 + 1) → G) : ℝ :=
  eJ
    (aV P.aQ e)
    e.face
    (aB
      (P.an.partition e.ay.succ e.face)
      (A.atom e.ay.succ e.face))
    y
noncomputable def gM
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : ak G k r)
    (A : ai G k r P.an)
    (e : aj k r)
    (y : Fin (e.ay.1 + 1) → G) : ℝ :=
  ni P A e y -
    bq P A e
noncomputable def kU
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : ak G k r)
    (A : ai G k r P.an)
    (e : aj k r)
    (y : Fin (e.ay.1 + 1) → G) : ℝ :=
  bX A e y -
    ni P A e y
noncomputable def dS
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : ak G k r)
    (A : ai G k r P.an)
    (e : aj k r)
    (y : Fin (e.ay.1 + 1) → G) : ℝ :=
  aB
    (au
      (aV P.an e) e.face)
    (fJ
      (aV P.an e) e.face
      (aI e.face A.witness))
    y
theorem pg
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : ak G k r)
    (A : ai G k r P.an)
    (e : aj k r)
    (y : Fin (e.ay.1 + 1) → G) :
    bX A e y =
      bq P A e +
        gM P A e y +
        kU P A e y := by
  unfold gM kU
  ring
theorem jk
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : ak G k r)
    (A : ai G k r P.an)
    (e : aj k r)
    (lx : 0 < e.ay.1)
    (i : Fin (e.ay.1 + 1))
    (x : Fin k → G)
    (sM :
      bX A (e.boundary lx i)
          (aI (e.boundary lx i).face x) ≠
        0) :
    b3 i (aI e.face x) ∈
      (aV P.an e
        (dH e.face i)).part
        (b3 i
          (aI e.face A.witness)) := by
  exact
    l8
      P.yO A e lx i x sM
def cu
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : ak G k r)
    (τ : cV r) : Prop :=
  ∀ j : Fin r,
    a3
      (P.aQ.partition j.castSucc)
      (P.an.partition j.succ)
      (τ j)
theorem oZ
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : ak G k r)
    (A : ai G k r P.an)
    (τ : cV r)
    (dk :
      cu P τ)
    (e : aj k r) :
    (⟨au
        (aV P.aQ e) e.face⟩ :
      aE
        (Fin (e.ay.1 + 1) → G)).q3
      (aB
        (P.an.partition e.ay.succ e.face)
        (A.atom e.ay.succ e.face))
      (τ e.ay) := by
  rw [aV]
  exact
    (dk e.ay).Ca
      e.face
      (A.atom e.ay.succ e.face)
theorem l9
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : ak G k r)
    (A : ai G k r P.an)
    (e : aj k r)
    (y : Fin (e.ay.1 + 1) → G) :
    gM P A e y *
        dS P A e y =
      eK
          (aV P.aQ e)
          (aV P.an e)
          e.face
          (P.an.partition e.ay.succ e.face)
          (A.atom e.ay.succ e.face) y *
        dS P A e y := by
  let Q :=
    au
      (aV P.an e) e.face
  let b : Q.parts :=
    fJ
      (aV P.an e) e.face
      (aI e.face A.witness)
  let f :
      (Fin (e.ay.1 + 1) → G) → ℝ :=
    aB
      (P.an.partition e.ay.succ e.face)
      (A.atom e.ay.succ e.face)
  by_cases hy : y ∈ b.1
  · have yN :
        aq Q f y =
          aq Q f
            (aI e.face A.witness) := by
      exact cY Q f hy
    rw [dS,
      dg _ _ hy,
      mul_one, mul_one]
    change
      aq
            (au
              (aV P.aQ e) e.face)
            f y -
          aq Q f
            (aI e.face A.witness) =
        aq
            (au
              (aV P.aQ e) e.face)
            f y -
          aq Q f y
    rw [yN]
  · rw [dS,
      c0 _ _ hy,
      mul_zero, mul_zero]
end av.ag
end
section
namespace av.ag
end av.ag
end
section
namespace av.ag
open scoped BigOperators
def aK
    {k r : ℕ} (e : aj k r) :
    Finset (Fin k) :=
  Finset.univ.map e.face.toEmbedding
@[simp]
theorem b1
    {k r : ℕ} (e : aj k r) :
    (aK e).card = e.rank := by
  simp [aK, aj.rank]
theorem cI
    {k r : ℕ} (e : aj k r) :
    (aK e).Nonempty := by
  apply Finset.card_pos.mp
  rw [b1]
  exact e.rank_pos
theorem cQ
    {k r : ℕ} (e : aj k r) :
    (aK e).card ≤ r := by
  rw [b1]
  unfold aj.rank
  omega
@[simp]
theorem eu
    {k r : ℕ} (e : aj k r)
    (v : Fin k) :
    v ∈ aK e ↔
      v ∈ Set.range e.face := by
  simp [aK]
noncomputable def bB
    {k r : ℕ} (t : Finset (Fin k))
    (ht : t.Nonempty) (pv : t.card ≤ r) :
    aj k r := by
  let j : Fin r :=
    ⟨t.card - 1, by
      have Ch : 0 < t.card :=
        Finset.card_pos.mpr ht
      omega⟩
  refine ⟨j, ?_⟩
  have fE : t.card = j.1 + 1 := by
    dsimp [j]
    have Ch : 0 < t.card :=
      Finset.card_pos.mpr ht
    omega
  exact t.orderEmbOfFin fE
@[simp]
theorem cE
    {k r : ℕ} (t : Finset (Fin k))
    (ht : t.Nonempty) (pv : t.card ≤ r) :
    aK
        (bB t ht pv) = t := by
  dsimp only [aK, bB]
  exact Finset.map_orderEmbOfFin_univ t _
theorem eQ
    {k r : ℕ} :
    Function.Injective
      (aK :
        aj k r → Finset (Fin k)) := by
  intro e f FF
  have qb : e.rank = f.rank := by
    rw [← b1 e,
      ← b1 f, FF]
  rcases e with ⟨je, e⟩
  rcases f with ⟨jf, f⟩
  simp only [aj.rank] at qb
  have hj : je = jf := by
    apply Fin.ext
    omega
  subst jf
  have z4 : Set.range e = Set.range f := by
    ext v
    have hv :=
      congrArg
        (fun s : Finset (Fin k) => v ∈ s) FF
    simpa [aK] using hv
  have Hq : e = f :=
    (OrderEmbedding.range_inj).mp z4
  subst f
  rfl
@[simp]
theorem mN
    {k r : ℕ} (e : aj k r) :
    bB
        (aK e)
        (cI e)
        (cQ e) = e := by
  apply eQ
  exact cE
    (aK e)
    (cI e)
    (cQ e)
noncomputable def aC
    (k r : ℕ) : Finset (Finset (Fin k)) :=
  insert ∅
    (Finset.univ.image
      (aK :
        aj k r → Finset (Fin k)))
@[simp]
theorem jb
    (k r : ℕ) :
    ∅ ∈ aC k r := by
  simp [aC]
theorem ie
    (k r : ℕ) :
    (∅ : Finset (Fin k)) ∉
      Finset.univ.image
        (aK :
          aj k r → Finset (Fin k)) := by
  intro h
  obtain ⟨e, _he, tV⟩ :=
    Finset.mem_image.mp h
  exact (cI e).ne_empty
    tV
@[simp]
theorem ek
    {k r : ℕ} (t : Finset (Fin k)) :
    t ∈ aC k r ↔
      t.card ≤ r := by
  constructor
  · intro ht
    rw [aC,
      Finset.mem_insert] at ht
    rcases ht with rfl | ht
    · simp
    · obtain ⟨e, _he, rfl⟩ :=
        Finset.mem_image.mp ht
      exact cQ e
  · intro pv
    by_cases vS : t = ∅
    · subst t
      exact jb k r
    · have ht : t.Nonempty :=
        Finset.nonempty_iff_ne_empty.mpr vS
      rw [aC,
        Finset.mem_insert]
      right
      apply Finset.mem_image.mpr
      refine
        ⟨bB t ht pv,
          Finset.mem_univ _, ?_⟩
      exact cE t ht pv
noncomputable def aD
    (k r : ℕ) :
    ah (Fin k) (Fin k)
      (aC k r) where
  edges := aC k r
  projection := id
  cW := by
    intro g hg x hx y hy u4
    exact u4
  c4 := by
    intro g hg
    simpa using hg
@[simp]
theorem d8
    (k r : ℕ) :
    (aD k r).edges =
      aC k r :=
  rfl
@[simp]
theorem hO
    (k r : ℕ) :
    (aD k r).projection =
      id :=
  rfl
theorem oG
    (k r : ℕ) :
    (aD k r).a6 := by
  intro g hg f ri
  rw [d8] at hg ⊢
  rw [ek] at hg ⊢
  exact (Finset.card_le_card ri).trans hg
noncomputable def eb
    {G : Type*} {k r : ℕ}
    (t : Finset (Fin k))
    (ht : t.Nonempty) (pv : t.card ≤ r)
    (y : {v : Fin k // v ∈ t} → G) :
    Fin ((bB t ht pv).ay.1 + 1) → G := by
  let e := bB t ht pv
  have fE : t.card = e.ay.1 + 1 := by
    dsimp [e, bB]
    have Ch : 0 < t.card :=
      Finset.card_pos.mpr ht
    omega
  exact fun i => y (t.orderIsoOfFin fE i)
@[simp]
theorem n4
    {k r : ℕ} (e : aj k r)
    (i : Fin (e.ay.1 + 1)) :
    ((aK e).orderIsoOfFin
        (by
          simp [aj.rank]) i).1 =
      e.face i := by
  rw [Finset.coe_orderIsoOfFin_apply]
  have iX :
      e.face =
        (aK e).orderEmbOfFin
          (by
            simp [aj.rank]) := by
    apply Finset.orderEmbOfFin_unique'
    intro q
    simp [aK]
  exact congrArg (fun f => f i) iX.symm
noncomputable def ar
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : aa G k r}
    (A : ai G k r C) :
    ah.cM (Fin k) G := by
  classical
  intro t y
  by_cases ht : t.Nonempty
  · by_cases pv : t.card ≤ r
    · exact bX A
        (bB t ht pv)
        (eb t ht pv y)
    · exact 1
  · exact 1
@[simp]
theorem fk
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : aa G k r}
    (A : ai G k r C)
    (y : {v : Fin k // v ∈ (∅ : Finset (Fin k))} → G) :
    ar A ∅ y = 1 := by
  simp [ar]
@[simp]
theorem jV
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : aa G k r}
    (A : ai G k r C)
    (e : aj k r)
    (y :
      {v : Fin k // v ∈ aK e} → G) :
    ar A
        (aK e) y =
      bX A e
        (fun i =>
          y ⟨e.face i,
            (eu e
              (e.face i)).2 ⟨i, rfl⟩⟩) := by
  classical
  simp only [ar,
    dif_pos (cI e),
    dif_pos (cQ e)]
  change
    (fun p :
        (Σ f : aj k r,
          Fin (f.ay.1 + 1) → G) =>
      bX A p.1 p.2)
        ⟨bB
            (aK e)
            (cI e)
            (cQ e),
          eb
            (aK e)
            (cI e)
            (cQ e) y⟩ =
      (fun p :
          (Σ f : aj k r,
            Fin (f.ay.1 + 1) → G) =>
        bX A p.1 p.2)
          ⟨e, fun i =>
            y ⟨e.face i,
              (eu e
                (e.face i)).2 ⟨i, rfl⟩⟩⟩
  apply congrArg
    (fun p :
        (Σ f : aj k r,
          Fin (f.ay.1 + 1) → G) =>
      bX A p.1 p.2)
  have he :
      bB
          (aK e)
          (cI e)
          (cQ e) = e :=
    mN e
  apply Sigma.ext he
  simp only
  apply Function.hfunext
    (congrArg
      (fun f : aj k r =>
        Fin (f.ay.1 + 1)) he)
  intro i i' GW
  apply heq_of_eq
  unfold eb
  apply congrArg y
  apply Subtype.ext
  have hn :
      (bB
          (aK e)
          (cI e)
          (cQ e)).ay.1 + 1 =
        e.ay.1 + 1 :=
    congrArg (fun f : aj k r =>
      f.ay.1 + 1) he
  have xq : i.1 = i'.1 := by
    have hcast :
        cast (congrArg Fin hn) i = i' := by
      exact eq_of_heq
        ((cast_heq (congrArg Fin hn) i).trans GW)
    calc
      i.1 = (cast (congrArg Fin hn) i).1 := by
        symm
        have C2 :
            ∀ {m n : ℕ} (h : m = n) (a : Fin m),
              (cast (congrArg Fin h) a).1 = a.1 := by
          intro m n h a
          cases h
          rfl
        exact C2 hn i
      _ = i'.1 := congrArg Fin.val hcast
  rw [Finset.coe_orderIsoOfFin_apply]
  calc
    (aK e).orderEmbOfFin _ i =
        (aK e).orderEmbOfFin _ i' :=
      Finset.orderEmbOfFin_eq_orderEmbOfFin_iff.mpr xq
    _ = e.face i' := by
      simpa only [Finset.coe_orderIsoOfFin_apply] using
        n4 e i'
theorem dF
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : aa G k r}
    (A : ai G k r C) :
    ah.eI
      (aC k r)
      (ar A) := by
  intro t ht y
  unfold ar
  by_cases vS : t.Nonempty
  · simp only [dif_pos vS]
    by_cases pv : t.card ≤ r
    · simp only [dif_pos pv]
      exact
        ⟨mL A _ _,
          mM A _ _⟩
    · simp [pv]
  · simp [vS]
theorem fW
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : aa G k r}
    (A : ai G k r C) :
    ah.eX
      (aC k r)
      (ar A) := by
  intro t ht y
  unfold ar
  by_cases vS : t.Nonempty
  · simp only [dif_pos vS]
    by_cases pv : t.card ≤ r
    · simp only [dif_pos pv]
      simpa [bX, pow_two] using
        (kS
          (C.partition
            (bB t vS pv).ay.succ
            (bB t vS pv).face)
          (A.atom
            (bB t vS pv).ay.succ
            (bB t vS pv).face)
          (eb t vS pv y))
    · simp [pv]
  · simp [vS]
noncomputable def bn
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : ak G k r)
    (A : ai G k r P.an) :
    Finset (Fin k) → ℝ := by
  classical
  intro t
  by_cases ht : t.Nonempty
  · by_cases pv : t.card ≤ r
    · exact bq P A
        (bB t ht pv)
    · exact 1
  · exact 1
@[simp]
theorem gy
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : ak G k r)
    (A : ai G k r P.an) :
    bn P A ∅ = 1 := by
  simp [bn]
@[simp]
theorem sW
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : ak G k r)
    (A : ai G k r P.an)
    (e : aj k r) :
    bn P A
        (aK e) =
      bq P A e := by
  classical
  unfold bn
  simp only [dif_pos (cI e)]
  have fE :
      (aK e).card ≤ r := by
    simpa [b1] using
      cQ e
  simp only [dif_pos fE]
  exact congrArg (bq P A)
    (mN e)
theorem kr
    {G : Type*} {k r : ℕ}
    {g : Finset (Fin k)}
    (hg :
      g ∈ (aD k r).edges)
    (x : Fin k → G) :
    (aD k r).ds hg
          (ah.bo g x) =
      fun j => x j.1 := by
  funext j
  have hj :
      (((aD k r).cp hg).symm j).1 =
        j.1 := by
    have z5 :=
      congrArg Subtype.val
        (((aD k r).cp hg).apply_symm_apply j)
    change
      (aD k r).projection
          (((aD k r).cp hg).symm j).1 =
        j.1 at z5
    change
      (((aD k r).cp hg).symm j).1 =
        j.1 at z5
    exact z5
  unfold ah.ds
    ah.bo
  exact congrArg x hj
theorem lz
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : aa G k r}
    (A : ai G k r C)
    (x : Fin k → G) :
    (aD k r).ao
          (ar A) ∅
          (ah.bo ∅ x) = 1 := by
  rw [(aD k r).b4
      (ar A)
      (jb k r)]
  exact fk A _
theorem hR
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : aa G k r}
    (A : ai G k r C)
    (e : aj k r)
    (x : Fin k → G) :
    (aD k r).ao
          (ar A)
          (aK e)
          (ah.bo
            (aK e) x) =
      bX A e
        (aI e.face x) := by
  have tV :
      aK e ∈
        (aD k r).edges := by
    rw [d8,
      ek]
    exact cQ e
  rw [(aD k r).b4
    (ar A) tV]
  have fH :
      (aK e).image
          (aD k r).projection =
        aK e := by
    simpa only [hO] using
      (Finset.image_id :
        (aK e).image id =
          aK e)
  have Ff :
      (⟨(aK e).image
            (aD k r).projection,
          (aD k r).ds
            tV
            (ah.bo
              (aK e) x)⟩ :
        Σ t : Finset (Fin k), ({j : Fin k // j ∈ t} → G)) =
      ⟨aK e,
        ah.bo
          (aK e) x⟩ := by
    apply Sigma.ext fH
    simp only
    apply Function.hfunext
      (congrArg
        (fun t : Finset (Fin k) =>
          {j : Fin k // j ∈ t}) fH)
    intro j j' GX
    apply heq_of_eq
    rw [congrFun
      (kr
        tV x) j]
    apply congrArg x
    exact
      (Subtype.heq_iff_coe_eq
        (fun v : Fin k => by
          rw [fH])).1 GX
  have sM :=
    congrArg
      (fun p :
          (Σ t : Finset (Fin k),
            ({j : Fin k // j ∈ t} → G)) =>
        ar A p.1 p.2)
      Ff
  rw [sM]
  rw [jV]
  apply congrArg (bX A e)
  funext i
  rfl
theorem lQ
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : aa G k r}
    (A : ai G k r C)
    (x : Fin k → G) :
    (aD k r).cy
        ((aD k r).ao
            (ar A)) x =
      bV A Finset.univ x := by
  classical
  change
    (∏ g ∈ (aD k r).edges,
      (aD k r).ao
          (ar A) g
          (ah.bo g x)) =
      bV A Finset.univ x
  rw [d8]
  change
    (∏ g ∈ insert ∅
        (Finset.univ.image
          (aK :
            aj k r → Finset (Fin k))),
      (aD k r).ao
          (ar A) g
          (ah.bo g x)) =
      bV A Finset.univ x
  rw [
    Finset.prod_insert
      (ie k r)]
  rw [lz]
  simp only [one_mul]
  rw [Finset.prod_image
    eQ.injOn]
  unfold bV
  apply Finset.prod_congr rfl
  intro e he
  exact
    hR
      A e x
theorem mO
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : aa G k r}
    (A : ai G k r C) :
    (aD k r).a7
        ((aD k r).ao
            (ar A)) =
      c9 A := by
  unfold ah.a7
    c9 fw
  apply congrArg mean
  funext x
  exact lQ A x
theorem kJ
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : ak G k r)
    (A : ai G k r P.an) :
    (aD k r).a0
          (bn P A) =
      ∏ e : aj k r,
        bq P A e := by
  classical
  change
    (∏ g ∈ (aD k r).edges,
      bn P A
        (g.image
          (aD k r).projection)) =
      ∏ e : aj k r,
        bq P A e
  rw [d8,
    hO]
  simp only [Function.id_def, Finset.image_id']
  change
    (∏ g ∈ insert ∅
        (Finset.univ.image
          (aK :
            aj k r → Finset (Fin k))),
      bn P A g) =
      ∏ e : aj k r,
        bq P A e
  rw [
    Finset.prod_insert
      (ie k r),
    gy,
    one_mul]
  rw [Finset.prod_image
    eQ.injOn]
  simp
end av.ag
end
section
namespace av.ag
open scoped BigOperators
namespace ah
variable {J K G : Type*}
  [DecidableEq J] [DecidableEq K]
  {H : Finset (Finset J)}
theorem ks
    (B C : ah J K H)
    (Et : C.edges ⊆ B.edges)
    (iK : B.projection = C.projection)
    (A : cM J G)
    (x : K → G) :
    C.cy (B.ao A) x =
      C.cy (C.ao A) x := by
  unfold cy
  apply Finset.prod_congr rfl
  intro g hg
  exact B.iv
    C A iK (Et hg) hg (bo g x)
theorem gs
    [Fintype K] [Fintype G]
    (B C : ah J K H)
    (Et : C.edges ⊆ B.edges)
    (iK : B.projection = C.projection)
    (A : cM J G) :
    C.a7 (B.ao A) =
      C.a7 (C.ao A) := by
  unfold a7
  apply congrArg mean
  funext x
  exact B.ks
    C Et iK A x
theorem mP
    [Fintype K] [Fintype G]
    (B : ah J K H)
    (g₀ : Finset K) (A : cM J G) :
    (B.cK g₀).a7
        (B.ao A) =
      (B.cK g₀).a7
        ((B.cK g₀).ao A) := by
  apply B.gs
    (B.cK g₀)
  · exact Finset.erase_subset _ _
  · rfl
theorem qw
    (B : ah J K H)
    (dv : B.a6)
    (g₀ : Finset K) :
    ((B.bu g₀.card).aU g₀).a6 := by
  apply (B.bu g₀.card).qh
    g₀
  intro g hg f ri
  have wT :
      g ∈ (B.bu g₀.card).edges :=
    Finset.mem_of_mem_erase hg
  have DK :
      f ∈ (B.bu g₀.card).edges :=
    B.wZ dv g₀.card
      wT ri
  apply Finset.mem_erase.mpr
  refine ⟨?_, DK⟩
  intro D8
  subst f
  have oP :
      g.card < g₀.card :=
    ((B.rC g₀.card g).1
      wT).2
  have DL : g₀.card ≤ g.card :=
    Finset.card_le_card ri
  exact (Nat.not_le_of_gt oP) DL
theorem pR
    (B : ah J K H)
    {g₀ : Finset K} (hg₀ : g₀.Nonempty) :
    ((B.bu g₀.card).aU g₀).order <
      g₀.card := by
  exact
    ((B.bu g₀.card).tM
      g₀).trans_lt
      (B.vV
        (Finset.card_pos.mpr hg₀))
theorem qc
    (B : ah J K H)
    (g₀ : Finset K) :
    ((B.bu g₀.card).aU g₀).edges.card ≤
      2 * B.edges.card := by
  calc
    ((B.bu g₀.card).aU g₀).edges.card =
        ((B.bu g₀.card).gG g₀).card := by
      rfl
    _ ≤
        2 *
          ((B.bu g₀.card).edges.erase g₀).card :=
      (B.bu g₀.card).vk g₀
    _ ≤ 2 * (B.bu g₀.card).edges.card :=
      Nat.mul_le_mul_left 2
        Finset.card_erase_le
    _ ≤ 2 * B.edges.card :=
      Nat.mul_le_mul_left 2
        (B.t4 g₀.card)
theorem tW
    (B : ah J K H)
    (z6 : 0 < B.order) :
    ∃ g₀ ∈ B.edges,
      g₀.card = B.order ∧
        ∀ g ∈ B.edges, g.card ≤ g₀.card := by
  have tZ : B.edges.Nonempty := by
    by_contra yc
    have GY : B.edges = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp yc
    simp [order, GY] at z6
  obtain ⟨g₀, hg₀, Eu⟩ :=
    Finset.exists_mem_eq_sup B.edges tZ Finset.card
  refine ⟨g₀, hg₀, ?_, ?_⟩
  · simpa [order] using Eu.symm
  · intro g hg
    rw [← Eu]
    exact Finset.le_sup hg
theorem l1
    {count main error : ℝ}
    (vb : |count - main| ≤ error * main) :
    count ≤ (1 + error) * main := by
  have Hk : count - main ≤ |count - main| :=
    le_abs_self _
  calc
    count ≤ main + |count - main| := by
      linarith
    _ ≤ main + error * main :=
      add_le_add_right vb main
    _ = (1 + error) * main := by
      ring
theorem m6
    (B : ah J K H)
    (p : Finset J → ℝ) {a : ℝ}
    (ha : 0 ≤ a)
    (hp :
      ∀ g ∈ B.edges,
        a ≤ p (g.image B.projection)) :
    a ^ B.edges.card ≤ B.a0 p := by
  classical
  unfold a0
  calc
    a ^ B.edges.card =
        ∏ _g ∈ B.edges, a := by
      simp
    _ ≤
        ∏ g ∈ B.edges,
          p (g.image B.projection) := by
      apply Finset.prod_le_prod
      · intro g hg
        exact ha
      · intro g hg
        exact hp g hg
theorem lR
    (B : ah J K H)
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    (d3 : ∀ g ∈ B.edges, g.card ≤ g₀.card)
    (p : Finset J → ℝ) {a : ℝ}
    (A9 : 0 ≤ a) (GZ : a ≤ 1)
    (hp :
      ∀ e ∈ H, e.card = g₀.card →
        a ≤ p e) :
    a ^ B.edges.card ≤
      p (g₀.image B.projection) *
        B.c3 g₀ p := by
  let s :=
    (B.edges.erase g₀).filter
      (fun g => ¬ g.card < g₀.card)
  have Ev :
      s.card ≤ (B.edges.erase g₀).card :=
    B.rF g₀
  have Fh :
      a ^ s.card ≤
        B.c3 g₀ p :=
    B.sH
      d3 p A9 hp
  have hpow :
      a ^ (B.edges.erase g₀).card ≤
        a ^ s.card :=
    pow_le_pow_of_le_one A9 GZ Ev
  have DM :
      a ^ (B.edges.erase g₀).card ≤
        B.c3 g₀ p :=
    hpow.trans Fh
  have pJ :
      a ≤ p (g₀.image B.projection) := by
    apply hp _ (B.c4 g₀ hg₀)
    exact B.kc hg₀
  have Bu :
      0 ≤ p (g₀.image B.projection) :=
    A9.trans pJ
  calc
    a ^ B.edges.card =
        a * a ^ (B.edges.erase g₀).card := by
      rw [← Finset.card_erase_add_one hg₀,
        pow_succ, mul_comm]
    _ ≤
        p (g₀.image B.projection) *
          a ^ (B.edges.erase g₀).card :=
      mul_le_mul_of_nonneg_right pJ
        (pow_nonneg A9 _)
    _ ≤
        p (g₀.image B.projection) *
          B.c3 g₀ p :=
      mul_le_mul_of_nonneg_left DM Bu
theorem ma
    [Fintype K] [Fintype G] [Nonempty G]
    (B : ah J K H)
    (A : cM J G)
    (p : Finset J → ℝ)
    (yP :
      ∀ y :
        {j : J // j ∈ (∅ : Finset J)} → G,
        A ∅ y = 1)
    (yQ : p ∅ = 1)
    (z6 : B.order = 0) :
    B.a7 (B.ao A) =
      B.a0 p := by
  have yd :
      ∀ g ∈ B.edges, g = ∅ := by
    intro g hg
    apply Finset.card_eq_zero.mp
    exact Nat.le_zero.mp
      (z6 ▸ B.mn hg)
  have xr :
      ∀ x : K → G,
        B.cy
            (B.ao A) x = 1 := by
    intro x
    unfold cy
    apply Finset.prod_eq_one
    intro g hg
    have FH : g = ∅ :=
      yd g hg
    subst g
    rw [B.b4 A hg]
    exact yP _
  have Bi :
      B.a0 p = 1 := by
    unfold a0
    apply Finset.prod_eq_one
    intro g hg
    rw [yd g hg]
    simp [yQ]
  rw [Bi]
  unfold a7
  calc
    mean
        (B.cy
          (B.ao A)) =
        mean (fun _x : K → G => 1) := by
      apply congrArg mean
      funext x
      exact xr x
    _ = 1 := ml 1
end ah
universe uJ uG
variable {J : Type uJ} {G : Type uG}
  [DecidableEq J] [Fintype G] [DecidableEq G]
  {H : Finset (Finset J)}
def iZ
    (A : ah.cM J G)
    (p : Finset J → ℝ)
    (β : ℕ → ℝ) (τ : ℝ) : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K]
    (B : ah J K H),
    B.a6 →
    ∀ {g₀ : Finset K}, g₀ ∈ B.edges →
      (∀ g ∈ B.edges, g.card ≤ g₀.card) →
      |B.a7 (B.ao A) -
          p (g₀.image B.projection) *
            (B.cK g₀).a7
              ((B.cK g₀).ao A)| ≤
        Real.sqrt
            (β g₀.card *
              (B.a8 g₀).a7
                ((B.a8 g₀).ao A) *
              ((B.bu g₀.card).aU g₀).a7
                (((B.bu g₀.card).aU g₀).ao
                  A)) +
          τ
omit [DecidableEq G] in
theorem jl
    [Nonempty G]
    (A : ah.cM J G)
    (p : Finset J → ℝ)
    (α β μ : ℕ → ℝ) (τ : ℝ)
    (E : ℕ → ℕ → ℝ)
    (wq :
      ah.eI H A)
    (_hAidempotent :
      ah.eX H A)
    (yP :
      ∀ y :
        {j : J // j ∈ (∅ : Finset J)} → G,
        A ∅ y = 1)
    (yQ : p ∅ = 1)
    (yR :
      ∀ e ∈ H, α e.card ≤ p e)
    (ow :
      iZ
        (H := H) A p β τ)
    (hE :
      cX α β μ τ E)
    {K : Type} [Fintype K] [DecidableEq K]
    (B : ah J K H)
    (dv : B.a6) :
    |B.a7 (B.ao A) -
        B.a0 p| ≤
      E B.order B.edges.card *
        B.a0 p := by
  let P : ℕ → ℕ → Prop :=
    fun d n =>
      ∀ (K' : Type) [Fintype K'] [DecidableEq K']
        (C : ah J K' H),
        C.order ≤ d →
        C.edges.card ≤ n →
        C.a6 →
        |C.a7 (C.ao A) -
            C.a0 p| ≤
          E d n * C.a0 p
  have wz :
      ∀ e ∈ H, 0 ≤ p e := by
    intro e he
    exact (hE.sV e.card).le.trans
      (yR e he)
  unfold iZ at ow
  have hP : ∀ d n, P d n := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d yS =>
        intro n
        induction n using Nat.strong_induction_on with
        | h n Ci =>
            dsimp [P]
            intro K' _instK' _decK' C Ew Ex sN
            by_cases sO : C.order = d
            · by_cases sP : C.edges.card = n
              · by_cases Cj : d = 0
                · have hzero : C.order = 0 :=
                    sO.trans Cj
                  have Ey :=
                    C.ma
                      A p yP yQ hzero
                  rw [Ey, sub_self, abs_zero]
                  exact mul_nonneg
                    (hE.pF d n)
                    (C.es p wz)
                · have zF : 0 < d :=
                    Nat.pos_of_ne_zero Cj
                  obtain ⟨g₀, hg₀, oP, d3⟩ :=
                    C.tW
                      (sO.symm ▸ zF)
                  have vc : g₀.card = d :=
                    oP.trans sO
                  have Ba : g₀.Nonempty := by
                    apply Finset.card_pos.mp
                    rw [vc]
                    exact zF
                  obtain ⟨d₀, rfl⟩ :=
                    Nat.exists_eq_succ_of_ne_zero Cj
                  have G0 : n ≠ 0 := by
                    intro hn
                    have Ck : C.edges.card = 0 :=
                      sP.trans hn
                    exact
                      (Finset.card_ne_zero.mpr
                        ⟨g₀, hg₀⟩) Ck
                  obtain ⟨n₀, rfl⟩ :=
                    Nat.exists_eq_succ_of_ne_zero G0
                  let nN := C.cK g₀
                  let iz := C.a8 g₀
                  let lA :=
                    (C.bu g₀.card).aU g₀
                  have zn :
                      nN.a6 :=
                    C.oa
                      sN hg₀ d3
                  have z7 :
                      nN.order ≤ d₀ + 1 := by
                    exact
                      (C.sX g₀).trans_eq
                        sO
                  have AN :
                      nN.edges.card ≤ n₀ := by
                    have fE :
                        nN.edges.card = n₀ := by
                      simp [nN,
                        Finset.card_erase_of_mem hg₀,
                        sP]
                    exact fE.le
                  have C3 :=
                    (Ci n₀ (Nat.lt_succ_self n₀))
                      K' nN z7
                        AN zn
                  have xE :
                      iz.a6 :=
                    C.u1 sN g₀
                  have ye :
                      iz.order ≤ d₀ := by
                    have Ez :
                        iz.order < d₀ + 1 := by
                      simpa [iz, vc,
                        Nat.succ_eq_add_one] using
                        C.uu Ba
                    omega
                  have yT :
                      iz.edges.card ≤ n₀ + 1 := by
                    exact
                      (C.sF g₀).trans_eq
                        sP
                  have AO :=
                    (yS d₀ (Nat.lt_succ_self d₀)
                      (n₀ + 1))
                      K' iz ye
                        yT xE
                  have zo :
                      lA.a6 := by
                    dsimp [lA]
                    exact C.qw
                      sN g₀
                  have z8 :
                      lA.order ≤ d₀ := by
                    have Ez :
                        lA.order < d₀ + 1 := by
                      simpa [lA, vc,
                        Nat.succ_eq_add_one] using
                        C.pR
                          Ba
                    omega
                  have AQ :
                      lA.edges.card ≤
                        2 * (n₀ + 1) := by
                    dsimp [lA]
                    exact
                      (C.qc
                        g₀).trans_eq
                        (congrArg (fun m => 2 * m)
                          sP)
                  have C4 :=
                    (yS d₀ (Nat.lt_succ_self d₀)
                      (2 * (n₀ + 1)))
                      (ah.bs g₀)
                      lA z8
                        AQ zo
                  let jW :=
                    nN.a0 p
                  let hU :=
                    iz.a0 p
                  let mQ :=
                    lA.a0 p
                  let fK :=
                    (C.bu g₀.card).a0 p
                  let sQ :=
                    C.c3 g₀ p
                  let i0 := C.a0 p
                  let gT :=
                    nN.a7
                      (nN.ao A)
                  let f9 :=
                    iz.a7
                      (iz.ao A)
                  let h6 :=
                    lA.a7
                      (lA.ao A)
                  let p₀ :=
                    p (g₀.image C.projection)
                  have E3 : 0 ≤ jW := by
                    dsimp [jW, nN]
                    exact
                      (C.cK g₀).es p wz
                  have yU :
                      0 ≤ hU := by
                    dsimp [hU, iz]
                    exact
                      (C.a8 g₀).es p wz
                  have E4 :
                      0 ≤ mQ := by
                    dsimp [mQ, lA]
                    exact
                      ((C.bu g₀.card).aU g₀).es
                        p wz
                  have uh :
                      0 ≤ fK := by
                    dsimp [fK]
                    exact
                      (C.bu g₀.card).es p wz
                  have DN : 0 ≤ i0 := by
                    dsimp [i0]
                    exact C.es p wz
                  have DA :
                      0 ≤ f9 := by
                    dsimp [f9, iz]
                    exact
                      (C.a8 g₀).mo
                        ((C.a8 g₀).en
                            A wq)
                  have z9 :
                      0 ≤ h6 := by
                    dsimp [h6, lA]
                    exact
                      ((C.bu g₀.card).aU g₀).mo
                          (ah.en
                            ((C.bu g₀.card).aU g₀) A wq)
                  have yV :
                      f9 ≤
                        (1 + E d₀ (n₀ + 1)) *
                          hU :=
                    ah.l1
                      AO
                  have AR :
                      h6 ≤
                        (1 + E d₀
                            (2 * (n₀ + 1))) *
                          mQ :=
                    ah.l1
                      C4
                  have Aa :
                      0 ≤
                        (1 + E d₀ (n₀ + 1)) *
                          (1 + E d₀
                            (2 * (n₀ + 1))) :=
                    hE.uv d₀ n₀
                  have w5 :
                      0 ≤ 1 + E d₀ (n₀ + 1) := by
                    linarith
                      [hE.pF d₀ (n₀ + 1)]
                  have C5 :
                      0 ≤ β (d₀ + 1) :=
                    hE.vN _
                  have s7 :
                      β (d₀ + 1) *
                            f9 * h6 ≤
                        β (d₀ + 1) *
                            ((1 + E d₀ (n₀ + 1)) *
                              hU) *
                          ((1 + E d₀
                              (2 * (n₀ + 1))) *
                            mQ) := by
                    calc
                      β (d₀ + 1) *
                            f9 * h6 ≤
                          β (d₀ + 1) *
                              ((1 + E d₀ (n₀ + 1)) *
                                hU) *
                            h6 :=
                        mul_le_mul_of_nonneg_right
                          (mul_le_mul_of_nonneg_left
                            yV C5)
                          z9
                      _ ≤
                          β (d₀ + 1) *
                              ((1 + E d₀ (n₀ + 1)) *
                                hU) *
                            ((1 + E d₀
                                (2 * (n₀ + 1))) *
                              mQ) :=
                        mul_le_mul_of_nonneg_left
                          AR
                          (mul_nonneg C5
                            (mul_nonneg
                              w5
                              yU))
                  let dm :=
                    Real.sqrt
                      (β (d₀ + 1) *
                        (1 + E d₀ (n₀ + 1)) *
                        (1 + E d₀
                          (2 * (n₀ + 1))))
                  have xF :
                      0 ≤ dm :=
                    Real.sqrt_nonneg _
                  have wI :
                      hU * mQ =
                        fK ^ 2 := by
                    dsimp [hU, mQ,
                      fK, iz, lA]
                    exact
                      C.ld
                        g₀ p
                  have zq :
                      0 ≤
                        β (d₀ + 1) *
                          (1 + E d₀ (n₀ + 1)) *
                          (1 + E d₀
                            (2 * (n₀ + 1))) := by
                    rw [mul_assoc]
                    exact mul_nonneg C5 Aa
                  have x2 :
                      Real.sqrt
                            (β (d₀ + 1) *
                              f9 * h6) ≤
                        dm * fK := by
                    calc
                      Real.sqrt
                            (β (d₀ + 1) *
                              f9 * h6) ≤
                          Real.sqrt
                            (β (d₀ + 1) *
                              ((1 + E d₀ (n₀ + 1)) *
                                hU) *
                              ((1 + E d₀
                                  (2 * (n₀ + 1))) *
                                mQ)) :=
                        Real.sqrt_le_sqrt s7
                      _ =
                          Real.sqrt
                              ((β (d₀ + 1) *
                                  (1 + E d₀ (n₀ + 1)) *
                                  (1 + E d₀
                                    (2 * (n₀ + 1)))) *
                                (hU * mQ)) := by
                        congr 1
                        ring
                      _ =
                          Real.sqrt
                              ((β (d₀ + 1) *
                                  (1 + E d₀ (n₀ + 1)) *
                                  (1 + E d₀
                                    (2 * (n₀ + 1)))) *
                                fK ^ 2) := by
                        congr 1
                        rw [wI]
                      _ = dm * fK := by
                        dsimp [dm]
                        rw [Real.sqrt_mul zq]
                        rw [Real.sqrt_sq uh]
                  have FY :
                      α (d₀ + 1) ^ (n₀ + 1) ≤
                        p₀ * sQ := by
                    dsimp [p₀, sQ]
                    have hpow :=
                      C.lR
                        hg₀ d3 p
                        (hE.sV g₀.card).le
                        (hE.density_le_one g₀.card)
                        (fun e he fE =>
                          yR e he |>
                            fun h => by
                              simpa [fE] using h)
                    simpa [vc, sP,
                      Nat.succ_eq_add_one] using hpow
                  have Cl :
                      0 < α (d₀ + 1) ^ (n₀ + 1) :=
                    pow_pos (hE.sV _) _
                  have AS :
                      fK * (p₀ * sQ) =
                        i0 := by
                    dsimp [fK, p₀, sQ,
                      i0, nN]
                    calc
                      (C.bu g₀.card).a0 p *
                          (p (g₀.image C.projection) *
                            C.c3
                              g₀ p) =
                          ((C.bu g₀.card).a0 p *
                            C.c3
                              g₀ p) *
                            p (g₀.image C.projection) := by
                        ring
                      _ =
                          (C.cK g₀).a0 p *
                            p (g₀.image C.projection) := by
                        rw [
                          C.mv
                            g₀ p]
                      _ = C.a0 p :=
                        C.lW
                          p hg₀
                  have yf :
                      Real.sqrt
                            (β (d₀ + 1) *
                              f9 * h6) ≤
                        (dm /
                            α (d₀ + 1) ^ (n₀ + 1)) *
                          i0 := by
                    have DO :
                        dm ≤
                          (dm /
                              α (d₀ + 1) ^ (n₀ + 1)) *
                            (p₀ * sQ) := by
                      calc
                        dm =
                            (dm /
                              α (d₀ + 1) ^ (n₀ + 1)) *
                              α (d₀ + 1) ^ (n₀ + 1) := by
                          field_simp
                        _ ≤
                            (dm /
                              α (d₀ + 1) ^ (n₀ + 1)) *
                              (p₀ * sQ) :=
                          mul_le_mul_of_nonneg_left FY
                            (div_nonneg xF
                              Cl.le)
                    calc
                      Real.sqrt
                            (β (d₀ + 1) *
                              f9 * h6) ≤
                          dm * fK :=
                        x2
                      _ ≤
                          ((dm /
                              α (d₀ + 1) ^ (n₀ + 1)) *
                            (p₀ * sQ)) *
                              fK :=
                        mul_le_mul_of_nonneg_right
                          DO uh
                      _ =
                          (dm /
                              α (d₀ + 1) ^ (n₀ + 1)) *
                            i0 := by
                        rw [← AS]
                        ring
                  have DP :
                      μ (d₀ + 1) ^ (n₀ + 1) ≤
                        i0 := by
                    dsimp [i0]
                    have hpow :=
                      C.m6
                        p (hE.floor_pos (d₀ + 1)).le
                        (fun g hg => by
                          have fE :
                              g.card ≤ d₀ + 1 := by
                            exact
                              (C.mn hg).trans_eq
                                (by
                                  simpa [Nat.succ_eq_add_one] using
                                    sO)
                          exact
                            (hE.y1 fE).trans
                              (yR _
                                (C.c4 g hg) |>
                                  fun h => by
                                    simpa [C.kc hg]
                                      using h))
                    simpa [sP] using hpow
                  have Cm :
                      0 < μ (d₀ + 1) ^ (n₀ + 1) :=
                    pow_pos (hE.floor_pos _) _
                  have wJ :
                      τ ≤
                        (τ /
                            μ (d₀ + 1) ^ (n₀ + 1)) *
                          i0 := by
                    calc
                      τ =
                          (τ /
                            μ (d₀ + 1) ^ (n₀ + 1)) *
                              μ (d₀ + 1) ^ (n₀ + 1) := by
                        field_simp
                      _ ≤
                          (τ /
                            μ (d₀ + 1) ^ (n₀ + 1)) *
                            i0 :=
                        mul_le_mul_of_nonneg_left DP
                          (div_nonneg hE.u3
                            Cm.le)
                  have C6 :=
                    ow K' C sN hg₀ d3
                  have yg :
                      |C.a7
                              (C.ao A) -
                            p₀ * gT| ≤
                        (dm /
                              α (d₀ + 1) ^ (n₀ + 1) +
                            τ /
                              μ (d₀ + 1) ^ (n₀ + 1)) *
                          i0 := by
                    calc
                      |C.a7
                              (C.ao A) -
                            p₀ * gT| ≤
                          Real.sqrt
                              (β (d₀ + 1) *
                                f9 * h6) +
                            τ := by
                        simpa [p₀, gT,
                          f9, h6,
                          nN, iz, lA,
                          vc] using C6
                      _ ≤
                          (dm /
                              α (d₀ + 1) ^ (n₀ + 1)) *
                              i0 +
                            (τ /
                              μ (d₀ + 1) ^ (n₀ + 1)) *
                              i0 :=
                        add_le_add yf
                          wJ
                      _ =
                          (dm /
                                α (d₀ + 1) ^ (n₀ + 1) +
                              τ /
                                μ (d₀ + 1) ^ (n₀ + 1)) *
                            i0 := by
                        ring
                  have Cn : 0 ≤ p₀ := by
                    dsimp [p₀]
                    exact wz _
                      (C.c4 g₀ hg₀)
                  have ui :
                      p₀ * jW = i0 := by
                    dsimp [p₀, jW, i0,
                      nN]
                    rw [mul_comm]
                    exact
                      C.lW
                        p hg₀
                  have xG :
                      p₀ *
                          |gT - jW| ≤
                        E (d₀ + 1) n₀ * i0 := by
                    calc
                      p₀ *
                            |gT - jW| ≤
                          p₀ *
                            (E (d₀ + 1) n₀ *
                              jW) :=
                        mul_le_mul_of_nonneg_left
                          C3 Cn
                      _ =
                          E (d₀ + 1) n₀ * i0 := by
                        rw [← ui]
                        ring
                  have Bv :
                      C.a7
                            (C.ao A) -
                          i0 =
                        (C.a7
                              (C.ao A) -
                            p₀ * gT) +
                          p₀ * (gT - jW) := by
                    rw [← ui]
                    ring
                  rw [Bv]
                  calc
                    |(C.a7
                              (C.ao A) -
                            p₀ * gT) +
                          p₀ * (gT - jW)| ≤
                        |C.a7
                              (C.ao A) -
                            p₀ * gT| +
                          |p₀ * (gT - jW)| :=
                      abs_add_le _ _
                    _ =
                        |C.a7
                              (C.ao A) -
                            p₀ * gT| +
                          p₀ * |gT - jW| := by
                      rw [abs_mul, abs_of_nonneg Cn]
                    _ ≤
                        (dm /
                              α (d₀ + 1) ^ (n₀ + 1) +
                            τ /
                              μ (d₀ + 1) ^ (n₀ + 1)) *
                            i0 +
                          E (d₀ + 1) n₀ * i0 :=
                      add_le_add yg
                        xG
                    _ =
                        (E (d₀ + 1) n₀ +
                            (dm /
                                α (d₀ + 1) ^ (n₀ + 1) +
                              τ /
                                μ (d₀ + 1) ^ (n₀ + 1))) *
                          i0 := by
                      ring
                    _ ≤
                        E (d₀ + 1) (n₀ + 1) *
                          i0 := by
                      apply mul_le_mul_of_nonneg_right
                      · simpa [dm,
                          jM,
                          add_assoc] using
                          hE.vn d₀ n₀
                      · exact DN
              · have DQ : C.edges.card < n :=
                  lt_of_le_of_ne Ex
                    sP
                have wK :=
                  (Ci C.edges.card DQ)
                    K' C Ew le_rfl sN
                have Ac :
                    0 ≤ C.a0 p :=
                  C.es p wz
                exact wK.trans
                  (mul_le_mul_of_nonneg_right
                    (hE.uB Ex) Ac)
            · have C7 : C.order < d :=
                lt_of_le_of_ne Ew
                  sO
              have wK :=
                (yS C.order C7 n)
                  K' C le_rfl Ex sN
              have Ac :
                  0 ≤ C.a0 p :=
                C.es p wz
              exact wK.trans
                (mul_le_mul_of_nonneg_right
                  (hE.q0 Ew) Ac)
  exact
    (hP B.order B.edges.card)
      K B le_rfl le_rfl dv
end av.ag
end
section
namespace av.ag
open scoped BigOperators
namespace ah
variable {G : Type*} [Fintype G] [DecidableEq G]
  {k r : ℕ}
theorem fo
    {K : Type*} [DecidableEq K]
    (B : ah (Fin k) K
      (aC k r))
    {g : Finset K} (_hg : g ∈ B.edges)
    (bt : g.Nonempty) :
    (g.image B.projection).Nonempty := by
  exact Finset.image_nonempty.mpr bt
theorem ew
    {K : Type*} [DecidableEq K]
    (B : ah (Fin k) K
      (aC k r))
    {g : Finset K} (hg : g ∈ B.edges) :
    (g.image B.projection).card ≤ r := by
  exact
    (ek
      (g.image B.projection)).1
      (B.c4 g hg)
noncomputable def aw
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : ah (Fin k) K
      (aC k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (bt : g.Nonempty) :
    aj k r :=
  bB
    (g.image B.projection)
    (B.fo hg bt)
    (B.ew hg)
noncomputable def bC
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : ah (Fin k) K
      (aC k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (bt : g.Nonempty)
    (y : {v : K // v ∈ g} → G) :
    Fin ((B.aw hg bt).ay.1 + 1) → G :=
  eb
    (g.image B.projection)
    (B.fo hg bt)
    (B.ew hg)
    (B.ds hg y)
noncomputable def f1
    {K : Type*} [Fintype K] [DecidableEq K]
    (P : ak G k r)
    (A : ai G k r P.an)
    (B : ah (Fin k) K
      (aC k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (bt : g.Nonempty)
    (y : {v : K // v ∈ g} → G) : ℝ :=
  gM P A
    (B.aw hg bt)
    (B.bC hg bt y)
noncomputable def fQ
    {K : Type*} [Fintype K] [DecidableEq K]
    (P : ak G k r)
    (A : ai G k r P.an)
    (B : ah (Fin k) K
      (aC k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (bt : g.Nonempty)
    (y : {v : K // v ∈ g} → G) : ℝ :=
  kU P A
    (B.aw hg bt)
    (B.bC hg bt y)
theorem mR
    {K : Type*} [Fintype K] [DecidableEq K]
    (P : ak G k r)
    (A : ai G k r P.an)
    (B : ah (Fin k) K
      (aC k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (bt : g.Nonempty) :
    bn P A
        (g.image B.projection) =
      bq P A
        (B.aw hg bt) := by
  unfold bn
  simp only [
    dif_pos (B.fo hg bt),
    dif_pos (B.ew hg)]
  rfl
theorem lj
    {K : Type*} [Fintype K] [DecidableEq K]
    (P : ak G k r)
    (A : ai G k r P.an)
    (B : ah (Fin k) K
      (aC k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (bt : g.Nonempty)
    (y : {v : K // v ∈ g} → G) :
    B.ao
          (ar A) g y =
      bn P A
          (g.image B.projection) +
        B.f1 P A hg bt y +
        B.fQ P A hg bt y := by
  rw [B.b4
    (ar A) hg y]
  rw [B.mR
    P A hg bt]
  unfold ar
  simp only [
    dif_pos (B.fo hg bt),
    dif_pos (B.ew hg)]
  exact
    pg P A
      (B.aw hg bt)
      (B.bC hg bt y)
noncomputable def eG
    {K : Type*} [Fintype K] [DecidableEq K]
    (P : ak G k r)
    (A : ai G k r P.an)
    (B : ah (Fin k) K
      (aC k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (bt : g.Nonempty)
    (y : {v : K // v ∈ g} → G) : ℝ :=
  B.f1 P A hg bt y *
    B.cT g
      (B.ao
        (ar A)) y
def hV
    (P : ak G k r)
    (A : ai G k r P.an)
    (β : ℕ → ℝ) : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K]
    (B : ah (Fin k) K
      (aC k r)),
    B.a6 →
    ∀ {g₀ : Finset K}, (hg₀ : g₀ ∈ B.edges) →
      (∀ g ∈ B.edges, g.card ≤ g₀.card) →
      (bt : g₀.Nonempty) →
      mean (fun y =>
        B.eG
            P A hg₀ bt y ^ 2) ≤
        β g₀.card *
          (B.a8 g₀).a7
            ((B.a8 g₀).ao
              (ar A))
def g7
    (P : ak G k r)
    (A : ai G k r P.an)
    (τ : ℝ) : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K]
    (B : ah (Fin k) K
      (aC k r)),
    B.a6 →
    ∀ {g₀ : Finset K}, (hg₀ : g₀ ∈ B.edges) →
      (∀ g ∈ B.edges, g.card ≤ g₀.card) →
      (bt : g₀.Nonempty) →
      ∀ z : bd g₀ → G,
        |B.eW g₀
            (B.fQ
              P A hg₀ bt)
            (B.ao
              (ar A)) z| ≤
          τ
theorem mS
    [Nonempty G]
    (P : ak G k r)
    (A : ai G k r P.an)
    (β : ℕ → ℝ) (τ : ℝ)
    (gr : ∀ d, 0 ≤ β d)
    (iQ : 0 ≤ τ)
    (vm :
      hV P A β)
    (yy :
      g7 P A τ) :
    iZ
      (H := aC k r)
      (ar A)
      (bn P A)
      β τ := by
  intro K _instK _decK B dv g₀ hg₀ d3
  by_cases bt : g₀.Nonempty
  · let W :=
      B.ao
        (ar A)
    let p :=
      bn P A
        (g₀.image B.projection)
    let b :=
      B.f1
        P A hg₀ bt
    let c :=
      B.fQ
        P A hg₀ bt
    let yh :=
      B.eG
        P A hg₀ bt
    have yx :
        ∀ y, W g₀ y = p + b y + c y := by
      intro y
      simpa only [W, p, b, c] using
        B.lj
          P A hg₀ bt y
    have i1 :
        B.a7 W =
          p * (B.cK g₀).a7 W +
            B.bf g₀ b W +
            B.bf g₀ c W :=
      B.tq
        W hg₀ p b c yx
    have EA :
        (B.cK g₀).a7 W =
          (B.cK g₀).a7
            ((B.cK g₀).ao
              (ar A)) := by
      exact
        B.mP g₀
          (ar A)
    have AT :
        B.nB W := by
      exact B.ou
        (ar A)
        (fW A)
    have vd :
        B.bf g₀ b W =
          B.bf g₀ yh W := by
      change B.bf g₀ b W =
        B.bf g₀
          (fun y =>
            b y * B.cT g₀ W y) W
      exact B.lN
        g₀ b W AT
    have lf :
        |B.bf g₀ b W| ≤
          Real.sqrt
            ((β g₀.card *
                (B.a8 g₀).a7
                  ((B.a8 g₀).ao
                      (ar A))) *
              ((B.bu g₀.card).aU g₀).a7
                  (((B.bu g₀.card).aU g₀).ao
                      (ar A))) := by
      rw [vd]
      exact
        B.iH
          dv hg₀ d3
          (ar A)
          (dF A)
          (fW A)
          yh (gr g₀.card)
          (vm K B dv hg₀ d3 bt)
    have mZ :
        |B.bf g₀ c W| ≤ τ := by
      exact B.qB
        g₀ c W
        (yy K B dv hg₀ d3 bt)
    rw [i1, EA]
    calc
      |p *
              (B.cK g₀).a7
                ((B.cK g₀).ao
                  (ar A)) +
            B.bf g₀ b W +
            B.bf g₀ c W -
          p *
              (B.cK g₀).a7
                ((B.cK g₀).ao
                  (ar A))| =
          |B.bf g₀ b W +
            B.bf g₀ c W| := by
        congr 1
        ring
      _ ≤
          |B.bf g₀ b W| +
            |B.bf g₀ c W| :=
        abs_add_le _ _
      _ ≤
          Real.sqrt
              ((β g₀.card *
                  (B.a8 g₀).a7
                    ((B.a8 g₀).ao
                        (ar A))) *
                ((B.bu g₀.card).aU g₀).a7
                    (((B.bu g₀.card).aU g₀).ao
                        (ar A))) +
            τ :=
        add_le_add lf mZ
  · have Fi : g₀ = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp bt
    subst g₀
    let W :=
      B.ao
        (ar A)
    have sM :
        ∀ y, W ∅ y = 1 := by
      intro y
      dsimp only [W]
      rw [B.b4
        (ar A) hg₀ y]
      simp only [Finset.image_empty]
      exact fk A
        (B.ds hg₀ y)
    have i1 :
        B.a7 W =
          (B.cK ∅).a7
            ((B.cK ∅).ao
              (ar A)) := by
      calc
        B.a7 W =
            B.bf ∅ (W ∅) W :=
          B.lV W hg₀
        _ =
            B.bf ∅ (fun _ => 1) W := by
          apply congrArg
            (fun q => B.bf ∅ q W)
          funext y
          exact sM y
        _ = (B.cK ∅).a7 W := by
          rw [B.uE]
          simp
        _ =
            (B.cK ∅).a7
              ((B.cK ∅).ao
                (ar A)) :=
          B.mP ∅
            (ar A)
    rw [i1, Finset.image_empty,
      gy,
      one_mul, sub_self, abs_zero]
    exact add_nonneg (Real.sqrt_nonneg _) iQ
end ah
end av.ag
end
section
namespace av.ag
open scoped BigOperators
namespace ah
variable {G : Type*} [Fintype G] [DecidableEq G]
  {k r : ℕ}
theorem fL
    {J K : Type*} [DecidableEq J] [DecidableEq K]
    {H : Finset (Finset J)}
    (B : ah J K H)
    {g₀ g : Finset K}
    (hg : g ∈ B.edges.erase g₀)
    (d3 : ∀ f ∈ B.edges, f.card ≤ g₀.card) :
    ∃ v ∈ g₀, v ∉ g := by
  classical
  by_contra xH
  have DR : g₀ ⊆ g := by
    intro v hv
    by_contra xZ
    exact xH ⟨v, hv, xZ⟩
  have iq : g ∈ B.edges :=
    Finset.mem_of_mem_erase hg
  have heq : g₀ = g :=
    Finset.eq_of_subset_of_card_le DR (d3 g iq)
  exact (Finset.mem_erase.mp hg).1 heq.symm
noncomputable def qd
    {K : Type*} [Fintype K] [DecidableEq K]
    (P : ak G k r)
    (B : ah (Fin k) K
      (aC k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (bt : g.Nonempty) :
    aE
      (Fin ((B.aw hg bt).ay.1 + 1) →
        G) :=
  ⟨au
    (aV P.aQ
      (B.aw hg bt))
    (B.aw hg bt).face⟩
noncomputable def pS
    {K : Type*} [Fintype K] [DecidableEq K]
    (P : ak G k r)
    (A : ai G k r P.an)
    (B : ah (Fin k) K
      (aC k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (bt : g.Nonempty) :
    (Fin ((B.aw hg bt).ay.1 + 1) →
      G) → ℝ :=
  aB
    (P.an.partition
      (B.aw hg bt).ay.succ
      (B.aw hg bt).face)
    (A.atom
      (B.aw hg bt).ay.succ
      (B.aw hg bt).face)
def ga
    (P : ak G k r)
    (A : ai G k r P.an) : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K]
    (B : ah (Fin k) K
      (aC k r)),
    B.a6 →
    ∀ {g₀ : Finset K}, (hg₀ : g₀ ∈ B.edges) →
      (∀ g ∈ B.edges, g.card ≤ g₀.card) →
      (bt : g₀.Nonempty) →
      ∀ z : bd g₀ → G,
        ∃ u :
            cU G
              ((B.aw
                hg₀ bt).ay.1 + 1),
          eC u ∧
            B.eW g₀
                (B.fQ
                  P A hg₀ bt)
                (B.ao
                  (ar A)) z =
              (B.qd
                  P hg₀ bt).et
                (B.pS
                  P A hg₀ bt)
                u
theorem ja
    (P : ak G k r)
    (A : ai G k r P.an)
    (τ : ℝ)
    (dk :
      cu P (fun _ => τ))
    (FZ :
      ga P A) :
    g7 P A τ := by
  intro K _instK _decK B dv g₀ hg₀ d3 bt z
  obtain ⟨u, hu, C8⟩ :=
    FZ K B dv hg₀ d3 bt z
  rw [C8]
  exact
    oZ
      P A (fun _ => τ) dk
      (B.aw hg₀ bt)
      u hu
end ah
end av.ag
end
section
namespace av.ag
open scoped BigOperators
namespace ah
variable {G : Type*} [Fintype G] [DecidableEq G]
  {k r : ℕ}
noncomputable def jX
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : ah (Fin k) K
      (aC k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (bt : g.Nonempty) :
    Fin ((B.aw hg bt).ay.1 + 1) ≃
      {j : Fin k // j ∈ g.image B.projection} := by
  let t := g.image B.projection
  let e := B.aw hg bt
  have fE : t.card = e.ay.1 + 1 := by
    have tV :
        aK e = t := by
      dsimp [e, aw, t]
      exact cE
        (g.image B.projection)
        (B.fo hg bt)
        (B.ew hg)
    calc
      t.card = (aK e).card :=
        congrArg Finset.card tV.symm
      _ = e.rank := b1 e
      _ = e.ay.1 + 1 := rfl
  exact (t.orderIsoOfFin fE).toEquiv
noncomputable def h7
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : ah (Fin k) K
      (aC k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (bt : g.Nonempty) :
    Fin ((B.aw hg bt).ay.1 + 1) ≃
      {v : K // v ∈ g} :=
  (B.jX hg bt).trans
    (B.cp hg).symm
noncomputable def d9
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : ah (Fin k) K
      (aC k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (bt : g.Nonempty) :
    ({v : K // v ∈ g} → G) ≃
      (Fin ((B.aw hg bt).ay.1 + 1) →
        G) :=
  (Equiv.arrowCongr
      (B.cp hg)
      (Equiv.refl G)).trans
    (Equiv.arrowCongr
      (B.jX hg bt).symm
      (Equiv.refl G))
omit [Fintype G] [DecidableEq G] in
@[simp]
theorem q7
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : ah (Fin k) K
      (aC k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (bt : g.Nonempty)
    (y : {v : K // v ∈ g} → G) :
    B.d9 hg bt y =
      B.bC hg bt y := by
  funext i
  unfold d9 jX
    bC
    eb
  rfl
omit [Fintype G] [DecidableEq G] in
@[simp]
theorem jE
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : ah (Fin k) K
      (aC k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (bt : g.Nonempty)
    (x :
      Fin ((B.aw hg bt).ay.1 + 1) →
        G)
    (v : {v : K // v ∈ g}) :
    (B.d9 hg bt).symm x v =
      x ((B.h7 hg bt).symm v) := by
  rfl
noncomputable def gu
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : ah (Fin k) K
      (aC k r))
    {g₀ : Finset K}
    (d3 : ∀ g ∈ B.edges, g.card ≤ g₀.card)
    (bt : g₀.Nonempty)
    (g : Finset K) : {v : K // v ∈ g₀} :=
  if hg : g ∈ B.edges.erase g₀ then
    ⟨Classical.choose
        (B.fL hg d3),
      (Classical.choose_spec
        (B.fL hg d3)).1⟩
  else
    ⟨Classical.choose bt, Classical.choose_spec bt⟩
theorem qQ
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : ah (Fin k) K
      (aC k r))
    {g₀ g : Finset K}
    (d3 : ∀ f ∈ B.edges, f.card ≤ g₀.card)
    (bt : g₀.Nonempty)
    (hg : g ∈ B.edges.erase g₀) :
    (B.gu d3 bt g).1 ∉ g := by
  classical
  simp only [gu, dif_pos hg]
  exact
    (Classical.choose_spec
      (B.fL hg d3)).2
noncomputable def dh
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : ah (Fin k) K
      (aC k r))
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    (d3 : ∀ g ∈ B.edges, g.card ≤ g₀.card)
    (bt : g₀.Nonempty)
    (g : Finset K) :
    Fin ((B.aw hg₀ bt).ay.1 + 1) :=
  (B.h7 hg₀ bt).symm
    (B.gu d3 bt g)
noncomputable def k4
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : ah (Fin k) K
      (aC k r))
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    (bt : g₀.Nonempty)
    (i :
      Fin ((B.aw hg₀ bt).ay.1 + 1))
    (a : G)
    (y :
      Fin (B.aw hg₀ bt).ay.1 → G) :
    {v : K // v ∈ g₀} → G :=
  (B.d9 hg₀ bt).symm
    (Fin.insertNth i a y)
noncomputable def dX
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : ah (Fin k) K
      (aC k r))
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    (bt : g₀.Nonempty)
    (i :
      Fin ((B.aw hg₀ bt).ay.1 + 1))
    (a : G)
    (y :
      Fin (B.aw hg₀ bt).ay.1 → G)
    (z : bd g₀ → G) : K → G :=
  (bF g₀).symm
    (B.k4 hg₀ bt i a y, z)
omit [Fintype G] [DecidableEq G] in
theorem lB
    {K : Type*} [DecidableEq K]
    (g₀ : Finset K)
    (y : {v : K // v ∈ g₀} → G)
    (z : bd g₀ → G)
    {v : K} (hv : v ∈ g₀) :
    (bF g₀).symm (y, z) v = y ⟨v, hv⟩ := by
  have h :=
    congrFun (fA g₀ y z) ⟨v, hv⟩
  exact h
omit [Fintype G] [DecidableEq G] in
theorem jY
    {K : Type*} [DecidableEq K]
    (g₀ : Finset K)
    (y : {v : K // v ∈ g₀} → G)
    (z : bd g₀ → G)
    {v : K} (hv : v ∉ g₀) :
    (bF g₀).symm (y, z) v = z ⟨v, hv⟩ := by
  unfold bF
  convert
    Equiv.piCongrLeft_sumInr
      (fun _ : K => G) (f6 g₀)
      y z ⟨v, hv⟩ using 1 ;
    simp [f6]
omit [Fintype G] [DecidableEq G] in
theorem oH
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : ah (Fin k) K
      (aC k r))
    {g₀ g : Finset K} (hg₀ : g₀ ∈ B.edges)
    (d3 : ∀ f ∈ B.edges, f.card ≤ g₀.card)
    (bt : g₀.Nonempty)
    (hg : g ∈ B.edges.erase g₀)
    (a : G)
    (x :
      Fin ((B.aw hg₀ bt).ay.1 + 1) →
        G)
    (z : bd g₀ → G) :
    bo g
        (B.dX hg₀ bt
          (B.dh hg₀ d3 bt g)
          a
          (Fin.removeNth
            (B.dh hg₀ d3 bt g) x)
          z) =
      bo g
        ((bF g₀).symm
          ((B.d9 hg₀ bt).symm x, z)) := by
  classical
  funext w
  unfold bo
  let i :=
    B.dh hg₀ d3 bt g
  by_cases uA : w.1 ∈ g₀
  · unfold dX
    rw [lB g₀ _ _ uA]
    rw [lB g₀ _ _ uA]
    unfold k4
    rw [B.jE]
    rw [B.jE]
    let q :=
      (B.h7 hg₀ bt).symm
        (⟨w.1, uA⟩ : {v : K // v ∈ g₀})
    have EB : q ≠ i := by
      intro h
      have uI :
          (⟨w.1, uA⟩ : {v : K // v ∈ g₀}) =
            B.gu d3 bt g := by
        apply (B.h7 hg₀ bt).symm.injective
        simpa only [q, i, dh] using h
      apply B.qQ d3 bt hg
      have Fj :
          w.1 =
            (B.gu d3 bt g).1 :=
        congrArg Subtype.val uI
      rw [← Fj]
      exact w.2
    change
      Fin.insertNth i a (Fin.removeNth i x) q = x q
    rw [Fin.insertNth_removeNth]
    simp [EB]
  · unfold dX
    rw [jY g₀ _ _ uA]
    rw [jY g₀ _ _ uA]
noncomputable def eR
    {K : Type*} [Fintype K] [DecidableEq K]
    {C : aa G k r}
    (A : ai G k r C)
    (B : ah (Fin k) K
      (aC k r))
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    (d3 : ∀ g ∈ B.edges, g.card ≤ g₀.card)
    (bt : g₀.Nonempty)
    (a : G)
    (z : bd g₀ → G) :
    cU G
      ((B.aw hg₀ bt).ay.1 + 1) :=
  fun i y =>
    ∏ g ∈ B.edges.erase g₀,
      if _hcoord :
          B.dh hg₀ d3 bt g = i
      then
        B.ao
          (ar A) g
          (bo g
            (B.dX hg₀ bt i a y z))
      else 1
theorem pT
    {K : Type*} [Fintype K] [DecidableEq K]
    (P : ak G k r)
    (A : ai G k r P.an)
    (B : ah (Fin k) K
      (aC k r))
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    (d3 : ∀ g ∈ B.edges, g.card ≤ g₀.card)
    (bt : g₀.Nonempty)
    (a : G)
    (z : bd g₀ → G) :
    eC
      (B.eR A hg₀ d3 bt a z) := by
  constructor
  · intro i y
    unfold eR
    apply Finset.prod_nonneg
    intro g hg
    split_ifs
    · exact
        (B.dR
          (ar A)
          (dF A)
          (Finset.mem_of_mem_erase hg) _).1
    · positivity
  · intro i y
    unfold eR
    apply Finset.prod_le_one
    · intro g hg
      split_ifs
      · exact
          (B.dR
            (ar A)
            (dF A)
            (Finset.mem_of_mem_erase hg) _).1
      · positivity
    · intro g hg
      split_ifs
      · exact
          (B.dR
            (ar A)
            (dF A)
            (Finset.mem_of_mem_erase hg) _).2
      · exact le_rfl
theorem nv
    {K : Type*} [Fintype K] [DecidableEq K]
    (P : ak G k r)
    (A : ai G k r P.an)
    (B : ah (Fin k) K
      (aC k r))
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    (d3 : ∀ g ∈ B.edges, g.card ≤ g₀.card)
    (bt : g₀.Nonempty)
    (a : G)
    (z : bd g₀ → G)
    (x :
      Fin ((B.aw hg₀ bt).ay.1 + 1) →
        G) :
    cN
        (B.eR A hg₀ d3 bt a z) x =
      B.d5 g₀
        (B.ao
          (ar A))
        ((B.d9 hg₀ bt).symm x) z := by
  classical
  unfold cN eR
  rw [Finset.prod_comm]
  unfold d5 d4 cy
  apply Finset.prod_congr rfl
  intro g hg
  let i :=
    B.dh hg₀ d3 bt g
  calc
    (∏ q :
        Fin ((B.aw hg₀ bt).ay.1 + 1),
        if EC :
            B.dh hg₀ d3 bt g = q
        then
          B.ao
            (ar A) g
            (bo g
              (B.dX hg₀ bt q a
                (Fin.removeNth q x) z))
        else 1) =
        (if EC :
            B.dh hg₀ d3 bt g = i
        then
          B.ao
            (ar A) g
            (bo g
            (B.dX hg₀ bt i a
                (Fin.removeNth i x) z))
        else 1) := by
      apply Fintype.prod_eq_single i
      intro q EB
      have C9 :
          B.dh hg₀ d3 bt g ≠ q := by
        intro h
        exact EB h.symm
      simp [C9]
    _ =
        B.ao
          (ar A) g
          (bo g
            (B.dX hg₀ bt i a
              (Fin.removeNth i x) z)) := by
      simp [i]
    _ =
        B.ao
          (ar A) g
          (bo g
            ((bF g₀).symm
              ((B.d9 hg₀ bt).symm x, z))) := by
      rw [B.oH
        hg₀ d3 bt hg a x z]
theorem kt
    [Nonempty G]
    (P : ak G k r)
    (A : ai G k r P.an) :
    ga P A := by
  intro K _instK _decK B _hclosed g₀ hg₀ d3 bt z
  let a : G := Classical.choice inferInstance
  let u :=
    B.eR A hg₀ d3 bt a z
  refine ⟨u, ?_, ?_⟩
  · exact
      B.pT
        P A hg₀ d3 bt a z
  · unfold eW
    unfold aE.et
    apply tT
      (B.d9 hg₀ bt)
    intro y
    rw [B.nv
      P A hg₀ d3 bt a z]
    simp only [Equiv.symm_apply_apply]
    rw [B.q7]
    rfl
end ah
end av.ag
end
section
namespace av.ag
open scoped BigOperators
abbrev cd (n : ℕ) :=
  aj (n + 1) n
@[simp]
theorem iA {n : ℕ}
    (d : cd n) :
    d.rank < n + 1 := by
  simp only [aj.rank]
  exact Nat.succ_lt_succ d.ay.2
abbrev eZ
    {k r : ℕ}
    (e : aj k r)
    (d : cd e.ay.1) :
    Fin (r + 1) :=
  ⟨d.ay.1 + 1, by
    have hd : d.rank < e.rank := by
      exact iA d
    have he : e.rank ≤ r := by
      simp only [aj.rank]
      exact e.ay.2
    omega⟩
abbrev de
    {k r : ℕ}
    (e : aj k r)
    (d : cd e.ay.1) :
    al k (d.ay.1 + 1) :=
  d.face.trans e.face
@[simp]
theorem m7
    {G : Type*} {k r : ℕ}
    (e : aj k r)
    (d : cd e.ay.1)
    (x : Fin k → G) :
    aI (de e d) x =
      aI d.face (aI e.face x) :=
  rfl
noncomputable def jZ
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : aa G k r)
    (e : aj k r)
    (d : cd e.ay.1) :
    ab (Fin (e.ay.1 + 1) → G) :=
  ab.pullback
    (aI d.face)
    (C.partition
      (eZ e d)
      (de e d))
noncomputable def k5
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : aa G k r)
    (e : aj k r) :
    ab (Fin (e.ay.1 + 1) → G) :=
  ab.kQ
    (Finset.univ :
      Finset (cd e.ay.1))
    (jZ C e)
noncomputable def aY
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : aa G k r)
    (e : aj k r) :
    ab (Fin (e.ay.1 + 1) → G) :=
  ab.join
    (au
      (aV C e) e.face)
    (k5 C e)
theorem mb
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : aa G k r)
    (e : aj k r) :
    aY C e ≤
      au
        (aV C e) e.face := by
  exact ab.t8 _ _
theorem gY
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : aa G k r)
    (e : aj k r)
    (x y : Fin (e.ay.1 + 1) → G) :
    y ∈ (aY C e).part x ↔
      y ∈
          (au
            (aV C e) e.face).part x ∧
        ∀ d : cd e.ay.1,
          aI d.face y ∈
            (C.partition
              (eZ e d)
              (de e d)).part
              (aI d.face x) := by
  rw [aY, ab.y3,
    Finset.mem_inter, k5,
    ab.qi]
  simp only [Finset.mem_univ, forall_const,
    jZ,
    ab.gb]
noncomputable def fl
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : aa G k r)
    (e : aj k r)
    (x : Fin (e.ay.1 + 1) → G) :
    (aY C e).parts :=
  bx (aY C e) x
noncomputable def gv
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : aa G k r)
    (e : aj k r)
    (x y : Fin (e.ay.1 + 1) → G) : ℝ :=
  aB
    (aY C e)
    (fl C e x)
    y
@[simp]
theorem qR
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : aa G k r)
    (e : aj k r)
    (x y : Fin (e.ay.1 + 1) → G) :
    gv C e x y ^ 2 =
      gv C e x y :=
  kS _ _ _
noncomputable def gU
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : ak G k r)
    (A : ai G k r P.an)
    (e : aj k r) : ℝ :=
  bq P A e
noncomputable def e3
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : ak G k r)
    (A : ai G k r P.an)
    (e : aj k r)
    (y : Fin (e.ay.1 + 1) → G) : ℝ :=
  gM P A e y
noncomputable def bD
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : ak G k r)
    (A : ai G k r P.an)
    (e : aj k r)
    (y : Fin (e.ay.1 + 1) → G) : ℝ :=
  gv P.an e
    (aI e.face A.witness) y
@[simp]
theorem q8
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : ak G k r)
    (A : ai G k r P.an)
    (e : aj k r)
    (y : Fin (e.ay.1 + 1) → G) :
    bD P A e y ^ 2 =
      bD P A e y :=
  qR _ _ _ _
def iE
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : ak G k r)
    (A : ai G k r P.an)
    (e : aj k r)
    (α β : ℝ) : Prop :=
  α ≤ gU P A e ∧
    aq
        (aY P.an e)
        (fun y => e3 P A e y ^ 2)
        (aI e.face A.witness) ≤
      β
def ai.c5
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : ak G k r)
    (A : ai G k r P.an)
    (α β : ℕ → ℝ) : Prop :=
  ∀ e : aj k r,
    iE P A e
      (α e.rank) (β e.rank)
noncomputable def f2
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : ak G k r)
    (A : ai G k r P.an)
    (e : aj k r) : ℝ :=
  mean fun y =>
    e3 P A e y ^ 2 *
      bD P A e y
theorem iE.oE
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : ak G k r)
    (A : ai G k r P.an)
    (e : aj k r)
    (α β : ℝ)
    (h5 : iE P A e α β) :
    f2 P A e ≤
      β * mean (bD P A e) := by
  unfold f2
  apply kI
    (aY P.an e)
    (fun y => e3 P A e y ^ 2)
    (fl P.an e
      (aI e.face A.witness))
  have vv :
      (aY P.an e).representative
          (fl P.an e
            (aI e.face A.witness)) ∈
        (aY P.an e).part
          (aI e.face A.witness) := by
    exact
      (aY P.an e).jP
        (fl P.an e
          (aI e.face A.witness))
  have heq :=
    cY
      (aY P.an e)
      (fun y => e3 P A e y ^ 2)
      vv
  rw [heq]
  exact h5.2
theorem ai.c5.oE
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : ak G k r)
    (A : ai G k r P.an)
    (α β : ℕ → ℝ)
    (h5 : A.c5 P α β)
    (e : aj k r) :
    f2 P A e ≤
      β e.rank *
        mean (bD P A e) :=
  (h5 e).oE P A e
    (α e.rank) (β e.rank)
end av.ag
end
section
namespace av.ag
open scoped BigOperators
namespace ah
variable {G : Type*} [Fintype G] [DecidableEq G]
  {k r : ℕ}
noncomputable def ee
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : ah (Fin k) K
      (aC k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (bt : g.Nonempty) :
    Fin ((B.aw hg bt).ay.1 + 1) ≃
      {j : Fin k // j ∈ g.image B.projection} := by
  let t := g.image B.projection
  let e := B.aw hg bt
  have fE : t.card = e.ay.1 + 1 := by
    have tV :
        aK e = t := by
      dsimp [e, aw, t]
      exact cE
        (g.image B.projection)
        (B.fo hg bt)
        (B.ew hg)
    calc
      t.card = (aK e).card :=
        congrArg Finset.card tV.symm
      _ = e.rank := b1 e
      _ = e.ay.1 + 1 := rfl
  exact (t.orderIsoOfFin fE).toEquiv
@[simp]
theorem l2
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : ah (Fin k) K
      (aC k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (bt : g.Nonempty)
    (i : Fin ((B.aw
      hg bt).ay.1 + 1)) :
    ((B.ee hg bt) i).1 =
      (B.aw hg bt).face i := by
  rfl
noncomputable def cF
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : ah (Fin k) K
      (aC k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (bt : g.Nonempty) :
    ({v : K // v ∈ g} → G) ≃
      (Fin ((B.aw hg bt).ay.1 + 1) → G) :=
  (Equiv.arrowCongr
      (B.cp hg)
      (Equiv.refl G)).trans
    (Equiv.arrowCongr
      (B.ee hg bt).symm
      (Equiv.refl G))
omit [Fintype G] [DecidableEq G] in
@[simp]
theorem gZ
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : ah (Fin k) K
      (aC k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (bt : g.Nonempty)
    (y : {v : K // v ∈ g} → G) :
    B.cF hg bt y =
      B.bC hg bt y := by
  funext i
  unfold cF
    bC
    eb ee
  rfl
def fF
    (e : aj k r)
    (d : cd e.ay.1) :
    aj k r where
  ay :=
    ⟨d.ay.1,
      lt_trans d.ay.2 e.ay.2⟩
  face := de e d
theorem lS
    (e : aj k r)
    (d : cd e.ay.1) :
    aK
        (fF e d) ⊂
      aK e := by
  constructor
  · intro v hv
    rw [eu] at hv ⊢
    obtain ⟨i, rfl⟩ := hv
    exact ⟨d.face i, rfl⟩
  · intro h
    have fE :=
      Finset.card_le_card h
    rw [b1,
      b1] at fE
    exact
      (Nat.not_le_of_gt
        (iA d)) fE
theorem kK
    (e f : aj k r)
    (Ad :
      aK f ⊂
        aK e) :
    ∃ d : cd e.ay.1,
      fF e d = f := by
  have qb : f.rank < e.rank := by
    rw [← b1,
      ← b1]
    exact Finset.card_lt_card Ad
  have z4 :
      Set.range f.face ⊆ Set.range e.face := by
    intro v hv
    rw [← eu] at hv ⊢
    exact Ad.1 hv
  choose q hq using fun i : Fin (f.ay.1 + 1) =>
    z4 ⟨i, rfl⟩
  have ED : StrictMono q := by
    intro i j hij
    apply e.face.lt_iff_lt.mp
    rw [hq i, hq j]
    exact f.face.strictMono hij
  let Fk : al
      (e.ay.1 + 1) (f.ay.1 + 1) :=
    OrderEmbedding.ofStrictMono q ED
  have xu : f.ay.1 < e.ay.1 := by
    simpa [aj.rank] using qb
  let d : cd e.ay.1 :=
    ⟨⟨f.ay.1, xu⟩, Fk⟩
  refine ⟨d, ?_⟩
  apply eQ
  apply Finset.Subset.antisymm
  · intro v hv
    rw [eu] at hv ⊢
    obtain ⟨i, rfl⟩ := hv
    exact ⟨i, (hq i).symm⟩
  · intro v hv
    rw [eu] at hv ⊢
    obtain ⟨i, rfl⟩ := hv
    exact ⟨i, hq i⟩
noncomputable def di
    (e : aj k r) :
    Finset (aj k r) :=
  Finset.univ.filter fun f =>
    aK f ⊂ aK e
@[simp]
theorem dY
    (e f : aj k r) :
    f ∈ di e ↔
      aK f ⊂ aK e := by
  simp [di]
theorem oI
    (e : aj k r)
    (lx : 0 < e.ay.1)
    (i : Fin (e.ay.1 + 1)) :
    aK (e.boundary lx i) ⊂
      aK e := by
  rcases e with ⟨⟨j, G1⟩, Bt⟩
  cases j with
  | zero =>
      simp at lx
  | succ n =>
      constructor
      · intro v hv
        rw [eu] at hv ⊢
        obtain ⟨q, rfl⟩ := hv
        exact ⟨i.succAbove q, rfl⟩
      · intro h
        have hc := Finset.card_le_card h
        rw [b1,
          b1] at hc
        exact
          (Nat.not_le_of_gt
            ((⟨⟨n + 1, G1⟩, Bt⟩ :
                aj k r).xB
              lx i)) hc
noncomputable def eS
    (P : ak G k r)
    (A : ai G k r P.an)
    (e : aj k r)
    (y : Fin (e.ay.1 + 1) → G) :
    Fin k → G :=
  (dM e.face).symm
    (y, h3 e.face A.witness)
@[simp]
theorem g8
    (P : ak G k r)
    (A : ai G k r P.an)
    (e : aj k r)
    (y : Fin (e.ay.1 + 1) → G) :
    aI e.face
        (eS P A e y) = y := by
  exact nt _ _ _
@[simp]
theorem o0
    {K : Type*} [Fintype K] [DecidableEq K]
    (P : ak G k r)
    (A : ai G k r P.an)
    (B : ah (Fin k) K
      (aC k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (bt : g.Nonempty)
    (y : {v : K // v ∈ g} → G)
    (v : {v : K // v ∈ g}) :
    eS P A
        (B.aw hg bt)
        (B.bC hg bt y)
        (B.projection v.1) =
      y v := by
  let j := B.cp hg v
  let i :=
    (B.ee hg bt).symm j
  have hi :
      B.ee hg bt i = j :=
    (B.ee hg bt).apply_symm_apply j
  have zG :
      (B.aw hg bt).face i =
        B.projection v.1 := by
    calc
      (B.aw hg bt).face i =
          ((B.ee hg bt) i).1 := by
        rw [B.l2]
      _ = j.1 := congrArg Subtype.val hi
      _ = B.projection v.1 := by
        exact B.kO hg v
  rw [← zG]
  change
    aI
        (B.aw hg bt).face
        (eS P A
          (B.aw hg bt)
          (B.bC hg bt y)) i =
      y v
  rw [g8]
  change
    B.ds hg y
        ((B.ee hg bt) i) =
      y v
  rw [hi]
  exact congrArg y
    ((B.cp hg).symm_apply_apply v)
theorem kV
    (P : ak G k r)
    (A : ai G k r P.an)
    (e : aj k r)
    (y : Fin (e.ay.1 + 1) → G) :
    bD P A e y =
      bV A
        (di e)
        (eS P A e y) := by
  classical
  let x := eS P A e y
  have EE : aI e.face x = y :=
    g8 P A e y
  by_cases hy :
      y ∈ (aY P.an e).part
        (aI e.face A.witness)
  · rw [show bD P A e y = 1 by
          exact dg _ _ hy]
    unfold bV
    symm
    apply Finset.prod_eq_one
    intro f hf
    have Ad :
      aK f ⊂
          aK e :=
      (dY e f).1
        hf
    obtain ⟨d, rfl⟩ :=
      kK e f Ad
    unfold bX
    apply dg
    have hd :=
      (gY
        P.an e
        (aI e.face A.witness) y).1 hy |>.2 d
    change
      aI
          (de e d) x ∈
        (A.atom
          (eZ e d)
          (de e d)).1
    rw [A.jo]
    change
      aI d.face
          (aI e.face x) ∈
        (P.an.partition
          (eZ e d)
          (de e d)).part
          (aI d.face
            (aI e.face A.witness))
    rw [EE]
    exact hd
  · rw [show bD P A e y = 0 by
          exact c0 _ _ hy]
    by_contra yi
    have EG :
        bV A
            (di e) x ≠ 0 :=
      fun hz => yi hz.symm
    have yW :
        ∀ f ∈ di e,
          bX A f
              (aI f.face x) ≠ 0 := by
      intro f hf
      exact Finset.prod_ne_zero_iff.mp
        (by simpa [bV] using EG) f hf
    exfalso
    apply hy
    apply
      (gY
        P.an e
        (aI e.face A.witness) y).2
    constructor
    · rw [jC]
      intro i
      by_cases DB : e.ay.1 = 0
      · have uI :
            b3 i y =
              b3 i
                (aI e.face A.witness) :=
          by
            funext q
            have hq : q.1 < 0 := by
              simpa [DB] using q.2
            omega
        rw [uI]
        exact
          (aV P.an e
            (dH e.face i)).mem_part
            (Finset.mem_univ _)
      · have Bw : 0 < e.ay.1 :=
          Nat.pos_of_ne_zero DB
        let f := e.boundary Bw i
        have Da :
            aK f ⊂
              aK e := by
          exact oI
            e Bw i
        have Bx :
            f ∈ di e :=
          (dY e f).2 Da
        have vx := yW f Bx
        rw [← EE]
        exact
          jk
            P A e Bw i x vx
    · intro d
      let f := fF e d
      have Bx :
          f ∈ di e :=
        (dY e f).2
          (lS e d)
      have vx := yW f Bx
      unfold bX at vx
      have yj :
          aI f.face x ∈
            (A.atom f.ay.succ f.face).1 := by
        by_contra hnot
        exact vx
          (c0 _ _ hnot)
      rw [A.jo] at yj
      change
        aI
            (de e d) x ∈
          (P.an.partition
            (eZ e d)
            (de e d)).part
            (aI
              (de e d) A.witness)
        at yj
      simp only [m7]
        at yj
      simpa only [EE] using yj
def kW
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : ah (Fin k) K
      (aC k r))
    (g₀ : Finset K) (t : Finset (Fin k)) :
    Finset K :=
  g₀.filter fun v => B.projection v ∈ t
theorem tj
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : ah (Fin k) K
      (aC k r))
    (g₀ : Finset K) (t : Finset (Fin k)) :
    B.kW g₀ t ⊆ g₀ := by
  exact Finset.filter_subset _ _
theorem tH
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : ah (Fin k) K
      (aC k r))
    (g₀ : Finset K) {t : Finset (Fin k)}
    (ht : t ⊆ g₀.image B.projection) :
    (B.kW g₀ t).image B.projection = t := by
  ext j
  constructor
  · intro hj
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hj
    exact (Finset.mem_filter.mp hv).2
  · intro hj
    obtain ⟨v, xZ, y0⟩ :=
      Finset.mem_image.mp (ht hj)
    apply Finset.mem_image.mpr
    refine ⟨v, Finset.mem_filter.mpr ⟨xZ, ?_⟩, y0⟩
    exact y0 ▸ hj
theorem nj
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : ah (Fin k) K
      (aC k r))
    {g₀ g : Finset K} (hg₀ : g₀ ∈ B.edges)
    (zN : g ⊆ g₀) :
    B.kW g₀
        (g.image B.projection) = g := by
  ext v
  constructor
  · intro hv
    have yk := (Finset.mem_filter.mp hv).1
    obtain ⟨w, A0, vM⟩ :=
      Finset.mem_image.mp (Finset.mem_filter.mp hv).2
    have Ae : w ∈ g₀ := zN A0
    have Bf : w = v :=
      B.cW g₀ hg₀ Ae yk vM
    exact Bf ▸ A0
  · intro hv
    exact Finset.mem_filter.mpr
      ⟨zN hv,
        Finset.mem_image.mpr ⟨v, hv, rfl⟩⟩
theorem fe
    {K : Type*} [Fintype K] [DecidableEq K]
    (P : ak G k r)
    (A : ai G k r P.an)
    (B : ah (Fin k) K
      (aC k r))
    (dv : B.a6)
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    (bt : g₀.Nonempty)
    (y : {v : K // v ∈ g₀} → G) :
    B.cT g₀
        (B.ao
          (ar A)) y =
      bD P A
        (B.aw hg₀ bt)
        (B.bC hg₀ bt y) := by
  classical
  let e := B.aw hg₀ bt
  let u := B.bC hg₀ bt y
  let x := eS P A e u
  have Co :
      aK e =
        g₀.image B.projection := by
    dsimp [e, aw]
    exact cE
      (g₀.image B.projection)
      (B.fo hg₀ bt)
      (B.ew hg₀)
  let z : bd g₀ → G :=
    fun v => A.witness (B.projection v.1)
  let xK : K → G :=
    (bF g₀).symm (y, z)
  have FI : bo g₀ xK = y := by
    exact fA g₀ y z
  have zr :
      B.cT g₀
          (B.ao
            (ar A)) y =
        (B.a8 g₀).cy
          (B.ao
            (ar A)) xK := by
    calc
      B.cT g₀
          (B.ao
            (ar A)) y =
        B.cT g₀
          (B.ao
            (ar A))
          (bo g₀ xK) := by
            rw [FI]
      _ =
        (B.a8 g₀).cy
          (B.ao
            (ar A)) xK :=
        B.gH g₀
          (B.ao
            (ar A)) xK
  have yc : ∅ ∈ (B.a8 g₀).edges := by
    apply (B.c7 g₀ ∅).2
    refine ⟨dv hg₀ (Finset.empty_subset g₀), ?_⟩
    exact Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.empty_subset _, bt.ne_empty.symm⟩
  have Af :
      B.ao
          (ar A) ∅
          (bo ∅ xK) = 1 := by
    rw [B.b4
      (ar A)
      ((B.c7 g₀ ∅).1 yc).1]
    exact fk A _
  rw [zr]
  rw [kV P A e u]
  unfold cy bV
  rw [← Finset.prod_erase_mul _ _ yc,
    Af, mul_one]
  apply Finset.prod_bij
    (fun g _hg =>
      bB
        (g.image B.projection)
        (Finset.image_nonempty.mpr
          (Finset.nonempty_iff_ne_empty.mpr
            (Finset.mem_erase.mp _hg).1))
        (B.ew
          (((B.c7 g₀ g).1
            (Finset.mem_of_mem_erase _hg)).1)))
  · intro g hg
    simp only [Finset.mem_erase] at hg
    rw [dY]
    rw [cE]
    rw [Co]
    have ot :=
      ((B.c7 g₀ g).1 hg.2).2
    constructor
    · intro j hj
      obtain ⟨v, xZ, rfl⟩ := Finset.mem_image.mp hj
      exact Finset.mem_image.mpr
        ⟨v, ot.1 xZ, rfl⟩
    · intro vq
      apply ot.2
      intro v yk
      obtain ⟨w, A0, vM⟩ :=
        Finset.mem_image.mp
          (vq
            (Finset.mem_image.mpr
              ⟨v, yk, rfl⟩))
      have Ae : w ∈ g₀ := ot.1 A0
      have Bf : w = v :=
        B.cW
          g₀ hg₀ Ae yk vM
      exact Bf ▸ A0
  · intro g₁ Fl g₂ Fm heq
    have fH :
        g₁.image B.projection =
          g₂.image B.projection := by
      simpa only [cE] using
        congrArg aK heq
    have Db :=
      ((B.c7 g₀ g₁).1
        (Finset.mem_of_mem_erase Fl)).2.1
    have Dc :=
      ((B.c7 g₀ g₂).1
        (Finset.mem_of_mem_erase Fm)).2.1
    rw [← B.nj hg₀ Db,
      ← B.nj hg₀ Dc,
      fH]
  · intro f hf
    have Ad :=
      (dY e f).1 hf
    let t := aK f
    let g := B.kW g₀ t
    have ht : t ⊆ g₀.image B.projection := by
      simpa [e, aw,
        cE] using Ad.1
    have rD : g ⊆ g₀ :=
      B.tj g₀ t
    have hgmem : g ∈ B.edges :=
      dv hg₀ rD
    have fH : g.image B.projection = t :=
      B.tH g₀ ht
    have uR : g ≠ ∅ := by
      intro hzero
      have : t = ∅ := by simpa [hzero] using fH.symm
      have Dd := cI f
      change t.Nonempty at Dd
      rw [this] at Dd
      exact Finset.not_nonempty_empty Dd
    have De : g ⊂ g₀ := by
      refine ⟨rD, ?_⟩
      intro G3
      have CM : g = g₀ :=
        Finset.Subset.antisymm rD G3
      have : t = g₀.image B.projection := by
        rw [← fH, CM]
      apply Ad.2
      rw [Co, ← this]
    refine ⟨g, Finset.mem_erase.mpr
      ⟨uR,
        (B.c7 g₀ g).2
          ⟨hgmem, De⟩⟩, ?_⟩
    apply eQ
    simpa only [cE] using fH
  · intro g hg
    simp only [Finset.mem_erase] at hg
    have iq :=
      ((B.c7 g₀ g).1 hg.2).1
    rw [B.b4
      (ar A) iq]
    unfold ar
    simp only [dif_pos (Finset.image_nonempty.mpr
      (Finset.nonempty_iff_ne_empty.mpr hg.1))]
    simp only [dif_pos (B.ew iq)]
    congr 1
    have uR : g.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hg.1
    change
      B.bC
          iq uR (bo g xK) =
        aI
          (B.aw iq uR).face x
    funext i
    let v : {v : K // v ∈ g} :=
      (B.cp iq).symm
        (B.ee iq uR i)
    have rD :
        g ⊆ g₀ :=
      ((B.c7 g₀ g).1 hg.2).2.1
    let xo : {v : K // v ∈ g₀} :=
      ⟨v.1, rD v.2⟩
    have iK :
        (B.aw iq uR).face i =
          B.projection xo.1 := by
      calc
        (B.aw iq uR).face i =
            (B.ee iq uR i).1 := by
          rw [B.l2]
        _ = ((B.cp iq) v).1 := by
          rw [Equiv.apply_symm_apply]
        _ = B.projection v.1 :=
          B.kO iq v
        _ = B.projection xo.1 := rfl
    calc
      B.bC
          iq uR (bo g xK) i =
          xK v.1 := by
        rfl
      _ = y xo := by
        have hv := congrFun FI xo
        exact hv
      _ = x (B.projection xo.1) := by
        symm
        exact
          B.o0
            P A hg₀ bt y xo
      _ =
          aI
            (B.aw iq uR).face
            x i := by
        rw [aI, iK]
theorem h8
    {K : Type*} [Fintype K] [DecidableEq K]
    (P : ak G k r)
    (A : ai G k r P.an)
    (B : ah (Fin k) K
      (aC k r))
    (dv : B.a6)
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    (bt : g₀.Nonempty) :
    (B.a8 g₀).a7
        ((B.a8 g₀).ao
          (ar A)) =
      mean (bD P A
        (B.aw hg₀ bt)) := by
  classical
  rw [← B.gs
    (B.a8 g₀)
    (Finset.filter_subset _ _)
    rfl
    (ar A)]
  cases isEmpty_or_nonempty G with
  | inl hG =>
      let : IsEmpty G := hG
      have : Nonempty K := ⟨bt.choose⟩
      have :
          Nonempty
            (Fin ((B.aw hg₀ bt).ay.1 + 1)) :=
        ⟨⟨0, Nat.succ_pos _⟩⟩
      simp only [a7, Be]
  | inr hG =>
      let : Nonempty G := hG
      unfold a7
      rw [sD g₀]
      unfold fq
      have EH :
          ∀ y : {v : K // v ∈ g₀} → G,
            mean (fun z : bd g₀ → G =>
                (B.a8 g₀).cy
                  (B.ao
                    (ar A))
                  ((bF g₀).symm (y, z))) =
              bD P A
                (B.aw hg₀ bt)
                (B.cF
                  hg₀ bt y) := by
        intro y
        calc
          mean (fun z : bd g₀ → G =>
              (B.a8 g₀).cy
                (B.ao
                  (ar A))
                ((bF g₀).symm (y, z))) =
              mean (fun _z : bd g₀ → G =>
                B.cT g₀
                  (B.ao
                    (ar A)) y) := by
            apply congrArg mean
            funext z
            rw [← B.gH g₀
              (B.ao
                (ar A))
              ((bF g₀).symm (y, z))]
            rw [fA]
          _ =
              B.cT g₀
                (B.ao
                  (ar A)) y := by
            exact ml _
          _ =
              bD P A
                (B.aw hg₀ bt)
                (B.bC hg₀ bt y) :=
            B.fe
              P A dv hg₀ bt y
          _ =
              bD P A
                (B.aw hg₀ bt)
                (B.cF hg₀ bt y) := by
            rw [gZ]
      rw [show
        (fun y : {v : K // v ∈ g₀} → G =>
          mean (fun z : bd g₀ → G =>
            (B.a8 g₀).cy
              (B.ao
                (ar A))
              ((bF g₀).symm (y, z)))) =
          fun y =>
            bD P A
              (B.aw hg₀ bt)
              (B.cF
                hg₀ bt y) by
        funext y
        exact EH y]
      exact tT
        (B.cF hg₀ bt)
        (fun y =>
          bD P A
            (B.aw hg₀ bt)
            (B.cF hg₀ bt y))
        (bD P A
          (B.aw hg₀ bt))
        (fun _ => rfl)
theorem g9
    (P : ak G k r)
    (A : ai G k r P.an)
    (α β : ℕ → ℝ)
    (h5 : A.c5 P α β) :
    hV P A β := by
  intro K _ _ B dv g₀ hg₀ d3 bt
  let e := B.aw hg₀ bt
  have qb : e.rank = g₀.card := by
    unfold e aw
    rw [← b1]
    rw [cE]
    exact B.kc hg₀
  have yl := h5.oE P A α β e
  rw [← qb]
  rw [B.h8
    P A dv hg₀ bt]
  calc
    mean (fun y =>
        B.eG
            P A hg₀ bt y ^ 2) =
        f2 P A e := by
      apply tT
        (B.cF hg₀ bt)
      intro y
      unfold eG
        f1
        e3
      rw [B.fe
        P A dv hg₀ bt y]
      rw [mul_pow, q8]
      rw [gZ]
    _ ≤
        β e.rank *
          mean (bD P A e) :=
      yl
end ah
end av.ag
end
section
namespace av.ag
open scoped BigOperators
end av.ag
end
section
namespace av.ag
open scoped BigOperators
end av.ag
end
section
namespace av.ag
open scoped BigOperators
structure fm
    (G : Type*) [Fintype G] [DecidableEq G]
    (k j : ℕ)
    (lower : af G k j)
    (upper : af G k (j + 1))
    (ε : ℝ) (aG : ℕ) where
  steps : ℕ
  aQ : af G k j
  sL : steps < aG
  dy : aP aQ lower
  regular : a3 aQ upper ε
  aO :
    ∀ e,
      ab.aO (aQ e) ≤
        (2 ^ (j + 1)) ^ steps *
          ab.aO (lower e)
theorem fm.nonempty
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (lower : af G k j)
    (upper : af G k (j + 1))
    {ε : ℝ} {aG : ℕ}
    (hε : 0 ≤ ε)
    (dP :
      (Fintype.card (al k (j + 1)) : ℝ) <
        (aG : ℝ) * ε ^ 2) :
    Nonempty
      (fm
        G k j lower upper ε aG) := by
  obtain ⟨steps, aQ, EI, Df,
      dk, b8⟩ :=
    eP
      lower upper hε dP
  exact ⟨{
    steps := steps
    aQ := aQ
    sL := EI
    dy := Df
    regular := dk
    aO := b8 }⟩
noncomputable def dN
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (lower : af G k j)
    (upper : af G k (j + 1))
    (ε : ℝ) (aG : ℕ)
    (hε : 0 ≤ ε)
    (dP :
      (Fintype.card (al k (j + 1)) : ℝ) <
        (aG : ℝ) * ε ^ 2) :
    fm
      G k j lower upper ε aG :=
  Classical.choice
    (fm.nonempty
      lower upper hε dP)
noncomputable def bS
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (initial : af G k j)
    (upper : af G k (j + 1))
    (ε : ℕ → ℝ) (aG : ℕ → ℕ)
    (hε : ∀ n, 0 ≤ ε n)
    (dP :
      ∀ n,
        (Fintype.card
          (al k (j + 1)) : ℝ) <
          (aG n : ℝ) * (ε n) ^ 2) :
    ℕ → af G k j
  | 0 => initial
  | n + 1 =>
      (dN
        (bS
          initial upper ε aG hε dP n)
        upper (ε n) (aG n)
        (hε n) (dP n)).aQ
@[simp]
theorem wW
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (initial : af G k j)
    (upper : af G k (j + 1))
    (ε : ℕ → ℝ) (aG : ℕ → ℕ)
    (hε : ∀ n, 0 ≤ ε n)
    (dP :
      ∀ n,
        (Fintype.card
          (al k (j + 1)) : ℝ) <
          (aG n : ℝ) * (ε n) ^ 2) :
    bS
      initial upper ε aG hε dP 0 = initial :=
  rfl
@[simp]
theorem gV
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (initial : af G k j)
    (upper : af G k (j + 1))
    (ε : ℕ → ℝ) (aG : ℕ → ℕ)
    (hε : ∀ n, 0 ≤ ε n)
    (dP :
      ∀ n,
        (Fintype.card
          (al k (j + 1)) : ℝ) <
          (aG n : ℝ) * (ε n) ^ 2)
    (n : ℕ) :
    bS
        initial upper ε aG hε dP (n + 1) =
      (dN
        (bS
          initial upper ε aG hε dP n)
        upper (ε n) (aG n)
        (hε n) (dP n)).aQ :=
  rfl
theorem gn
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (initial : af G k j)
    (upper : af G k (j + 1))
    (ε : ℕ → ℝ) (aG : ℕ → ℕ)
    (hε : ∀ n, 0 ≤ ε n)
    (dP :
      ∀ n,
        (Fintype.card
          (al k (j + 1)) : ℝ) <
          (aG n : ℝ) * (ε n) ^ 2)
    (n : ℕ) :
    aP
      (bS
        initial upper ε aG hε dP (n + 1))
      (bS
        initial upper ε aG hε dP n) := by
  rw [gV]
  exact
    (dN
      (bS
        initial upper ε aG hε dP n)
      upper (ε n) (aG n)
      (hε n) (dP n)).dy
theorem mc
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (initial : af G k j)
    (upper : af G k (j + 1))
    (ε : ℕ → ℝ) (aG : ℕ → ℕ)
    (hε : ∀ n, 0 ≤ ε n)
    (dP :
      ∀ n,
        (Fintype.card
          (al k (j + 1)) : ℝ) <
          (aG n : ℝ) * (ε n) ^ 2) :
    ∀ n,
      aP
        (bS
          initial upper ε aG hε dP n)
        initial := by
  intro n
  induction n with
  | zero =>
      exact aP.refl initial
  | succ n ih =>
      exact aP.trans
        (gn
          initial upper ε aG hε dP n)
        ih
theorem ph
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (initial : af G k j)
    (upper : af G k (j + 1))
    (ε : ℕ → ℝ) (aG : ℕ → ℕ)
    (hε : ∀ n, 0 ≤ ε n)
    (dP :
      ∀ n,
        (Fintype.card
          (al k (j + 1)) : ℝ) <
          (aG n : ℝ) * (ε n) ^ 2)
    (n : ℕ) :
    a3
      (bS
        initial upper ε aG hε dP (n + 1))
      upper (ε n) := by
  rw [gV]
  exact
    (dN
      (bS
        initial upper ε aG hε dP n)
      upper (ε n) (aG n)
      (hε n) (dP n)).regular
def aL
    (j : ℕ) (aG : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 =>
      (2 ^ (j + 1)) ^ (aG n) *
        aL j aG n
theorem hX
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (initial : af G k j)
    (upper : af G k (j + 1))
    (ε : ℕ → ℝ) (aG : ℕ → ℕ)
    (hε : ∀ n, 0 ≤ ε n)
    (dP :
      ∀ n,
        (Fintype.card
          (al k (j + 1)) : ℝ) <
          (aG n : ℝ) * (ε n) ^ 2) :
    ∀ (n : ℕ) (e : al k j),
      ab.aO
          (bS
            initial upper ε aG hε dP n e) ≤
        aL j aG n *
          ab.aO (initial e) := by
  intro n
  induction n with
  | zero =>
      intro e
      simp [aL]
  | succ n ih =>
      intro e
      let fp :=
        dN
          (bS
            initial upper ε aG hε dP n)
          upper (ε n) (aG n)
          (hε n) (dP n)
      have ow := fp.aO e
      have wL :
          (2 ^ (j + 1)) ^ fp.steps ≤
            (2 ^ (j + 1)) ^ (aG n) :=
        Nat.pow_le_pow_right (by positivity)
          (Nat.le_of_lt fp.sL)
      rw [gV]
      calc
        ab.aO (fp.aQ e) ≤
            (2 ^ (j + 1)) ^ fp.steps *
              ab.aO
                (bS
                  initial upper ε aG hε dP n e) :=
          ow
        _ ≤
            (2 ^ (j + 1)) ^ (aG n) *
              ab.aO
                (bS
                  initial upper ε aG hε dP n e) :=
          Nat.mul_le_mul_right _ wL
        _ ≤
            (2 ^ (j + 1)) ^ (aG n) *
              (aL
                  j aG n *
                ab.aO (initial e)) :=
          Nat.mul_le_mul_left _ (ih e)
        _ =
            aL
                j aG (n + 1) *
              ab.aO (initial e) := by
          simp [aL,
            Nat.mul_assoc]
structure gw
    (G : Type*) [Fintype G] [DecidableEq G]
    (k j : ℕ)
    (initial : af G k j)
    (upper : af G k (j + 1))
    (ε : ℕ → ℝ) (aG : ℕ → ℕ)
    (length : ℕ) where
  index : ℕ
  fM : index < length
  an : af G k j
  aQ : af G k j
  dy : aP aQ an
  bJ :
    aP an initial
  lC :
    a3 aQ upper (ε index)
  eo :
    0 ≤ aH aQ upper -
      aH an upper
  gN :
    aH aQ upper -
        aH an upper ≤
      (Fintype.card (al k (j + 1)) : ℝ) /
        (length : ℝ)
  bT :
    ∀ e,
      ab.aO (an e) ≤
        aL
            j aG index *
          ab.aO (initial e)
  c1 :
    ∀ e,
      ab.aO (aQ e) ≤
        aL
            j aG (index + 1) *
          ab.aO (initial e)
theorem ru
    (E : ℕ → ℝ) {length : ℕ}
    (iB : 0 < length)
    {B : ℝ}
    (Ht : 0 ≤ E 0)
    (G4 : E length ≤ B) :
    ∃ i : ℕ, i < length ∧
      E (i + 1) - E i ≤ B / length := by
  have F0 :
      ∑ i ∈ Finset.range length,
          (E (i + 1) - E i) =
        E length - E 0 :=
    Finset.sum_range_sub E length
  have hsum :
      ∑ i ∈ Finset.range length,
          (E (i + 1) - E i) ≤
        ∑ _i ∈ Finset.range length,
          B / (length : ℝ) := by
    rw [F0]
    calc
      E length - E 0 ≤ B := by linarith
      _ =
          ∑ _i ∈ Finset.range length,
            B / (length : ℝ) := by
        simp only [Finset.sum_const,
          Finset.card_range, nsmul_eq_mul]
        field_simp
  obtain ⟨i, hi, wK⟩ :=
    Finset.exists_le_of_sum_le
      ⟨0, Finset.mem_range.mpr iB⟩ hsum
  exact ⟨i, Finset.mem_range.mp hi, wK⟩
theorem gw.nonempty
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (initial : af G k j)
    (upper : af G k (j + 1))
    (ε : ℕ → ℝ) (aG : ℕ → ℕ)
    (hε : ∀ n, 0 ≤ ε n)
    (dP :
      ∀ n,
        (Fintype.card
          (al k (j + 1)) : ℝ) <
          (aG n : ℝ) * (ε n) ^ 2)
    {length : ℕ} (iB : 0 < length) :
    Nonempty
      (gw
        G k j initial upper ε aG length) := by
  let ym :=
    bS
      initial upper ε aG hε dP
  obtain ⟨i, hi, ip⟩ :=
    ru
      (fun n => aH
        (ym n) upper)
      iB
      (nh
        (ym 0) upper)
      (mG
        (ym length) upper)
  refine ⟨{
    index := i
    fM := hi
    an := ym i
    aQ := ym (i + 1)
    dy := ?_
    bJ := ?_
    lC := ?_
    eo := ?_
    gN := ip
    bT := ?_
    c1 := ?_ }⟩
  · exact gn
      initial upper ε aG hε dP i
  · exact mc
      initial upper ε aG hε dP i
  · exact ph
      initial upper ε aG hε dP i
  · exact sub_nonneg.mpr
      (te
        (gn
          initial upper ε aG hε dP i)
        upper)
  · exact hX
      initial upper ε aG hε dP i
  · exact hX
      initial upper ε aG hε dP (i + 1)
noncomputable def iF
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (initial : af G k j)
    (upper : af G k (j + 1))
    (ε : ℕ → ℝ) (aG : ℕ → ℕ)
    (hε : ∀ n, 0 ≤ ε n)
    (dP :
      ∀ n,
        (Fintype.card
          (al k (j + 1)) : ℝ) <
          (aG n : ℝ) * (ε n) ^ 2)
    (length : ℕ) (iB : 0 < length) :
    gw
      G k j initial upper ε aG length :=
  Classical.choice
    (gw.nonempty
      initial upper ε aG hε dP iB)
def cR
    {r : ℕ}
    (ε : (j : Fin r) → ℕ → ℝ)
    (index : Fin r → ℕ) :
    cV r :=
  fun j => ε j (index j)
structure bk
    (G : Type*) [Fintype G] [DecidableEq G]
    (k r : ℕ)
    (initial : aa G k r)
    (ε : (j : Fin r) → ℕ → ℝ)
    (aG : (j : Fin r) → ℕ → ℕ)
    (length : Fin r → ℕ) where
  index : Fin r → ℕ
  an : aa G k r
  aQ : aa G k r
  dy : aQ.db an
  bJ : an.db initial
  da :
    an.bl = initial.bl
  dZ :
    aQ.bl = initial.bl
  fM : ∀ j, index j < length j
  regular :
    il aQ
      (cR ε index)
  eo :
    ∀ j : Fin r,
      0 ≤
        aH
            (aQ.partition j.castSucc)
            (aQ.partition j.succ) -
          aH
            (an.partition j.castSucc)
            (aQ.partition j.succ)
  gN :
    ∀ j : Fin r,
      aH
            (aQ.partition j.castSucc)
            (aQ.partition j.succ) -
          aH
            (an.partition j.castSucc)
            (aQ.partition j.succ) ≤
        (Fintype.card
          (al k (j.1 + 1)) : ℝ) /
            (length j : ℝ)
  bT :
    ∀ (j : Fin r) (e : al k j.1),
      ab.aO
          (an.partition j.castSucc e) ≤
        aL
            j.1 (aG j) (index j) *
          ab.aO
            (initial.partition j.castSucc e)
  c1 :
    ∀ (j : Fin r) (e : al k j.1),
      ab.aO
          (aQ.partition j.castSucc e) ≤
        aL
            j.1 (aG j) (index j + 1) *
          ab.aO
            (initial.partition j.castSucc e)
namespace bk
def nO
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : aa G k r}
    {ε : (j : Fin r) → ℕ → ℝ}
    {aG : (j : Fin r) → ℕ → ℕ}
    {length : Fin r → ℕ}
    (R : bk
      G k r initial ε aG length) :
    ak G k r where
  an := R.an
  aQ := R.aQ
  dy := R.dy
end bk
theorem bk.nonempty
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (initial : aa G k r)
    (ε : (j : Fin r) → ℕ → ℝ)
    (aG : (j : Fin r) → ℕ → ℕ)
    (length : Fin r → ℕ)
    (hε : ∀ j n, 0 ≤ ε j n)
    (dP :
      ∀ j n,
        (Fintype.card
          (al k (j.1 + 1)) : ℝ) <
          (aG j n : ℝ) * (ε j n) ^ 2)
    (iB : ∀ j, 0 < length j) :
    Nonempty
      (bk
        G k r initial ε aG length) := by
  induction r with
  | zero =>
      let index : Fin 0 → ℕ := fun j => Fin.elim0 j
      refine ⟨{
        index := index
        an := initial
        aQ := initial
        dy :=
          aa.db.refl initial
        bJ :=
          aa.db.refl initial
        da := rfl
        dZ := rfl
        fM := ?_
        regular := ?_
        eo := ?_
        gN := ?_
        bT := ?_
        c1 := ?_ }⟩
      · intro j
        exact Fin.elim0 j
      · intro j
        exact Fin.elim0 j
      · intro j
        exact Fin.elim0 j
      · intro j
        exact Fin.elim0 j
      · intro j
        exact Fin.elim0 j
      · intro j
        exact Fin.elim0 j
  | succ r ih =>
      let lD :
          af G k r :=
        initial.ed.bl
      let upper :
          af G k (r + 1) :=
        initial.bl
      have wF :
          ∀ n, 0 ≤ ε (Fin.last r) n :=
        fun n => hε (Fin.last r) n
      have xI :
          ∀ n,
            (Fintype.card
              (al k (r + 1)) : ℝ) <
              (aG (Fin.last r) n : ℝ) *
                (ε (Fin.last r) n) ^ 2 := by
        intro n
        have h := dP (Fin.last r) n
        change
          (Fintype.card
            (al k (r + 1)) : ℝ) <
            (aG (Fin.last r) n : ℝ) *
              (ε (Fin.last r) n) ^ 2 at h
        exact h
      let bc :=
        iF
          lD upper
          (ε (Fin.last r))
          (aG (Fin.last r))
          wF xI
          (length (Fin.last r))
          (iB (Fin.last r))
      let eE :
          aa G k r :=
        initial.ed.bb bc.aQ
      let εlower : (j : Fin r) → ℕ → ℝ :=
        fun j => ε j.castSucc
      let jI : (j : Fin r) → ℕ → ℕ :=
        fun j => aG j.castSucc
      let jJ : Fin r → ℕ :=
        fun j => length j.castSucc
      have uf :
          ∀ j n, 0 ≤ εlower j n :=
        fun j n => hε j.castSucc n
      have vy :
          ∀ j n,
            (Fintype.card
              (al k (j.1 + 1)) : ℝ) <
              (jI j n : ℝ) *
                (εlower j n) ^ 2 :=
        fun j n => dP j.castSucc n
      have uj :
          ∀ j, 0 < jJ j :=
        fun j => iB j.castSucc
      obtain ⟨aA⟩ :=
        ih eE εlower jI jJ
          uf vy uj
      let bA :
          aa G k r :=
        aA.an.bb
          bc.an
      let an :
          aa G k (r + 1) :=
        bA.eF upper
      let aQ :
          aa G k (r + 1) :=
        aA.aQ.eF upper
      let index : Fin (r + 1) → ℕ :=
        fun j =>
          Fin.lastCases bc.index
            aA.index j
      have ku :
          aA.aQ.bl =
            bc.aQ := by
        calc
          aA.aQ.bl =
              eE.bl :=
            aA.dZ
          _ = bc.aQ :=
            aa.eY
              initial.ed bc.aQ
      have fS :
          aA.an.bl =
            bc.aQ := by
        calc
          aA.an.bl =
              eE.bl :=
            aA.da
          _ = bc.aQ :=
            aa.eY
              initial.ed bc.aQ
      refine ⟨{
        index := index
        an := an
        aQ := aQ
        dy := ?_
        bJ := ?_
        da := ?_
        dZ := ?_
        fM := ?_
        regular := ?_
        eo := ?_
        gN := ?_
        bT := ?_
        c1 := ?_ }⟩
      · have lk :
            aA.aQ.db
              bA := by
          intro q e
          cases q using Fin.lastCases with
          | last =>
              simp only [bA,
                aa.bb,
                Fin.lastCases_last]
              change al k r at e
              have heq :
                  aA.aQ.partition
                      (Fin.last r) e =
                    bc.aQ e :=
                congrFun ku e
              rw [heq]
              exact bc.dy e
          | cast i =>
              simp only [bA,
                aa.bb,
                Fin.lastCases_castSucc]
              exact aA.dy
                i.castSucc e
        exact aa.g3
          lk
          (aP.refl upper)
      · have lk :
            bA.db initial.ed := by
          intro q e
          cases q using Fin.lastCases with
          | last =>
              simp only [bA,
                aa.bb,
                Fin.lastCases_last]
              change al k r at e
              exact bc.bJ e
          | cast i =>
              simp only [bA,
                aa.bb,
                Fin.lastCases_castSucc]
              have h :=
                aA.bJ
                  i.castSucc e
              simpa only [eE,
                aa.bb,
                Fin.lastCases_castSucc,
                aa.ed] using h
        have ve :=
          aa.g3
            lk
            (aP.refl upper)
        simpa [an, upper] using ve
      · simp [an, upper]
      · simp [aQ, upper]
      · intro q
        cases q using Fin.lastCases with
        | last =>
            simpa [index] using bc.fM
        | cast i =>
            simpa [index, jJ] using
              aA.fM i
      · intro q
        cases q using Fin.lastCases with
        | last =>
            simp only [aQ,
              aa.aT,
              aa.dB,
              Fin.succ_last,
              cR,
              index, Fin.lastCases_last]
            change
              @a3
                G _ _ k r
                (aA.aQ.partition
                  (Fin.last r))
                upper
                (ε (Fin.last r) bc.index)
            have dk := bc.lC
            rw [← ku] at dk
            exact dk
        | cast i =>
            have dk :=
              aA.regular i
            simp only [aQ,
              aa.aT,
              Fin.succ_castSucc,
              cR,
              index, Fin.lastCases_castSucc]
            change
              @a3
                G _ _ k i.1
                (aA.aQ.partition
                  i.castSucc)
                (aA.aQ.partition i.succ)
                (ε i.castSucc
                  (aA.index i))
            exact dk
      · intro q
        cases q using Fin.lastCases with
        | last =>
            have ip := bc.eo
            simp only [aQ, an, bA,
              aa.aT,
              aa.dB,
              aa.bb,
              Fin.lastCases_last, Fin.succ_last]
            change
              0 ≤
                aH
                    aA.aQ.bl upper -
                  aH
                    bc.an upper
            rw [ku]
            exact ip
        | cast i =>
            have ip :=
              aA.eo i
            simp only [aQ, an, bA,
              aa.aT,
              aa.bb,
              Fin.lastCases_castSucc,
              Fin.succ_castSucc]
            convert ip using 1
      · intro q
        cases q using Fin.lastCases with
        | last =>
            have ip := bc.gN
            simp only [aQ, an, bA,
              aa.aT,
              aa.dB,
              aa.bb,
              Fin.lastCases_last, Fin.succ_last]
            change
              aH
                    aA.aQ.bl upper -
                  aH
                    bc.an upper ≤
                (Fintype.card
                  (al k (r + 1)) : ℝ) /
                    (length (Fin.last r) : ℝ)
            rw [ku]
            exact ip
        | cast i =>
            have ip :=
              aA.gN i
            simp only [aQ, an, bA,
              aa.aT,
              aa.bb,
              Fin.lastCases_castSucc,
              Fin.succ_castSucc, jJ]
            convert ip using 1; rfl
      · intro q
        cases q using Fin.lastCases with
        | last =>
            intro e
            have b8 :=
              bc.bT e
            simp only [an, bA,
              aa.aT,
              aa.bb,
              Fin.lastCases_last,
              index, Fin.lastCases_last]
            change al k r at e
            change
              ab.aO
                    (bc.an e) ≤
                aL
                    r (aG (Fin.last r))
                    bc.index *
                  ab.aO
                    (initial.partition
                      (Fin.last r).castSucc e)
            exact b8
        | cast i =>
            intro e
            change al k i.1 at e
            have b8 :=
              aA.bT i e
            simp only [an, bA,
              aa.aT,
              aa.bb,
              Fin.lastCases_castSucc,
              index, Fin.lastCases_castSucc]
            change
              ab.aO
                  (aA.an.partition
                    i.castSucc e) ≤
                aL
                    i.1 (aG i.castSucc)
                    (aA.index i) *
                  ab.aO
                    (initial.partition
                      i.castSucc.castSucc e)
            simp only [jI, eE,
              aa.bb,
              Fin.lastCases_castSucc,
              aa.ed] at b8
            convert b8 using 1
      · intro q
        cases q using Fin.lastCases with
        | last =>
            intro e
            change al k r at e
            have b8 :=
              bc.c1 e
            simp only [aQ,
              aa.aT,
              index, Fin.lastCases_last]
            change
              ab.aO
                  (aA.aQ.partition
                    (Fin.last r) e) ≤
                aL
                    r (aG (Fin.last r))
                    (bc.index + 1) *
                  ab.aO
                    (initial.partition
                      (Fin.last r).castSucc e)
            have heq :
                aA.aQ.partition
                    (Fin.last r) e =
                  bc.aQ e :=
              congrFun ku e
            rw [heq]
            exact b8
        | cast i =>
            intro e
            change al k i.1 at e
            have b8 :=
              aA.c1 i e
            simp only [aQ,
              aa.aT,
              index, Fin.lastCases_castSucc]
            change
              ab.aO
                  (aA.aQ.partition
                    i.castSucc e) ≤
                aL
                    i.1 (aG i.castSucc)
                    (aA.index i + 1) *
                  ab.aO
                    (initial.partition
                      i.castSucc.castSucc e)
            simp only [jI, eE,
              aa.bb,
              Fin.lastCases_castSucc,
              aa.ed] at b8
            convert b8 using 1
namespace bk
end bk
end av.ag
end
section
namespace av.ag
open scoped BigOperators
structure a5
    (G : Type*) [Fintype G] [DecidableEq G]
    (k r : ℕ)
    (initial : aa G k r)
    (ε : (j : Fin r) → ℕ → ℝ)
    (aG : (j : Fin r) → ℕ → ℕ)
    (length : Fin r → ℕ) where
  index : Fin r → ℕ
  an : aa G k r
  aQ : aa G k r
  dy : aQ.db an
  bJ : an.db initial
  da :
    an.bl = initial.bl
  dZ :
    aQ.bl = initial.bl
  fM : ∀ j, index j < length j
  lE :
    ∀ j : Fin r,
      a3
        (aQ.partition j.castSucc)
        (an.partition j.succ)
        (ε j (index j))
  eo :
    ∀ j : Fin r,
      0 ≤
        aH
            (aQ.partition j.castSucc)
            (an.partition j.succ) -
          aH
            (an.partition j.castSucc)
            (an.partition j.succ)
  gN :
    ∀ j : Fin r,
      aH
            (aQ.partition j.castSucc)
            (an.partition j.succ) -
          aH
            (an.partition j.castSucc)
            (an.partition j.succ) ≤
        (Fintype.card
          (al k (j.1 + 1)) : ℝ) /
            (length j : ℝ)
  bT :
    ∀ (j : Fin r) (e : al k j.1),
      ab.aO
          (an.partition j.castSucc e) ≤
        aL
            j.1 (aG j) (index j) *
          ab.aO
            (initial.partition j.castSucc e)
  c1 :
    ∀ (j : Fin r) (e : al k j.1),
      ab.aO
          (aQ.partition j.castSucc e) ≤
        aL
            j.1 (aG j) (index j + 1) *
          ab.aO
            (initial.partition j.castSucc e)
namespace a5
def nO
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : aa G k r}
    {ε : (j : Fin r) → ℕ → ℝ}
    {aG : (j : Fin r) → ℕ → ℕ}
    {length : Fin r → ℕ}
    (R : a5
      G k r initial ε aG length) :
    ak G k r where
  an := R.an
  aQ := R.aQ
  dy := R.dy
end a5
theorem a5.nonempty
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (initial : aa G k r)
    (ε : (j : Fin r) → ℕ → ℝ)
    (aG : (j : Fin r) → ℕ → ℕ)
    (length : Fin r → ℕ)
    (hε : ∀ j n, 0 ≤ ε j n)
    (dP :
      ∀ j n,
        (Fintype.card
          (al k (j.1 + 1)) : ℝ) <
          (aG j n : ℝ) * (ε j n) ^ 2)
    (iB : ∀ j, 0 < length j) :
    Nonempty
      (a5
        G k r initial ε aG length) := by
  induction r with
  | zero =>
      let index : Fin 0 → ℕ := fun j => Fin.elim0 j
      refine ⟨{
        index := index
        an := initial
        aQ := initial
        dy :=
          aa.db.refl initial
        bJ :=
          aa.db.refl initial
        da := rfl
        dZ := rfl
        fM := ?_
        lE := ?_
        eo := ?_
        gN := ?_
        bT := ?_
        c1 := ?_ }⟩
      · intro j
        exact Fin.elim0 j
      · intro j
        exact Fin.elim0 j
      · intro j
        exact Fin.elim0 j
      · intro j
        exact Fin.elim0 j
      · intro j
        exact Fin.elim0 j
      · intro j
        exact Fin.elim0 j
  | succ r ih =>
      let lD :
          af G k r :=
        initial.ed.bl
      let upper :
          af G k (r + 1) :=
        initial.bl
      have wF :
          ∀ n, 0 ≤ ε (Fin.last r) n :=
        fun n => hε (Fin.last r) n
      have xI :
          ∀ n,
            (Fintype.card
              (al k (r + 1)) : ℝ) <
              (aG (Fin.last r) n : ℝ) *
                (ε (Fin.last r) n) ^ 2 := by
        intro n
        have h := dP (Fin.last r) n
        change
          (Fintype.card
            (al k (r + 1)) : ℝ) <
            (aG (Fin.last r) n : ℝ) *
              (ε (Fin.last r) n) ^ 2 at h
        exact h
      let bc :=
        iF
          lD upper
          (ε (Fin.last r))
          (aG (Fin.last r))
          wF xI
          (length (Fin.last r))
          (iB (Fin.last r))
      let eE :
          aa G k r :=
        initial.ed.bb bc.an
      let εlower : (j : Fin r) → ℕ → ℝ :=
        fun j => ε j.castSucc
      let jI : (j : Fin r) → ℕ → ℕ :=
        fun j => aG j.castSucc
      let jJ : Fin r → ℕ :=
        fun j => length j.castSucc
      have uf :
          ∀ j n, 0 ≤ εlower j n :=
        fun j n => hε j.castSucc n
      have vy :
          ∀ j n,
            (Fintype.card
              (al k (j.1 + 1)) : ℝ) <
              (jI j n : ℝ) *
                (εlower j n) ^ 2 :=
        fun j n => dP j.castSucc n
      have uj :
          ∀ j, 0 < jJ j :=
        fun j => iB j.castSucc
      obtain ⟨aA⟩ :=
        ih eE εlower jI jJ
          uf vy uj
      let bA :
          aa G k r :=
        aA.an
      let dD :
          aa G k r :=
        aA.aQ.bb bc.aQ
      let an :
          aa G k (r + 1) :=
        bA.eF upper
      let aQ :
          aa G k (r + 1) :=
        dD.eF upper
      let index : Fin (r + 1) → ℕ :=
        fun j =>
          Fin.lastCases bc.index
            aA.index j
      have ku :
          aA.aQ.bl =
            bc.an := by
        calc
          aA.aQ.bl =
              eE.bl :=
            aA.dZ
          _ = bc.an :=
            aa.eY
              initial.ed bc.an
      have fS :
          aA.an.bl =
            bc.an := by
        calc
          aA.an.bl =
              eE.bl :=
            aA.da
          _ = bc.an :=
            aa.eY
              initial.ed bc.an
      refine ⟨{
        index := index
        an := an
        aQ := aQ
        dy := ?_
        bJ := ?_
        da := ?_
        dZ := ?_
        fM := ?_
        lE := ?_
        eo := ?_
        gN := ?_
        bT := ?_
        c1 := ?_ }⟩
      · have lk :
            dD.db bA := by
          intro q e
          cases q using Fin.lastCases with
          | last =>
              simp only [dD, bA,
                aa.bb,
                Fin.lastCases_last]
              change al k r at e
              have heq :
                  aA.an.partition
                      (Fin.last r) e =
                    bc.an e :=
                congrFun fS e
              rw [heq]
              exact bc.dy e
          | cast i =>
              simp only [dD, bA,
                aa.bb,
                Fin.lastCases_castSucc]
              exact aA.dy
                i.castSucc e
        exact aa.g3
          lk
          (aP.refl upper)
      · have wM :
            eE.db initial.ed := by
          exact aa.oD
            initial.ed bc.an
            (by
              simpa only [lD] using
                bc.bJ)
        have lk :
            bA.db initial.ed :=
          aa.db.trans
            aA.bJ
            wM
        have ve :=
          aa.g3
            lk
            (aP.refl upper)
        simpa [an, bA, upper] using ve
      · simp [an, upper]
      · simp [aQ, upper]
      · intro q
        cases q using Fin.lastCases with
        | last =>
            simpa [index] using bc.fM
        | cast i =>
            simpa [index, jJ] using
              aA.fM i
      · intro q
        cases q using Fin.lastCases with
        | last =>
            simp only [aQ, dD, an,
              bA,
              aa.aT,
              aa.dB,
              aa.bb,
              Fin.lastCases_last, Fin.succ_last,
              index, Fin.lastCases_last]
            exact bc.lC
        | cast i =>
            have dk :=
              aA.lE i
            simp only [aQ, dD, an,
              bA,
              aa.aT,
              aa.bb,
              Fin.lastCases_castSucc, Fin.succ_castSucc,
              index, Fin.lastCases_castSucc]
            change
              @a3
                G _ _ k i.1
                (aA.aQ.partition
                  i.castSucc)
                (aA.an.partition
                  i.succ)
                (ε i.castSucc
                  (aA.index i))
            exact dk
      · intro q
        cases q using Fin.lastCases with
        | last =>
            have ip := bc.eo
            simp only [aQ, dD, an,
              bA,
              aa.aT,
              aa.dB,
              aa.bb,
              Fin.lastCases_last, Fin.succ_last]
            change
              0 ≤
                aH
                    bc.aQ upper -
                  aH
                    aA.an.bl
                    upper
            rw [fS]
            exact ip
        | cast i =>
            have ip :=
              aA.eo i
            simp only [aQ, dD, an,
              bA,
              aa.aT,
              aa.bb,
              Fin.lastCases_castSucc, Fin.succ_castSucc]
            convert ip using 1
      · intro q
        cases q using Fin.lastCases with
        | last =>
            have ip := bc.gN
            simp only [aQ, dD, an,
              bA,
              aa.aT,
              aa.dB,
              aa.bb,
              Fin.lastCases_last, Fin.succ_last]
            change
              aH
                    bc.aQ upper -
                  aH
                    aA.an.bl
                    upper ≤
                (Fintype.card
                  (al k (r + 1)) : ℝ) /
                    (length (Fin.last r) : ℝ)
            rw [fS]
            exact ip
        | cast i =>
            have ip :=
              aA.gN i
            simp only [aQ, dD, an,
              bA,
              aa.aT,
              aa.bb,
              Fin.lastCases_castSucc, Fin.succ_castSucc,
              jJ]
            convert ip using 1; rfl
      · intro q
        cases q using Fin.lastCases with
        | last =>
            intro e
            change al k r at e
            have b8 :=
              bc.bT e
            simp only [an, bA,
              aa.aT,
              index, Fin.lastCases_last]
            change
              ab.aO
                  (aA.an.partition
                    (Fin.last r) e) ≤
                aL
                    r (aG (Fin.last r))
                    bc.index *
                  ab.aO
                    (initial.partition
                      (Fin.last r).castSucc e)
            have heq :
                aA.an.partition
                    (Fin.last r) e =
                  bc.an e :=
              congrFun fS e
            rw [heq]
            exact b8
        | cast i =>
            intro e
            change al k i.1 at e
            have b8 :=
              aA.bT i e
            simp only [an, bA,
              aa.aT,
              index, Fin.lastCases_castSucc]
            change
              ab.aO
                  (aA.an.partition
                    i.castSucc e) ≤
                aL
                    i.1 (aG i.castSucc)
                    (aA.index i) *
                  ab.aO
                    (initial.partition
                      i.castSucc.castSucc e)
            simp only [jI, eE,
              aa.bb,
              Fin.lastCases_castSucc,
              aa.ed] at b8
            convert b8 using 1
      · intro q
        cases q using Fin.lastCases with
        | last =>
            intro e
            change al k r at e
            have b8 :=
              bc.c1 e
            simp only [aQ, dD,
              aa.aT,
              aa.bb,
              Fin.lastCases_last,
              index, Fin.lastCases_last]
            exact b8
        | cast i =>
            intro e
            change al k i.1 at e
            have b8 :=
              aA.c1 i e
            simp only [aQ, dD,
              aa.aT,
              aa.bb,
              Fin.lastCases_castSucc,
              index, Fin.lastCases_castSucc]
            change
              ab.aO
                  (aA.aQ.partition
                    i.castSucc e) ≤
                aL
                    i.1 (aG i.castSucc)
                    (aA.index i + 1) *
                  ab.aO
                    (initial.partition
                      i.castSucc.castSucc e)
            simp only [jI, eE,
              aa.bb,
              Fin.lastCases_castSucc,
              aa.ed] at b8
            convert b8 using 1
namespace ak
end ak
namespace a5
end a5
end av.ag
end
section
namespace av.ag
inductive aJ (k : ℕ) : ℕ → Type
  | nil : aJ k 0
  | node {r : ℕ}
      (aR : ℕ → ℝ)
      (aG : ℕ → ℕ)
      (length : ℕ)
      (next : Fin length → aJ k r) :
      aJ k (r + 1)
namespace aJ
def IsAdmissible {k r : ℕ} :
    aJ k r → Prop
  | .nil => True
  | .node aR aG length next =>
      (∀ n, 0 ≤ aR n) ∧
      (∀ n,
        (Fintype.card (al k r) : ℝ) <
          (aG n : ℝ) * (aR n) ^ 2) ∧
      0 < length ∧
      ∀ i, (next i).IsAdmissible
inductive br {k : ℕ} :
    {r : ℕ} → aJ k r → Type
  | nil : br (.nil : aJ k 0)
  | node {r : ℕ}
      {aR : ℕ → ℝ}
      {aG : ℕ → ℕ}
      {length : ℕ}
      {next : Fin length → aJ k r}
      (index : Fin length)
      (lower : br (next index)) :
      br (.node aR aG length next)
namespace br
def aR {k r : ℕ}
    {S : aJ k r}
    (P : S.br) :
    (j : Fin r) → ℕ → ℝ :=
  match P with
  | .nil => fun j => Fin.elim0 j
  | .node (aR := aR) _ lower =>
      fun j => Fin.lastCases aR lower.aR j
def aG {k r : ℕ}
    {S : aJ k r}
    (P : S.br) :
    (j : Fin r) → ℕ → ℕ :=
  match P with
  | .nil => fun j => Fin.elim0 j
  | .node (aG := aG) _ lower =>
      fun j => Fin.lastCases aG lower.aG j
def length {k r : ℕ}
    {S : aJ k r}
    (P : S.br) :
    Fin r → ℕ :=
  match P with
  | .nil => fun j => Fin.elim0 j
  | .node (length := length) _ lower =>
      fun j => Fin.lastCases length lower.length j
def index {k r : ℕ}
    {S : aJ k r}
    (P : S.br) :
    Fin r → ℕ :=
  match P with
  | .nil => fun j => Fin.elim0 j
  | .node bW lower =>
      fun j => Fin.lastCases bW.1 lower.index j
@[simp]
theorem sB
    {k r : ℕ}
    {aR : ℕ → ℝ}
    {aG : ℕ → ℕ}
    {length : ℕ}
    {next : Fin length → aJ k r}
    (bW : Fin length)
    (lower : (next bW).br) :
    (br.node
      (aR := aR) (aG := aG)
      bW lower).aR (Fin.last r) =
      aR := by
  simp [br.aR]
@[simp]
theorem qk
    {k r : ℕ}
    {aR : ℕ → ℝ}
    {aG : ℕ → ℕ}
    {length : ℕ}
    {next : Fin length → aJ k r}
    (bW : Fin length)
    (lower : (next bW).br)
    (j : Fin r) :
    (br.node
      (aR := aR) (aG := aG)
      bW lower).aR j.castSucc =
      lower.aR j := by
  simp [br.aR]
@[simp]
theorem q9
    {k r : ℕ}
    {aR : ℕ → ℝ}
    {aG : ℕ → ℕ}
    {length : ℕ}
    {next : Fin length → aJ k r}
    (bW : Fin length)
    (lower : (next bW).br) :
    (br.node
      (aR := aR) (aG := aG)
      bW lower).aG (Fin.last r) =
      aG := by
  simp [br.aG]
@[simp]
theorem vz
    {k r : ℕ}
    {aR : ℕ → ℝ}
    {aG : ℕ → ℕ}
    {length : ℕ}
    {next : Fin length → aJ k r}
    (bW : Fin length)
    (lower : (next bW).br)
    (j : Fin r) :
    (br.node
      (aR := aR) (aG := aG)
      bW lower).aG j.castSucc =
      lower.aG j := by
  simp [br.aG]
@[simp]
theorem xJ
    {k r : ℕ}
    {aR : ℕ → ℝ}
    {aG : ℕ → ℕ}
    {length : ℕ}
    {next : Fin length → aJ k r}
    (bW : Fin length)
    (lower : (next bW).br) :
    (br.node
      (aR := aR) (aG := aG)
      bW lower).length (Fin.last r) =
      length := by
  simp [br.length]
@[simp]
theorem vA
    {k r : ℕ}
    {aR : ℕ → ℝ}
    {aG : ℕ → ℕ}
    {length : ℕ}
    {next : Fin length → aJ k r}
    (bW : Fin length)
    (lower : (next bW).br)
    (j : Fin r) :
    (br.node
      (aR := aR) (aG := aG)
      bW lower).length j.castSucc =
      lower.length j := by
  simp [br.length]
@[simp]
theorem rR
    {k r : ℕ}
    {aR : ℕ → ℝ}
    {aG : ℕ → ℕ}
    {length : ℕ}
    {next : Fin length → aJ k r}
    (bW : Fin length)
    (lower : (next bW).br) :
    (br.node
      (aR := aR) (aG := aG)
      bW lower).index (Fin.last r) =
      bW.1 := by
  simp [br.index]
@[simp]
theorem v9
    {k r : ℕ}
    {aR : ℕ → ℝ}
    {aG : ℕ → ℕ}
    {length : ℕ}
    {next : Fin length → aJ k r}
    (bW : Fin length)
    (lower : (next bW).br)
    (j : Fin r) :
    (br.node
      (aR := aR) (aG := aG)
      bW lower).index j.castSucc =
      lower.index j := by
  simp [br.index]
theorem yo {k r : ℕ}
    {S : aJ k r}
    (P : S.br) :
    ∀ j, P.index j < P.length j := by
  induction P with
  | nil =>
      intro j
      exact Fin.elim0 j
  | node bW lower ih =>
      intro j
      cases j using Fin.lastCases with
      | last =>
          simp [index, length]
      | cast j =>
          simpa [index, length] using ih j
theorem uk {k r : ℕ}
    {S : aJ k r}
    (P : S.br) (hS : S.IsAdmissible) :
    ∀ j n, 0 ≤ P.aR j n := by
  induction P with
  | nil =>
      intro j
      exact Fin.elim0 j
  | @node r aR aG length next bW lower ih =>
      rcases hS with ⟨rS, _hbudget, _hlength, vD⟩
      intro j n
      cases j using Fin.lastCases with
      | last =>
          simpa using rS n
      | cast j =>
          simpa using ih (vD bW) j n
theorem xk {k r : ℕ}
    {S : aJ k r}
    (P : S.br) (hS : S.IsAdmissible) :
    ∀ j n,
      (Fintype.card (al k (j.1 + 1)) : ℝ) <
        (P.aG j n : ℝ) * (P.aR j n) ^ 2 := by
  induction P with
  | nil =>
      intro j
      exact Fin.elim0 j
  | @node r aR aG length next bW lower ih =>
      rcases hS with ⟨_htolerance, gS, _hlength, vD⟩
      intro j n
      cases j using Fin.lastCases with
      | last =>
          change
            (Fintype.card (al k (r + 1)) : ℝ) <
              ((br.node
                (aR := aR) (aG := aG)
                bW lower).aG (Fin.last r) n : ℕ) *
                (br.node
                  (aR := aR) (aG := aG)
                  bW lower).aR (Fin.last r) n ^ 2
          rw [q9, sB]
          exact gS n
      | cast j =>
          change
            (Fintype.card (al k (j.1 + 1)) : ℝ) <
              ((br.node
                (aR := aR) (aG := aG)
                bW lower).aG j.castSucc n : ℕ) *
                (br.node
                  (aR := aR) (aG := aG)
                  bW lower).aR j.castSucc n ^ 2
          rw [vz, qk]
          exact ih (vD bW) j n
theorem length_pos {k r : ℕ}
    {S : aJ k r}
    (P : S.br) (hS : S.IsAdmissible) :
    ∀ j, 0 < P.length j := by
  induction P with
  | nil =>
      intro j
      exact Fin.elim0 j
  | @node r aR aG length next bW lower ih =>
      rcases hS with ⟨_htolerance, _hbudget, iB, vD⟩
      intro j
      cases j using Fin.lastCases with
      | last =>
          simpa using iB
      | cast j =>
          simpa using ih (vD bW) j
end br
structure uS
    {G : Type*} [Fintype G] [DecidableEq G]
    (k r : ℕ)
    (initial : aa G k r)
    (S : aJ k r) where
  cn : S.br
  fp :
    a5
      G k r initial
        cn.aR cn.aG cn.length
  vE : fp.index = cn.index
theorem uS.nonempty
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (initial : aa G k r)
    (S : aJ k r)
    (hS : S.IsAdmissible) :
    Nonempty (uS k r initial S) := by
  induction r with
  | zero =>
      cases S with
      | nil =>
          let cn :
              (aJ.nil :
                aJ k 0).br :=
            br.nil
          let fp :
              a5
                G k 0 initial
                  cn.aR cn.aG cn.length := {
            index := cn.index
            an := initial
            aQ := initial
            dy :=
              aa.db.refl initial
            bJ :=
              aa.db.refl initial
            da := rfl
            dZ := rfl
            fM := fun j => Fin.elim0 j
            lE := fun j => Fin.elim0 j
            eo := fun j => Fin.elim0 j
            gN := fun j => Fin.elim0 j
            bT := fun j => Fin.elim0 j
            c1 := fun j => Fin.elim0 j }
          exact ⟨{
            cn := cn
            fp := fp
            vE := rfl }⟩
  | succ r ih =>
      cases S with
      | @node _ aR aG length next =>
          rcases hS with
            ⟨rS, gS, iB, vD⟩
          let lD :
              af G k r :=
            initial.ed.bl
          let upper :
              af G k (r + 1) :=
            initial.bl
          let bc :=
            iF
              lD upper aR aG
              rS gS length iB
          let bW : Fin length :=
            ⟨bc.index, bc.fM⟩
          let eE :
              aa G k r :=
            initial.ed.bb bc.an
          obtain ⟨ra⟩ :=
            ih eE (next bW) (vD bW)
          let i2 := ra.cn
          let aA := ra.fp
          have uT :
              aA.index = i2.index :=
            ra.vE
          let cn :
              (aJ.node
                aR aG length next).br :=
            br.node
              (aR := aR) (aG := aG)
              bW i2
          let bA :
              aa G k r :=
            aA.an
          let dD :
              aa G k r :=
            aA.aQ.bb bc.aQ
          let an :
              aa G k (r + 1) :=
            bA.eF upper
          let aQ :
              aa G k (r + 1) :=
            dD.eF upper
          have ku :
              aA.aQ.bl =
                bc.an := by
            calc
              aA.aQ.bl =
                  eE.bl :=
                aA.dZ
              _ = bc.an :=
                aa.eY
                  initial.ed bc.an
          have fS :
              aA.an.bl =
                bc.an := by
            calc
              aA.an.bl =
                  eE.bl :=
                aA.da
              _ = bc.an :=
                aa.eY
                  initial.ed bc.an
          let fp :
              a5
                G k (r + 1) initial
                  cn.aR cn.aG cn.length := {
            index := cn.index
            an := an
            aQ := aQ
            dy := by
              have lk :
                  dD.db bA := by
                intro q e
                cases q using Fin.lastCases with
                | last =>
                    simp only [dD, bA,
                      aa.bb,
                      Fin.lastCases_last]
                    change al k r at e
                    have heq :
                        aA.an.partition
                            (Fin.last r) e =
                          bc.an e :=
                      congrFun fS e
                    rw [heq]
                    exact bc.dy e
                | cast i =>
                    simp only [dD, bA,
                      aa.bb,
                      Fin.lastCases_castSucc]
                    exact aA.dy
                      i.castSucc e
              exact aa.g3
                lk
                (aP.refl upper)
            bJ := by
              have wM :
                  eE.db initial.ed := by
                exact
                  aa.oD
                    initial.ed bc.an
                    (by
                      simpa only [lD] using
                        bc.bJ)
              have lk :
                  bA.db initial.ed :=
                aa.db.trans
                  aA.bJ
                  wM
              have ve :=
                aa.g3
                  lk
                  (aP.refl upper)
              simpa [an, bA, upper] using ve
            da := by
              simp [an, upper]
            dZ := by
              simp [aQ, upper]
            fM := by
              exact cn.yo
            lE := by
              intro q
              cases q using Fin.lastCases with
              | last =>
                  simp only [aQ, dD, an,
                    bA,
                    aa.aT,
                    aa.dB,
                    aa.bb,
                    Fin.lastCases_last, Fin.succ_last]
                  change
                    a3
                      bc.aQ upper
                      (cn.aR (Fin.last r)
                        (cn.index (Fin.last r)))
                  simpa [cn, bW] using
                    bc.lC
              | cast i =>
                  have dk :=
                    aA.lE i
                  simp only [aQ, dD, an,
                    bA,
                    aa.aT,
                    aa.bb,
                    Fin.lastCases_castSucc, Fin.succ_castSucc]
                  change
                    @a3
                      G _ _ k i.1
                      (aA.aQ.partition
                        i.castSucc)
                      (aA.an.partition
                        i.succ)
                      (cn.aR i.castSucc
                        (cn.index i.castSucc))
                  rw [show cn.aR i.castSucc =
                      i2.aR i by
                        simp [cn]]
                  rw [show cn.index i.castSucc =
                      i2.index i by
                        simp [cn]]
                  rw [← congrFun uT i]
                  exact dk
            eo := by
              intro q
              cases q using Fin.lastCases with
              | last =>
                  have ip := bc.eo
                  simp only [aQ, dD, an,
                    bA,
                    aa.aT,
                    aa.dB,
                    aa.bb,
                    Fin.lastCases_last, Fin.succ_last]
                  change
                    0 ≤
                      aH
                          bc.aQ upper -
                        aH
                          aA.an.bl
                          upper
                  rw [fS]
                  exact ip
              | cast i =>
                  have ip :=
                    aA.eo i
                  simp only [aQ, dD, an,
                    bA,
                    aa.aT,
                    aa.bb,
                    Fin.lastCases_castSucc, Fin.succ_castSucc]
                  convert ip using 1
            gN := by
              intro q
              cases q using Fin.lastCases with
              | last =>
                  have ip := bc.gN
                  simp only [aQ, dD, an,
                    bA,
                    aa.aT,
                    aa.dB,
                    aa.bb,
                    Fin.lastCases_last, Fin.succ_last]
                  change
                    aH
                          bc.aQ upper -
                        aH
                          aA.an.bl
                          upper ≤
                      (Fintype.card
                        (al k (r + 1)) : ℝ) /
                          (cn.length (Fin.last r) : ℝ)
                  rw [fS]
                  simpa [cn] using ip
              | cast i =>
                  have ip :=
                    aA.gN i
                  simp only [aQ, dD, an,
                    bA,
                    aa.aT,
                    aa.bb,
                    Fin.lastCases_castSucc, Fin.succ_castSucc]
                  change
                    aH
                          (aA.aQ.partition
                            i.castSucc)
                          (aA.an.partition
                            i.succ) -
                        aH
                          (aA.an.partition
                            i.castSucc)
                          (aA.an.partition
                            i.succ) ≤
                      (Fintype.card
                        (al k (i.1 + 1)) : ℝ) /
                          (cn.length i.castSucc : ℝ)
                  rw [show cn.length i.castSucc =
                      i2.length i by
                        simp [cn]]
                  exact ip
            bT := by
              intro q
              cases q using Fin.lastCases with
              | last =>
                  intro e
                  change al k r at e
                  have b8 :=
                    bc.bT e
                  simp only [an, bA,
                    aa.aT]
                  change
                    ab.aO
                        (aA.an.partition
                          (Fin.last r) e) ≤
                      aL
                          r (cn.aG (Fin.last r))
                          (cn.index (Fin.last r)) *
                        ab.aO
                          (initial.partition
                            (Fin.last r).castSucc e)
                  have heq :
                      aA.an.partition
                          (Fin.last r) e =
                        bc.an e :=
                    congrFun fS e
                  rw [heq]
                  simp only [cn, bW,
                    br.q9,
                    br.rR]
                  convert b8 using 1; rfl
              | cast i =>
                  intro e
                  change al k i.1 at e
                  have b8 :=
                    aA.bT i e
                  simp only [an, bA,
                    aa.aT]
                  change
                    ab.aO
                        (aA.an.partition
                          i.castSucc e) ≤
                      aL
                          i.1 (cn.aG i.castSucc)
                          (cn.index i.castSucc) *
                        ab.aO
                          (initial.partition
                            i.castSucc.castSucc e)
                  rw [show cn.aG i.castSucc =
                      i2.aG i by
                        simp [cn]]
                  rw [show cn.index i.castSucc =
                      i2.index i by
                        simp [cn]]
                  rw [← congrFun uT i]
                  simp only [eE,
                    aa.bb,
                    Fin.lastCases_castSucc,
                    aa.ed] at b8
                  convert b8 using 1
            c1 := by
              intro q
              cases q using Fin.lastCases with
              | last =>
                  intro e
                  change al k r at e
                  have b8 :=
                    bc.c1 e
                  simp only [aQ, dD,
                    aa.aT,
                    aa.bb,
                    Fin.lastCases_last]
                  change
                    ab.aO
                        (bc.aQ e) ≤
                      aL
                          r (cn.aG (Fin.last r))
                          (cn.index (Fin.last r) + 1) *
                        ab.aO
                          (initial.partition
                            (Fin.last r).castSucc e)
                  simp only [cn, bW,
                    br.q9,
                    br.rR]
                  convert b8 using 1
                  rfl
              | cast i =>
                  intro e
                  change al k i.1 at e
                  have b8 :=
                    aA.c1 i e
                  simp only [aQ, dD,
                    aa.aT,
                    aa.bb,
                    Fin.lastCases_castSucc]
                  change
                    ab.aO
                        (aA.aQ.partition
                          i.castSucc e) ≤
                      aL
                          i.1 (cn.aG i.castSucc)
                          (cn.index i.castSucc + 1) *
                        ab.aO
                          (initial.partition
                            i.castSucc.castSucc e)
                  rw [show cn.aG i.castSucc =
                      i2.aG i by
                        simp [cn]]
                  rw [show cn.index i.castSucc =
                      i2.index i by
                        simp [cn]]
                  rw [← congrFun uT i]
                  simp only [eE,
                    aa.bb,
                    Fin.lastCases_castSucc,
                    aa.ed] at b8
                  convert b8 using 1 }
          exact ⟨{
            cn := cn
            fp := fp
            vE := rfl }⟩
theorem o1
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (initial : aa G k r)
    (S : aJ k r)
    (hS : S.IsAdmissible) :
    ∃ P : S.br,
      ∃ R :
          a5
            G k r initial P.aR P.aG P.length,
        R.index = P.index := by
  obtain ⟨uU⟩ :=
    uS.nonempty initial S hS
  exact
    ⟨uU.cn, uU.fp,
      uU.vE⟩
end aJ
end av.ag
end
section
namespace av.ag
open scoped BigOperators
noncomputable def j0 (k r : ℕ) : ℕ :=
  Fintype.card (aj k r)
noncomputable def r9 (r : ℕ) : ℕ :=
  Fintype.card (ct r)
noncomputable def qe (r M : ℕ) : ℕ :=
  r9 r * M
noncomputable def tI
    (r M : ℕ) (ξ : ℝ) : ℝ :=
  min (1 / 2)
    (ξ /
      (4 *
        ((qe r M : ℝ) + 1)))
noncomputable def om
    (k r M : ℕ) (ξ : ℝ) : ℝ :=
  tI r M ξ ^
      j0 k r /
    (4 *
      ((j0 k r : ℝ) + 1))
noncomputable def sa
    (k r M : ℕ) (ξ : ℝ) : ℝ :=
  om k r M ξ ^ 2
noncomputable def sb
    (k r M : ℕ) (ξ : ℝ) : ℝ :=
  ξ * sa k r M ξ / 4
noncomputable def ey
    (k j : ℕ) (τ : ℝ) : ℕ :=
  Nat.ceil
      ((Fintype.card (al k (j + 1)) : ℝ) /
        τ ^ 2) +
    1
theorem kh
    {k j : ℕ} {τ : ℝ} (iQ : 0 < τ) :
    (Fintype.card (al k (j + 1)) : ℝ) <
      (ey k j τ : ℝ) * τ ^ 2 := by
  have Ee : 0 < τ ^ 2 := sq_pos_of_pos iQ
  have By :
      (Fintype.card (al k (j + 1)) : ℝ) /
          τ ^ 2 <
        (ey k j τ : ℝ) := by
    unfold ey
    calc
      (Fintype.card (al k (j + 1)) : ℝ) /
            τ ^ 2 ≤
          (Nat.ceil
            ((Fintype.card
              (al k (j + 1)) : ℝ) /
                τ ^ 2) : ℝ) :=
        Nat.le_ceil _
      _ <
          (Nat.ceil
            ((Fintype.card
              (al k (j + 1)) : ℝ) /
                τ ^ 2) : ℝ) + 1 := by
        linarith
      _ =
          ((Nat.ceil
              ((Fintype.card
                (al k (j + 1)) : ℝ) /
                  τ ^ 2) + 1 : ℕ) : ℝ) := by
        norm_num
  exact (div_lt_iff₀ Ee).1 By
def iC
    (r initialBound : ℕ)
    (aG : (j : Fin r) → ℕ → ℕ)
    (length : Fin r → ℕ) : ℕ :=
  initialBound *
    (1 +
      ∑ j : Fin r,
        aL
          j.1 (aG j) (length j))
namespace bk
end bk
namespace bk
end bk
end av.ag
end
section
namespace av.ag
structure aF where
  toFun : ℕ → ℕ
  monotone' : Monotone toFun
  nP : ∀ n, n + 1 ≤ toFun n
namespace aF
instance : CoeFun aF (fun _ => ℕ → ℕ) :=
  ⟨aF.toFun⟩
theorem monotone (F : aF) :
    Monotone F :=
  F.monotone'
theorem positive (F : aF) (n : ℕ) :
    0 < F n := by
  exact lt_of_lt_of_le (Nat.zero_lt_succ n)
    (F.nP n)
end aF
noncomputable def dC
    (F : aF) (M : ℕ) : ℝ :=
  1 / (F M : ℝ)
noncomputable def kv
    (k j : ℕ) (F : aF) (M : ℕ) : ℕ :=
  ey
    k j (dC F M)
noncomputable def bE
    (k j initialBound : ℕ) (F : aF) :
    ℕ → ℕ
  | 0 => initialBound
  | n + 1 =>
      (2 ^ (j + 1)) ^
          kv
            k j F
              (bE
                k j initialBound F n) *
        bE
          k j initialBound F n
noncomputable def fx
    (k j initialBound : ℕ) (F : aF) :
    ℕ → ℝ :=
  fun n =>
    dC F
      (bE
        k j initialBound F n)
noncomputable def gg
    (k j initialBound : ℕ) (F : aF) :
    ℕ → ℕ :=
  fun n =>
    kv k j F
      (bE
        k j initialBound F n)
@[simp]
theorem xU
    (k j initialBound : ℕ) (F : aF) :
    bE
      k j initialBound F 0 = initialBound :=
  rfl
@[simp]
theorem rv
    (k j initialBound n : ℕ) (F : aF) :
    bE
        k j initialBound F (n + 1) =
      (2 ^ (j + 1)) ^
          gg
            k j initialBound F n *
        bE
          k j initialBound F n :=
  rfl
@[simp]
theorem nQ
    (k j initialBound n : ℕ) (F : aF) :
    fx
        k j initialBound F n =
      1 /
        (F (bE
          k j initialBound F n) : ℝ) :=
  rfl
theorem k6
    (F : aF) (M : ℕ) :
    0 < dC F M := by
  unfold dC
  exact one_div_pos.mpr
    (by exact_mod_cast F.positive M)
theorem jm
    (k j initialBound : ℕ) (F : aF) :
    ∀ n,
      0 <
        fx
          k j initialBound F n := by
  intro n
  exact k6 F
    (bE
      k j initialBound F n)
theorem oo
    (k j initialBound : ℕ) (F : aF) :
    ∀ n,
      (Fintype.card
          (al k (j + 1)) : ℝ) <
        (gg
            k j initialBound F n : ℝ) *
          (fx
            k j initialBound F n) ^ 2 := by
  intro n
  exact kh
    (jm
      k j initialBound F n)
theorem eM
    (k j initialBound : ℕ) (F : aF) :
    ∀ n,
      bE
          k j initialBound F n =
        aL
            j (gg
              k j initialBound F) n *
          initialBound := by
  intro n
  induction n with
  | zero =>
      simp [aL]
  | succ n ih =>
      rw [rv, ih]
      simp [aL,
        Nat.mul_assoc]
noncomputable def dU
    (k j : ℕ) (γ : ℝ) : ℕ :=
  Nat.ceil
      ((Fintype.card
        (al k (j + 1)) : ℝ) / γ) +
    1
theorem h9
    (k j : ℕ) (γ : ℝ) :
    0 < dU k j γ := by
  unfold dU
  omega
theorem fb
    {k j : ℕ} {γ : ℝ} (Cp : 0 < γ) :
    (Fintype.card
        (al k (j + 1)) : ℝ) /
        (dU k j γ : ℝ) <
      γ := by
  let A : ℝ :=
    (Fintype.card
      (al k (j + 1)) : ℝ)
  let L : ℕ :=
    dU k j γ
  have Fn : 0 < L :=
    h9 k j γ
  have EJ : (0 : ℝ) < (L : ℝ) := by
    exact_mod_cast Fn
  have By : A / γ < (L : ℝ) := by
    dsimp only [A, L]
    unfold dU
    calc
      (Fintype.card
          (al k (j + 1)) : ℝ) / γ ≤
          (Nat.ceil
            ((Fintype.card
              (al k (j + 1)) : ℝ) / γ) : ℝ) :=
        Nat.le_ceil _
      _ <
          (Nat.ceil
            ((Fintype.card
              (al k (j + 1)) : ℝ) / γ) : ℝ) + 1 := by
        linarith
      _ =
          ((Nat.ceil
            ((Fintype.card
              (al k (j + 1)) : ℝ) / γ) + 1 : ℕ) : ℝ) := by
        norm_num
  have hA : A < (L : ℝ) * γ :=
    (div_lt_iff₀ Cp).1 By
  apply (div_lt_iff₀ EJ).2
  simpa [mul_comm] using hA
structure ki
    (G : Type*) [Fintype G] [DecidableEq G]
    (k j initialBound : ℕ)
    (initial : af G k j)
    (upper : af G k (j + 1))
    (F : aF) (γ : ℝ) where
  index : ℕ
  fM :
    index < dU k j γ
  an : af G k j
  aQ : af G k j
  dy : aP aQ an
  bJ :
    aP an initial
  lC :
    a3 aQ upper
      (1 /
        (F (bE
          k j initialBound F index) : ℝ))
  eo :
    0 ≤
      aH aQ upper -
        aH an upper
  gN :
    aH aQ upper -
        aH an upper ≤ γ
  bT :
    ∀ e,
      ab.aO (an e) ≤
        bE
          k j initialBound F index
  c1 :
    ∀ e,
      ab.aO (aQ e) ≤
        bE
          k j initialBound F (index + 1)
theorem ki.nonempty
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j initialBound : ℕ}
    (initial : af G k j)
    (upper : af G k (j + 1))
    (F : aF) {γ : ℝ} (Cp : 0 < γ)
    (gO :
      ∀ e,
        ab.aO (initial e) ≤
          initialBound) :
    Nonempty
      (ki
        G k j initialBound initial upper F γ) := by
  let τ : ℕ → ℝ :=
    fx k j initialBound F
  let B : ℕ → ℕ :=
    gg k j initialBound F
  let L : ℕ :=
    dU k j γ
  obtain ⟨R⟩ :=
    gw.nonempty
      initial upper τ B
      (fun n =>
        (jm
          k j initialBound F n).le)
      (oo
        k j initialBound F)
      (h9 k j γ)
  refine ⟨{
    index := R.index
    fM := R.fM
    an := R.an
    aQ := R.aQ
    dy := R.dy
    bJ :=
      R.bJ
    lC := ?_
    eo := R.eo
    gN := ?_
    bT := ?_
    c1 := ?_ }⟩
  · simpa [τ, nQ] using
      R.lC
  · exact R.gN.trans
      (fb
        Cp).le
  · intro e
    calc
      ab.aO (R.an e) ≤
          aL
              j B R.index *
            ab.aO (initial e) :=
        R.bT e
      _ ≤
          aL
              j B R.index *
            initialBound :=
        Nat.mul_le_mul_left _ (gO e)
      _ =
          bE
            k j initialBound F R.index := by
        rw [eM]
  · intro e
    calc
      ab.aO (R.aQ e) ≤
          aL
              j B (R.index + 1) *
            ab.aO (initial e) :=
        R.c1 e
      _ ≤
          aL
              j B (R.index + 1) *
            initialBound :=
        Nat.mul_le_mul_left _ (gO e)
      _ =
          bE
            k j initialBound F (R.index + 1) := by
        rw [eM]
end av.ag
end
section
namespace av.ag
namespace gx
end gx
noncomputable def f4
    (k r : ℕ)
    (initialBound : Fin (r + 1) → ℕ)
    (F : aF) :
    (j : Fin r) → ℕ → ℝ :=
  fun j =>
    fx
      k j.1 (initialBound j.castSucc) F
noncomputable def gD
    (k r : ℕ)
    (initialBound : Fin (r + 1) → ℕ)
    (F : aF) :
    (j : Fin r) → ℕ → ℕ :=
  fun j =>
    gg
      k j.1 (initialBound j.castSucc) F
noncomputable def gE
    (k r : ℕ) (γ : Fin r → ℝ) :
    Fin r → ℕ :=
  fun j =>
    dU k j.1 (γ j)
noncomputable def c6
    (k r : ℕ)
    (initialBound : Fin (r + 1) → ℕ)
    (F : aF)
    (index : Fin r → ℕ)
    (j : Fin r) : ℕ :=
  bE
    k j.1 (initialBound j.castSucc) F (index j)
noncomputable def k7
    (k r : ℕ)
    (initialBound : Fin (r + 1) → ℕ)
    (F : aF)
    (index : Fin r → ℕ)
    (j : Fin r) : ℕ :=
  bE
    k j.1 (initialBound j.castSucc) F (index j + 1)
noncomputable def eN
    (k r : ℕ)
    (initialBound : Fin (r + 1) → ℕ)
    (F : aF)
    (index : Fin r → ℕ) :
    Fin (r + 1) → ℕ :=
  Fin.lastCases
    (initialBound (Fin.last r))
    (fun j =>
      c6
        k r initialBound F index j)
noncomputable def eh
    (k r : ℕ)
    (initialBound : Fin (r + 1) → ℕ)
    (F : aF)
    (index : Fin r → ℕ) :
    Fin (r + 1) → ℕ :=
  Fin.lastCases
    (initialBound (Fin.last r))
    (fun j =>
      k7
        k r initialBound F index j)
theorem pU
    (k r : ℕ)
    (initialBound : Fin (r + 1) → ℕ)
    (F : aF) :
    ∀ j n,
      0 <
        f4
          k r initialBound F j n := by
  intro j n
  exact jm
    k j.1 (initialBound j.castSucc) F n
theorem qx
    (k r : ℕ)
    (initialBound : Fin (r + 1) → ℕ)
    (F : aF) :
    ∀ j n,
      (Fintype.card
          (al k (j.1 + 1)) : ℝ) <
        (gD
            k r initialBound F j n : ℝ) *
          (f4
            k r initialBound F j n) ^ 2 := by
  intro j n
  exact oo
    k j.1 (initialBound j.castSucc) F n
theorem qS
    (k r : ℕ) (γ : Fin r → ℝ) :
    ∀ j,
      0 <
        gE k r γ j := by
  intro j
  exact h9 k j.1 (γ j)
structure bg
    (G : Type*) [Fintype G] [DecidableEq G]
    (k r : ℕ)
    (initial : aa G k r)
    (initialBound : Fin (r + 1) → ℕ)
    (F : aF)
    (γ : Fin r → ℝ) where
  index : Fin r → ℕ
  an : aa G k r
  aQ : aa G k r
  dy : aQ.db an
  bJ : an.db initial
  da :
    an.bl = initial.bl
  dZ :
    aQ.bl = initial.bl
  fM :
    ∀ j : Fin r,
      index j <
        dU k j.1 (γ j)
  regular :
    il aQ
      (fun j =>
        1 /
          (F (c6
            k r initialBound F index j) : ℝ))
  eo :
    ∀ j : Fin r,
      0 ≤
        aH
            (aQ.partition j.castSucc)
            (aQ.partition j.succ) -
          aH
            (an.partition j.castSucc)
            (aQ.partition j.succ)
  gN :
    ∀ j : Fin r,
      aH
            (aQ.partition j.castSucc)
            (aQ.partition j.succ) -
          aH
            (an.partition j.castSucc)
            (aQ.partition j.succ) ≤
        γ j
  bT :
    ∀ (q : Fin (r + 1)) (e : al k q.1),
      ab.aO
          (an.partition q e) ≤
        eN
          k r initialBound F index q
  c1 :
    ∀ (q : Fin (r + 1)) (e : al k q.1),
      ab.aO
          (aQ.partition q e) ≤
        eh
          k r initialBound F index q
namespace bg
end bg
theorem bg.nonempty
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (initial : aa G k r)
    (initialBound : Fin (r + 1) → ℕ)
    (F : aF)
    (γ : Fin r → ℝ)
    (Cp : ∀ j, 0 < γ j)
    (gO :
      ∀ (q : Fin (r + 1)) (e : al k q.1),
        ab.aO
          (initial.partition q e) ≤ initialBound q) :
    Nonempty
      (bg
        G k r initial initialBound F γ) := by
  let τ : (j : Fin r) → ℕ → ℝ :=
    f4
      k r initialBound F
  let B : (j : Fin r) → ℕ → ℕ :=
    gD
      k r initialBound F
  let L : Fin r → ℕ :=
    gE k r γ
  obtain ⟨R⟩ :=
    bk.nonempty
      initial τ B L
      (fun j n =>
        (pU
          k r initialBound F j n).le)
      (qx
        k r initialBound F)
      (qS k r γ)
  refine ⟨{
    index := R.index
    an := R.an
    aQ := R.aQ
    dy := R.dy
    bJ :=
      R.bJ
    da := R.da
    dZ := R.dZ
    fM := ?_
    regular := ?_
    eo := R.eo
    gN := ?_
    bT := ?_
    c1 := ?_ }⟩
  · intro j
    simpa [L, gE] using
      R.fM j
  · intro j
    have dk := R.regular j
    simpa [τ, f4,
      cR,
      c6,
      nQ] using dk
  · intro j
    exact (R.gN j).trans
      (by
        simpa [L, gE] using
          (fb
            (Cp j)).le)
  · intro q
    cases q using Fin.lastCases with
    | last =>
        intro e
        have m5 := congrFun R.da e
        simp only [aa.bl] at m5
        rw [m5]
        simpa [eN] using
          gO (Fin.last r) e
    | cast i =>
        intro e
        have b8 := R.bT i e
        calc
          ab.aO
              (R.an.partition i.castSucc e) ≤
              aL
                  i.1 (B i) (R.index i) *
                ab.aO
                  (initial.partition i.castSucc e) := by
            simpa [B, gD] using
              b8
          _ ≤
              aL
                  i.1 (B i) (R.index i) *
                initialBound i.castSucc :=
            Nat.mul_le_mul_left _
              (gO i.castSucc e)
          _ =
              eN
                k r initialBound F R.index i.castSucc := by
            simp only [
              eN,
              c6,
              Fin.lastCases_castSucc]
            rw [eM]
            rfl
  · intro q
    cases q using Fin.lastCases with
    | last =>
        intro e
        have m5 := congrFun R.dZ e
        simp only [aa.bl] at m5
        rw [m5]
        simpa [eh] using
          gO (Fin.last r) e
    | cast i =>
        intro e
        have b8 := R.c1 i e
        calc
          ab.aO
              (R.aQ.partition i.castSucc e) ≤
              aL
                  i.1 (B i) (R.index i + 1) *
                ab.aO
                  (initial.partition i.castSucc e) := by
            simpa [B, gD] using
              b8
          _ ≤
              aL
                  i.1 (B i) (R.index i + 1) *
                initialBound i.castSucc :=
            Nat.mul_le_mul_left _
              (gO i.castSucc e)
          _ =
              eh
                k r initialBound F R.index i.castSucc := by
            simp only [
              eh,
              k7,
              Fin.lastCases_castSucc]
            rw [eM]
            rfl
end av.ag
end
section
namespace av.ag
noncomputable def md
    (k j : ℕ) (F : aF) (M : ℕ) : ℕ :=
  (2 ^ (j + 1)) ^
      kv k j F M * M
@[simp]
theorem vf
    (k j initialBound n : ℕ) (F : aF) :
    bE
        k j initialBound F (n + 1) =
      md k j F
        (bE
          k j initialBound F n) :=
  rfl
def kx : (n : ℕ) → (Fin n → ℕ) → ℕ
  | 0, _ => 0
  | n + 1, value =>
      max
        (kx n (fun i => value i.castSucc))
        (value (Fin.last n))
theorem um :
    ∀ {n : ℕ} (value : Fin n → ℕ) (i : Fin n),
      value i ≤ kx n value
  | 0, _, i => Fin.elim0 i
  | n + 1, value, i => by
      cases i using Fin.lastCases with
      | last =>
          rw [kx]
          exact le_max_right _ _
      | cast i =>
          rw [kx]
          exact
            (um
              (fun q => value q.castSucc) i).trans
              (le_max_left _ _)
namespace bg
end bg
end av.ag
end
section
namespace av.ag
noncomputable def b0
    {r : ℕ} (F : aF)
    (scale : Fin (r + 1) → ℕ) : ℝ :=
  1 / (F (scale 0) : ℝ)
noncomputable def fG
    {r : ℕ} (F : aF)
    (scale : Fin (r + 1) → ℕ)
    (j : Fin r) : ℝ :=
  1 / (F (scale j.succ) : ℝ) ^ 2
theorem nk
    {r : ℕ} (F : aF)
    (scale : Fin (r + 1) → ℕ) :
    0 < b0 F scale := by
  unfold b0
  exact one_div_pos.mpr
    (by exact_mod_cast F.positive (scale 0))
def ca
    {k r : ℕ}
    (initialBound : Fin (r + 1) → ℕ)
    {S : aJ k r}
    (P : S.br) :
    Fin (r + 1) → ℕ :=
  Fin.lastCases
    (initialBound (Fin.last r))
    (fun j =>
      aL
          j.1 (P.aG j) (P.index j) *
        initialBound j.castSucc)
structure a4
    (k r : ℕ)
    (initialBound : Fin (r + 1) → ℕ)
    (F : aF)
    (bP : ℕ) where
  lG : aJ k r
  gp : lG.IsAdmissible
  scale : lG.br → Fin (r + 1) → ℕ
  kj :
    ∀ P, bP ≤ scale P (Fin.last r)
  fT :
    ∀ P (j : Fin r),
      F (scale P j.succ) ≤ scale P j.castSucc
  dq :
    ∀ P (j : Fin r),
      P.aR j (P.index j) ≤
        b0 F (scale P)
  i9 :
    ∀ P (j : Fin r),
      (Fintype.card
          (al k (j.1 + 1)) : ℝ) /
            (P.length j : ℝ) ≤
        fG F (scale P) j
  e4 :
    ∀ P q,
      ca initialBound P q ≤
        scale P q
namespace a4
theorem sR
    {k r : ℕ}
    {initialBound : Fin (r + 1) → ℕ}
    {F : aF}
    {bP : ℕ}
    (S : a4
      k r initialBound F bP)
    (P : S.lG.br) :
    Antitone (S.scale P) := by
  rw [Fin.antitone_iff_succ_le]
  intro j
  exact
    (Nat.le_succ _).trans
      ((F.nP (S.scale P j.succ)).trans
        (S.fT P j))
theorem o2
    {k r : ℕ}
    {initialBound : Fin (r + 1) → ℕ}
    {F : aF}
    {bP : ℕ}
    (S : a4
      k r initialBound F bP)
    (P : S.lG.br)
    (q : Fin (r + 1)) :
    bP ≤ S.scale P q := by
  exact (S.kj P).trans
    (S.sR P (Fin.le_last q))
structure iL
    {G : Type*} [Fintype G] [DecidableEq G]
    (k r : ℕ)
    (initial : aa G k r)
    (initialBound : Fin (r + 1) → ℕ)
    (F : aF)
    (bP : ℕ) where
  aR : (j : Fin r) → ℕ → ℝ
  aG : (j : Fin r) → ℕ → ℕ
  length : Fin r → ℕ
  regularity :
    a5
      G k r initial aR aG length
  scale : Fin (r + 1) → ℕ
  o2 : ∀ q, bP ≤ scale q
  fT :
    ∀ j : Fin r,
      F (scale j.succ) ≤ scale j.castSucc
  pw :
    ∀ j : Fin r,
      0 ≤
        cR
          aR regularity.index j
  dq :
    ∀ j : Fin r,
      cR
          aR regularity.index j ≤
        b0 F scale
  uV :
    ∀ j : Fin r,
      regularity.nO.fB j ≤
        fG F scale j
  bT :
    ∀ (q : Fin (r + 1)) (e : al k q.1),
      ab.aO
          (regularity.an.partition q e) ≤
        scale q
theorem oJ
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    {initialBound : Fin (r + 1) → ℕ}
    {F : aF}
    {bP : ℕ}
    (S : a4
      k r initialBound F bP)
    (initial : aa G k r)
    (gO :
      ∀ (q : Fin (r + 1)) (e : al k q.1),
        ab.aO
            (initial.partition q e) ≤
          initialBound q) :
    Nonempty
      (iL k r initial initialBound F bP) := by
  obtain ⟨P, R, rT⟩ :=
    S.lG.o1
      initial S.gp
  refine ⟨{
    aR := P.aR
    aG := P.aG
    length := P.length
    regularity := R
    scale := S.scale P
    o2 := S.o2 P
    fT := S.fT P
    pw := ?_
    dq := ?_
    uV := ?_
    bT := ?_ }⟩
  · intro j
    simp only [cR]
    rw [congrFun rT j]
    exact
      P.uk S.gp
        j (P.index j)
  · intro j
    simpa [cR, rT] using
      S.dq P j
  · intro j
    have ip := R.gN j
    have uW := S.i9 P j
    change
      aH
            (R.aQ.partition j.castSucc)
            (R.an.partition j.succ) -
          aH
            (R.an.partition j.castSucc)
            (R.an.partition j.succ) ≤
        fG F (S.scale P) j
    exact ip.trans uW
  · intro q
    cases q using Fin.lastCases with
    | last =>
        intro e
        have m5 := congrFun R.da e
        simp only [aa.bl] at m5
        rw [m5]
        calc
          ab.aO
                (initial.partition (Fin.last r) e) ≤
              initialBound (Fin.last r) :=
            gO (Fin.last r) e
          _ =
              ca
                initialBound P (Fin.last r) := by
            simp [ca]
          _ ≤ S.scale P (Fin.last r) :=
            S.e4 P (Fin.last r)
    | cast j =>
        intro e
        calc
          ab.aO
                (R.an.partition j.castSucc e) ≤
              aL
                    j.1 (P.aG j) (P.index j) *
                ab.aO
                    (initial.partition j.castSucc e) := by
            rw [← congrFun rT j]
            exact R.bT j e
          _ ≤
              aL
                    j.1 (P.aG j) (P.index j) *
                initialBound j.castSucc :=
            Nat.mul_le_mul_left _
              (gO j.castSucc e)
          _ =
              ca
                initialBound P j.castSucc := by
            simp [ca]
          _ ≤ S.scale P j.castSucc :=
            S.e4 P j.castSucc
def zero
    (k : ℕ)
    (initialBound : Fin 1 → ℕ)
    (F : aF)
    (bP : ℕ) :
    a4
      k 0 initialBound F bP where
  lG := .nil
  gp := trivial
  scale := fun _ _ =>
    max bP (initialBound 0)
  kj := by
    intro P
    exact le_max_left _ _
  fT := by
    intro P j
    exact Fin.elim0 j
  dq := by
    intro P j
    exact Fin.elim0 j
  i9 := by
    intro P j
    exact Fin.elim0 j
  e4 := by
    intro P q
    have hq : q = 0 := Fin.eq_zero q
    subst q
    change initialBound 0 ≤
      max bP (initialBound 0)
    exact le_max_right _ _
def oq
    {k r length : ℕ}
    {aR : ℕ → ℝ}
    {aG : ℕ → ℕ}
    {next : Fin length → aJ k r}
    (a9 : ℕ)
    (ia :
      ∀ i : Fin length,
        (next i).br → Fin (r + 1) → ℕ)
    (P :
      (aJ.node
        aR aG length next).br) :
    Fin (r + 2) → ℕ :=
  match P with
  | .node bW lower =>
      Fin.lastCases a9
        (ia bW lower)
@[simp]
theorem lM
    {k r length : ℕ}
    {aR : ℕ → ℝ}
    {aG : ℕ → ℕ}
    {next : Fin length → aJ k r}
    (a9 : ℕ)
    (ia :
      ∀ i : Fin length,
        (next i).br → Fin (r + 1) → ℕ)
    (bW : Fin length)
    (lower : (next bW).br) :
    oq (aR := aR) (aG := aG)
        a9 ia
        (aJ.br.node
          (aR := aR) (aG := aG)
          bW lower)
        (Fin.last (r + 1)) =
      a9 := by
  simp [oq]
@[simp]
theorem fc
    {k r length : ℕ}
    {aR : ℕ → ℝ}
    {aG : ℕ → ℕ}
    {next : Fin length → aJ k r}
    (a9 : ℕ)
    (ia :
      ∀ i : Fin length,
        (next i).br → Fin (r + 1) → ℕ)
    (bW : Fin length)
    (lower : (next bW).br)
    (q : Fin (r + 1)) :
    oq (aR := aR) (aG := aG)
        a9 ia
        (aJ.br.node
          (aR := aR) (aG := aG)
          bW lower)
        q.castSucc =
      ia bW lower q := by
  simp [oq]
@[simp]
theorem kk
    {k r length : ℕ}
    {aR : ℕ → ℝ}
    {aG : ℕ → ℕ}
    {next : Fin length → aJ k r}
    (F : aF)
    (a9 : ℕ)
    (ia :
      ∀ i : Fin length,
        (next i).br → Fin (r + 1) → ℕ)
    (bW : Fin length)
    (lower : (next bW).br) :
    b0 F
        (oq (aR := aR) (aG := aG)
          a9 ia
          (aJ.br.node
            (aR := aR) (aG := aG)
            bW lower)) =
      b0 F
        (ia bW lower) := by
  unfold b0
  rw [show
    (0 : Fin (r + 2)) =
      (0 : Fin (r + 1)).castSucc by rfl]
  rw [fc]
def gk
    {r : ℕ}
    (initialBound : Fin (r + 2) → ℕ)
    (aG : ℕ → ℕ)
    {length : ℕ}
    (i : Fin length) :
    Fin (r + 1) → ℕ :=
  Fin.lastCases
    (aL r aG i.1 *
      initialBound (Fin.last r).castSucc)
    (fun q => initialBound q.castSucc.castSucc)
def node
    {k r : ℕ}
    {initialBound : Fin (r + 2) → ℕ}
    {F : aF}
    {bP : ℕ}
    (a9 : ℕ)
    (aR : ℕ → ℝ)
    (aG : ℕ → ℕ)
    (length : ℕ)
    (next :
      (i : Fin length) →
        a4
          k r (gk initialBound aG i)
            F (F a9))
    (rS : ∀ n, 0 ≤ aR n)
    (gS :
      ∀ n,
        (Fintype.card
            (al k (r + 1)) : ℝ) <
          (aG n : ℝ) * (aR n) ^ 2)
    (iB : 0 < length)
    (AU : bP ≤ a9)
    (AV :
      initialBound (Fin.last (r + 1)) ≤ a9)
    (zs :
      ∀ (i : Fin length)
          (P : (next i).lG.br),
        aR i.1 ≤
          b0 F ((next i).scale P))
    (DT :
      (Fintype.card
          (al k (r + 1)) : ℝ) /
            (length : ℝ) ≤
        1 / (F a9 : ℝ) ^ 2) :
    a4
      k (r + 1) initialBound F bP where
  lG :=
    .node aR aG length
      (fun i => (next i).lG)
  gp := by
    exact ⟨rS, gS, iB,
      fun i => (next i).gp⟩
  scale :=
    oq a9
      (fun i => (next i).scale)
  kj := by
    intro P
    cases P with
    | node bW lower =>
        simpa only [lM] using
          AU
  fT := by
    intro P j
    cases P with
    | node bW lower =>
        cases j using Fin.lastCases with
        | last =>
            simpa only [Fin.succ_last,
              lM,
              fc] using
              (next bW).kj lower
        | cast q =>
            simpa only [Fin.succ_castSucc,
              fc] using
              (next bW).fT lower q
  dq := by
    intro P j
    cases P with
    | node bW lower =>
        cases j using Fin.lastCases with
        | last =>
            simpa only [
              aJ.br.sB,
              aJ.br.rR,
              kk] using
              zs bW lower
        | cast q =>
            simpa only [
              aJ.br.qk,
              aJ.br.v9,
              kk] using
              (next bW).dq
                lower q
  i9 := by
    intro P j
    cases P with
    | node bW lower =>
        cases j using Fin.lastCases with
        | last =>
            simp only [
              aJ.br.xJ,
              fG, Fin.succ_last,
              lM, Fin.val_last]
            convert DT using 1
        | cast q =>
            simp only [
              aJ.br.vA,
              fG, Fin.succ_castSucc,
              fc,
              Fin.val_castSucc]
            convert
              (next bW).i9 lower q using 1
            · congr 1
  e4 := by
    intro P q
    cases P with
    | node bW lower =>
        cases q using Fin.lastCases with
        | last =>
            simpa [ca,
              lM] using
              AV
        | cast q =>
            cases q using Fin.lastCases with
            | last =>
                simpa [ca,
                  gk,
                  fc] using
                  (next bW).e4
                    lower (Fin.last r)
            | cast j =>
                simpa [ca,
                  gk,
                  fc] using
                  (next bW).e4
                    lower j.castSucc
structure Bounded
    (k r : ℕ)
    (initialBound : Fin (r + 1) → ℕ)
    (F : aF)
    (bP : ℕ) where
  jn :
    a4
      k r initialBound F bP
  ef : ℕ
  kz :
    ∀ P : jn.lG.br,
      jn.scale P 0 ≤ ef
namespace Bounded
def xL
    {k r : ℕ}
    {initialBound rU :
      Fin (r + 1) → ℕ}
    {F : aF}
    {bP : ℕ}
    (S : Bounded k r initialBound F bP)
    (h : initialBound = rU) :
    Bounded k r rU F bP where
  jn := h ▸ S.jn
  ef := S.ef
  kz := by
    subst rU
    exact S.kz
end Bounded
def AW
    (k : ℕ)
    (initialBound : Fin 1 → ℕ)
    (F : aF)
    (bP : ℕ) :
    Bounded k 0 initialBound F bP where
  jn := zero k initialBound F bP
  ef := max bP (initialBound 0)
  kz := by
    intro P
    change
      max bP (initialBound 0) ≤
        max bP (initialBound 0)
    exact le_rfl
def jq
    {r : ℕ}
    (initialBound : Fin (r + 2) → ℕ)
    (factor : ℕ) :
    Fin (r + 1) → ℕ :=
  Fin.lastCases
    (factor * initialBound (Fin.last r).castSucc)
    (fun q => initialBound q.castSucc.castSucc)
noncomputable def fN
    {k r : ℕ}
    (initialBound : Fin (r + 2) → ℕ)
    (F : aF)
    (a9 : ℕ)
    (bm :
      (bound : Fin (r + 1) → ℕ) →
        Bounded k r bound F (F a9)) :
    ℕ → ℕ
  | 0 => 1
  | n + 1 =>
      let previous :=
        fN
          initialBound F a9 bm n
      let lower :=
        bm
          (jq
            initialBound previous)
      let aR :=
        dC
          F lower.ef
      let aG :=
        ey
          k r aR
      (2 ^ (r + 1)) ^ aG * previous
noncomputable def i3
    {k r : ℕ}
    (initialBound : Fin (r + 2) → ℕ)
    (F : aF)
    (a9 : ℕ)
    (bm :
      (bound : Fin (r + 1) → ℕ) →
        Bounded k r bound F (F a9))
    (n : ℕ) :
    Fin (r + 1) → ℕ :=
  jq initialBound
    (fN
      initialBound F a9 bm n)
noncomputable def hl
    {k r : ℕ}
    (initialBound : Fin (r + 2) → ℕ)
    (F : aF)
    (a9 : ℕ)
    (bm :
      (bound : Fin (r + 1) → ℕ) →
        Bounded k r bound F (F a9))
    (n : ℕ) :
    Bounded k r
      (i3
        initialBound F a9 bm n)
      F (F a9) :=
  bm
    (i3
      initialBound F a9 bm n)
noncomputable def i4
    {k r : ℕ}
    (initialBound : Fin (r + 2) → ℕ)
    (F : aF)
    (a9 : ℕ)
    (bm :
      (bound : Fin (r + 1) → ℕ) →
        Bounded k r bound F (F a9))
    (n : ℕ) : ℝ :=
  dC F
    (hl
      initialBound F a9 bm n).ef
noncomputable def ez
    {k r : ℕ}
    (initialBound : Fin (r + 2) → ℕ)
    (F : aF)
    (a9 : ℕ)
    (bm :
      (bound : Fin (r + 1) → ℕ) →
        Bounded k r bound F (F a9))
    (n : ℕ) : ℕ :=
  ey k r
    (i4
      initialBound F a9 bm n)
theorem j9
    {k r : ℕ}
    (initialBound : Fin (r + 2) → ℕ)
    (F : aF)
    (a9 : ℕ)
    (bm :
      (bound : Fin (r + 1) → ℕ) →
        Bounded k r bound F (F a9)) :
    ∀ n,
      aL r
          (ez
            initialBound F a9 bm) n =
        fN
          initialBound F a9 bm n := by
  intro n
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change
        (2 ^ (r + 1)) ^
              ez
                initialBound F a9 bm n *
            aL r
              (ez
                initialBound F a9 bm) n =
          (2 ^ (r + 1)) ^
              ez
                initialBound F a9 bm n *
            fN
              initialBound F a9 bm n
      rw [ih]
theorem o3
    {k r length : ℕ}
    (initialBound : Fin (r + 2) → ℕ)
    (F : aF)
    (a9 : ℕ)
    (bm :
      (bound : Fin (r + 1) → ℕ) →
        Bounded k r bound F (F a9))
    (i : Fin length) :
    gk initialBound
        (ez
          initialBound F a9 bm) i =
      i3
        initialBound F a9 bm i.1 := by
  funext q
  cases q using Fin.lastCases with
  | last =>
      simp [gk, i3,
        jq,
        j9]
  | cast q =>
      simp [gk, i3,
        jq]
noncomputable def sC
    {k r length : ℕ}
    (initialBound : Fin (r + 2) → ℕ)
    (F : aF)
    (a9 : ℕ)
    (bm :
      (bound : Fin (r + 1) → ℕ) →
        Bounded k r bound F (F a9))
    (i : Fin length) :
    Bounded k r
      (gk initialBound
        (ez
          initialBound F a9 bm) i)
      F (F a9) :=
  (hl
      initialBound F a9 bm i.1).xL
    (o3
      initialBound F a9 bm i).symm
@[simp]
theorem tl
    {k r length : ℕ}
    (initialBound : Fin (r + 2) → ℕ)
    (F : aF)
    (a9 : ℕ)
    (bm :
      (bound : Fin (r + 1) → ℕ) →
        Bounded k r bound F (F a9))
    (i : Fin length) :
    (sC
      initialBound F a9 bm i).ef =
      (hl
        initialBound F a9 bm i.1).ef :=
  rfl
theorem nS
    {k r : ℕ}
    (initialBound : Fin (r + 2) → ℕ)
    (F : aF)
    (a9 : ℕ)
    (bm :
      (bound : Fin (r + 1) → ℕ) →
        Bounded k r bound F (F a9))
    (n : ℕ) :
    0 <
      i4
        initialBound F a9 bm n := by
  exact k6 F
    (hl
      initialBound F a9 bm n).ef
theorem uo
    (k r : ℕ)
    (initialBound : Fin (r + 1) → ℕ)
    (F : aF)
    (bP : ℕ) :
    Nonempty
      (Bounded k r initialBound F bP) := by
  induction r generalizing bP with
  | zero =>
      exact
        ⟨AW
          k initialBound F bP⟩
  | succ r ih =>
      let a9 : ℕ :=
        max bP
          (initialBound (Fin.last (r + 1)))
      let Bb : ℝ :=
        1 / (F a9 : ℝ) ^ 2
      let length : ℕ :=
        dU k r Bb
      let bm :
          (bound : Fin (r + 1) → ℕ) →
            Bounded k r bound F (F a9) :=
        fun bound =>
          Classical.choice
            (ih bound (F a9))
      let aR : ℕ → ℝ :=
        i4
          initialBound F a9 bm
      let aG : ℕ → ℕ :=
        ez
          initialBound F a9 bm
      let next :
          (i : Fin length) →
            Bounded k r
              (gk initialBound aG i)
              F (F a9) :=
        fun i =>
          sC
            initialBound F a9 bm i
      have Dg : 0 < Bb := by
        dsimp only [Bb]
        exact one_div_pos.mpr
          (sq_pos_of_pos
            (by exact_mod_cast F.positive a9))
      let jn :
          a4
            k (r + 1) initialBound F bP :=
        node a9 aR aG length
          (fun i => (next i).jn)
          (by
            intro n
            exact
              (nS
                initialBound F a9 bm n).le)
          (by
            intro n
            change
              (Fintype.card
                  (al k (r + 1)) : ℝ) <
                (ez
                    initialBound F a9 bm n : ℝ) *
                  (i4
                    initialBound F a9 bm n) ^ 2
            exact
              kh
                (nS
                  initialBound F a9 bm n))
          (by
            exact h9 k r Bb)
          (by
            exact le_max_left _ _)
          (by
            exact le_max_right _ _)
          (by
            intro i P
            have oT :
                (next i).jn.scale P 0 ≤
                  (hl
                    initialBound F a9
                      bm i.1).ef := by
              exact
                ((next i).kz P).trans_eq
                  (tl
                    initialBound F a9
                      bm i)
            change
              dC F
                    (hl
                      initialBound F a9
                        bm i.1).ef ≤
                b0 F
                  ((next i).jn.scale P)
            unfold dC
              b0
            apply one_div_le_one_div_of_le
            · exact_mod_cast
                F.positive ((next i).jn.scale P 0)
            · exact_mod_cast F.monotone oT)
          (by
            have ip :=
              fb
                (k := k) (j := r) Dg
            exact ip.le)
      let ef : ℕ :=
        kx length
          (fun i => (next i).ef)
      refine ⟨{
        jn := jn
        ef := ef
        kz := ?_ }⟩
      intro P
      cases P with
      | node bW lower =>
          dsimp only [jn, ef, node]
          change
            oq a9
                (fun i => (next i).jn.scale)
                (aJ.br.node
                  bW lower) 0 ≤
              kx length
                (fun i => (next i).ef)
          rw [show
            (0 : Fin (r + 2)) =
              (0 : Fin (r + 1)).castSucc by rfl]
          rw [fc]
          exact
            ((next bW).kz lower).trans
              (um
                (fun i => (next i).ef) bW)
theorem nonempty
    (k r : ℕ)
    (initialBound : Fin (r + 1) → ℕ)
    (F : aF)
    (bP : ℕ) :
    Nonempty
      (a4
        k r initialBound F bP) := by
  obtain ⟨S⟩ :=
    uo
      k r initialBound F bP
  exact ⟨S.jn⟩
end a4
end av.ag
end
section
namespace av.ag
open scoped BigOperators
theorem nT
    (k r : ℕ) :
    (aD k r).order ≤ r := by
  unfold ah.order
  rw [d8]
  apply Finset.sup_le
  intro e he
  exact (ek e).1 he
theorem a4.iL.m8
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : aa G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : aF}
    {bP : ℕ}
    (R : a4.iL
      k r initial initialBound F bP) :
    cu
      R.regularity.nO
      (fun _ => b0 F R.scale) := by
  intro j e a b
  exact
    (R.regularity.lE j e a b).trans
      (R.dq j)
theorem hY
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : ak G k r)
    (A : ai G k r P.an)
    (α β : ℕ → ℝ)
    (sS : α 0 ≤ 1)
    (h5 : A.c5 P α β) :
    ∀ e ∈ aC k r,
      α e.card ≤ bn P A e := by
  intro e he
  by_cases DB : e = ∅
  · subst e
    simpa using sS
  · have Dh : e.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr DB
    have EK : e.card ≤ r :=
      (ek e).1 he
    have rb :=
      (h5 (bB e Dh EK)).1
    have qb :
        (bB e Dh EK).rank = e.card := by
      rw [← b1,
        cE]
    rw [qb] at rb
    simpa [gU,
      bn, Dh, EK] using rb
theorem g4
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : ak G k r)
    (A : ai G k r P.an)
    (α β : ℕ → ℝ) (τ : ℝ)
    (gr : ∀ d, 0 ≤ β d)
    (iQ : 0 ≤ τ)
    (h5 : A.c5 P α β)
    (dk :
      cu P (fun _ => τ)) :
    iZ
      (H := aC k r)
      (ar A)
      (bn P A)
      β τ := by
  apply ah.mS
      P A β τ gr iQ
  · exact
      ah.g9
        P A α β h5
  · exact
      ah.ja
        P A τ dk
        (ah.kt
          P A)
theorem ib
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : ak G k r)
    (A : ai G k r P.an)
    (α β μ : ℕ → ℝ) (τ : ℝ)
    (E : ℕ → ℕ → ℝ)
    (sS : α 0 ≤ 1)
    (gr : ∀ d, 0 ≤ β d)
    (iQ : 0 ≤ τ)
    (h5 : A.c5 P α β)
    (dk :
      cu P (fun _ => τ))
    (k8 : cX α β μ τ E)
    {K : Type} [Fintype K] [DecidableEq K]
    (B : ah (Fin k) K
      (aC k r))
    (dv : B.a6) :
    |B.a7
          (B.ao
            (ar A)) -
        B.a0
          (bn P A)| ≤
      E B.order B.edges.card *
        B.a0
          (bn P A) := by
  exact
    @jl
      (Fin k) G inferInstance inferInstance
      (aC k r) inferInstance
      (ar A)
      (bn P A)
      α β μ τ E
      (dF A)
      (fW A)
      (fk A)
      (gy P A)
      (hY
        P A α β sS h5)
      (g4
        P A α β τ gr iQ h5 dk)
      k8 K inferInstance inferInstance B dv
theorem g0
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : ak G k r)
    (A : ai G k r P.an)
    (α β μ : ℕ → ℝ) (τ : ℝ)
    (E : ℕ → ℕ → ℝ)
    (sS : α 0 ≤ 1)
    (gr : ∀ d, 0 ≤ β d)
    (iQ : 0 ≤ τ)
    (h5 : A.c5 P α β)
    (dk :
      cu P (fun _ => τ))
    (k8 : cX α β μ τ E) :
    (1 - E
          (aD k r).order
          (aD k r).edges.card) *
        (∏ e : aj k r,
          bq P A e) ≤
      c9 A := by
  have i1 :=
    ib
      P A α β μ τ E sS gr iQ h5 dk k8
      (aD k r)
      (oG k r)
  rw [mO A,
    kJ P A] at i1
  have rE :
      - (E
          (aD k r).order
          (aD k r).edges.card *
            (∏ e : aj k r,
              bq P A e)) ≤
        c9 A -
          (∏ e : aj k r,
            bq P A e) :=
    neg_le_of_abs_le i1
  linarith
theorem ka
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : ak G k r)
    (A : ai G k r P.an)
    (α β μ : ℕ → ℝ) (τ : ℝ)
    (E : ℕ → ℕ → ℝ)
    (fX : ∀ d, 0 < α d)
    (Ag : ∀ d, α d ≤ 1)
    (gr : ∀ d, 0 ≤ β d)
    (iQ : 0 ≤ τ)
    (h5 : A.c5 P α β)
    (dk :
      cu P (fun _ => τ))
    (k8 : cX α β μ τ E)
    (vb :
      E
          (aD k r).order
          (aD k r).edges.card <
        1 / 2) :
    (1 / 2 : ℝ) *
        (∏ e : aj k r, α e.rank) ≤
      c9 A := by
  have rE :=
    g0
      P A α β μ τ E (Ag 0) gr iQ h5 dk k8
  have vF :
      0 ≤ ∏ e : aj k r, α e.rank := by
    exact Finset.prod_nonneg fun e _ => (fX e.rank).le
  have yp :
      (∏ e : aj k r, α e.rank) ≤
        ∏ e : aj k r,
          bq P A e := by
    apply Finset.prod_le_prod
    · intro e _he
      exact (fX e.rank).le
    · intro e _he
      simpa [gU] using (h5 e).1
  have Bz :
      (1 / 2 : ℝ) ≤
        1 - E
          (aD k r).order
          (aD k r).edges.card := by
    linarith
  have AX :
      0 ≤
        1 - E
          (aD k r).order
          (aD k r).edges.card := by
    linarith
  calc
    (1 / 2 : ℝ) *
          (∏ e : aj k r, α e.rank) ≤
        (1 - E
            (aD k r).order
            (aD k r).edges.card) *
          (∏ e : aj k r, α e.rank) :=
      mul_le_mul_of_nonneg_right Bz vF
    _ ≤
        (1 - E
            (aD k r).order
            (aD k r).edges.card) *
          (∏ e : aj k r,
            bq P A e) := by
      exact mul_le_mul_of_nonneg_left yp AX
    _ ≤ c9 A :=
      rE
theorem hZ
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : ak G k r)
    (A : ai G k r P.an)
    (α β μ : ℕ → ℝ) (τ : ℝ)
    (E : ℕ → ℕ → ℝ)
    (fX : ∀ d, 0 < α d)
    (Ag : ∀ d, α d ≤ 1)
    (gr : ∀ d, 0 ≤ β d)
    (iQ : 0 ≤ τ)
    (h5 : A.c5 P α β)
    (dk :
      cu P (fun _ => τ))
    (k8 : cX α β μ τ E)
    (vb :
      E r (aD k r).edges.card <
        1 / 2) :
    (1 / 2 : ℝ) *
        (∏ e : aj k r, α e.rank) ≤
      c9 A := by
  apply
    ka
      P A α β μ τ E fX Ag gr iQ h5 dk k8
  exact
    (k8.q0
      (nT k r)).trans_lt
      vb
end av.ag
end
section
namespace av.ag
open scoped BigOperators
namespace ak
noncomputable def c2
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : ak G k r)
    (e : aj k r)
    (upper : ab (Fin (e.ay.1 + 1) → G))
    (a : upper.parts)
    (x : Fin (e.ay.1 + 1) → G) : ℝ :=
  iY
    (au
      (aV P.aQ e) e.face)
    (au
      (aV P.an e) e.face)
    upper a x
theorem sg
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : ak G k r)
    (e : aj k r)
    (upper : ab (Fin (e.ay.1 + 1) → G))
    (a : upper.parts)
    (x : Fin (e.ay.1 + 1) → G) :
    0 ≤ P.c2 e upper a x := by
  exact ti _ _ upper a x
noncomputable def dG
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : ak G k r)
    (e : aj k r)
    (upper : ab (Fin (e.ay.1 + 1) → G))
    (a : upper.parts) (β : ℝ) :
    Finset (Fin (e.ay.1 + 1) → G) :=
  fZ
    (aY P.an e)
    (P.c2 e upper a) β
@[simp]
theorem j1
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : ak G k r)
    (e : aj k r)
    (upper : ab (Fin (e.ay.1 + 1) → G))
    (a : upper.parts) (β : ℝ)
    (x : Fin (e.ay.1 + 1) → G) :
    x ∈ P.dG e upper a β ↔
      β <
        aq
          (aY P.an e)
          (P.c2 e upper a) x := by
  exact
    jU
      (aY P.an e)
      (P.c2 e upper a) β x
theorem j2
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : ak G k r)
    (e : aj k r)
    (upper : ab (Fin (e.ay.1 + 1) → G))
    (a : upper.parts)
    {β : ℝ} (gr : 0 ≤ β) :
    β * mean (aN
        (P.dG e upper a β)) ≤
      mean (P.c2 e upper a) := by
  exact
    mJ
      (aY P.an e)
      (P.c2 e upper a)
      (P.sg e upper a)
      gr
theorem kX
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : ak G k r)
    (e : aj k r)
    (upper : ab (Fin (e.ay.1 + 1) → G))
    (a : upper.parts)
    {β : ℝ} (gr : 0 < β) :
    mean (aN
        (P.dG e upper a β)) ≤
      mean (P.c2 e upper a) / β := by
  apply (le_div_iff₀ gr).2
  simpa [mul_comm] using
    P.j2
      e upper a gr.le
theorem jz
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : ak G k r)
    (e : aj k r)
    (upper : ab (Fin (e.ay.1 + 1) → G)) :
    bI
          (aV P.aQ e) e.face upper -
        bI
          (aV P.an e) e.face upper =
      ∑ a : upper.parts,
        mean (P.c2 e upper a) := by
  rw [pP
    (aQ := aV P.aQ e)
    (an := aV P.an e)
    (fun f => P.dy e.ay.castSucc f)
    e.face upper]
  rfl
noncomputable def cA
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : ak G k r)
    (e : aj k r)
    (upper : ab (Fin (e.ay.1 + 1) → G))
    (a : upper.parts) (α β : ℝ) :
    Finset (Fin (e.ay.1 + 1) → G) :=
  cO
      (au
        (aV P.an e) e.face)
      (aB upper a) α ∪
    P.dG e upper a β
@[simp]
theorem xM
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : ak G k r)
    (e : aj k r)
    (upper : ab (Fin (e.ay.1 + 1) → G))
    (a : upper.parts) (α β : ℝ)
    (x : Fin (e.ay.1 + 1) → G) :
    x ∈ P.cA e upper a α β ↔
      aq
          (au
            (aV P.an e) e.face)
          (aB upper a) x < α ∨
        β <
          aq
            (aY P.an e)
            (P.c2 e upper a) x := by
  rw [cA, Finset.mem_union,
    jT,
    P.j1]
theorem jv
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : ak G k r)
    (e : aj k r)
    (upper : ab (Fin (e.ay.1 + 1) → G))
    (a : upper.parts)
    {α β : ℝ} (fX : 0 ≤ α) (gr : 0 < β) :
    mean (aN
        (a.1 ∩ P.cA
          e upper a α β)) ≤
      α + mean (P.c2 e upper a) / β := by
  calc
    mean (aN
        (a.1 ∩ P.cA
          e upper a α β)) ≤
        mean (aN
          (a.1 ∩
            cO
              (au
                (aV P.an e) e.face)
              (aB upper a) α)) +
          mean (aN
            (P.dG
              e upper a β)) := by
      exact
        qN
          a.1
          (cO
            (au
              (aV P.an e) e.face)
            (aB upper a) α)
          (P.dG e upper a β)
    _ ≤
        α + mean (P.c2 e upper a) / β :=
      add_le_add
        (lP
          (au
            (aV P.an e) e.face)
          a.1 fX)
        (P.kX
          e upper a gr)
noncomputable def er
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : ak G k r)
    (e : aj k r)
    (upper : ab (Fin (e.ay.1 + 1) → G))
    (α β : ℝ) :
    Finset (Fin (e.ay.1 + 1) → G) := by
  classical
  exact
    (Finset.univ : Finset upper.parts).biUnion fun a =>
      a.1 ∩ P.cA e upper a α β
@[simp]
theorem qf
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : ak G k r)
    (e : aj k r)
    (upper : ab (Fin (e.ay.1 + 1) → G))
    (α β : ℝ) (x : Fin (e.ay.1 + 1) → G) :
    x ∈ P.er e upper α β ↔
      x ∈ P.cA e upper
        (bx upper x) α β := by
  classical
  constructor
  · intro hx
    rw [er] at hx
    obtain ⟨a, _ha, wG⟩ :=
      Finset.mem_biUnion.mp hx
    have Ce : x ∈ a.1 :=
      (Finset.mem_inter.mp wG).1
    have ug :
        x ∈ P.cA
          e upper a α β :=
      (Finset.mem_inter.mp wG).2
    have iX : bx upper x = a :=
      (d6 upper x a).2 Ce
    simpa [iX] using ug
  · intro ug
    rw [er]
    apply Finset.mem_biUnion.mpr
    refine ⟨bx upper x, Finset.mem_univ _, ?_⟩
    exact Finset.mem_inter.mpr
      ⟨upper.mem_part (Finset.mem_univ x), ug⟩
theorem ln
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : ak G k r)
    (e : aj k r)
    (upper : ab (Fin (e.ay.1 + 1) → G))
    {α β : ℝ} (fX : 0 ≤ α) (gr : 0 < β) :
    mean (aN
        (P.er
          e upper α β)) ≤
      (ab.aO upper : ℝ) * α +
        (bI
            (aV P.aQ e) e.face upper -
          bI
            (aV P.an e) e.face upper) / β := by
  calc
    mean (aN
        (P.er
          e upper α β)) ≤
        ∑ a : upper.parts,
          mean (aN
            (a.1 ∩ P.cA
              e upper a α β)) := by
      exact
        ke
          (Finset.univ : Finset upper.parts)
          (fun a =>
            a.1 ∩ P.cA
              e upper a α β)
    _ ≤
        ∑ a : upper.parts,
          (α + mean
            (P.c2 e upper a) / β) := by
      apply Finset.sum_le_sum
      intro a _ha
      exact
        P.jv
          e upper a fX gr
    _ =
        (ab.aO upper : ℝ) * α +
          (bI
              (aV P.aQ e) e.face upper -
            bI
              (aV P.an e) e.face upper) / β := by
      rw [Finset.sum_add_distrib, ← Finset.sum_div]
      simp only [Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul]
      rw [Fintype.card_coe]
      rw [← P.jz
        e upper]
      rfl
noncomputable def cv
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : ak G k r)
    (e : aj k r)
    (α β : ℝ) :
    Finset (Fin (e.ay.1 + 1) → G) :=
  P.er e
    (P.an.partition e.ay.succ e.face) α β
@[simp]
theorem n5
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : ak G k r)
    (e : aj k r)
    (α β : ℝ) (x : Fin (e.ay.1 + 1) → G) :
    x ∈ P.cv e α β ↔
      x ∈ P.cA e
        (P.an.partition e.ay.succ e.face)
        (bx
          (P.an.partition e.ay.succ e.face) x)
        α β := by
  exact
    P.qf e
      (P.an.partition e.ay.succ e.face) α β x
theorem jK
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : ak G k r)
    (e : aj k r)
    {α β : ℝ} (fX : 0 ≤ α) (gr : 0 < β) :
    mean (aN
        (P.cv e α β)) ≤
      (ab.aO
          (P.an.partition e.ay.succ e.face) : ℝ) * α +
        P.cz
          e.ay e.face / β := by
  unfold cv
    cz
  exact
    P.ln
      e (P.an.partition e.ay.succ e.face) fX gr
end ak
theorem jw
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : ak G k r)
    (A : ai G k r P.an)
    (e : aj k r)
    (y : Fin (e.ay.1 + 1) → G)
    (hy :
      y ∈
        (aY P.an e).part
          (aI e.face A.witness)) :
    e3 P A e y =
      eK
        (aV P.aQ e)
        (aV P.an e)
        e.face
        (P.an.partition e.ay.succ e.face)
        (A.atom e.ay.succ e.face) y := by
  have BA :
      y ∈
        (au
          (aV P.an e) e.face).part
          (aI e.face A.witness) :=
    ab.gj
      (mb
        P.an e)
      (aI e.face A.witness) hy
  have BB :
      dS P A e y = 1 := by
    unfold dS
    exact dg _ _ BA
  have h :=
    l9 P A e y
  rw [BB, mul_one, mul_one] at h
  simpa [e3] using h
theorem nw
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : ak G k r)
    (A : ai G k r P.an)
    (e : aj k r) :
    aq
        (aY P.an e)
        (fun y => e3 P A e y ^ 2)
        (aI e.face A.witness) =
      aq
        (aY P.an e)
        (P.c2 e
          (P.an.partition e.ay.succ e.face)
          (A.atom e.ay.succ e.face))
        (aI e.face A.witness) := by
  unfold aq
  apply Finset.expect_congr rfl
  intro y hy
  rw [jw
    P A e y hy]
  rfl
namespace ai
def uq
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : ak G k r)
    (A : ai G k r P.an)
    (α β : ℕ → ℝ) : Prop :=
  ∀ e : aj k r,
    aI e.face A.witness ∉
      P.cv e
        (α e.rank) (β e.rank)
theorem m9
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : ak G k r)
    (A : ai G k r P.an)
    (e : aj k r)
    (α β : ℝ)
    (wN :
      aI e.face A.witness ∉
        P.cv e α β) :
    iE P A e α β := by
  let upper :=
    P.an.partition e.ay.succ e.face
  let a : upper.parts :=
    A.atom e.ay.succ e.face
  let x : Fin (e.ay.1 + 1) → G :=
    aI e.face A.witness
  have iX :
      bx upper x = a := by
    exact (A.jo
      e.ay.succ e.face).symm
  have yl :
      x ∉ P.cA
        e upper a α β := by
    intro ug
    apply wN
    apply
      (P.n5
        e α β x).2
    change
      x ∈ P.cA
        e upper (bx upper x) α β
    rw [iX]
    exact ug
  have Di :
      x ∉
        cO
          (au
            (aV P.an e) e.face)
          (aB upper a) α := by
    intro h
    exact yl (Finset.mem_union_left _ h)
  have EL :
      x ∉
        P.dG
          e upper a β := by
    intro h
    exact yl (Finset.mem_union_right _ h)
  constructor
  · have rb :
        α ≤
          aq
            (au
              (aV P.an e) e.face)
            (aB upper a) x :=
      not_lt.mp fun h =>
        Di
          ((jT
            (au
              (aV P.an e) e.face)
            (aB upper a) α x).2 h)
    simpa [gU,
      bq, upper, a, x,
      eJ] using rb
  · rw [nw P A e]
    have lf :
        aq
            (aY P.an e)
            (P.c2 e upper a) x ≤
          β :=
      not_lt.mp fun h =>
        EL
          ((P.j1
            e upper a β x).2 h)
    simpa [upper, a, x] using lf
theorem oK
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : ak G k r)
    (A : ai G k r P.an)
    (α β : ℕ → ℝ)
    (wN : A.uq P α β) :
    A.c5 P α β := by
  intro e
  exact
    A.m9
      P e (α e.rank) (β e.rank) (wN e)
end ai
end av.ag
end
section
namespace av.ag
noncomputable def a2.edgeFinset
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} (H : a2 G k r)
    (e : al k r) : Finset (Fin r → G) := by
  classical
  exact Finset.univ.filter (H.edge e)
@[simp]
theorem a2.mem_edgeFinset
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} (H : a2 G k r)
    (e : al k r) (y : Fin r → G) :
    y ∈ H.edgeFinset e ↔ H.edge e y := by
  simp [a2.edgeFinset]
noncomputable def cB
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} (H : a2 G k r) :
    af G k r := by
  classical
  exact fun e =>
    ab.generatedBy ({H.edgeFinset e} :
      Finset (Finset (Fin r → G)))
theorem na
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} (H : a2 G k r)
    (e : al k r) :
    ab.aO
        (cB H e) ≤ 2 := by
  simpa [cB] using
    ab.pq
      ({H.edgeFinset e} :
        Finset (Finset (Fin r → G)))
theorem nx
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {P : ab Ω} {S : Finset Ω}
    (hP : P ≤ ab.generatedBy
      ({S} : Finset (Finset Ω)))
    {x y : Ω} (hx : x ∈ S) (hy : y ∈ P.part x) :
    y ∈ S := by
  have AY :
      y ∈
        (ab.generatedBy
          ({S} : Finset (Finset Ω))).part x :=
    ab.gj hP x hy
  have ox :=
    (ab.fI
      ({S} : Finset (Finset Ω)) x y).1 AY
  exact (ox S (by simp)).1 hx
theorem n6
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} (H : a2 G k r)
    {P : af G k r}
    (hP : aP P
      (cB H))
    (e : al k r) {x y : Fin r → G}
    (hx : H.edge e x) (hy : y ∈ (P e).part x) :
    H.edge e y := by
  rw [← H.mem_edgeFinset e y]
  exact
    nx
      (hP e)
      ((H.mem_edgeFinset e x).2 hx) hy
def k9
    (G : Type*) [Fintype G] [DecidableEq G]
    (k r : ℕ) : aa G k r where
  partition _ _ := ab.indiscrete
noncomputable def dO
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} (H : a2 G k r) :
    aa G k r :=
  (k9 G k r).bb
    (cB H)
@[simp]
theorem jF
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} (H : a2 G k r) :
    (dO H).bl =
      cB H := by
  exact aa.eY _ _
theorem iI
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} (H : a2 G k r)
    {C : aa G k r}
    (hC : C.db (dO H)) :
    aP C.bl
      (cB H) := by
  intro e
  change
    C.partition (Fin.last r) e ≤
      cB H e
  rw [← jF H]
  exact hC (Fin.last r) e
theorem ai.wa
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} (H : a2 G k r)
    {C : aa G k r}
    (hC : aP C.bl
      (cB H))
    (A : ai G k r C)
    (hA : H.fj A.witness)
    (e : al k r) (y : Fin r → G)
    (hy : y ∈ (A.atom (Fin.last r) e).1) :
    H.edge e y := by
  apply
    n6
      H hC e (hA e)
  have hw :
      aI e A.witness ∈
        (A.atom (Fin.last r) e).1 :=
    A.xA (Fin.last r) e
  have x5 :
      (C.bl e).part
          (aI e A.witness) =
        (A.atom (Fin.last r) e).1 := by
    exact
      (C.bl e).part_eq_of_mem
        (A.atom (Fin.last r) e).2 hw
  rwa [x5]
theorem ai.sT
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} (H : a2 G k r)
    {C : aa G k r}
    (hC : aP C.bl
      (cB H))
    (A : ai G k r C)
    (hA : H.fj A.witness)
    (x : Fin k → G)
    (hx :
      ∀ e : al k r,
        aI e x ∈
          (A.atom (Fin.last r) e).1) :
    H.fj x := by
  intro e
  exact A.wa H hC hA e
    (aI e x) (hx e)
end av.ag
end
section
namespace av.ag
def nb
    {k n : ℕ} (e : al k (n + 1)) :
    aj k (n + 1) where
  ay := Fin.last n
  face := e
theorem jx
    {G : Type*} [Fintype G] [DecidableEq G]
    {k n : ℕ}
    (H : a2 G k (n + 1))
    {C : aa G k (n + 1)}
    (hC : aP C.bl
      (cB H))
    (A : ai G k (n + 1) C)
    (hA : H.fj A.witness)
    {x : Fin k → G} (hx : ¬H.fj x) :
    bV A Finset.univ x = 0 := by
  have xH :
      ∃ e : al k (n + 1),
        aI e x ∉
          (A.atom (Fin.last (n + 1)) e).1 := by
    by_contra h
    push Not at h
    exact hx
      (A.sT
        H hC hA x h)
  obtain ⟨e, he⟩ := xH
  unfold bV
  apply Finset.prod_eq_zero
    (Finset.mem_univ (nb e))
  unfold bX
  change
    aB
        (C.partition (Fin.last (n + 1)) e)
        (A.atom (Fin.last (n + 1)) e)
        (aI e x) =
      0
  exact
    c0
      (C.partition (Fin.last (n + 1)) e)
      (A.atom (Fin.last (n + 1)) e) he
theorem lH
    {G : Type*} [Fintype G] [DecidableEq G]
    {k n : ℕ}
    (H : a2 G k (n + 1))
    {C : aa G k (n + 1)}
    (hC : aP C.bl
      (cB H))
    (A : ai G k (n + 1) C)
    (hA : H.fj A.witness)
    (x : Fin k → G) :
    bV A Finset.univ x ≤
      H.cD.ko x := by
  by_cases hx : H.fj x
  · rw [H.jt hx]
    exact qP
      A Finset.univ x
  · rw [H.iw hx,
      jx
        H hC A hA hx]
theorem pj
    {G : Type*} [Fintype G] [DecidableEq G]
    {k n : ℕ}
    (H : a2 G k (n + 1))
    {C : aa G k (n + 1)}
    (hC : aP C.bl
      (cB H))
    (A : ai G k (n + 1) C)
    (hA : H.fj A.witness) :
    c9 A ≤
      H.cD.gJ := by
  unfold c9 fw
    bQ.gJ
  exact mm
    (lH
      H hC A hA)
end av.ag
end
section
namespace av.ag
open scoped BigOperators
namespace ak
noncomputable def eT
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : ak G k r)
    (e : al k r)
    (α β : ℕ → ℝ) :
    Finset (Fin r → G) := by
  classical
  exact
    (Finset.univ :
      Finset (ct r)).biUnion fun q =>
      eL q.2
        (P.cv
          ({ ay := q.1
             face := q.2.trans e } : aj k r)
          (α (q.1.1 + 1))
          (β (q.1.1 + 1)))
noncomputable def e7
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : ak G k r)
    (α β : ℕ → ℝ) :
    a2.bj (G := G) k r :=
  fun e => P.eT e α β
theorem mf
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : ak G k r)
    (e : al k r)
    (α β : ℕ → ℝ)
    (fX : ∀ j, 0 ≤ α (j + 1))
    (gr : ∀ j, 0 < β (j + 1)) :
    mean (aN
        (P.eT e α β)) ≤
      ∑ q : ct r,
        ((ab.aO
            (P.an.partition q.1.succ
              (q.2.trans e)) : ℝ) *
            α (q.1.1 + 1) +
          P.cz
              q.1 (q.2.trans e) /
            β (q.1.1 + 1)) := by
  calc
    mean (aN
        (P.eT e α β)) ≤
        ∑ q : ct r,
          mean (aN
            (eL q.2
              (P.cv
                ({ ay := q.1
                   face := q.2.trans e } :
                  aj k r)
                (α (q.1.1 + 1))
                (β (q.1.1 + 1))))) := by
      exact
        ke
          (Finset.univ : Finset (ct r))
          (fun q =>
            eL q.2
              (P.cv
                ({ ay := q.1
                   face := q.2.trans e } :
                  aj k r)
                (α (q.1.1 + 1))
                (β (q.1.1 + 1))))
    _ ≤
        ∑ q : ct r,
          ((ab.aO
              (P.an.partition q.1.succ
                (q.2.trans e)) : ℝ) *
              α (q.1.1 + 1) +
            P.cz
                q.1 (q.2.trans e) /
              β (q.1.1 + 1)) := by
      apply Finset.sum_le_sum
      intro q _hq
      rw [oF]
      exact
        P.jK
          ({ ay := q.1
             face := q.2.trans e } : aj k r)
          (fX q.1.1) (gr q.1.1)
theorem j3
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : ak G k r)
    (α β : ℕ → ℝ)
    (fX : ∀ j, 0 ≤ α (j + 1))
    (gr : ∀ j, 0 < β (j + 1))
    (e : al k r) :
    a2.eB
        (P.e7 α β) e ≤
      ∑ q : ct r,
        ((ab.aO
            (P.an.partition q.1.succ
              (q.2.trans e)) : ℝ) *
            α (q.1.1 + 1) +
          P.cz
              q.1 (q.2.trans e) /
            β (q.1.1 + 1)) := by
  rw [show
      a2.eB
          (P.e7 α β) e =
        mean (aN
          (P.eT e α β)) by
    unfold a2.eB
      e7
    rw [iM]]
  exact
    P.mf
      e α β fX gr
end ak
namespace ai
theorem i5
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} (Cf : r ≤ k)
    (P : ak G k r)
    (x : Fin k → G) (α β : ℕ → ℝ)
    (wN :
      ∀ e : al k r,
        aI e x ∉
          P.eT e α β) :
    (ai.yL
      P.an x).c5 P α β := by
  apply
    (ai.yL
      P.an x).oK
      P α β
  intro f ug
  obtain ⟨e, d, G5⟩ :=
    qO
      (Nat.succ_le_iff.mpr f.ay.2) Cf f.face
  apply wN e
  rw [ak.eT]
  apply Finset.mem_biUnion.mpr
  refine ⟨⟨f.ay, d⟩, Finset.mem_univ _, ?_⟩
  rw [ji]
  change
    aI (d.trans e) x ∈
      P.cv
        ({ ay := f.ay
           face := d.trans e } : aj k r)
        (α (f.ay.1 + 1))
        (β (f.ay.1 + 1))
  rw [G5]
  exact ug
end ai
theorem g5
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k n : ℕ} (Cf : n + 1 ≤ k)
    (H : a2 G k (n + 1))
    (P : ak G k (n + 1))
    (gO :
      P.an.db (dO H))
    (α β : ℕ → ℝ) (c : ℝ)
    (i1 : H.cD.gJ < c)
    (vG :
      ∀ A : ai
          G k (n + 1) P.an,
        A.c5 P α β →
          c ≤ c9 A) :
    H.IsCover
      (P.e7 α β) := by
  intro x hx
  by_contra zd
  push Not at zd
  let A :
      ai
        G k (n + 1) P.an :=
    ai.yL P.an x
  have h5 : A.c5 P α β := by
    exact
      ai.i5
        Cf P x α β zd
  have Hu : c ≤ c9 A :=
    vG A h5
  have m5 :
      aP P.an.bl
        (cB H) :=
    iI
      H gO
  have Hv :
      c9 A ≤
        H.cD.gJ :=
    pj
      H m5 A ((H.kR x).1 hx)
  linarith
end av.ag
end
section
namespace av.ag
open scoped BigOperators
noncomputable def bz (δ : ℝ) (m : ℕ) : ℝ :=
  δ / (m + 1 : ℕ)
noncomputable def ch
    (δ η : ℝ) (N m : ℕ) : ℝ :=
  η * bz δ m ^ N
theorem g1
    {δ : ℝ} (fD : 0 < δ) (m : ℕ) :
    0 < bz δ m := by
  unfold bz
  positivity
theorem o4
    {δ : ℝ} (fD : 0 ≤ δ) (m : ℕ) :
    0 ≤ bz δ m := by
  unfold bz
  positivity
theorem o5
    {δ : ℝ} (fD : δ ≤ 1) (F1 : 0 ≤ δ) (m : ℕ) :
    bz δ m ≤ 1 := by
  unfold bz
  have ur : (1 : ℝ) ≤ (m + 1 : ℕ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
  exact (div_le_self F1 ur).trans fD
theorem nU
    {δ : ℝ} (fD : 0 ≤ δ) :
    Antitone (bz δ) := by
  intro a b hab
  unfold bz
  apply div_le_div_of_nonneg_left fD
  · positivity
  · exact_mod_cast Nat.add_le_add_right hab 1
theorem tJ
    {δ : ℝ} (fD : 0 ≤ δ) (m : ℕ) :
    (m : ℝ) * bz δ m ≤ δ := by
  unfold bz
  have ur : (0 : ℝ) < (m + 1 : ℕ) := by positivity
  calc
    (m : ℝ) * (δ / (m + 1 : ℕ)) =
        δ * ((m : ℝ) / (m + 1 : ℕ)) := by ring
    _ ≤ δ * 1 := by
      apply mul_le_mul_of_nonneg_left _ fD
      exact (div_le_one ur).2 (by norm_num)
    _ = δ := mul_one δ
theorem os
    {δ η : ℝ} (fD : 0 < δ) (hη : 0 < η)
    (N m : ℕ) :
    0 < ch δ η N m := by
  unfold ch
  exact mul_pos hη (pow_pos (g1 fD m) N)
theorem rV
    {δ η : ℝ} (fD : 0 ≤ δ) (hη : 0 ≤ η)
    (N m : ℕ) :
    0 ≤ ch δ η N m := by
  unfold ch
  exact mul_nonneg hη
    (pow_nonneg (o4 fD m) N)
def ei
    {r : ℕ} (scale : Fin (r + 1) → ℕ) (d : ℕ) : ℕ :=
  scale ⟨min d r, Nat.lt_succ_iff.mpr (Nat.min_le_right d r)⟩
@[simp]
theorem rW
    {r : ℕ} (scale : Fin (r + 1) → ℕ) :
    ei scale 0 = scale 0 := by
  simp [ei]
theorem rx
    {r d : ℕ} (scale : Fin (r + 1) → ℕ) (hd : d ≤ r) :
    ei scale d =
      scale ⟨d, Nat.lt_succ_iff.mpr hd⟩ := by
  simp [ei, Nat.min_eq_left hd]
noncomputable def bY
    {r : ℕ} (δ : ℝ) (scale : Fin (r + 1) → ℕ) (d : ℕ) : ℝ :=
  bz δ (ei scale d)
noncomputable def dE
    {r : ℕ} (δ κ : ℝ) (N : ℕ)
    (scale : Fin (r + 1) → ℕ) (d : ℕ) : ℝ :=
  ch δ κ N
      (ei scale d) ^ 2
theorem l3
    {r : ℕ} {δ : ℝ} (fD : 0 < δ)
    (scale : Fin (r + 1) → ℕ) (d : ℕ) :
    0 < bY δ scale d :=
  g1 fD _
theorem kL
    {r : ℕ} {δ : ℝ} (fD : 0 ≤ δ) (mj : δ ≤ 1)
    (scale : Fin (r + 1) → ℕ) (d : ℕ) :
    bY δ scale d ≤ 1 :=
  o5 mj fD _
theorem la
    {r : ℕ} (δ κ : ℝ) (N : ℕ)
    (scale : Fin (r + 1) → ℕ) (d : ℕ) :
    0 ≤ dE δ κ N scale d :=
  sq_nonneg _
theorem qg
    {r : ℕ} {δ : ℝ} (fD : 0 ≤ δ)
    {scale : Fin (r + 1) → ℕ} (oT : Antitone scale)
    (d : ℕ) :
    bY δ scale 0 ≤
      bY δ scale d := by
  apply nU fD
  exact oT (Fin.zero_le _)
theorem oL
    {α : ℕ → ℝ} (fX : ∀ d, α 0 ≤ α d) :
    ∀ d, α 0 ≤ bh α d := by
  intro d
  induction d with
  | zero => exact le_rfl
  | succ d ih =>
      rw [lX]
      exact le_min ih (fX (d + 1))
def bw (Q N : ℕ) : aF where
  toFun m := Q * (m + 1) ^ N + (m + 1)
  monotone' := by
    intro a b hab
    apply Nat.add_le_add
    · exact Nat.mul_le_mul_left Q
        (Nat.pow_le_pow_left (Nat.add_le_add_right hab 1) N)
    · exact Nat.add_le_add_right hab 1
  nP := by
    intro m
    exact (Nat.le_add_left (m + 1) (Q * (m + 1) ^ N))
@[simp]
theorem ry
    (Q N m : ℕ) :
    bw Q N m =
      Q * (m + 1) ^ N + (m + 1) :=
  rfl
theorem jd
    (Q N m : ℕ) :
    Q * (m + 1) ^ N ≤ bw Q N m := by
  rw [ry]
  exact Nat.le_add_right _ _
structure fy
    (δ η : ℝ) (N Q : ℕ) : Prop where
  uniform :
    1 ≤ (Q : ℝ) * η ^ 2 * δ ^ N
  Bb :
    1 ≤ δ * (Q : ℝ) ^ 2 * η ^ 2 * δ ^ (2 * N)
theorem ny
    {δ η : ℝ} (fD : 0 < δ) (mj : δ ≤ 1)
    (hη : 0 < η) (_hη_one : η ≤ 1) (N : ℕ) :
    ∃ Q : ℕ,
      fy δ η N Q := by
  let x : ℝ := η ^ 2 * δ ^ (2 * N + 1)
  have hx : 0 < x := by
    dsimp [x]
    positivity
  obtain ⟨Q, hQ⟩ := exists_nat_gt (1 / x)
  have BC : 0 < (Q : ℝ) := (div_pos one_pos hx).trans hQ
  have Fo : (1 : ℝ) ≤ Q := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr
      (by exact_mod_cast ne_of_gt BC))
  have FJ : 1 < (Q : ℝ) * x := by
    calc
      1 = (1 / x) * x := by field_simp
      _ < (Q : ℝ) * x := mul_lt_mul_of_pos_right hQ hx
  refine ⟨Q, ?_, ?_⟩
  · have hpow : δ ^ (2 * N + 1) ≤ δ ^ N := by
      exact pow_le_pow_of_le_one fD.le mj (by omega)
    calc
      1 ≤ (Q : ℝ) * x := FJ.le
      _ ≤ (Q : ℝ) * η ^ 2 * δ ^ N := by
        dsimp [x]
        simpa [mul_assoc] using
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hpow (sq_nonneg η))
            BC.le)
  · calc
      1 ≤ (Q : ℝ) * x := FJ.le
      _ ≤ (Q : ℝ) * ((Q : ℝ) * x) := by
        simpa only [one_mul] using
          (mul_le_mul_of_nonneg_right Fo
            (mul_nonneg BC.le hx.le))
      _ = δ * (Q : ℝ) ^ 2 * η ^ 2 * δ ^ (2 * N) := by
        dsimp [x]
        ring
theorem pV
    {δ η : ℝ} {N Q : ℕ}
    (fD : 0 < δ) (hη : 0 < η)
    (hQ : fy δ η N Q)
    (m : ℕ) :
    1 / (bw Q N m : ℝ) ≤
      η ^ 2 * bz δ m ^ N := by
  have hx : (0 : ℝ) < (m + 1 : ℕ) := by positivity
  have hF : (0 : ℝ) < bw Q N m := by
    exact_mod_cast (bw Q N).positive m
  apply (div_le_iff₀ hF).2
  have BD :
      (Q : ℝ) * ((m + 1 : ℕ) : ℝ) ^ N ≤
        (bw Q N m : ℕ) := by
    exact_mod_cast jd Q N m
  calc
    1 ≤ (Q : ℝ) * η ^ 2 * δ ^ N := hQ.uniform
    _ =
        (η ^ 2 * bz δ m ^ N) *
          ((Q : ℝ) * ((m + 1 : ℕ) : ℝ) ^ N) := by
      unfold bz
      rw [div_pow]
      field_simp
    _ ≤
        (η ^ 2 * bz δ m ^ N) *
          (bw Q N m : ℕ) := by
      apply mul_le_mul_of_nonneg_left BD
      exact mul_nonneg (sq_nonneg η)
        (pow_nonneg (o4 fD.le m) N)
theorem kM
    {δ η : ℝ} {N Q : ℕ}
    (fD : 0 < δ) (hη : 0 < η)
    (hQ : fy δ η N Q)
    (m : ℕ) :
    (1 / (bw Q N m : ℝ) ^ 2) /
          ch δ η N m ^ 2 ≤
      δ := by
  have hx : (0 : ℝ) < (m + 1 : ℕ) := by positivity
  have hF : (0 : ℝ) < bw Q N m := by
    exact_mod_cast (bw Q N).positive m
  have ht : 0 < ch δ η N m :=
    os fD hη N m
  rw [div_le_iff₀ (sq_pos_of_pos ht)]
  rw [div_le_iff₀ (sq_pos_of_pos hF)]
  have BD :
      (Q : ℝ) * ((m + 1 : ℕ) : ℝ) ^ N ≤
        (bw Q N m : ℕ) := by
    exact_mod_cast jd Q N m
  have DU :
      ((Q : ℝ) * ((m + 1 : ℕ) : ℝ) ^ N) ^ 2 ≤
        (bw Q N m : ℝ) ^ 2 := by
    exact
      (sq_le_sq₀
        (mul_nonneg (Nat.cast_nonneg Q) (pow_nonneg hx.le N))
        hF.le).2 BD
  calc
    1 ≤ δ * (Q : ℝ) ^ 2 * η ^ 2 * δ ^ (2 * N) := hQ.Bb
    _ =
        δ * (((Q : ℝ) * ((m + 1 : ℕ) : ℝ) ^ N) ^ 2 *
          ch δ η N m ^ 2) := by
      unfold ch bz
      rw [div_pow]
      field_simp
      ring
    _ ≤
        δ * ((bw Q N m : ℝ) ^ 2 *
          ch δ η N m ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ fD.le
      exact mul_le_mul_of_nonneg_right DU (sq_nonneg _)
    _ =
        δ * ch δ η N m ^ 2 *
          (bw Q N m : ℝ) ^ 2 := by
      ring
theorem lT
    {δ κ step : ℝ} {N p m : ℕ}
    (fD : 0 < δ) (mj : δ ≤ 1)
    (yq : 0 ≤ κ) (vH : 4 * κ ≤ step)
    (hp : p ≤ N) :
    Real.sqrt
          (ch δ κ N m ^ 2 *
            (1 + (1 : ℝ)) * (1 + (1 : ℝ))) /
        bz δ m ^ p ≤
      step / 2 := by
  let a := bz δ m
  let t := ch δ κ N m
  have ha : 0 < a := g1 fD m
  have Ah : a ≤ 1 :=
    o5 mj fD.le m
  have ht : 0 ≤ t :=
    rV fD.le yq N m
  have hpow : a ^ N ≤ a ^ p :=
    pow_le_pow_of_le_one ha.le Ah hp
  have x2 :
      Real.sqrt (t ^ 2 * (1 + (1 : ℝ)) * (1 + (1 : ℝ))) =
        2 * t := by
    rw [show
      t ^ 2 * (1 + (1 : ℝ)) * (1 + (1 : ℝ)) =
        (2 * t) ^ 2 by ring]
    exact Real.sqrt_sq (mul_nonneg (by norm_num) ht)
  rw [show ch δ κ N m = t by rfl,
    show bz δ m = a by rfl, x2]
  have xc : 2 * t / a ^ p ≤ 2 * κ := by
    apply (div_le_iff₀ (pow_pos ha p)).2
    calc
      2 * t = (2 * κ) * a ^ N := by
        dsimp [t, a, ch]
        ring
      _ ≤ (2 * κ) * a ^ p :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
  exact xc.trans (by linarith)
theorem rX
    {τ κ a μ : ℝ} {p N : ℕ}
    (ha : 0 < a) (Ah : a ≤ 1) (EM : a ≤ μ)
    (iQ : τ ≤ κ ^ 2 * a ^ N) (hp : p ≤ N) :
    τ / μ ^ p ≤ κ ^ 2 := by
  have rl : 0 < μ := ha.trans_le EM
  have DV : a ^ N ≤ a ^ p :=
    pow_le_pow_of_le_one ha.le Ah hp
  have DW : a ^ p ≤ μ ^ p :=
    pow_le_pow_left₀ ha.le EM p
  apply (div_le_iff₀ (pow_pos rl p)).2
  exact iQ.trans
    (mul_le_mul_of_nonneg_left (DV.trans DW) (sq_nonneg κ))
theorem mg
    {r bU Q : ℕ} {δ κ step : ℝ}
    (fD : 0 < δ) (mj : δ ≤ 1)
    (yq : 0 < κ) (ow : 0 ≤ step)
    (vH : 4 * κ ≤ step)
    (Ai : κ ^ 2 ≤ step / 2)
    (xt :
      (r : ℝ) *
          (aZ r bU 0 : ℝ) * step ≤ 1)
    (zQ :
      (r : ℝ) *
          (aZ r bU 0 : ℝ) * step < 1 / 2)
    (hQ : fy δ κ
      (aZ r bU 0) Q)
    (scale : Fin (r + 1) → ℕ) (oT : Antitone scale) :
    cX
        (bY δ scale)
        (dE δ κ
          (aZ r bU 0) scale)
        (bh
          (bY δ scale))
        (b0
          (bw Q
            (aZ r bU 0)) scale)
        (a1
          (bY δ scale)
          (dE δ κ
            (aZ r bU 0) scale)
          (bh
            (bY δ scale))
          (b0
            (bw Q
              (aZ r bU 0)) scale)) ∧
      a1
          (bY δ scale)
          (dE δ κ
            (aZ r bU 0) scale)
          (bh
            (bY δ scale))
          (b0
            (bw Q
              (aZ r bU 0)) scale)
          r bU < 1 / 2 := by
  let N := aZ r bU 0
  let α := bY δ scale
  let β := dE δ κ N scale
  let μ := bh α
  let τ := b0
    (bw Q N) scale
  have fX : ∀ d, 0 < α d := by
    intro d
    exact l3 fD scale d
  have rm : ∀ d, α d ≤ 1 := by
    intro d
    exact kL fD.le mj scale d
  have gr : ∀ d, 0 ≤ β d := by
    intro d
    exact la δ κ N scale d
  have iQ : 0 ≤ τ := by
    exact (nk
      (bw Q N) scale).le
  have sS : ∀ d, α 0 ≤ α d := by
    intro d
    exact qg fD.le oT d
  have wO :
      ∀ d, d < r → ∀ n,
        n < aZ r bU (d + 1) →
          n + 1 ≤ N := by
    intro d _hd n hn
    have F2 :=
      jN r bU (d + 1)
    dsimp only [N]
    omega
  apply
    (h0
      fX rm gr iQ ow r bU xt zQ)
  · intro d hd n hn
    have hp := wO d hd n hn
    simpa only [α, β, N, dE,
      bY] using
      (lT
        fD mj yq.le vH hp)
  · intro d hd n hn
    have hp := wO d hd n hn
    have A9 : 0 < α 0 := fX 0
    have DX : α 0 ≤ 1 := rm 0
    have Fp : α 0 ≤ μ (d + 1) :=
      oL sS (d + 1)
    have Cq : τ ≤ κ ^ 2 * (α 0) ^ N := by
      simpa only [τ, α, N, b0,
        bY, rW] using
        (pV fD yq hQ (scale 0))
    exact
      (rX
        A9 DX Fp Cq hp).trans Ai
namespace a4.iL
theorem sR
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : aa G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : aF}
    {bP : ℕ}
    (C : a4.iL
      k r initial initialBound F bP) :
    Antitone C.scale := by
  rw [Fin.antitone_iff_succ_le]
  intro j
  exact
    (Nat.le_succ _).trans
      ((F.nP (C.scale j.succ)).trans
        (C.fT j))
end a4.iL
namespace a4.Bounded
structure iL
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initialBound : Fin (r + 1) → ℕ}
    {F : aF}
    {bP : ℕ}
    (S : a4.Bounded
      k r initialBound F bP)
    (initial : aa G k r) where
  wP :
    a4.iL
      k r initial initialBound F bP
  vg : wP.scale 0 ≤ S.ef
theorem oJ
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    {initialBound : Fin (r + 1) → ℕ}
    {F : aF}
    {bP : ℕ}
    (S : a4.Bounded
      k r initialBound F bP)
    (initial : aa G k r)
    (gO :
      ∀ (q : Fin (r + 1)) (e : al k q.1),
        ab.aO
            (initial.partition q e) ≤
          initialBound q) :
    Nonempty (iL S initial) := by
  obtain ⟨P, R, rT⟩ :=
    S.jn.lG.o1
      initial S.jn.gp
  let C : a4.iL
      k r initial initialBound F bP :=
    { aR := P.aR
      aG := P.aG
      length := P.length
      regularity := R
      scale := S.jn.scale P
      o2 := S.jn.o2 P
      fT := S.jn.fT P
      pw := by
        intro j
        simp only [cR]
        rw [congrFun rT j]
        exact
          P.uk S.jn.gp
            j (P.index j)
      dq := by
        intro j
        simpa [cR, rT] using
          S.jn.dq P j
      uV := by
        intro j
        have ip := R.gN j
        have uW := S.jn.i9 P j
        change
          aH
                (R.aQ.partition j.castSucc)
                (R.an.partition j.succ) -
              aH
                (R.an.partition j.castSucc)
                (R.an.partition j.succ) ≤
            fG F (S.jn.scale P) j
        exact ip.trans uW
      bT := by
        intro q
        cases q using Fin.lastCases with
        | last =>
            intro e
            have m5 := congrFun R.da e
            simp only [aa.bl] at m5
            rw [m5]
            calc
              ab.aO
                    (initial.partition (Fin.last r) e) ≤
                  initialBound (Fin.last r) :=
                gO (Fin.last r) e
              _ = ca
                    initialBound P (Fin.last r) := by
                simp [ca]
              _ ≤ S.jn.scale P (Fin.last r) :=
                S.jn.e4 P (Fin.last r)
        | cast j =>
            intro e
            calc
              ab.aO
                    (R.an.partition j.castSucc e) ≤
                  aL
                        j.1 (P.aG j) (P.index j) *
                    ab.aO
                        (initial.partition j.castSucc e) := by
                rw [← congrFun rT j]
                exact R.bT j e
              _ ≤ aL
                        j.1 (P.aG j) (P.index j) *
                    initialBound j.castSucc :=
                Nat.mul_le_mul_left _ (gO j.castSucc e)
              _ = ca
                    initialBound P j.castSucc := by
                simp [ca]
              _ ≤ S.jn.scale P j.castSucc :=
                S.jn.e4 P j.castSucc }
  exact ⟨⟨C, S.kz P⟩⟩
end a4.Bounded
end av.ag
end
section
namespace av.ag
open scoped BigOperators
theorem mh
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ} (H : a2 G k r) :
    ∀ (j : Fin (r + 1)) (e : al k j.1),
      ab.aO
          ((dO H).partition j e) ≤ 2 := by
  intro j
  cases j using Fin.lastCases with
  | last =>
      intro e
      change
        ab.aO
            ((dO H).bl e) ≤ 2
      rw [jF]
      exact na H e
  | cast i =>
      intro e
      simp [dO,
        k9,
        aa.bb]
structure nc
    (k r initialBound : ℕ) (ξ : ℝ) where
  aR : (j : Fin r) → ℕ → ℝ
  aG : (j : Fin r) → ℕ → ℕ
  length : Fin r → ℕ
  zv : ∀ j n, 0 < aR j n
  xk :
    ∀ j n,
      (Fintype.card
          (al k (j.1 + 1)) : ℝ) <
        (aG j n : ℝ) * (aR j n) ^ 2
  length_pos : ∀ j, 0 < length j
  EN :
    ∀ j n,
      aR j n ≤
        om k r
          (iC
            r initialBound aG length) ξ
  i9 :
    (∑ j : Fin r,
      (Fintype.card
          (al k (j.1 + 1)) : ℝ) /
        (length j : ℝ)) ≤
      sb k r
        (iC
          r initialBound aG length) ξ
namespace nc
theorem oJ
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r initialBound : ℕ} {ξ : ℝ}
    (S : nc k r initialBound ξ)
    (initial : aa G k r) :
    Nonempty
      (bk
        G k r initial S.aR S.aG S.length) := by
  exact bk.nonempty
    initial S.aR S.aG S.length
    (fun j n => (S.zv j n).le)
    S.xk S.length_pos
end nc
end av.ag
end
section
namespace av.ag
open scoped BigOperators
noncomputable def cC (k r : ℕ) : ℕ :=
  aZ r
    (aD k r).edges.card 0
noncomputable def cJ
    (ε : ℝ) (r : ℕ) : ℝ :=
  min ε 1 /
    (4 * (Fintype.card (ct r) + 1 : ℕ) : ℕ)
noncomputable def cP (k r : ℕ) : ℝ :=
  1 /
    (4 * (r * cC k r + 1 : ℕ) : ℕ)
noncomputable def d0 (k r : ℕ) : ℝ :=
  cP k r / 8
theorem pW
    {ε : ℝ} (hε : 0 < ε) (r : ℕ) :
    0 < cJ ε r := by
  unfold cJ
  positivity
theorem o6
    {ε : ℝ} (hε : 0 < ε) (r : ℕ) :
    cJ ε r ≤ 1 := by
  unfold cJ
  have F3 : min ε 1 ≤ 1 := min_le_right _ _
  have ur : (1 : ℝ) ≤
      (4 * (Fintype.card (ct r) + 1 : ℕ) : ℕ) := by
    push_cast
    have fE :
        (0 : ℝ) ≤ Fintype.card (ct r) := by
      positivity
    nlinarith
  exact (div_le_self (le_of_lt (lt_min hε zero_lt_one)) ur).trans F3
theorem lI
    {ε : ℝ} (hε : 0 < ε) (r : ℕ) :
    (Fintype.card (ct r) : ℝ) *
        (cJ ε r +
          cJ ε r) ≤ ε := by
  let s := Fintype.card (ct r)
  let x : ℝ := min ε 1
  have hx : 0 < x := lt_min hε zero_lt_one
  have ur : (0 : ℝ) < (4 * (s + 1 : ℕ) : ℕ) := by
    positivity
  have hs : (0 : ℝ) ≤ s := by positivity
  calc
    (Fintype.card (ct r) : ℝ) *
          (cJ ε r +
            cJ ε r) =
        ((2 * (s : ℝ)) * x) / (4 * (s + 1 : ℕ) : ℕ) := by
      simp only [cJ, s, x]
      ring
    _ ≤ x := by
      apply (div_le_iff₀ ur).2
      push_cast
      nlinarith
    _ ≤ ε := min_le_left _ _
theorem fY (k r : ℕ) :
    0 < cP k r := by
  unfold cP
  positivity
theorem mT (k r : ℕ) :
    cP k r ≤ 1 := by
  unfold cP
  apply (div_le_one (by positivity)).2
  push_cast
  have hr : (0 : ℝ) ≤ r := by positivity
  have hH : (0 : ℝ) ≤ cC k r := by
    positivity
  nlinarith [mul_nonneg hr hH]
theorem sU (k r : ℕ) :
    0 < d0 k r := by
  unfold d0
  exact div_pos (fY k r) (by norm_num)
theorem rz (k r : ℕ) :
    d0 k r ≤ 1 := by
  unfold d0
  have ow := mT k r
  nlinarith [fY k r]
theorem n7 (k r : ℕ) :
    4 * d0 k r ≤
      cP k r := by
  unfold d0
  nlinarith [fY k r]
theorem oM (k r : ℕ) :
    d0 k r ^ 2 ≤
      cP k r / 2 := by
  unfold d0
  have lx := fY k r
  have Bz := mT k r
  nlinarith [sq_nonneg (cP k r)]
theorem i6 (k r : ℕ) :
    (r : ℝ) * (cC k r : ℝ) *
        cP k r ≤ 1 / 4 := by
  let p := r * cC k r
  have ur : (0 : ℝ) < (4 * (p + 1 : ℕ) : ℕ) := by
    positivity
  rw [show
    (r : ℝ) * (cC k r : ℝ) *
          cP k r =
        (p : ℝ) / (4 * (p + 1 : ℕ) : ℕ) by
      simp only [cP, p]
      push_cast
      ring]
  apply (div_le_iff₀ ur).2
  push_cast
  have hp : (0 : ℝ) ≤ p := by positivity
  nlinarith
theorem pX (k r : ℕ) :
    (r : ℝ) * (cC k r : ℝ) *
        cP k r ≤ 1 :=
  (i6 k r).trans (by norm_num)
theorem pB (k r : ℕ) :
    (r : ℝ) * (cC k r : ℝ) *
        cP k r < 1 / 2 :=
  (i6 k r).trans_lt (by norm_num)
noncomputable def fU
    (k r ef : ℕ) (δ : ℝ) : ℝ :=
  (1 / 2 : ℝ) *
    bz δ ef ^
      Fintype.card (aj k r)
theorem pC
    {δ : ℝ} (fD : 0 < δ) (k r ef : ℕ) :
    0 < fU k r ef δ := by
  unfold fU
  exact mul_pos (by norm_num)
    (pow_pos (g1 fD ef) _)
theorem nV
    (k n : ℕ) (qb : n + 1 ≤ k) :
    ep k (n + 1) := by
  intro ε hε
  let r : ℕ := n + 1
  let bU : ℕ :=
    (aD k r).edges.card
  let N : ℕ := cC k r
  let δ : ℝ := cJ ε r
  let step : ℝ := cP k r
  let κ : ℝ := d0 k r
  have fD : 0 < δ := by
    exact pW hε r
  have mj : δ ≤ 1 := by
    exact o6 hε r
  have ow : 0 < step := by
    exact fY k r
  have yq : 0 < κ := by
    exact sU k r
  have DY : κ ≤ 1 := by
    exact rz k r
  have vH : 4 * κ ≤ step := by
    exact n7 k r
  have Ai : κ ^ 2 ≤ step / 2 := by
    exact oM k r
  obtain ⟨Q, hQ⟩ :=
    ny
      fD mj yq DY N
  let F : aF := bw Q N
  let initialBound : Fin (r + 1) → ℕ := fun _ => 2
  let S : a4.Bounded
      k r initialBound F 0 :=
    Classical.choice
      (a4.uo
        k r initialBound F 0)
  let c : ℝ :=
    fU k r S.ef δ
  have hc : 0 < c := by
    exact pC fD k r S.ef
  refine ⟨c, hc, ?_⟩
  intro G _instFintype _instDecidableEq _instNonempty H i1
  let initial : aa G k r :=
    dO H
  obtain ⟨Aj⟩ :=
    S.oJ initial (by
      intro q e
      exact mh H q e)
  let C := Aj.wP
  let P : ak G k r :=
    C.regularity.nO
  let α : ℕ → ℝ := bY δ C.scale
  let β : ℕ → ℝ := dE δ κ N C.scale
  let μ : ℕ → ℝ := bh α
  let τ : ℝ := b0 F C.scale
  let E : ℕ → ℕ → ℝ :=
    a1 α β μ τ
  let D : a2.bj (G := G) k r :=
    P.e7 α β
  have fX : ∀ d, 0 < α d := by
    intro d
    exact l3 fD C.scale d
  have rm : ∀ d, α d ≤ 1 := by
    intro d
    exact kL fD.le mj C.scale d
  have gr : ∀ d, 0 ≤ β d := by
    intro d
    exact la δ κ N C.scale d
  have DZ : ∀ d, 0 < β d := by
    intro d
    unfold β dE
    exact sq_pos_of_pos
      (os fD yq N _)
  have iQ : 0 ≤ τ := by
    exact (nk F C.scale).le
  have oT : Antitone C.scale := C.sR
  have wQ :=
    mg
      (r := r) (bU := bU) (Q := Q)
      fD mj yq ow.le vH Ai
      (by
        simpa [step, N, bU, cC] using
          pX k r)
      (by
        simpa [step, N, bU, cC] using
          pB k r)
      (by simpa [N, bU, cC] using hQ)
      C.scale oT
  have k8 : cX α β μ τ E := by
    simpa [α, β, μ, τ, E, F, N, bU,
      cC] using wQ.1
  have vb : E r bU < 1 / 2 := by
    simpa [α, β, μ, τ, E, F, N, bU,
      cC] using wQ.2
  have dk :
      cu P (fun _ => τ) := by
    simpa [P, τ] using
      C.m8
  have BE :
      c ≤ (1 / 2 : ℝ) *
        (∏ e : aj k r, α e.rank) := by
    have EO : 0 ≤ bz δ S.ef :=
      (g1 fD S.ef).le
    have EP : ∀ e : aj k r,
        bz δ S.ef ≤ α e.rank := by
      intro e
      unfold α bY
      apply nU fD.le
      exact
        (oT (Fin.zero_le _)).trans
          Aj.vg
    have yi :
        bz δ S.ef ^
            Fintype.card (aj k r) ≤
          ∏ e : aj k r, α e.rank := by
      calc
        bz δ S.ef ^
              Fintype.card (aj k r) =
            ∏ _e : aj k r,
              bz δ S.ef := by simp
        _ ≤ ∏ e : aj k r, α e.rank := by
          apply Finset.prod_le_prod
          · intro e _he
            exact EO
          · intro e _he
            exact EP e
    simpa [c, fU] using
      (mul_le_mul_of_nonneg_left yi (by norm_num : (0 : ℝ) ≤ 1 / 2))
  have vG :
      ∀ A : ai G k r P.an,
        A.c5 P α β →
          c ≤ c9 A := by
    intro A h5
    exact BE.trans
      (hZ
        P A α β μ τ E fX rm gr iQ h5 dk
        k8 (by simpa [bU] using vb))
  have gO :
      P.an.db (dO H) := by
    simpa [P, initial,
      a5.nO] using
        C.regularity.bJ
  have fC : H.IsCover D := by
    exact
      g5
        (by simpa [r] using qb) H P gO α β c i1 vG
  refine ⟨D, fC, ?_⟩
  intro e
  have BF :=
    P.j3
      α β (fun j => (fX (j + 1)).le) (fun j => DZ (j + 1)) e
  calc
    a2.eB D e ≤
        ∑ q : ct r,
          ((ab.aO
              (P.an.partition q.1.succ (q.2.trans e)) : ℝ) *
                α (q.1.1 + 1) +
            P.cz q.1 (q.2.trans e) /
                β (q.1.1 + 1)) := by
      simpa [D] using BF
    _ ≤ ∑ _q : ct r, (δ + δ) := by
      apply Finset.sum_le_sum
      intro q _hq
      have hd : q.1.1 + 1 ≤ r := by omega
      have pJ :
          ei C.scale (q.1.1 + 1) =
            C.scale q.1.succ := by
        calc
          ei C.scale (q.1.1 + 1) =
              C.scale
                ⟨q.1.1 + 1, Nat.lt_succ_iff.mpr hd⟩ :=
            rx C.scale hd
          _ = C.scale q.1.succ := by
            apply congrArg C.scale
            exact Fin.ext rfl
      have b8 :
          ab.aO
              (P.an.partition q.1.succ (q.2.trans e)) ≤
            C.scale q.1.succ := by
        simpa [P,
          a5.nO] using
          C.bT q.1.succ (q.2.trans e)
      have Di :
          (ab.aO
              (P.an.partition q.1.succ (q.2.trans e)) : ℝ) *
                α (q.1.1 + 1) ≤ δ := by
        calc
          (ab.aO
                (P.an.partition q.1.succ (q.2.trans e)) : ℝ) *
                  α (q.1.1 + 1) ≤
              (C.scale q.1.succ : ℝ) * α (q.1.1 + 1) :=
            mul_le_mul_of_nonneg_right
              (Nat.cast_le.mpr b8) (fX _).le
          _ = (C.scale q.1.succ : ℝ) *
                bz δ (C.scale q.1.succ) := by
            simp [α, bY, pJ]
          _ ≤ δ := tJ fD.le _
      have BG :
          P.cz q.1 (q.2.trans e) ≤
            P.fB q.1 := by
        rw [P.n3 q.1]
        exact Finset.single_le_sum
          (fun f _ => P.qa q.1 f)
          (Finset.mem_univ (q.2.trans e))
      have ER :
          P.fB q.1 ≤
            fG F C.scale q.1 := by
        simpa [P] using C.uV q.1
      have lf :
          P.cz q.1 (q.2.trans e) /
                β (q.1.1 + 1) ≤ δ := by
        calc
          P.cz q.1 (q.2.trans e) /
                β (q.1.1 + 1) ≤
              fG F C.scale q.1 /
                β (q.1.1 + 1) :=
            div_le_div_of_nonneg_right
              (BG.trans ER) (gr _)
          _ =
              (1 /
                  (bw Q N
                    (C.scale q.1.succ) : ℝ) ^ 2) /
                ch δ κ N
                    (C.scale q.1.succ) ^ 2 := by
            simp [F, fG, β,
              dE, pJ]
          _ ≤ δ :=
            kM
              fD yq hQ (C.scale q.1.succ)
      exact add_le_add Di lf
    _ = (Fintype.card (ct r) : ℝ) *
          (δ + δ) := by
      simp [mul_add]
    _ ≤ ε := by
      simpa [δ, r] using
        lI hε (n + 1)
end av.ag
end
section
namespace av.ag
def yr (k N : ℕ) [NeZero N]
    (δ c : ℝ) : Prop :=
  ∀ A : Finset (ZMod N),
    δ ≤ mean (aN A) →
      c ≤ eU k N (aN A)
def jL (k : ℕ) (δ c : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N], yr k N δ c
end av.ag
end
section
namespace av.ag
open scoped BigOperators
def eA (k N : ℕ) (A : Finset (ZMod N)) :
    aM (fun _ : Fin k => ZMod N) where
  edge j x := f8 k N j x ∈ A
@[simp]
theorem vI
    (k N : ℕ) (A : Finset (ZMod N))
    (j : Fin k)
    (x : b9 (fun _ : Fin k => ZMod N) j) :
    (eA k N A).edge j x ↔
      f8 k N j x ∈ A :=
  Iff.rfl
@[simp]
theorem pD
    (k N : ℕ) (A : Finset (ZMod N))
    (j : Fin k)
    (x : b9 (fun _ : Fin k => ZMod N) j) :
    (eA k N A).cD.dt j x =
      aN A (f8 k N j x) := by
  classical
  by_cases hx : f8 k N j x ∈ A
  · rw [aM.r7]
    · exact (cG hx).symm
    · exact hx
  · rw [aM.k2]
    · exact (cj hx).symm
    · exact hx
theorem mU
    (r N : ℕ) [NeZero N] (A : Finset (ZMod N)) :
    (eA (r + 2) N A).cD.iT =
      eU (r + 2) N (aN A) := by
  rw [← mF
    r N (aN A)]
  simp only [cm.iT]
  apply congrArg mean
  funext x
  apply Finset.prod_congr rfl
  intro j _
  exact pD
    (r + 2) N A j (bO x j)
abbrev dz
    (r N : ℕ) (A : Finset (ZMod N)) :=
  ↥A × (Fin r → ZMod N)
def dI
    (r N : ℕ) (A : Finset (ZMod N))
    (p : dz r N A) :
    Fin (r + 2) → ZMod N :=
  dj r N p.1.1 0 p.2
@[simp]
theorem pk
    (r N : ℕ) (A : Finset (ZMod N))
    (p : dz r N A) :
    cS (r + 2) N
      (dI r N A p) = 0 := by
  simp [dI]
@[simp]
theorem n8
    (r N : ℕ) (A : Finset (ZMod N))
    (p : dz r N A) :
    cw (r + 2) N
      (dI r N A p) = p.1.1 := by
  simp [dI]
@[simp]
theorem rA
    (r N : ℕ) (A : Finset (ZMod N))
    (p : dz r N A)
    (j : Fin (r + 2)) :
    f8 (r + 2) N j
        (bO (dI r N A p) j) =
      p.1.1 := by
  rw [mD,
    n8,
    pk]
  simp
theorem kl
    (r N : ℕ) [NeZero N] (A : Finset (ZMod N))
    (p : dz r N A) :
    dI r N A p ∈
      (eA (r + 2) N A).ff := by
  let : ∀ _ : Fin (r + 2), Fintype (ZMod N) :=
    fun _ => inferInstance
  rw [aM.nC]
  intro j
  rw [vI,
    rA]
  exact p.1.2
theorem tn
    (r N : ℕ) (A : Finset (ZMod N)) :
    Function.Injective (dI r N A) := by
  intro p q hpq
  apply Prod.ext
  · apply Subtype.ext
    have yB :=
      congrArg
        (cw (r + 2) N) hpq
    simpa using yB
  · funext i
    exact congrFun hpq i.succ.succ
noncomputable def cx
    {G : Type*} {n : ℕ} (j : Fin (n + 1))
    (x : b9 (fun _ : Fin (n + 1) => G) j) :
    Fin n → G :=
  fun t => x (finSuccAboveEquiv j t)
theorem nW
    {G : Type*} [AddCommGroup G] {n : ℕ}
    {x y : Fin (n + 1) → G}
    {j l : Fin (n + 1)}
    (Hw : j = l)
    (Ak :
      cx j (bO x j) =
        cx l (bO y l))
    (hsum : (∑ i, x i) = ∑ i, y i) :
    x = y := by
  subst l
  have z0 :
      ∑ i ∈ (Finset.univ : Finset (Fin (n + 1))).erase j,
          x i =
        ∑ i ∈ (Finset.univ : Finset (Fin (n + 1))).erase j,
          y i := by
    apply Finset.sum_congr rfl
    intro i hi
    have hij : i ≠ j := (Finset.mem_erase.mp hi).1
    obtain ⟨t, ht⟩ := Fin.exists_succAbove_eq hij
    subst i
    exact congrFun Ak t
  have hj : x j = y j := by
    apply add_left_cancel
      (a :=
        ∑ i ∈ (Finset.univ : Finset (Fin (n + 1))).erase j,
          x i)
    calc
      (∑ i ∈ (Finset.univ : Finset (Fin (n + 1))).erase j,
          x i) + x j =
          ∑ i, x i :=
        Finset.sum_erase_add _ _ (Finset.mem_univ j)
      _ = ∑ i, y i := hsum
      _ =
          (∑ i ∈
              (Finset.univ : Finset (Fin (n + 1))).erase j,
              y i) + y j :=
        (Finset.sum_erase_add _ _ (Finset.mem_univ j)).symm
      _ =
          (∑ i ∈
              (Finset.univ : Finset (Fin (n + 1))).erase j,
              x i) + y j := by
        rw [z0]
  funext i
  by_cases hij : i = j
  · simpa [hij] using hj
  · obtain ⟨t, ht⟩ := Fin.exists_succAbove_eq hij
    subst i
    exact congrFun Ak t
namespace aM
noncomputable def j4
    {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
    (bG :
      bj (fun _ : Fin (n + 1) => G)) :
    Finset (Fin (n + 1) × (Fin n → G)) := by
  classical
  exact Finset.univ.biUnion fun j =>
    (bG j).image fun x =>
      (j, cx j x)
theorem uX
    {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
    (bG :
      bj (fun _ : Fin (n + 1) => G))
    (j : Fin (n + 1))
    (x : b9 (fun _ : Fin (n + 1) => G) j)
    (hx : x ∈ bG j) :
    (j, cx j x) ∈
      j4 bG := by
  classical
  apply Finset.mem_biUnion.mpr
  refine ⟨j, Finset.mem_univ j, ?_⟩
  exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
theorem oN
    {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
    (bG :
      bj (fun _ : Fin (n + 1) => G)) :
    (j4 bG).card ≤
      fh bG := by
  classical
  calc
    (j4 bG).card ≤
        ∑ j : Fin (n + 1),
          ((bG j).image fun x =>
            (j, cx j x)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ j : Fin (n + 1), (bG j).card := by
      apply Finset.sum_le_sum
      intro j _
      exact Finset.card_image_le
    _ = fh bG := rfl
end aM
noncomputable def j5
    (r N : ℕ) [NeZero N] (A : Finset (ZMod N))
    (bG :
      aM.bj
        (fun _ : Fin (r + 2) => ZMod N))
    (fC :
      (eA (r + 2) N A).gR bG)
    (p : dz r N A) :
    Fin (r + 2) :=
  Classical.choose
    (fC (dI r N A p)
      (kl r N A p))
@[simp]
theorem uY
    (r N : ℕ) [NeZero N] (A : Finset (ZMod N))
    (bG :
      aM.bj
        (fun _ : Fin (r + 2) => ZMod N))
    (fC :
      (eA (r + 2) N A).gR bG)
    (p : dz r N A) :
    bO (dI r N A p)
        (j5 r N A bG fC p) ∈
      bG (j5 r N A bG fC p) :=
  Classical.choose_spec
    (fC (dI r N A p)
      (kl r N A p))
noncomputable def pl
    (r N : ℕ) [NeZero N] (A : Finset (ZMod N))
    (bG :
      aM.bj
        (fun _ : Fin (r + 2) => ZMod N))
    (fC :
      (eA (r + 2) N A).gR bG)
    (p : dz r N A) :
    Fin (r + 2) × (Fin (r + 1) → ZMod N) :=
  let j := j5 r N A bG fC p
  (j, cx j
    (bO (dI r N A p) j))
theorem nX
    (r N : ℕ) [NeZero N] (A : Finset (ZMod N))
    (bG :
      aM.bj
        (fun _ : Fin (r + 2) => ZMod N))
    (fC :
      (eA (r + 2) N A).gR bG)
    (p : dz r N A) :
    pl r N A bG fC p ∈
      aM.j4 bG := by
  classical
  exact aM.uX bG
    (j5 r N A bG fC p)
    (bO (dI r N A p)
      (j5 r N A bG fC p))
    (uY r N A bG fC p)
theorem sh
    (r N : ℕ) [NeZero N] (A : Finset (ZMod N))
    (bG :
      aM.bj
        (fun _ : Fin (r + 2) => ZMod N))
    (fC :
      (eA (r + 2) N A).gR bG) :
    Function.Injective
      (pl r N A bG fC) := by
  intro p q hpq
  apply tn r N A
  apply nW
  · exact congrArg Prod.fst hpq
  · exact congrArg Prod.snd hpq
  · change
      cS (r + 2) N
          (dI r N A p) =
        cS (r + 2) N
          (dI r N A q)
    simp
theorem n9
    (r N : ℕ) [NeZero N] (A : Finset (ZMod N))
    (bG :
      aM.bj
        (fun _ : Fin (r + 2) => ZMod N))
    (fC :
      (eA (r + 2) N A).gR bG) :
    Fintype.card (dz r N A) ≤
      aM.fh bG := by
  classical
  let f := pl r N A bG fC
  calc
    Fintype.card (dz r N A) =
        (Finset.univ.image f).card := by
      rw [Finset.card_image_of_injective _
        (sh r N A bG fC)]
      simp
    _ ≤
        (aM.j4 bG).card := by
      apply Finset.card_le_card
      intro y hy
      obtain ⟨p, _hp, rfl⟩ := Finset.mem_image.mp hy
      exact nX
        r N A bG fC p
    _ ≤ aM.fh bG :=
      aM.oN
        bG
@[simp]
theorem vh
    (r N : ℕ) [NeZero N] :
    aM.ik
        (fun _ : Fin (r + 2) => ZMod N) =
      (r + 2) * N ^ (r + 1) := by
  simp [aM.ik, b9,
    Fintype.card_pi, ZMod.card]
theorem kY
    (r N : ℕ) [NeZero N] (A : Finset (ZMod N))
    (bG :
      aM.bj
        (fun _ : Fin (r + 2) => ZMod N))
    (fC :
      (eA (r + 2) N A).gR bG) :
    mean (aN A) / (r + 2 : ℝ) ≤
      aM.eO bG := by
  have i1 :
      A.card * N ^ r ≤
        aM.fh bG := by
    simpa using
      n9
        r N A bG fC
  have hN : (N : ℝ) ≠ 0 := by
    exact_mod_cast (NeZero.ne N)
  rw [iM, ZMod.card,
    aM.eO,
    vh]
  calc
    (A.card : ℝ) / (N : ℝ) / (r + 2 : ℝ) =
        ((A.card * N ^ r : ℕ) : ℝ) /
          (((r + 2) * N ^ (r + 1) : ℕ) : ℝ) := by
      norm_num [Nat.cast_mul, Nat.cast_pow]
      field_simp
      ring
    _ ≤
        (aM.fh bG : ℝ) /
          (((r + 2) * N ^ (r + 1) : ℕ) : ℝ) := by
      apply div_le_div_of_nonneg_right
      · exact_mod_cast i1
      · positivity
def gz (k : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ c : ℝ, 0 < c ∧
      ∀ (N : ℕ) [NeZero N],
        ∀ H :
            aM (fun _ : Fin k => ZMod N),
          H.cD.iT < c →
            ∃ bG :
                aM.bj
                  (fun _ : Fin k => ZMod N),
              H.gR bG ∧
                aM.eO
                    bG ≤ ε
theorem nd
    (r : ℕ)
    (F4 :
      gz (r + 2))
    {δ : ℝ} (fD : 0 < δ) :
    ∃ c : ℝ, 0 < c ∧
      jL (r + 2) δ c := by
  let ε : ℝ := (δ / (r + 2 : ℝ)) / 2
  have hk : 0 < (r + 2 : ℝ) := by positivity
  have BF : 0 < δ / (r + 2 : ℝ) :=
    div_pos fD hk
  have hε : 0 < ε := by
    exact div_pos BF (by norm_num)
  obtain ⟨c, hc, yX⟩ := F4 ε hε
  refine ⟨c, hc, ?_⟩
  intro N inst A hA
  by_contra i1
  have Cr :
      eU (r + 2) N (aN A) < c :=
    lt_of_not_ge i1
  have AZ :
      (eA (r + 2) N A).cD.iT <
        c := by
    simpa [mU]
      using Cr
  obtain ⟨bG, fC, Hl⟩ :=
    yX N (eA (r + 2) N A) AZ
  have rE :
      mean (aN A) / (r + 2 : ℝ) ≤
        aM.eO bG :=
    kY
      r N A bG fC
  have rb :
      δ / (r + 2 : ℝ) ≤
        mean (aN A) / (r + 2 : ℝ) :=
    div_le_div_of_nonneg_right hA hk.le
  have G6 : ε < δ / (r + 2 : ℝ) := by
    dsimp [ε]
    linarith
  linarith
end av.ag
end
section
namespace av.ag
open scoped BigOperators
def eV {n : ℕ} (j : Fin (n + 1)) :
    al (n + 1) n :=
  Fin.succAboveOrderEmb j
noncomputable def el (n : ℕ) :
    Fin (n + 1) ≃ al (n + 1) n :=
  (Set.powersetCard.ofSingleton :
      Fin (n + 1) ≃ Set.powersetCard (Fin (n + 1)) 1) |>.trans
    ((Set.powersetCard.compl (m := n) (n := 1) (by simp) :
        Set.powersetCard (Fin (n + 1)) 1 ≃
          Set.powersetCard (Fin (n + 1)) n) |>.trans
      (Set.powersetCard.ofFinEmbEquiv :
        al (n + 1) n ≃
          Set.powersetCard (Fin (n + 1)) n).symm)
@[simp]
theorem mi
    {n : ℕ} (j : Fin (n + 1)) :
    el n j = eV j := by
  apply OrderEmbedding.range_inj.mp
  change
    Set.range ((el n) j) =
      Set.range (Fin.succAboveOrderEmb j)
  rw [Fin.range_succAboveOrderEmb]
  ext i
  simp only [el, Equiv.trans_apply]
  rw [
    Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem]
  rw [Set.powersetCard.mem_compl]
  change
    i ∉ ({j} : Finset (Fin (n + 1))) ↔
      i ∈ ({j} : Set (Fin (n + 1)))ᶜ
  simp
@[simp]
theorem lU
    {G : Type*} {n : ℕ} (j : Fin (n + 1))
    (y : Fin n → G) :
    cx j
        (cf j y) = y := by
  funext t
  simp [cx]
@[simp]
theorem e5
    {G : Type*} {n : ℕ} (j : Fin (n + 1))
    (x : b9 (fun _ : Fin (n + 1) => G) j) :
    cf j
        (cx j x) = x := by
  funext i
  change
    x (finSuccAboveEquiv j
        ((finSuccAboveEquiv j).symm i)) = x i
  rw [(finSuccAboveEquiv j).apply_symm_apply]
noncomputable def o7
    {G : Type*} {n : ℕ} (j : Fin (n + 1)) :
    b9 (fun _ : Fin (n + 1) => G) j ≃
      (Fin n → G) where
  toFun := cx j
  invFun := cf j
  left_inv := e5 j
  right_inv := lU j
@[simp]
theorem i7
    {G : Type*} {n : ℕ} (j : Fin (n + 1))
    (x : Fin (n + 1) → G) :
    cx j (bO x j) =
      aI (eV j) x := by
  rfl
@[simp]
theorem vK
    {G : Type*} {n : ℕ} (j : Fin (n + 1))
    (x : Fin (n + 1) → G) :
    cf j
        (aI (eV j) x) =
      bO x j := by
  rw [←
    e5 j
      (bO x j)]
  congr
noncomputable def aM.gP
    {G : Type*} {n : ℕ}
    (H : aM (fun _ : Fin (n + 1) => G)) :
    a2 G (n + 1) n where
  edge e y :=
    let j := (el n).symm e
    H.edge j (cf j y)
@[simp]
theorem aM.kN
    {G : Type*} {n : ℕ}
    (H : aM (fun _ : Fin (n + 1) => G))
    (j : Fin (n + 1)) (y : Fin n → G) :
    H.gP.edge (eV j) y ↔
      H.edge j (cf j y) := by
  change
    H.edge ((el n).symm (eV j))
        (cf
          ((el n).symm (eV j)) y) ↔
      H.edge j (cf j y)
  have hj :
      (el n).symm (eV j) = j := by
    rw [← mi]
    exact (el n).symm_apply_apply j
  rw [hj]
theorem aM.qT
    {G : Type*} {n : ℕ}
    (H : aM (fun _ : Fin (n + 1) => G))
    (x : Fin (n + 1) → G) :
    H.gP.fj x ↔
      ∀ j, H.edge j (bO x j) := by
  constructor
  · intro hx j
    have hj := hx (eV j)
    rw [H.kN] at hj
    simpa using hj
  · intro hx e
    let j := (el n).symm e
    have he : eV j = e := by
      rw [← mi]
      exact (el n).apply_symm_apply e
    rw [← he]
    rw [H.kN]
    simpa using hx j
theorem aM.lb
    {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
    (H : aM (fun _ : Fin (n + 1) => G)) :
    H.gP.ij =
      H.ff := by
  ext x
  rw [a2.kR,
    aM.nC,
    H.qT]
theorem aM.si
    {G : Type*} [Fintype G] [Nonempty G]
    {n : ℕ}
    (H : aM (fun _ : Fin (n + 1) => G)) :
    H.gP.cD.gJ =
      H.cD.iT := by
  classical
  rw [a2.tz,
    aM.p8,
    H.lb]
noncomputable def c8
    {G : Type*} [DecidableEq G] {n : ℕ}
    (D : a2.bj
      (G := G) (n + 1) n) :
    aM.bj
      (fun _ : Fin (n + 1) => G) := by
  classical
  exact fun j =>
    (D (eV j)).image
      (cf j)
@[simp]
theorem rd
    {G : Type*} [DecidableEq G] {n : ℕ}
    (D : a2.bj
      (G := G) (n + 1) n)
    (j : Fin (n + 1))
    (x : b9 (fun _ : Fin (n + 1) => G) j) :
    x ∈ c8 D j ↔
      cx j x ∈ D (eV j) := by
  classical
  constructor
  · intro hx
    obtain ⟨y, hy, Em⟩ := Finset.mem_image.mp hx
    rw [← Em]
    simpa using hy
  · intro hx
    exact Finset.mem_image.mpr
      ⟨cx j x, hx,
        e5 j x⟩
@[simp]
theorem sj
    {G : Type*} [DecidableEq G] {n : ℕ}
    (D : a2.bj
      (G := G) (n + 1) n)
    (j : Fin (n + 1)) :
    (c8 D j).card =
      (D (eV j)).card := by
  classical
  rw [c8,
    Finset.card_image_of_injective _]
  intro y z G7
  have ES :=
    congrArg (cx j) G7
  simpa using ES
theorem aM.o8
    {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
    (H : aM (fun _ : Fin (n + 1) => G))
    (D : a2.bj
      (G := G) (n + 1) n)
    (fC : H.gP.IsCover D) :
    H.gR (c8 D) := by
  intro x hx
  have Cs :
      x ∈ H.gP.ij := by
    rw [H.lb]
    exact hx
  obtain ⟨e, he⟩ := fC x Cs
  let j := (el n).symm e
  have heq : eV j = e := by
    rw [← mi]
    exact (el n).apply_symm_apply e
  refine ⟨j, (rd D j _).2 ?_⟩
  rw [
    i7,
    heq]
  exact he
theorem mV
    {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
    (D : a2.bj
      (G := G) (n + 1) n)
    (j : Fin (n + 1)) :
    aM.iU
        (c8 D) j =
      a2.eB
        D (eV j) := by
  rw [aM.iU,
    a2.eB,
    sj]
  have fE :
      Fintype.card
          (b9
            (fun _ : Fin (n + 1) => G) j) =
        Fintype.card (Fin n → G) :=
    Fintype.card_congr (o7 j)
  rw [fE]
theorem kZ
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {n : ℕ}
    (D : a2.bj
      (G := G) (n + 1) n)
    {ε : ℝ}
    (hD :
      ∀ e, a2.eB D e ≤ ε) :
    aM.eO
        (c8 D) ≤ ε := by
  let M : ℕ := Fintype.card (Fin n → G)
  have hM : 0 < M := Fintype.card_pos
  have zG (j : Fin (n + 1)) :
      Fintype.card
          (b9
            (fun _ : Fin (n + 1) => G) j) = M := by
    exact Fintype.card_congr (o7 j)
  have fE (j : Fin (n + 1)) :
      ((c8 D j).card : ℝ) ≤
        ε * M := by
    have rb :=
      mV D j
    have hbound := hD (eV j)
    rw [← rb] at hbound
    rw [aM.iU,
      zG] at hbound
    have G8 : (0 : ℝ) < M := by
      exact_mod_cast hM
    exact (div_le_iff₀ G8).mp hbound
  have i1 :
      (aM.fh
          (c8 D) : ℝ) ≤
        (n + 1 : ℝ) * (ε * M) := by
    calc
      (aM.fh
          (c8 D) : ℝ) =
          ∑ j : Fin (n + 1),
            ((c8 D j).card : ℝ) := by
        simp [aM.fh]
      _ ≤ ∑ _j : Fin (n + 1), ε * M :=
        Finset.sum_le_sum fun j _ => fE j
      _ = (n + 1 : ℝ) * (ε * M) := by
        simp
  have Ct :
      aM.ik
          (fun _ : Fin (n + 1) => G) =
        (n + 1) * M := by
    unfold aM.ik
    simp_rw [zG]
    simp
  rw [aM.eO,
    Ct]
  have ET :
      (0 : ℝ) < ((n + 1) * M : ℕ) := by
    exact_mod_cast Nat.mul_pos (by omega) hM
  apply (div_le_iff₀ ET).2
  calc
    (aM.fh
        (c8 D) : ℝ) ≤
        (n + 1 : ℝ) * (ε * M) := i1
    _ = ε * (((n + 1) * M : ℕ) : ℝ) := by
      push_cast
      ring
theorem lJ
    (n : ℕ)
    (rf :
      ep (n + 1) n) :
    gz (n + 1) := by
  intro ε hε
  obtain ⟨c, hc, yX⟩ := rf ε hε
  refine ⟨c, hc, ?_⟩
  intro N inst H i1
  have zw :
      H.gP.cD.gJ < c := by
    rw [H.si]
    exact i1
  obtain ⟨D, fC, hD⟩ :=
    yX (ZMod N) H.gP zw
  exact
    ⟨c8 D,
      H.o8 D fC,
      kZ D hD⟩
theorem jA
    (r : ℕ)
    (rf :
      ep (r + 2) (r + 1)) :
    gz (r + 2) := by
  simpa [Nat.add_assoc] using
    (lJ
      (r + 1) (by simpa [Nat.add_assoc] using rf))
end av.ag
end
section
namespace av.ag
theorem nf
    (r : ℕ)
    (rf :
      ep (r + 2) (r + 1))
    {δ : ℝ} (fD : 0 < δ) :
    ∃ c : ℝ, 0 < c ∧
      jL (r + 2) δ c :=
  nd r
    (jA
      r rf)
    fD
theorem j6
    (k : ℕ) (hk : 2 ≤ k)
    (rf :
      ep k (k - 1))
    {δ : ℝ} (fD : 0 < δ) :
    ∃ c : ℝ, 0 < c ∧
      jL k δ c := by
  have Bc : k - 2 + 2 = k := by
    omega
  have qb : k - 2 + 1 = k - 1 := by
    omega
  have Cu :
      ep
        (k - 2 + 2) (k - 2 + 1) := by
    simpa only [Bc, qb] using rf
  simpa only [Bc] using
    (nf
      (k - 2) Cu fD)
end av.ag
end
section
namespace av.ag
theorem Cv (k : ℕ) (hk : 2 ≤ k) {δ : ℝ} (fD : 0 < δ) :
    ∃ c : ℝ, 0 < c ∧ jL k δ c := by
  refine
    j6
      k hk ?_ fD
  have qb : k - 1 = (k - 2) + 1 := by omega
  rw [qb]
  exact nV
    k (k - 2) (by omega)
end av.ag
end
section
namespace av.ag
open scoped BigOperators
noncomputable def lK (k N : ℕ) [NeZero N]
    (f : ZMod N → ℝ) : ℝ :=
  ∑ a : ZMod N, ∑ d : ZMod N, cr k N f a d
noncomputable def f5 (k N : ℕ) [NeZero N]
    (f : ZMod N → ℝ) : ℝ :=
  ∑ a : ZMod N, cr k N f a 0
noncomputable def gq (k N : ℕ) [NeZero N]
    (f : ZMod N → ℝ) : ℝ :=
  ∑ a : ZMod N,
    ∑ d ∈ (Finset.univ.filter fun d : ZMod N => d ≠ 0),
      cr k N f a d
@[simp]
theorem xX
    (k N : ℕ) (f : ZMod N → ℝ) (a : ZMod N) :
    cr k N f a 0 = f a ^ k := by
  simp [cr, gK]
theorem rB
    (k N : ℕ) [NeZero N] (f : ZMod N → ℝ) :
    f5 k N f = ∑ a : ZMod N, f a ^ k := by
  simp [f5]
theorem wb
    {x B : ℝ} (EU : 0 ≤ x) (A7 : x ≤ B)
    {k : ℕ} (hk : 1 ≤ k) :
    x ^ k ≤ B ^ (k - 1) * x := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  have Hx : 0 ≤ B := EU.trans A7
  have hpow : x ^ m ≤ B ^ m :=
    pow_le_pow_left₀ EU A7 m
  simpa [Nat.add_comm, pow_succ', Nat.add_sub_cancel, mul_comm] using
    (mul_le_mul_of_nonneg_right hpow EU)
theorem ux
    {k N : ℕ} [NeZero N] {f : ZMod N → ℝ} {B : ℝ}
    (hk : 1 ≤ k)
    (Bd : ∀ x, 0 ≤ f x)
    (BR : ∀ x, f x ≤ B) :
    f5 k N f ≤
      B ^ (k - 1) * (N : ℝ) * mean f := by
  rw [rB]
  calc
    ∑ a : ZMod N, f a ^ k ≤
        ∑ a : ZMod N, B ^ (k - 1) * f a := by
      exact Finset.sum_le_sum fun a _ =>
        wb (Bd a) (BR a) hk
    _ = B ^ (k - 1) * ∑ a : ZMod N, f a := by
      rw [Finset.mul_sum]
    _ = B ^ (k - 1) * ((N : ℝ) * mean f) := by
      rw [← Fintype.card_mul_expect]
      simp [mean, ZMod.card]
    _ = B ^ (k - 1) * (N : ℝ) * mean f := by ring
theorem oO
    (k N : ℕ) [NeZero N] (f : ZMod N → ℝ) :
    lK k N f =
      f5 k N f + gq k N f := by
  classical
  rw [lK, f5, gq,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  have Cw :
      ∑ d ∈ (Finset.univ.filter fun d : ZMod N => d = 0),
        cr k N f a d =
          cr k N f a 0 := by
    apply Finset.sum_eq_single 0
    · intro d hd Cj
      exact (Cj (Finset.mem_filter.mp hd).2).elim
    · simp
  rw [← Finset.sum_filter_add_sum_filter_not
    (s := Finset.univ) (p := fun d : ZMod N => d = 0)
    (f := fun d => cr k N f a d)]
  rw [Cw]
theorem nA
    (k N : ℕ) [NeZero N] (f : ZMod N → ℝ)
    (h :
      f5 k N f <
        lK k N f) :
    0 < gq k N f := by
  rw [oO] at h
  linarith
theorem sm
    (k N : ℕ) [NeZero N] (f : ZMod N → ℝ) :
    eU k N f =
      lK k N f / (N : ℝ) / (N : ℝ) := by
  simp [eU, lK, fq, mean,
    Fintype.expect_eq_sum_div_card, ZMod.card, Finset.sum_div]
theorem sn
    (k N : ℕ) [NeZero N] (f : ZMod N → ℝ) :
    lK k N f =
      (N : ℝ) * (N : ℝ) * eU k N f := by
  rw [sm]
  have hN : (N : ℝ) ≠ 0 := by
    exact_mod_cast (NeZero.ne N)
  field_simp
theorem rg
    {k N : ℕ} [NeZero N] {f : ZMod N → ℝ} {B : ℝ}
    (hk : 1 ≤ k)
    (Bd : ∀ x, 0 ≤ f x)
    (BR : ∀ x, f x ≤ B)
    (i1 :
      B ^ (k - 1) * mean f <
        (N : ℝ) * eU k N f) :
    0 < gq k N f := by
  apply nA
  have hN : 0 < (N : ℝ) := by
    exact_mod_cast NeZero.pos N
  calc
    f5 k N f ≤
        B ^ (k - 1) * (N : ℝ) * mean f :=
      ux hk Bd BR
    _ = (N : ℝ) * (B ^ (k - 1) * mean f) := by ring
    _ < (N : ℝ) *
        ((N : ℝ) * eU k N f) :=
      mul_lt_mul_of_pos_left i1 hN
    _ = lK k N f := by
      rw [sn]
      ring
theorem qU
    {k N : ℕ} {f : ZMod N → ℝ}
    (hf : ∀ x, 0 ≤ f x) (a d : ZMod N) :
    0 < cr k N f a d ↔
      ∀ j : Fin k, 0 < f (gK a d j) := by
  constructor
  · intro yi j
    have Dj :
        (∏ i : Fin k, f (gK a d i)) ≠ 0 := by
      simpa only [cr] using ne_of_gt yi
    have BH : f (gK a d j) ≠ 0 :=
      Finset.prod_ne_zero_iff.mp Dj j (Finset.mem_univ j)
    exact lt_of_le_of_ne (hf _) (Ne.symm BH)
  · intro D0
    rw [cr]
    exact Finset.prod_pos fun j _ => D0 j
theorem qy
    {k N : ℕ} [NeZero N] {f : ZMod N → ℝ}
    (hf : ∀ x, 0 ≤ f x)
    (DC : 0 < gq k N f) :
    ∃ a d : ZMod N, d ≠ 0 ∧
      ∀ j : Fin k, 0 < f (gK a d j) := by
  classical
  rw [gq] at DC
  have zx :
      ∀ a ∈ (Finset.univ : Finset (ZMod N)),
        0 ≤
          ∑ d ∈ (Finset.univ.filter fun d : ZMod N => d ≠ 0),
            cr k N f a d := by
    intro a _
    exact Finset.sum_nonneg fun d _ => qH hf a d
  obtain ⟨a, _, ha⟩ :=
    (Finset.sum_pos_iff_of_nonneg zx).mp DC
  have zy :
      ∀ d ∈ (Finset.univ.filter fun d : ZMod N => d ≠ 0),
        0 ≤ cr k N f a d := by
    intro d _
    exact qH hf a d
  obtain ⟨d, Fq, zF⟩ :=
    (Finset.sum_pos_iff_of_nonneg zy).mp ha
  refine ⟨a, d, (Finset.mem_filter.mp Fq).2, ?_⟩
  exact (qU hf a d).mp zF
end av.ag
end
section
namespace av.ag
def bZ {N : ℕ} [NeZero N] (a d : ZMod N) (j : ℕ) : ℕ :=
  (a + (j : ZMod N) * d).val
@[simp]
theorem xN {N : ℕ} [NeZero N]
    (a d : ZMod N) (j : ℕ) :
    (bZ a d j : ZMod N) = a + (j : ZMod N) * d :=
  ZMod.natCast_zmod_val _
theorem uy {L U Dk Dl Dm : ℤ}
    (Hm : L ≤ Dk ∧ Dk ≤ U)
    (Hn : L ≤ Dl ∧ Dl ≤ U)
    (Ho : L ≤ Dm ∧ Dm ≤ U) :
    |Dm - 2 * Dl + Dk| ≤ 2 * (U - L) := by
  rw [abs_le]
  constructor <;> linarith
theorem pY {k N : ℕ} [NeZero N]
    (a d : ZMod N) (L U : ℤ)
    (jO :
      ∀ i : ℕ, i < k →
        L ≤ bZ a d i ∧ bZ a d i ≤ U)
    (rY : 2 * (U - L) < (N : ℤ))
    (j : ℕ) (hj : j + 2 < k) :
    (bZ a d (j + 2) : ℤ) -
        2 * bZ a d (j + 1) +
        bZ a d j = 0 := by
  let z : ℤ :=
    (bZ a d (j + 2) : ℤ) -
      2 * bZ a d (j + 1) +
      bZ a d j
  apply Int.eq_zero_of_abs_lt_dvd (m := (N : ℤ)) (x := z)
  · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    dsimp [z]
    push_cast
    simp only [xN, Nat.cast_add, Nat.cast_ofNat]
    ring
  · exact lt_of_le_of_lt
      (uy
        (jO j (by omega))
        (jO (j + 1) (by omega))
        (jO (j + 2) hj))
      rY
theorem qz
    (z : ℕ → ℤ) (k : ℕ)
    (D1 :
      ∀ j : ℕ, j + 2 < k →
        z (j + 2) - 2 * z (j + 1) + z j = 0) :
    ∀ j : ℕ, j < k →
      z j = z 0 + (j : ℤ) * (z 1 - z 0) := by
  intro j
  induction j using Nat.twoStepInduction with
  | zero =>
      intro
      ring
  | one =>
      intro
      ring
  | more j G9 EV =>
      intro hj
      have Fr : j < k := by omega
      have Fs : j + 1 < k := by omega
      have hs := D1 j hj
      rw [G9 Fr, EV Fs] at hs
      push_cast at hs ⊢
      linarith
theorem vi {k N : ℕ} [NeZero N]
    (a d : ZMod N) (L U : ℤ)
    (jO :
      ∀ j : ℕ, j < k →
        L ≤ bZ a d j ∧ bZ a d j ≤ U)
    (rY : 2 * (U - L) < (N : ℤ)) :
    ∀ j : ℕ, j < k →
      (bZ a d j : ℤ) =
        bZ a d 0 +
          (j : ℤ) *
            ((bZ a d 1 : ℤ) - bZ a d 0) := by
  apply qz
  intro j hj
  exact pY a d L U jO rY j hj
theorem rh {N : ℕ} [NeZero N]
    (a d : ZMod N) (hd : d ≠ 0) :
    (bZ a d 1 : ℤ) - bZ a d 0 ≠ 0 := by
  intro hzero
  have xq : bZ a d 1 = bZ a d 0 := by
    exact_mod_cast sub_eq_zero.mp hzero
  have Ha : a + d = a := by
    apply ZMod.val_injective N
    simpa [bZ] using xq
  apply hd
  apply add_left_cancel (a := a)
  simpa using Ha
theorem uz {k N : ℕ} [NeZero N]
    (a d : ZMod N) (hd : d ≠ 0) (L U : ℤ)
    (jO :
      ∀ j : ℕ, j < k →
        L ≤ bZ a d j ∧ bZ a d j ≤ U)
    (rY : 2 * (U - L) < (N : ℤ)) :
    ∃ s : ℤ, s ≠ 0 ∧
      ∀ j : ℕ, j < k →
        (bZ a d j : ℤ) =
          bZ a d 0 + (j : ℤ) * s := by
  refine ⟨(bZ a d 1 : ℤ) - bZ a d 0,
    rh a d hd, ?_⟩
  exact vi a d L U jO rY
end av.ag
end
section
namespace av.ag
open scoped BigOperators
noncomputable def tK (A : Set ℕ) (n : ℕ) : ℝ :=
  (∑ k ∈ Finset.range (n + 1), A.indicator (fun _ => (1 : ℝ)) k) / (n + 1)
noncomputable def jg (A : Set ℕ) (n : ℕ) : Finset ℕ :=
  by
    classical
    exact (Finset.range (n + 1)).filter (fun k => k ∈ A)
theorem rp (A : Set ℕ) (n : ℕ) :
    tK A n = (jg A n).card / (n + 1 : ℕ) := by
  classical
  simp [tK, jg, Set.indicator]
noncomputable def lL (A : Set ℕ) (n N : ℕ) [NeZero N] : Finset (ZMod N) :=
  by
    classical
    exact Finset.univ.filter fun x => x.val < n + 1 ∧ x.val ∈ A
theorem w8 {A : Set ℕ} {n N : ℕ} [NeZero N]
    (hN : n + 1 ≤ N) :
    (lL A n N).card = (jg A n).card := by
  classical
  symm
  apply Finset.card_bij (fun (x : ℕ) _ => (x : ZMod N))
  · intro x hx
    simp only [jg, lL, Finset.mem_filter] at hx ⊢
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · rw [ZMod.val_natCast_of_lt]
      · exact (Finset.mem_range.mp hx.1)
      · exact (Finset.mem_range.mp hx.1).trans_le hN
    · rw [ZMod.val_natCast_of_lt]
      · exact hx.2
      · exact (Finset.mem_range.mp hx.1).trans_le hN
  · intro x hx y hy u4
    simp only [jg, Finset.mem_filter] at hx hy
    have Hb : x < N := (Finset.mem_range.mp hx.1).trans_le hN
    have Hc : y < N := (Finset.mem_range.mp hy.1).trans_le hN
    have xq := congrArg (ZMod.val : ZMod N → ℕ) u4
    simpa [ZMod.val_natCast_of_lt Hb, ZMod.val_natCast_of_lt Hc] using xq
  · intro z hz
    simp only [lL, Finset.mem_filter] at hz
    refine ⟨z.val, ?_, ?_⟩
    · simp only [jg, Finset.mem_filter]
      exact ⟨Finset.mem_range.mpr hz.2.1, hz.2.2⟩
    · exact ZMod.natCast_zmod_val z
theorem w9 {A : Set ℕ} {n N : ℕ} [NeZero N]
    (hN : n + 1 ≤ N) :
    mean (aN (lL A n N)) =
      tK A n * ((n + 1 : ℕ) / N : ℝ) := by
  rw [iM, w8 hN, rp]
  simp only [ZMod.card]
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  field_simp
theorem mW
    {A : Set ℕ} {k N : ℕ} [NeZero N]
    (a d : ZMod N) (hd : d ≠ 0) (hk : 2 ≤ k)
    (L U : ℤ)
    (wR :
      ∀ j : ℕ, j < k →
        L ≤ bZ a d j ∧ bZ a d j ≤ U)
    (rY : 2 * (U - L) < (N : ℤ))
    (hA : ∀ j : ℕ, j < k → bZ a d j ∈ A) :
    ∃ x step : ℕ, 1 ≤ step ∧
      ∀ j : ℕ, j < k → x + step * j ∈ A := by
  obtain ⟨s, hs, yY⟩ :=
    uz a d hd L U wR rY
  rcases lt_or_gt_of_ne hs with Ft | Fu
  · let step : ℕ := (-s).toNat
    have vL : (step : ℤ) = -s := by
      exact Int.natCast_toNat_eq_self.mpr (neg_nonneg.mpr Ft.le)
    have wS : 0 < step := by omega
    refine ⟨bZ a d (k - 1), step, wS, ?_⟩
    intro j hj
    have hlast : k - 1 < k := by omega
    have Bh : k - 1 - j < k := by omega
    have rT :
        ((k - 1 - j : ℕ) : ℤ) = (k - 1 : ℕ) - (j : ℤ) := by
      omega
    have BI :
        bZ a d (k - 1) + step * j =
          bZ a d (k - 1 - j) := by
      apply Int.ofNat_inj.mp
      push_cast
      rw [vL, yY (k - 1) hlast,
        yY (k - 1 - j) Bh, rT]
      ring
    rw [BI]
    exact hA (k - 1 - j) Bh
  · let step : ℕ := s.toNat
    have vL : (step : ℤ) = s := by
      exact Int.natCast_toNat_eq_self.mpr Fu.le
    have wS : 0 < step := by omega
    refine ⟨bZ a d 0, step, wS, ?_⟩
    intro j hj
    have BI :
        bZ a d 0 + step * j = bZ a d j := by
      apply Int.ofNat_inj.mp
      push_cast
      rw [vL, yY j hj]
      ring
    rw [BI]
    exact hA j hj
end av.ag
end
section
open scoped Topology
open Asymptotics Filter
namespace Erdos142.Am
def xb (k : ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ →
    ∃ yZ : ℕ, 0 < yZ ∧ ∀ N : ℕ, yZ ≤ N → ∀ A : Finset ℕ,
      A ⊆ Finset.Icc 1 N → δ * (N : ℝ) ≤ (A.card : ℝ) →
        ¬(A : Set ℕ).IsAPOfLengthFree k
lemma ss
    (a d k : ℕ) (hd : 0 < d) :
    ENat.card {x : ℕ | ∃ i : ℕ, i < k ∧ x = a + i * d} = k := by
  let f : ℕ → ℕ := fun i ↦ a + i * d
  have hf : Function.Injective f := by
    apply StrictMono.injective
    apply strictMono_nat_of_lt_succ
    intro i
    dsimp [f]
    nlinarith
  have F5 : {x : ℕ | ∃ i : ℕ, i < k ∧ x = a + i * d} =
      f '' {i : ℕ | i < k} := by
    ext x
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, hi, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, hi, rfl⟩
  rw [F5]
  simp only [ENat.card_coe_set_eq, hf.encard_image, Set.Nat.encard_range]
theorem su
    (a d k : ℕ) (hd : 0 < d) :
    Set.IsAPOfLength
      {x : ℕ | ∃ i : ℕ, i < k ∧ x = a + i * d} (k : ℕ∞) := by
  refine ⟨a, d, ss a d k hd, ?_⟩
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, by exact_mod_cast hi, by simp⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, by exact_mod_cast hi, by simp⟩
theorem qA {A : Set ℕ} {k a d : ℕ}
    (hk : 1 < k) (hd : 0 < d)
    (jO : ∀ i < k, a + i * d ∈ A) :
    ¬A.IsAPOfLengthFree k := by
  intro BJ
  let t : Set ℕ := {x | ∃ i : ℕ, i < k ∧ x = a + i * d}
  have ht : t ⊆ A := by
    intro x hx
    rcases hx with ⟨i, hi, rfl⟩
    exact jO i hi
  have Hd : t.IsAPOfLength k := su a d k hd
  have hle := BJ t ht Hd
  have F6 : ¬(k : ℕ∞) ≤ 1 := by exact_mod_cast (not_le.mpr hk)
  exact F6 hle
theorem qV {k : ℕ} (hk : 1 < k) :
    xb k := by
  intro δ fD
  let K : ℕ := max 2 k
  have DD : 2 ≤ K := le_max_left 2 k
  have He : k ≤ K := le_max_right 2 k
  obtain ⟨c, hc, mZ⟩ :=
    av.ag.Cv K DD (by positivity : 0 < δ / 8)
  obtain ⟨m : ℕ, hm : 1 / c < m⟩ := exists_nat_gt (1 / c)
  refine ⟨max 1 m, by simp, ?_⟩
  intro N hN A hA EW
  have Hp : 0 < N := (le_max_left 1 m).trans hN
  let M : ℕ := 4 * (N + 1)
  let : NeZero M := ⟨by dsimp [M]; omega⟩
  have Hf : N + 1 ≤ M := by
    dsimp [M]
    omega
  let S : Finset (ZMod M) :=
    av.ag.lL (A : Set ℕ) N M
  have lk : av.ag.jg (A : Set ℕ) N = A := by
    ext x
    simp only [av.ag.jg, Finset.mem_filter,
      Finset.mem_range]
    constructor
    · exact fun h => h.2
    · intro hx
      have Hg := hA hx
      simp only [Finset.mem_Icc] at Hg
      exact ⟨by omega, hx⟩
  have Fv : δ / 8 ≤
      av.ag.mean
        (av.ag.aN S) := by
    rw [show S = av.ag.lL (A : Set ℕ) N M from rfl,
      av.ag.w9 (A := (A : Set ℕ)) Hf,
      av.ag.rp, lk]
    have EX : (((N + 1 : ℕ) : ℝ) / (M : ℕ)) = 1 / 4 := by
      dsimp [M]
      push_cast
      field_simp
    rw [EX]
    have Hr : N + 1 ≤ 2 * N := by omega
    have oT : (δ / 2) * (N + 1 : ℕ) ≤ δ * (N : ℝ) := by
      calc
        (δ / 2) * (N + 1 : ℕ) ≤ (δ / 2) * (2 * N : ℕ) := by
          gcongr
        _ = δ * (N : ℝ) := by push_cast; ring
    have Gd : δ / 2 ≤ (A.card : ℝ) / (N + 1 : ℕ) := by
      have ur : (0 : ℝ) < (N + 1 : ℕ) := by positivity
      exact (le_div_iff₀ ur).2 (oT.trans EW)
    nlinarith
  have D3 :
      c ≤ av.ag.eU K M
        (av.ag.aN S) :=
    mZ M S Fv
  have Bd : ∀ x : ZMod M,
      0 ≤ av.ag.aN S x := by
    intro x
    unfold av.ag.aN
    split <;> norm_num
  have FK : ∀ x : ZMod M,
      av.ag.aN S x ≤ 1 := by
    intro x
    unfold av.ag.aN
    split <;> norm_num
  have Cx : av.ag.mean
      (av.ag.aN S) ≤ 1 :=
    av.ag.sv FK
  have D4 : 1 / c < (N : ℝ) :=
    hm.trans_le (by exact_mod_cast ((le_max_right 1 m).trans hN))
  have EY : 1 < (M : ℝ) * c := by
    have Bz : 1 < (N : ℝ) * c := (div_lt_iff₀ hc).mp D4
    have F7 : (N : ℝ) ≤ M := by
      exact_mod_cast (show N ≤ M by dsimp [M]; omega)
    exact Bz.trans_le (mul_le_mul_of_nonneg_right F7 hc.le)
  have Dn :
      0 < av.ag.gq K M
        (av.ag.aN S) := by
    apply av.ag.rg
      (by omega) Bd FK
    calc
      1 ^ (K - 1) * av.ag.mean
          (av.ag.aN S) =
          av.ag.mean
            (av.ag.aN S) := by simp
      _ ≤ 1 := Cx
      _ < (M : ℝ) * c := EY
      _ ≤ (M : ℝ) * av.ag.eU K M
          (av.ag.aN S) :=
        mul_le_mul_of_nonneg_left D3 (by positivity)
  obtain ⟨a, d, hd, Cy⟩ :=
    av.ag.qy Bd Dn
  have EZ : ∀ j : ℕ, j < K → a + (j : ZMod M) * d ∈ S := by
    intro j hj
    let jf : Fin K := ⟨j, hj⟩
    have hp := Cy jf
    have jO : av.ag.gK a d jf ∈ S := by
      by_contra hnot
      rw [av.ag.cj hnot] at hp
      linarith
    simpa [av.ag.gK, jf] using jO
  have ze : ∀ j : ℕ, j < K →
      av.ag.bZ a d j < N + 1 ∧
        av.ag.bZ a d j ∈ (A : Set ℕ) := by
    intro j hj
    have jO := EZ j hj
    simpa [S, av.ag.lL,
      av.ag.bZ] using jO
  have wR : ∀ j : ℕ, j < K →
      (0 : ℤ) ≤ av.ag.bZ a d j ∧
        av.ag.bZ a d j ≤ (N : ℤ) := by
    intro j hj
    have jO := ze j hj
    constructor
    · positivity
    · exact_mod_cast (Nat.lt_succ_iff.mp jO.1)
  have rY : 2 * ((N : ℤ) - 0) < (M : ℤ) := by
    dsimp [M]
    omega
  obtain ⟨x, step, ow, An⟩ :=
    av.ag.mW
      a d hd DD 0 N wR rY
      (fun j hj => (ze j hj).2)
  exact qA hk ow
    (fun j hj => by simpa [Nat.mul_comm] using An j (hj.trans_le He))
end Erdos142.Am
namespace Erdos142
end Erdos142
end
section
namespace xl
open Erdos142 Finset
theorem Dp {k : ℕ} (hk : 2 ≤ k) (S : Set ℕ) :
    S.IsAPOfLengthFree k ↔ ∀ a d : ℕ, 0 < d → ¬ (∀ i < k, a + i * d ∈ S) := by
  constructor
  · intro h a d hd yW
    have hinj : Function.Injective (fun i : ℕ => a + i * d) := by
      intro i j hij
      have : i * d = j * d := by simpa using hij
      exact Nat.eq_of_mul_eq_mul_right hd this
    have E0 : Set.IsAPOfLength (((Finset.range k).image (fun i => a + i * d) : Finset ℕ) : Set ℕ) (k : ℕ∞) := by
      refine ⟨a, d, ?_, ?_⟩
      · show Set.encard _ = _
        rw [Set.encard_coe_eq_coe_finsetCard, card_image_of_injective _ hinj, card_range]
      · ext x
        simp [smul_eq_mul]
    have uI : (((Finset.range k).image (fun i => a + i * d) : Finset ℕ) : Set ℕ) ⊆ S := by
      intro x hx
      simp only [coe_image, coe_range, Set.mem_image, Set.mem_Iio] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      exact yW i hi
    have := h _ uI E0
    have : k ≤ 1 := by exact_mod_cast this
    omega
  · intro h t ht E0
    exfalso
    obtain ⟨a, d, fE, heq⟩ := E0
    rcases Nat.eq_zero_or_pos d with hd | hd
    · subst hd
      have : t = {a} := by
        rw [heq]
        ext x
        simp only [smul_zero, add_zero, Set.mem_ofPred_eq, Set.mem_singleton_iff]
        constructor
        · rintro ⟨n, -, rfl⟩
          rfl
        · rintro rfl
          exact ⟨0, by exact_mod_cast (by omega : 0 < k), rfl⟩
      rw [this] at fE
      simp at fE
      have : k = 1 := by exact_mod_cast fE.symm
      omega
    · apply h a d hd
      intro i hi
      apply ht
      rw [heq]
      exact ⟨i, by exact_mod_cast hi, by simp [smul_eq_mul]⟩
end xl
end
section
namespace Erdos142.SzH2
theorem BK {N : ℕ} (hN : 2 ≤ N) : Real.log (Real.log (N : ℝ)) < N := by
  have Hh : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hL : 0 < Real.log (N : ℝ) := Real.log_pos Hh
  have h1 := Real.log_le_sub_one_of_pos hL
  have h2 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < N by linarith)
  linarith
theorem h2 : ∀ k : ℕ, 4 ≤ k → ∀ T : ℝ, ∃ Q : ℝ, ∀ (N : ℕ) (S : Finset ℕ),
    2 ≤ N → S ⊆ Finset.Icc 1 N → 0 < S.card →
    (¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S) →
    max 2 (Real.log (2 * (N : ℝ) / (S.card : ℝ))) ≤ T →
      Real.log (Real.log (N : ℝ)) < Q := by
  intro k hk T
  obtain ⟨yZ, -, Hi⟩ := Erdos142.Am.qV (k := k) (by omega)
    (2 * Real.exp (-T)) (by positivity)
  refine ⟨yZ, fun N S hN hS fE BJ hT => ?_⟩
  have Ez : N < yZ := by
    by_contra! FH
    apply Hi N FH S hS _ ((xl.Dp (by omega) _).2 fun a d hd yW => BJ ⟨a, d, hd, yW⟩)
    have hc : (0 : ℝ) < S.card := by exact_mod_cast fE
    have F8 : Real.log (2 * (N : ℝ) / (S.card : ℝ)) ≤ T := (le_max_right _ _).trans hT
    have lx : 0 < 2 * (N : ℝ) / (S.card : ℝ) := by
      have : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
      positivity
    have F9 := (Real.log_le_iff_le_exp lx).1 F8
    rw [div_le_iff₀ hc] at F9
    have he : Real.exp (-T) * Real.exp T = 1 := by rw [← Real.exp_add]; simp
    have hE : 0 < Real.exp (-T) := Real.exp_pos _
    nlinarith
  calc Real.log (Real.log (N : ℝ)) < N := BK hN
    _ ≤ yZ := by exact_mod_cast Ez.le
end Erdos142.SzH2
end
theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R2_H1_R2.H2 := Erdos142.SzH2.h2
