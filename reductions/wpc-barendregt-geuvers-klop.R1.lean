import OMAStatements.S_wpc_barendregt_geuvers_klop
/- Copyright OpenAI, openai/math@3344da59991ed94f9ba711217b29c1d760badfa6, Apache-2.0. Adapted from lean/OAI/Computability/TypeSystem/{Basic,Reduction,Restriction,Normalization}.lean. Cross-universe transport and two-sided restriction added. -/

namespace OMA

namespace S_wpc_barendregt_geuvers_klop

universe u v w
namespace HasType

variable {S : Type u} {P : Specification S} {Γ : List (Expr S)} {M A : Expr S}

theorem valid (h : HasType P Γ M A) : ValidContext P Γ := by
  induction h with
  | ax _ => exact .nil
  | var h ih => exact .cons ih h
  | weaken _ h _ ih => exact .cons ih h
  | product _ _ _ ih _ => exact ih
  | abstraction _ _ _ ih => exact ih
  | application _ _ ih _ => exact ih
  | conversion _ _ _ ih _ => exact ih

end HasType
namespace Normal

variable {S : Type u}

theorem var (n : Nat) : Normal (.var n : Expr S) := by
  intro N h
  cases h

theorem sort (s : S) : Normal (.sort s) := by
  intro N h
  cases h

theorem stronglyNormalizing {M : Expr S} (h : Normal M) : StronglyNormalizing M :=
  .intro M (fun N hN => False.elim (h N hN))


end Normal
namespace Normal

variable {S : Type u} {M : Expr S}

theorem of_map {f : Expr S → Expr S}
    (hf : ∀ {a b}, Beta a b → Beta (f a) (f b)) (h : Normal (f M)) : Normal M :=
  fun N hN => h (f N) (hf hN)

theorem app_left {f a : Expr S} (h : Normal (.app f a)) : Normal f :=
  of_map Beta.app_left h

theorem app_right {f a : Expr S} (h : Normal (.app f a)) : Normal a :=
  of_map Beta.app_right h

theorem lam_domain {A b : Expr S} (h : Normal (.lam A b)) : Normal A :=
  of_map Beta.lam_domain h

theorem lam_body {A b : Expr S} (h : Normal (.lam A b)) : Normal b :=
  of_map Beta.lam_body h

theorem pi_domain {A B : Expr S} (h : Normal (.pi A B)) : Normal A :=
  of_map Beta.pi_domain h

theorem pi_body {A B : Expr S} (h : Normal (.pi A B)) : Normal B :=
  of_map Beta.pi_body h

theorem pi {A B : Expr S} (hA : Normal A) (hB : Normal B) : Normal (.pi A B) := by
  intro N h
  cases h with
  | pi_domain h => exact hA _ h
  | pi_body h => exact hB _ h

theorem lam {A b : Expr S} (hA : Normal A) (hb : Normal b) : Normal (.lam A b) := by
  intro N h
  cases h with
  | lam_domain h => exact hA _ h
  | lam_body h => exact hb _ h


end Normal


namespace Expr

variable {S : Type u} {T : Type v} {U : Type w}

@[simp] theorem mapSort_id (M : Expr S) : (Expr.rec (motive := fun _ => Expr _) Expr.var (fun a => Expr.sort (id a)) (fun _ _ => Expr.app) (fun _ _ => Expr.lam) (fun _ _ => Expr.pi)) M = M := by
  induction M <;> simp_all only [id_eq]

@[simp] theorem mapSort_comp (M : Expr S) (f : S → T) (g : T → U) :
    (Expr.rec (motive := fun _ => Expr _) Expr.var (fun a => Expr.sort (g a)) (fun _ _ => Expr.app) (fun _ _ => Expr.lam) (fun _ _ => Expr.pi)) ((Expr.rec (motive := fun _ => Expr _) Expr.var (fun a => Expr.sort (f a)) (fun _ _ => Expr.app) (fun _ _ => Expr.lam) (fun _ _ => Expr.pi)) M) = (Expr.rec (motive := fun _ => Expr _) Expr.var (fun a => Expr.sort ((g ∘ f) a)) (fun _ _ => Expr.app) (fun _ _ => Expr.lam) (fun _ _ => Expr.pi)) M := by
  induction M <;> simp_all only [Function.comp_apply]

@[simp] theorem mapSort_rename (M : Expr S) (f : S → T) (ρ : Nat → Nat) :
    (Expr.rec (motive := fun _ => Expr _) Expr.var (fun a => Expr.sort (f a)) (fun _ _ => Expr.app) (fun _ _ => Expr.lam) (fun _ _ => Expr.pi)) (M.rename ρ) = ((Expr.rec (motive := fun _ => Expr _) Expr.var (fun a => Expr.sort (f a)) (fun _ _ => Expr.app) (fun _ _ => Expr.lam) (fun _ _ => Expr.pi)) M).rename ρ := by
  induction M generalizing ρ <;> simp_all only [rename]

@[simp] theorem mapSort_liftSub (f : S → T) (σ : Nat → Expr S) :
    (Expr.rec (motive := fun _ => Expr _) Expr.var (fun a => Expr.sort (f a)) (fun _ _ => Expr.app) (fun _ _ => Expr.lam) (fun _ _ => Expr.pi)) ∘ liftSub σ = liftSub ((Expr.rec (motive := fun _ => Expr _) Expr.var (fun a => Expr.sort (f a)) (fun _ _ => Expr.app) (fun _ _ => Expr.lam) (fun _ _ => Expr.pi)) ∘ σ) := by
  funext n
  cases n <;> simp only [Function.comp_apply, liftSub, mapSort_rename]

@[simp] theorem mapSort_subst (M : Expr S) (f : S → T) (σ : Nat → Expr S) :
    (Expr.rec (motive := fun _ => Expr _) Expr.var (fun a => Expr.sort (f a)) (fun _ _ => Expr.app) (fun _ _ => Expr.lam) (fun _ _ => Expr.pi)) (M.subst σ) = ((Expr.rec (motive := fun _ => Expr _) Expr.var (fun a => Expr.sort (f a)) (fun _ _ => Expr.app) (fun _ _ => Expr.lam) (fun _ _ => Expr.pi)) M).subst ((Expr.rec (motive := fun _ => Expr _) Expr.var (fun a => Expr.sort (f a)) (fun _ _ => Expr.app) (fun _ _ => Expr.lam) (fun _ _ => Expr.pi)) ∘ σ) := by
  induction M generalizing σ <;>
    simp_all only [subst, Function.comp_apply, mapSort_liftSub]

@[simp] theorem mapSort_single (f : S → T) (a : Expr S) :
    (Expr.rec (motive := fun _ => Expr _) Expr.var (fun a => Expr.sort (f a)) (fun _ _ => Expr.app) (fun _ _ => Expr.lam) (fun _ _ => Expr.pi)) ∘ single a = single ((Expr.rec (motive := fun _ => Expr _) Expr.var (fun a => Expr.sort (f a)) (fun _ _ => Expr.app) (fun _ _ => Expr.lam) (fun _ _ => Expr.pi)) a) := by
  funext n
  cases n <;> rfl

@[simp] theorem mapSort_instantiate (b a : Expr S) (f : S → T) :
    (Expr.rec (motive := fun _ => Expr _) Expr.var (fun a => Expr.sort (f a)) (fun _ _ => Expr.app) (fun _ _ => Expr.lam) (fun _ _ => Expr.pi)) (b.instantiate a) = ((Expr.rec (motive := fun _ => Expr _) Expr.var (fun a => Expr.sort (f a)) (fun _ _ => Expr.app) (fun _ _ => Expr.lam) (fun _ _ => Expr.pi)) b).instantiate ((Expr.rec (motive := fun _ => Expr _) Expr.var (fun a => Expr.sort (f a)) (fun _ _ => Expr.app) (fun _ _ => Expr.lam) (fun _ _ => Expr.pi)) a) := by
  simp only [instantiate, mapSort_subst, mapSort_single]

end Expr

namespace Beta

variable {S : Type u} {T : Type v} {M N : Expr S}

theorem mapSort (h : Beta M N) (f : S → T) : Beta ((Expr.rec (motive := fun _ => Expr _) Expr.var (fun a => Expr.sort (f a)) (fun _ _ => Expr.app) (fun _ _ => Expr.lam) (fun _ _ => Expr.pi)) M) ((Expr.rec (motive := fun _ => Expr _) Expr.var (fun a => Expr.sort (f a)) (fun _ _ => Expr.app) (fun _ _ => Expr.lam) (fun _ _ => Expr.pi)) N) := by
  induction h with
  | head A b a =>
      simpa only [Expr.mapSort_instantiate] using
        (Beta.head ((Expr.rec (motive := fun _ => Expr _) Expr.var (fun a => Expr.sort (f a)) (fun _ _ => Expr.app) (fun _ _ => Expr.lam) (fun _ _ => Expr.pi)) A) ((Expr.rec (motive := fun _ => Expr _) Expr.var (fun a => Expr.sort (f a)) (fun _ _ => Expr.app) (fun _ _ => Expr.lam) (fun _ _ => Expr.pi)) b) ((Expr.rec (motive := fun _ => Expr _) Expr.var (fun a => Expr.sort (f a)) (fun _ _ => Expr.app) (fun _ _ => Expr.lam) (fun _ _ => Expr.pi)) a))
  | app_left _ ih => exact .app_left ih
  | app_right _ ih => exact .app_right ih
  | lam_domain _ ih => exact .lam_domain ih
  | lam_body _ ih => exact .lam_body ih
  | pi_domain _ ih => exact .pi_domain ih
  | pi_body _ ih => exact .pi_body ih

end Beta

namespace Reduces

variable {S : Type u} {T : Type v} {M N : Expr S}

theorem mapSort (h : Relation.ReflTransGen Beta M N) (f : S → T) : Relation.ReflTransGen Beta ((Expr.rec (motive := fun _ => Expr _) Expr.var (fun a => Expr.sort (f a)) (fun _ _ => Expr.app) (fun _ _ => Expr.lam) (fun _ _ => Expr.pi)) M) ((Expr.rec (motive := fun _ => Expr _) Expr.var (fun a => Expr.sort (f a)) (fun _ _ => Expr.app) (fun _ _ => Expr.lam) (fun _ _ => Expr.pi)) N) :=
  h.lift ((Expr.rec (motive := fun _ => Expr _) Expr.var (fun a => Expr.sort (f a)) (fun _ _ => Expr.app) (fun _ _ => Expr.lam) (fun _ _ => Expr.pi))) (fun _ _ h => h.mapSort f)

end Reduces

namespace Converts

variable {S : Type u} {T : Type v} {M N : Expr S}

theorem mapSort (h : Converts M N) (f : S → T) : Converts ((Expr.rec (motive := fun _ => Expr _) Expr.var (fun a => Expr.sort (f a)) (fun _ _ => Expr.app) (fun _ _ => Expr.lam) (fun _ _ => Expr.pi)) M) ((Expr.rec (motive := fun _ => Expr _) Expr.var (fun a => Expr.sort (f a)) (fun _ _ => Expr.app) (fun _ _ => Expr.lam) (fun _ _ => Expr.pi)) N) := by
  induction h with
  | rel _ _ h => exact .rel _ _ (h.mapSort f)
  | refl _ => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂

end Converts

namespace Normal

variable {S : Type u} {T : Type v}

theorem mapSort {M : Expr S} (h : Normal M) (f : S → T) : Normal ((Expr.rec (motive := fun _ => Expr _) Expr.var (fun a => Expr.sort (f a)) (fun _ _ => Expr.app) (fun _ _ => Expr.lam) (fun _ _ => Expr.pi)) M) := by
  induction M with
  | var n => exact Normal.var _
  | sort s => exact Normal.sort _
  | pi A B ihA ihB => exact (ihA h.pi_domain).pi (ihB h.pi_body)
  | lam A b ihA ihb => exact (ihA h.lam_domain).lam (ihb h.lam_body)
  | app M a ihM iha =>
      have hM := ihM h.app_left
      have ha := iha h.app_right
      cases M with
      | lam D b => exact False.elim (h _ (.head D b a))
      | var n | sort s | app M b | pi D B =>
          intro N hN
          cases hN with
          | app_left hr => exact hM _ hr
          | app_right hr => exact ha _ hr

end Normal

namespace StronglyNormalizing

variable {S : Type u} {T : Type v}

theorem of_mapSort (f : S → T) {M : Expr S} (h : StronglyNormalizing ((Expr.rec (motive := fun _ => Expr _) Expr.var (fun a => Expr.sort (f a)) (fun _ _ => Expr.app) (fun _ _ => Expr.lam) (fun _ _ => Expr.pi)) M)) :
    StronglyNormalizing M := by
  have aux : ∀ N : Expr T, StronglyNormalizing N →
      ∀ M : Expr S, (Expr.rec (motive := fun _ => Expr _) Expr.var (fun a => Expr.sort (f a)) (fun _ _ => Expr.app) (fun _ _ => Expr.lam) (fun _ _ => Expr.pi)) M = N → StronglyNormalizing M := by
    intro N hN
    induction hN with
    | intro N hN ih =>
        intro M he
        subst N
        refine Acc.intro M ?_
        intro M' hM'
        exact ih ((Expr.rec (motive := fun _ => Expr _) Expr.var (fun a => Expr.sort (f a)) (fun _ _ => Expr.app) (fun _ _ => Expr.lam) (fun _ _ => Expr.pi)) M') (hM'.mapSort f) M' rfl
  exact aux _ h M rfl

end StronglyNormalizing

namespace WeaklyNormalizing

variable {S : Type u} {T : Type v}

theorem mapSort {M : Expr S} (h : WeaklyNormalizing M) (f : S → T) :
    WeaklyNormalizing ((Expr.rec (motive := fun _ => Expr _) Expr.var (fun a => Expr.sort (f a)) (fun _ _ => Expr.app) (fun _ _ => Expr.lam) (fun _ _ => Expr.pi)) M) := by
  obtain ⟨N, hr, hn⟩ := h
  exact ⟨(Expr.rec (motive := fun _ => Expr _) Expr.var (fun a => Expr.sort (f a)) (fun _ _ => Expr.app) (fun _ _ => Expr.lam) (fun _ _ => Expr.pi)) N, Reduces.mapSort hr f, hn.mapSort f⟩

theorem of_retraction (f : S → T) (g : T → S) (hfg : Function.LeftInverse g f)
    {M : Expr S} (h : WeaklyNormalizing ((Expr.rec (motive := fun _ => Expr _) Expr.var (fun a => Expr.sort (f a)) (fun _ _ => Expr.app) (fun _ _ => Expr.lam) (fun _ _ => Expr.pi)) M)) : WeaklyNormalizing M := by
  have he : g ∘ f = id := funext hfg
  simpa only [Expr.mapSort_comp, he, Expr.mapSort_id] using h.mapSort g

end WeaklyNormalizing

namespace HasType

variable {S : Type u} {T : Type v} {P Q : Specification S}

theorem monotone {Γ : List (Expr S)} {M A : Expr S} (h : HasType P Γ M A)
    (ha : ∀ s t, P.sortAxioms s t → Q.sortAxioms s t)
    (hr : ∀ a b c, P.rule a b c → Q.rule a b c) : HasType Q Γ M A := by
  induction h with
  | ax h => exact .ax (ha _ _ h)
  | var _ ih => exact .var ih
  | weaken _ _ ihM ihA => exact .weaken ihM ihA
  | product _ _ h ihA ihB => exact .product ihA ihB (hr _ _ _ h)
  | abstraction _ _ ihb ihPi => exact .abstraction ihb ihPi
  | application _ _ ihf iha => exact .application ihf iha
  | conversion _ _ hc ihM ihA => exact .conversion ihM ihA hc

theorem mapSort {Q : Specification T} {Γ : List (Expr S)} {M A : Expr S}
    (h : HasType P Γ M A) (f : S → T)
    (ha : ∀ s t, P.sortAxioms s t → Q.sortAxioms (f s) (f t))
    (hr : ∀ a b c, P.rule a b c → Q.rule (f a) (f b) (f c)) :
    HasType Q (Γ.map ((Expr.rec (motive := fun _ => Expr _) Expr.var (fun a => Expr.sort (f a)) (fun _ _ => Expr.app) (fun _ _ => Expr.lam) (fun _ _ => Expr.pi)))) ((Expr.rec (motive := fun _ => Expr _) Expr.var (fun a => Expr.sort (f a)) (fun _ _ => Expr.app) (fun _ _ => Expr.lam) (fun _ _ => Expr.pi)) M) ((Expr.rec (motive := fun _ => Expr _) Expr.var (fun a => Expr.sort (f a)) (fun _ _ => Expr.app) (fun _ _ => Expr.lam) (fun _ _ => Expr.pi)) A) := by
  induction h with
  | ax h => exact .ax (ha _ _ h)
  | var _ ih => simpa only [List.map_cons, Expr.mapSort_rename] using HasType.var ih
  | weaken _ _ ihM ihA =>
      simpa only [List.map_cons, Expr.mapSort_rename] using HasType.weaken ihM ihA
  | product _ _ h ihA ihB => exact .product ihA ihB (hr _ _ _ h)
  | abstraction _ _ ihb ihPi => exact .abstraction ihb ihPi
  | application _ _ ihf iha =>
      simpa only [Expr.mapSort_instantiate] using HasType.application ihf iha
  | conversion _ _ hc ihM ihA => exact .conversion ihM ihA (hc.mapSort f)

theorem has_axiom {Γ : List (Expr S)} {M A : Expr S} (h : HasType P Γ M A) :
    ∃ s t, P.sortAxioms s t := by
  induction h with
  | ax h => exact ⟨_, _, h⟩
  | var _ ih => exact ih
  | weaken _ _ ih _ => exact ih
  | product _ _ _ ih _ => exact ih
  | abstraction _ _ ih _ => exact ih
  | application _ _ ih _ => exact ih
  | conversion _ _ _ ih _ => exact ih

end HasType



namespace HasType

variable {S : Type u} {P : Specification S} {Γ : List (Expr S)} {M T : Expr S}

theorem restrict_mono {A A' : Finset (S × S)} {R R' : Finset (S × S × S)}
    (h : HasType ((⟨fun s t => P.sortAxioms s t ∧ (s,t) ∈ A, fun a b c => P.rule a b c ∧ (a,b,c) ∈ R⟩ : Specification S)) Γ M T) (hA : A ⊆ A') (hR : R ⊆ R') :
    HasType ((⟨fun s t => P.sortAxioms s t ∧ (s,t) ∈ A', fun a b c => P.rule a b c ∧ (a,b,c) ∈ R'⟩ : Specification S)) Γ M T :=
  h.monotone (fun _ _ h => ⟨h.1, hA h.2⟩) (fun _ _ _ h => ⟨h.1, hR h.2⟩)

theorem finite_support (h : HasType P Γ M T) :
    ∃ A : Finset (S × S), ∃ R : Finset (S × S × S), HasType ((⟨fun s t => P.sortAxioms s t ∧ (s,t) ∈ A, fun a b c => P.rule a b c ∧ (a,b,c) ∈ R⟩ : Specification S)) Γ M T := by
  classical
  induction h with
  | ax h => exact ⟨{(_,_)}, ∅, .ax ⟨h, Finset.mem_singleton_self _⟩⟩
  | var _ ih =>
      obtain ⟨A, R, ht⟩ := ih
      exact ⟨A, R, .var ht⟩
  | weaken _ _ ihM ihA =>
      obtain ⟨A, R, hM⟩ := ihM
      obtain ⟨A', R', hA⟩ := ihA
      exact ⟨A ∪ A', R ∪ R', .weaken
        (hM.restrict_mono Finset.subset_union_left Finset.subset_union_left)
        (hA.restrict_mono Finset.subset_union_right Finset.subset_union_right)⟩
  | @product Γ D E a b c _ _ hr ihD ihE =>
      obtain ⟨A, R, hD⟩ := ihD
      obtain ⟨A', R', hE⟩ := ihE
      refine ⟨A ∪ A', insert (a,b,c) (R ∪ R'), .product
        (hD.restrict_mono Finset.subset_union_left
          (Finset.subset_union_left.trans (Finset.subset_insert _ _)))
        (hE.restrict_mono Finset.subset_union_right
          (Finset.subset_union_right.trans (Finset.subset_insert _ _))) ?_⟩
      exact ⟨hr, Finset.mem_insert_self _ _⟩
  | abstraction _ _ ihb ihPi =>
      obtain ⟨A, R, hb⟩ := ihb
      obtain ⟨A', R', hPi⟩ := ihPi
      exact ⟨A ∪ A', R ∪ R', .abstraction
        (hb.restrict_mono Finset.subset_union_left Finset.subset_union_left)
        (hPi.restrict_mono Finset.subset_union_right Finset.subset_union_right)⟩
  | application _ _ ihf iha =>
      obtain ⟨A, R, hf⟩ := ihf
      obtain ⟨A', R', ha⟩ := iha
      exact ⟨A ∪ A', R ∪ R', .application
        (hf.restrict_mono Finset.subset_union_left Finset.subset_union_left)
        (ha.restrict_mono Finset.subset_union_right Finset.subset_union_right)⟩
  | conversion _ _ hc ihM ihT =>
      obtain ⟨A, R, hM⟩ := ihM
      obtain ⟨A', R', hT⟩ := ihT
      exact ⟨A ∪ A', R ∪ R', .conversion
        (hM.restrict_mono Finset.subset_union_left Finset.subset_union_left)
        (hT.restrict_mono Finset.subset_union_right Finset.subset_union_right) hc⟩

end HasType

namespace SystemWeaklyNormalizing

variable {S : Type u} {P : Specification S}

theorem on {D : Set S} (hw : SystemWeaklyNormalizing P) (d₀ : D) :
    SystemWeaklyNormalizing ((⟨fun s t => P.sortAxioms s.val t.val, fun a b c => P.rule a.val b.val c.val⟩ : Specification D)) := by
  classical
  let f : S → D := fun s => if h : s ∈ D then ⟨s,h⟩ else d₀
  have hf : Function.LeftInverse f Subtype.val := by
    intro s
    apply Subtype.ext
    simp only [f, dif_pos s.property]
  intro Γ _ M hM
  obtain ⟨A, h | h⟩ := hM
  · have ht := h.mapSort Subtype.val (fun _ _ h => h) (fun _ _ _ h => h)
    exact WeaklyNormalizing.of_retraction Subtype.val f hf
      (hw _ ht.valid _ ⟨_, Or.inl ht⟩)
  · have ht := h.mapSort Subtype.val (fun _ _ h => h) (fun _ _ _ h => h)
    exact WeaklyNormalizing.of_retraction Subtype.val f hf
      (hw _ ht.valid _ ⟨_, Or.inr ht⟩)

end SystemWeaklyNormalizing

namespace HasType

variable {S : Type u} {P : Specification S} {Γ : List (Expr S)} {M T : Expr S}

/-- A non-strongly-normalizing typed term has a counterexample over a finite
subspecification. No normalization conclusion for that finite PTS is assumed. -/
theorem finite_counterexample (h : HasType P Γ M T) (hn : ¬ StronglyNormalizing M ∨ ¬ StronglyNormalizing T)
    (hw : SystemWeaklyNormalizing P) :
    ∃ D : Finset S, ∃ Γ' : List (Expr {s // s ∈ D}),
      ∃ M' T' : Expr {s // s ∈ D},
        HasType (⟨fun s t => P.sortAxioms s.val t.val, fun a b c => P.rule a.val b.val c.val⟩ : Specification {s // s ∈ D}) Γ' M' T' ∧ (¬ StronglyNormalizing M' ∨ ¬ StronglyNormalizing T') ∧
          SystemWeaklyNormalizing (⟨fun s t => P.sortAxioms s.val t.val, fun a b c => P.rule a.val b.val c.val⟩ : Specification {s // s ∈ D}) := by
  classical
  obtain ⟨A, R, hr⟩ := h.finite_support
  let D := A.biUnion (fun a => {a.1, a.2}) ∪
    R.biUnion (fun r => {r.1, r.2.1, r.2.2})
  have ax_mem {s t : S} (h : (s,t) ∈ A) : s ∈ D ∧ t ∈ D := by
    constructor
    · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨(s,t), h, by simp⟩)
    · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨(s,t), h, by simp⟩)
  have rule_mem {a b c : S} (h : (a,b,c) ∈ R) : a ∈ D ∧ b ∈ D ∧ c ∈ D := by
    constructor
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨(a,b,c), h, by simp⟩)
    constructor
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨(a,b,c), h, by simp⟩)
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨(a,b,c), h, by simp⟩)
  obtain ⟨s₀, t₀, h₀⟩ := hr.has_axiom
  let d₀ : {s // s ∈ D} := ⟨s₀, (ax_mem h₀.2).1⟩
  let f : S → {s // s ∈ D} := fun s => if h : s ∈ D then ⟨s,h⟩ else d₀
  have f_val {s : S} (h : s ∈ D) : (f s).val = s := by
    simp only [f, dif_pos h]
  have ha : ∀ s t, ((⟨fun s t => P.sortAxioms s t ∧ (s,t) ∈ A, fun a b c => P.rule a b c ∧ (a,b,c) ∈ R⟩ : Specification S)).sortAxioms s t →
      (⟨fun s t => P.sortAxioms s.val t.val, fun a b c => P.rule a.val b.val c.val⟩ : Specification {s // s ∈ D}).sortAxioms (f s) (f t) := by
    intro s t hst
    change P.sortAxioms (f s).val (f t).val
    rw [f_val (ax_mem hst.2).1, f_val (ax_mem hst.2).2]
    exact hst.1
  have hp : ∀ a b c, ((⟨fun s t => P.sortAxioms s t ∧ (s,t) ∈ A, fun a b c => P.rule a b c ∧ (a,b,c) ∈ R⟩ : Specification S)).rule a b c →
      (⟨fun s t => P.sortAxioms s.val t.val, fun a b c => P.rule a.val b.val c.val⟩ : Specification {s // s ∈ D}).rule (f a) (f b) (f c) := by
    intro a b c habc
    change P.rule (f a).val (f b).val (f c).val
    rw [f_val (rule_mem habc.2).1, f_val (rule_mem habc.2).2.1,
      f_val (rule_mem habc.2).2.2]
    exact habc.1
  exact ⟨D, _, _, _, hr.mapSort f ha hp,
    hn.imp (fun h hs => h (StronglyNormalizing.of_mapSort f hs)) (fun h hs => h (StronglyNormalizing.of_mapSort f hs)), hw.on d₀⟩

end HasType

end S_wpc_barendregt_geuvers_klop

end OMA

namespace OMA.S_wpc_barendregt_geuvers_klop
universe u v
theorem small_bad {S : Type u} (P : Specification S) (hw : SystemWeaklyNormalizing P)
    (hn : ¬ SystemStronglyNormalizing P) :
    ∃ n, ∃ Q : Specification (Fin n), SystemWeaklyNormalizing Q ∧ ¬ SystemStronglyNormalizing Q := by
  classical
  have witness : ∃ Γ M T, HasType P Γ M T ∧ (¬ StronglyNormalizing M ∨ ¬ StronglyNormalizing T) := by
    by_contra! good
    apply hn
    intro Γ _ M h
    obtain ⟨A,h | h⟩ := h
    · exact (good Γ M A h).1
    · exact (good Γ A M h).2
  obtain ⟨Γ,M₀,T₀,ht₀,bad⟩ := witness
  obtain ⟨F,Γ',M,T,ht,hm,hw'⟩ := ht₀.finite_counterexample bad hw
  let e := Fintype.equivFin {s // s ∈ F}
  let R := (⟨fun s t => P.sortAxioms s.val t.val, fun a b c => P.rule a.val b.val c.val⟩ : Specification {s // s ∈ F})
  let Q : Specification (Fin _) := ⟨fun a b => R.sortAxioms (e.symm a) (e.symm b), fun a b c => R.rule (e.symm a) (e.symm b) (e.symm c)⟩
  refine ⟨_, Q, ?_, ?_⟩
  · intro Δ _ t leg
    obtain ⟨A, h | h⟩ := leg
    · have h' := h.mapSort (Q := R) e.symm (fun _ _ h => h) (fun _ _ _ h => h)
      exact WeaklyNormalizing.of_retraction e.symm e e.apply_symm_apply (hw' _ h'.valid _ ⟨_, Or.inl h'⟩)
    · have h' := h.mapSort (Q := R) e.symm (fun _ _ h => h) (fun _ _ _ h => h)
      exact WeaklyNormalizing.of_retraction e.symm e e.apply_symm_apply (hw' _ h'.valid _ ⟨_, Or.inr h'⟩)
  · intro hs
    have ht' := ht.mapSort (Q := Q) e (by intro x y h; simpa [Q,R] using h) (by intro x y z h; simpa [Q,R] using h)
    rcases hm with h | h
    · exact h (StronglyNormalizing.of_mapSort e (hs _ ht'.valid _ ⟨_, Or.inl ht'⟩))
    · exact h (StronglyNormalizing.of_mapSort e (hs _ ht'.valid _ ⟨_, Or.inr ht'⟩))

end OMA.S_wpc_barendregt_geuvers_klop

namespace OMA.R_wpc_barendregt_geuvers_klop_R1
open OMA.S_wpc_barendregt_geuvers_klop

def H1 : Prop := ∀ n (P : Specification (Fin n)), ¬ SystemStronglyNormalizing P →
  ∃ Γ f a D E, HasType P Γ f (.pi D E) ∧ HasType P Γ a D ∧ StronglyNormalizing f ∧ StronglyNormalizing a ∧ ¬ StronglyNormalizing (.app f a)

def H2 : Prop := ∀ n (P : Specification (Fin n)), SystemWeaklyNormalizing P → ∀ Γ f a D E, HasType P Γ f (.pi D E) → HasType P Γ a D → StronglyNormalizing f → StronglyNormalizing a → StronglyNormalizing (.app f a)

theorem main : H1 → H2 → type_of% @OMA.S_wpc_barendregt_geuvers_klop.main := by
  intro witness app S P hw
  by_contra hn
  obtain ⟨n,Q,hq,hb⟩ := small_bad P hw hn
  obtain ⟨Γ,f,a,D,E,hf,ha,sf,sa,no⟩ := witness n Q hb
  exact no (app n Q hq Γ f a D E hf ha sf sa)
end OMA.R_wpc_barendregt_geuvers_klop_R1
