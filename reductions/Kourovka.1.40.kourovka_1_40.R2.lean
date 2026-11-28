import FormalConjectures.Kourovka.«1_40»

/-!
# Kourovka 1.40: the nilpotent case via Fitting's theorem

Proved here: Fitting's theorem (lemma `fitting_class`): if `H, K` are normal subgroups of `G`
with `H ⊔ K = ⊤` and `H.lowerCentralSeries c = ⊥`, `K.lowerCentralSeries d = ⊥`, then
`(⊤ : Subgroup G).lowerCentralSeries (c + d) = ⊥`. Hence `G` is nilpotent, hence Engel.
Also proved (`direct_case`): if `H ⊓ K = ⊥` then `G ≅ H × K` and `G` is Engel.
Open residue (always with `H ⊓ K ≠ ⊥`): H1, neither factor nilpotent; H2, the mixed case
`H` nilpotent and `K` not (the other mixed case follows by symmetry).
-/

namespace OMA.R_Kourovka_1_40_kourovka_1_40_R2

open Kourovka.«1.40» Subgroup
open scoped commutatorElement

def H1 : Prop :=
  ∀ (G : Type) [Group G] (H K : Subgroup G),
    H.Normal → K.Normal → IsEngelGroup H → IsEngelGroup K → H ⊔ K = ⊤ →
    ¬ Group.IsNilpotent H → ¬ Group.IsNilpotent K → H ⊓ K ≠ ⊥ → IsEngelGroup G

def H2 : Prop :=
  ∀ (G : Type) [Group G] (H K : Subgroup G),
    H.Normal → K.Normal → IsEngelGroup H → IsEngelGroup K → H ⊔ K = ⊤ →
    Group.IsNilpotent H → ¬ Group.IsNilpotent K → H ⊓ K ≠ ⊥ → IsEngelGroup G

variable {G : Type*} [Group G]

lemma lcs_normal (H : Subgroup G) [H.Normal] : ∀ n, (H.lowerCentralSeries n).Normal
  | 0 => inferInstance
  | n + 1 => by
    rw [Subgroup.lowerCentralSeries_succ]
    have := lcs_normal H n
    infer_instance

lemma comm_iSup_le {ι : Sort*} (S : ι → Subgroup G) (Y Z : Subgroup G) [hZ : Z.Normal]
    (h : ∀ i, ⁅S i, Y⁆ ≤ Z) : ⁅⨆ i, S i, Y⁆ ≤ Z := by
  rw [commutator_le]
  intro x hx y hy
  refine iSup_induction S (C := fun x => ⁅x, y⁆ ∈ Z) hx ?_ ?_ ?_
  · intro i x hx
    exact commutator_le.mp (h i) x hx y hy
  · simp
  · intro x x' hx hx'
    have e : ⁅x * x', y⁆ = (x * ⁅x', y⁆ * x⁻¹) * ⁅x, y⁆ := by group
    rw [e]
    exact mul_mem (hZ.conj_mem _ hx' x) hx

lemma comm_sup_le (X A B Z : Subgroup G) [Z.Normal]
    (hA : ⁅X, A⁆ ≤ Z) (hB : ⁅X, B⁆ ≤ Z) : ⁅X, A ⊔ B⁆ ≤ Z := by
  rw [commutator_comm, show A ⊔ B = ⨆ b : Bool, cond b A B from by rw [iSup_bool_eq]; rfl]
  refine comm_iSup_le _ X Z ?_
  intro b
  cases b
  · rw [commutator_comm]; exact hB
  · rw [commutator_comm]; exact hA

lemma fitting_core (H K : Subgroup G) [H.Normal] [K.Normal] (hHK : H ⊔ K = ⊤)
    (Hs Ks : ℕ → Subgroup G) (hHn : ∀ a, (Hs a).Normal) (hKn : ∀ b, (Ks b).Normal)
    (hH : ∀ a, ⁅Hs a, H⁆ ≤ Hs (a + 1)) (hK : ∀ b, ⁅Ks b, K⁆ ≤ Ks (b + 1))
    (h0 : ⊤ ≤ ⨆ p : {p : ℕ × ℕ // p.1 + p.2 = 1}, Hs p.1.1 ⊓ Ks p.1.2) :
    ∀ n, (⊤ : Subgroup G).lowerCentralSeries n ≤
      ⨆ p : {p : ℕ × ℕ // p.1 + p.2 = n + 1}, Hs p.1.1 ⊓ Ks p.1.2
  | 0 => h0
  | n + 1 => by
    rw [Subgroup.lowerCentralSeries_succ]
    refine (commutator_mono (fitting_core H K hHK Hs Ks hHn hKn hH hK h0 n) le_rfl).trans ?_
    have : ∀ p : {p : ℕ × ℕ // p.1 + p.2 = n + 1 + 1}, (Hs p.1.1 ⊓ Ks p.1.2).Normal :=
      fun p => by have := hHn p.1.1; have := hKn p.1.2; infer_instance
    rw [← hHK]
    apply comm_sup_le
    · refine comm_iSup_le _ H _ ?_
      intro p
      have := hKn p.1.2
      have hle : ⁅Hs p.1.1 ⊓ Ks p.1.2, H⁆ ≤ Hs (p.1.1 + 1) ⊓ Ks p.1.2 :=
        le_inf ((commutator_mono inf_le_left le_rfl).trans (hH _))
          ((commutator_mono inf_le_right le_rfl).trans (commutator_le_left _ _))
      exact hle.trans (le_iSup_of_le
        (f := fun p : {p : ℕ × ℕ // p.1 + p.2 = n + 1 + 1} => Hs p.1.1 ⊓ Ks p.1.2)
        ⟨(p.1.1 + 1, p.1.2), by have := p.2; simp only at this ⊢; omega⟩ le_rfl)
    · refine comm_iSup_le _ K _ ?_
      intro p
      have := hHn p.1.1
      have hle : ⁅Hs p.1.1 ⊓ Ks p.1.2, K⁆ ≤ Hs p.1.1 ⊓ Ks (p.1.2 + 1) :=
        le_inf ((commutator_mono inf_le_left le_rfl).trans (commutator_le_left _ _))
          ((commutator_mono inf_le_right le_rfl).trans (hK _))
      exact hle.trans (le_iSup_of_le
        (f := fun p : {p : ℕ × ℕ // p.1 + p.2 = n + 1 + 1} => Hs p.1.1 ⊓ Ks p.1.2)
        ⟨(p.1.1, p.1.2 + 1), by have := p.2; simp only at this ⊢; omega⟩ le_rfl)

/-- The shifted series: `⊤, H, ⁅H, H⁆, ...`. -/
lemma shifted (H : Subgroup G) [H.Normal] :
    ∃ Hs : ℕ → Subgroup G, (∀ a, (Hs a).Normal) ∧ (∀ a, ⁅Hs a, H⁆ ≤ Hs (a + 1)) ∧
      Hs 0 = ⊤ ∧ ∀ a, Hs (a + 1) = H.lowerCentralSeries a := by
  refine ⟨fun a => if a = 0 then ⊤ else H.lowerCentralSeries (a - 1), ?_, ?_, ?_, ?_⟩
  · intro a
    by_cases h : a = 0
    · simp only [h, if_true]; infer_instance
    · simp only [h, if_false]; exact lcs_normal H _
  · intro a
    rcases a with _ | a
    · simp only [if_true, Nat.add_one_ne_zero, if_false, zero_add]
      exact commutator_le_right _ _
    · simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
      exact le_of_eq (Subgroup.lowerCentralSeries_succ H a).symm
  · simp
  · intro a; simp

/-- Fitting's theorem (1938), with Fitting's class bound `c + d`. -/
theorem fitting_class (H K : Subgroup G) [H.Normal] [K.Normal] (hHK : H ⊔ K = ⊤)
    (c d : ℕ) (hc : H.lowerCentralSeries c = ⊥) (hd : K.lowerCentralSeries d = ⊥) :
    (⊤ : Subgroup G).lowerCentralSeries (c + d) = ⊥ := by
  obtain ⟨Hs, hHn, hH, hH0, hH1⟩ := shifted H
  obtain ⟨Ks, hKn, hK, hK0, hK1⟩ := shifted K
  have h0 : ⊤ ≤ ⨆ p : {p : ℕ × ℕ // p.1 + p.2 = 1}, Hs p.1.1 ⊓ Ks p.1.2 := by
    rw [← hHK]
    refine sup_le ?_ ?_
    · refine le_iSup_of_le
        (f := fun p : {p : ℕ × ℕ // p.1 + p.2 = 1} => Hs p.1.1 ⊓ Ks p.1.2) ⟨(1, 0), rfl⟩ ?_
      simp only [hH1, hK0, Subgroup.lowerCentralSeries_zero, inf_top_eq, le_refl]
    · refine le_iSup_of_le
        (f := fun p : {p : ℕ × ℕ // p.1 + p.2 = 1} => Hs p.1.1 ⊓ Ks p.1.2) ⟨(0, 1), rfl⟩ ?_
      simp only [hK1, hH0, Subgroup.lowerCentralSeries_zero, top_inf_eq, le_refl]
  have key := fitting_core H K hHK Hs Ks hHn hKn hH hK h0 (c + d)
  rw [eq_bot_iff]
  refine key.trans (iSup_le ?_)
  rintro ⟨⟨a, b⟩, hab⟩
  simp only at hab ⊢
  rcases Nat.lt_or_ge c a with ha | ha
  · obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    rw [hH1]
    refine inf_le_left.trans ?_
    rw [← hc]
    exact Subgroup.lowerCentralSeries_antitone H (by omega)
  · obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    rw [hK1]
    refine inf_le_right.trans ?_
    rw [← hd]
    exact Subgroup.lowerCentralSeries_antitone K (by omega)

theorem fitting (H K : Subgroup G) [H.Normal] [K.Normal] (hHK : H ⊔ K = ⊤)
    (hH : Group.IsNilpotent H) (hK : Group.IsNilpotent K) : Group.IsNilpotent G := by
  obtain ⟨c, hc⟩ := (Subgroup.isNilpotent_iff_lowerCentralSeries H).mp hH
  obtain ⟨d, hd⟩ := (Subgroup.isNilpotent_iff_lowerCentralSeries K).mp hK
  exact Subgroup.nilpotent_iff_lowerCentralSeries.mpr ⟨c + d, fitting_class H K hHK c d hc hd⟩

lemma engel_mem (x y : G) :
    ∀ n, engelCommutator x y n ∈ (⊤ : Subgroup G).lowerCentralSeries n
  | 0 => mem_top x
  | n + 1 => by
    simp only [engelCommutator, Subgroup.lowerCentralSeries_succ]
    exact commutator_mem_commutator (engel_mem x y n) (mem_top y)

theorem engel_of_nilpotent (h : Group.IsNilpotent G) : IsEngelGroup G := by
  obtain ⟨n, hn⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.mp h
  intro y x
  refine ⟨n, ?_⟩
  have := engel_mem x y n
  rw [hn] at this
  exact (mem_bot.mp this)

lemma engel_map {G' : Type*} [Group G'] (f : G →* G') (x y : G) :
    ∀ n, f (engelCommutator x y n) = engelCommutator (f x) (f y) n
  | 0 => rfl
  | n + 1 => by simp only [engelCommutator, map_commutatorElement, engel_map f x y n]

lemma engel_stable (x y : G) (m : ℕ) (hm : engelCommutator x y m = 1) :
    ∀ k, engelCommutator x y (m + k) = 1
  | 0 => hm
  | k + 1 => by
    show engelCommutator x y (m + k + 1) = 1
    simp only [engelCommutator, engel_stable x y m hm k, commutatorElement_one_left]

lemma engel_prod {A B : Type*} [Group A] [Group B] (hA : IsEngelGroup A)
    (hB : IsEngelGroup B) : IsEngelGroup (A × B) := by
  intro y x
  obtain ⟨n1, h1⟩ := hA y.1 x.1
  obtain ⟨n2, h2⟩ := hB y.2 x.2
  refine ⟨n1 + n2, ?_⟩
  have e1 := engel_map (MonoidHom.fst A B) x y (n1 + n2)
  have e2 := engel_map (MonoidHom.snd A B) x y (n1 + n2)
  simp only [MonoidHom.coe_fst, MonoidHom.coe_snd] at e1 e2
  refine Prod.ext ?_ ?_
  · rw [e1, Prod.fst_one]; exact engel_stable _ _ n1 h1 n2
  · rw [e2, Prod.snd_one, Nat.add_comm]; exact engel_stable _ _ n2 h2 n1

lemma engel_of_surj {A : Type*} [Group A] (f : A →* G) (hf : Function.Surjective f)
    (hA : IsEngelGroup A) : IsEngelGroup G := by
  intro y x
  obtain ⟨b, rfl⟩ := hf y
  obtain ⟨a, rfl⟩ := hf x
  obtain ⟨n, hn⟩ := hA b a
  exact ⟨n, by rw [← engel_map, hn, map_one]⟩

/-- The direct-product case `H ⊓ K = ⊥`: then `G ≅ H × K`, and Engel passes to products. -/
theorem direct_case (H K : Subgroup G) [H.Normal] [K.Normal] (hHK : H ⊔ K = ⊤)
    (hbot : H ⊓ K = ⊥) (hH : IsEngelGroup H) (hK : IsEngelGroup K) : IsEngelGroup G := by
  have comm : ∀ (a : H) (b : K), Commute (H.subtype a) (K.subtype b) := by
    intro a b
    have hmem : ⁅(a : G), (b : G)⁆ ∈ H ⊓ K :=
      (commutator_le_inf H K) (commutator_mem_commutator a.2 b.2)
    rw [hbot, mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact hmem
  refine engel_of_surj (H.subtype.noncommCoprod K.subtype comm) ?_ (engel_prod hH hK)
  intro g
  have hg : g ∈ H ⊔ K := hHK ▸ mem_top g
  obtain ⟨y, hy, z, hz, hyz⟩ := mem_sup_of_normal_left.mp hg
  exact ⟨(⟨y, hy⟩, ⟨z, hz⟩), by simp [hyz]⟩

theorem main : H1 → H2 → type_of% @Kourovka.«1.40».kourovka_1_40 := by
  intro h1 h2 G _ H K hHn hKn hHe hKe hHK
  by_cases hb : H ⊓ K = ⊥
  · exact direct_case H K hHK hb hHe hKe
  by_cases nH : Group.IsNilpotent H <;> by_cases nK : Group.IsNilpotent K
  · exact engel_of_nilpotent (fitting H K hHK nH nK)
  · exact h2 G H K hHn hKn hHe hKe hHK nH nK hb
  · exact h2 G K H hKn hHn hKe hHe (by rw [sup_comm]; exact hHK) nK nH
      (by rw [inf_comm]; exact hb)
  · exact h1 G H K hHn hKn hHe hKe hHK nH nK hb

end OMA.R_Kourovka_1_40_kourovka_1_40_R2
