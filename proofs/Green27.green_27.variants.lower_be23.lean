import FormalConjectures.GreensOpenProblems.«27»
import Mathlib

-- Problem: Ben Green's Open Problem 27, Bedert lower bound omega(p) log p <= m(p) (a KNOWN result, Be23 Theorem 3)
-- Upstream: formal-conjectures FormalConjectures/GreensOpenProblems/27.lean (declaration Green27.green_27.variants.lower_be23)
-- Route: the stronger near-quadratic bound m(p) >= c (log p / log log p)^2 (He 2026, and Hou-Yang 2026) implies it.
-- Lean source of that bound: github.com/xinjiegit/ben_27_formalization, commit f70352964007662e97a810c880abbfea1e2ea262,
-- licence Apache-2.0 (NUSLean/*.lean, concatenated into this single file, comments stripped, one attribute-instance line
-- replaced by explicit instances, ported from Lean v4.32.0 / Mathlib v4.32.0 to the site pin). Original notices:
-- Copyright the authors of ben_27_formalization, licensed under the Apache License, Version 2.0.
-- The bridge from NUS.m to Green27.m and the final theorem are new.




namespace NUS

open Finset


theorem multiset_pair_eq_pair {α : Type*} {a b c d : α} :
    ({a, b} : Multiset α) = {c, d} ↔ a = c ∧ b = d ∨ a = d ∧ b = c := by
  constructor
  · intro h
    rw [Multiset.insert_eq_cons, Multiset.insert_eq_cons, Multiset.cons_eq_cons] at h
    rcases h with ⟨hac, hbd⟩ | ⟨_, cs, hb, hd⟩
    · exact Or.inl ⟨hac, Multiset.singleton_inj.mp hbd⟩
    · rw [Multiset.singleton_eq_cons_iff] at hb hd
      exact Or.inr ⟨hd.1.symm, hb.1⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact Multiset.pair_comm a b

variable {G : Type*} [AddCommGroup G]


def IsPairFrom (A : Finset G) (t : Multiset G) : Prop :=
  Multiset.card t = 2 ∧ ∀ x ∈ t, x ∈ A


def HasNoUniqueSum (A : Finset G) : Prop :=
  ∀ t : Multiset G, IsPairFrom A t →
    ∃ t' : Multiset G, IsPairFrom A t' ∧ t' ≠ t ∧ t'.sum = t.sum


theorem exists_minimal (A : Finset G) :
    2 ≤ A.card → HasNoUniqueSum A →
      ∃ B, B ⊆ A ∧ 2 ≤ B.card ∧ HasNoUniqueSum B ∧
        ∀ C, C ⊂ B → 2 ≤ C.card → ¬HasNoUniqueSum C := by
  induction A using Finset.strongInduction with
  | _ A ih =>
    intro h2 h
    by_cases hmin : ∀ C, C ⊂ A → 2 ≤ C.card → ¬HasNoUniqueSum C
    · exact ⟨A, Finset.Subset.refl A, h2, h, hmin⟩
    · push Not at hmin
      obtain ⟨C, hCA, hC2, hCnus⟩ := hmin
      obtain ⟨B, hBC, hB2, hBnus, hBmin⟩ := ih C hCA hC2 hCnus
      exact ⟨B, hBC.trans hCA.subset, hB2, hBnus, hBmin⟩




noncomputable def m (p : ℕ) : ℕ :=
  sInf {k | ∃ A : Finset (ZMod p), A.card = k ∧ 2 ≤ k ∧ HasNoUniqueSum A}


theorem hasNoUniqueSum_univ (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    HasNoUniqueSum (univ : Finset (ZMod p)) := by
  haveI : Fact (1 < p) := ⟨hp.out.one_lt⟩
  have h1 : (1 : ZMod p) ≠ 0 := one_ne_zero
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by push_cast; exact h
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp this)
  rintro t ⟨hcard, -⟩
  obtain ⟨a, b, rfl⟩ := Multiset.card_eq_two.mp hcard
  by_cases hab : b = a + 1
  · 
    refine ⟨{b + 1, a - 1}, ⟨rfl, fun x _ => mem_univ x⟩, ?_, by
      simp only [Multiset.insert_eq_cons, Multiset.sum_cons, Multiset.sum_singleton]
      ring⟩
    rw [Ne, multiset_pair_eq_pair]
    rintro (⟨hba, -⟩ | ⟨hbb, -⟩)
    · 
      apply h2
      have : a + (1 + 1) = a + 0 := by
        rw [← add_assoc, ← hab, hba, add_zero]
      have h20 : (1 + 1 : ZMod p) = 0 := add_left_cancel this
      calc (2 : ZMod p) = 1 + 1 := by norm_num
        _ = 0 := h20
    · 
      exact h1 (add_left_cancel (show b + 1 = b + 0 by rw [add_zero]; exact hbb))
  · 
    refine ⟨{a + 1, b - 1}, ⟨rfl, fun x _ => mem_univ x⟩, ?_, by
      simp only [Multiset.insert_eq_cons, Multiset.sum_cons, Multiset.sum_singleton]
      ring⟩
    rw [Ne, multiset_pair_eq_pair]
    rintro (⟨haa, -⟩ | ⟨hab', -⟩)
    · exact h1 (add_left_cancel (show a + 1 = a + 0 by rw [add_zero]; exact haa))
    · exact hab hab'.symm


end NUS




namespace NUS


theorem exists_derangement (α : Type*) [Fintype α] [DecidableEq α]
    (h : 2 ≤ Fintype.card α) : ∃ π : Equiv.Perm α, ∀ x, π x ≠ x := by
  obtain ⟨k, hk⟩ : ∃ k, Fintype.card α = k + 2 := ⟨Fintype.card α - 2, by omega⟩
  let e : α ≃ Fin (k + 2) := Fintype.equivFinOfCardEq hk
  refine ⟨e.trans ((finRotate (k + 2)).trans e.symm), fun x hx => ?_⟩
  replace hx := congrArg e hx
  simp only [Equiv.trans_apply, Equiv.apply_symm_apply, finRotate_apply] at hx
  have h1 : (1 : Fin (k + 2)) = 0 :=
    add_left_cancel (show e x + 1 = e x + 0 by rw [add_zero]; exact hx)
  rw [Fin.one_eq_zero_iff] at h1
  omega


theorem exists_fiberwise_derangement {α β : Type*} [Fintype α] [DecidableEq α]
    (f : α → β) (h : ∀ x, ∃ y, y ≠ x ∧ f y = f x) :
    ∃ π : Equiv.Perm α, (∀ x, f (π x) = f x) ∧ ∀ x, π x ≠ x := by
  classical
  have hfib : ∀ b : β, ∃ δ : Equiv.Perm {y // f y = b}, ∀ z, δ z ≠ z := by
    intro b
    rcases isEmpty_or_nonempty {y // f y = b} with hE | hN
    · exact ⟨Equiv.refl _, fun z => (hE.false z).elim⟩
    · obtain ⟨⟨x, hx⟩⟩ := hN
      obtain ⟨y, hyx, hyf⟩ := h x
      have hcard : 2 ≤ Fintype.card {y // f y = b} := by
        haveI : Nontrivial {y // f y = b} :=
          ⟨⟨⟨y, hyf.trans hx⟩, ⟨x, hx⟩, by simpa using hyx⟩⟩
        exact Fintype.one_lt_card
      exact exists_derangement _ hcard
  choose δ hδ using hfib
  refine ⟨(Equiv.sigmaFiberEquiv f).symm.trans
      ((Equiv.sigmaCongrRight δ).trans (Equiv.sigmaFiberEquiv f)), fun x => ?_, fun x hx => ?_⟩
  · exact (δ (f x) ⟨x, rfl⟩).2
  · exact hδ (f x) ⟨x, rfl⟩ (Subtype.ext hx)

end NUS





namespace NUS

open Finset Matrix


theorem sym2_surj {α : Type*} (z : Sym2 α) : ∃ x y, z = s(x, y) :=
  Sym2.ind (fun x y => ⟨x, y, rfl⟩) z



variable {n : ℕ}


def uvec : Sym2 (Fin n) → (Fin n → ℤ) :=
  Sym2.lift ⟨fun i j => Pi.single i 1 + Pi.single j 1, fun _ _ => add_comm _ _⟩

@[simp] theorem uvec_mk (i j : Fin n) :
    uvec s(i, j) = Pi.single i 1 + Pi.single j 1 := rfl


def pairSum {R : Type*} [AddCommMonoid R] (x : Fin n → R) : Sym2 (Fin n) → R :=
  Sym2.lift ⟨fun i j => x i + x j, fun _ _ => add_comm _ _⟩

@[simp] theorem pairSum_mk {R : Type*} [AddCommMonoid R] (x : Fin n → R) (i j : Fin n) :
    pairSum x s(i, j) = x i + x j := rfl


theorem uvec_cast_dot {R : Type*} [CommRing R] (t : Sym2 (Fin n)) (x : Fin n → R) :
    (fun k => ((uvec t k : ℤ) : R)) ⬝ᵥ x = pairSum x t := by
  induction t using Sym2.ind with
  | _ i j =>
    simp only [uvec_mk, pairSum_mk, dotProduct, Pi.add_apply, Pi.single_apply]
    push_cast
    simp [add_mul, ite_mul, Finset.sum_add_distrib]




structure MinimalNUS (p n : ℕ) where
  
  a : Fin n ↪ ZMod p
  two_le : 2 ≤ n
  nus : HasNoUniqueSum (Finset.univ.map a)
  minimal : ∀ C, C ⊂ Finset.univ.map a → 2 ≤ C.card → ¬HasNoUniqueSum C

namespace MinimalNUS

variable {p : ℕ} (S : MinimalNUS p n)


def carrier : Finset (ZMod p) := Finset.univ.map S.a

theorem mem_carrier (i : Fin n) : S.a i ∈ S.carrier :=
  mem_map_of_mem _ (mem_univ i)


def sumMap : Sym2 (Fin n) → ZMod p :=
  Sym2.lift ⟨fun i j => S.a i + S.a j, fun _ _ => add_comm _ _⟩

@[simp] theorem sumMap_mk (i j : Fin n) : S.sumMap s(i, j) = S.a i + S.a j := rfl

theorem pairSum_a (t : Sym2 (Fin n)) : pairSum (fun i => S.a i) t = S.sumMap t := by
  induction t using Sym2.ind with
  | _ i j => rfl


def pairMul : Sym2 (Fin n) → Multiset (ZMod p) :=
  Sym2.lift ⟨fun i j => {S.a i, S.a j}, fun _ _ => Multiset.pair_comm _ _⟩

@[simp] theorem pairMul_mk (i j : Fin n) : S.pairMul s(i, j) = {S.a i, S.a j} := rfl

theorem isPairFrom_pairMul (t : Sym2 (Fin n)) : IsPairFrom S.carrier (S.pairMul t) := by
  induction t using Sym2.ind with
  | _ i j =>
    refine ⟨by simp, ?_⟩
    intro x hx
    rcases (by simpa using hx : x = S.a i ∨ x = S.a j) with rfl | rfl
    exacts [S.mem_carrier i, S.mem_carrier j]

theorem sum_pairMul (t : Sym2 (Fin n)) : (S.pairMul t).sum = S.sumMap t := by
  induction t using Sym2.ind with
  | _ i j => simp


theorem exists_mate (t : Sym2 (Fin n)) :
    ∃ t' : Sym2 (Fin n), t' ≠ t ∧ S.sumMap t' = S.sumMap t := by
  obtain ⟨m', ⟨hcard, hmem⟩, hne, hsum⟩ := S.nus (S.pairMul t) (S.isPairFrom_pairMul t)
  obtain ⟨c, d, rfl⟩ := Multiset.card_eq_two.mp hcard
  obtain ⟨i', -, hi'⟩ := Finset.mem_map.mp (hmem c (by simp))
  obtain ⟨j', -, hj'⟩ := Finset.mem_map.mp (hmem d (by simp))
  refine ⟨s(i', j'), fun hEq => hne ?_, ?_⟩
  · have : S.pairMul s(i', j') = S.pairMul t := by rw [hEq]
    rw [pairMul_mk, hi', hj'] at this
    exact this
  · have : ({c, d} : Multiset (ZMod p)).sum = S.sumMap t := by rw [hsum, S.sum_pairMul]
    rw [sumMap_mk, hi', hj']
    simpa using this


structure Pairing (S : MinimalNUS p n) where
  
  μ : Equiv.Perm (Sym2 (Fin n))
  sumMap_fix : ∀ t, S.sumMap (μ t) = S.sumMap t
  ne : ∀ t, μ t ≠ t


theorem exists_pairing : Nonempty S.Pairing := by
  obtain ⟨π, hfib, hne⟩ := exists_fiberwise_derangement S.sumMap fun t => by
    obtain ⟨t', h1, h2⟩ := S.exists_mate t
    exact ⟨t', h1, h2⟩
  exact ⟨⟨π, hfib, hne⟩⟩




def rho (P : S.Pairing) (t : Sym2 (Fin n)) : Fin n → ℤ :=
  uvec t - uvec (P.μ t)


def colLat (P : S.Pairing) : Submodule ℤ (Fin n → ℤ) :=
  Submodule.span ℤ (Set.range (S.rho P))


theorem rho_cast_dot {R : Type*} [CommRing R] (P : S.Pairing) (t : Sym2 (Fin n))
    (x : Fin n → R) :
    (fun k => ((S.rho P t k : ℤ) : R)) ⬝ᵥ x = pairSum x t - pairSum x (P.μ t) := by
  have hfun : (fun k => ((S.rho P t k : ℤ) : R)) =
      (fun k => ((uvec t k : ℤ) : R)) - fun k => ((uvec (P.μ t) k : ℤ) : R) := by
    funext k
    simp [rho]
  rw [hfun, sub_dotProduct, uvec_cast_dot, uvec_cast_dot]


theorem rho_cast_dot_one {R : Type*} [CommRing R] (P : S.Pairing) (t : Sym2 (Fin n)) :
    (fun k => ((S.rho P t k : ℤ) : R)) ⬝ᵥ (fun _ => (1 : R)) = 0 := by
  rw [rho_cast_dot]
  have h2 : ∀ z : Sym2 (Fin n), pairSum (fun _ => (1 : R)) z = 2 := by
    intro z
    induction z using Sym2.ind with
    | _ i j => rw [pairSum_mk]; norm_num
  rw [h2, h2, sub_self]


theorem rho_cast_dot_a (P : S.Pairing) (t : Sym2 (Fin n)) :
    (fun k => ((S.rho P t k : ℤ) : ZMod p)) ⬝ᵥ (fun i => S.a i) = 0 := by
  rw [rho_cast_dot, pairSum_a, pairSum_a, P.sumMap_fix, sub_self]



theorem eq_const_of_rho_dot_eq_zero (P : S.Pairing) (x : Fin n → ℚ)
    (hx : ∀ t, (fun k => ((S.rho P t k : ℤ) : ℚ)) ⬝ᵥ x = 0) (i j : Fin n) : x i = x j := by
  by_contra hne
  
  have hw : ∀ t, pairSum x (P.μ t) = pairSum x t := by
    intro t
    have h := hx t
    rw [S.rho_cast_dot P t x, sub_eq_zero] at h
    exact h.symm
  
  haveI hne' : Nonempty (Fin n) := ⟨i⟩
  have himg : (Finset.univ.image x).Nonempty :=
    Finset.univ_nonempty.image x
  set xmax := (Finset.univ.image x).max' himg with hxmax
  set M := Finset.univ.filter (fun k => x k = xmax) with hMdef
  have hle : ∀ k, x k ≤ xmax := fun k =>
    Finset.le_max' _ _ (Finset.mem_image_of_mem x (Finset.mem_univ k))
  have hmemM : ∀ k, k ∈ M ↔ x k = xmax := by
    intro k
    simp [hMdef]
  have hMne : M.Nonempty := by
    obtain ⟨k, -, hk⟩ := Finset.mem_image.mp ((Finset.univ.image x).max'_mem himg)
    exact ⟨k, (hmemM k).mpr hk⟩
  
  have hstab : ∀ t : Sym2 (Fin n), (∀ k ∈ t, k ∈ M) → ∀ k ∈ P.μ t, k ∈ M := by
    intro t ht
    obtain ⟨i₀, j₀, rfl⟩ := sym2_surj t
    obtain ⟨i₁, j₁, h₁⟩ := sym2_surj (P.μ s(i₀, j₀))
    have hi₀ : x i₀ = xmax := (hmemM i₀).mp (ht i₀ (Sym2.mem_mk_left _ _))
    have hj₀ : x j₀ = xmax := (hmemM j₀).mp (ht j₀ (Sym2.mem_mk_right _ _))
    have hsum : x i₁ + x j₁ = x i₀ + x j₀ := by
      have := hw s(i₀, j₀)
      rw [h₁, pairSum_mk, pairSum_mk] at this
      exact this
    have hmax1 : x i₁ = xmax ∧ x j₁ = xmax := by
      constructor <;> [skip; skip] <;>
        · have h1 := hle i₁
          have h2 := hle j₁
          rw [hi₀, hj₀] at hsum
          linarith
    intro k hk
    rw [h₁] at hk
    rcases Sym2.mem_iff.mp hk with rfl | rfl
    · exact (hmemM k).mpr hmax1.1
    · exact (hmemM k).mpr hmax1.2
  
  have hM2 : 2 ≤ M.card := by
    by_contra hlt
    obtain ⟨i₁, hMi₁⟩ := Finset.card_eq_one.mp
      (le_antisymm (by omega) (Finset.card_pos.mpr hMne))
    have hmem : ∀ k ∈ s(i₁, i₁), k ∈ M := by
      intro k hk
      rcases Sym2.mem_iff.mp hk with rfl | rfl <;> simp [hMi₁]
    have hin := hstab s(i₁, i₁) hmem
    obtain ⟨c, d, hcd⟩ := sym2_surj (P.μ s(i₁, i₁))
    have hc : c ∈ M := hin c (by rw [hcd]; exact Sym2.mem_mk_left _ _)
    have hd : d ∈ M := hin d (by rw [hcd]; exact Sym2.mem_mk_right _ _)
    rw [hMi₁, Finset.mem_singleton] at hc hd
    exact P.ne s(i₁, i₁) (by rw [hcd, hc, hd])
  
  have hMuniv : M ≠ Finset.univ := by
    intro hEq
    apply hne
    have hi : x i = xmax := (hmemM i).mp (hEq ▸ Finset.mem_univ i)
    have hj : x j = xmax := (hmemM j).mp (hEq ▸ Finset.mem_univ j)
    rw [hi, hj]
  
  set B := M.map S.a with hBdef
  have hBcard : 2 ≤ B.card := by rw [hBdef, Finset.card_map]; exact hM2
  have hBsub : B ⊂ S.carrier :=
    Finset.map_ssubset_map.mpr (Finset.ssubset_univ_iff.mpr hMuniv)
  have hBnus : HasNoUniqueSum B := by
    rintro tm ⟨hcard2, hmem2⟩
    obtain ⟨c, d, rfl⟩ := Multiset.card_eq_two.mp hcard2
    obtain ⟨i₀, hi₀M, hi₀⟩ := Finset.mem_map.mp (hmem2 c (by simp))
    obtain ⟨j₀, hj₀M, hj₀⟩ := Finset.mem_map.mp (hmem2 d (by simp))
    obtain ⟨i₁, j₁, h₁⟩ := sym2_surj (P.μ s(i₀, j₀))
    have hin : ∀ k ∈ P.μ s(i₀, j₀), k ∈ M := by
      apply hstab
      intro k hk
      rcases Sym2.mem_iff.mp hk with rfl | rfl
      exacts [hi₀M, hj₀M]
    have hi₁M : i₁ ∈ M := hin i₁ (by rw [h₁]; exact Sym2.mem_mk_left _ _)
    have hj₁M : j₁ ∈ M := hin j₁ (by rw [h₁]; exact Sym2.mem_mk_right _ _)
    refine ⟨{S.a i₁, S.a j₁}, ⟨by simp, ?_⟩, ?_, ?_⟩
    · intro z hz
      rcases (by simpa using hz : z = S.a i₁ ∨ z = S.a j₁) with rfl | rfl
      exacts [Finset.mem_map_of_mem _ hi₁M, Finset.mem_map_of_mem _ hj₁M]
    · 
      intro hEqm
      apply P.ne s(i₀, j₀)
      rw [h₁]
      rw [← hi₀, ← hj₀, multiset_pair_eq_pair] at hEqm
      rcases hEqm with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [S.a.injective h1, S.a.injective h2]
      · rw [S.a.injective h1, S.a.injective h2]
        exact Sym2.eq_swap
    · 
      have hfix := P.sumMap_fix s(i₀, j₀)
      rw [h₁, sumMap_mk, sumMap_mk] at hfix
      simpa [← hi₀, ← hj₀] using hfix
  exact S.minimal B hBsub hBcard hBnus




def rhoQ (P : S.Pairing) (t : Sym2 (Fin n)) : Fin n → ℚ :=
  fun k => ((S.rho P t k : ℤ) : ℚ)


theorem finrank_span_rhoQ (P : S.Pairing) :
    Module.finrank ℚ (Submodule.span ℚ (Set.range (S.rhoQ P))) = n - 1 := by
  classical
  have hn := S.two_le
  set R : Matrix (Sym2 (Fin n)) (Fin n) ℚ := Matrix.of fun t => S.rhoQ P t with hRdef
  
  have hker : LinearMap.ker R.mulVecLin = Submodule.span ℚ {fun _ => (1 : ℚ)} := by
    apply le_antisymm
    · intro x hxk
      have hx : ∀ t, (fun k => ((S.rho P t k : ℤ) : ℚ)) ⬝ᵥ x = 0 := by
        intro t
        have := LinearMap.mem_ker.mp hxk
        exact congrFun this t
      have hconst := S.eq_const_of_rho_dot_eq_zero P x hx
      refine Submodule.mem_span_singleton.mpr ⟨x ⟨0, by omega⟩, ?_⟩
      funext k
      simp [hconst k ⟨0, by omega⟩]
    · rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, LinearMap.mem_ker]
      funext t
      simpa [hRdef, Matrix.mulVecLin_apply, Matrix.mulVec, rhoQ] using
        S.rho_cast_dot_one (R := ℚ) P t
  have hkerrank : Module.finrank ℚ (LinearMap.ker R.mulVecLin) = 1 := by
    rw [hker]
    refine finrank_span_singleton ?_
    intro hzero
    have := congrFun hzero ⟨0, by omega⟩
    norm_num at this
  have hrn := LinearMap.finrank_range_add_finrank_ker R.mulVecLin
  rw [hkerrank, Module.finrank_pi] at hrn
  have hrank : R.rank = n - 1 := by
    have : R.rank + 1 = n := by
      rw [Matrix.rank]
      simpa using hrn
    omega
  have hspan := R.rank_eq_finrank_span_row
  rw [hrank] at hspan
  have hrange : Set.range R.row = Set.range (S.rhoQ P) := rfl
  rw [hrange] at hspan
  exact hspan.symm




def modp (p : ℕ) {n : ℕ} : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ZMod p) where
  toFun v := fun k => ((v k : ℤ) : ZMod p)
  map_add' u v := by
    funext k
    simp
  map_smul' c v := by
    funext k
    simp [zsmul_eq_mul]


theorem colLat_orth (P : S.Pairing) {y : Fin n → ℤ} (hy : y ∈ S.colLat P) :
    (modp p y) ⬝ᵥ (fun _ => (1 : ZMod p)) = 0 ∧ (modp p y) ⬝ᵥ (fun i => S.a i) = 0 := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨t, rfl⟩ := hy
    exact ⟨S.rho_cast_dot_one P t, S.rho_cast_dot_a P t⟩
  | zero => simp
  | add u v hu hv hu' hv' =>
    rw [map_add, add_dotProduct, add_dotProduct, hu'.1, hv'.1, hu'.2, hv'.2]
    simp
  | smul c u hu hu' =>
    rw [map_smul, smul_dotProduct, smul_dotProduct, hu'.1, hu'.2]
    simp

section ModularDefect

variable [Fact p.Prime]


def Bt : Matrix (Fin 2) (Fin n) (ZMod p) :=
  Matrix.of ![fun _ => (1 : ZMod p), fun i => S.a i]

theorem Bt_rank : (Bt S).rank = 2 := by
  have hn := S.two_le
  have i₀ : Fin n := ⟨0, by omega⟩
  have i₁ : Fin n := ⟨1, by omega⟩
  have hli : LinearIndependent (ZMod p) (Bt S).row := by
    have hrow : (Bt S).row = ![fun _ => (1 : ZMod p), fun i => S.a i] := rfl
    rw [hrow, linearIndependent_fin2]
    constructor
    · 
      intro hzero
      have h0 : S.a ⟨0, by omega⟩ = 0 := congrFun (by simpa using hzero) _
      have h1 : S.a ⟨1, by omega⟩ = 0 := congrFun (by simpa using hzero) _
      have := S.a.injective (h0.trans h1.symm)
      simp [Fin.ext_iff] at this
    · 
      intro c hc
      have h0 : c * S.a ⟨0, by omega⟩ = 1 := congrFun (by simpa using hc) _
      have h1 : c * S.a ⟨1, by omega⟩ = 1 := congrFun (by simpa using hc) _
      have hc0 : c ≠ 0 := by
        intro h
        rw [h, zero_mul] at h0
        exact zero_ne_one h0
      have : S.a ⟨0, by omega⟩ = S.a ⟨1, by omega⟩ :=
        mul_left_cancel₀ hc0 (h0.trans h1.symm)
      have := S.a.injective this
      simp [Fin.ext_iff] at this
  have := hli.rank_matrix
  simpa using this


theorem p_dvd_det_mul (P : S.Pairing)
    (v : Fin (n - 1) → (Fin n → ℤ)) (hv : ∀ r, v r ∈ S.colLat P)
    (U : Matrix (Fin n) (Fin (n - 1)) ℤ) :
    (p : ℤ) ∣ (Matrix.of v * U).det := by
  classical
  have hn := S.two_le
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have key : (((Matrix.of v * U).det : ℤ) : ZMod p) =
      ((Matrix.of v * U).map ⇑(Int.castRingHom (ZMod p))).det :=
    RingHom.map_det (Int.castRingHom (ZMod p)) _
  rw [key, Matrix.map_mul]
  by_contra hdet
  
  have hzero : (Matrix.of v).map ⇑(Int.castRingHom (ZMod p)) * (Bt S)ᵀ = 0 := by
    ext r c
    have horth := S.colLat_orth P (hv r)
    fin_cases c
    · simpa [Matrix.mul_apply, Matrix.map_apply, Bt, modp, dotProduct,
        mul_comm] using horth.1
    · simpa [Matrix.mul_apply, Matrix.map_apply, Bt, modp, dotProduct,
        mul_comm] using horth.2
  have hrank2 := Matrix.rank_add_rank_le_card_of_mul_eq_zero hzero
  rw [Matrix.rank_transpose, Bt_rank S, Fintype.card_fin] at hrank2
  have hVrank : ((Matrix.of v).map ⇑(Int.castRingHom (ZMod p))).rank ≤ n - 2 := by omega
  have hprod : ((Matrix.of v).map ⇑(Int.castRingHom (ZMod p)) *
      U.map ⇑(Int.castRingHom (ZMod p))).rank ≤ n - 2 :=
    le_trans (Matrix.rank_mul_le_left _ _) hVrank
  
  have hli := Matrix.linearIndependent_rows_of_det_ne_zero hdet
  have hfull : ((Matrix.of v).map ⇑(Int.castRingHom (ZMod p)) *
      U.map ⇑(Int.castRingHom (ZMod p))).rank = n - 1 := by
    have := hli.rank_matrix
    simpa using this
  omega

end ModularDefect

end MinimalNUS

end NUS





namespace NUS

open Finset Matrix
open scoped RealInnerProductSpace


theorem abs_det_le_prod_euclidean_row_norm {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) :
    |A.det| ≤ ∏ i, ‖(WithLp.toLp 2 (A i) : EuclideanSpace ℝ (Fin d))‖ := by
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d) := ⟨by simp⟩
  let b : OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)) :=
    EuclideanSpace.basisFun (Fin d) ℝ
  let o : Orientation ℝ (EuclideanSpace ℝ (Fin d)) (Fin d) := b.toBasis.orientation
  let v : Fin d → EuclideanSpace ℝ (Fin d) := fun i => WithLp.toLp 2 (A i)
  have h := o.abs_volumeForm_apply_le v
  rw [o.volumeForm_robust' b v] at h
  have hd : b.toBasis.det v = A.det := by
    rw [Module.Basis.det_apply]
    rw [show b.toBasis.toMatrix v = Aᵀ by
      ext i j
      simp [b, v, Module.Basis.toMatrix_apply], Matrix.det_transpose]
  rwa [hd] at h



section NearUnimodular


def NearUni {κ : Type*} (v : κ → ℤ) : Prop :=
  (∀ c, v c = 1 ∨ v c = 0 ∨ v c = -1) ∧
    (∀ c c', v c = 1 → v c' = 1 → c = c') ∧
    ∀ c c', v c = -1 → v c' = -1 → c = c'

theorem NearUni.comp {κ κ' : Type*} {v : κ → ℤ} (hv : NearUni v) {f : κ' → κ}
    (hf : Function.Injective f) : NearUni (v ∘ f) :=
  ⟨fun c => hv.1 (f c), fun c c' h h' => hf (hv.2.1 (f c) (f c') h h'),
    fun c c' h h' => hf (hv.2.2 (f c) (f c') h h')⟩


def isub {α : Type*} [DecidableEq α] (a b : α) : α → ℤ :=
  Pi.single a 1 - Pi.single b 1

theorem isub_apply {α : Type*} [DecidableEq α] (a b k : α) :
    isub a b k = (if k = a then (1 : ℤ) else 0) - if k = b then (1 : ℤ) else 0 := by
  rw [isub, Pi.sub_apply, Pi.single_apply, Pi.single_apply]


theorem sum_isub_eq_zero {α : Type*} [DecidableEq α] (T : Finset α) {a b : α}
    (ha : a ∈ T) (hb : b ∈ T) : ∑ k ∈ T, isub a b k = 0 := by
  simp [isub, Finset.sum_sub_distrib, ha, hb]

theorem isub_ne_zero_support {α : Type*} [DecidableEq α] {a b k : α}
    (h : isub a b k ≠ 0) : k = a ∨ k = b := by
  rw [isub_apply] at h
  by_cases ha : k = a
  · exact Or.inl ha
  by_cases hb : k = b
  · exact Or.inr hb
  simp [ha, hb] at h

theorem sum_sq_isub_le_two {α : Type*} [Fintype α] [DecidableEq α] (a b : α) :
    ∑ k, (((isub a b k : ℤ) : ℝ) ^ 2) ≤ 2 := by
  by_cases h : a = b
  · subst b
    simp [isub]
  · calc
      ∑ k, (((isub a b k : ℤ) : ℝ) ^ 2) =
          ∑ k, (((if k = a then 1 else 0) : ℝ) ^ 2 +
            ((if k = b then 1 else 0) : ℝ) ^ 2 -
            2 * (if k = a then 1 else 0) * (if k = b then 1 else 0)) := by
              apply Finset.sum_congr rfl
              intro k _
              simp only [isub, Pi.sub_apply, Pi.single_apply]
              push_cast
              ring
      _ = 2 := by
        have hp : ∀ k : α,
            (((if k = a then 1 else 0) : ℝ) ^ 2 +
              ((if k = b then 1 else 0) : ℝ) ^ 2 -
              2 * (if k = a then 1 else 0) * (if k = b then 1 else 0)) =
            (if k = a then 1 else 0) + (if k = b then 1 else 0) := by
          intro k
          by_cases ha : k = a
          · have hb : k ≠ b := fun e => h (ha.symm.trans e)
            simp [ha, h]
          · by_cases hb : k = b <;> simp [ha, hb, Ne.symm h]
        simp_rw [hp, Finset.sum_add_distrib]
        norm_num
      _ ≤ 2 := le_rfl


theorem exists_indep_family_of_finrank {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] {ι : Type*} (g : ι → V) (d : ℕ)
    (hd : d ≤ Module.finrank F (Submodule.span F (Set.range g))) :
    ∃ t : Fin d → ι, LinearIndependent F (fun j => g (t j)) := by
  classical
  obtain ⟨sb, hsub, hspan, hli⟩ := exists_linearIndependent F (Set.range g)
  have hfin : sb.Finite := hli.setFinite
  haveI := hfin.fintype
  have hcard : d ≤ Fintype.card sb := by
    have h1 : Module.finrank F (Submodule.span F sb) = sb.toFinset.card :=
      finrank_span_set_eq_card hli
    rw [hspan] at h1
    rw [Set.toFinset_card] at h1
    omega
  let emb : Fin d ↪ sb :=
    (Fin.castLEEmb hcard).trans (Fintype.equivFin sb).symm.toEmbedding
  have hsel : ∀ x : sb, ∃ i : ι, g i = (x : V) := fun x => hsub x.2
  choose sel hsel using hsel
  refine ⟨fun j => sel (emb j), ?_⟩
  have hfun : (fun j => g (sel (emb j))) = (fun x : sb => (x : V)) ∘ emb := by
    funext j
    simp [hsel]
  rw [hfun]
  exact hli.comp emb emb.injective


theorem exists_coordinate_minor {F κ : Type*} [Field F] [Fintype κ] [DecidableEq κ]
    {d : ℕ} (g : Fin d → (κ → F)) (hg : LinearIndependent F g) :
    ∃ c : Fin d ↪ κ, (Matrix.of fun i j => g i (c j)).det ≠ 0 := by
  classical
  let A : Matrix (Fin d) κ F := g
  have hrank : A.rank = d := by
    have h := hg.rank_matrix
    simpa only [A, Fintype.card_fin] using h
  have hspan : d ≤ Module.finrank F
      (Submodule.span F (Set.range (fun k : κ => A.col k))) := by
    rw [← A.rank_eq_finrank_span_cols, hrank]
  obtain ⟨c, hc⟩ := exists_indep_family_of_finrank (fun k : κ => A.col k) d hspan
  have cinj : Function.Injective c := by
    intro i j hij
    apply hc.injective
    simp [hij]
  refine ⟨⟨c, cinj⟩, ?_⟩
  let B : Matrix (Fin d) (Fin d) F := Matrix.of fun i j => g i (c j)
  have hcols : LinearIndependent F (fun j => B.col j) := by
    change LinearIndependent F (fun j i => g i (c j))
    have heq : (fun j => A.col (c j)) = (fun j i => g i (c j)) := by
      funext j i
      rfl
    rw [← heq]
    exact hc
  have hu : IsUnit B := Matrix.linearIndependent_cols_iff_isUnit.mp hcols
  exact (B.isUnit_iff_isUnit_det.mp hu).ne_zero


end NearUnimodular

namespace MinimalNUS

variable {p n : ℕ}


def rectangle (X Y : Finset (Fin n)) : Set (Sym2 (Fin n)) :=
  {t | ∃ i ∈ X, ∃ j ∈ Y, t = s(i, j)}


theorem rho_eq_isub_add_isub (S : MinimalNUS p n) (P : S.Pairing) {i j i' j' : Fin n}
    (hEq : P.μ s(i, j) = s(i', j')) :
    S.rho P s(i, j) = fun k => isub i i' k + isub j j' k := by
  funext k
  simp only [rho, hEq, uvec_mk, Pi.sub_apply, Pi.add_apply, isub_apply, Pi.single_apply]
  ring


theorem rho_apply_eq_zero (S : MinimalNUS p n) (P : S.Pairing) {i j i' j' k : Fin n}
    (hEq : P.μ s(i, j) = s(i', j')) (h1 : k ≠ i) (h2 : k ≠ j) (h3 : k ≠ i') (h4 : k ≠ j') :
    S.rho P s(i, j) k = 0 := by
  simp only [rho, hEq, uvec_mk, Pi.sub_apply, Pi.add_apply, Pi.single_apply,
    if_neg h1, if_neg h2, if_neg h3, if_neg h4]
  ring


theorem sum_rho_rectangle_side_eq_zero (S : MinimalNUS p n) (P : S.Pairing)
    {X Y : Finset (Fin n)} (hXY : Disjoint X Y)
    (hinv : ∀ t ∈ rectangle X Y, P.μ t ∈ rectangle X Y)
    (t : ↑(rectangle X Y)) :
    (∑ k ∈ X, S.rho P t.1 k = 0) ∧ (∑ k ∈ Y, S.rho P t.1 k = 0) := by
  classical
  obtain ⟨i, hi, j, hj, ht⟩ := t.2
  obtain ⟨i', hi', j', hj', hEq⟩ := hinv s(i, j) ⟨i, hi, j, hj, rfl⟩
  rw [ht]
  rw [rho_eq_isub_add_isub S P hEq]
  have hji : j ∉ X := fun h => Finset.disjoint_left.mp hXY h hj
  have hj'i : j' ∉ X := fun h => Finset.disjoint_left.mp hXY h hj'
  have hij : i ∉ Y := fun h => Finset.disjoint_left.mp hXY hi h
  have hi'j : i' ∉ Y := fun h => Finset.disjoint_left.mp hXY hi' h
  constructor
  · rw [Finset.sum_add_distrib, sum_isub_eq_zero X hi hi']
    simp [isub, hji, hj'i]
  · rw [Finset.sum_add_distrib, sum_isub_eq_zero Y hj hj']
    simp [isub, hij, hi'j]


theorem sum_sq_rho_rectangle_le_four (S : MinimalNUS p n) (P : S.Pairing)
    {X Y : Finset (Fin n)} (hXY : Disjoint X Y)
    (hinv : ∀ t ∈ rectangle X Y, P.μ t ∈ rectangle X Y)
    (t : ↑(rectangle X Y)) :
    ∑ k, (((S.rho P t.1 k : ℤ) : ℝ) ^ 2) ≤ 4 := by
  classical
  obtain ⟨i, hi, j, hj, ht⟩ := t.2
  obtain ⟨i', hi', j', hj', hEq⟩ := hinv s(i, j) ⟨i, hi, j, hj, rfl⟩
  rw [ht, rho_eq_isub_add_isub S P hEq]
  have hcross : ∀ k, (isub i i' k : ℝ) * (isub j j' k : ℝ) = 0 := by
    intro k
    by_cases hx : isub i i' k = 0
    · simp [hx]
    by_cases hy : isub j j' k = 0
    · simp [hy]
    obtain hik | hik := isub_ne_zero_support hx
    <;> obtain hjk | hjk := isub_ne_zero_support hy
    all_goals
      have hkX : k ∈ X := by first | simpa [hik] using hi | simpa [hik] using hi'
      have hkY : k ∈ Y := by first | simpa [hjk] using hj | simpa [hjk] using hj'
      exact (Finset.disjoint_left.mp hXY hkX hkY).elim
  calc
    ∑ k, (((isub i i' k + isub j j' k : ℤ) : ℝ) ^ 2) =
        (∑ k, (((isub i i' k : ℤ) : ℝ) ^ 2)) +
          ∑ k, (((isub j j' k : ℤ) : ℝ) ^ 2) := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro k _
            push_cast
            rw [add_sq]
            nlinarith [hcross k]
    _ ≤ 2 + 2 := add_le_add (sum_sq_isub_le_two i i') (sum_sq_isub_le_two j j')
    _ = 4 := by norm_num


theorem sum_subtype_mul_eq_dot {R : Type*} [CommRing R] {U : Finset (Fin n)} {v : Fin n → ℤ}
    (hsupp : ∀ k, k ∉ U → v k = 0) (w : Fin n → R) :
    ∑ k : ↥U, w k.1 * ((v k.1 : ℤ) : R) = (fun k => ((v k : ℤ) : R)) ⬝ᵥ w := by
  rw [Finset.sum_coe_sort U (fun k => w k * ((v k : ℤ) : R)), dotProduct_comm]
  simp only [dotProduct]
  exact Finset.sum_subset (Finset.subset_univ U) fun k _ hk => by rw [hsupp k hk]; norm_num


theorem three_le_of_invariant (S : MinimalNUS p n) (P : S.Pairing) {X' Y' : Finset (Fin n)}
    (hX' : X'.Nonempty) (hY' : Y'.Nonempty)
    (hinv : ∀ t ∈ rectangle X' Y', P.μ t ∈ rectangle X' Y') :
    3 ≤ X'.card + Y'.card := by
  by_contra hlt
  have hx := Finset.card_pos.mpr hX'
  have hy := Finset.card_pos.mpr hY'
  have hx1 : X'.card = 1 := by omega
  have hy1 : Y'.card = 1 := by omega
  obtain ⟨i₀, hX0⟩ := Finset.card_eq_one.mp hx1
  obtain ⟨j₀, hY0⟩ := Finset.card_eq_one.mp hy1
  obtain ⟨i', hi', j', hj', hEq⟩ := hinv s(i₀, j₀) ⟨i₀, by simp [hX0], j₀, by simp [hY0], rfl⟩
  rw [hX0, Finset.mem_singleton] at hi'
  rw [hY0, Finset.mem_singleton] at hj'
  exact P.ne s(i₀, j₀) (by rw [hEq, hi', hj'])


theorem exists_minimal_rectangle (S : MinimalNUS p n) (P : S.Pairing)
    {X Y : Finset (Fin n)} (hX : X.Nonempty) (hY : Y.Nonempty)
    (hinv : ∀ t ∈ rectangle X Y, P.μ t ∈ rectangle X Y) :
    ∃ X' Y', X' ⊆ X ∧ Y' ⊆ Y ∧ X'.Nonempty ∧ Y'.Nonempty ∧
      (∀ t ∈ rectangle X' Y', P.μ t ∈ rectangle X' Y') ∧
      ∀ X'' Y'', X'' ⊆ X' → Y'' ⊆ Y' → X''.Nonempty → Y''.Nonempty →
        (∀ t ∈ rectangle X'' Y'', P.μ t ∈ rectangle X'' Y'') →
        X'' = X' ∧ Y'' = Y' := by
  classical
  let Good : ℕ → Prop := fun k => ∃ X' Y', X' ⊆ X ∧ Y' ⊆ Y ∧
    X'.Nonempty ∧ Y'.Nonempty ∧
    (∀ t ∈ rectangle X' Y', P.μ t ∈ rectangle X' Y') ∧
    X'.card + Y'.card = k
  have hex : ∃ k, Good k := ⟨X.card + Y.card, X, Y, Subset.rfl, Subset.rfl,
    hX, hY, hinv, rfl⟩
  let k₀ := Nat.find hex
  obtain ⟨X', Y', hXsub, hYsub, hXne, hYne, hinv', hcard⟩ := Nat.find_spec hex
  refine ⟨X', Y', hXsub, hYsub, hXne, hYne, hinv', ?_⟩
  intro X'' Y'' hXX hYY hX'' hY'' hinv''
  have hgood : Good (X''.card + Y''.card) :=
    ⟨X'', Y'', hXX.trans hXsub, hYY.trans hYsub, hX'', hY'', hinv'', rfl⟩
  have hmincard : k₀ ≤ X''.card + Y''.card := Nat.find_min' hex hgood
  have hleX := Finset.card_le_card hXX
  have hleY := Finset.card_le_card hYY
  dsimp only [k₀] at hmincard
  have hsum : X''.card + Y''.card = X'.card + Y'.card := by
    omega
  have heqX : X''.card = X'.card := by omega
  have heqY : Y''.card = Y'.card := by omega
  exact ⟨Finset.eq_of_subset_of_card_le hXX heqX.ge,
    Finset.eq_of_subset_of_card_le hYY heqY.ge⟩


theorem const_on_sides (S : MinimalNUS p n) (P : S.Pairing) {X' Y' : Finset (Fin n)}
    (hX' : X'.Nonempty) (hY' : Y'.Nonempty)
    (hinv : ∀ t ∈ rectangle X' Y', P.μ t ∈ rectangle X' Y')
    (hmin : ∀ X'' Y'', X'' ⊆ X' → Y'' ⊆ Y' → X''.Nonempty → Y''.Nonempty →
      (∀ t ∈ rectangle X'' Y'', P.μ t ∈ rectangle X'' Y'') → X'' = X' ∧ Y'' = Y')
    (W : Fin n → ℚ)
    (hW : ∀ i ∈ X', ∀ j ∈ Y', pairSum W (P.μ s(i, j)) = pairSum W s(i, j)) :
    (∀ i₁ ∈ X', ∀ i₂ ∈ X', W i₁ = W i₂) ∧ ∀ j₁ ∈ Y', ∀ j₂ ∈ Y', W j₁ = W j₂ := by
  classical
  have hXimg : (X'.image W).Nonempty := hX'.image W
  have hYimg : (Y'.image W).Nonempty := hY'.image W
  set mX := (X'.image W).max' hXimg with hmX
  set mY := (Y'.image W).max' hYimg with hmY
  have hleX : ∀ i ∈ X', W i ≤ mX := fun i hi =>
    Finset.le_max' _ _ (Finset.mem_image_of_mem W hi)
  have hleY : ∀ j ∈ Y', W j ≤ mY := fun j hj =>
    Finset.le_max' _ _ (Finset.mem_image_of_mem W hj)
  set A := X'.filter (fun k => W k = mX) with hA
  set B := Y'.filter (fun k => W k = mY) with hB
  have hAsub : A ⊆ X' := Finset.filter_subset _ _
  have hBsub : B ⊆ Y' := Finset.filter_subset _ _
  have hAne : A.Nonempty := by
    obtain ⟨i, hi, hWi⟩ := Finset.mem_image.mp ((X'.image W).max'_mem hXimg)
    exact ⟨i, Finset.mem_filter.mpr ⟨hi, hWi⟩⟩
  have hBne : B.Nonempty := by
    obtain ⟨j, hj, hWj⟩ := Finset.mem_image.mp ((Y'.image W).max'_mem hYimg)
    exact ⟨j, Finset.mem_filter.mpr ⟨hj, hWj⟩⟩
  have hABinv : ∀ t ∈ rectangle A B, P.μ t ∈ rectangle A B := by
    rintro t ⟨i, hiA, j, hjB, rfl⟩
    have hiX : i ∈ X' := hAsub hiA
    have hjY : j ∈ Y' := hBsub hjB
    obtain ⟨i', hi', j', hj', hEq⟩ := hinv s(i, j) ⟨i, hiX, j, hjY, rfl⟩
    have hsum : W i' + W j' = W i + W j := by
      have h := hW i hiX j hjY
      rw [hEq, pairSum_mk, pairSum_mk] at h
      exact h
    have hWi : W i = mX := (Finset.mem_filter.mp hiA).2
    have hWj : W j = mY := (Finset.mem_filter.mp hjB).2
    have hWi' : W i' = mX := by
      have h1 := hleX i' hi'
      have h2 := hleY j' hj'
      rw [hWi, hWj] at hsum
      linarith
    have hWj' : W j' = mY := by
      rw [hWi, hWj, hWi'] at hsum
      linarith
    exact ⟨i', Finset.mem_filter.mpr ⟨hi', hWi'⟩, j', Finset.mem_filter.mpr ⟨hj', hWj'⟩, hEq⟩
  obtain ⟨hAX, hBY⟩ := hmin A B hAsub hBsub hAne hBne hABinv
  constructor
  · intro i₁ h₁ i₂ h₂
    have e₁ : W i₁ = mX := (Finset.mem_filter.mp (by rw [hAX]; exact h₁ : i₁ ∈ A)).2
    have e₂ : W i₂ = mX := (Finset.mem_filter.mp (by rw [hAX]; exact h₂ : i₂ ∈ A)).2
    rw [e₁, e₂]
  · intro j₁ h₁ j₂ h₂
    have e₁ : W j₁ = mY := (Finset.mem_filter.mp (by rw [hBY]; exact h₁ : j₁ ∈ B)).2
    have e₂ : W j₂ = mY := (Finset.mem_filter.mp (by rw [hBY]; exact h₂ : j₂ ∈ B)).2
    rw [e₁, e₂]


theorem finrank_rectRows_ge (S : MinimalNUS p n) (P : S.Pairing)
    {X' Y' : Finset (Fin n)} (hX' : X'.Nonempty) (hY' : Y'.Nonempty)
    (hinv : ∀ t ∈ rectangle X' Y', P.μ t ∈ rectangle X' Y')
    (hmin : ∀ X'' Y'', X'' ⊆ X' → Y'' ⊆ Y' → X''.Nonempty → Y''.Nonempty →
      (∀ t ∈ rectangle X'' Y'', P.μ t ∈ rectangle X'' Y'') → X'' = X' ∧ Y'' = Y') :
    (X' ∪ Y').card - 2 ≤ Module.finrank ℚ
      (Submodule.span ℚ (Set.range (fun t : ↑(rectangle X' Y') =>
        fun k : ↑(X' ∪ Y') => ((S.rho P t.1 k.1 : ℤ) : ℚ)))) := by
  classical
  let U := X' ∪ Y'
  let I := ↑(rectangle X' Y')
  let A : Matrix I ↑U ℚ := Matrix.of fun t k => ((S.rho P t.1 k.1 : ℤ) : ℚ)
  obtain ⟨ix, hix⟩ := hX'
  obtain ⟨iy, hiy⟩ := hY'
  have hkerle : Module.finrank ℚ (LinearMap.ker A.mulVecLin) ≤ 2 := by
    let ixU : ↑U := ⟨ix, Finset.mem_union_left _ hix⟩
    let iyU : ↑U := ⟨iy, Finset.mem_union_right _ hiy⟩
    let ev : LinearMap.ker A.mulVecLin →ₗ[ℚ] (Fin 2 → ℚ) :=
      { toFun := fun w => ![w.1 ixU, w.1 iyU]
        map_add' := by intro u v; funext j; fin_cases j <;> rfl
        map_smul' := by intro c w; funext j; fin_cases j <;> rfl }
    have hev : Function.Injective ev := by
      intro u v huv
      apply Subtype.ext
      funext k
      let W : Fin n → ℚ := fun z => if hz : z ∈ U then u.1 ⟨z, hz⟩ - v.1 ⟨z, hz⟩ else 0
      have horth : ∀ i ∈ X', ∀ j ∈ Y',
          pairSum W (P.μ s(i, j)) = pairSum W s(i, j) := by
        intro i hi j hj
        let t : I := ⟨s(i, j), i, hi, j, hj, rfl⟩
        obtain ⟨i', hi', j', hj', hEq⟩ := hinv s(i, j) ⟨i, hi, j, hj, rfl⟩
        have hsupp : ∀ z, z ∉ U → S.rho P s(i, j) z = 0 := by
          intro z hz
          apply rho_apply_eq_zero S P hEq
          · intro h; subst z; exact hz (Finset.mem_union_left _ hi)
          · intro h; subst z; exact hz (Finset.mem_union_right _ hj)
          · intro h; subst z; exact hz (Finset.mem_union_left _ hi')
          · intro h; subst z; exact hz (Finset.mem_union_right _ hj')
        have hu0 : ∑ z : ↑U, ((S.rho P s(i, j) z.1 : ℤ) : ℚ) * u.1 z = 0 := by
          have hz := congrFun (LinearMap.mem_ker.mp u.2) t
          change (∑ z : ↑U, ((S.rho P s(i, j) z.1 : ℤ) : ℚ) * u.1 z) = 0 at hz
          exact hz
        have hv0 : ∑ z : ↑U, ((S.rho P s(i, j) z.1 : ℤ) : ℚ) * v.1 z = 0 := by
          have hz := congrFun (LinearMap.mem_ker.mp v.2) t
          change (∑ z : ↑U, ((S.rho P s(i, j) z.1 : ℤ) : ℚ) * v.1 z) = 0 at hz
          exact hz
        have hdot : (fun z => ((S.rho P s(i, j) z : ℤ) : ℚ)) ⬝ᵥ W = 0 := by
          rw [← sum_subtype_mul_eq_dot hsupp W]
          calc ∑ z : ↑U, W z.1 * ((S.rho P s(i, j) z.1 : ℤ) : ℚ)
              = ∑ z : ↑U, (((S.rho P s(i, j) z.1 : ℤ) : ℚ) * u.1 z -
                  ((S.rho P s(i, j) z.1 : ℤ) : ℚ) * v.1 z) := by
                    apply Finset.sum_congr rfl
                    intro z hz
                    simp only [W, dif_pos z.2]
                    ring
            _ = 0 := by rw [Finset.sum_sub_distrib, hu0, hv0, sub_self]
        rw [S.rho_cast_dot P s(i, j), sub_eq_zero] at hdot
        exact hdot.symm
      have hc := const_on_sides S P ⟨ix, hix⟩ ⟨iy, hiy⟩ hinv hmin W horth
      have huv0 : ev u = ev v := huv
      have hx0 : u.1 ixU = v.1 ixU := by
        have := congrFun huv0 0
        simpa [ev] using this
      have hy0 : u.1 iyU = v.1 iyU := by
        have := congrFun huv0 1
        simpa [ev] using this
      have hkU : k.1 ∈ U := k.2
      rcases Finset.mem_union.mp hkU with hkX | hkY
      · have hh := hc.1 k.1 hkX ix hix
        have hWk : W k.1 = u.1 k - v.1 k := by simp [W, k.2]
        have hWix : W ix = u.1 ixU - v.1 ixU := by
          have hixU : ix ∈ U := Finset.mem_union_left Y' hix
          have heq : (⟨ix, hixU⟩ : ↑U) = ixU := Subtype.ext (by rfl)
          rw [show W ix = u.1 ⟨ix, hixU⟩ - v.1 ⟨ix, hixU⟩ by
            simp only [W, dif_pos hixU], heq]
        rw [hWk, hWix] at hh
        exact sub_eq_zero.mp (hh.trans (sub_eq_zero.mpr hx0))
      · have hh := hc.2 k.1 hkY iy hiy
        have hWk : W k.1 = u.1 k - v.1 k := by simp [W, k.2]
        have hWiy : W iy = u.1 iyU - v.1 iyU := by
          have hiyU : iy ∈ U := Finset.mem_union_right X' hiy
          have heq : (⟨iy, hiyU⟩ : ↑U) = iyU := Subtype.ext (by rfl)
          rw [show W iy = u.1 ⟨iy, hiyU⟩ - v.1 ⟨iy, hiyU⟩ by
            simp only [W, dif_pos hiyU], heq]
        rw [hWk, hWiy] at hh
        exact sub_eq_zero.mp (hh.trans (sub_eq_zero.mpr hy0))
    have hr := LinearMap.finrank_le_finrank_of_injective hev
    simpa [Module.finrank_pi] using hr
  have hrn := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  have hdomain : Module.finrank ℚ (↑U → ℚ) = U.card := by simp
  rw [hdomain] at hrn
  have hrange : U.card - 2 ≤ Module.finrank ℚ (LinearMap.range A.mulVecLin) := by omega
  have hrank : A.rank = Module.finrank ℚ (LinearMap.range A.mulVecLin) := rfl
  rw [← hrank, A.rank_eq_finrank_span_row] at hrange
  change (X' ∪ Y').card - 2 ≤ Module.finrank ℚ
    (Submodule.span ℚ (Set.range (fun t : ↑(rectangle X' Y') =>
      fun k : ↑(X' ∪ Y') => ((S.rho P t.1 k.1 : ℤ) : ℚ)))) at hrange
  exact hrange


theorem clean_rectangle [Fact p.Prime] (S : MinimalNUS p n) (P : S.Pairing)
    (X Y : Finset (Fin n)) (hX : X.Nonempty) (hY : Y.Nonempty) (hXY : Disjoint X Y)
    (hinv : ∀ t ∈ rectangle X Y, P.μ t ∈ rectangle X Y) :
    p ≤ 2 ^ (X.card + Y.card - 2) := by
  classical
  obtain ⟨X', Y', hXsub, hYsub, hX', hY', hinv', hmin⟩ :=
    exists_minimal_rectangle S P hX hY hinv
  have hXY' : Disjoint X' Y' := hXY.mono hXsub hYsub
  let U := X' ∪ Y'
  let d := U.card - 2
  have hUcard : U.card = X'.card + Y'.card := by
    simpa [U] using Finset.card_union_of_disjoint hXY'
  have hthree : 3 ≤ U.card := by
    rw [hUcard]
    exact three_le_of_invariant S P hX' hY' hinv'
  let rowQ : ↑(rectangle X' Y') → (↑U → ℚ) := fun t k =>
    ((S.rho P t.1 k.1 : ℤ) : ℚ)
  have hrank := finrank_rectRows_ge S P hX' hY' hinv' hmin
  change d ≤ Module.finrank ℚ (Submodule.span ℚ (Set.range rowQ)) at hrank
  obtain ⟨r, hr⟩ := exists_indep_family_of_finrank rowQ d hrank
  obtain ⟨c, hc⟩ := exists_coordinate_minor (fun i => rowQ (r i)) hr
  let B : Matrix (Fin d) (Fin d) ℤ := Matrix.of fun i j => S.rho P (r i).1 (c j).1
  have hBne : B.det ≠ 0 := by
    intro hzero
    have hcast : (B.map (fun z : ℤ => (z : ℚ))).det = 0 := by
      rw [← Int.cast_det, hzero]
      norm_num
    apply hc
    change (B.map (fun z : ℤ => (z : ℚ))).det = 0
    exact hcast
  have hpdiv : (p : ℤ) ∣ B.det := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    let R : Matrix (Fin d) ↑U (ZMod p) := Matrix.of fun i k =>
      ((S.rho P (r i).1 k.1 : ℤ) : ZMod p)
    let K : Matrix ↑U (Fin 3) (ZMod p) := Matrix.of fun k q =>
      if q = 0 then if k.1 ∈ X' then 1 else 0
      else if q = 1 then if k.1 ∈ Y' then 1 else 0
      else S.a k.1
    obtain ⟨ix, hix⟩ := hX'
    obtain ⟨iy, hiy⟩ := hY'
    have hixY : ix ∉ Y' := fun h => Finset.disjoint_left.mp hXY' hix h
    have hiyX : iy ∉ X' := fun h => Finset.disjoint_left.mp hXY' h hiy
    have hextra : ∃ z, (z ∈ X' ∧ z ≠ ix) ∨ (z ∈ Y' ∧ z ≠ iy) := by
      by_contra h
      push Not at h
      have hxle : X'.card ≤ 1 := by
        apply Finset.card_le_one.mpr
        intro a ha b hb
        exact (h a).1 ha |>.trans ((h b).1 hb).symm
      have hyle : Y'.card ≤ 1 := by
        apply Finset.card_le_one.mpr
        intro a ha b hb
        exact (h a).2 ha |>.trans ((h b).2 hb).symm
      rw [hUcard] at hthree
      omega
    obtain ⟨z, hz⟩ := hextra
    have hKli : LinearIndependent (ZMod p) (fun q => K.col q) := by
      rw [Fintype.linearIndependent_iff]
      intro g hg
      have ex := congrFun hg ⟨ix, Finset.mem_union_left Y' hix⟩
      have ey := congrFun hg ⟨iy, Finset.mem_union_right X' hiy⟩
      simp [K, hix, hixY, hiy, hiyX, Fin.sum_univ_succ] at ex ey
      have eg : g 2 = 0 := by
        rcases hz with ⟨hz, hzne⟩ | ⟨hz, hzne⟩
        · have ez := congrFun hg ⟨z, Finset.mem_union_left Y' hz⟩
          have hznot : z ∉ Y' := fun h => Finset.disjoint_left.mp hXY' hz h
          simp [K, hz, hznot, Fin.sum_univ_succ] at ez
          have hm : g 2 * (S.a z - S.a ix) = 0 := by
            linear_combination ez - ex
          rcases mul_eq_zero.mp hm with h0 | h0
          · exact h0
          · exact absurd (sub_eq_zero.mp h0) (fun e => hzne (S.a.injective e))
        · have ez := congrFun hg ⟨z, Finset.mem_union_right X' hz⟩
          have hznot : z ∉ X' := fun h => Finset.disjoint_left.mp hXY' h hz
          simp [K, hz, hznot, Fin.sum_univ_succ] at ez
          have hm : g 2 * (S.a z - S.a iy) = 0 := by
            linear_combination ez - ey
          rcases mul_eq_zero.mp hm with h0 | h0
          · exact h0
          · exact absurd (sub_eq_zero.mp h0) (fun e => hzne (S.a.injective e))
      have e0 : g 0 = 0 := by simpa [eg] using ex
      have e1 : g 1 = 0 := by simpa [eg] using ey
      intro q
      fin_cases q <;> assumption
    have hKrank : K.rank = 3 := by
      have h := hKli.rank_matrix
      simpa using h
    have hRK : R * K = 0 := by
      ext i q
      rw [Matrix.mul_apply]
      have hsupp : ∀ k, k ∉ U → S.rho P (r i).1 k = 0 := by
        intro k hk
        obtain ⟨a, ha, b, hb, ht⟩ := (r i).2
        obtain ⟨a', ha', b', hb', hEq⟩ := hinv' s(a, b) ⟨a, ha, b, hb, rfl⟩
        rw [ht]
        apply rho_apply_eq_zero S P hEq
        · intro e; subst k; exact hk (Finset.mem_union_left _ ha)
        · intro e; subst k; exact hk (Finset.mem_union_right _ hb)
        · intro e; subst k; exact hk (Finset.mem_union_left _ ha')
        · intro e; subst k; exact hk (Finset.mem_union_right _ hb')
      fin_cases q
      · have hs := (sum_rho_rectangle_side_eq_zero S P hXY' hinv' (r i)).1
        change ∑ k : ↑U, ((S.rho P (r i).1 k.1 : ℤ) : ZMod p) *
          (if k.1 ∈ X' then 1 else 0) = 0
        rw [show (∑ k : ↑U, ((S.rho P (r i).1 k.1 : ℤ) : ZMod p) *
            (if k.1 ∈ X' then 1 else 0)) =
            (∑ k : Fin n, ((S.rho P (r i).1 k : ℤ) : ZMod p) *
              (if k ∈ X' then 1 else 0)) by
              simpa [mul_comm, dotProduct] using sum_subtype_mul_eq_dot (R := ZMod p) hsupp
                (fun k => if k ∈ X' then 1 else 0)]
        rw [← Finset.sum_subset (Finset.subset_univ X')]
        · simpa using congrArg (fun z : ℤ => (z : ZMod p)) hs
        · intro k _ hk
          simp [hk]
      · have hs := (sum_rho_rectangle_side_eq_zero S P hXY' hinv' (r i)).2
        change ∑ k : ↑U, ((S.rho P (r i).1 k.1 : ℤ) : ZMod p) *
          (if k.1 ∈ Y' then 1 else 0) = 0
        rw [show (∑ k : ↑U, ((S.rho P (r i).1 k.1 : ℤ) : ZMod p) *
            (if k.1 ∈ Y' then 1 else 0)) =
            (∑ k : Fin n, ((S.rho P (r i).1 k : ℤ) : ZMod p) *
              (if k ∈ Y' then 1 else 0)) by
              simpa [mul_comm, dotProduct] using sum_subtype_mul_eq_dot (R := ZMod p) hsupp
                (fun k => if k ∈ Y' then 1 else 0)]
        rw [← Finset.sum_subset (Finset.subset_univ Y')]
        · simpa using congrArg (fun z : ℤ => (z : ZMod p)) hs
        · intro k _ hk
          simp [hk]
      ·
        have hdot := S.rho_cast_dot_a P (r i).1
        rw [← sum_subtype_mul_eq_dot hsupp (fun k => S.a k)] at hdot
        simpa [R, K, mul_comm] using hdot
    have hranksum := Matrix.rank_add_rank_le_card_of_mul_eq_zero hRK
    rw [hKrank] at hranksum
    have hRrank : R.rank ≤ d - 1 := by
      have hdU : d = U.card - 2 := rfl
      rw [Fintype.card_coe] at hranksum
      omega
    by_contra hdet
    let BM : Matrix (Fin d) (Fin d) (ZMod p) := B.map (fun z : ℤ => (z : ZMod p))
    have hdetM : BM.det ≠ 0 := by
      rw [← Int.cast_det]
      exact hdet
    have hsmallLI : LinearIndependent (ZMod p)
        (fun i => BM.row i) :=
      Matrix.linearIndependent_rows_of_det_ne_zero hdetM
    have hfullLI : LinearIndependent (ZMod p) (fun i => R.row i) := by
      rw [Fintype.linearIndependent_iff] at hsmallLI ⊢
      intro g hg
      apply hsmallLI g
      funext j
      have e := congrFun hg (c j)
      simpa [R, BM, B] using e
    have hfullrank : R.rank = d := by
      have h := hfullLI.rank_matrix
      simpa using h
    omega
  have hBbound : B.det.natAbs ≤ 2 ^ d := by
    let BR : Matrix (Fin d) (Fin d) ℝ := B.map (fun z : ℤ => (z : ℝ))
    have hrow : ∀ i, ‖(WithLp.toLp 2 (BR i) : EuclideanSpace ℝ (Fin d))‖ ≤ 2 := by
      intro i
      rw [EuclideanSpace.norm_eq, Real.sqrt_le_iff]
      constructor
      · norm_num
      have hsel : ∑ j : Fin d, (((S.rho P (r i).1 (c j).1 : ℤ) : ℝ) ^ 2) ≤
          ∑ k : Fin n, (((S.rho P (r i).1 k : ℤ) : ℝ) ^ 2) := by
        let emb : Fin d ↪ Fin n := c.trans ⟨Subtype.val, Subtype.val_injective⟩
        rw [show (∑ j : Fin d, (((S.rho P (r i).1 (c j).1 : ℤ) : ℝ) ^ 2)) =
            ∑ k ∈ Finset.univ.map emb,
              (((S.rho P (r i).1 k : ℤ) : ℝ) ^ 2) by
              rw [Finset.sum_map]
              rfl]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun k _ _ => sq_nonneg _)
      have hfour := sum_sq_rho_rectangle_le_four S P hXY' hinv' (r i)
      simp only [Real.norm_eq_abs, sq_abs]
      dsimp only [BR, Matrix.map_apply]
      change (∑ j : Fin d, (((B i j : ℤ) : ℝ) ^ 2)) ≤ 2 ^ 2
      rw [show (2 : ℝ) ^ 2 = 4 by norm_num]
      change @LE.le ℝ Real.instPreorder.toLE
        (∑ j : Fin d, (((S.rho P (r i).1 (c j).1 : ℤ) : ℝ) ^ 2)) 4
      exact hsel.trans hfour
    have hhad := abs_det_le_prod_euclidean_row_norm BR
    have hprod : ∏ i, ‖(WithLp.toLp 2 (BR i) : EuclideanSpace ℝ (Fin d))‖ ≤
        (2 : ℝ) ^ d := by
      calc
        ∏ i, ‖(WithLp.toLp 2 (BR i) : EuclideanSpace ℝ (Fin d))‖ ≤ ∏ _ : Fin d, (2 : ℝ) :=
          Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => hrow i)
        _ = (2 : ℝ) ^ d := by simp
    have hreal : |(B.det : ℝ)| ≤ (2 : ℝ) ^ d := by
      rw [Int.cast_det]
      exact hhad.trans hprod
    rw [← Nat.cast_le (α := ℤ), Int.natCast_natAbs]
    exact_mod_cast hreal
  have hpB : p ≤ B.det.natAbs := by
    obtain ⟨q, hq⟩ := hpdiv
    have hq0 : q ≠ 0 := by
      intro h
      rw [h, mul_zero] at hq
      exact hBne hq
    rw [hq, Int.natAbs_mul]
    have hp0 : 0 < p := (Fact.out : p.Prime).pos
    have hq1 : 1 ≤ q.natAbs := (Int.natAbs_pos.mpr hq0).nat_succ_le
    simpa using Nat.mul_le_mul_left p hq1
  calc
    p ≤ B.det.natAbs := hpB
    _ ≤ 2 ^ d := hBbound
    _ ≤ 2 ^ (X.card + Y.card - 2) := by
      apply Nat.pow_le_pow_right (by omega)
      dsimp [d, U]
      have hx := Finset.card_le_card hXsub
      have hy := Finset.card_le_card hYsub
      rw [Finset.card_union_of_disjoint hXY']
      omega

end MinimalNUS

end NUS




namespace NUS

universe u


structure Configuration (V : Type*) where
  
  j : V
  
  τ : Sym2 V
  
  not_mem : j ∉ τ


def Hits {V : Type*} (T : Finset V) (c : Configuration V) : Prop :=
  c.j ∈ T ∧ ∃ v ∈ T, v ∈ c.τ



namespace Bernoulli

variable {ι : Type u} [Fintype ι] [DecidableEq ι]




def optionOutcome {i : Type*} (b : Bool) (a : i → Bool) : Option i → Bool
  | none => b
  | some t => a t

@[simp] theorem optionOutcome_none {i : Type*} (b : Bool) (a : i → Bool) :
    optionOutcome b a none = b := rfl

@[simp] theorem optionOutcome_some {i : Type*} (b : Bool) (a : i → Bool) (t : i) :
    optionOutcome b a (some t) = a t := rfl

@[simp] theorem piOptionEquivProd_symm_apply {i : Type*} (b : Bool) (a : i → Bool) :
    (Equiv.piOptionEquivProd (β := fun _ : Option i => Bool)).symm (b, a) =
      optionOutcome b a := by
  funext t
  cases t <;> rfl

theorem update_optionOutcome_none {i : Type*} [DecidableEq i] [DecidableEq (Option i)]
    (b : Bool) (a : i → Bool) :
    Function.update (optionOutcome b a) none false = optionOutcome false a := by
  funext t
  cases t <;> simp [Function.update, optionOutcome]

theorem update_optionOutcome_some {i : Type*} [DecidableEq i] [DecidableEq (Option i)]
    (b : Bool) (a : i → Bool) (t : i) :
    Function.update (optionOutcome b a) (some t) false =
      optionOutcome b (Function.update a t false) := by
  funext u
  cases u <;> simp [Function.update, optionOutcome]


def reindexOutcome {a b : Type*} (e : a ≃ b) (w : b → Bool) : a → Bool :=
  fun t => w (e t)


noncomputable def wt (θ : ℝ) (ω : ι → Bool) : ℝ :=
  ∏ t, if ω t then θ else 1 - θ


noncomputable def expect (θ : ℝ) (F : (ι → Bool) → ℝ) : ℝ :=
  ∑ ω, wt θ ω * F ω


noncomputable def var (θ : ℝ) (F : (ι → Bool) → ℝ) : ℝ :=
  expect θ fun ω => (F ω - expect θ F) ^ 2

theorem wt_reindexOutcome {a b : Type*} [Fintype a] [Fintype b]
    (e : a ≃ b) (θ : ℝ) (w : b → Bool) :
    wt θ (reindexOutcome e w) = wt θ w := by
  unfold wt reindexOutcome
  exact e.prod_comp (fun t => if w t then θ else 1 - θ)

theorem expect_reindexOutcome {a b : Type*} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (e : a ≃ b) (θ : ℝ) (F : (a → Bool) → ℝ) :
    expect θ F = expect θ (fun w : b → Bool => F (reindexOutcome e w)) := by
  unfold expect
  rw [← Equiv.sum_comp (Equiv.piCongrLeft (fun _ : b => Bool) e).symm
    (fun w => wt θ w * F w)]
  apply Finset.sum_congr rfl
  intro w hw
  have hq : (Equiv.piCongrLeft (fun _ : b => Bool) e).symm w = reindexOutcome e w := by
    funext t
    simp [reindexOutcome]
  rw [hq]
  rw [wt_reindexOutcome]

theorem var_reindexOutcome {a b : Type*} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (e : a ≃ b) (θ : ℝ) (F : (a → Bool) → ℝ) :
    var θ F = var θ (fun w : b → Bool => F (reindexOutcome e w)) := by
  unfold var
  rw [expect_reindexOutcome e θ]
  rw [expect_reindexOutcome e θ F]

theorem reindexOutcome_update {a b : Type*} [DecidableEq a] [DecidableEq b]
    (e : a ≃ b) (w : b → Bool) (t : a) :
    reindexOutcome e (Function.update w (e t) false) =
      Function.update (reindexOutcome e w) t false := by
  funext u
  by_cases h : u = t
  · subst u
    simp [reindexOutcome]
  · have he : e u ≠ e t := fun h' => h (e.injective h')
    simp [reindexOutcome, Function.update, h, he]

theorem switchEnergy_reindexOutcome {a b : Type*} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (e : a ≃ b) (F : (a → Bool) → ℝ) (w : b → Bool) :
    (∑ u : b, (F (reindexOutcome e w) -
        F (reindexOutcome e (Function.update w u false))) ^ 2) =
      ∑ t : a, (F (reindexOutcome e w) -
        F (Function.update (reindexOutcome e w) t false)) ^ 2 := by
  rw [← e.sum_comp]
  apply Finset.sum_congr rfl
  intro t ht
  rw [reindexOutcome_update]

omit [DecidableEq ι] in
theorem wt_nonneg {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (ω : ι → Bool) : 0 ≤ wt θ ω :=
  Finset.prod_nonneg fun t _ => by
    by_cases h : ω t <;> simp [h] <;> linarith


theorem sum_wt (θ : ℝ) : ∑ ω : ι → Bool, wt θ ω = 1 := by
  classical
  have h := Finset.prod_univ_sum (fun _ : ι => (Finset.univ : Finset Bool))
    fun _ b => if b then θ else 1 - θ
  rw [Fintype.piFinset_univ] at h
  unfold wt
  rw [← h]
  simp

omit [DecidableEq ι] in
theorem wt_pos {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (ω : ι → Bool) : 0 < wt θ ω :=
  Finset.prod_pos fun t _ => by
    by_cases h : ω t <;> simp [h] <;> linarith


theorem expect_option {i : Type*} [Fintype i] [DecidableEq i] [DecidableEq (Option i)] (θ : ℝ)
    (F : (Option i → Bool) → ℝ) :
    expect θ F = θ * expect θ (fun a : i → Bool => F (optionOutcome true a))
      + (1 - θ) * expect θ (fun a : i → Bool => F (optionOutcome false a)) := by
  classical
  unfold expect wt
  rw [← Equiv.sum_comp (Equiv.piOptionEquivProd (β := fun _ => Bool)).symm
    (fun ω => (∏ t, if ω t then θ else 1 - θ) * F ω)]
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [piOptionEquivProd_symm_apply, Fintype.prod_option, optionOutcome_none,
    optionOutcome_some, if_true, Bool.false_eq_true, if_false]
  change (∑ a : i → Bool, (θ * ∏ t, if a t then θ else 1 - θ) *
      F (optionOutcome true a))
    + ∑ a : i → Bool, ((1 - θ) * ∏ t, if a t then θ else 1 - θ) *
      F (optionOutcome false a) = _
  rw [Finset.mul_sum, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro a ha <;> ring


theorem var_eq_expect_sq_sub (θ : ℝ) (F : (ι → Bool) → ℝ) :
    var θ F = expect θ (fun ω => (F ω) ^ 2) - (expect θ F) ^ 2 := by
  unfold var expect
  have hpoint : ∀ ω : ι → Bool,
      wt θ ω * (F ω - ∑ ω, wt θ ω * F ω) ^ 2 =
      wt θ ω * F ω ^ 2
        - 2 * (∑ ω, wt θ ω * F ω) * (wt θ ω * F ω)
        + (∑ ω, wt θ ω * F ω) ^ 2 * wt θ ω := by
    intro ω
    ring
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, sum_wt]
  ring


theorem sq_expect_le_expect_sq {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (F : (ι → Bool) → ℝ) :
    (expect θ F) ^ 2 ≤ expect θ (fun ω => (F ω) ^ 2) := by
  unfold expect
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (ι → Bool))
    (fun ω => Real.sqrt (wt θ ω)) (fun ω => Real.sqrt (wt θ ω) * F ω)
  have hsqrt : ∀ ω : ι → Bool, (Real.sqrt (wt θ ω)) ^ 2 = wt θ ω := by
    intro ω
    exact Real.sq_sqrt (wt_nonneg hθ0 hθ1 ω)
  have hmul : ∀ ω : ι → Bool,
      Real.sqrt (wt θ ω) * Real.sqrt (wt θ ω) = wt θ ω := by
    intro ω
    exact Real.mul_self_sqrt (wt_nonneg hθ0 hθ1 ω)
  simpa only [← mul_assoc, hmul, hsqrt, one_mul, sum_wt, mul_one, mul_pow] using hcs

theorem expect_nonneg {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) {F : (ι → Bool) → ℝ}
    (hF : ∀ ω, 0 ≤ F ω) : 0 ≤ expect θ F :=
  Finset.sum_nonneg fun ω _ => mul_nonneg (wt_nonneg hθ0 hθ1 ω) (hF ω)

theorem expect_mono {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) {F G : (ι → Bool) → ℝ}
    (h : ∀ ω, F ω ≤ G ω) : expect θ F ≤ expect θ G :=
  Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (h ω) (wt_nonneg hθ0 hθ1 ω)


theorem expect_const (θ c : ℝ) : expect θ (fun _ : ι → Bool => c) = c := by
  unfold expect
  rw [← Finset.sum_mul, sum_wt, one_mul]

theorem expect_add (θ : ℝ) (F G : (ι → Bool) → ℝ) :
    expect θ (fun ω => F ω + G ω) = expect θ F + expect θ G := by
  unfold expect
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun ω _ => mul_add _ _ _

theorem expect_sub (θ : ℝ) (F G : (ι → Bool) → ℝ) :
    expect θ (fun ω => F ω - G ω) = expect θ F - expect θ G := by
  unfold expect
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun ω _ => mul_sub _ _ _

theorem expect_const_mul (θ c : ℝ) (F : (ι → Bool) → ℝ) :
    expect θ (fun ω => c * F ω) = c * expect θ F := by
  unfold expect
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun ω _ => by ring

theorem expect_sum {κ : Type*} (θ : ℝ) (s : Finset κ) (F : κ → (ι → Bool) → ℝ) :
    expect θ (fun ω => ∑ k ∈ s, F k ω) = ∑ k ∈ s, expect θ (F k) := by
  unfold expect
  calc ∑ ω, wt θ ω * ∑ k ∈ s, F k ω
      = ∑ ω, ∑ k ∈ s, wt θ ω * F k ω :=
        Finset.sum_congr rfl fun ω _ => Finset.mul_sum _ _ _
    _ = ∑ k ∈ s, ∑ ω, wt θ ω * F k ω := Finset.sum_comm


theorem exists_expect_le {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (F : (ι → Bool) → ℝ) :
    ∃ ω : ι → Bool, expect θ F ≤ F ω := by
  by_contra h
  push Not at h
  have h1 : expect θ F < expect θ F := by
    conv_rhs => rw [← expect_const θ (expect θ F) (ι := ι)]
    unfold expect
    exact Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun ω _ =>
      mul_lt_mul_of_pos_left (h ω) (wt_pos hθ0 hθ1 ω)
  exact lt_irrefl _ h1


theorem exists_le_expect {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (F : (ι → Bool) → ℝ) :
    ∃ ω : ι → Bool, F ω ≤ expect θ F := by
  by_contra h
  push Not at h
  have h1 : expect θ F < expect θ F := by
    conv_lhs => rw [← expect_const θ (expect θ F) (ι := ι)]
    unfold expect
    exact Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun ω _ =>
      mul_lt_mul_of_pos_left (h ω) (wt_pos hθ0 hθ1 ω)
  exact lt_irrefl _ h1


theorem expect_prod_comp (θ : ℝ) (g : ι → Bool → ℝ) :
    expect θ (fun ω => ∏ t, g t (ω t)) = ∏ t, (θ * g t true + (1 - θ) * g t false) := by
  have h := Finset.prod_univ_sum (fun _ : ι => (Finset.univ : Finset Bool))
    fun t b => (if b then θ else 1 - θ) * g t b
  rw [Fintype.piFinset_univ] at h
  unfold expect wt
  calc ∑ ω : ι → Bool, (∏ t, if ω t then θ else 1 - θ) * ∏ t, g t (ω t)
      = ∑ ω : ι → Bool, ∏ t, (if ω t then θ else 1 - θ) * g t (ω t) :=
        Finset.sum_congr rfl fun ω _ => (Finset.prod_mul_distrib).symm
    _ = ∏ t, ∑ b : Bool, (if b then θ else 1 - θ) * g t b := h.symm
    _ = ∏ t, (θ * g t true + (1 - θ) * g t false) :=
        Finset.prod_congr rfl fun t _ => by rw [Fintype.sum_bool]; simp


theorem expect_cylinder (θ : ℝ) (S T : Finset ι) (hd : Disjoint S T) :
    expect θ (fun ω => if (∀ i ∈ S, ω i = true) ∧ (∀ i ∈ T, ω i = false) then (1 : ℝ) else 0)
      = θ ^ S.card * (1 - θ) ^ T.card := by
  have key : (fun ω : ι → Bool =>
        if (∀ i ∈ S, ω i = true) ∧ (∀ i ∈ T, ω i = false) then (1 : ℝ) else 0)
      = fun ω => ∏ t, (if t ∈ S then (if ω t then (1 : ℝ) else 0)
          else if t ∈ T then (if ω t then (0 : ℝ) else 1) else 1) := by
    funext ω
    by_cases h : (∀ i ∈ S, ω i = true) ∧ (∀ i ∈ T, ω i = false)
    · rw [if_pos h]
      refine (Finset.prod_eq_one fun t _ => ?_).symm
      by_cases hS : t ∈ S
      · simp [hS, h.1 t hS]
      · by_cases hT : t ∈ T
        · simp [hS, hT, h.2 t hT]
        · simp [hS, hT]
    · rw [if_neg h]
      push Not at h
      by_cases hA : ∀ i ∈ S, ω i = true
      · obtain ⟨i, hiT, hi⟩ := h hA
        simp only [ne_eq, Bool.not_eq_false] at hi
        refine (Finset.prod_eq_zero (Finset.mem_univ i) ?_).symm
        have hiS : i ∉ S := Finset.disjoint_right.mp hd hiT
        simp [hiS, hiT, hi]
      · push Not at hA
        obtain ⟨i, hiS, hi⟩ := hA
        simp only [ne_eq, Bool.not_eq_true] at hi
        refine (Finset.prod_eq_zero (Finset.mem_univ i) ?_).symm
        simp [hiS, hi]
  have h2 : ∀ t : ι, θ * (if t ∈ S then (if (true : Bool) then (1 : ℝ) else 0)
        else if t ∈ T then (if (true : Bool) then (0 : ℝ) else 1) else 1)
      + (1 - θ) * (if t ∈ S then (if (false : Bool) then (1 : ℝ) else 0)
        else if t ∈ T then (if (false : Bool) then (0 : ℝ) else 1) else 1)
      = (if t ∈ S then θ else if t ∈ T then 1 - θ else 1) := by
    intro t
    by_cases hS : t ∈ S
    · simp [hS]
    · by_cases hT : t ∈ T <;> simp [hS, hT]
  have h3 : (∏ t ∈ Finset.univ.filter (· ∈ S),
      (if t ∈ S then θ else if t ∈ T then 1 - θ else 1)) = θ ^ S.card := by
    rw [Finset.filter_univ_mem]
    rw [Finset.prod_congr rfl fun t ht => if_pos ht]
    exact Finset.prod_const θ
  have h4 : (∏ t ∈ Finset.univ.filter (fun t => ¬ t ∈ S),
      (if t ∈ S then θ else if t ∈ T then 1 - θ else 1)) = (1 - θ) ^ T.card := by
    rw [Finset.prod_congr rfl fun t ht => if_neg ((Finset.mem_filter.mp ht).2)]
    rw [Finset.prod_ite_mem]
    have hTsub : Finset.univ.filter (fun t => ¬ t ∈ S) ∩ T = T := by
      rw [Finset.inter_eq_right]
      intro u hu
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ u, Finset.disjoint_right.mp hd hu⟩
    rw [hTsub]
    exact Finset.prod_const _
  rw [key]
  refine (expect_prod_comp θ (fun t b => if t ∈ S then (if b then (1 : ℝ) else 0)
      else if t ∈ T then (if b then (0 : ℝ) else 1) else 1)).trans ?_
  refine (Finset.prod_congr rfl fun t _ => h2 t).trans ?_
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (· ∈ S), h3, h4]


def merge (p : ι → Prop) [DecidablePred p] (a : {i // p i} → Bool) (b : {i // ¬ p i} → Bool) :
    ι → Bool := fun i => if h : p i then a ⟨i, h⟩ else b ⟨i, h⟩

omit [DecidableEq ι] in
theorem wt_merge (θ : ℝ) (p : ι → Prop) [DecidablePred p]
    (a : {i // p i} → Bool) (b : {i // ¬ p i} → Bool) :
    wt θ (merge p a b) = wt θ a * wt θ b := by
  unfold wt merge
  rw [← Fintype.prod_subtype_mul_prod_subtype p
    (fun i => if (if h : p i then a ⟨i, h⟩ else b ⟨i, h⟩) then θ else 1 - θ)]
  congr 1
  · exact Finset.prod_congr rfl fun i _ => by rw [dif_pos i.2]
  · exact Finset.prod_congr rfl fun i _ => by rw [dif_neg i.2]


theorem expect_split (θ : ℝ) (p : ι → Prop) [DecidablePred p] (F : (ι → Bool) → ℝ) :
    expect θ F = expect θ (fun a : {i // p i} → Bool =>
      expect θ (fun b : {i // ¬ p i} → Bool => F (merge p a b))) := by
  unfold expect
  rw [← Equiv.sum_comp (Equiv.piEquivPiSubtypeProd p (fun _ => Bool)).symm
    (fun ω => wt θ ω * F ω)]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hm : (Equiv.piEquivPiSubtypeProd p (fun _ => Bool)).symm (a, b) = merge p a b := rfl
  rw [hm, wt_merge]
  ring

end Bernoulli




theorem one_sub_pow_le_inv {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (d : ℕ) :
    (1 - θ) ^ d ≤ 1 / (1 + θ * d) := by
  induction d with
  | zero => norm_num
  | succ n ih =>
    have hpos : (0 : ℝ) < 1 + θ * n := by positivity
    have hpos' : (0 : ℝ) < 1 + θ * (n + 1 : ℕ) := by positivity
    calc (1 - θ) ^ (n + 1) = (1 - θ) ^ n * (1 - θ) := pow_succ _ _
      _ ≤ (1 / (1 + θ * n)) * (1 - θ) :=
          mul_le_mul_of_nonneg_right ih (by linarith)
      _ ≤ 1 / (1 + θ * (n + 1 : ℕ)) := by
          rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ hpos hpos']
          push_cast
          nlinarith [sq_nonneg θ]


theorem half_le_one_sub_pow {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) {d : ℕ}
    (hd : 1 ≤ θ * d) : (1 / 2 : ℝ) ≤ 1 - (1 - θ) ^ d := by
  have h := one_sub_pow_le_inv hθ0 hθ1 d
  have hpos : (0 : ℝ) < 1 + θ * d := by positivity
  have h2 : (1 : ℝ) / (1 + θ * d) ≤ 1 / 2 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    linarith
  linarith


theorem lin_le_one_sub_pow {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) {d : ℕ}
    (hd : θ * d ≤ 1) : θ * d / 2 ≤ 1 - (1 - θ) ^ d := by
  have h := one_sub_pow_le_inv hθ0 hθ1 d
  have hpos : (0 : ℝ) < 1 + θ * d := by positivity
  have hd0 : (0 : ℝ) ≤ θ * d := by positivity
  have h2 : (1 : ℝ) / (1 + θ * d) ≤ 1 - θ * d / 2 := by
    rw [div_le_iff₀ hpos]
    nlinarith
  linarith


theorem one_sub_pow_le_exp {θ : ℝ} (_hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (n : ℕ) :
    (1 - θ) ^ n ≤ Real.exp (-(θ * n)) := by
  have h1 : 1 - θ ≤ Real.exp (-θ) := by
    have := Real.add_one_le_exp (-θ)
    linarith
  calc (1 - θ) ^ n ≤ Real.exp (-θ) ^ n := pow_le_pow_left₀ (by linarith) h1 n
    _ = Real.exp (-(θ * n)) := by
        rw [← Real.exp_nat_mul]
        ring_nf

theorem exp_neg_eight_le : Real.exp (-8) ≤ (1 / 256 : ℝ) := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by
    (convert Real.add_one_le_exp 1 using 1; norm_num)
  have hp : (256 : ℝ) ≤ Real.exp 1 ^ (8 : ℕ) := by
    calc (256 : ℝ) = 2 ^ (8 : ℕ) := by norm_num
      _ ≤ Real.exp 1 ^ (8 : ℕ) := pow_le_pow_left₀ (by norm_num) h2 8
  have he : (256 : ℝ) ≤ Real.exp 8 := by
    rw [show (8 : ℝ) = (8 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
    simpa using hp
  rw [Real.exp_neg, one_div]
  exact (inv_le_inv₀ (Real.exp_pos 8) (by norm_num)).2 he

namespace Bernoulli

variable {ι : Type u} [Fintype ι] [DecidableEq ι]


theorem var_option {i : Type*} [Fintype i] [DecidableEq i] [DecidableEq (Option i)]
    (θ : ℝ) (F : (Option i → Bool) → ℝ) :
    var θ F =
      θ * var θ (fun a : i → Bool => F (optionOutcome true a))
      + (1 - θ) * var θ (fun a : i → Bool => F (optionOutcome false a))
      + θ * (1 - θ) *
        (expect θ (fun a : i → Bool => F (optionOutcome true a))
          - expect θ (fun a : i → Bool => F (optionOutcome false a))) ^ 2 := by
  rw [var_eq_expect_sq_sub, expect_option, expect_option,
    var_eq_expect_sq_sub, var_eq_expect_sq_sub]
  ring


theorem switchEnergy_option {i : Type*} [Fintype i] [DecidableEq i] [DecidableEq (Option i)]
    (θ : ℝ) (F : (Option i → Bool) → ℝ) :
    expect θ (fun ω => ∑ t, (F ω - F (Function.update ω t false)) ^ 2) =
      θ * expect θ (fun a : i → Bool =>
        (F (optionOutcome true a) - F (optionOutcome false a)) ^ 2)
      + θ * expect θ (fun a : i → Bool => ∑ t,
        (F (optionOutcome true a) -
          F (optionOutcome true (Function.update a t false))) ^ 2)
      + (1 - θ) * expect θ (fun a : i → Bool => ∑ t,
        (F (optionOutcome false a) -
          F (optionOutcome false (Function.update a t false))) ^ 2) := by
  rw [expect_option]
  have htrue : (fun a : i → Bool => ∑ t : Option i,
        (F (optionOutcome true a) -
          F (Function.update (optionOutcome true a) t false)) ^ 2) =
      (fun a => (F (optionOutcome true a) - F (optionOutcome false a)) ^ 2
        + ∑ t : i, (F (optionOutcome true a) -
          F (optionOutcome true (Function.update a t false))) ^ 2) := by
    funext a
    rw [Fintype.sum_option, update_optionOutcome_none]
    congr 1
    apply Finset.sum_congr rfl
    intro t ht
    rw [update_optionOutcome_some]
  have hfalse : (fun a : i → Bool => ∑ t : Option i,
        (F (optionOutcome false a) -
          F (Function.update (optionOutcome false a) t false)) ^ 2) =
      (fun a => ∑ t : i, (F (optionOutcome false a) -
        F (optionOutcome false (Function.update a t false))) ^ 2) := by
    funext a
    rw [Fintype.sum_option, update_optionOutcome_none]
    rw [sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add]
    apply Finset.sum_congr rfl
    intro t ht
    rw [update_optionOutcome_some]
  rw [htrue, hfalse, expect_add]
  ring


theorem efron_stein_option {i : Type*} [Fintype i] [DecidableEq i]
    [DecidableEq (Option i)]
    (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (ih : ∀ G : (i → Bool) → ℝ,
      var θ G ≤ expect θ fun a => ∑ t, (G a - G (Function.update a t false)) ^ 2)
    (F : (Option i → Bool) → ℝ) :
    var θ F ≤ expect θ fun ω => ∑ t, (F ω - F (Function.update ω t false)) ^ 2 := by
  let F₁ : (i → Bool) → ℝ := fun a => F (optionOutcome true a)
  let F₀ : (i → Bool) → ℝ := fun a => F (optionOutcome false a)
  have hJ : (expect θ F₁ - expect θ F₀) ^ 2 ≤
      expect θ (fun a => (F₁ a - F₀ a) ^ 2) := by
    rw [← expect_sub]
    exact sq_expect_le_expect_sq hθ0 hθ1 (fun a => F₁ a - F₀ a)
  have hcoef : 0 ≤ θ * (1 - θ) := mul_nonneg hθ0 (by linarith)
  have hcross : θ * (1 - θ) * (expect θ F₁ - expect θ F₀) ^ 2 ≤
      θ * expect θ (fun a => (F₁ a - F₀ a) ^ 2) := by
    calc
      θ * (1 - θ) * (expect θ F₁ - expect θ F₀) ^ 2
          ≤ θ * (1 - θ) * expect θ (fun a => (F₁ a - F₀ a) ^ 2) :=
            mul_le_mul_of_nonneg_left hJ hcoef
      _ ≤ θ * expect θ (fun a => (F₁ a - F₀ a) ^ 2) := by
        have hE : 0 ≤ expect θ (fun a => (F₁ a - F₀ a) ^ 2) :=
          expect_nonneg hθ0 hθ1 fun a => sq_nonneg _
        calc
          θ * (1 - θ) * expect θ (fun a => (F₁ a - F₀ a) ^ 2) =
              (1 - θ) * (θ * expect θ (fun a => (F₁ a - F₀ a) ^ 2)) := by ring
          _ ≤ 1 * (θ * expect θ (fun a => (F₁ a - F₀ a) ^ 2)) :=
            mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hθ0 hE)
          _ = _ := one_mul _
  rw [var_option, switchEnergy_option]
  dsimp only [F₁, F₀] at hcross ⊢
  have h1 := ih (fun a => F (optionOutcome true a))
  have h0 := ih (fun a => F (optionOutcome false a))
  have hc1 : 0 ≤ θ := hθ0
  have hc0 : 0 ≤ 1 - θ := by linarith
  have hh1 := mul_le_mul_of_nonneg_left h1 hc1
  have hh0 := mul_le_mul_of_nonneg_left h0 hc0
  linarith


theorem efron_stein_of_equiv {a b : Type*} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (e : a ≃ b) (θ : ℝ)
    (h : ∀ G : (b → Bool) → ℝ,
      var θ G ≤ expect θ fun w => ∑ u, (G w - G (Function.update w u false)) ^ 2)
    (F : (a → Bool) → ℝ) :
    var θ F ≤ expect θ fun w => ∑ t, (F w - F (Function.update w t false)) ^ 2 := by
  let G : (b → Bool) → ℝ := fun w => F (reindexOutcome e w)
  rw [var_reindexOutcome e θ F]
  rw [expect_reindexOutcome e θ
    (fun w => ∑ t, (F w - F (Function.update w t false)) ^ 2)]
  have hG := h G
  apply hG.trans_eq
  apply congrArg (expect θ)
  funext w
  exact switchEnergy_reindexOutcome e F w


def EfronProperty (a : Type u) [Fintype a] [DecidableEq a] : Prop :=
  ∀ (θ : ℝ), 0 ≤ θ → θ ≤ 1 → ∀ G : (a → Bool) → ℝ,
    var θ G ≤ expect θ fun w => ∑ t, (G w - G (Function.update w t false)) ^ 2


theorem efron_stein (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (F : (ι → Bool) → ℝ) :
    var θ F ≤ expect θ fun ω => ∑ t, (F ω - F (Function.update ω t false)) ^ 2 := by
  classical
  let P := fun (a : Type u) [fa : Fintype a] =>
    ∀ da : DecidableEq a, @EfronProperty a fa da
  have hall : P ι := Fintype.induction_empty_option (P := P)
    (fun a b _ e ha => by
      intro db
      letI : DecidableEq b := db
      unfold EfronProperty
      intro θ h0 h1 G
      letI : Fintype a := Fintype.ofEquiv b e.symm
      let da : DecidableEq a := Classical.decEq a
      letI : DecidableEq a := da
      exact efron_stein_of_equiv e.symm θ (ha da θ h0 h1) G)
    (by
      intro de
      letI : DecidableEq PEmpty := de
      unfold EfronProperty
      intro θ h0 h1 G
      let w₀ : PEmpty → Bool := fun x => nomatch x
      have hG : G = fun _ => G w₀ := by
        funext w
        exact congrArg G (Subsingleton.elim _ _)
      rw [hG]
      simp [var, expect_const])
    (fun a _ ha => by
      intro dopt
      let da : DecidableEq a := Classical.decEq a
      letI : DecidableEq a := da
      letI : DecidableEq (Option a) := dopt
      unfold EfronProperty
      intro θ h0 h1 G
      exact efron_stein_option θ h0 h1 (ha da θ h0 h1) G)
    ι
  exact hall (inferInstance : DecidableEq ι) θ hθ0 hθ1 F

end Bernoulli



section Coverage

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in

theorem sym2_card_le (z : Sym2 V) (s : Finset V) (h : ∀ v ∈ s, v ∈ z) : s.card ≤ 2 := by
  induction z using Sym2.inductionOn with
  | hf x y =>
    have hsub : s ⊆ ({x, y} : Finset V) := by
      intro v hv
      rcases Sym2.mem_iff.mp (h v hv) with h1 | h1 <;> simp [h1]
    calc s.card ≤ ({x, y} : Finset V).card := Finset.card_le_card hsub
      _ ≤ 2 := le_trans (Finset.card_insert_le _ _) (by simp)

omit [Fintype V] in

theorem sym2_mem_image_product (H : Finset V) (z : Sym2 V) (h : ∀ v ∈ z, v ∈ H) :
    z ∈ (H ×ˢ H).image (fun p : V × V => s(p.1, p.2)) := by
  induction z using Sym2.inductionOn with
  | hf x y =>
    refine Finset.mem_image.mpr ⟨(x, y), ?_, rfl⟩
    exact Finset.mem_product.mpr ⟨h x (Sym2.mem_mk_left x y), h y (Sym2.mem_mk_right x y)⟩


def retained (F : Finset (Configuration V)) (σ : V → Bool) : Finset (Configuration V) :=
  F.filter fun c => σ c.j = true ∧ ∀ v ∈ c.τ, σ v = false

theorem mem_retained {F : Finset (Configuration V)} {σ : V → Bool}
    {c : Configuration V} :
    c ∈ retained F σ ↔ c ∈ F ∧ σ c.j = true ∧ ∀ v ∈ c.τ, σ v = false := by
  simp [retained]


theorem exists_large_retained (F : Finset (Configuration V)) :
    ∃ σ : V → Bool, F.card ≤ 8 * (retained F σ).card := by
  classical
  let Z : (V → Bool) → ℝ := fun σ => ((retained F σ).card : ℝ)
  have hZ : ∀ σ : V → Bool, Z σ = ∑ c ∈ F,
      if σ c.j = true ∧ ∀ v ∈ c.τ.toFinset, σ v = false then (1 : ℝ) else 0 := by
    intro σ
    simp only [Z, retained, Finset.card_filter]
    push_cast
    apply Finset.sum_congr rfl
    intro c hc
    apply if_congr
    · simp only [Sym2.mem_toFinset]
    · rfl
    · rfl
  have hterm : ∀ c : Configuration V,
      (1 / 8 : ℝ) ≤ Bernoulli.expect (1 / 2) (fun σ : V → Bool =>
        if σ c.j = true ∧ ∀ v ∈ c.τ.toFinset, σ v = false then (1 : ℝ) else 0) := by
    intro c
    have hd : Disjoint ({c.j} : Finset V) c.τ.toFinset := by
      rw [Finset.disjoint_left]
      intro v hvj hvτ
      rw [Finset.mem_singleton] at hvj
      subst v
      exact c.not_mem (Sym2.mem_toFinset.mp hvτ)
    rw [show (fun σ : V → Bool =>
          if σ c.j = true ∧ ∀ v ∈ c.τ.toFinset, σ v = false then (1 : ℝ) else 0) =
        (fun σ => if (∀ i ∈ ({c.j} : Finset V), σ i = true) ∧
          (∀ i ∈ c.τ.toFinset, σ i = false) then (1 : ℝ) else 0) by
          funext σ; simp]
    rw [Bernoulli.expect_cylinder (1 / 2) {c.j} c.τ.toFinset hd]
    simp only [Finset.card_singleton, pow_one]
    have hc : c.τ.toFinset.card ≤ 2 := by
      rw [Sym2.card_toFinset]
      split <;> omega
    interval_cases hcard : c.τ.toFinset.card <;> norm_num
  have hEZ : (F.card : ℝ) / 8 ≤ Bernoulli.expect (1 / 2) Z := by
    rw [show Z = (fun σ : V → Bool => ∑ c ∈ F,
      if σ c.j = true ∧ ∀ v ∈ c.τ.toFinset, σ v = false then (1 : ℝ) else 0) from
        funext hZ]
    rw [Bernoulli.expect_sum]
    have hs : (∑ c ∈ F, (1 / 8 : ℝ)) ≤ ∑ c ∈ F,
        Bernoulli.expect (1 / 2) (fun σ : V → Bool =>
          if σ c.j = true ∧ ∀ v ∈ c.τ.toFinset, σ v = false then (1 : ℝ) else 0) :=
      Finset.sum_le_sum fun c _ => hterm c
    simpa [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv] using hs
  obtain ⟨σ, hσ⟩ := Bernoulli.exists_expect_le (θ := (1 / 2 : ℝ)) (by norm_num) (by norm_num) Z
  refine ⟨σ, ?_⟩
  have hreal : (F.card : ℝ) ≤ 8 * ((retained F σ).card : ℝ) := by
    dsimp only [Z] at hσ
    linarith
  exact_mod_cast hreal


def offSide (σ : V → Bool) : Finset V := Finset.univ.filter (fun v => σ v = false)

omit [DecidableEq V] in
theorem mem_offSide {σ : V → Bool} {v : V} : v ∈ offSide σ ↔ σ v = false := by
  unfold offSide; simp


def covSet (R : Finset (Configuration V)) (v : V) : Finset V :=
  (R.filter (fun c => v ∈ c.τ)).image Configuration.j

omit [Fintype V] in
theorem mem_covSet {R : Finset (Configuration V)} {v u : V} :
    u ∈ covSet R v ↔ ∃ c ∈ R, v ∈ c.τ ∧ c.j = u := by
  unfold covSet
  simp [Finset.mem_image, Finset.mem_filter, and_assoc]


def coveredSet (R : Finset (Configuration V)) (σ : V → Bool) (ω : V → Bool) : Finset V :=
  (offSide σ).filter (fun v => ∃ u ∈ covSet R v, ω u = true)

theorem mem_coveredSet {R : Finset (Configuration V)} {σ ω : V → Bool} {v : V} :
    v ∈ coveredSet R σ ω ↔ σ v = false ∧ ∃ u ∈ covSet R v, ω u = true := by
  unfold coveredSet
  rw [Finset.mem_filter, mem_offSide]

theorem coveredSet_update_subset (R : Finset (Configuration V)) (σ ω : V → Bool) (u : V) :
    coveredSet R σ (Function.update ω u false) ⊆ coveredSet R σ ω := by
  intro v hv
  obtain ⟨h1, w, hw, hww⟩ := mem_coveredSet.mp hv
  refine mem_coveredSet.mpr ⟨h1, w, hw, ?_⟩
  by_cases h : w = u
  · subst h
    rw [Function.update_self] at hww
    simp at hww
  · rwa [Function.update_of_ne h] at hww


def loseSet (R : Finset (Configuration V)) (σ ω : V → Bool) (u : V) : Finset V :=
  coveredSet R σ ω \ coveredSet R σ (Function.update ω u false)

theorem card_loseSet (R : Finset (Configuration V)) (σ ω : V → Bool) (u : V) :
    (loseSet R σ ω u).card
      = (coveredSet R σ ω).card - (coveredSet R σ (Function.update ω u false)).card :=
  Finset.card_sdiff_of_subset (coveredSet_update_subset R σ ω u)


theorem eq_of_mem_loseSet {R : Finset (Configuration V)} {σ ω : V → Bool} {u v w : V}
    (hv : v ∈ loseSet R σ ω u) (hw : w ∈ covSet R v) (hww : ω w = true) : w = u := by
  rw [loseSet, Finset.mem_sdiff] at hv
  by_contra hne
  apply hv.2
  exact mem_coveredSet.mpr ⟨(mem_coveredSet.mp hv.1).1, w, hw,
    by rwa [Function.update_of_ne hne]⟩


theorem card_loseSet_le_two {R : Finset (Configuration V)}
    (hj : Set.InjOn Configuration.j (R : Set (Configuration V))) (σ ω : V → Bool) (u : V) :
    (loseSet R σ ω u).card ≤ 2 := by
  by_cases hc : ∃ c ∈ R, c.j = u
  · obtain ⟨c, hcR, hcj⟩ := hc
    refine sym2_card_le c.τ _ fun v hv => ?_
    have hv1 : v ∈ coveredSet R σ ω := (Finset.mem_sdiff.mp hv).1
    obtain ⟨hoff, w, hw, hww⟩ := mem_coveredSet.mp hv1
    have hwu : w = u := eq_of_mem_loseSet hv hw hww
    subst hwu
    obtain ⟨c', hc'R, hvτ, hc'j⟩ := mem_covSet.mp hw
    have hcc : c' = c := hj hc'R hcR (hc'j.trans hcj.symm)
    exact hcc ▸ hvτ
  · have hempty : loseSet R σ ω u = ∅ := by
      rw [loseSet, Finset.sdiff_eq_empty_iff_subset]
      intro v hv
      obtain ⟨hoff, w, hw, hww⟩ := mem_coveredSet.mp hv
      refine mem_coveredSet.mpr ⟨hoff, w, hw, ?_⟩
      have hne : w ≠ u := by
        intro h
        subst h
        obtain ⟨c', hc'R, _, hc'j⟩ := mem_covSet.mp hw
        exact hc ⟨c', hc'R, hc'j⟩
      rwa [Function.update_of_ne hne]
    rw [hempty]
    simp


theorem sum_card_loseSet_le (R : Finset (Configuration V)) (σ ω : V → Bool) :
    ∑ u : V, (loseSet R σ ω u).card ≤ (coveredSet R σ ω).card := by
  have hdisj : (↑(Finset.univ : Finset V) : Set V).PairwiseDisjoint (loseSet R σ ω) := by
    intro u _ u' _ hne
    refine Finset.disjoint_left.mpr fun v hv hv' => hne ?_
    obtain ⟨hoff, w, hw, hww⟩ := mem_coveredSet.mp (Finset.mem_sdiff.mp hv).1
    exact (eq_of_mem_loseSet hv hw hww).symm.trans (eq_of_mem_loseSet hv' hw hww)
  calc ∑ u : V, (loseSet R σ ω u).card
      = (Finset.univ.biUnion (loseSet R σ ω)).card := (Finset.card_biUnion hdisj).symm
    _ ≤ (coveredSet R σ ω).card := Finset.card_le_card (by
        intro v hv
        obtain ⟨u, _, hvu⟩ := Finset.mem_biUnion.mp hv
        exact (Finset.mem_sdiff.mp hvu).1)

end Coverage

section MissBound

open Bernoulli

variable {V : Type*} [Fintype V] [DecidableEq V]


theorem miss_bound (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (R : Finset (Configuration V)) (σ : V → Bool)
    (hret : ∀ c ∈ R, σ c.j = true ∧ ∀ v ∈ c.τ, σ v = false)
    (hj : Set.InjOn Configuration.j (R : Set (Configuration V)))
    (hτ : Set.InjOn Configuration.τ (R : Set (Configuration V)))
    {ρ : ℝ} (hρ : 0 < ρ) (hRcard : ρ ≤ (R.card : ℝ)) :
    expect θ (fun ω : V → Bool =>
        if ∃ c ∈ R, ω c.j = true ∧ ∃ v ∈ c.τ, ω v = true then (0 : ℝ) else 1)
      ≤ 8 / min (Real.sqrt (ρ / 2) / 2) (θ * ρ / 4)
        + Real.exp (-(θ * min (Real.sqrt (ρ / 2) / 2) (θ * ρ / 4) / 2)) := by
  classical
  set μ₀ := min (Real.sqrt (ρ / 2) / 2) (θ * ρ / 4) with hμ₀def
  have hμ₀pos : 0 < μ₀ := by
    apply lt_min
    · exact div_pos (Real.sqrt_pos.mpr (by linarith)) two_pos
    · exact div_pos (mul_pos hθ0 hρ) (by norm_num)
  set Z : (V → Bool) → ℝ := fun ω => ((coveredSet R σ ω).card : ℝ) with hZdef
  set μ := expect θ Z with hμdef
  
  have hZsum : ∀ ω : V → Bool, Z ω = ∑ v ∈ offSide σ,
      (if ∃ u ∈ covSet R v, ω u = true then (1 : ℝ) else 0) := by
    intro ω
    simp only [hZdef]
    unfold coveredSet
    rw [Finset.card_filter]
    push_cast
    rfl
  have hμeq : μ = ∑ v ∈ offSide σ, (1 - (1 - θ) ^ (covSet R v).card) := by
    rw [hμdef]
    rw [show Z = (fun ω : V → Bool => ∑ v ∈ offSide σ,
      (if ∃ u ∈ covSet R v, ω u = true then (1 : ℝ) else 0)) from funext hZsum]
    rw [expect_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    have hpt : ∀ ω : V → Bool, (if ∃ u ∈ covSet R v, ω u = true then (1 : ℝ) else 0)
        = 1 - (if (∀ i ∈ (∅ : Finset V), ω i = true) ∧ (∀ i ∈ covSet R v, ω i = false)
            then (1 : ℝ) else 0) := by
      intro ω
      by_cases h : ∃ u ∈ covSet R v, ω u = true
      · have hncyl : ¬ ((∀ i ∈ (∅ : Finset V), ω i = true)
            ∧ (∀ i ∈ covSet R v, ω i = false)) := by
          rintro ⟨-, hall⟩
          obtain ⟨u, hu, huu⟩ := h
          rw [hall u hu] at huu
          exact Bool.noConfusion huu
        rw [if_pos h, if_neg hncyl]
        norm_num
      · rw [if_neg h]
        push Not at h
        have hcyl : (∀ i ∈ (∅ : Finset V), ω i = true)
            ∧ (∀ i ∈ covSet R v, ω i = false) := by
          refine ⟨by simp, fun i hi => ?_⟩
          simpa using h i hi
        rw [if_pos hcyl]
        norm_num
    rw [show (fun ω : V → Bool => if ∃ u ∈ covSet R v, ω u = true then (1 : ℝ) else 0)
      = (fun ω : V → Bool => 1 - (if (∀ i ∈ (∅ : Finset V), ω i = true)
          ∧ (∀ i ∈ covSet R v, ω i = false) then (1 : ℝ) else 0)) from funext hpt]
    rw [expect_sub, expect_const,
      expect_cylinder θ ∅ (covSet R v) (Finset.disjoint_empty_left _)]
    simp
  
  have hterm_nonneg : ∀ d : ℕ, (0 : ℝ) ≤ 1 - (1 - θ) ^ d := by
    intro d
    have h1 : (1 - θ) ^ d ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
    linarith
  set H := (offSide σ).filter (fun v => 1 ≤ θ * ((covSet R v).card : ℝ)) with hHdef
  set Hc := (offSide σ).filter (fun v => ¬ 1 ≤ θ * ((covSet R v).card : ℝ)) with hHcdef
  have hμsplit : μ = (∑ v ∈ H, (1 - (1 - θ) ^ (covSet R v).card))
      + ∑ v ∈ Hc, (1 - (1 - θ) ^ (covSet R v).card) := by
    rw [hμeq, hHdef, hHcdef]
    exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hμ0 : μ₀ ≤ μ := by
    by_cases hcase : ρ / 2 ≤ ((H.card : ℝ)) ^ 2
    · 
      have h1 : (H.card : ℝ) / 2 ≤ ∑ v ∈ H, (1 - (1 - θ) ^ (covSet R v).card) := by
        have h2 : ∀ v ∈ H, (1 / 2 : ℝ) ≤ 1 - (1 - θ) ^ (covSet R v).card := by
          intro v hv
          rw [hHdef] at hv
          exact half_le_one_sub_pow hθ0.le hθ1 (Finset.mem_filter.mp hv).2
        have h3 := Finset.sum_le_sum h2
        rw [Finset.sum_const, nsmul_eq_mul] at h3
        linarith
      have hsqrt : Real.sqrt (ρ / 2) ≤ (H.card : ℝ) := by
        have h2 : Real.sqrt (ρ / 2) ≤ Real.sqrt (((H.card : ℝ)) ^ 2) :=
          Real.sqrt_le_sqrt hcase
        rwa [Real.sqrt_sq (by positivity)] at h2
      have hrest : 0 ≤ ∑ v ∈ Hc, (1 - (1 - θ) ^ (covSet R v).card) :=
        Finset.sum_nonneg fun v _ => hterm_nonneg _
      calc μ₀ ≤ Real.sqrt (ρ / 2) / 2 := min_le_left _ _
        _ ≤ (H.card : ℝ) / 2 := by linarith
        _ ≤ ∑ v ∈ H, (1 - (1 - θ) ^ (covSet R v).card) := h1
        _ ≤ μ := by rw [hμsplit]; linarith
    · 
      push Not at hcase
      have hcapped : ((R.filter (fun c => ∀ v ∈ c.τ, v ∈ H)).card : ℝ)
          ≤ ((H.card : ℝ)) ^ 2 := by
        have h1 : (R.filter (fun c => ∀ v ∈ c.τ, v ∈ H)).card
            ≤ ((H ×ˢ H).image (fun p : V × V => s(p.1, p.2))).card := by
          apply Finset.card_le_card_of_injOn Configuration.τ
          · intro c hc
            exact sym2_mem_image_product H c.τ (Finset.mem_filter.mp hc).2
          · exact hτ.mono (Finset.coe_subset.mpr (Finset.filter_subset _ _))
        have h2 : ((H ×ˢ H).image (fun p : V × V => s(p.1, p.2))).card ≤ (H ×ˢ H).card :=
          Finset.card_image_le
        have h3 : (H ×ˢ H).card = H.card * H.card := Finset.card_product _ _
        have h4 : (R.filter (fun c => ∀ v ∈ c.τ, v ∈ H)).card ≤ H.card * H.card := by
          omega
        calc ((R.filter (fun c => ∀ v ∈ c.τ, v ∈ H)).card : ℝ)
            ≤ (H.card : ℝ) * H.card := by exact_mod_cast h4
          _ = ((H.card : ℝ)) ^ 2 := by ring
      have hcard_cov : ∀ v : V, (covSet R v).card = (R.filter (fun c => v ∈ c.τ)).card :=
        fun v => Finset.card_image_of_injOn
          (hj.mono (Finset.coe_subset.mpr (Finset.filter_subset _ _)))
      have hdouble : ((R.filter (fun c => ¬ ∀ v ∈ c.τ, v ∈ H)).card : ℕ)
          ≤ ∑ v ∈ Hc, (covSet R v).card := by
        calc (R.filter (fun c => ¬ ∀ v ∈ c.τ, v ∈ H)).card
            = ∑ c ∈ R, if ¬ ∀ v ∈ c.τ, v ∈ H then 1 else 0 := Finset.card_filter _ _
          _ ≤ ∑ c ∈ R, (Hc.filter (fun v => v ∈ c.τ)).card := by
              apply Finset.sum_le_sum
              intro c hcR
              by_cases hcap : ∀ v ∈ c.τ, v ∈ H
              · have hnone : ¬ ∃ v ∈ c.τ, v ∉ H := by
                  rintro ⟨v, hvτ, hvH⟩
                  exact hvH (hcap v hvτ)
                simp [hnone]
              · have hncap : ¬ ∀ v ∈ c.τ, v ∈ H := hcap
                push Not at hcap
                obtain ⟨v, hvτ, hvH⟩ := hcap
                rw [if_pos hncap]
                refine Finset.card_pos.mpr ⟨v, Finset.mem_filter.mpr ⟨?_, hvτ⟩⟩
                have hoff : σ v = false := (hret c hcR).2 v hvτ
                rw [hHcdef, Finset.mem_filter, mem_offSide]
                refine ⟨hoff, fun hpred => hvH ?_⟩
                rw [hHdef, Finset.mem_filter, mem_offSide]
                exact ⟨hoff, hpred⟩
          _ = ∑ v ∈ Hc, (R.filter (fun c => v ∈ c.τ)).card := by
              simp only [Finset.card_filter]
              exact Finset.sum_comm
          _ = ∑ v ∈ Hc, (covSet R v).card := by
              exact Finset.sum_congr rfl fun v _ => (hcard_cov v).symm
      have hfil : (R.filter (fun c => ∀ v ∈ c.τ, v ∈ H)).card
          + (R.filter (fun c => ¬ ∀ v ∈ c.τ, v ∈ H)).card = R.card :=
        Finset.card_filter_add_card_filter_not _
      have hsum_ge : ρ / 2 ≤ ∑ v ∈ Hc, ((covSet R v).card : ℝ) := by
        have h2 : ((R.filter (fun c => ¬ ∀ v ∈ c.τ, v ∈ H)).card : ℝ)
            ≤ ∑ v ∈ Hc, ((covSet R v).card : ℝ) := by
          have := hdouble
          exact_mod_cast this
        have h3 : ((R.filter (fun c => ∀ v ∈ c.τ, v ∈ H)).card : ℝ)
            + ((R.filter (fun c => ¬ ∀ v ∈ c.τ, v ∈ H)).card : ℝ) = (R.card : ℝ) := by
          exact_mod_cast hfil
        linarith
      have hHc_term : ∀ v ∈ Hc, θ * ((covSet R v).card : ℝ) / 2
          ≤ 1 - (1 - θ) ^ (covSet R v).card := by
        intro v hv
        have hnp := (Finset.mem_filter.mp (hHcdef ▸ hv)).2
        push Not at hnp
        exact lin_le_one_sub_pow hθ0.le hθ1 hnp.le
      have hB : θ * ρ / 4 ≤ μ := by
        have h1 := Finset.sum_le_sum hHc_term
        have h2 : ∑ v ∈ Hc, θ * ((covSet R v).card : ℝ) / 2
            = θ / 2 * ∑ v ∈ Hc, ((covSet R v).card : ℝ) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun v _ => by ring
        have h3 : θ / 2 * (ρ / 2) ≤ θ / 2 * ∑ v ∈ Hc, ((covSet R v).card : ℝ) :=
          mul_le_mul_of_nonneg_left hsum_ge (by positivity)
        have h4 : 0 ≤ ∑ v ∈ H, (1 - (1 - θ) ^ (covSet R v).card) :=
          Finset.sum_nonneg fun v _ => hterm_nonneg _
        rw [hμsplit]
        nlinarith
      exact le_trans (min_le_right _ _) hB
  have hμpos : 0 < μ := lt_of_lt_of_le hμ₀pos hμ0
  
  have hvar : var θ Z ≤ 2 * μ := by
    refine le_trans (efron_stein θ hθ0.le hθ1 Z) ?_
    have hpt : ∀ ω : V → Bool,
        (∑ u : V, (Z ω - Z (Function.update ω u false)) ^ 2) ≤ 2 * Z ω := by
      intro ω
      have hcast : ∀ u : V, Z ω - Z (Function.update ω u false)
          = ((loseSet R σ ω u).card : ℝ) := by
        intro u
        simp only [hZdef]
        rw [card_loseSet R σ ω u,
          Nat.cast_sub (Finset.card_le_card (coveredSet_update_subset R σ ω u))]
      calc ∑ u : V, (Z ω - Z (Function.update ω u false)) ^ 2
          = ∑ u : V, ((loseSet R σ ω u).card : ℝ) ^ 2 :=
            Finset.sum_congr rfl fun u _ => by rw [hcast u]
        _ ≤ ∑ u : V, 2 * ((loseSet R σ ω u).card : ℝ) := by
            apply Finset.sum_le_sum
            intro u _
            have h2 : ((loseSet R σ ω u).card : ℝ) ≤ 2 := by
              exact_mod_cast card_loseSet_le_two hj σ ω u
            have h0 : (0 : ℝ) ≤ ((loseSet R σ ω u).card : ℝ) := by positivity
            nlinarith
        _ = 2 * ∑ u : V, ((loseSet R σ ω u).card : ℝ) := by rw [Finset.mul_sum]
        _ ≤ 2 * Z ω := by
            have hc : (∑ u : V, ((loseSet R σ ω u).card : ℝ))
                ≤ ((coveredSet R σ ω).card : ℝ) := by
              exact_mod_cast sum_card_loseSet_le R σ ω
            simp only [hZdef]
            linarith
    calc expect θ (fun ω => ∑ u : V, (Z ω - Z (Function.update ω u false)) ^ 2)
        ≤ expect θ (fun ω => 2 * Z ω) := expect_mono hθ0.le hθ1 hpt
      _ = 2 * μ := by rw [expect_const_mul, ← hμdef]
  
  have hcheb : expect θ (fun ω => if Z ω < μ / 2 then (1 : ℝ) else 0) ≤ 8 / μ₀ := by
    have hμne : μ ≠ 0 := ne_of_gt hμpos
    have hpt : ∀ ω : V → Bool, (if Z ω < μ / 2 then (1 : ℝ) else 0)
        ≤ 4 / μ ^ 2 * (Z ω - μ) ^ 2 := by
      intro ω
      by_cases h : Z ω < μ / 2
      · rw [if_pos h]
        have h1 : μ / 2 ≤ μ - Z ω := by
          have h0 : (0 : ℝ) ≤ Z ω := by simp only [hZdef]; positivity
          linarith
        have h2 : (μ / 2) ^ 2 ≤ (Z ω - μ) ^ 2 := by
          rw [show (Z ω - μ) ^ 2 = (μ - Z ω) ^ 2 by ring]
          exact pow_le_pow_left₀ (by positivity) h1 2
        have h3 : 4 / μ ^ 2 * (μ / 2) ^ 2 = 1 := by
          field_simp
          ring
        calc (1 : ℝ) = 4 / μ ^ 2 * (μ / 2) ^ 2 := h3.symm
          _ ≤ 4 / μ ^ 2 * (Z ω - μ) ^ 2 :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
      · rw [if_neg h]
        positivity
    calc expect θ (fun ω => if Z ω < μ / 2 then (1 : ℝ) else 0)
        ≤ expect θ (fun ω => 4 / μ ^ 2 * (Z ω - μ) ^ 2) := expect_mono hθ0.le hθ1 hpt
      _ = 4 / μ ^ 2 * var θ Z := by
          rw [expect_const_mul, hμdef]
          rfl
      _ ≤ 4 / μ ^ 2 * (2 * μ) := mul_le_mul_of_nonneg_left hvar (by positivity)
      _ = 8 / μ := by
          field_simp
          ring
      _ ≤ 8 / μ₀ := div_le_div_of_nonneg_left (by norm_num) hμ₀pos hμ0
  
  have hσall : ∀ {v u : V}, u ∈ covSet R v → σ u = true := by
    intro v u hu
    obtain ⟨c, hcR, _, hcj⟩ := mem_covSet.mp hu
    rw [← hcj]
    exact (hret c hcR).1
  have hcond : expect θ (fun ω : V → Bool =>
      if (∀ v ∈ coveredSet R σ ω, ω v = false) ∧ μ / 2 ≤ Z ω then (1 : ℝ) else 0)
      ≤ Real.exp (-(θ * μ₀ / 2)) := by
    rw [expect_split θ (fun v => σ v = true)]
    have houter : ∀ a : {i : V // σ i = true} → Bool,
        expect θ (fun b : {i : V // ¬ σ i = true} → Bool =>
          if (∀ v ∈ coveredSet R σ (merge (fun v => σ v = true) a b),
              (merge (fun v => σ v = true) a b) v = false)
            ∧ μ / 2 ≤ Z (merge (fun v => σ v = true) a b) then (1 : ℝ) else 0)
        ≤ Real.exp (-(θ * μ / 2)) := by
      intro a
      set ω₀ : V → Bool := merge (fun v => σ v = true) a (fun _ => false) with hω₀
      set Wa := coveredSet R σ ω₀ with hWa
      have hkey : ∀ (b : {i : V // ¬ σ i = true} → Bool) (u : V) (hu : σ u = true),
          merge (fun v => σ v = true) a b u = ω₀ u := by
        intro b u hu
        rw [hω₀]
        unfold merge
        rw [dif_pos hu, dif_pos hu]
      have hkey2 : ∀ (b : {i : V // ¬ σ i = true} → Bool) (i : {i : V // ¬ σ i = true}),
          merge (fun v => σ v = true) a b ↑i = b i := by
        intro b i
        unfold merge
        rw [dif_neg i.2]
      have hWeq : ∀ b : {i : V // ¬ σ i = true} → Bool,
          coveredSet R σ (merge (fun v => σ v = true) a b) = Wa := by
        intro b
        rw [hWa]
        unfold coveredSet
        apply Finset.filter_congr
        intro v _
        constructor
        · rintro ⟨u, hu, huu⟩
          refine ⟨u, hu, ?_⟩
          rw [← hkey b u (hσall hu)]
          exact huu
        · rintro ⟨u, hu, huu⟩
          refine ⟨u, hu, ?_⟩
          rw [hkey b u (hσall hu)]
          exact huu
      have hZeq : ∀ b : {i : V // ¬ σ i = true} → Bool,
          Z (merge (fun v => σ v = true) a b) = (Wa.card : ℝ) := by
        intro b
        simp only [hZdef]
        rw [hWeq b]
      have hWnp : ∀ v ∈ Wa, ¬ σ v = true := by
        intro v hv
        have h1 := (mem_coveredSet.mp (hWa ▸ hv)).1
        simp [h1]
      by_cases hbig : μ / 2 ≤ (Wa.card : ℝ)
      · have hfun : (fun b : {i : V // ¬ σ i = true} → Bool =>
            if (∀ v ∈ coveredSet R σ (merge (fun v => σ v = true) a b),
                (merge (fun v => σ v = true) a b) v = false)
              ∧ μ / 2 ≤ Z (merge (fun v => σ v = true) a b) then (1 : ℝ) else 0)
            = fun b => if (∀ i ∈ (∅ : Finset {i : V // ¬ σ i = true}), b i = true)
              ∧ (∀ i ∈ Wa.subtype (fun v => ¬ σ v = true), b i = false)
              then (1 : ℝ) else 0 := by
          funext b
          apply if_congr _ rfl rfl
          rw [hWeq b, hZeq b]
          constructor
          · rintro ⟨hall, -⟩
            refine ⟨by simp, fun i hi => ?_⟩
            rw [← hkey2 b i]
            exact hall _ (Finset.mem_subtype.mp hi)
          · rintro ⟨-, hall⟩
            refine ⟨fun v hv => ?_, hbig⟩
            exact (hkey2 b ⟨v, hWnp v hv⟩).trans
              (hall ⟨v, hWnp v hv⟩ (Finset.mem_subtype.mpr hv))
        rw [hfun, expect_cylinder θ ∅ (Wa.subtype (fun v => ¬ σ v = true))
          (Finset.disjoint_empty_left _)]
        have hcards : (Wa.subtype (fun v => ¬ σ v = true)).card = Wa.card := by
          rw [Finset.card_subtype, Finset.filter_true_of_mem hWnp]
        rw [hcards]
        simp only [Finset.card_empty, pow_zero, one_mul]
        calc (1 - θ) ^ Wa.card ≤ Real.exp (-(θ * Wa.card)) :=
            one_sub_pow_le_exp hθ0.le hθ1 _
          _ ≤ Real.exp (-(θ * μ / 2)) := by
              rw [Real.exp_le_exp]
              have h5 : θ * (μ / 2) ≤ θ * (Wa.card : ℝ) :=
                mul_le_mul_of_nonneg_left hbig hθ0.le
              linarith
      · have hfun : (fun b : {i : V // ¬ σ i = true} → Bool =>
            if (∀ v ∈ coveredSet R σ (merge (fun v => σ v = true) a b),
                (merge (fun v => σ v = true) a b) v = false)
              ∧ μ / 2 ≤ Z (merge (fun v => σ v = true) a b) then (1 : ℝ) else 0)
            = fun _ => (0 : ℝ) := by
          funext b
          rw [if_neg]
          rintro ⟨-, hZb⟩
          rw [hZeq b] at hZb
          exact hbig hZb
        rw [hfun, expect_const]
        positivity
    calc expect θ (fun a : {i : V // σ i = true} → Bool =>
          expect θ (fun b : {i : V // ¬ σ i = true} → Bool =>
            (fun ω : V → Bool => if (∀ v ∈ coveredSet R σ ω, ω v = false)
              ∧ μ / 2 ≤ Z ω then (1 : ℝ) else 0) (merge (fun v => σ v = true) a b)))
        ≤ expect θ (fun _ : {i : V // σ i = true} → Bool => Real.exp (-(θ * μ / 2))) :=
          expect_mono hθ0.le hθ1 houter
      _ = Real.exp (-(θ * μ / 2)) := expect_const _ _
      _ ≤ Real.exp (-(θ * μ₀ / 2)) := by
          rw [Real.exp_le_exp]
          have h5 := mul_le_mul_of_nonneg_left hμ0 hθ0.le
          linarith
  
  have hsplit : ∀ ω : V → Bool,
      (if ∃ c ∈ R, ω c.j = true ∧ ∃ v ∈ c.τ, ω v = true then (0 : ℝ) else 1)
      ≤ (if Z ω < μ / 2 then (1 : ℝ) else 0)
        + (if (∀ v ∈ coveredSet R σ ω, ω v = false) ∧ μ / 2 ≤ Z ω
            then (1 : ℝ) else 0) := by
    intro ω
    by_cases hmiss : ∃ c ∈ R, ω c.j = true ∧ ∃ v ∈ c.τ, ω v = true
    · rw [if_pos hmiss]
      have h1 : (0 : ℝ) ≤ (if Z ω < μ / 2 then (1 : ℝ) else 0) := by positivity
      have h2 : (0 : ℝ) ≤ (if (∀ v ∈ coveredSet R σ ω, ω v = false) ∧ μ / 2 ≤ Z ω
          then (1 : ℝ) else 0) := by positivity
      linarith
    · rw [if_neg hmiss]
      have hallOff : ∀ v ∈ coveredSet R σ ω, ω v = false := by
        intro v hv
        obtain ⟨hoff, u, hu, huu⟩ := mem_coveredSet.mp hv
        obtain ⟨c, hcR, hvτ, hcj⟩ := mem_covSet.mp hu
        by_contra hvt
        simp only [Bool.not_eq_false] at hvt
        exact hmiss ⟨c, hcR, by rw [hcj]; exact huu, v, hvτ, hvt⟩
      by_cases hZb : Z ω < μ / 2
      · rw [if_pos hZb, if_neg (fun hcontra => (not_le.mpr hZb) hcontra.2)]
        norm_num
      · rw [if_neg hZb, if_pos ⟨hallOff, not_lt.mp hZb⟩]
        norm_num
  calc expect θ (fun ω : V → Bool =>
        if ∃ c ∈ R, ω c.j = true ∧ ∃ v ∈ c.τ, ω v = true then (0 : ℝ) else 1)
      ≤ expect θ (fun ω : V → Bool => (if Z ω < μ / 2 then (1 : ℝ) else 0)
          + (if (∀ v ∈ coveredSet R σ ω, ω v = false) ∧ μ / 2 ≤ Z ω
              then (1 : ℝ) else 0)) := expect_mono hθ0.le hθ1 hsplit
    _ = expect θ (fun ω => if Z ω < μ / 2 then (1 : ℝ) else 0)
        + expect θ (fun ω : V → Bool =>
            if (∀ v ∈ coveredSet R σ ω, ω v = false) ∧ μ / 2 ≤ Z ω
              then (1 : ℝ) else 0) := expect_add _ _ _
    _ ≤ 8 / μ₀ + Real.exp (-(θ * μ₀ / 2)) := add_le_add hcheb hcond

end MissBound


theorem common_cut (α : ℝ) (hα : 0 < α) :
    ∃ (D : ℝ) (m₀ : ℕ), 0 < D ∧
      ∀ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (q : ℕ)
        (𝓕 : Fin q → Finset (Configuration V)),
        m₀ ≤ Fintype.card V →
        q ≤ Fintype.card V →
        (∀ k, α * Fintype.card V ≤ ((𝓕 k).card : ℝ)) →
        (∀ k, Set.InjOn Configuration.j (𝓕 k : Set (Configuration V))) →
        (∀ k, Set.InjOn Configuration.τ (𝓕 k : Set (Configuration V))) →
        ∃ T : Finset V, (T.card : ℝ) ≤ D * Real.sqrt (Fintype.card V) ∧
          ∃ Bad : Finset (Fin q), 8 * Bad.card ≤ Fintype.card V ∧
            ∀ k, k ∉ Bad → ∃ c ∈ 𝓕 k, Hits T c := by
  classical
  let C : ℝ := 256 * (1 / α + 1 / Real.sqrt α)
  have hsα : 0 < Real.sqrt α := Real.sqrt_pos.2 hα
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  let c₀ : ℝ := min (Real.sqrt α / 8) (C * α / 32)
  have hc₀ : 0 < c₀ := by
    dsimp only [c₀]
    exact lt_min (by positivity) (by positivity)
  let R₀ : ℝ := max (C + 1) (1024 / c₀)
  have hR₀ : 0 < R₀ := lt_of_lt_of_le (by positivity : 0 < C + 1) (le_max_left _ _)
  obtain ⟨m₀, hm₀⟩ : ∃ m₀ : ℕ, R₀ ^ 2 ≤ m₀ := exists_nat_ge (R₀ ^ 2)
  refine ⟨4 * C, m₀, by positivity, ?_⟩
  intro V _ _ q families hm hq hcard hj hτ
  let m : ℕ := Fintype.card V
  have hmR : R₀ ^ 2 ≤ (m : ℝ) := by
    exact le_trans hm₀ (by exact_mod_cast hm)
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := by positivity
  have hRroot : R₀ ≤ Real.sqrt m := by
    have h := Real.sqrt_le_sqrt hmR
    rwa [Real.sqrt_sq hR₀.le] at h
  have hsqrtm : 0 < Real.sqrt m := lt_of_lt_of_le hR₀ hRroot
  have hmpos : 0 < m := by
    by_contra hz
    have : m = 0 := Nat.eq_zero_of_not_pos hz
    rw [this] at hsqrtm
    norm_num at hsqrtm
  let θ : ℝ := C / Real.sqrt m
  have hθ0 : 0 < θ := div_pos hC hsqrtm
  have hθ1 : θ < 1 := by
    have hCR : C + 1 ≤ R₀ := le_max_left _ _
    have hCsqrt : C < Real.sqrt m := lt_of_lt_of_le (by linarith) hRroot
    exact (div_lt_one hsqrtm).2 hCsqrt
  have hm_sqrt : (m : ℝ) / Real.sqrt m = Real.sqrt m := by
    apply (div_eq_iff (ne_of_gt hsqrtm)).2
    rw [Real.mul_self_sqrt hm0]
  have hCsa : (256 : ℝ) ≤ C * Real.sqrt α := by
    have hpart : 256 * (1 / Real.sqrt α) ≤ C := by
      dsimp only [C]
      have ha0 : 0 ≤ 1 / α := by positivity
      nlinarith
    have h := mul_le_mul_of_nonneg_right hpart hsα.le
    calc (256 : ℝ) = 256 * ((1 / Real.sqrt α) * Real.sqrt α) := by
          rw [one_div_mul_cancel (ne_of_gt hsα), mul_one]
      _ = (256 * (1 / Real.sqrt α)) * Real.sqrt α := by ring
      _ ≤ C * Real.sqrt α := h
  choose σ hσ using fun k => exists_large_retained (families k)
  let R : Fin q → Finset (Configuration V) := fun k => retained (families k) (σ k)
  have hRcard : ∀ k, α * m / 8 ≤ ((R k).card : ℝ) := by
    intro k
    have hk := hσ k
    have hk' : ((families k).card : ℝ) ≤ 8 * ((R k).card : ℝ) := by
      dsimp only [R]
      exact_mod_cast hk
    have hc := hcard k
    dsimp only [m]
    linarith
  have hRret : ∀ k, ∀ c ∈ R k,
      σ k c.j = true ∧ ∀ v ∈ c.τ, σ k v = false := by
    intro k c hc
    exact (mem_retained.mp hc).2
  have hRj : ∀ k, Set.InjOn Configuration.j (R k : Set (Configuration V)) := by
    intro k
    exact (hj k).mono (Finset.coe_subset.mpr (Finset.filter_subset _ _))
  have hRτ : ∀ k, Set.InjOn Configuration.τ (R k : Set (Configuration V)) := by
    intro k
    exact (hτ k).mono (Finset.coe_subset.mpr (Finset.filter_subset _ _))
  have hmu : (1024 : ℝ) ≤
      min (Real.sqrt ((α * m / 8) / 2) / 2) (θ * (α * m / 8) / 4) := by
    have hA : c₀ * Real.sqrt m ≤ Real.sqrt ((α * m / 8) / 2) / 2 := by
      have hcA : c₀ ≤ Real.sqrt α / 8 := min_le_left _ _
      have hsqrtprod : Real.sqrt ((α * (m : ℝ) / 8) / 2) / 2 =
          (Real.sqrt α / 8) * Real.sqrt m := by
        rw [show (α * (m : ℝ) / 8) / 2 = α * ((m : ℝ) / 16) by ring,
          Real.sqrt_mul hα.le, Real.sqrt_div (by positivity : (0 : ℝ) ≤ m)]
        norm_num
        ring
      rw [hsqrtprod]
      exact mul_le_mul_of_nonneg_right hcA (Real.sqrt_nonneg _)
    have hB : c₀ * Real.sqrt m ≤ θ * (α * m / 8) / 4 := by
      have hcB : c₀ ≤ C * α / 32 := min_le_right _ _
      have hform : θ * (α * (m : ℝ) / 8) / 4 =
          (C * α / 32) * Real.sqrt m := by
        dsimp only [θ]
        field_simp
        nlinarith [Real.sq_sqrt hm0]
      rw [hform]
      exact mul_le_mul_of_nonneg_right hcB (Real.sqrt_nonneg _)
    have hbase : (1024 : ℝ) ≤ c₀ * Real.sqrt m := by
      have hquot : 1024 / c₀ ≤ R₀ := le_max_right _ _
      have h := le_trans hquot hRroot
      simpa [mul_comm] using (div_le_iff₀ hc₀).mp h
    exact le_min (le_trans hbase hA) (le_trans hbase hB)
  let μ₀ : ℝ := min (Real.sqrt ((α * m / 8) / 2) / 2) (θ * (α * m / 8) / 4)
  have hμ₀ : (1024 : ℝ) ≤ μ₀ := hmu
  have hμ₀pos : 0 < μ₀ := lt_of_lt_of_le (by norm_num) hμ₀
  have hAform : θ * (Real.sqrt ((α * m / 8) / 2) / 2) / 2 =
      C * Real.sqrt α / 16 := by
    have hsqrtprod : Real.sqrt ((α * (m : ℝ) / 8) / 2) / 2 =
        (Real.sqrt α / 8) * Real.sqrt m := by
      rw [show (α * (m : ℝ) / 8) / 2 = α * ((m : ℝ) / 16) by ring,
        Real.sqrt_mul hα.le, Real.sqrt_div (by positivity : (0 : ℝ) ≤ m)]
      norm_num
      ring
    rw [hsqrtprod]
    dsimp only [θ]
    field_simp
    ring
  have hBform : θ * (θ * (α * m / 8) / 4) / 2 = C ^ 2 * α / 64 := by
    dsimp only [θ]
    field_simp
    nlinarith [Real.sq_sqrt hm0]
  have hAe : (8 : ℝ) ≤ θ * (Real.sqrt ((α * m / 8) / 2) / 2) / 2 := by
    rw [hAform]
    linarith
  have hBe : (8 : ℝ) ≤ θ * (θ * (α * m / 8) / 4) / 2 := by
    rw [hBform]
    have hsquare : (256 : ℝ) ^ 2 ≤ (C * Real.sqrt α) ^ 2 :=
      pow_le_pow_left₀ (by norm_num) hCsa 2
    rw [mul_pow, Real.sq_sqrt hα.le] at hsquare
    nlinarith
  have harg : (8 : ℝ) ≤ θ * μ₀ / 2 := by
    dsimp only [μ₀]
    by_cases hab : Real.sqrt ((α * m / 8) / 2) / 2 ≤ θ * (α * m / 8) / 4
    · rw [min_eq_left hab]
      exact hAe
    · rw [min_eq_right (le_of_not_ge hab)]
      exact hBe
  have hsmall : 8 / μ₀ + Real.exp (- (θ * μ₀ / 2)) ≤ (1 / 64 : ℝ) := by
    have hfirst : 8 / μ₀ ≤ (1 / 128 : ℝ) := by
      rw [div_le_iff₀ hμ₀pos]
      nlinarith
    have hsecond : Real.exp (- (θ * μ₀ / 2)) ≤ (1 / 256 : ℝ) := by
      calc Real.exp (- (θ * μ₀ / 2)) ≤ Real.exp (-8) := by
              rw [Real.exp_le_exp]
              linarith
        _ ≤ (1 / 256 : ℝ) := exp_neg_eight_le
    linarith
  let Tset : (V → Bool) → Finset V := fun w => Finset.univ.filter (fun v => w v = true)
  have hHits : ∀ (w : V → Bool) (c : Configuration V),
      Hits (Tset w) c ↔ w c.j = true ∧ ∃ v ∈ c.τ, w v = true := by
    intro w c
    simp only [Hits, Tset, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hjw, v, hvw, hvτ⟩
      exact ⟨hjw, v, hvτ, hvw⟩
    · rintro ⟨hjw, v, hvτ, hvw⟩
      exact ⟨hjw, v, hvw, hvτ⟩
  have hmissR : ∀ k, Bernoulli.expect θ (fun w : V → Bool =>
      if ∃ c ∈ R k, Hits (Tset w) c then (0 : ℝ) else 1) ≤ 1 / 64 := by
    intro k
    have hraw := miss_bound θ hθ0 hθ1.le (R k) (σ k) (hRret k) (hRj k) (hRτ k)
      (show 0 < α * m / 8 by positivity) (hRcard k)
    rw [show (fun w : V → Bool =>
        if ∃ c ∈ R k, Hits (Tset w) c then (0 : ℝ) else 1) =
      (fun w => if ∃ c ∈ R k, w c.j = true ∧ ∃ v ∈ c.τ, w v = true
        then (0 : ℝ) else 1) by
          funext w
          apply if_congr
          · simp only [hHits]
          · rfl
          · rfl]
    exact hraw.trans hsmall
  have hmissF : ∀ k, Bernoulli.expect θ (fun w : V → Bool =>
      if ∃ c ∈ families k, Hits (Tset w) c then (0 : ℝ) else 1) ≤ 1 / 64 := by
    intro k
    refine le_trans (Bernoulli.expect_mono hθ0.le hθ1.le ?_) (hmissR k)
    intro w
    by_cases hf : ∃ c ∈ families k, Hits (Tset w) c
    · rw [if_pos hf]
      positivity
    · have hr : ¬ ∃ c ∈ R k, Hits (Tset w) c := by
        rintro ⟨c, hcR, hhit⟩
        exact hf ⟨c, (mem_retained.mp hcR).1, hhit⟩
      simp [hf, hr]
  let Bad : (V → Bool) → Finset (Fin q) := fun w =>
    Finset.univ.filter (fun k => ¬ ∃ c ∈ families k, Hits (Tset w) c)
  have hBadcard : ∀ w : V → Bool, ((Bad w).card : ℝ) = ∑ k : Fin q,
      if ∃ c ∈ families k, Hits (Tset w) c then (0 : ℝ) else 1 := by
    intro w
    dsimp only [Bad]
    rw [Finset.card_filter]
    push_cast
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hhit : ∃ c ∈ families k, Hits (Tset w) c <;> simp [hhit]
  have hEBad : Bernoulli.expect θ (fun w : V → Bool => ((Bad w).card : ℝ)) ≤ m / 64 := by
    rw [show (fun w : V → Bool => ((Bad w).card : ℝ)) =
      (fun w => ∑ k : Fin q, if ∃ c ∈ families k, Hits (Tset w) c then (0 : ℝ) else 1) from
        funext hBadcard]
    rw [show (fun w : V → Bool => ∑ k : Fin q,
        if ∃ c ∈ families k, Hits (Tset w) c then (0 : ℝ) else 1) =
      (fun w => ∑ k ∈ (Finset.univ : Finset (Fin q)),
        (fun k w => if ∃ c ∈ families k, Hits (Tset w) c then (0 : ℝ) else 1) k w) by
          funext w; simp]
    rw [Bernoulli.expect_sum]
    calc ∑ k ∈ (Finset.univ : Finset (Fin q)), Bernoulli.expect θ
          (fun w : V → Bool => if ∃ c ∈ families k, Hits (Tset w) c then (0 : ℝ) else 1)
        ≤ ∑ k ∈ (Finset.univ : Finset (Fin q)), (1 / 64 : ℝ) :=
          Finset.sum_le_sum fun k _ => hmissF k
      _ = q / 64 := by simp [div_eq_mul_inv]
      _ ≤ m / 64 := by
        have hqm : (q : ℝ) ≤ m := by exact_mod_cast hq
        exact div_le_div_of_nonneg_right hqm (by norm_num)
  have hTcard : ∀ w : V → Bool, ((Tset w).card : ℝ) = ∑ v : V,
      if w v = true then (1 : ℝ) else 0 := by
    intro w
    dsimp only [Tset]
    rw [Finset.card_filter]
    push_cast
    rfl
  have hsingle : ∀ v : V, Bernoulli.expect θ (fun w : V → Bool =>
      if w v = true then (1 : ℝ) else 0) = θ := by
    intro v
    rw [show (fun w : V → Bool => if w v = true then (1 : ℝ) else 0) =
      (fun w => if (∀ i ∈ ({v} : Finset V), w i = true) ∧
        (∀ i ∈ (∅ : Finset V), w i = false) then (1 : ℝ) else 0) by
          funext w; simp]
    rw [Bernoulli.expect_cylinder θ {v} ∅ (Finset.disjoint_empty_right _)]
    simp
  have hET : Bernoulli.expect θ (fun w : V → Bool => ((Tset w).card : ℝ)) =
      θ * m := by
    rw [show (fun w : V → Bool => ((Tset w).card : ℝ)) =
      (fun w => ∑ v : V, if w v = true then (1 : ℝ) else 0) from funext hTcard]
    rw [show (fun w : V → Bool => ∑ v : V, if w v = true then (1 : ℝ) else 0) =
      (fun w => ∑ v ∈ (Finset.univ : Finset V),
        (fun v w => if w v = true then (1 : ℝ) else 0) v w) by funext w; simp]
    rw [Bernoulli.expect_sum]
    simp only [hsingle, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [mul_comm]
  let Obj : (V → Bool) → ℝ := fun w =>
    (1 / (4 * C * Real.sqrt m)) * ((Tset w).card : ℝ)
      + (8 / m) * ((Bad w).card : ℝ)
  have hEObj : Bernoulli.expect θ Obj ≤ 3 / 8 := by
    have hdenT : 0 < 4 * C * Real.sqrt m := by positivity
    have hdenm : (0 : ℝ) < m := by exact_mod_cast hmpos
    rw [show Obj = (fun w => (1 / (4 * C * Real.sqrt m)) * ((Tset w).card : ℝ)
      + (8 / m) * ((Bad w).card : ℝ)) from rfl]
    rw [Bernoulli.expect_add, Bernoulli.expect_const_mul, Bernoulli.expect_const_mul, hET]
    have hfirst : (1 / (4 * C * Real.sqrt m)) * (θ * m) = (1 / 4 : ℝ) := by
      have ht : θ * (m : ℝ) = C * Real.sqrt m := by
        dsimp only [θ]
        calc C / Real.sqrt m * (m : ℝ) = C * ((m : ℝ) / Real.sqrt m) := by ring
          _ = C * Real.sqrt m := by rw [hm_sqrt]
      rw [ht]
      field_simp
    rw [hfirst]
    have hsecond : (8 / (m : ℝ)) * Bernoulli.expect θ
        (fun w : V → Bool => ((Bad w).card : ℝ)) ≤ 1 / 8 := by
      calc (8 / (m : ℝ)) * Bernoulli.expect θ
            (fun w : V → Bool => ((Bad w).card : ℝ))
          ≤ (8 / (m : ℝ)) * ((m : ℝ) / 64) :=
            mul_le_mul_of_nonneg_left hEBad (by positivity)
        _ = (1 / 8 : ℝ) := by
          field_simp [ne_of_gt hdenm]
          norm_num
    linarith
  obtain ⟨w, hw⟩ := Bernoulli.exists_le_expect hθ0 hθ1 Obj
  have hw' : Obj w ≤ 3 / 8 := le_trans hw hEObj
  refine ⟨Tset w, ?_, Bad w, ?_, ?_⟩
  · have hbadnonneg : 0 ≤ (8 / (m : ℝ)) * ((Bad w).card : ℝ) := by positivity
    have hpart : (1 / (4 * C * Real.sqrt m)) * ((Tset w).card : ℝ) ≤ 3 / 8 := by
      dsimp only [Obj] at hw'
      linarith
    have hden : 0 < 4 * C * Real.sqrt m := by positivity
    rw [one_div_mul_eq_div, div_le_iff₀ hden] at hpart
    change ((Tset w).card : ℝ) ≤ 4 * C * Real.sqrt m
    linarith
  · have hTnonneg : 0 ≤ (1 / (4 * C * Real.sqrt m)) * ((Tset w).card : ℝ) := by
      positivity
    have hpart : (8 / (m : ℝ)) * ((Bad w).card : ℝ) ≤ 3 / 8 := by
      dsimp only [Obj] at hw'
      linarith
    have hmreal : (0 : ℝ) < m := by exact_mod_cast hmpos
    have hreal : (8 * (Bad w).card : ℕ) < m := by
      have : (8 * ((Bad w).card : ℝ)) < m := by
        rw [div_mul_eq_mul_div] at hpart
        have hle := (div_le_iff₀ hmreal).mp hpart
        have hlt : (3 / 8 : ℝ) * m < m := by
          exact mul_lt_of_lt_one_left hmreal (by norm_num)
        exact lt_of_le_of_lt hle hlt
      have hcast : (((8 * (Bad w).card : ℕ) : ℝ)) < (m : ℝ) := by
        norm_num only [Nat.cast_mul, Nat.cast_ofNat]
        exact this
      exact Nat.cast_lt.mp hcast
    exact Nat.le_of_lt hreal
  · intro k hk
    by_contra hno
    apply hk
    dsimp only [Bad]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ k, hno⟩

end NUS




namespace NUS

open SimpleGraph



private noncomputable def efst {α : Type*} (e : Sym2 α) : α := (Quot.out e).1

private noncomputable def esnd {α : Type*} (e : Sym2 α) : α := (Quot.out e).2

private lemma sym2_eq_mk {α : Type*} (e : Sym2 α) : e = s(efst e, esnd e) := by
  conv_lhs => rw [← Quot.out_eq e]
  rfl

private lemma efst_mem {α : Type*} (e : Sym2 α) : efst e ∈ e := Sym2.out_fst_mem e

private lemma esnd_mem {α : Type*} (e : Sym2 α) : esnd e ∈ e := Sym2.out_snd_mem e

private lemma mem_out_cases {α : Type*} {x : α} {e : Sym2 α} (h : x ∈ e) :
    x = efst e ∨ x = esnd e := by
  rw [sym2_eq_mk e, Sym2.mem_iff] at h
  exact h




private def pgraph {α : Type*} (p : α → Option α) : SimpleGraph α :=
  SimpleGraph.fromRel fun x y => p x = some y

private lemma pgraph_adj {α : Type*} (p : α → Option α) (x y : α) :
    (pgraph p).Adj x y ↔ x ≠ y ∧ (p x = some y ∨ p y = some x) :=
  SimpleGraph.fromRel_adj _ x y


private lemma reachable_invariant {α : Type*} {H : SimpleGraph α} {Q : α → Prop}
    (hQ : ∀ x y, H.Adj x y → Q x → Q y) :
    ∀ {x y : α}, H.Reachable x y → Q x → Q y := by
  have key : ∀ (x y : α), H.Walk x y → Q x → Q y := by
    intro x y W
    induction W with
    | nil => exact fun h => h
    | cons hadj tail ih => exact fun hq => ih (hQ _ _ hadj hq)
  intro x y h hx
  exact h.elim fun W => key x y W hx


private lemma pgraph_isAcyclic {α : Type*} (p : α → Option α) (rk : α → ℕ)
    (hp : ∀ x y, p x = some y → rk y < rk x) : (pgraph p).IsAcyclic := by
  classical
  intro v c hc
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image c.support.toFinset rk
    ⟨v, List.mem_toFinset.mpr c.start_mem_support⟩
  have hm' : m ∈ c.support := List.mem_toFinset.mp hm
  have hc' : (c.rotate m hm').IsCycle := hc.rotate hm'
  have hnil : ¬(c.rotate m hm').Nil := hc'.not_nil
  have h1 := (pgraph_adj p _ _).mp ((c.rotate m hm').adj_snd hnil)
  have h2 := (pgraph_adj p _ _).mp ((c.rotate m hm').adj_penultimate hnil)
  have hsnd : rk (c.rotate m hm').snd ≤ rk m := hmax _ (List.mem_toFinset.mpr
    ((Walk.mem_support_rotate_iff c m hm').mp ((c.rotate m hm').getVert_mem_support 1)))
  have hpen : rk (c.rotate m hm').penultimate ≤ rk m := hmax _ (List.mem_toFinset.mpr
    ((Walk.mem_support_rotate_iff c m hm').mp
      ((c.rotate m hm').getVert_mem_support ((c.rotate m hm').length - 1))))
  have e1 : p m = some (c.rotate m hm').snd := by
    rcases h1.2 with h | h
    · exact h
    · exact absurd (hp _ _ h) (by omega)
  have e2 : p m = some (c.rotate m hm').penultimate := by
    rcases h2.2 with h | h
    · exact absurd (hp _ _ h) (by omega)
    · exact h
  exact hc'.snd_ne_penultimate (Option.some.inj (e1.symm.trans e2))


theorem bounded_radius_contraction {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph (Option V)) [DecidableRel G.Adj] (f : ℕ)
    (hf : (Finset.univ.filter fun v : V => ∀ w, ¬G.Adj (some v) w).card ≤ f) :
    ∃ F : SimpleGraph (Option V), F ≤ G ∧ F.IsAcyclic ∧
      (∀ u v : Option V, F.Reachable u v → ¬F.Reachable u none → F.dist u v ≤ 3) ∧
      (∀ v : V, F.Reachable (some v) none → F.dist (some v) none ≤ 4) ∧
      2 * Nat.card {c : F.ConnectedComponent // (none : Option V) ∉ c.supp} ≤
        Fintype.card V + f ∧
      ∃ (parent : Option V → Option (Option V)) (rk : Option V → ℕ),
        (∀ x y, F.Adj x y ↔
          x ≠ y ∧ (parent x = some y ∨ parent y = some x)) ∧
        (∀ x y, parent x = some y → rk y < rk x) ∧
        (∀ v : V, rk (some v) ≤ 3) ∧
        2 * (Finset.univ.filter fun v : V => parent (some v) = none).card ≤
          Fintype.card V + f := by
  set II := Finset.univ.filter fun v : V => ∀ w, ¬G.Adj (some v) w with hIIdef
  classical
  
  have hexM : ∃ M : Finset (Sym2 V),
      (∀ e ∈ M, e ∈ (SimpleGraph.comap some G).edgeSet) ∧
      (∀ e ∈ M, ∀ e' ∈ M, e ≠ e' → ∀ x : V, x ∈ e → x ∉ e') ∧
      (∀ u w : V, G.Adj (some u) (some w) →
        (∃ e ∈ M, u ∈ e) ∨ (∃ e ∈ M, w ∈ e)) := by
    obtain ⟨M, hMmem, hMcard⟩ := Finset.exists_max_image
      ((Finset.univ : Finset (Finset (Sym2 V))).filter fun m =>
        (∀ e ∈ m, e ∈ (SimpleGraph.comap some G).edgeSet) ∧
        (∀ e ∈ m, ∀ e' ∈ m, e ≠ e' → ∀ x : V, x ∈ e → x ∉ e'))
      Finset.card ⟨∅, by simp⟩
    rw [Finset.mem_filter] at hMmem
    obtain ⟨-, hMedge, hMdisj⟩ := hMmem
    refine ⟨M, hMedge, hMdisj, ?_⟩
    intro u w huw
    by_contra hcon
    have hu : ∀ e ∈ M, u ∉ e := fun e he hue => hcon (Or.inl ⟨e, he, hue⟩)
    have hw : ∀ e ∈ M, w ∉ e := fun e he hwe => hcon (Or.inr ⟨e, he, hwe⟩)
    have hnew : s(u, w) ∉ M := fun hmem => hu _ hmem (Sym2.mem_mk_left u w)
    have hmem2 : insert s(u, w) M ∈
        ((Finset.univ : Finset (Finset (Sym2 V))).filter fun m =>
          (∀ e ∈ m, e ∈ (SimpleGraph.comap some G).edgeSet) ∧
          (∀ e ∈ m, ∀ e' ∈ m, e ≠ e' → ∀ x : V, x ∈ e → x ∉ e')) := by
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · intro e he
        rcases Finset.mem_insert.mp he with rfl | he'
        · exact huw
        · exact hMedge e he'
      · intro e he e' he' hee x hxe hxe'
        rcases Finset.mem_insert.mp he with rfl | he1
        · rcases Finset.mem_insert.mp he' with rfl | he2
          · exact hee rfl
          · rcases Sym2.mem_iff.mp hxe with rfl | rfl
            · exact hu e' he2 hxe'
            · exact hw e' he2 hxe'
        · rcases Finset.mem_insert.mp he' with rfl | he2
          · rcases Sym2.mem_iff.mp hxe' with rfl | rfl
            · exact hu e he1 hxe
            · exact hw e he1 hxe
          · exact hMdisj e he1 e' he2 hee x hxe hxe'
    have hcard := hMcard _ hmem2
    rw [Finset.card_insert_of_notMem hnew] at hcard
    omega
  obtain ⟨M, hMedge, hMdisj, hMmax⟩ := hexM
  
  have hMout : ∀ e ∈ M, G.Adj (some (efst e)) (some (esnd e)) := by
    intro e he
    have h := hMedge e he
    rw [sym2_eq_mk e] at h
    exact h
  have hMne : ∀ e ∈ M, efst e ≠ esnd e := by
    intro e he h
    exact (hMout e he).ne (congrArg some h)
  have huniq : ∀ e, e ∈ M → ∀ e', e' ∈ M → ∀ x : V, x ∈ e → x ∈ e' → e = e' := by
    intro e he e' he' x hx hx'
    by_contra hne
    exact hMdisj e he e' he' hne x hx hx'
  have hmatched_hasnbr : ∀ e, e ∈ M → ∀ x, x ∈ e → ∃ w : V, G.Adj (some x) (some w) := by
    intro e he x hx
    rcases mem_out_cases hx with rfl | rfl
    · exact ⟨esnd e, hMout e he⟩
    · exact ⟨efst e, (hMout e he).symm⟩
  
  have hex : ∀ x : Option V, ∃ (o : Option (Option V)) (r : ℕ) (hb : Option (Sym2 V)),
      (x = none ∧ o = none ∧ r = 0 ∧ hb = none) ∨
      (∃ v : V, x = some v ∧
        ((∃ e ∈ M, v ∈ e ∧ hb = some e ∧
            ((v = efst e ∧ o = none ∧ r = 1) ∨
             (v = esnd e ∧ o = some (some (efst e)) ∧ r = 2))) ∨
         ((∀ e ∈ M, v ∉ e) ∧ r = 3 ∧
            ((∃ w : V, (∃ e ∈ M, w ∈ e ∧ hb = some e) ∧ G.Adj (some v) (some w) ∧
                o = some (some w)) ∨
             ((∀ w : V, ¬G.Adj (some v) (some w)) ∧ G.Adj (some v) none ∧
                o = some none ∧ hb = none) ∨
             ((∀ w : V, ¬G.Adj (some v) (some w)) ∧ ¬G.Adj (some v) none ∧
                o = none ∧ hb = none))))) := by
    intro x
    rcases x with _ | v
    · exact ⟨none, 0, none, Or.inl ⟨rfl, rfl, rfl, rfl⟩⟩
    · by_cases hm : ∃ e ∈ M, v ∈ e
      · obtain ⟨e, he, hv⟩ := hm
        rcases mem_out_cases hv with h1 | h2
        · exact ⟨none, 1, some e, Or.inr ⟨v, rfl, Or.inl ⟨e, he, hv, rfl,
            Or.inl ⟨h1, rfl, rfl⟩⟩⟩⟩
        · exact ⟨some (some (efst e)), 2, some e, Or.inr ⟨v, rfl, Or.inl ⟨e, he, hv, rfl,
            Or.inr ⟨h2, rfl, rfl⟩⟩⟩⟩
      · have hm' : ∀ e ∈ M, v ∉ e := fun e he hv => hm ⟨e, he, hv⟩
        by_cases hl : ∃ w : V, G.Adj (some v) (some w)
        · obtain ⟨w, hw⟩ := hl
          have hwm : ∃ e ∈ M, w ∈ e := by
            rcases hMmax v w hw with h | h
            · exact absurd h hm
            · exact h
          obtain ⟨e, he, hwe⟩ := hwm
          exact ⟨some (some w), 3, some e, Or.inr ⟨v, rfl, Or.inr ⟨hm', rfl,
            Or.inl ⟨w, ⟨e, he, hwe, rfl⟩, hw, rfl⟩⟩⟩⟩
        · have hl' : ∀ w : V, ¬G.Adj (some v) (some w) := fun w hw => hl ⟨w, hw⟩
          by_cases hr : G.Adj (some v) none
          · exact ⟨some none, 3, none, Or.inr ⟨v, rfl, Or.inr ⟨hm', rfl,
              Or.inr (Or.inl ⟨hl', hr, rfl, rfl⟩)⟩⟩⟩
          · exact ⟨none, 3, none, Or.inr ⟨v, rfl, Or.inr ⟨hm', rfl,
              Or.inr (Or.inr ⟨hl', hr, rfl, rfl⟩)⟩⟩⟩
  choose par rk hub hspec using hex
  have hparnone : par none = none := by
    rcases hspec none with ⟨-, h, -, -⟩ | ⟨v, hv, -⟩
    · exact h
    · exact absurd hv (by simp)
  have hrknone : rk none = 0 := by
    rcases hspec none with ⟨-, -, h, -⟩ | ⟨v, hv, -⟩
    · exact h
    · exact absurd hv (by simp)
  have hsome : ∀ v : V,
      (∃ e ∈ M, v ∈ e ∧ hub (some v) = some e ∧
        ((v = efst e ∧ par (some v) = none ∧ rk (some v) = 1) ∨
         (v = esnd e ∧ par (some v) = some (some (efst e)) ∧ rk (some v) = 2))) ∨
      ((∀ e ∈ M, v ∉ e) ∧ rk (some v) = 3 ∧
        ((∃ w : V, (∃ e ∈ M, w ∈ e ∧ hub (some v) = some e) ∧ G.Adj (some v) (some w) ∧
            par (some v) = some (some w)) ∨
         ((∀ w : V, ¬G.Adj (some v) (some w)) ∧ G.Adj (some v) none ∧
            par (some v) = some none ∧ hub (some v) = none) ∨
         ((∀ w : V, ¬G.Adj (some v) (some w)) ∧ ¬G.Adj (some v) none ∧
            par (some v) = none ∧ hub (some v) = none))) := by
    intro v
    rcases hspec (some v) with ⟨h, -⟩ | ⟨v', hv', h⟩
    · exact absurd h (by simp)
    · obtain rfl : v = v' := Option.some.inj hv'
      exact h
  
  have hdec : ∀ x y, par x = some y → rk y < rk x := by
    intro x y hxy
    rcases x with _ | v
    · rw [hparnone] at hxy
      exact absurd hxy (by simp)
    · rcases hsome v with ⟨e, he, hv, -, ⟨-, hpar, -⟩ | ⟨-, hpar, hrk2⟩⟩ | ⟨-, hrk3, hcase⟩
      · rw [hpar] at hxy
        exact absurd hxy (by simp)
      · rw [hpar] at hxy
        obtain rfl : some (efst e) = y := Option.some.inj hxy
        rcases hsome (efst e) with ⟨e', he', hv', -, ⟨-, -, hrk1⟩ | ⟨h2', -, -⟩⟩ |
          ⟨hunm', -, -⟩
        · omega
        · rw [huniq e' he' e he (efst e) hv' (efst_mem e)] at h2'
          exact absurd h2' (hMne e he)
        · exact absurd (efst_mem e) (hunm' e he)
      · rcases hcase with ⟨w, ⟨e, he, hwe, -⟩, -, hpar⟩ | ⟨-, -, hpar, -⟩ | ⟨-, -, hpar, -⟩
        · rw [hpar] at hxy
          obtain rfl : some w = y := Option.some.inj hxy
          rcases hsome w with ⟨e', he', hv', -, ⟨-, -, hrk'⟩ | ⟨-, -, hrk'⟩⟩ | ⟨hunm', -, -⟩
          · omega
          · omega
          · exact absurd hwe (hunm' e he)
        · rw [hpar] at hxy
          obtain rfl : (none : Option V) = y := Option.some.inj hxy
          omega
        · rw [hpar] at hxy
          exact absurd hxy (by simp)
  have hrkle3 : ∀ v : V, rk (some v) ≤ 3 := by
    intro v
    rcases hsome v with ⟨e, he, hv, hhub, hcase⟩ | ⟨hunm, hrk, hcase⟩
    · rcases hcase with ⟨hfst, hpar, hrk⟩ | ⟨hsnd, hpar, hrk⟩ <;> omega
    · omega
  have hFadj : ∀ x y, par x = some y → (pgraph par).Adj x y := by
    intro x y h
    rw [pgraph_adj]
    refine ⟨?_, Or.inl h⟩
    intro heq
    subst heq
    exact lt_irrefl _ (hdec x x h)
  
  have hhub_matched : ∀ (x : V) (e : Sym2 V), e ∈ M → x ∈ e → hub (some x) = some e := by
    intro x e he hx
    rcases hsome x with ⟨e', he', hv', hhb', -⟩ | ⟨hunm, -, -⟩
    · rwa [huniq e' he' e he x hv' hx] at hhb'
    · exact absurd hx (hunm e he)
  have hhub_M : ∀ (x : V) (e : Sym2 V), hub (some x) = some e → e ∈ M := by
    intro x e hx
    rcases hsome x with ⟨e', he', -, hhb', -⟩ | ⟨-, -, hcase⟩
    · rw [hhb'] at hx
      exact (Option.some.inj hx) ▸ he'
    · rcases hcase with ⟨w, ⟨e', he', -, hhb'⟩, -, -⟩ | ⟨-, -, -, hhb'⟩ | ⟨-, -, -, hhb'⟩
      · rw [hhb'] at hx
        exact (Option.some.inj hx) ▸ he'
      · rw [hhb'] at hx
        exact absurd hx (by simp)
      · rw [hhb'] at hx
        exact absurd hx (by simp)
  have hchild_matched : ∀ w v : V, par (some w) = some (some v) → ∃ e ∈ M, v ∈ e := by
    intro w v h
    rcases hsome w with ⟨e, he, hw, -, ⟨-, hpar, -⟩ | ⟨-, hpar, -⟩⟩ | ⟨-, -, hcase⟩
    · rw [hpar] at h
      exact absurd h (by simp)
    · rw [hpar] at h
      obtain rfl : efst e = v := Option.some.inj (Option.some.inj h)
      exact ⟨e, he, efst_mem e⟩
    · rcases hcase with ⟨w', ⟨e, he, hwe, -⟩, -, hpar⟩ | ⟨-, -, hpar, -⟩ | ⟨-, -, hpar, -⟩
      · rw [hpar] at h
        obtain rfl : w' = v := Option.some.inj (Option.some.inj h)
        exact ⟨e, he, hwe⟩
      · rw [hpar] at h
        exact absurd (Option.some.inj h) (by simp)
      · rw [hpar] at h
        exact absurd h (by simp)
  have hpar_live : ∀ v w : V, par (some v) = some (some w) →
      ∃ e ∈ M, hub (some v) = some e ∧ hub (some w) = some e := by
    intro v w h
    rcases hsome v with ⟨e, he, hv, hhb, ⟨-, hpar, -⟩ | ⟨-, hpar, -⟩⟩ | ⟨-, -, hcase⟩
    · rw [hpar] at h
      exact absurd h (by simp)
    · rw [hpar] at h
      obtain rfl : efst e = w := Option.some.inj (Option.some.inj h)
      exact ⟨e, he, hhb, hhub_matched _ e he (efst_mem e)⟩
    · rcases hcase with ⟨w', ⟨e, he, hwe, hhb⟩, -, hpar⟩ | ⟨-, -, hpar, -⟩ | ⟨-, -, hpar, -⟩
      · rw [hpar] at h
        obtain rfl : w' = w := Option.some.inj (Option.some.inj h)
        exact ⟨e, he, hhb, hhub_matched _ e he hwe⟩
      · rw [hpar] at h
        exact absurd (Option.some.inj h) (by simp)
      · rw [hpar] at h
        exact absurd h (by simp)
  have hAdj_live : ∀ v w : V, (pgraph par).Adj (some v) (some w) →
      ∃ e ∈ M, hub (some v) = some e ∧ hub (some w) = some e := by
    intro v w h
    rw [pgraph_adj] at h
    rcases h.2 with h' | h'
    · exact hpar_live v w h'
    · obtain ⟨e, he, h1, h2⟩ := hpar_live w v h'
      exact ⟨e, he, h2, h1⟩
  have hAdj_root : ∀ x : Option V, (pgraph par).Adj x none →
      ∃ v : V, x = some v ∧ par (some v) = some none := by
    intro x h
    rw [pgraph_adj] at h
    rcases h.2 with h' | h'
    · rcases x with _ | v
      · exact absurd rfl h.1
      · exact ⟨v, rfl, h'⟩
    · rw [hparnone] at h'
      exact absurd h' (by simp)
  have hpar_root : ∀ v : V, par (some v) = some none →
      (∀ w : V, ¬G.Adj (some v) (some w)) ∧ G.Adj (some v) none := by
    intro v h
    rcases hsome v with ⟨e, he, hv, -, ⟨-, hpar, -⟩ | ⟨-, hpar, -⟩⟩ | ⟨-, -, hcase⟩
    · rw [hpar] at h
      exact absurd h (by simp)
    · rw [hpar] at h
      exact absurd (Option.some.inj h) (by simp)
    · rcases hcase with ⟨w, -, -, hpar⟩ | ⟨hnl, hroot, -, -⟩ | ⟨-, -, hpar, -⟩
      · rw [hpar] at h
        exact absurd (Option.some.inj h) (by simp)
      · exact ⟨hnl, hroot⟩
      · rw [hpar] at h
        exact absurd h (by simp)
  
  have hAdj_dist1 : ∀ x y, (pgraph par).Adj x y → (pgraph par).dist x y ≤ 1 := by
    intro x y h
    have := SimpleGraph.dist_le (Walk.cons h Walk.nil)
    simpa using this
  have hsum : ∀ (v : V) (e : Sym2 V), e ∈ M → hub (some v) = some e →
      (pgraph par).Reachable (some v) (some (efst e)) ∧
      (pgraph par).Reachable (some v) (some (esnd e)) ∧
      (pgraph par).dist (some v) (some (efst e)) +
        (pgraph par).dist (some v) (some (esnd e)) ≤ 3 := by
    intro v e he hhb
    have hedge : (pgraph par).Adj (some (esnd e)) (some (efst e)) := by
      rcases hsome (esnd e) with ⟨e', he', hv', -, ⟨h1, -, -⟩ | ⟨-, hpar, -⟩⟩ | ⟨hunm, -, -⟩
      · rw [huniq e' he' e he (esnd e) hv' (esnd_mem e)] at h1
        exact absurd h1.symm (hMne e he)
      · have he'e : e' = e := huniq e' he' e he (esnd e) hv' (esnd_mem e)
        subst he'e
        exact hFadj _ _ hpar
      · exact absurd (esnd_mem e) (hunm e he)
    rcases hsome v with ⟨e', he', hv', hhb', hbr⟩ | ⟨-, -, hcase⟩
    · have he'e : e' = e := by
        rw [hhb'] at hhb
        exact Option.some.inj hhb
      subst he'e
      rcases hbr with ⟨h1, -, -⟩ | ⟨h2, -, -⟩
      · subst h1
        have d0 : (pgraph par).dist (some (efst e')) (some (efst e')) = 0 :=
          SimpleGraph.dist_self
        have d1 : (pgraph par).dist (some (efst e')) (some (esnd e')) ≤ 1 := by
          have := hAdj_dist1 _ _ hedge
          have hcomm : (pgraph par).dist (some (esnd e')) (some (efst e')) =
              (pgraph par).dist (some (efst e')) (some (esnd e')) := SimpleGraph.dist_comm
          omega
        exact ⟨SimpleGraph.Reachable.refl _, hedge.symm.reachable, by omega⟩
      · subst h2
        have d0 : (pgraph par).dist (some (esnd e')) (some (esnd e')) = 0 :=
          SimpleGraph.dist_self
        have d1 : (pgraph par).dist (some (esnd e')) (some (efst e')) ≤ 1 :=
          hAdj_dist1 _ _ hedge
        exact ⟨hedge.reachable, SimpleGraph.Reachable.refl _, by omega⟩
    · rcases hcase with ⟨w, ⟨e', he', hwe, hhb'⟩, -, hpar⟩ | ⟨-, -, -, hhb'⟩ | ⟨-, -, -, hhb'⟩
      · have he'e : e' = e := by
          rw [hhb'] at hhb
          exact Option.some.inj hhb
        subst he'e
        have hvw : (pgraph par).Adj (some v) (some w) := hFadj _ _ hpar
        have dvw : (pgraph par).dist (some v) (some w) ≤ 1 := hAdj_dist1 _ _ hvw
        rcases mem_out_cases hwe with hw1 | hw2
        · subst hw1
          have r1 : (pgraph par).Reachable (some v) (some (efst e')) := hvw.reachable
          have r2 : (pgraph par).Reachable (some v) (some (esnd e')) :=
            r1.trans hedge.symm.reachable
          have tri := r1.dist_triangle_left (some (esnd e'))
          have d2 : (pgraph par).dist (some (efst e')) (some (esnd e')) ≤ 1 := by
            have := hAdj_dist1 _ _ hedge
            have hcomm : (pgraph par).dist (some (esnd e')) (some (efst e')) =
                (pgraph par).dist (some (efst e')) (some (esnd e')) := SimpleGraph.dist_comm
            omega
          exact ⟨r1, r2, by omega⟩
        · subst hw2
          have r2 : (pgraph par).Reachable (some v) (some (esnd e')) := hvw.reachable
          have r1 : (pgraph par).Reachable (some v) (some (efst e')) :=
            r2.trans hedge.reachable
          have tri := r2.dist_triangle_left (some (efst e'))
          have d2 : (pgraph par).dist (some (esnd e')) (some (efst e')) ≤ 1 :=
            hAdj_dist1 _ _ hedge
          exact ⟨r1, r2, by omega⟩
      · rw [hhb'] at hhb
        exact absurd hhb (by simp)
      · rw [hhb'] at hhb
        exact absurd hhb (by simp)
  
  have hrootstar : ∀ x y, (pgraph par).Adj x y →
      (x = none ∨ ∃ w : V, x = some w ∧ par (some w) = some none) →
      (y = none ∨ ∃ w : V, y = some w ∧ par (some w) = some none) := by
    rintro x y hxy (rfl | ⟨w, rfl, hw⟩)
    · obtain ⟨v', hv', hpar'⟩ := hAdj_root _ hxy.symm
      exact Or.inr ⟨v', hv', hpar'⟩
    · rw [pgraph_adj] at hxy
      rcases hxy.2 with h' | h'
      · rw [hw] at h'
        exact Or.inl (Option.some.inj h').symm
      · rcases y with _ | wy
        · exact Or.inl rfl
        · obtain ⟨e, he, hwem⟩ := hchild_matched wy w h'
          obtain ⟨w', hw'⟩ := hmatched_hasnbr e he w hwem
          obtain ⟨hnl, -⟩ := hpar_root w hw
          exact absurd hw' (hnl w')
  
  have hle : pgraph par ≤ G := by
    have key : ∀ x y, par x = some y → G.Adj x y := by
      intro x y h
      rcases x with _ | v
      · rw [hparnone] at h
        exact absurd h (by simp)
      · rcases hsome v with ⟨e, he, hv, -, ⟨-, hpar, -⟩ | ⟨h2, hpar, -⟩⟩ | ⟨-, -, hcase⟩
        · rw [hpar] at h
          exact absurd h (by simp)
        · rw [hpar] at h
          obtain rfl : some (efst e) = y := Option.some.inj h
          rw [h2]
          exact (hMout e he).symm
        · rcases hcase with ⟨w, ⟨e, he, hwe, -⟩, hadj, hpar⟩ | ⟨-, hroot, hpar, -⟩ |
            ⟨-, -, hpar, -⟩
          · rw [hpar] at h
            obtain rfl : some w = y := Option.some.inj h
            exact hadj
          · rw [hpar] at h
            obtain rfl : (none : Option V) = y := Option.some.inj h
            exact hroot
          · rw [hpar] at h
            exact absurd h (by simp)
    intro x y hxy
    rw [pgraph_adj] at hxy
    rcases hxy.2 with h | h
    · exact key _ _ h
    · exact (key _ _ h).symm
  
  have hdiam : ∀ u v : Option V, (pgraph par).Reachable u v →
      ¬(pgraph par).Reachable u none → (pgraph par).dist u v ≤ 3 := by
    intro u v hru hnr
    rcases u with _ | vu
    · exact absurd (SimpleGraph.Reachable.refl _) hnr
    rcases v with _ | vv
    · exact absurd hru hnr
    rcases hE : hub (some vu) with _ | e
    · rcases hsome vu with ⟨e, he, hv, hhb, -⟩ | ⟨hunm, -, hcase⟩
      · rw [hhb] at hE
        exact absurd hE (by simp)
      · rcases hcase with ⟨w, ⟨e, he, hwe, hhb⟩, -, -⟩ | ⟨hnl, hroot, hpar, -⟩ |
          ⟨hnl, hnr', hpar, -⟩
        · rw [hhb] at hE
          exact absurd hE (by simp)
        · exact absurd (hFadj _ _ hpar).reachable hnr
        · 
          have hnoadj : ∀ y, ¬(pgraph par).Adj (some vu) y := by
            intro y hy
            rw [pgraph_adj] at hy
            rcases hy.2 with h' | h'
            · rw [hpar] at h'
              exact absurd h' (by simp)
            · rcases y with _ | w
              · rw [hparnone] at h'
                exact absurd h' (by simp)
              · obtain ⟨e, he, hve⟩ := hchild_matched w vu h'
                obtain ⟨w', hw'⟩ := hmatched_hasnbr e he vu hve
                exact absurd hw' (hnl w')
          have hvv := reachable_invariant (Q := fun z => z = some vu)
            (fun x y hxy hx => absurd (hx ▸ hxy) (hnoadj y)) hru rfl
          obtain rfl : vv = vu := Option.some.inj hvv
          simp [SimpleGraph.dist_self]
    · 
      have heM : e ∈ M := hhub_M vu e hE
      have hinv : ∀ x y, (pgraph par).Adj x y →
          (∃ vz : V, x = some vz ∧ hub (some vz) = some e) →
          (∃ vz : V, y = some vz ∧ hub (some vz) = some e) := by
        rintro x y hxy ⟨vx, rfl, hx⟩
        rcases y with _ | vy
        · obtain ⟨v', hv', hpar'⟩ := hAdj_root _ hxy
          obtain rfl : vx = v' := Option.some.inj hv'
          obtain ⟨hnl, -⟩ := hpar_root _ hpar'
          rcases hsome vx with ⟨e', he', hv'', -, -⟩ | ⟨-, -, hcase⟩
          · obtain ⟨w', hw'⟩ := hmatched_hasnbr e' he' vx hv''
            exact absurd hw' (hnl w')
          · rcases hcase with ⟨w, ⟨e', he', hwe, -⟩, hadj', -⟩ | ⟨-, -, -, hhb'⟩ |
              ⟨-, -, -, hhb'⟩
            · exact absurd hadj' (hnl w)
            · rw [hhb'] at hx
              exact absurd hx (by simp)
            · rw [hhb'] at hx
              exact absurd hx (by simp)
        · obtain ⟨e', he', h1, h2⟩ := hAdj_live vx vy hxy
          rw [hx] at h1
          obtain rfl : e = e' := Option.some.inj h1
          exact ⟨vy, rfl, h2⟩
      obtain ⟨vv', hvv', hEv⟩ := reachable_invariant hinv hru ⟨vu, rfl, hE⟩
      obtain rfl : vv = vv' := Option.some.inj hvv'
      obtain ⟨ru1, ru2, hdu⟩ := hsum vu e heM hE
      obtain ⟨rv1, rv2, hdv⟩ := hsum vv e heM hEv
      have t1 := ru1.dist_triangle_left (some vv)
      have t2 := ru2.dist_triangle_left (some vv)
      have c1 : (pgraph par).dist (some (efst e)) (some vv) =
          (pgraph par).dist (some vv) (some (efst e)) := SimpleGraph.dist_comm
      have c2 : (pgraph par).dist (some (esnd e)) (some vv) =
          (pgraph par).dist (some vv) (some (esnd e)) := SimpleGraph.dist_comm
      omega
  
  have hroot4 : ∀ v : V, (pgraph par).Reachable (some v) none →
      (pgraph par).dist (some v) none ≤ 4 := by
    intro v hrv
    rcases reachable_invariant hrootstar hrv.symm (Or.inl rfl) with h | ⟨w, hw, hpar'⟩
    · exact absurd h (by simp)
    · obtain rfl : v = w := Option.some.inj hw
      have h1 := hAdj_dist1 _ _ (hFadj _ _ hpar')
      omega
  
  have hIA : ∀ a : V, a ∈ M.image efst ∪ II →
      (none : Option V) ∉ ((pgraph par).connectedComponentMk (some a)).supp := by
    intro a ha hmem
    rw [ConnectedComponent.mem_supp_iff] at hmem
    have hreach : (pgraph par).Reachable none (some a) := ConnectedComponent.eq.mp hmem
    rcases reachable_invariant hrootstar hreach (Or.inl rfl) with h | ⟨w, hw, hpar'⟩
    · exact absurd h (by simp)
    · obtain rfl : a = w := Option.some.inj hw
      obtain ⟨hnl, hroot⟩ := hpar_root a hpar'
      rcases Finset.mem_union.mp ha with hA | hII
      · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hA
        obtain ⟨w', hw'⟩ := hmatched_hasnbr e he _ (efst_mem e)
        exact absurd hw' (hnl w')
      · rw [hIIdef] at hII
        exact absurd hroot ((Finset.mem_filter.mp hII).2 none)
  have hsurj : Function.Surjective
      (fun a : {a : V // a ∈ M.image efst ∪ II} =>
        (⟨(pgraph par).connectedComponentMk (some a.1), hIA a.1 a.2⟩ :
          {c : (pgraph par).ConnectedComponent // (none : Option V) ∉ c.supp})) := by
    rintro ⟨c, hc⟩
    obtain ⟨x, rfl⟩ := c.exists_rep
    rcases x with _ | vx
    · exact absurd ((ConnectedComponent.mem_supp_iff _ _).mpr rfl) hc
    · rcases hsome vx with ⟨e, he, hv, hhb, -⟩ | ⟨-, -, hcase⟩
      · refine ⟨⟨efst e, Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e, he, rfl⟩)⟩, ?_⟩
        exact Subtype.ext (ConnectedComponent.sound (hsum vx e he hhb).1.symm)
      · rcases hcase with ⟨w, ⟨e, he, hwe, hhb⟩, -, -⟩ | ⟨-, -, hpar, -⟩ | ⟨hnl, hnr', -, -⟩
        · refine ⟨⟨efst e, Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e, he, rfl⟩)⟩, ?_⟩
          exact Subtype.ext (ConnectedComponent.sound (hsum vx e he hhb).1.symm)
        · have hreach : (pgraph par).Reachable (some vx) none := (hFadj _ _ hpar).reachable
          exact absurd ((ConnectedComponent.mem_supp_iff _ _).mpr
            (ConnectedComponent.sound hreach.symm)) hc
        · refine ⟨⟨vx, Finset.mem_union_right _ ?_⟩, ?_⟩
          · rw [hIIdef]
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
            intro w
            cases w with
            | none => exact hnr'
            | some w' => exact hnl w'
          · exact Subtype.ext rfl
  have hAcard : (M.image efst).card = M.card := by
    apply Finset.card_image_of_injOn
    intro e he e' he' h
    exact huniq e (Finset.mem_coe.mp he) e' (Finset.mem_coe.mp he') (efst e) (efst_mem e)
      (by rw [h]; exact efst_mem e')
  have hBcard : (M.image esnd).card = M.card := by
    apply Finset.card_image_of_injOn
    intro e he e' he' h
    exact huniq e (Finset.mem_coe.mp he) e' (Finset.mem_coe.mp he') (esnd e) (esnd_mem e)
      (by rw [h]; exact esnd_mem e')
  have hABdisj : Disjoint (M.image efst) (M.image esnd) := by
    rw [Finset.disjoint_left]
    intro a haA haB
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp haA
    obtain ⟨e', he', h2⟩ := Finset.mem_image.mp haB
    have he'e : e' = e := huniq e' he' e he (efst e) (by rw [← h2]; exact esnd_mem e')
      (efst_mem e)
    subst he'e
    exact hMne e' he (by rw [h2])
  have hAIdisj : Disjoint (M.image efst) II := by
    rw [Finset.disjoint_left]
    intro a haA haI
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp haA
    obtain ⟨w', hw'⟩ := hmatched_hasnbr e he _ (efst_mem e)
    rw [hIIdef] at haI
    exact (Finset.mem_filter.mp haI).2 (some w') hw'
  have hBIdisj : Disjoint (M.image esnd) II := by
    rw [Finset.disjoint_left]
    intro a haA haI
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp haA
    obtain ⟨w', hw'⟩ := hmatched_hasnbr e he _ (esnd_mem e)
    rw [hIIdef] at haI
    exact (Finset.mem_filter.mp haI).2 (some w') hw'
  have hcard2 : (M.image efst).card + (M.image esnd).card + II.card ≤ Fintype.card V := by
    have hd : Disjoint (M.image efst ∪ M.image esnd) II :=
      Finset.disjoint_union_left.mpr ⟨hAIdisj, hBIdisj⟩
    have h1 : (M.image efst ∪ M.image esnd ∪ II).card =
        (M.image efst).card + (M.image esnd).card + II.card := by
      rw [Finset.card_union_of_disjoint hd, Finset.card_union_of_disjoint hABdisj]
    exact h1 ▸ Finset.card_le_univ _
  have hcard1 : Nat.card {c : (pgraph par).ConnectedComponent // (none : Option V) ∉ c.supp} ≤
      (M.image efst ∪ II).card := by
    calc Nat.card {c : (pgraph par).ConnectedComponent // (none : Option V) ∉ c.supp}
        ≤ Nat.card {a : V // a ∈ M.image efst ∪ II} :=
          Nat.card_le_card_of_surjective _ hsurj
      _ = (M.image efst ∪ II).card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  have hcount : 2 * Nat.card {c : (pgraph par).ConnectedComponent //
      (none : Option V) ∉ c.supp} ≤ Fintype.card V + f := by
    have h3 : (M.image efst ∪ II).card ≤ (M.image efst).card + II.card :=
      Finset.card_union_le _ _
    have h4 : II.card ≤ f := hf
    omega
  have hrootsub : (Finset.univ.filter fun v : V => par (some v) = none) ⊆
      M.image efst ∪ II := by
    intro v hv
    have hp := (Finset.mem_filter.mp hv).2
    rcases hsome v with ⟨e, he, hve, hhub, hcase⟩ | ⟨hunm, hrk, hcase⟩
    · rcases hcase with ⟨hfst, hpar, hrk⟩ | ⟨hsnd, hpar, hrk⟩
      · apply Finset.mem_union_left
        apply Finset.mem_image.mpr
        exact ⟨e, he, hfst.symm⟩
      · rw [hpar] at hp
        contradiction
    · rcases hcase with ⟨w, hw, hadj, hpar⟩ | ⟨hnl, hroot, hpar, hhub⟩ |
          ⟨hnl, hroot, hpar, hhub⟩
      · rw [hpar] at hp
        contradiction
      · rw [hpar] at hp
        contradiction
      · apply Finset.mem_union_right
        rw [hIIdef]
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        intro y
        cases y with
        | none => exact hroot
        | some w => exact hnl w
  have hrootcard : (Finset.univ.filter fun v : V => par (some v) = none).card ≤
      (M.image efst ∪ II).card := Finset.card_le_card hrootsub
  have hrootcount :
      2 * (Finset.univ.filter fun v : V => par (some v) = none).card ≤
        Fintype.card V + f := by
    have h3 : (M.image efst ∪ II).card ≤ (M.image efst).card + II.card :=
      Finset.card_union_le _ _
    have h4 : II.card ≤ f := hf
    omega
  exact ⟨pgraph par, hle, pgraph_isAcyclic par rk hdec, hdiam, hroot4, hcount,
    par, rk, pgraph_adj par, hdec, hrkle3, hrootcount⟩

end NUS







namespace NUS

open MinimalNUS


theorem exists_departing_pair {p n : ℕ} [Fact p.Prime] (S : MinimalNUS p n)
    (P : S.Pairing) (X Y : Finset (Fin n)) (hX : X.Nonempty) (hY : Y.Nonempty)
    (hXY : Disjoint X Y) (hlight : 2 ^ (X.card + Y.card - 2) < p) :
    ∃ t ∈ MinimalNUS.rectangle X Y, P.μ t ∉ MinimalNUS.rectangle X Y := by
  by_contra h
  push Not at h
  have hinv : ∀ t ∈ MinimalNUS.rectangle X Y,
      P.μ t ∈ MinimalNUS.rectangle X Y := by
    intro t ht
    exact h t ht
  have hp := MinimalNUS.clean_rectangle S P X Y hX hY hXY hinv
  omega




def departingLive {V : Type*} [DecidableEq V] (i j : V) (ν : Multiset V) : V → ℤ :=
  Pi.single i 1 + Pi.single j 1 - fun v => (ν.count v : ℤ)


def IsUnitRelation {V : Type*} [DecidableEq V] (w : V → ℤ) : Prop :=
  (∃ a, w = Pi.single a 1) ∨
  (∃ a b, a ≠ b ∧ w = Pi.single a 1 - Pi.single b 1) ∨
  (∃ a, w = -(Pi.single a 1)) ∨
  ∃ a b, a ≠ b ∧ w = -(Pi.single a 1 - Pi.single b 1)


theorem unitRelation_normalize_at_one {V : Type*} [DecidableEq V]
    {w : V → ℤ} (i : V) (hu : IsUnitRelation w) (hi : w i = 1) :
    w = Pi.single i 1 ∨
      ∃ b, b ≠ i ∧ w = Pi.single i 1 - Pi.single b 1 := by
  rcases hu with ⟨a, ha⟩ | ⟨a, b, hab, ha⟩ | ⟨a, ha⟩ | ⟨a, b, hab, ha⟩
  · have hai : a = i := by
      by_contra h
      have hv := congrFun ha i
      simp [h] at hv hi
      omega
    subst a
    exact Or.inl ha
  · have hai : a = i := by
      by_contra hia
      have hbi : b ≠ i := by
        intro hbi
        subst b
        have hv := congrFun ha i
        simp [hia] at hv hi
        omega
      have hv := congrFun ha i
      simp [hia, hbi] at hv hi
      omega
    subst a
    exact Or.inr ⟨b, hab.symm, ha⟩
  · exfalso
    have hv := congrFun ha i
    by_cases hai : a = i <;> simp [hai] at hv hi <;> omega
  · have hbi : b = i := by
      by_contra hbi
      have hai : a ≠ i := by
        intro hai
        subst a
        have hv := congrFun ha i
        simp [hbi] at hv hi
        omega
      have hv := congrFun ha i
      simp [hai, hbi] at hv hi
      omega
    subst b
    right
    refine ⟨a, hab, ?_⟩
    rw [ha]
    ext v
    simp only [Pi.neg_apply, Pi.sub_apply]
    ring


theorem unitRelation_restrict_at_one {V : Type*} [Fintype V] [DecidableEq V]
    {w : V → ℤ} (i : V) (hu : IsUnitRelation w) (hi : w i = 1)
    (T : Finset V) (hiT : i ∉ T) :
    IsUnitRelation (fun v : {v : V // v ∉ T} => w v.1) := by
  rcases unitRelation_normalize_at_one i hu hi with hw | ⟨b, hbi, hw⟩
  · left
    refine ⟨⟨i, hiT⟩, ?_⟩
    funext v
    rw [hw]
    simp [Pi.single_apply, Subtype.ext_iff]
  · by_cases hbT : b ∈ T
    · left
      refine ⟨⟨i, hiT⟩, ?_⟩
      funext v
      rw [hw]
      have hvb : v.1 ≠ b := fun e => v.2 (e ▸ hbT)
      simp [Pi.single_apply, hvb, Subtype.ext_iff]
    · right; left
      refine ⟨⟨i, hiT⟩, ⟨b, hbT⟩, ?_, ?_⟩
      · exact fun e => hbi (congrArg Subtype.val e).symm
      · funext v
        rw [hw]
        simp [Pi.single_apply, Subtype.ext_iff]

theorem multiset_card_le_two_cases {V : Type*} (ν : Multiset V) (hν : ν.card ≤ 2) :
    ν = 0 ∨ (∃ a, ν = {a}) ∨ ∃ a b, ν = {a, b} := by
  rcases Nat.eq_zero_or_pos ν.card with h0 | hp
  · exact Or.inl (Multiset.card_eq_zero.mp h0)
  have hc : ν.card = 1 ∨ ν.card = 2 := by omega
  rcases hc with h1 | h2
  · obtain ⟨a, ha⟩ := Multiset.card_eq_one.mp h1
    exact Or.inr (Or.inl ⟨a, ha⟩)
  · obtain ⟨a, b, hab⟩ := Multiset.card_eq_two.mp h2
    exact Or.inr (Or.inr ⟨a, b, hab⟩)

theorem count_pair_apply {V : Type*} [DecidableEq V] (a b v : V) :
    (({a, b} : Multiset V).count v : ℤ) =
      (Pi.single a (1 : ℤ) : V → ℤ) v + (Pi.single b (1 : ℤ) : V → ℤ) v := by
  have hc : ({a, b} : Multiset V).count v =
      (if v = a then 1 else 0) + if v = b then 1 else 0 := by
    rw [Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton]
    rw [add_comm]
  rw [hc]
  simp only [Pi.single_apply]
  push_cast
  rfl

theorem count_singleton_apply {V : Type*} [DecidableEq V] (a v : V) :
    (({a} : Multiset V).count v : ℤ) = (Pi.single a (1 : ℤ) : V → ℤ) v := by
  rw [Multiset.count_singleton]
  simp only [Pi.single_apply]
  split <;> norm_num


theorem departingLive_unit_of_mem_right {V : Type*} [DecidableEq V]
    (i j : V) (ν : Multiset V) (hcard : ν.card ≤ 2) (hmem : j ∈ ν)
    (hne : ν ≠ {i, j}) : IsUnitRelation (departingLive i j ν) := by
  rcases multiset_card_le_two_cases ν hcard with h0 | ⟨a, ha⟩ | ⟨a, b, hab⟩
  · rw [h0] at hmem
    simp at hmem
  · subst ν
    simp only [Multiset.mem_singleton] at hmem
    subst a
    left
    refine ⟨i, ?_⟩
    ext v
    simp [departingLive, count_singleton_apply]
  · subst ν
    rw [Multiset.insert_eq_cons] at hmem
    simp only [Multiset.mem_cons, Multiset.mem_singleton] at hmem
    rcases hmem with rfl | rfl
    · by_cases hbi : b = i
      · subst b
        exact absurd (Multiset.pair_comm j i) hne
      · right; left
        refine ⟨i, b, Ne.symm hbi, ?_⟩
        ext v
        simp only [departingLive, Pi.add_apply, Pi.sub_apply]
        rw [count_pair_apply]
        ring
    · by_cases hai : a = i
      · subst a
        exact absurd (by simp) hne
      · right; left
        refine ⟨i, a, Ne.symm hai, ?_⟩
        ext v
        simp only [departingLive, Pi.add_apply, Pi.sub_apply]
        rw [count_pair_apply]
        ring

theorem departingLive_comm {V : Type*} [DecidableEq V] (i j : V) (ν : Multiset V) :
    departingLive i j ν = departingLive j i ν := by
  ext v
  simp only [departingLive, Pi.add_apply, Pi.sub_apply]
  ring


theorem departingLive_unit_of_mem_left {V : Type*} [DecidableEq V]
    (i j : V) (ν : Multiset V) (hcard : ν.card ≤ 2) (hmem : i ∈ ν)
    (hne : ν ≠ {i, j}) : IsUnitRelation (departingLive i j ν) := by
  have hne' : ν ≠ {j, i} := by
    intro h
    apply hne
    rw [h, Multiset.pair_comm]
  rw [departingLive_comm i j ν]
  exact departingLive_unit_of_mem_right j i ν hcard hmem hne'


theorem departingLive_anchor_of_mem_right {V : Type*} [DecidableEq V]
    (i j : V) (ν : Multiset V) (hij : i ≠ j) (hcard : ν.card ≤ 2)
    (hmem : j ∈ ν) (hne : ν ≠ {i, j}) : departingLive i j ν i = 1 := by
  rcases multiset_card_le_two_cases ν hcard with h0 | ⟨a, ha⟩ | ⟨a, b, hab⟩
  · subst ν
    simp at hmem
  · subst ν
    simp only [Multiset.mem_singleton] at hmem
    subst a
    simp [departingLive, count_singleton_apply, Pi.single_apply, hij]
  · subst ν
    have hj : j = a ∨ j = b := by simpa using hmem
    have hi : i ≠ a ∧ i ≠ b := by
      constructor
      · intro hia
        subst a
        rcases hj with hji | hjb
        · exact hij hji.symm
        · apply hne
          simp [hjb]
      · intro hib
        subst b
        rcases hj with hja | hji
        · subst j
          exact hne (Multiset.pair_comm a i)
        · exact hij hji.symm
    simp only [departingLive, Pi.add_apply, Pi.sub_apply]
    rw [count_pair_apply]
    simp [hij, hi.1, hi.2]


theorem departingLive_label_of_mem_left {V : Type*} [DecidableEq V]
    (i j : V) (ν : Multiset V) (hij : i ≠ j) (hcard : ν.card ≤ 2)
    (hmem : i ∈ ν) (hne : ν ≠ {i, j}) : departingLive i j ν j = 1 := by
  rw [departingLive_comm]
  apply departingLive_anchor_of_mem_right j i ν hij.symm hcard hmem
  intro h
  apply hne
  exact h.trans (Multiset.pair_comm j i)

theorem departingLive_anchor_of_not_mem {V : Type*} [DecidableEq V]
    (i j : V) (ν : Multiset V) (hij : i ≠ j) (hi : i ∉ ν) :
    departingLive i j ν i = 1 := by
  simp [departingLive, hij, Multiset.count_eq_zero.mpr hi]


theorem departingLive_sub_same_type {V : Type*} [DecidableEq V]
    (i j j' : V) (ν : Multiset V) :
    departingLive i j ν - departingLive i j' ν =
      Pi.single j 1 - Pi.single j' 1 := by
  ext v
  simp only [departingLive, Pi.add_apply, Pi.sub_apply]
  ring

def IsEasyDeparture {V : Type*} (i j : V) (ν : Multiset V) : Prop :=
  i ∉ ν ∧ j ∉ ν ∧ ν.card ≤ 1

def IsProperDeparture {V : Type*} (i j : V) (ν : Multiset V) : Prop :=
  i ∉ ν ∧ j ∉ ν ∧ ν.card = 2


theorem easy_after_promote_unit {V : Type*} [Fintype V] [DecidableEq V]
    {i j : V} {ν : Multiset V} (h : IsEasyDeparture i j ν)
    (T : Finset V) (hiT : i ∉ T) (hjT : j ∈ T) :
    IsUnitRelation (fun v : {v : V // v ∉ T} => departingLive i j ν v.1) := by
  classical
  have hij : i ≠ j := by
    intro hij
    subst j
    exact hiT hjT
  rcases Nat.eq_zero_or_pos ν.card with hzero | hpos
  · have hν : ν = 0 := Multiset.card_eq_zero.mp hzero
    left
    refine ⟨⟨i, hiT⟩, ?_⟩
    funext v
    have hvj : v.1 ≠ j := fun e => v.2 (e ▸ hjT)
    simp [departingLive, hν, Pi.single_apply, hvj, Subtype.ext_iff]
  · have hle : ν.card ≤ 1 := h.2.2
    have hcard : ν.card = 1 := by omega
    obtain ⟨a, rfl⟩ := Multiset.card_eq_one.mp hcard
    have hia : i ≠ a := by simpa using h.1
    by_cases haT : a ∈ T
    · left
      refine ⟨⟨i, hiT⟩, ?_⟩
      funext v
      have hvj : v.1 ≠ j := fun e => v.2 (e ▸ hjT)
      have hva : v.1 ≠ a := fun e => v.2 (e ▸ haT)
      simp [departingLive, count_singleton_apply, Pi.single_apply, hvj, hva,
        Subtype.ext_iff]
    · right; left
      refine ⟨⟨i, hiT⟩, ⟨a, haT⟩, ?_, ?_⟩
      · exact fun e => hia (congrArg Subtype.val e)
      · funext v
        have hvj : v.1 ≠ j := fun e => v.2 (e ▸ hjT)
        simp [departingLive, count_singleton_apply, Pi.single_apply, hvj,
          Subtype.ext_iff]


theorem proper_after_promote_unit {V : Type*} [Fintype V] [DecidableEq V]
    {i j : V} {ν : Multiset V} (h : IsProperDeparture i j ν)
    (T : Finset V) (hiT : i ∉ T) (hjT : j ∈ T)
    (hhit : ∃ u ∈ T, u ∈ ν) :
    IsUnitRelation (fun v : {v : V // v ∉ T} => departingLive i j ν v.1) := by
  classical
  have hij : i ≠ j := by
    intro hij
    subst j
    exact hiT hjT
  obtain ⟨a, b, rfl⟩ := Multiset.card_eq_two.mp h.2.2
  have hia : i ≠ a := by
    intro e
    subst a
    exact h.1 (by simp)
  have hib : i ≠ b := by
    intro e
    subst b
    exact h.1 (by simp)
  rcases hhit with ⟨u, huT, huν⟩
  have habT : a ∈ T ∨ b ∈ T := by
    have huv : u = a ∨ u = b := by simpa using huν
    rcases huv with rfl | rfl
    · exact Or.inl huT
    · exact Or.inr huT
  by_cases haT : a ∈ T
  · by_cases hbT : b ∈ T
    · left
      refine ⟨⟨i, hiT⟩, ?_⟩
      funext v
      have hvj : v.1 ≠ j := fun e => v.2 (e ▸ hjT)
      have hva : v.1 ≠ a := fun e => v.2 (e ▸ haT)
      have hvb : v.1 ≠ b := fun e => v.2 (e ▸ hbT)
      simp only [departingLive, Pi.add_apply, Pi.sub_apply]
      rw [show (({a, b} : Multiset V).count v.1 : ℤ) =
        (Pi.single a (1 : ℤ) : V → ℤ) v.1 +
          (Pi.single b (1 : ℤ) : V → ℤ) v.1 by exact count_pair_apply a b v.1]
      simp [Pi.single_apply, hvj, hva, hvb, Subtype.ext_iff]
    · right; left
      refine ⟨⟨i, hiT⟩, ⟨b, hbT⟩, ?_, ?_⟩
      · exact fun e => hib (congrArg Subtype.val e)
      · funext v
        have hvj : v.1 ≠ j := fun e => v.2 (e ▸ hjT)
        have hva : v.1 ≠ a := fun e => v.2 (e ▸ haT)
        simp only [departingLive, Pi.add_apply, Pi.sub_apply]
        rw [show (({a, b} : Multiset V).count v.1 : ℤ) =
          (Pi.single a (1 : ℤ) : V → ℤ) v.1 +
            (Pi.single b (1 : ℤ) : V → ℤ) v.1 by exact count_pair_apply a b v.1]
        simp [Pi.single_apply, hvj, hva, Subtype.ext_iff]
  · have hbT : b ∈ T := habT.resolve_left haT
    right; left
    refine ⟨⟨i, hiT⟩, ⟨a, haT⟩, ?_, ?_⟩
    · exact fun e => hia (congrArg Subtype.val e)
    · funext v
      have hvj : v.1 ≠ j := fun e => v.2 (e ▸ hjT)
      have hvb : v.1 ≠ b := fun e => v.2 (e ▸ hbT)
      simp only [departingLive, Pi.add_apply, Pi.sub_apply]
      rw [show (({a, b} : Multiset V).count v.1 : ℤ) =
        (Pi.single a (1 : ℤ) : V → ℤ) v.1 +
          (Pi.single b (1 : ℤ) : V → ℤ) v.1 by exact count_pair_apply a b v.1]
      simp [Pi.single_apply, hvj, hvb, Subtype.ext_iff]


structure LiveBlocks (n : ℕ) (V : Type*) where
  block : V → Finset (Fin n)
  owner : Fin n → Option V
  mem_block_iff : ∀ a v, a ∈ block v ↔ owner a = some v
  nonempty : ∀ v, (block v).Nonempty

noncomputable def LiveBlocks.heavy {n : ℕ} {V : Type*}
    [Fintype V] [DecidableEq V] (B : LiveBlocks n V) (L : ℕ) : Finset V := by
  classical
  exact Finset.univ.filter fun v => L ≤ (B.block v).card

def LiveBlocks.mass {n : ℕ} {V : Type*} [Fintype V]
    (B : LiveBlocks n V) : ℕ := ∑ v, (B.block v).card

theorem LiveBlocks.disjoint {n : ℕ} {V : Type*} [DecidableEq V]
    (B : LiveBlocks n V) {i j : V} (hij : i ≠ j) : Disjoint (B.block i) (B.block j) := by
  rw [Finset.disjoint_left]
  intro a hai haj
  have hi := (B.mem_block_iff a i).mp hai
  have hj := (B.mem_block_iff a j).mp haj
  exact hij (Option.some.inj (hi.symm.trans hj))

theorem LiveBlocks.mass_le {n : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (B : LiveBlocks n V) : B.mass ≤ n := by
  classical
  have hd : (↑(Finset.univ : Finset V) : Set V).PairwiseDisjoint B.block := by
    intro i hi j hj hij
    exact B.disjoint hij
  calc
    B.mass = (Finset.univ.biUnion B.block).card := (Finset.card_biUnion hd).symm
    _ ≤ Finset.univ.card := Finset.card_le_univ _
    _ = n := Fintype.card_fin n


def liveLabels {n : ℕ} {V : Type*} (B : LiveBlocks n V) : Sym2 (Fin n) → Multiset V :=
  Sym2.lift ⟨fun a b => (B.owner a).toList + (B.owner b).toList, by
    intro a b
    exact add_comm _ _⟩

theorem liveLabels_mk {n : ℕ} {V : Type*} (B : LiveBlocks n V) (a b : Fin n) :
    liveLabels B s(a, b) = (B.owner a).toList + (B.owner b).toList := rfl

theorem liveLabels_card_le_two {n : ℕ} {V : Type*} (B : LiveBlocks n V)
    (t : Sym2 (Fin n)) : (liveLabels B t).card ≤ 2 := by
  induction t using Sym2.inductionOn with
  | hf a b =>
      simp only [liveLabels_mk, Multiset.card_add, Option.toList]
      split <;> split <;> simp

theorem liveLabels_source_pair {n : ℕ} {V : Type*} [DecidableEq V]
    (B : LiveBlocks n V) {i j : V} {t : Sym2 (Fin n)}
    (ht : t ∈ MinimalNUS.rectangle (B.block i) (B.block j)) :
    liveLabels B t = {i, j} := by
  obtain ⟨a, ha, b, hb, rfl⟩ := ht
  rw [liveLabels_mk, (B.mem_block_iff a i).mp ha, (B.mem_block_iff b j).mp hb]
  simp [Multiset.insert_eq_cons]

theorem mem_rectangle_of_liveLabels_eq_pair {n : ℕ} {V : Type*} [DecidableEq V]
    (B : LiveBlocks n V) {i j : V} (_hij : i ≠ j) {t : Sym2 (Fin n)}
    (ht : liveLabels B t = {i, j}) :
    t ∈ MinimalNUS.rectangle (B.block i) (B.block j) := by
  induction t using Sym2.inductionOn with
  | hf a b =>
      rw [liveLabels_mk] at ht
      rcases hOA : B.owner a with _ | u
      · have hc := congrArg Multiset.card ht
        simp [hOA] at hc
        rcases hOB : B.owner b with _ | v <;> simp [hOB] at hc
      rcases hOB : B.owner b with _ | v
      · have hc := congrArg Multiset.card ht
        simp [hOA, hOB] at hc
      have huv : ({u, v} : Multiset V) = {i, j} := by
        simpa [hOA, hOB, Multiset.insert_eq_cons] using ht
      rcases (multiset_pair_eq_pair.mp huv) with ⟨hui, hvj⟩ | ⟨huj, hvi⟩
      · subst u; subst v
        exact ⟨a, (B.mem_block_iff a i).mpr hOA, b,
          (B.mem_block_iff b j).mpr hOB, rfl⟩
      · subst u; subst v
        rw [Sym2.eq_swap]
        exact ⟨b, (B.mem_block_iff b i).mpr hOB, a,
          (B.mem_block_iff a j).mpr hOA, rfl⟩

theorem liveLabels_departing_ne {n : ℕ} {V : Type*} [DecidableEq V]
    (B : LiveBlocks n V) {i j : V} (hij : i ≠ j) {t : Sym2 (Fin n)}
    (hout : t ∉ MinimalNUS.rectangle (B.block i) (B.block j)) :
    liveLabels B t ≠ {i, j} := by
  intro h
  exact hout (mem_rectangle_of_liveLabels_eq_pair B hij h)


structure CompressionState {p n : ℕ} (S : MinimalNUS p n) (P : S.Pairing)
    (C V : Type*) [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V] where
  Q : Submodule ℤ (Fin n → ℤ)
  le_colLat : Q ≤ S.colLat P
  primitive : ∀ (v : Fin n → ℤ) (c : ℤ), c ≠ 0 → c • v ∈ Q → v ∈ Q
  basis : Module.Basis (Sum C V) ℤ ((Fin n → ℤ) ⧸ Q)
  blocks : LiveBlocks n V
  live_coord : ∀ a v,
    basis.repr (Submodule.Quotient.mk (Pi.single a 1)) (Sum.inr v) =
      if blocks.owner a = some v then 1 else 0

namespace CompressionState

variable {p n : ℕ} {S : MinimalNUS p n} {P : S.Pairing}
variable {C V : Type*} [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]
variable {B : LiveBlocks n V}

noncomputable def projectedRow (st : CompressionState S P C V) (t : Sym2 (Fin n)) : Sum C V → ℤ :=
  st.basis.repr (Submodule.Quotient.mk (S.rho P t))


def CoreBound (st : CompressionState S P C V) (M : ℤ) : Prop :=
  ∀ a : Fin n,
    ∑ c : C,
      |st.basis.repr (Submodule.Quotient.mk (Pi.single a 1)) (Sum.inl c)| ≤ M

theorem coreBound_nonneg (st : CompressionState S P C V) {M : ℤ}
    (hM : st.CoreBound M) : 0 ≤ M := by
  classical
  let a : Fin n := ⟨0, lt_of_lt_of_le (by norm_num) S.two_le⟩
  exact le_trans (Finset.sum_nonneg fun _ _ => abs_nonneg _) (hM a)


theorem core_norm_uvec_le (st : CompressionState S P C V) {M : ℤ}
    (hM : st.CoreBound M) (t : Sym2 (Fin n)) :
    ∑ c : C,
        |st.basis.repr (Submodule.Quotient.mk (uvec t)) (Sum.inl c)| ≤ 2 * M := by
  classical
  induction t using Sym2.inductionOn with
  | hf a b =>
      rw [uvec_mk, Submodule.Quotient.mk_add]
      calc
        ∑ c : C,
            |(st.basis.repr
                (Submodule.Quotient.mk (Pi.single a 1) +
                  Submodule.Quotient.mk (Pi.single b 1))) (Sum.inl c)|
            ≤ ∑ c : C,
                (|st.basis.repr (Submodule.Quotient.mk (Pi.single a 1)) (Sum.inl c)| +
                 |st.basis.repr (Submodule.Quotient.mk (Pi.single b 1)) (Sum.inl c)|) := by
              apply Finset.sum_le_sum
              intro c hc
              rw [map_add, Finsupp.add_apply]
              exact abs_add_le _ _
        _ = (∑ c : C,
                |st.basis.repr (Submodule.Quotient.mk (Pi.single a 1)) (Sum.inl c)|) +
              ∑ c : C,
                |st.basis.repr (Submodule.Quotient.mk (Pi.single b 1)) (Sum.inl c)| := by
              rw [Finset.sum_add_distrib]
        _ ≤ M + M := add_le_add (hM a) (hM b)
        _ = 2 * M := by ring


theorem projectedRow_core_norm_le (st : CompressionState S P C V) {M : ℤ}
    (hM : st.CoreBound M) (t : Sym2 (Fin n)) :
    ∑ c : C, |st.projectedRow t (Sum.inl c)| ≤ 4 * M := by
  classical
  change ∑ c : C,
      |st.basis.repr (Submodule.Quotient.mk (S.rho P t)) (Sum.inl c)| ≤ _
  rw [MinimalNUS.rho, Submodule.Quotient.mk_sub]
  calc
    ∑ c : C,
        |(st.basis.repr
            (Submodule.Quotient.mk (uvec t) -
              Submodule.Quotient.mk (uvec (P.μ t)))) (Sum.inl c)|
        ≤ ∑ c : C,
            (|st.basis.repr (Submodule.Quotient.mk (uvec t)) (Sum.inl c)| +
             |st.basis.repr (Submodule.Quotient.mk (uvec (P.μ t))) (Sum.inl c)|) := by
          apply Finset.sum_le_sum
          intro c hc
          rw [map_sub, Finsupp.sub_apply]
          exact abs_sub _ _
    _ = (∑ c : C, |st.basis.repr (Submodule.Quotient.mk (uvec t)) (Sum.inl c)|) +
          ∑ c : C, |st.basis.repr (Submodule.Quotient.mk (uvec (P.μ t))) (Sum.inl c)| := by
          rw [Finset.sum_add_distrib]
    _ ≤ 2 * M + 2 * M := add_le_add (st.core_norm_uvec_le hM t)
      (st.core_norm_uvec_le hM (P.μ t))
    _ = 4 * M := by ring

theorem live_coord_uvec (st : CompressionState S P C V) (t : Sym2 (Fin n)) (v : V) :
    st.basis.repr (Submodule.Quotient.mk (uvec t)) (Sum.inr v) =
      ((liveLabels st.blocks t).count v : ℤ) := by
  induction t using Sym2.inductionOn with
  | hf a b =>
      rw [uvec_mk]
      rw [Submodule.Quotient.mk_add, map_add, Finsupp.add_apply]
      simp only [liveLabels_mk]
      rcases ha : st.blocks.owner a with _ | x <;>
        rcases hb : st.blocks.owner b with _ | y
      all_goals
        rw [st.live_coord a v, st.live_coord b v]
        simp [ha, hb, Multiset.count_cons,
          Multiset.count_singleton, eq_comm, add_comm]


theorem live_norm_uvec_le (st : CompressionState S P C V) (t : Sym2 (Fin n)) :
    ∑ v : V, |st.basis.repr (Submodule.Quotient.mk (uvec t)) (Sum.inr v)| ≤ 2 := by
  classical
  simp_rw [st.live_coord_uvec]
  have hsum : ∑ v : V, (liveLabels st.blocks t).count v =
      (liveLabels st.blocks t).card := by
    exact Multiset.sum_count_eq_card (by simp)
  have hcard := liveLabels_card_le_two st.blocks t
  have habs : ∀ v : V, |((liveLabels st.blocks t).count v : ℤ)| =
      ((liveLabels st.blocks t).count v : ℤ) := by
    intro v
    exact abs_of_nonneg (by positivity)
  simp_rw [habs]
  exact_mod_cast hsum.symm ▸ hcard


theorem projectedRow_live_norm_le (st : CompressionState S P C V)
    (t : Sym2 (Fin n)) :
    ∑ v : V, |st.projectedRow t (Sum.inr v)| ≤ 4 := by
  classical
  change ∑ v : V,
      |st.basis.repr (Submodule.Quotient.mk (S.rho P t)) (Sum.inr v)| ≤ 4
  rw [MinimalNUS.rho, Submodule.Quotient.mk_sub]
  calc
    ∑ v : V,
        |(st.basis.repr
          (Submodule.Quotient.mk (uvec t) - Submodule.Quotient.mk (uvec (P.μ t))))
            (Sum.inr v)|
      ≤ ∑ v : V,
          (|st.basis.repr (Submodule.Quotient.mk (uvec t)) (Sum.inr v)| +
           |st.basis.repr (Submodule.Quotient.mk (uvec (P.μ t))) (Sum.inr v)|) := by
        apply Finset.sum_le_sum
        intro v hv
        rw [map_sub, Finsupp.sub_apply]
        exact abs_sub _ _
    _ = (∑ v : V,
          |st.basis.repr (Submodule.Quotient.mk (uvec t)) (Sum.inr v)|) +
        ∑ v : V,
          |st.basis.repr (Submodule.Quotient.mk (uvec (P.μ t))) (Sum.inr v)| := by
        rw [Finset.sum_add_distrib]
    _ ≤ 2 + 2 := add_le_add (st.live_norm_uvec_le t) (st.live_norm_uvec_le (P.μ t))
    _ = 4 := by norm_num

theorem projectedRow_live (st : CompressionState S P C V) {i j : V}
    (_hij : i ≠ j) {t : Sym2 (Fin n)}
    (ht : t ∈ MinimalNUS.rectangle (st.blocks.block i) (st.blocks.block j)) :
    (fun v => st.projectedRow t (Sum.inr v)) =
      departingLive i j (liveLabels st.blocks (P.μ t)) := by
  have hsrc := liveLabels_source_pair st.blocks ht
  ext v
  change st.basis.repr (Submodule.Quotient.mk (S.rho P t)) (Sum.inr v) = _
  rw [show Submodule.Quotient.mk (S.rho P t) =
      Submodule.Quotient.mk (uvec t) - Submodule.Quotient.mk (uvec (P.μ t)) by
        rw [MinimalNUS.rho, Submodule.Quotient.mk_sub]]
  rw [map_sub, Finsupp.sub_apply, st.live_coord_uvec, st.live_coord_uvec]
  rw [hsrc, count_pair_apply]
  rfl

end CompressionState

def initialLiveBlocks (n : ℕ) : LiveBlocks n (Fin n) where
  block i := {i}
  owner a := some a
  mem_block_iff a i := by simp
  nonempty i := ⟨i, by simp⟩


noncomputable def initialCompressionState {p n : ℕ} (S : MinimalNUS p n)
    (P : S.Pairing) : CompressionState S P Empty (Fin n) := by
  let e : (Fin n → ℤ) ≃ₗ[ℤ] ((Fin n → ℤ) ⧸ (⊥ : Submodule ℤ (Fin n → ℤ))) :=
    LinearEquiv.ofBijective (⊥ : Submodule ℤ (Fin n → ℤ)).mkQ
      ⟨by rw [← LinearMap.ker_eq_bot, Submodule.ker_mkQ], Submodule.mkQ_surjective _⟩
  let b₀ : Module.Basis (Fin n) ℤ ((Fin n → ℤ) ⧸ (⊥ : Submodule ℤ (Fin n → ℤ))) :=
    (Pi.basisFun ℤ (Fin n)).map e
  let b : Module.Basis (Sum Empty (Fin n)) ℤ
      ((Fin n → ℤ) ⧸ (⊥ : Submodule ℤ (Fin n → ℤ))) :=
    b₀.reindex (Equiv.emptySum Empty (Fin n)).symm
  refine
    { Q := ⊥
      le_colLat := bot_le
      primitive := ?_
      basis := b
      blocks := initialLiveBlocks n
      live_coord := ?_ }
  · intro v c hc hcv
    simpa only [Submodule.mem_bot] using (smul_eq_zero.mp hcv).resolve_left hc
  · intro a v
    have he : e.symm (Submodule.Quotient.mk (Pi.single a 1)) = Pi.single a 1 := by
      rw [e.symm_apply_eq]
      rfl
    simp only [b, Module.Basis.repr_reindex_apply,
      b₀, Module.Basis.map_repr, LinearEquiv.trans_apply, Pi.basisFun_repr, he,
      initialLiveBlocks]
    simp [Pi.single_apply, eq_comm]

theorem initialCompressionState_coreBound {p n : ℕ} (S : MinimalNUS p n)
    (P : S.Pairing) : (initialCompressionState S P).CoreBound 0 := by
  intro a
  simp




def promoteOwner {V : Type*} [DecidableEq V] (T : Finset V) :
    Option V → Option {v : V // v ∉ T}
  | none => none
  | some v => if hv : v ∈ T then none else some ⟨v, hv⟩

@[simp] theorem promoteOwner_eq_some_iff {V : Type*} [DecidableEq V]
    (T : Finset V) (o : Option V) (v : {v : V // v ∉ T}) :
    promoteOwner T o = some v ↔ o = some v.1 := by
  rcases o with _ | w
  · simp [promoteOwner]
  · by_cases hw : w ∈ T
    · have hwv : w ≠ v.1 := by
        intro h
        subst w
        exact v.2 hw
      simp [promoteOwner, hw, hwv]
    · simp [promoteOwner, hw, Subtype.ext_iff]


def LiveBlocks.promote {n : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (B : LiveBlocks n V) (T : Finset V) : LiveBlocks n {v : V // v ∉ T} where
  block v := B.block v.1
  owner a := promoteOwner T (B.owner a)
  mem_block_iff a v := by
    rw [B.mem_block_iff, promoteOwner_eq_some_iff]
  nonempty v := B.nonempty v.1

theorem LiveBlocks.promote_heavy_is_light {n : ℕ} {V : Type*}
    [Fintype V] [DecidableEq V] (B : LiveBlocks n V) (L : ℕ)
    (v : {v : V // v ∉ B.heavy L}) : ((B.promote (B.heavy L)).block v).card < L := by
  have hv : ¬L ≤ (B.block v.1).card := by
    simpa only [LiveBlocks.heavy, Finset.mem_filter, Finset.mem_univ, true_and] using v.2
  simpa [LiveBlocks.promote] using (Nat.lt_of_not_ge hv)

theorem LiveBlocks.heavy_card_mul_le_removed {n : ℕ} {V : Type*}
    [Fintype V] [DecidableEq V] (B : LiveBlocks n V) (L : ℕ) :
    L * (B.heavy L).card ≤ ∑ v ∈ B.heavy L, (B.block v).card := by
  classical
  calc
    L * (B.heavy L).card = ∑ v ∈ B.heavy L, L := by simp [mul_comm]
    _ ≤ ∑ v ∈ B.heavy L, (B.block v).card := by
      apply Finset.sum_le_sum
      intro v hv
      simpa only [LiveBlocks.heavy, Finset.mem_filter, Finset.mem_univ, true_and]
        using hv

theorem LiveBlocks.mass_promote_add_removed {n : ℕ} {V : Type*}
    [Fintype V] [DecidableEq V] (B : LiveBlocks n V) (T : Finset V) :
    (B.promote T).mass + ∑ v ∈ T, (B.block v).card = B.mass := by
  classical
  let U := Finset.univ.filter fun v : V => v ∉ T
  have hnewdisj : (↑(Finset.univ : Finset {v : V // v ∉ T}) :
      Set {v : V // v ∉ T}).PairwiseDisjoint (B.promote T).block := by
    intro i hi j hj hij
    exact (B.promote T).disjoint hij
  have hUdisj : (↑U : Set V).PairwiseDisjoint B.block := by
    intro i hi j hj hij
    exact B.disjoint hij
  have hunion : Finset.univ.biUnion (B.promote T).block = U.biUnion B.block := by
    ext a
    constructor
    · intro ha
      obtain ⟨v, hv, hav⟩ := Finset.mem_biUnion.mp ha
      apply Finset.mem_biUnion.mpr
      exact ⟨v.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, v.2⟩, hav⟩
    · intro ha
      obtain ⟨v, hv, hav⟩ := Finset.mem_biUnion.mp ha
      have hvT := (Finset.mem_filter.mp hv).2
      apply Finset.mem_biUnion.mpr
      exact ⟨⟨v, hvT⟩, Finset.mem_univ _, hav⟩
  have hmass : (B.promote T).mass = ∑ v ∈ U, (B.block v).card := by
    calc
      (B.promote T).mass =
          (Finset.univ.biUnion (B.promote T).block).card :=
        (Finset.card_biUnion hnewdisj).symm
      _ = (U.biUnion B.block).card := congrArg Finset.card hunion
      _ = ∑ v ∈ U, (B.block v).card := Finset.card_biUnion hUdisj
  rw [hmass]
  have hpart := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun v : V => v ∈ T) (fun v => (B.block v).card)
  have hT : Finset.univ.filter (fun v : V => v ∈ T) = T := by ext v; simp
  have hU : Finset.univ.filter (fun v : V => ¬v ∈ T) = U := by ext v; simp [U]
  rw [hT, hU] at hpart
  simpa [LiveBlocks.mass, add_comm] using hpart


def promoteIndexEquiv {C V : Type*} [DecidableEq V] (T : Finset V) :
    Sum (Sum C {v : V // v ∈ T}) {v : V // v ∉ T} ≃ Sum C V where
  toFun
    | Sum.inl (Sum.inl c) => Sum.inl c
    | Sum.inl (Sum.inr v) => Sum.inr v.1
    | Sum.inr v => Sum.inr v.1
  invFun
    | Sum.inl c => Sum.inl (Sum.inl c)
    | Sum.inr v => if hv : v ∈ T then Sum.inl (Sum.inr ⟨v, hv⟩) else Sum.inr ⟨v, hv⟩
  left_inv x := by
    rcases x with (c | v) | v
    · rfl
    · simp [v.2]
    · simp [v.2]
  right_inv x := by
    rcases x with c | v
    · rfl
    · by_cases hv : v ∈ T <;> simp [hv]


noncomputable def CompressionState.promote {p n : ℕ} {S : MinimalNUS p n}
    {P : S.Pairing} {C V : Type*} [Fintype C] [DecidableEq C]
    [Fintype V] [DecidableEq V] (st : CompressionState S P C V) (T : Finset V) :
    CompressionState S P (Sum C {v : V // v ∈ T}) {v : V // v ∉ T} where
  Q := st.Q
  le_colLat := st.le_colLat
  primitive := st.primitive
  basis := st.basis.reindex (promoteIndexEquiv T).symm
  blocks := st.blocks.promote T
  live_coord a v := by
    rw [Module.Basis.repr_reindex_apply]
    change st.basis.repr (Submodule.Quotient.mk (Pi.single a 1)) (Sum.inr (v : V)) = _
    rw [st.live_coord]
    have hp : (st.blocks.promote T).owner a = some v ↔
        st.blocks.owner a = some v.1 := promoteOwner_eq_some_iff T _ v
    by_cases h : st.blocks.owner a = some v.1
    · simp [h, hp.mpr h]
    · have h' : (st.blocks.promote T).owner a ≠ some v := fun h' => h (hp.mp h')
      simp [h, h']

@[simp] theorem CompressionState.promote_old_core_coord {p n : ℕ}
    {S : MinimalNUS p n} {P : S.Pairing} {C V : Type*}
    [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]
    (st : CompressionState S P C V) (T : Finset V) (a : Fin n) (c : C) :
    (st.promote T).basis.repr (Submodule.Quotient.mk (Pi.single a 1))
        (Sum.inl (Sum.inl c)) =
      st.basis.repr (Submodule.Quotient.mk (Pi.single a 1)) (Sum.inl c) := by
  rw [CompressionState.promote, Module.Basis.repr_reindex_apply]
  rfl

@[simp] theorem CompressionState.promote_new_core_coord {p n : ℕ}
    {S : MinimalNUS p n} {P : S.Pairing} {C V : Type*}
    [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]
    (st : CompressionState S P C V) (T : Finset V) (a : Fin n) (v : {v : V // v ∈ T}) :
    (st.promote T).basis.repr (Submodule.Quotient.mk (Pi.single a 1))
        (Sum.inl (Sum.inr v)) =
      if st.blocks.owner a = some v.1 then 1 else 0 := by
  rw [CompressionState.promote, Module.Basis.repr_reindex_apply]
  change st.basis.repr (Submodule.Quotient.mk (Pi.single a 1)) (Sum.inr (v : V)) = _
  exact st.live_coord a v.1


@[simp] theorem CompressionState.promote_old_core_coord_row {p n : ℕ}
    {S : MinimalNUS p n} {P : S.Pairing} {C V : Type*}
    [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]
    (st : CompressionState S P C V) (T : Finset V) (r : Fin n → ℤ) (c : C) :
    (st.promote T).basis.repr (Submodule.Quotient.mk r)
        (Sum.inl (Sum.inl c)) =
      st.basis.repr (Submodule.Quotient.mk r) (Sum.inl c) := by
  rw [CompressionState.promote, Module.Basis.repr_reindex_apply]
  rfl

@[simp] theorem CompressionState.promote_new_core_coord_row {p n : ℕ}
    {S : MinimalNUS p n} {P : S.Pairing} {C V : Type*}
    [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]
    (st : CompressionState S P C V) (T : Finset V) (r : Fin n → ℤ)
    (v : {v : V // v ∈ T}) :
    (st.promote T).basis.repr (Submodule.Quotient.mk r)
        (Sum.inl (Sum.inr v)) =
      st.basis.repr (Submodule.Quotient.mk r) (Sum.inr v.1) := by
  rw [CompressionState.promote, Module.Basis.repr_reindex_apply]
  rfl

@[simp] theorem CompressionState.promote_live_coord_row {p n : ℕ}
    {S : MinimalNUS p n} {P : S.Pairing} {C V : Type*}
    [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]
    (st : CompressionState S P C V) (T : Finset V) (r : Fin n → ℤ)
    (v : {v : V // v ∉ T}) :
    (st.promote T).basis.repr (Submodule.Quotient.mk r) (Sum.inr v) =
      st.basis.repr (Submodule.Quotient.mk r) (Sum.inr v.1) := by
  rw [CompressionState.promote, Module.Basis.repr_reindex_apply]
  rfl


theorem CompressionState.promote_core_norm_row {p n : ℕ}
    {S : MinimalNUS p n} {P : S.Pairing} {C V : Type*}
    [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]
    (st : CompressionState S P C V) (T : Finset V) (r : Fin n → ℤ) :
    (∑ c : Sum C {v : V // v ∈ T},
        |(st.promote T).basis.repr (Submodule.Quotient.mk r) (Sum.inl c)|) =
      (∑ c : C, |st.basis.repr (Submodule.Quotient.mk r) (Sum.inl c)|) +
        ∑ v : {v : V // v ∈ T},
          |st.basis.repr (Submodule.Quotient.mk r) (Sum.inr v.1)| := by
  rw [Fintype.sum_sum_type]
  simp


theorem CompressionState.promote_projectedRow_core_norm_le {p n : ℕ}
    {S : MinimalNUS p n} {P : S.Pairing} {C V : Type*}
    [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]
    (st : CompressionState S P C V) (T : Finset V) {M : ℤ}
    (hM : st.CoreBound M) (t : Sym2 (Fin n)) :
    ∑ c : Sum C {v : V // v ∈ T},
        |(st.promote T).basis.repr (Submodule.Quotient.mk (S.rho P t))
          (Sum.inl c)| ≤ 4 * M + 4 := by
  rw [st.promote_core_norm_row T (S.rho P t)]
  apply add_le_add (st.projectedRow_core_norm_le hM t)
  calc
    ∑ v : {v : V // v ∈ T},
        |st.basis.repr (Submodule.Quotient.mk (S.rho P t)) (Sum.inr v.1)|
      ≤ ∑ v : V,
          |st.basis.repr (Submodule.Quotient.mk (S.rho P t)) (Sum.inr v)| := by
        calc
          _ = ∑ v ∈ T,
              |st.basis.repr (Submodule.Quotient.mk (S.rho P t)) (Sum.inr v)| := by
                rw [← Finset.attach_eq_univ]
                exact Finset.sum_attach T (fun v =>
                  |st.basis.repr (Submodule.Quotient.mk (S.rho P t)) (Sum.inr v)|)
          _ ≤ ∑ v ∈ (Finset.univ : Finset V),
              |st.basis.repr (Submodule.Quotient.mk (S.rho P t)) (Sum.inr v)| := by
                exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T)
                  (fun v hv hnot => abs_nonneg _)
          _ = _ := by simp
    _ ≤ 4 := st.projectedRow_live_norm_le t


theorem CompressionState.promote_projectedRow_core_norm_le_eight_mul {p n : ℕ}
    {S : MinimalNUS p n} {P : S.Pairing} {C V : Type*}
    [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]
    (st : CompressionState S P C V) (T : Finset V) {M : ℤ}
    (hM : st.CoreBound M) (hM1 : 1 ≤ M) (t : Sym2 (Fin n)) :
    ∑ c : Sum C {v : V // v ∈ T},
        |(st.promote T).basis.repr (Submodule.Quotient.mk (S.rho P t))
          (Sum.inl c)| ≤ 8 * M := by
  refine le_trans (st.promote_projectedRow_core_norm_le T hM t) ?_
  linarith


theorem CompressionState.promote_coreBound {p n : ℕ} {S : MinimalNUS p n}
    {P : S.Pairing} {C V : Type*} [Fintype C] [DecidableEq C]
    [Fintype V] [DecidableEq V] (st : CompressionState S P C V) (T : Finset V)
    {M : ℤ} (hM : st.CoreBound M) : (st.promote T).CoreBound (M + 1) := by
  classical
  intro a
  rw [Fintype.sum_sum_type]
  simp_rw [st.promote_old_core_coord, st.promote_new_core_coord]
  have hnew : (∑ v : {v : V // v ∈ T},
      |if st.blocks.owner a = some v.1 then (1 : ℤ) else 0|) ≤ 1 := by
    rcases h : st.blocks.owner a with _ | w
    · simp
    · by_cases hw : w ∈ T
      · let wT : {v : V // v ∈ T} := ⟨w, hw⟩
        rw [Finset.sum_eq_single wT]
        · simp [wT]
        · intro v hv hvw
          have hvw' : v.1 ≠ w := by
            intro he
            apply hvw
            exact Subtype.ext he
          simp [hvw'.symm]
        · simp
      · have hne : ∀ v : {v : V // v ∈ T}, w ≠ v.1 := by
          intro v he
          subst w
          exact (hw v.2).elim
        simp [hne]
  exact add_le_add (hM a) hnew




def unitElim {C V : Type*} [DecidableEq V] (v : V) (y : Sum C V → ℤ) :
    (Sum C V → ℤ) →ₗ[ℤ] (Sum C {u : V // u ≠ v} → ℤ) where
  toFun z
    | Sum.inl c => z (Sum.inl c) - z (Sum.inr v) * y (Sum.inl c)
    | Sum.inr u => z (Sum.inr u.1) - z (Sum.inr v) * y (Sum.inr u.1)
  map_add' z z' := by
    funext i
    rcases i with c | u <;> simp <;> ring
  map_smul' k z := by
    funext i
    rcases i with c | u <;> simp <;> ring

@[simp] theorem unitElim_apply_left {C V : Type*} [DecidableEq V]
    (v : V) (y z : Sum C V → ℤ) (c : C) :
    unitElim v y z (Sum.inl c) =
      z (Sum.inl c) - z (Sum.inr v) * y (Sum.inl c) := rfl

@[simp] theorem unitElim_apply_right {C V : Type*} [DecidableEq V]
    (v : V) (y z : Sum C V → ℤ) (u : {u : V // u ≠ v}) :
    unitElim v y z (Sum.inr u) =
      z (Sum.inr u.1) - z (Sum.inr v) * y (Sum.inr u.1) := rfl


theorem ker_primitive {M ι : Type*} [AddCommGroup M] [Module ℤ M]
    (f : M →ₗ[ℤ] (ι → ℤ)) :
    ∀ (x : M) (c : ℤ), c ≠ 0 → c • x ∈ LinearMap.ker f → x ∈ LinearMap.ker f := by
  intro x c hc hcx
  rw [LinearMap.mem_ker] at hcx ⊢
  funext i
  have h := congrFun hcx i
  rw [map_zsmul, Pi.smul_apply, smul_eq_mul] at h
  exact (mul_eq_zero.mp h).resolve_left hc


def contractOwner {V : Type*} [DecidableEq V] (v : V)
    (parent : Option {u : V // u ≠ v}) : Option V → Option {u : V // u ≠ v}
  | none => none
  | some u => if h : u = v then parent else some ⟨u, h⟩

@[simp] theorem contractOwner_eq_some_iff {V : Type*} [DecidableEq V] (v : V)
    (parent : Option {u : V // u ≠ v}) (o : Option V) (u : {u : V // u ≠ v}) :
    contractOwner v parent o = some u ↔
      o = some u.1 ∨ (o = some v ∧ parent = some u) := by
  rcases o with _ | w
  · simp [contractOwner]
  · by_cases hwv : w = v
    · subst w
      have hvu : v ≠ u.1 := Ne.symm u.2
      simp [contractOwner, hvu]
    · simp [contractOwner, hwv, Subtype.ext_iff]

def LiveBlocks.contract {n : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (B : LiveBlocks n V) (v : V) (parent : Option {u : V // u ≠ v}) :
    LiveBlocks n {u : V // u ≠ v} where
  block u := if parent = some u then B.block u.1 ∪ B.block v else B.block u.1
  owner a := contractOwner v parent (B.owner a)
  mem_block_iff a u := by
    rw [contractOwner_eq_some_iff]
    by_cases hp : parent = some u
    · simp only [hp, if_pos, Finset.mem_union]
      rw [B.mem_block_iff, B.mem_block_iff]
      simp [and_comm]
    · simp only [if_neg hp]
      rw [B.mem_block_iff]
      constructor
      · exact Or.inl
      · rintro (h | ⟨-, hpu⟩)
        · exact h
        · exact absurd hpu hp
  nonempty u := by
    obtain ⟨a, ha⟩ := B.nonempty u.1
    refine ⟨a, ?_⟩
    by_cases hp : parent = some u
    · simp [hp, ha]
    · simp [hp, ha]


theorem exists_easy_configuration_family {V : Type*} [Fintype V] [DecidableEq V]
    (i : V) (E : Finset V) (hi : i ∉ E) (hE : 2 ≤ E.card) :
    ∃ F : Finset (Configuration V),
      F.card = E.card ∧
      Set.InjOn Configuration.j (F : Set (Configuration V)) ∧
      Set.InjOn Configuration.τ (F : Set (Configuration V)) ∧
      ∀ (T : Finset V) (c : Configuration V), c ∈ F → Hits T c →
        ∃ j ∈ T, j ∈ E := by
  classical
  have hcard : 2 ≤ Fintype.card (↥E) := by simpa using hE
  obtain ⟨π, hπ⟩ := exists_derangement (↥E) hcard
  let cf : ↥E → Configuration V := fun j =>
    { j := j.1
      τ := s(i, (π j).1)
      not_mem := by
        rw [Sym2.mem_iff]
        push Not
        constructor
        · intro hji
          apply hi
          simpa [hji] using j.2
        · intro hjπ
          apply hπ j
          exact Subtype.ext hjπ.symm }
  have hcf : Function.Injective cf := by
    intro j k hjk
    apply Subtype.ext
    exact congrArg Configuration.j hjk
  let F : Finset (Configuration V) := Finset.univ.map ⟨cf, hcf⟩
  refine ⟨F, ?_, ?_, ?_, ?_⟩
  · simp [F]
  · intro c hc d hd hcd
    obtain ⟨j, -, rfl⟩ := Finset.mem_map.mp hc
    obtain ⟨k, -, rfl⟩ := Finset.mem_map.mp hd
    apply congrArg cf
    apply Subtype.ext
    exact hcd
  · intro c hc d hd hcd
    obtain ⟨j, -, rfl⟩ := Finset.mem_map.mp hc
    obtain ⟨k, -, rfl⟩ := Finset.mem_map.mp hd
    have ht : s(i, (π j).1) = s(i, (π k).1) := hcd
    rcases Sym2.eq_iff.mp ht with h | h
    · apply congrArg cf
      exact π.injective (Subtype.ext h.2)
    · exact absurd h.1 (by
        intro hik
        apply hi
        rw [hik]
        exact (π k).2)
  · intro T c hc hhit
    obtain ⟨j, -, rfl⟩ := Finset.mem_map.mp hc
    exact ⟨j.1, hhit.1, j.2⟩


theorem mem_equivMultiset_iff {V : Type*} (u : V) (z : Sym2 V) :
    u ∈ ((Sym2.equivMultiset V) z : Multiset V) ↔ u ∈ z := by
  induction z using Sym2.inductionOn with
  | hf a b =>
      change u ∈ ({a, b} : Multiset V) ↔ u ∈ s(a, b)
      simp [Sym2.mem_iff]

noncomputable def properConfiguration {V : Type*} [DecidableEq V]
    (j : V) (ν : Multiset V) (hj : j ∉ ν) (hν : ν.card = 2) : Configuration V where
  j := j
  τ := (Sym2.equivMultiset V).symm ⟨ν, hν⟩
  not_mem := by
    intro h
    apply hj
    have hm : ((Sym2.equivMultiset V)
        ((Sym2.equivMultiset V).symm ⟨ν, hν⟩) : Multiset V) = ν := congrArg Subtype.val
      ((Sym2.equivMultiset V).apply_symm_apply ⟨ν, hν⟩)
    have h' : j ∈ ((Sym2.equivMultiset V)
        ((Sym2.equivMultiset V).symm ⟨ν, hν⟩) : Multiset V) :=
      (mem_equivMultiset_iff j _).mpr h
    rwa [hm] at h'

@[simp] theorem properConfiguration_j {V : Type*} [DecidableEq V]
    (j : V) (ν : Multiset V) (hj : j ∉ ν) (hν : ν.card = 2) :
    (properConfiguration j ν hj hν).j = j := rfl

theorem properConfiguration_multiset {V : Type*} [DecidableEq V]
    (j : V) (ν : Multiset V) (hj : j ∉ ν) (hν : ν.card = 2) :
    (Sym2.equivMultiset V) (properConfiguration j ν hj hν).τ = ⟨ν, hν⟩ := by
  exact (Sym2.equivMultiset V).apply_symm_apply _


abbrev OrderedDistinct (V : Type*) := {ij : V × V // ij.1 ≠ ij.2}


structure DepartingSystem {p n : ℕ} {S : MinimalNUS p n} (P : S.Pairing)
    {V : Type*} [Fintype V] [DecidableEq V] (B : LiveBlocks n V) where
  t : OrderedDistinct V → Sym2 (Fin n)
  mem_rectangle : ∀ e,
    t e ∈ MinimalNUS.rectangle (B.block e.1.1) (B.block e.1.2)
  leaves_rectangle : ∀ e,
    P.μ (t e) ∉ MinimalNUS.rectangle (B.block e.1.1) (B.block e.1.2)


theorem light_blocks_power_lt {n p : ℕ} {V : Type*}
    [Fintype V] [DecidableEq V] (B : LiveBlocks n V) (hp : 64 ≤ p)
    (hlight : ∀ v, (B.block v).card < Nat.log 2 p / 3) :
    ∀ e : OrderedDistinct V,
      2 ^ ((B.block e.1.1).card + (B.block e.1.2).card - 2) < p := by
  intro e
  let ell := Nat.log 2 p
  have hell : 6 ≤ ell := by
    have hmono := Nat.log_mono_right (b := 2) hp
    norm_num at hmono ⊢
    exact hmono
  have hexp : (B.block e.1.1).card + (B.block e.1.2).card - 2 < ell := by
    have h1 := hlight e.1.1
    have h2 := hlight e.1.2
    dsimp [ell] at h1 h2 ⊢
    omega
  have hpow : 2 ^ ((B.block e.1.1).card + (B.block e.1.2).card - 2) <
      2 ^ ell := Nat.pow_lt_pow_right (by norm_num) hexp
  exact hpow.trans_le (Nat.pow_log_le_self 2 (by omega))


theorem exists_departingSystem {p n : ℕ} [Fact p.Prime]
    (S : MinimalNUS p n) (P : S.Pairing)
    {V : Type*} [Fintype V] [DecidableEq V] (B : LiveBlocks n V)
    (hlight : ∀ e : OrderedDistinct V,
      2 ^ ((B.block e.1.1).card + (B.block e.1.2).card - 2) < p) :
    Nonempty (DepartingSystem P B) := by
  have hex : ∀ e : OrderedDistinct V,
      ∃ t ∈ MinimalNUS.rectangle (B.block e.1.1) (B.block e.1.2),
        P.μ t ∉ MinimalNUS.rectangle (B.block e.1.1) (B.block e.1.2) := by
    intro e
    apply exists_departing_pair S P
    · exact B.nonempty e.1.1
    · exact B.nonempty e.1.2
    · exact B.disjoint e.2
    · exact hlight e
  choose t ht hout using hex
  exact ⟨⟨t, ht, hout⟩⟩

namespace DepartingSystem

variable {p n : ℕ} {S : MinimalNUS p n} {P : S.Pairing}
variable {C V : Type*} [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]
variable {B : LiveBlocks n V}

def row (D : DepartingSystem P B) (e : OrderedDistinct V) : Fin n → ℤ :=
  S.rho P (D.t e)

def liveType (D : DepartingSystem P B) (e : OrderedDistinct V) : Multiset V :=
  liveLabels B (P.μ (D.t e))

theorem row_mem_colLat (D : DepartingSystem P B) (e : OrderedDistinct V) :
    D.row e ∈ S.colLat P :=
  Submodule.subset_span ⟨D.t e, rfl⟩

theorem row_unit_of_mem_right (st : CompressionState S P C V)
    (D : DepartingSystem P st.blocks) (e : OrderedDistinct V)
    (hmem : e.1.2 ∈ D.liveType e) :
    IsUnitRelation (fun v => st.basis.repr
      (Submodule.Quotient.mk (D.row e)) (Sum.inr v)) := by
  change IsUnitRelation (fun v => st.projectedRow (D.t e) (Sum.inr v))
  rw [st.projectedRow_live e.2 (D.mem_rectangle e)]
  exact departingLive_unit_of_mem_right e.1.1 e.1.2 (D.liveType e)
    (liveLabels_card_le_two st.blocks _) hmem
    (liveLabels_departing_ne st.blocks e.2 (D.leaves_rectangle e))

theorem row_unit_of_mem_left (st : CompressionState S P C V)
    (D : DepartingSystem P st.blocks) (e : OrderedDistinct V)
    (hmem : e.1.1 ∈ D.liveType e) :
    IsUnitRelation (fun v => st.basis.repr
      (Submodule.Quotient.mk (D.row e)) (Sum.inr v)) := by
  change IsUnitRelation (fun v => st.projectedRow (D.t e) (Sum.inr v))
  rw [st.projectedRow_live e.2 (D.mem_rectangle e)]
  exact departingLive_unit_of_mem_left e.1.1 e.1.2 (D.liveType e)
    (liveLabels_card_le_two st.blocks _) hmem
    (liveLabels_departing_ne st.blocks e.2 (D.leaves_rectangle e))

theorem row_core_norm_le (st : CompressionState S P C V) {M : ℤ}
    (hM : st.CoreBound M) (D : DepartingSystem P st.blocks) (e : OrderedDistinct V) :
    ∑ c : C, |st.basis.repr (Submodule.Quotient.mk (D.row e)) (Sum.inl c)| ≤
      4 * M :=
  st.projectedRow_core_norm_le hM (D.t e)

theorem row_sub_mem_colLat (D : DepartingSystem P B)
    (e e' : OrderedDistinct V) :
    D.row e - D.row e' ∈ S.colLat P :=
  (S.colLat P).sub_mem (D.row_mem_colLat e) (D.row_mem_colLat e')


theorem row_sub_live_eq (st : CompressionState S P C V)
    (D : DepartingSystem P st.blocks) (e e' : OrderedDistinct V)
    (hanchor : e.1.1 = e'.1.1) (htype : D.liveType e = D.liveType e') :
    (fun v => st.basis.repr
      (Submodule.Quotient.mk (D.row e - D.row e')) (Sum.inr v)) =
      Pi.single e.1.2 1 - Pi.single e'.1.2 1 := by
  have he := st.projectedRow_live e.2 (D.mem_rectangle e)
  have he' := st.projectedRow_live e'.2 (D.mem_rectangle e')
  rw [Submodule.Quotient.mk_sub, map_sub]
  ext v
  simp only [Finsupp.sub_apply]
  change st.projectedRow (D.t e) (Sum.inr v) -
      st.projectedRow (D.t e') (Sum.inr v) = _
  rw [congrFun he v, congrFun he' v]
  change liveLabels st.blocks (P.μ (D.t e)) =
    liveLabels st.blocks (P.μ (D.t e')) at htype
  rw [hanchor, htype]
  exact congrFun (departingLive_sub_same_type e'.1.1 e.1.2 e'.1.2
    (D.liveType e')) v


theorem row_sub_core_norm_le (st : CompressionState S P C V) {M : ℤ}
    (hM : st.CoreBound M) (D : DepartingSystem P st.blocks)
    (e e' : OrderedDistinct V) :
    ∑ c : C, |st.basis.repr
      (Submodule.Quotient.mk (D.row e - D.row e')) (Sum.inl c)| ≤ 8 * M := by
  classical
  rw [Submodule.Quotient.mk_sub, map_sub]
  calc
    ∑ c : C, |(st.basis.repr (Submodule.Quotient.mk (D.row e)) -
        st.basis.repr (Submodule.Quotient.mk (D.row e'))) (Sum.inl c)|
      ≤ ∑ c : C,
          (|st.basis.repr (Submodule.Quotient.mk (D.row e)) (Sum.inl c)| +
           |st.basis.repr (Submodule.Quotient.mk (D.row e')) (Sum.inl c)|) := by
        apply Finset.sum_le_sum
        intro c hc
        rw [Finsupp.sub_apply]
        exact abs_sub _ _
    _ = (∑ c : C,
          |st.basis.repr (Submodule.Quotient.mk (D.row e)) (Sum.inl c)|) +
        ∑ c : C,
          |st.basis.repr (Submodule.Quotient.mk (D.row e')) (Sum.inl c)| := by
        rw [Finset.sum_add_distrib]
    _ ≤ 4 * M + 4 * M := add_le_add (D.row_core_norm_le st hM e)
      (D.row_core_norm_le st hM e')
    _ = 8 * M := by ring


theorem promoted_row_unit_of_easy (st : CompressionState S P C V)
    (D : DepartingSystem P st.blocks) (e : OrderedDistinct V)
    (heasy : IsEasyDeparture e.1.1 e.1.2 (D.liveType e))
    (T : Finset V) (hiT : e.1.1 ∉ T) (hjT : e.1.2 ∈ T) :
    IsUnitRelation (fun v : {v : V // v ∉ T} =>
      (st.promote T).basis.repr (Submodule.Quotient.mk (D.row e)) (Sum.inr v)) := by
  have hlive := st.projectedRow_live e.2 (D.mem_rectangle e)
  have hu := easy_after_promote_unit heasy T hiT hjT
  rw [show (fun v : {v : V // v ∉ T} =>
      (st.promote T).basis.repr (Submodule.Quotient.mk (D.row e)) (Sum.inr v)) =
      (fun v => departingLive e.1.1 e.1.2 (D.liveType e) v.1) by
    funext v
    rw [st.promote_live_coord_row]
    exact congrFun hlive v.1]
  exact hu


theorem promoted_row_unit_of_proper (st : CompressionState S P C V)
    (D : DepartingSystem P st.blocks) (e : OrderedDistinct V)
    (hproper : IsProperDeparture e.1.1 e.1.2 (D.liveType e))
    (T : Finset V) (hiT : e.1.1 ∉ T) (hjT : e.1.2 ∈ T)
    (hhit : ∃ u ∈ T, u ∈ D.liveType e) :
    IsUnitRelation (fun v : {v : V // v ∉ T} =>
      (st.promote T).basis.repr (Submodule.Quotient.mk (D.row e)) (Sum.inr v)) := by
  have hlive := st.projectedRow_live e.2 (D.mem_rectangle e)
  have hu := proper_after_promote_unit hproper T hiT hjT hhit
  rw [show (fun v : {v : V // v ∉ T} =>
      (st.promote T).basis.repr (Submodule.Quotient.mk (D.row e)) (Sum.inr v)) =
      (fun v => departingLive e.1.1 e.1.2 (D.liveType e) v.1) by
    funext v
    rw [st.promote_live_coord_row]
    exact congrFun hlive v.1]
  exact hu


theorem promoted_row_core_norm_le_eight_mul (st : CompressionState S P C V)
    (D : DepartingSystem P st.blocks) (e : OrderedDistinct V)
    (T : Finset V) {M : ℤ} (hM : st.CoreBound M) (hM1 : 1 ≤ M) :
    ∑ c : Sum C {v : V // v ∈ T},
      |(st.promote T).basis.repr (Submodule.Quotient.mk (D.row e)) (Sum.inl c)|
        ≤ 8 * M := by
  exact st.promote_projectedRow_core_norm_le_eight_mul T hM hM1 (D.t e)


theorem promoted_row_unit_of_mem_right (st : CompressionState S P C V)
    (D : DepartingSystem P st.blocks) (e : OrderedDistinct V)
    (hmem : e.1.2 ∈ D.liveType e) (T : Finset V) (hiT : e.1.1 ∉ T) :
    IsUnitRelation (fun v : {v : V // v ∉ T} =>
      (st.promote T).basis.repr (Submodule.Quotient.mk (D.row e)) (Sum.inr v)) := by
  have hu := D.row_unit_of_mem_right st e hmem
  have hi : st.basis.repr (Submodule.Quotient.mk (D.row e)) (Sum.inr e.1.1) = 1 := by
    change st.projectedRow (D.t e) (Sum.inr e.1.1) = 1
    rw [congrFun (st.projectedRow_live e.2 (D.mem_rectangle e)) e.1.1]
    exact departingLive_anchor_of_mem_right e.1.1 e.1.2 (D.liveType e) e.2
      (liveLabels_card_le_two st.blocks _) hmem
      (liveLabels_departing_ne st.blocks e.2 (D.leaves_rectangle e))
  have hr := unitRelation_restrict_at_one e.1.1 hu hi T hiT
  rw [show (fun v : {v : V // v ∉ T} =>
      (st.promote T).basis.repr (Submodule.Quotient.mk (D.row e)) (Sum.inr v)) =
      (fun v => st.basis.repr (Submodule.Quotient.mk (D.row e)) (Sum.inr v.1)) by
        funext v
        exact st.promote_live_coord_row T (D.row e) v]
  exact hr

end DepartingSystem



abbrev OtherLabel {V : Type*} (i : V) := {j : V // j ≠ i}

def anchorPair {V : Type*} (i : V) (j : OtherLabel i) : OrderedDistinct V :=
  ⟨(i, j.1), Ne.symm j.2⟩

def DepartingSystem.IsDirectAnchor {p n : ℕ} {S : MinimalNUS p n} {P : S.Pairing}
    {V : Type*} [Fintype V] [DecidableEq V] {B : LiveBlocks n V}
    (D : DepartingSystem P B) (i : V) : Prop :=
  ∃ j : OtherLabel i, j.1 ∈ D.liveType (anchorPair i j)

noncomputable def DepartingSystem.easyLabels {p n : ℕ} {S : MinimalNUS p n} {P : S.Pairing}
    {V : Type*} [Fintype V] [DecidableEq V] {B : LiveBlocks n V}
    (D : DepartingSystem P B) (i : V) :
    Finset (OtherLabel i) := by
  classical
  exact Finset.univ.filter fun j =>
    IsEasyDeparture i j.1 (D.liveType (anchorPair i j))

noncomputable def DepartingSystem.properLabels {p n : ℕ} {S : MinimalNUS p n} {P : S.Pairing}
    {V : Type*} [Fintype V] [DecidableEq V] {B : LiveBlocks n V}
    (D : DepartingSystem P B) (i : V) :
    Finset (OtherLabel i) := by
  classical
  exact Finset.univ.filter fun j =>
    IsProperDeparture i j.1 (D.liveType (anchorPair i j))

noncomputable def DepartingSystem.properTypes {p n : ℕ} {S : MinimalNUS p n} {P : S.Pairing}
    {V : Type*} [Fintype V] [DecidableEq V] {B : LiveBlocks n V}
    (D : DepartingSystem P B) (i : V) :
    Finset (Multiset V) := by
  classical
  exact (D.properLabels i).image fun j => D.liveType (anchorPair i j)


theorem DepartingSystem.exists_easy_anchor_family {p n : ℕ}
    {S : MinimalNUS p n} {P : S.Pairing} {V : Type*}
    [Fintype V] [DecidableEq V] {B : LiveBlocks n V}
    (D : DepartingSystem P B) (i : V) (h2 : 2 ≤ (D.easyLabels i).card) :
    ∃ F : Finset (Configuration V),
      F.card = (D.easyLabels i).card ∧
      Set.InjOn Configuration.j (F : Set (Configuration V)) ∧
      Set.InjOn Configuration.τ (F : Set (Configuration V)) ∧
      ∀ (T : Finset V) (c : Configuration V), c ∈ F → Hits T c →
        ∃ j : OtherLabel i, j ∈ D.easyLabels i ∧ j.1 ∈ T := by
  classical
  let E : Finset V := (D.easyLabels i).image Subtype.val
  have hEcard : E.card = (D.easyLabels i).card := by
    apply Finset.card_image_of_injOn
    intro a ha b hb hab
    exact Subtype.ext hab
  have hiE : i ∉ E := by
    intro hi
    obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hi
    exact j.2 hji
  obtain ⟨F, hcard, hjinj, hτinj, hhit⟩ :=
    exists_easy_configuration_family i E hiE (by simpa [hEcard] using h2)
  refine ⟨F, hcard.trans hEcard, hjinj, hτinj, ?_⟩
  intro T c hcF hcHit
  obtain ⟨v, hvT, hvE⟩ := hhit T c hcF hcHit
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hvE
  exact ⟨j, hj, hvT⟩


theorem DepartingSystem.exists_proper_anchor_family {p n : ℕ}
    {S : MinimalNUS p n} {P : S.Pairing} {V : Type*}
    [Fintype V] [DecidableEq V] {B : LiveBlocks n V}
    (D : DepartingSystem P B) (i : V) :
    ∃ F : Finset (Configuration V),
      F.card = (D.properTypes i).card ∧
      Set.InjOn Configuration.j (F : Set (Configuration V)) ∧
      Set.InjOn Configuration.τ (F : Set (Configuration V)) ∧
      ∀ (T : Finset V) (c : Configuration V), c ∈ F → Hits T c →
        ∃ j : OtherLabel i, j ∈ D.properLabels i ∧ j.1 ∈ T ∧
          ∃ u ∈ T, u ∈ D.liveType (anchorPair i j) := by
  classical
  let Types := D.properTypes i
  have hex : ∀ t : ↥Types, ∃ j : OtherLabel i,
      j ∈ D.properLabels i ∧ D.liveType (anchorPair i j) = t.1 := by
    intro t
    obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp t.2
    exact ⟨j, hj, heq⟩
  choose sel hselP hsel using hex
  have hselinj : Function.Injective sel := by
    intro t u htu
    apply Subtype.ext
    rw [← hsel t, ← hsel u, htu]
  have hproper : ∀ t : ↥Types,
      IsProperDeparture i (sel t).1 (D.liveType (anchorPair i (sel t))) := by
    intro t
    simpa only [DepartingSystem.properLabels, Finset.mem_filter, Finset.mem_univ,
      true_and] using hselP t
  let cf : ↥Types → Configuration V := fun t =>
    properConfiguration (sel t).1 (D.liveType (anchorPair i (sel t)))
      (hproper t).2.1 (hproper t).2.2
  have hcfinj : Function.Injective cf := by
    intro t u htu
    apply hselinj
    apply Subtype.ext
    exact congrArg Configuration.j htu
  let F : Finset (Configuration V) := Finset.univ.map ⟨cf, hcfinj⟩
  refine ⟨F, by simp [F, Types], ?_, ?_, ?_⟩
  · intro c hc d hd hcd
    obtain ⟨t, -, rfl⟩ := Finset.mem_map.mp hc
    obtain ⟨u, -, rfl⟩ := Finset.mem_map.mp hd
    exact congrArg cf (hselinj (Subtype.ext hcd))
  · intro c hc d hd hcd
    obtain ⟨t, -, rfl⟩ := Finset.mem_map.mp hc
    obtain ⟨u, -, rfl⟩ := Finset.mem_map.mp hd
    apply congrArg cf
    apply Subtype.ext
    have he := congrArg (Sym2.equivMultiset V) hcd
    have ht := properConfiguration_multiset (sel t).1
      (D.liveType (anchorPair i (sel t))) (hproper t).2.1 (hproper t).2.2
    have hu := properConfiguration_multiset (sel u).1
      (D.liveType (anchorPair i (sel u))) (hproper u).2.1 (hproper u).2.2
    have hv := congrArg Subtype.val (ht.symm.trans (he.trans hu))
    simpa [hsel t, hsel u] using hv
  · intro T c hc hhit
    obtain ⟨t, -, rfl⟩ := Finset.mem_map.mp hc
    refine ⟨sel t, hselP t, hhit.1, ?_⟩
    obtain ⟨u, huT, huτ⟩ := hhit.2
    refine ⟨u, huT, ?_⟩
    have hm := properConfiguration_multiset (sel t).1
      (D.liveType (anchorPair i (sel t))) (hproper t).2.1 (hproper t).2.2
    have hu' : u ∈ ((Sym2.equivMultiset V) (cf t).τ : Multiset V) :=
      (mem_equivMultiset_iff u _).mpr huτ
    rwa [congrArg Subtype.val hm] at hu'

def DepartingSystem.SampleCoversAnchor {p n : ℕ} {S : MinimalNUS p n}
    {P : S.Pairing} {V : Type*} [Fintype V] [DecidableEq V]
    {B : LiveBlocks n V} (D : DepartingSystem P B) (i : V) (T : Finset V) : Prop :=
  (∃ j : OtherLabel i, j ∈ D.easyLabels i ∧ j.1 ∈ T) ∨
  ∃ j : OtherLabel i, j ∈ D.properLabels i ∧ j.1 ∈ T ∧
    ∃ u ∈ T, u ∈ D.liveType (anchorPair i j)


theorem DepartingSystem.exists_large_anchor_family {p n : ℕ}
    {S : MinimalNUS p n} {P : S.Pairing} {V : Type*}
    [Fintype V] [DecidableEq V] {B : LiveBlocks n V}
    (D : DepartingSystem P B) (i : V) (hm : 16 ≤ Fintype.card V)
    (hlarge : Fintype.card V ≤ 8 * (D.easyLabels i).card ∨
      Fintype.card V ≤ 8 * (D.properTypes i).card) :
    ∃ F : Finset (Configuration V),
      (1 / 8 : ℝ) * Fintype.card V ≤ F.card ∧
      Set.InjOn Configuration.j (F : Set (Configuration V)) ∧
      Set.InjOn Configuration.τ (F : Set (Configuration V)) ∧
      ∀ (T : Finset V) (c : Configuration V), c ∈ F → Hits T c →
        D.SampleCoversAnchor i T := by
  classical
  rcases hlarge with heasy | hproper
  · have h2 : 2 ≤ (D.easyLabels i).card := by omega
    obtain ⟨F, hcard, hj, hτ, hhit⟩ := D.exists_easy_anchor_family i h2
    refine ⟨F, ?_, hj, hτ, ?_⟩
    · rw [hcard]
      have he : (Fintype.card V : ℝ) ≤ 8 * ((D.easyLabels i).card : ℝ) := by
        exact_mod_cast heasy
      norm_num at ⊢
      linarith
    · intro T c hc hh
      exact Or.inl (hhit T c hc hh)
  · obtain ⟨F, hcard, hj, hτ, hhit⟩ := D.exists_proper_anchor_family i
    refine ⟨F, ?_, hj, hτ, ?_⟩
    · rw [hcard]
      have hp : (Fintype.card V : ℝ) ≤ 8 * ((D.properTypes i).card : ℝ) := by
        exact_mod_cast hproper
      norm_num at ⊢
      linarith
    · intro T c hc hh
      exact Or.inr (hhit T c hc hh)




def CompressionState.IsEdgeRow {p n : ℕ} {S : MinimalNUS p n} {P : S.Pairing}
    {C V : Type*} [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]
    (st : CompressionState S P C V) (r : Fin n → ℤ) : Option V → Option V → Prop
  | none, none => False
  | none, some b =>
      (fun u => st.basis.repr (Submodule.Quotient.mk r) (Sum.inr u)) = Pi.single b 1
  | some a, none =>
      (fun u => st.basis.repr (Submodule.Quotient.mk r) (Sum.inr u)) = -(Pi.single a 1)
  | some a, some b =>
      (fun u => st.basis.repr (Submodule.Quotient.mk r) (Sum.inr u)) =
        Pi.single a 1 - Pi.single b 1

theorem CompressionState.isEdgeRow_symm {p n : ℕ} {S : MinimalNUS p n}
    {P : S.Pairing} {C V : Type*} [Fintype C] [DecidableEq C]
    [Fintype V] [DecidableEq V] (st : CompressionState S P C V)
    (r : Fin n → ℤ) (x y : Option V) :
    st.IsEdgeRow r x y → st.IsEdgeRow (-r) y x := by
  rcases x with _ | a <;> rcases y with _ | b
  · simp [CompressionState.IsEdgeRow]
  · intro h
    change (fun u => st.basis.repr (Submodule.Quotient.mk (-r)) (Sum.inr u)) = _
    rw [Submodule.Quotient.mk_neg, map_neg]
    ext u
    have hu := congrFun h u
    simp only [Finsupp.neg_apply, Pi.neg_apply, Pi.single_apply] at hu ⊢
    rw [hu]
  · intro h
    change (fun u => st.basis.repr (Submodule.Quotient.mk (-r)) (Sum.inr u)) = _
    rw [Submodule.Quotient.mk_neg, map_neg]
    ext u
    have hu := congrFun h u
    simp only [Finsupp.neg_apply, Pi.neg_apply, Pi.single_apply] at hu ⊢
    rw [hu]
    split <;> ring
  · intro h
    change (fun u => st.basis.repr (Submodule.Quotient.mk (-r)) (Sum.inr u)) = _
    rw [Submodule.Quotient.mk_neg, map_neg]
    ext u
    have hu := congrFun h u
    simp only [Finsupp.neg_apply, Pi.single_apply,
      Pi.sub_apply] at hu ⊢
    rw [hu]
    ring


noncomputable def CompressionState.unitGraph {p n : ℕ} {S : MinimalNUS p n}
    {P : S.Pairing} {C V : Type*} [Fintype C] [DecidableEq C]
    [Fintype V] [DecidableEq V] (st : CompressionState S P C V) (R : ℤ) :
    SimpleGraph (Option V) :=
  SimpleGraph.fromRel fun x y => ∃ r : Fin n → ℤ,
    r ∈ S.colLat P ∧
    (∑ c : C, |st.basis.repr (Submodule.Quotient.mk r) (Sum.inl c)|) ≤ R ∧
    st.IsEdgeRow r x y

theorem CompressionState.unitGraph_adj_of_row {p n : ℕ} {S : MinimalNUS p n}
    {P : S.Pairing} {C V : Type*} [Fintype C] [DecidableEq C]
    [Fintype V] [DecidableEq V] (st : CompressionState S P C V) {R : ℤ}
    {r : Fin n → ℤ} (hr : r ∈ S.colLat P)
    (hR : (∑ c : C, |st.basis.repr (Submodule.Quotient.mk r) (Sum.inl c)|) ≤ R)
    {x y : Option V} (hxy : x ≠ y) (hedge : st.IsEdgeRow r x y) :
    (st.unitGraph R).Adj x y := by
  rw [CompressionState.unitGraph, SimpleGraph.fromRel_adj]
  exact ⟨hxy, Or.inl ⟨r, hr, hR, hedge⟩⟩

theorem CompressionState.exists_row_of_unitGraph_adj {p n : ℕ}
    {S : MinimalNUS p n} {P : S.Pairing} {C V : Type*}
    [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]
    (st : CompressionState S P C V) {R : ℤ} {x y : Option V}
    (hxy : (st.unitGraph R).Adj x y) :
    ∃ r : Fin n → ℤ, r ∈ S.colLat P ∧
      (∑ c : C, |st.basis.repr (Submodule.Quotient.mk r) (Sum.inl c)|) ≤ R ∧
      st.IsEdgeRow r x y := by
  rw [CompressionState.unitGraph, SimpleGraph.fromRel_adj] at hxy
  rcases hxy.2 with ⟨r, hr, hR, he⟩ | ⟨r, hr, hR, he⟩
  · exact ⟨r, hr, hR, he⟩
  · refine ⟨-r, (S.colLat P).neg_mem hr, ?_, st.isEdgeRow_symm r y x he⟩
    simpa only [Submodule.Quotient.mk_neg, map_neg, Finsupp.neg_apply, abs_neg] using hR


theorem CompressionState.exists_pivot_of_unitGraph_adj {p n : ℕ}
    {S : MinimalNUS p n} {P : S.Pairing} {C V : Type*}
    [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]
    (st : CompressionState S P C V) {R : ℤ} (v : V) (y : Option V)
    (hvy : (st.unitGraph R).Adj (some v) y) :
    ∃ (r : Fin n → ℤ) (_hr : r ∈ S.colLat P)
        (parent : Option {u : V // u ≠ v}),
      st.basis.repr (Submodule.Quotient.mk r) (Sum.inr v) = 1 ∧
      (∀ u : {u : V // u ≠ v},
        st.basis.repr (Submodule.Quotient.mk r) (Sum.inr u.1) =
          if parent = some u then -1 else 0) ∧
      Option.map Subtype.val parent = y ∧
      (∑ c : C, |st.basis.repr (Submodule.Quotient.mk r) (Sum.inl c)|) ≤ R := by
  classical
  obtain ⟨q, hq, hqR, hedge⟩ := st.exists_row_of_unitGraph_adj hvy
  rcases y with _ | w
  · refine ⟨-q, (S.colLat P).neg_mem hq, none, ?_, ?_, rfl, ?_⟩
    · have h := congrFun hedge v
      change st.basis.repr (Submodule.Quotient.mk (-q)) (Sum.inr v) = 1
      rw [Submodule.Quotient.mk_neg, map_neg, Finsupp.neg_apply]
      simpa [CompressionState.IsEdgeRow, Pi.single_apply] using congrArg Neg.neg h
    · intro u
      have h := congrFun hedge u.1
      change st.basis.repr (Submodule.Quotient.mk (-q)) (Sum.inr u.1) = _
      rw [Submodule.Quotient.mk_neg, map_neg, Finsupp.neg_apply]
      have hn := congrArg Neg.neg h
      simpa [CompressionState.IsEdgeRow, Pi.single_apply, u.2] using hn
    · simpa only [Submodule.Quotient.mk_neg, map_neg, Finsupp.neg_apply,
        abs_neg] using hqR
  · have hvw : v ≠ w := by
      intro e
      subst w
      exact hvy.ne rfl
    let w' : {u : V // u ≠ v} := ⟨w, Ne.symm hvw⟩
    refine ⟨q, hq, some w', ?_, ?_, rfl, hqR⟩
    · have h := congrFun hedge v
      simpa [CompressionState.IsEdgeRow, Pi.single_apply, hvw] using h
    · intro u
      have h := congrFun hedge u.1
      by_cases huw : u.1 = w
      · have huw' : u = w' := Subtype.ext huw
        subst u
        simpa [CompressionState.IsEdgeRow, Pi.single_apply, hvw, w'] using h
      · have hune : some w' ≠ some u := by
          intro e
          exact huw (congrArg Subtype.val (Option.some.inj e)).symm
        simpa [CompressionState.IsEdgeRow, Pi.single_apply, u.2, huw, hune] using h


theorem CompressionState.exists_unitGraph_neighbor_at {p n : ℕ}
    {S : MinimalNUS p n} {P : S.Pairing} {C V : Type*}
    [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]
    (st : CompressionState S P C V) {R : ℤ} (r : Fin n → ℤ)
    (hr : r ∈ S.colLat P)
    (hR : (∑ c : C, |st.basis.repr (Submodule.Quotient.mk r) (Sum.inl c)|) ≤ R)
    (i : V)
    (hu : IsUnitRelation
      (fun u => st.basis.repr (Submodule.Quotient.mk r) (Sum.inr u)))
    (hi : st.basis.repr (Submodule.Quotient.mk r) (Sum.inr i) = 1) :
    ∃ y : Option V, (st.unitGraph R).Adj (some i) y := by
  let w : V → ℤ := fun u => st.basis.repr (Submodule.Quotient.mk r) (Sum.inr u)
  change w i = 1 at hi
  rcases hu with ⟨a, ha⟩ | ⟨a, b, hab, ha⟩ | ⟨a, ha⟩ | ⟨a, b, hab, ha⟩
  · have hai : a = i := by
      by_contra h
      have := congrFun ha i
      simp [w, h] at this hi
      omega
    subst a
    exact ⟨none, (st.unitGraph_adj_of_row hr hR (by simp)
      (by simpa [CompressionState.IsEdgeRow, w] using ha)).symm⟩
  · have hai : a = i := by
      by_contra hia
      have hbi : b ≠ i := by
        intro hbi
        subst b
        have hv := congrFun ha i
        simp [w, hia] at hv hi
        omega
      have hv := congrFun ha i
      simp [w, hia, hbi] at hv hi
      omega
    subst a
    exact ⟨some b, st.unitGraph_adj_of_row hr hR (by simp [hab])
      (by simpa [CompressionState.IsEdgeRow, w] using ha)⟩
  · have hv := congrFun ha i
    exfalso
    by_cases hai : a = i <;> simp [w, hai] at hv hi <;> omega
  · have hbi : b = i := by
      by_contra hbi
      have hai : a ≠ i := by
        intro hai
        subst a
        have hv := congrFun ha i
        simp [w, hbi] at hv hi
        omega
      have hv := congrFun ha i
      simp [w, hai, hbi] at hv hi
      omega
    subst b
    exact ⟨some a, st.unitGraph_adj_of_row hr hR
      (by intro e; exact hab (Option.some.inj e).symm)
      (by
        change (fun u => st.basis.repr (Submodule.Quotient.mk r) (Sum.inr u)) =
          Pi.single i 1 - Pi.single a 1
        rw [ha]
        ext u
        simp only [Pi.neg_apply, Pi.sub_apply]
        ring)⟩


theorem DepartingSystem.unitGraph_neighbor_label_of_mem_left {p n : ℕ}
    {S : MinimalNUS p n} {P : S.Pairing} {C V : Type*}
    [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]
    (st : CompressionState S P C V) {M : ℤ} (hM : st.CoreBound M)
    (D : DepartingSystem P st.blocks) (e : OrderedDistinct V)
    (hmem : e.1.1 ∈ D.liveType e) :
    ∃ y, (st.unitGraph (8 * M)).Adj (some e.1.2) y := by
  apply st.exists_unitGraph_neighbor_at (D.row e) (D.row_mem_colLat e)
    (le_trans (D.row_core_norm_le st hM e) (by
      have hM0 := st.coreBound_nonneg hM
      linarith)) e.1.2 (D.row_unit_of_mem_left st e hmem)
  change st.projectedRow (D.t e) (Sum.inr e.1.2) = 1
  rw [congrFun (st.projectedRow_live e.2 (D.mem_rectangle e)) e.1.2]
  exact departingLive_label_of_mem_left e.1.1 e.1.2 (D.liveType e) e.2
    (liveLabels_card_le_two st.blocks _) hmem
    (liveLabels_departing_ne st.blocks e.2 (D.leaves_rectangle e))


theorem DepartingSystem.promoted_unitGraph_neighbor_at {p n : ℕ}
    {S : MinimalNUS p n} {P : S.Pairing} {C V : Type*}
    [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]
    (st : CompressionState S P C V) {M : ℤ} (hM : st.CoreBound M) (hM1 : 1 ≤ M)
    (D : DepartingSystem P st.blocks) (e : OrderedDistinct V) (T : Finset V)
    (i : {v : V // v ∉ T})
    (hu : IsUnitRelation (fun v : {v : V // v ∉ T} =>
      (st.promote T).basis.repr (Submodule.Quotient.mk (D.row e)) (Sum.inr v)))
    (hi : (st.promote T).basis.repr (Submodule.Quotient.mk (D.row e))
      (Sum.inr i) = 1) :
    ∃ y, ((st.promote T).unitGraph (8 * M)).Adj (some i) y := by
  exact (st.promote T).exists_unitGraph_neighbor_at (D.row e) (D.row_mem_colLat e)
    (D.promoted_row_core_norm_le_eight_mul st e T hM hM1) i hu hi

theorem DepartingSystem.promoted_neighbor_of_direct {p n : ℕ}
    {S : MinimalNUS p n} {P : S.Pairing} {C V : Type*}
    [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]
    (st : CompressionState S P C V) {M : ℤ} (hM : st.CoreBound M) (hM1 : 1 ≤ M)
    (D : DepartingSystem P st.blocks) (e : OrderedDistinct V)
    (hmem : e.1.2 ∈ D.liveType e) (T : Finset V) (hiT : e.1.1 ∉ T) :
    ∃ y, ((st.promote T).unitGraph (8 * M)).Adj (some ⟨e.1.1, hiT⟩) y := by
  apply D.promoted_unitGraph_neighbor_at st hM hM1 e T ⟨e.1.1, hiT⟩
    (D.promoted_row_unit_of_mem_right st e hmem T hiT)
  rw [st.promote_live_coord_row]
  change st.projectedRow (D.t e) (Sum.inr e.1.1) = 1
  rw [congrFun (st.projectedRow_live e.2 (D.mem_rectangle e)) e.1.1]
  exact departingLive_anchor_of_mem_right e.1.1 e.1.2 (D.liveType e) e.2
    (liveLabels_card_le_two st.blocks _) hmem
    (liveLabels_departing_ne st.blocks e.2 (D.leaves_rectangle e))

theorem DepartingSystem.promoted_neighbor_of_easy {p n : ℕ}
    {S : MinimalNUS p n} {P : S.Pairing} {C V : Type*}
    [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]
    (st : CompressionState S P C V) {M : ℤ} (hM : st.CoreBound M) (hM1 : 1 ≤ M)
    (D : DepartingSystem P st.blocks) (e : OrderedDistinct V)
    (heasy : IsEasyDeparture e.1.1 e.1.2 (D.liveType e))
    (T : Finset V) (hiT : e.1.1 ∉ T) (hjT : e.1.2 ∈ T) :
    ∃ y, ((st.promote T).unitGraph (8 * M)).Adj (some ⟨e.1.1, hiT⟩) y := by
  apply D.promoted_unitGraph_neighbor_at st hM hM1 e T ⟨e.1.1, hiT⟩
    (D.promoted_row_unit_of_easy st e heasy T hiT hjT)
  rw [st.promote_live_coord_row]
  change st.projectedRow (D.t e) (Sum.inr e.1.1) = 1
  rw [congrFun (st.projectedRow_live e.2 (D.mem_rectangle e)) e.1.1]
  exact departingLive_anchor_of_not_mem e.1.1 e.1.2 (D.liveType e) e.2 heasy.1

theorem DepartingSystem.promoted_neighbor_of_proper {p n : ℕ}
    {S : MinimalNUS p n} {P : S.Pairing} {C V : Type*}
    [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]
    (st : CompressionState S P C V) {M : ℤ} (hM : st.CoreBound M) (hM1 : 1 ≤ M)
    (D : DepartingSystem P st.blocks) (e : OrderedDistinct V)
    (hproper : IsProperDeparture e.1.1 e.1.2 (D.liveType e))
    (T : Finset V) (hiT : e.1.1 ∉ T) (hjT : e.1.2 ∈ T)
    (hhit : ∃ u ∈ T, u ∈ D.liveType e) :
    ∃ y, ((st.promote T).unitGraph (8 * M)).Adj (some ⟨e.1.1, hiT⟩) y := by
  apply D.promoted_unitGraph_neighbor_at st hM hM1 e T ⟨e.1.1, hiT⟩
    (D.promoted_row_unit_of_proper st e hproper T hiT hjT hhit)
  rw [st.promote_live_coord_row]
  change st.projectedRow (D.t e) (Sum.inr e.1.1) = 1
  rw [congrFun (st.projectedRow_live e.2 (D.mem_rectangle e)) e.1.1]
  exact departingLive_anchor_of_not_mem e.1.1 e.1.2 (D.liveType e) e.2 hproper.1


noncomputable def CompressionState.isolatedLive {p n : ℕ}
    {S : MinimalNUS p n} {P : S.Pairing} {C V : Type*}
    [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]
    (st : CompressionState S P C V) (R : ℤ) : Finset V := by
  classical
  exact Finset.univ.filter fun v => ∀ w, ¬(st.unitGraph R).Adj (some v) w

theorem exists_high_anchor_sample :
    ∃ (D₀ : ℝ) (m₀ : ℕ), 0 < D₀ ∧
      ∀ {p n : ℕ} {S : MinimalNUS p n} {P : S.Pairing} {C V : Type}
        [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]
        (st : CompressionState S P C V) {M : ℤ}, st.CoreBound M → 1 ≤ M →
        (D : DepartingSystem P st.blocks) →
        max m₀ 16 ≤ Fintype.card V →
        (∀ i, ¬D.IsDirectAnchor i →
          Fintype.card V ≤ 8 * (D.easyLabels i).card ∨
          Fintype.card V ≤ 8 * (D.properTypes i).card) →
        ∃ T : Finset V, (T.card : ℝ) ≤ D₀ * Real.sqrt (Fintype.card V) ∧
          8 * ((st.promote T).isolatedLive (8 * M)).card ≤ Fintype.card V := by
  classical
  obtain ⟨D₀, m₀, hD₀, hcut⟩ := common_cut (1 / 8 : ℝ) (by norm_num)
  refine ⟨D₀, m₀, hD₀, ?_⟩
  intro p n S P C V _ _ _ _ st M hM hM1 D hm hall
  have hm0 : m₀ ≤ Fintype.card V := le_trans (le_max_left _ _) hm
  have hm16 : 16 ≤ Fintype.card V := le_trans (le_max_right _ _) hm
  by_cases hndex : ∃ i : V, ¬D.IsDirectAnchor i
  · obtain ⟨i₀, hi₀⟩ := hndex
    obtain ⟨F₀, hF₀card, hF₀j, hF₀τ, hF₀hit⟩ :=
      D.exists_large_anchor_family i₀ hm16 (hall i₀ hi₀)
    have hfamilies : ∀ i : V, ∃ F : Finset (Configuration V),
        (1 / 8 : ℝ) * Fintype.card V ≤ F.card ∧
        Set.InjOn Configuration.j (F : Set (Configuration V)) ∧
        Set.InjOn Configuration.τ (F : Set (Configuration V)) ∧
        (¬D.IsDirectAnchor i → ∀ T c, c ∈ F → Hits T c →
          D.SampleCoversAnchor i T) := by
      intro i
      by_cases hdi : D.IsDirectAnchor i
      · exact ⟨F₀, hF₀card, hF₀j, hF₀τ, fun h => (h hdi).elim⟩
      · obtain ⟨F, hc, hj, hτ, hhit⟩ :=
          D.exists_large_anchor_family i hm16 (hall i hdi)
        exact ⟨F, hc, hj, hτ, fun _ => hhit⟩
    choose Fam hFam using hfamilies
    let ev : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
    let 𝓕 : Fin (Fintype.card V) → Finset (Configuration V) :=
      fun k => Fam (ev.symm k)
    obtain ⟨T, hTcard, Bad, hBad, hhit⟩ :=
      hcut V inferInstance inferInstance (Fintype.card V) 𝓕 hm0 (le_refl _)
        (fun k => (hFam (ev.symm k)).1)
        (fun k => (hFam (ev.symm k)).2.1)
        (fun k => (hFam (ev.symm k)).2.2.1)
    refine ⟨T, hTcard, ?_⟩
    let Iso := (st.promote T).isolatedLive (8 * M)
    let emb : {v : V // v ∉ T} ↪ Fin (Fintype.card V) :=
      ⟨fun v => ev v.1, fun a b h => Subtype.ext (ev.injective h)⟩
    have hsub : Iso.image emb ⊆ Bad := by
      intro k hk
      obtain ⟨v, hvIso, rfl⟩ := Finset.mem_image.mp hk
      by_contra hkBad
      let i : V := v.1
      have hviso : ∀ y, ¬((st.promote T).unitGraph (8 * M)).Adj (some v) y := by
        simpa [Iso, CompressionState.isolatedLive] using hvIso
      by_cases hdi : D.IsDirectAnchor i
      · obtain ⟨j, hj⟩ := hdi
        obtain ⟨y, hy⟩ := D.promoted_neighbor_of_direct st hM hM1
          (anchorPair i j) hj T v.2
        exact hviso y hy
      · have hfamilyHit := hhit (ev i) hkBad
        obtain ⟨c, hcF, hcHit⟩ := hfamilyHit
        have hcF' : c ∈ Fam i := by simpa [𝓕] using hcF
        have hcover := (hFam i).2.2.2 hdi T c hcF' hcHit
        rcases hcover with ⟨j, hjEasy, hjT⟩ | ⟨j, hjProper, hjT, hu, huT, huν⟩
        · have heasy : IsEasyDeparture i j.1
              (D.liveType (anchorPair i j)) := by
            simpa only [DepartingSystem.easyLabels, Finset.mem_filter,
              Finset.mem_univ, true_and] using hjEasy
          obtain ⟨y, hy⟩ := D.promoted_neighbor_of_easy st hM hM1
            (anchorPair i j) heasy T v.2 hjT
          exact hviso y hy
        · have hproper : IsProperDeparture i j.1
              (D.liveType (anchorPair i j)) := by
            simpa only [DepartingSystem.properLabels, Finset.mem_filter,
              Finset.mem_univ, true_and] using hjProper
          obtain ⟨y, hy⟩ := D.promoted_neighbor_of_proper st hM hM1
            (anchorPair i j) hproper T v.2 hjT ⟨hu, huT, huν⟩
          exact hviso y hy
    have hcardImage : (Iso.image emb).card = Iso.card := by
      exact Finset.card_image_of_injective _ emb.injective
    have hle := Finset.card_le_card hsub
    rw [hcardImage] at hle
    exact le_trans (Nat.mul_le_mul_left 8 hle) hBad
  · push Not at hndex
    refine ⟨∅, ?_, ?_⟩
    · simp
      positivity
    · have hzero : ((st.promote (∅ : Finset V)).isolatedLive (8 * M)).card = 0 := by
        apply Finset.card_eq_zero.mpr
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro v hv
        have hviso : ∀ y,
            ¬((st.promote (∅ : Finset V)).unitGraph (8 * M)).Adj (some v) y := by
          simpa [CompressionState.isolatedLive] using hv
        obtain ⟨j, hj⟩ := hndex v.1
        obtain ⟨y, hy⟩ := D.promoted_neighbor_of_direct st hM hM1
          (anchorPair v.1 j) hj ∅ v.2
        exact hviso y hy
      rw [hzero]
      simp


theorem DepartingSystem.isolated_mem_easy_or_proper {p n : ℕ}
    {S : MinimalNUS p n} {P : S.Pairing} {C V : Type*}
    [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]
    (st : CompressionState S P C V) {M : ℤ} (hM : st.CoreBound M)
    (D : DepartingSystem P st.blocks) (i : V) (hnd : ¬D.IsDirectAnchor i)
    (j : OtherLabel i) (hjiso : j.1 ∈ st.isolatedLive (8 * M)) :
    j ∈ D.easyLabels i ∨ j ∈ D.properLabels i := by
  classical
  let e : OrderedDistinct V := anchorPair i j
  let ν : Multiset V := D.liveType e
  have hcard : ν.card ≤ 2 := liveLabels_card_le_two st.blocks _
  have hne : ν ≠ {i, j.1} :=
    liveLabels_departing_ne st.blocks e.2 (D.leaves_rectangle e)
  have hni : i ∉ ν := by
    intro hi
    obtain ⟨y, hy⟩ := D.unitGraph_neighbor_label_of_mem_left st hM e hi
    have hiso : ∀ w, ¬(st.unitGraph (8 * M)).Adj (some j.1) w := by
      simpa [CompressionState.isolatedLive] using hjiso
    exact hiso y hy
  have hnj : j.1 ∉ ν := by
    intro hj
    apply hnd
    exact ⟨j, hj⟩
  by_cases hsmall : ν.card ≤ 1
  · left
    simp only [DepartingSystem.easyLabels, Finset.mem_filter, Finset.mem_univ, true_and]
    simpa [e, ν] using (show IsEasyDeparture i j.1 ν from ⟨hni, hnj, hsmall⟩)
  · right
    have htwo : ν.card = 2 := by omega
    simp only [DepartingSystem.properLabels, Finset.mem_filter, Finset.mem_univ, true_and]
    simpa [e, ν] using (show IsProperDeparture i j.1 ν from ⟨hni, hnj, htwo⟩)


theorem DepartingSystem.unitGraph_adj_of_same_type {p n : ℕ}
    {S : MinimalNUS p n} {P : S.Pairing} {C V : Type*}
    [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]
    (st : CompressionState S P C V) {M : ℤ} (hM : st.CoreBound M)
    (D : DepartingSystem P st.blocks) (e e' : OrderedDistinct V)
    (hanchor : e.1.1 = e'.1.1) (htype : D.liveType e = D.liveType e')
    (hlabel : e.1.2 ≠ e'.1.2) :
    (st.unitGraph (8 * M)).Adj (some e.1.2) (some e'.1.2) := by
  apply st.unitGraph_adj_of_row (D.row_sub_mem_colLat e e')
    (D.row_sub_core_norm_le st hM e e')
  · intro heq
    exact hlabel (Option.some.inj heq)
  · exact D.row_sub_live_eq st e e' hanchor htype


theorem DepartingSystem.isolated_proper_type_injective {p n : ℕ}
    {S : MinimalNUS p n} {P : S.Pairing} {C V : Type*}
    [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]
    (st : CompressionState S P C V) {M : ℤ} (hM : st.CoreBound M)
    (D : DepartingSystem P st.blocks) (i : V) :
    Set.InjOn (fun j : OtherLabel i => D.liveType (anchorPair i j))
      {j | j ∈ D.properLabels i ∧ j.1 ∈ st.isolatedLive (8 * M)} := by
  intro j hj k hk htype
  apply Subtype.ext
  by_contra hjk
  have hadj := D.unitGraph_adj_of_same_type st hM (anchorPair i j) (anchorPair i k)
    rfl htype hjk
  have hkiso : ∀ w, ¬(st.unitGraph (8 * M)).Adj (some k.1) w := by
    simpa [CompressionState.isolatedLive] using hk.2
  exact hkiso (some j.1) hadj.symm


theorem DepartingSystem.isolatedLive_card_le_anchor {p n : ℕ}
    {S : MinimalNUS p n} {P : S.Pairing} {C V : Type*}
    [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]
    (st : CompressionState S P C V) {M : ℤ} (hM : st.CoreBound M)
    (D : DepartingSystem P st.blocks) (i : V) (hnd : ¬D.IsDirectAnchor i) :
    (st.isolatedLive (8 * M)).card ≤
      1 + (D.easyLabels i).card + (D.properTypes i).card := by
  classical
  let Iso := st.isolatedLive (8 * M)
  let I : Finset (OtherLabel i) := Finset.univ.filter fun j => j.1 ∈ Iso
  let A : Finset (OtherLabel i) := I.filter fun j => j ∈ D.easyLabels i
  let B : Finset (OtherLabel i) := I.filter fun j => j ∉ D.easyLabels i
  let τ : OtherLabel i → Multiset V := fun j => D.liveType (anchorPair i j)
  have hIcard : Iso.card ≤ I.card + 1 := by
    have hIeq : I = Iso.subtype fun v => v ≠ i := by
      ext j
      simp [I]
    have hfilter : (Iso.filter fun v => v ≠ i) = Iso.erase i := by
      ext v
      simp [ne_eq, and_comm]
    rw [hIeq, Finset.card_subtype, hfilter]
    by_cases hi : i ∈ Iso
    · have he := Finset.card_erase_add_one hi
      omega
    · rw [Finset.erase_eq_self.mpr hi]
      omega
  have hsplit : A.card + B.card = I.card := by
    simpa [A, B] using I.card_filter_add_card_filter_not
      (fun j : OtherLabel i => j ∈ D.easyLabels i)
  have hA : A.card ≤ (D.easyLabels i).card := by
    apply Finset.card_le_card
    intro j hj
    exact (Finset.mem_filter.mp hj).2
  have hBproper : B ⊆ D.properLabels i := by
    intro j hj
    have hjI := (Finset.mem_filter.mp hj).1
    have hjne := (Finset.mem_filter.mp hj).2
    have hjiso : j.1 ∈ st.isolatedLive (8 * M) := by
      simpa [I, Iso] using hjI
    rcases D.isolated_mem_easy_or_proper st hM i hnd j hjiso with he | hp
    · exact absurd he hjne
    · exact hp
  have hτinj : Set.InjOn τ (B : Set (OtherLabel i)) := by
    intro j hj k hk heq
    apply D.isolated_proper_type_injective st hM i
    · exact ⟨hBproper (Finset.mem_coe.mp hj), by
        have hjI := (Finset.mem_filter.mp (Finset.mem_coe.mp hj)).1
        simpa [I, Iso] using hjI⟩
    · exact ⟨hBproper (Finset.mem_coe.mp hk), by
        have hkI := (Finset.mem_filter.mp (Finset.mem_coe.mp hk)).1
        simpa [I, Iso] using hkI⟩
    · exact heq
  have hBimage : (B.image τ).card = B.card := by
    apply Finset.card_image_of_injOn
    intro j hj k hk heq
    exact hτinj (Finset.mem_coe.mpr hj) (Finset.mem_coe.mpr hk) heq
  have himage : B.image τ ⊆ D.properTypes i := by
    intro ν hν
    obtain ⟨j, hjB, rfl⟩ := Finset.mem_image.mp hν
    rw [DepartingSystem.properTypes]
    exact Finset.mem_image.mpr ⟨j, hBproper hjB, rfl⟩
  have hB : B.card ≤ (D.properTypes i).card := by
    rw [← hBimage]
    exact Finset.card_le_card himage
  change Iso.card ≤ 1 + (D.easyLabels i).card + (D.properTypes i).card
  omega




structure ForestPivotPlan {p n : ℕ} {S : MinimalNUS p n} {P : S.Pairing}
    {C V : Type*} [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]
    (st : CompressionState S P C V) (R : ℤ) where
  parent : V → Option (Option V)
  rank : Option V → ℕ
  decreases : ∀ v y, parent v = some y → rank y < rank (some v)
  rank_le_three : ∀ v : V, rank (some v) ≤ 3
  pivotData : ∀ v y, parent v = some y →
    ∃ (r : Fin n → ℤ) (_hr : r ∈ S.colLat P)
        (pivParent : Option {u : V // u ≠ v}),
      st.basis.repr (Submodule.Quotient.mk r) (Sum.inr v) = 1 ∧
      (∀ u : {u : V // u ≠ v},
        st.basis.repr (Submodule.Quotient.mk r) (Sum.inr u.1) =
          if pivParent = some u then -1 else 0) ∧
      Option.map Subtype.val pivParent = y ∧
      (∑ c : C, |st.basis.repr (Submodule.Quotient.mk r) (Sum.inl c)|) ≤ R


theorem CompressionState.exists_forestPivotPlan {p n : ℕ}
    {S : MinimalNUS p n} {P : S.Pairing} {C V : Type*}
    [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]
    (st : CompressionState S P C V) (R : ℤ)
    [DecidableRel (st.unitGraph R).Adj] (f : ℕ)
    (hf : (Finset.univ.filter fun v : V =>
      ∀ w, ¬(st.unitGraph R).Adj (some v) w).card ≤ f) :
    ∃ F : SimpleGraph (Option V), F ≤ st.unitGraph R ∧ F.IsAcyclic ∧
      2 * Nat.card {c : F.ConnectedComponent // (none : Option V) ∉ c.supp} ≤
        Fintype.card V + f ∧
      ∃ plan : ForestPivotPlan st R,
        2 * Fintype.card {v : V // plan.parent v = none} ≤ Fintype.card V + f := by
  classical
  obtain ⟨F, hFG, hacyc, hdiam, hroot, hcount, hdata⟩ :=
    bounded_radius_contraction (st.unitGraph R) f hf
  obtain ⟨par, rk, hadj, hdec, hrank, hrootcount⟩ := hdata
  let liveParent : V → Option (Option V) := fun v => par (some v)
  have hpivot : ∀ v y, liveParent v = some y →
      ∃ (r : Fin n → ℤ) (hr : r ∈ S.colLat P)
          (pivParent : Option {u : V // u ≠ v}),
        st.basis.repr (Submodule.Quotient.mk r) (Sum.inr v) = 1 ∧
        (∀ u : {u : V // u ≠ v},
          st.basis.repr (Submodule.Quotient.mk r) (Sum.inr u.1) =
            if pivParent = some u then -1 else 0) ∧
        Option.map Subtype.val pivParent = y ∧
        (∑ c : C, |st.basis.repr (Submodule.Quotient.mk r) (Sum.inl c)|) ≤ R := by
    intro v y hpar
    have hne : some v ≠ y := by
      intro e
      have hd := hdec (some v) y hpar
      rw [e] at hd
      exact (Nat.lt_irrefl _ hd)
    have hFy : F.Adj (some v) y := (hadj (some v) y).mpr ⟨hne, Or.inl hpar⟩
    exact st.exists_pivot_of_unitGraph_adj v y (hFG hFy)
  let plan : ForestPivotPlan st R :=
    { parent := liveParent
      rank := rk
      decreases := fun v y h => hdec (some v) y h
      rank_le_three := hrank
      pivotData := hpivot }
  refine ⟨F, hFG, hacyc, hcount, plan, ?_⟩
  rw [Fintype.card_subtype]
  simpa [plan, liveParent] using hrootcount

namespace ForestPivotPlan

variable {p n : ℕ} {S : MinimalNUS p n} {P : S.Pairing}
variable {C V : Type*} [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]
variable {st : CompressionState S P C V} {R : ℤ}


abbrev Roots (plan : ForestPivotPlan st R) := {v : V // plan.parent v = none}


abbrev Active (plan : ForestPivotPlan st R) := {v : V // plan.parent v ≠ none}

noncomputable def activeParent (plan : ForestPivotPlan st R)
    (v : plan.Active) : Option V :=
  Classical.choose (Option.ne_none_iff_exists'.mp v.2)

theorem parent_activeParent (plan : ForestPivotPlan st R) (v : plan.Active) :
    plan.parent v.1 = some (plan.activeParent v) :=
  Classical.choose_spec (Option.ne_none_iff_exists'.mp v.2)


def terminalRoot (plan : ForestPivotPlan st R) (v : V) : Option plan.Roots :=
  match h : plan.parent v with
  | none => some ⟨v, h⟩
  | some none => none
  | some (some w) => terminalRoot plan w
termination_by plan.rank (some v)
decreasing_by exact plan.decreases v (some w) h

@[simp] theorem terminalRoot_of_root (plan : ForestPivotPlan st R)
    (v : plan.Roots) : plan.terminalRoot v.1 = some v := by
  rw [terminalRoot]
  split <;> rename_i hpar
  · apply congrArg some
    exact Subtype.ext rfl
  · rw [v.2] at hpar
    contradiction
  · rw [v.2] at hpar
    contradiction

theorem terminalRoot_of_live_parent (plan : ForestPivotPlan st R) {v w : V}
    (h : plan.parent v = some (some w)) :
    plan.terminalRoot v = plan.terminalRoot w := by
  rw [terminalRoot]
  split <;> simp_all

theorem terminalRoot_of_core_parent (plan : ForestPivotPlan st R) {v : V}
    (h : plan.parent v = some none) : plan.terminalRoot v = none := by
  rw [terminalRoot]
  split <;> simp_all


noncomputable def chosenRow (plan : ForestPivotPlan st R) {v : V} {y : Option V}
    (h : plan.parent v = some y) : Fin n → ℤ :=
  Classical.choose (plan.pivotData v y h)

theorem chosenRow_mem (plan : ForestPivotPlan st R) {v : V} {y : Option V}
    (h : plan.parent v = some y) : plan.chosenRow h ∈ S.colLat P :=
  Classical.choose (Classical.choose_spec (plan.pivotData v y h))

noncomputable def chosenPivotParent (plan : ForestPivotPlan st R)
    {v : V} {y : Option V} (h : plan.parent v = some y) :
    Option {u : V // u ≠ v} :=
  Classical.choose (Classical.choose_spec
    (Classical.choose_spec (plan.pivotData v y h)))

theorem chosenRow_spec (plan : ForestPivotPlan st R) {v : V} {y : Option V}
    (h : plan.parent v = some y) :
    st.basis.repr (Submodule.Quotient.mk (plan.chosenRow h)) (Sum.inr v) = 1 ∧
    (∀ u : {u : V // u ≠ v},
      st.basis.repr (Submodule.Quotient.mk (plan.chosenRow h)) (Sum.inr u.1) =
        if plan.chosenPivotParent h = some u then -1 else 0) ∧
    Option.map Subtype.val (plan.chosenPivotParent h) = y ∧
    (∑ c : C,
      |st.basis.repr (Submodule.Quotient.mk (plan.chosenRow h)) (Sum.inl c)|) ≤ R := by
  exact Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (plan.pivotData v y h)))

theorem chosenRow_core_norm_le (plan : ForestPivotPlan st R)
    {v : V} {y : Option V} (h : plan.parent v = some y) :
    (∑ c : C,
      |st.basis.repr (Submodule.Quotient.mk (plan.chosenRow h)) (Sum.inl c)|) ≤ R :=
  (plan.chosenRow_spec h).2.2.2

noncomputable def activeRow (plan : ForestPivotPlan st R)
    (v : plan.Active) : Fin n → ℤ :=
  plan.chosenRow (plan.parent_activeParent v)

theorem activeRow_mem (plan : ForestPivotPlan st R) (v : plan.Active) :
    plan.activeRow v ∈ S.colLat P :=
  plan.chosenRow_mem (plan.parent_activeParent v)


noncomputable def pivotMatrix (plan : ForestPivotPlan st R) :
    Matrix plan.Active plan.Active ℤ := fun v u =>
  st.basis.repr (Submodule.Quotient.mk (plan.activeRow v)) (Sum.inr u.1)

@[simp] theorem pivotMatrix_diag (plan : ForestPivotPlan st R)
    (v : plan.Active) : plan.pivotMatrix v v = 1 := by
  exact (plan.chosenRow_spec (plan.parent_activeParent v)).1


theorem rank_lt_of_pivotMatrix_ne_zero (plan : ForestPivotPlan st R)
    {v u : plan.Active} (hvu : plan.pivotMatrix v u ≠ 0) :
    u = v ∨ plan.rank (some u.1) < plan.rank (some v.1) := by
  classical
  let hp := plan.parent_activeParent v
  have hs := plan.chosenRow_spec hp
  change st.basis.repr (Submodule.Quotient.mk (plan.chosenRow hp))
    (Sum.inr u.1) ≠ 0 at hvu
  by_cases huv : u.1 = v.1
  · exact Or.inl (Subtype.ext huv)
  · let u' : {x : V // x ≠ v.1} := ⟨u.1, huv⟩
    have hu := hs.2.1 u'
    by_cases hpu : plan.chosenPivotParent hp = some u'
    · have hy : plan.activeParent v = some u.1 := by
        have hm := hs.2.2.1
        simpa [hpu, u'] using hm.symm
      right
      have hp' : plan.parent v.1 = some (some u.1) := hp.trans (congrArg some hy)
      exact plan.decreases v.1 (some u.1) hp'
    · rw [if_neg hpu] at hu
      exact absurd hu hvu


theorem pivotMatrix_det_eq_one (plan : ForestPivotPlan st R) :
    (plan.pivotMatrix).det = 1 := by
  classical
  let e : plan.Active ≃ Fin (Fintype.card plan.Active) := Fintype.equivFin plan.Active
  let key : plan.Active → (ℕ ×ₗ Fin (Fintype.card plan.Active)) := fun v =>
    toLex (plan.rank (some v.1), e v)
  letI : LinearOrder plan.Active := LinearOrder.lift' key (by
    intro u v huv
    apply e.injective
    exact congrArg (fun z => (ofLex z).2) huv)
  have htri : (plan.pivotMatrix).BlockTriangular OrderDual.toDual := by
    intro i j hij
    by_contra hn
    rcases plan.rank_lt_of_pivotMatrix_ne_zero hn with hji | hrank
    · subst j
      exact (lt_irrefl _ hij)
    · have hij' : i < j := by exact hij
      change key i < key j at hij'
      have hrle : plan.rank (some i.1) ≤ plan.rank (some j.1) :=
        (Prod.Lex.lt_iff'.mp hij').1
      omega
  rw [Matrix.det_of_lowerTriangular _ htri]
  simp

theorem pivotMatrix_isUnit (plan : ForestPivotPlan st R) :
    IsUnit (plan.pivotMatrix).det := by
  rw [plan.pivotMatrix_det_eq_one]
  exact isUnit_one

theorem chosenPivotParent_eq_none (plan : ForestPivotPlan st R) {v : V}
    (h : plan.parent v = some none) : plan.chosenPivotParent h = none := by
  have hm := (plan.chosenRow_spec h).2.2.1
  cases hp : plan.chosenPivotParent h with
  | none => rfl
  | some u =>
      rw [hp] at hm
      simp at hm

theorem chosenPivotParent_of_live (plan : ForestPivotPlan st R) {v w : V}
    (h : plan.parent v = some (some w)) :
    ∃ (hwv : w ≠ v), plan.chosenPivotParent h = some ⟨w, hwv⟩ := by
  have hm := (plan.chosenRow_spec h).2.2.1
  cases hp : plan.chosenPivotParent h with
  | none =>
      rw [hp] at hm
      simp at hm
  | some u =>
      have huw : u.1 = w := by
        simpa [hp] using hm
      subst w
      exact ⟨u.2, congrArg some (Subtype.ext rfl)⟩


theorem chosenRow_live_core_parent (plan : ForestPivotPlan st R) {v : V}
    (h : plan.parent v = some none) :
    (fun u => st.basis.repr (Submodule.Quotient.mk (plan.chosenRow h))
      (Sum.inr u)) = Pi.single v 1 := by
  have hs := plan.chosenRow_spec h
  have hp := plan.chosenPivotParent_eq_none h
  funext u
  by_cases huv : u = v
  · subst u
    simpa [Pi.single_apply] using hs.1
  · let u' : {u : V // u ≠ v} := ⟨u, huv⟩
    have hu := hs.2.1 u'
    simp [hp, huv, u'] at hu ⊢
    exact hu


theorem chosenRow_live_live_parent (plan : ForestPivotPlan st R) {v w : V}
    (h : plan.parent v = some (some w)) :
    (fun u => st.basis.repr (Submodule.Quotient.mk (plan.chosenRow h))
      (Sum.inr u)) = Pi.single v 1 - Pi.single w 1 := by
  obtain ⟨hwv, hp⟩ := plan.chosenPivotParent_of_live h
  have hs := plan.chosenRow_spec h
  funext u
  by_cases huv : u = v
  · subst u
    simpa [Pi.single_apply, Ne.symm hwv] using hs.1
  · let u' : {u : V // u ≠ v} := ⟨u, huv⟩
    have hu := hs.2.1 u'
    by_cases huw : u = w
    · subst u
      have heq : (⟨w, hwv⟩ : {u : V // u ≠ v}) = u' := Subtype.ext rfl
      simp [hp, heq, hwv, u'] at hu ⊢
      exact hu
    · have hne : some ⟨w, hwv⟩ ≠ some u' := by
        intro e
        exact huw (congrArg Subtype.val (Option.some.inj e)).symm
      simp [hp, hne, huv, huw, u'] at hu ⊢
      exact hu


def rootImage (plan : ForestPivotPlan st R) (v : V) : plan.Roots → ℤ :=
  match plan.terminalRoot v with
  | none => 0
  | some w => Pi.single w 1


noncomputable def coreImage (plan : ForestPivotPlan st R) (v : V) : C → ℤ :=
  match h : plan.parent v with
  | none => 0
  | some none => fun c =>
      -st.basis.repr (Submodule.Quotient.mk (plan.chosenRow h)) (Sum.inl c)
  | some (some w) => fun c => plan.coreImage w c -
      st.basis.repr (Submodule.Quotient.mk (plan.chosenRow h)) (Sum.inl c)
termination_by plan.rank (some v)
decreasing_by exact plan.decreases v (some w) h

@[simp] theorem rootImage_of_root (plan : ForestPivotPlan st R)
    (v : plan.Roots) : plan.rootImage v.1 = Pi.single v 1 := by
  simp [rootImage]

@[simp] theorem coreImage_of_root (plan : ForestPivotPlan st R)
    (v : plan.Roots) : plan.coreImage v.1 = 0 := by
  rw [coreImage]
  split <;> rename_i hpar
  · rfl
  · rw [v.2] at hpar
    contradiction
  · rw [v.2] at hpar
    contradiction

theorem rootImage_of_core_parent (plan : ForestPivotPlan st R) {v : V}
    (h : plan.parent v = some none) : plan.rootImage v = 0 := by
  simp [rootImage, plan.terminalRoot_of_core_parent h]

theorem rootImage_of_live_parent (plan : ForestPivotPlan st R) {v w : V}
    (h : plan.parent v = some (some w)) :
    plan.rootImage v = plan.rootImage w := by
  simp [rootImage, plan.terminalRoot_of_live_parent h]

theorem coreImage_of_core_parent (plan : ForestPivotPlan st R) {v : V}
    (h : plan.parent v = some none) (c : C) :
    plan.coreImage v c =
      -st.basis.repr (Submodule.Quotient.mk (plan.chosenRow h)) (Sum.inl c) := by
  have hf : plan.coreImage v = fun c =>
      -st.basis.repr (Submodule.Quotient.mk (plan.chosenRow h)) (Sum.inl c) := by
    rw [coreImage]
    split
    · rename_i heq
      simp [h] at heq
    · rfl
    · rename_i w' heq
      simp [h] at heq
  exact congrFun hf c

theorem coreImage_of_live_parent (plan : ForestPivotPlan st R) {v w : V}
    (h : plan.parent v = some (some w)) (c : C) :
    plan.coreImage v c = plan.coreImage w c -
      st.basis.repr (Submodule.Quotient.mk (plan.chosenRow h)) (Sum.inl c) := by
  have hf : plan.coreImage v = fun c => plan.coreImage w c -
      st.basis.repr (Submodule.Quotient.mk (plan.chosenRow h)) (Sum.inl c) := by
    rw [coreImage]
    split
    · rename_i heq
      simp [h] at heq
    · rename_i heq
      simp [h] at heq
    · rename_i w' heq
      have hw : w = w' := by simpa [h] using heq
      subst w'
      rfl
  exact congrFun hf c


theorem coreImage_norm_le_rank_mul (plan : ForestPivotPlan st R) (hR : 0 ≤ R)
    (v : V) :
    (∑ c : C, |plan.coreImage v c|) ≤ (plan.rank (some v) : ℤ) * R := by
  classical
  generalize hk : plan.rank (some v) = k
  induction k using Nat.strong_induction_on generalizing v with
  | h k ih =>
      subst k
      cases hpar : plan.parent v with
      | none =>
          let vr : plan.Roots := ⟨v, hpar⟩
          have hc := plan.coreImage_of_root vr
          have hcv : plan.coreImage v = 0 := by simpa [vr] using hc
          simp [hcv]
          exact mul_nonneg (Int.natCast_nonneg _) hR
      | some y =>
          cases y with
          | none =>
              have hlt := plan.decreases v none hpar
              have hone : (1 : ℤ) ≤ (plan.rank (some v) : ℤ) := by
                exact_mod_cast (show 1 ≤ plan.rank (some v) by omega)
              calc
                (∑ c : C, |plan.coreImage v c|) =
                    ∑ c : C, |st.basis.repr
                      (Submodule.Quotient.mk (plan.chosenRow hpar)) (Sum.inl c)| := by
                        apply Finset.sum_congr rfl
                        intro c hc
                        rw [plan.coreImage_of_core_parent hpar c]
                        simp
                _ ≤ R := plan.chosenRow_core_norm_le hpar
                _ = (1 : ℤ) * R := by ring
                _ ≤ (plan.rank (some v) : ℤ) * R :=
                  mul_le_mul_of_nonneg_right hone hR
          | some w =>
              have hlt := plan.decreases v (some w) hpar
              have hi := ih (plan.rank (some w)) (by omega) w rfl
              have hrank : (plan.rank (some w) : ℤ) + 1 ≤
                  (plan.rank (some v) : ℤ) := by
                exact_mod_cast (show plan.rank (some w) + 1 ≤ plan.rank (some v) by omega)
              calc
                (∑ c : C, |plan.coreImage v c|) ≤
                    ∑ c : C, (|plan.coreImage w c| +
                      |st.basis.repr (Submodule.Quotient.mk
                        (plan.chosenRow hpar)) (Sum.inl c)|) := by
                          apply Finset.sum_le_sum
                          intro c hc
                          rw [plan.coreImage_of_live_parent hpar c]
                          exact abs_sub _ _
                _ = (∑ c : C, |plan.coreImage w c|) +
                    ∑ c : C, |st.basis.repr (Submodule.Quotient.mk
                      (plan.chosenRow hpar)) (Sum.inl c)| := by
                        rw [Finset.sum_add_distrib]
                _ ≤ (plan.rank (some w) : ℤ) * R + R :=
                  add_le_add hi (plan.chosenRow_core_norm_le hpar)
                _ = ((plan.rank (some w) : ℤ) + 1) * R := by ring
                _ ≤ (plan.rank (some v) : ℤ) * R :=
                  mul_le_mul_of_nonneg_right hrank hR


theorem coreImage_norm_le_three_mul (plan : ForestPivotPlan st R) (hR : 0 ≤ R)
    (v : V) : (∑ c : C, |plan.coreImage v c|) ≤ 3 * R := by
  calc
    (∑ c : C, |plan.coreImage v c|) ≤ (plan.rank (some v) : ℤ) * R :=
      plan.coreImage_norm_le_rank_mul hR v
    _ ≤ 3 * R := mul_le_mul_of_nonneg_right (by exact_mod_cast plan.rank_le_three v) hR


noncomputable def forestMap (plan : ForestPivotPlan st R) :
    (Sum C V → ℤ) →ₗ[ℤ] (Sum C plan.Roots → ℤ) where
  toFun z
    | Sum.inl c => z (Sum.inl c) + ∑ v : V, z (Sum.inr v) * plan.coreImage v c
    | Sum.inr w => ∑ v : V, z (Sum.inr v) * plan.rootImage v w
  map_add' z z' := by
    funext i
    rcases i with c | w
    · simp only [Pi.add_apply]
      simp_rw [add_mul]
      rw [Finset.sum_add_distrib]
      ring
    · simp only [Pi.add_apply]
      simp_rw [add_mul]
      rw [Finset.sum_add_distrib]
  map_smul' k z := by
    funext i
    rcases i with c | w
    · simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
      calc
        k * z (Sum.inl c) + ∑ v : V,
            k * z (Sum.inr v) * plan.coreImage v c =
          k * z (Sum.inl c) + ∑ v : V,
            k * (z (Sum.inr v) * plan.coreImage v c) := by
              apply congrArg (fun x => k * z (Sum.inl c) + x)
              apply Finset.sum_congr rfl
              intro v hv
              ring
        _ = k * z (Sum.inl c) + k * ∑ v : V,
            z (Sum.inr v) * plan.coreImage v c := by rw [Finset.mul_sum]
        _ = k * (z (Sum.inl c) + ∑ v : V,
            z (Sum.inr v) * plan.coreImage v c) := by ring
    · simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
      calc
        (∑ v : V, k * z (Sum.inr v) * plan.rootImage v w) =
            ∑ v : V, k * (z (Sum.inr v) * plan.rootImage v w) := by
              apply Finset.sum_congr rfl
              intro v hv
              ring
        _ = k * ∑ v : V, z (Sum.inr v) * plan.rootImage v w := by
              rw [Finset.mul_sum]


theorem forestMap_surjective (plan : ForestPivotPlan st R) :
    Function.Surjective plan.forestMap := by
  classical
  intro x
  let z : Sum C V → ℤ
    | Sum.inl c => x (Sum.inl c)
    | Sum.inr v => if h : plan.parent v = none then x (Sum.inr ⟨v, h⟩) else 0
  refine ⟨z, ?_⟩
  funext i
  rcases i with c | w
  · change z (Sum.inl c) + ∑ v : V, z (Sum.inr v) * plan.coreImage v c =
      x (Sum.inl c)
    have hzero : ∑ v : V, z (Sum.inr v) * plan.coreImage v c = 0 := by
      apply Finset.sum_eq_zero
      intro v hv
      by_cases hroot : plan.parent v = none
      · let vr : plan.Roots := ⟨v, hroot⟩
        have hc := congrFun (plan.coreImage_of_root vr) c
        simp [z, hroot, vr, hc]
      · simp [z, hroot]
    rw [hzero, add_zero]
  · change (∑ v : V, z (Sum.inr v) * plan.rootImage v w) = x (Sum.inr w)
    rw [Finset.sum_eq_single w.1]
    · have hw := plan.rootImage_of_root w
      simp [z, w.2, hw]
    · intro v hv hvw
      by_cases hroot : plan.parent v = none
      · let vr : plan.Roots := ⟨v, hroot⟩
        have hvrw : vr ≠ w := by
          intro e
          exact hvw (congrArg Subtype.val e)
        have hr := plan.rootImage_of_root vr
        simp [z, hroot, vr, hr, hvrw]
      · simp [z, hroot]
    · simp

private theorem sum_single_mul (a : V) (f : V → ℤ) :
    ∑ x : V, (Pi.single a (1 : ℤ) : V → ℤ) x * f x = f a := by
  classical
  rw [Finset.sum_eq_single a]
  · simp
  · intro b hb hba
    simp [hba]
  · simp

private theorem sum_single_sub_mul (a b : V) (f : V → ℤ) :
    ∑ x : V, ((Pi.single a (1 : ℤ) : V → ℤ) -
      (Pi.single b (1 : ℤ) : V → ℤ)) x * f x = f a - f b := by
  simp_rw [Pi.sub_apply, sub_mul]
  rw [Finset.sum_sub_distrib, sum_single_mul, sum_single_mul]


theorem chosenRow_mem_ker_forestMap (plan : ForestPivotPlan st R)
    {v : V} {y : Option V} (h : plan.parent v = some y) :
    (fun i => st.basis.repr (Submodule.Quotient.mk (plan.chosenRow h)) i) ∈
      LinearMap.ker plan.forestMap := by
  classical
  rw [LinearMap.mem_ker]
  funext i
  rcases y with _ | w
  · have hlive := plan.chosenRow_live_core_parent h
    rcases i with c | q
    · change st.basis.repr (Submodule.Quotient.mk (plan.chosenRow h)) (Sum.inl c) +
          ∑ u : V, st.basis.repr (Submodule.Quotient.mk (plan.chosenRow h))
            (Sum.inr u) * plan.coreImage u c = 0
      simp_rw [congrFun hlive]
      rw [sum_single_mul, plan.coreImage_of_core_parent h c]
      ring
    · change (∑ u : V, st.basis.repr
          (Submodule.Quotient.mk (plan.chosenRow h)) (Sum.inr u) *
            plan.rootImage u q) = 0
      simp_rw [congrFun hlive]
      rw [sum_single_mul, plan.rootImage_of_core_parent h]
      rfl
  · have hlive := plan.chosenRow_live_live_parent h
    rcases i with c | q
    · change st.basis.repr (Submodule.Quotient.mk (plan.chosenRow h)) (Sum.inl c) +
          ∑ u : V, st.basis.repr (Submodule.Quotient.mk (plan.chosenRow h))
            (Sum.inr u) * plan.coreImage u c = 0
      simp_rw [congrFun hlive]
      rw [sum_single_sub_mul, plan.coreImage_of_live_parent h c]
      ring
    · change (∑ u : V, st.basis.repr
          (Submodule.Quotient.mk (plan.chosenRow h)) (Sum.inr u) *
            plan.rootImage u q) = 0
      simp_rw [congrFun hlive]
      rw [sum_single_sub_mul, plan.rootImage_of_live_parent h]
      ring


theorem eq_zero_of_mem_ker_of_active_zero (plan : ForestPivotPlan st R)
    (z : Sum C V → ℤ) (hz : z ∈ LinearMap.ker plan.forestMap)
    (hactive : ∀ v : plan.Active, z (Sum.inr v.1) = 0) : z = 0 := by
  classical
  have hmap : plan.forestMap z = 0 := LinearMap.mem_ker.mp hz
  have hlive : ∀ v : V, z (Sum.inr v) = 0 := by
    intro v
    by_cases hv : plan.parent v = none
    · let vr : plan.Roots := ⟨v, hv⟩
      have hout := congrFun hmap (Sum.inr vr)
      change (∑ u : V, z (Sum.inr u) * plan.rootImage u vr) = 0 at hout
      have hsum : (∑ u : V, z (Sum.inr u) * plan.rootImage u vr) =
          z (Sum.inr v) := by
        rw [Finset.sum_eq_single v]
        · have hr := plan.rootImage_of_root vr
          simp [vr, hr]
        · intro u hu huv
          by_cases huA : plan.parent u ≠ none
          · have hzA := hactive ⟨u, huA⟩
            simp [hzA]
          · have huR : plan.parent u = none := not_ne_iff.mp huA
            let ur : plan.Roots := ⟨u, huR⟩
            have hurne : ur ≠ vr := by
              intro e
              exact huv (congrArg Subtype.val e)
            have hr := plan.rootImage_of_root ur
            simp [ur, hr, hurne]
        · simp
      linarith
    · exact hactive ⟨v, hv⟩
  funext i
  rcases i with c | v
  · have hout := congrFun hmap (Sum.inl c)
    change z (Sum.inl c) + ∑ v : V, z (Sum.inr v) * plan.coreImage v c = 0 at hout
    have hsum : ∑ v : V, z (Sum.inr v) * plan.coreImage v c = 0 := by
      apply Finset.sum_eq_zero
      intro v hv
      rw [hlive v, zero_mul]
    rw [hsum, add_zero] at hout
    simpa using hout
  · simp [hlive v]

noncomputable def activeRowCoords (plan : ForestPivotPlan st R)
    (v : plan.Active) : Sum C V → ℤ := fun i =>
  st.basis.repr (Submodule.Quotient.mk (plan.activeRow v)) i

theorem activeRowCoords_mem_ker (plan : ForestPivotPlan st R)
    (v : plan.Active) : plan.activeRowCoords v ∈ LinearMap.ker plan.forestMap := by
  exact plan.chosenRow_mem_ker_forestMap (plan.parent_activeParent v)


theorem exists_activeRowCoords_sum (plan : ForestPivotPlan st R)
    (z : Sum C V → ℤ) (hz : z ∈ LinearMap.ker plan.forestMap) :
    ∃ k : plan.Active → ℤ,
      z = ∑ v : plan.Active, k v • plan.activeRowCoords v := by
  classical
  have hunit : IsUnit plan.pivotMatrix :=
    (Matrix.isUnit_iff_isUnit_det plan.pivotMatrix).mpr plan.pivotMatrix_isUnit
  let target : plan.Active → ℤ := fun u => z (Sum.inr u.1)
  obtain ⟨k, hk⟩ := (Matrix.vecMul_surjective_iff_isUnit.mpr hunit) target
  let q : Sum C V → ℤ := ∑ v : plan.Active, k v • plan.activeRowCoords v
  have hqker : q ∈ LinearMap.ker plan.forestMap := by
    apply Submodule.sum_mem
    intro v hv
    exact Submodule.smul_mem _ _ (plan.activeRowCoords_mem_ker v)
  have hqactive : ∀ u : plan.Active, q (Sum.inr u.1) = target u := by
    intro u
    have hku := congrFun hk u
    change (∑ v : plan.Active, k v * plan.pivotMatrix v u) = target u at hku
    change (∑ v : plan.Active, k v • plan.activeRowCoords v) (Sum.inr u.1) = target u
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, activeRowCoords,
      pivotMatrix, activeRow] using hku
  have hdker : z - q ∈ LinearMap.ker plan.forestMap :=
    (LinearMap.ker plan.forestMap).sub_mem hz hqker
  have hdactive : ∀ u : plan.Active, (z - q) (Sum.inr u.1) = 0 := by
    intro u
    change z (Sum.inr u.1) - q (Sum.inr u.1) = 0
    rw [hqactive u]
    simp [target]
  have hd0 := plan.eq_zero_of_mem_ker_of_active_zero (z - q) hdker hdactive
  refine ⟨k, ?_⟩
  exact sub_eq_zero.mp hd0


def contractedBlocks (plan : ForestPivotPlan st R) : LiveBlocks n plan.Roots where
  block w := Finset.univ.filter fun a =>
    st.blocks.owner a >>= plan.terminalRoot = some w
  owner a := st.blocks.owner a >>= plan.terminalRoot
  mem_block_iff a w := by simp
  nonempty w := by
    obtain ⟨a, ha⟩ := st.blocks.nonempty w.1
    refine ⟨a, ?_⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [(st.blocks.mem_block_iff a w.1).mp ha]
    simp

theorem contractedBlocks_mass_le (plan : ForestPivotPlan st R) :
    plan.contractedBlocks.mass ≤ st.blocks.mass := by
  classical
  have hnewdisj : (↑(Finset.univ : Finset plan.Roots) : Set plan.Roots).PairwiseDisjoint
      plan.contractedBlocks.block := by
    intro i hi j hj hij
    exact plan.contractedBlocks.disjoint hij
  have holddisj : (↑(Finset.univ : Finset V) : Set V).PairwiseDisjoint
      st.blocks.block := by
    intro i hi j hj hij
    exact st.blocks.disjoint hij
  have hsub : Finset.univ.biUnion plan.contractedBlocks.block ⊆
      Finset.univ.biUnion st.blocks.block := by
    intro a ha
    obtain ⟨w, hw, haw⟩ := Finset.mem_biUnion.mp ha
    have hterm := (Finset.mem_filter.mp haw).2
    cases howner : st.blocks.owner a with
    | none =>
        simp [howner] at hterm
    | some v =>
        apply Finset.mem_biUnion.mpr
        refine ⟨v, Finset.mem_univ _, ?_⟩
        exact (st.blocks.mem_block_iff a v).mpr howner
  calc
    plan.contractedBlocks.mass =
        (Finset.univ.biUnion plan.contractedBlocks.block).card :=
      (Finset.card_biUnion hnewdisj).symm
    _ ≤ (Finset.univ.biUnion st.blocks.block).card := Finset.card_le_card hsub
    _ = st.blocks.mass := Finset.card_biUnion holddisj


noncomputable def ambientForestMap (plan : ForestPivotPlan st R) :
    (Fin n → ℤ) →ₗ[ℤ] (Sum C plan.Roots → ℤ) :=
  plan.forestMap.comp
    (st.basis.equivFun.toLinearMap.comp (st.Q.mkQ : (Fin n → ℤ) →ₗ[ℤ] _))

theorem ambientForestMap_surjective (plan : ForestPivotPlan st R) :
    Function.Surjective plan.ambientForestMap := by
  intro z
  obtain ⟨w, hw⟩ := plan.forestMap_surjective z
  obtain ⟨q, hq⟩ := st.basis.equivFun.surjective w
  obtain ⟨x, hx⟩ := Submodule.mkQ_surjective st.Q q
  refine ⟨x, ?_⟩
  change plan.forestMap (st.basis.equivFun (st.Q.mkQ x)) = z
  rw [hx, hq, hw]


noncomputable def contract (plan : ForestPivotPlan st R) :
    CompressionState S P C plan.Roots := by
  let f := plan.ambientForestMap
  have hf : Function.Surjective f := plan.ambientForestMap_surjective
  let e : ((Fin n → ℤ) ⧸ LinearMap.ker f) ≃ₗ[ℤ]
      (Sum C plan.Roots → ℤ) := f.quotKerEquivOfSurjective hf
  let b : Module.Basis (Sum C plan.Roots) ℤ
      ((Fin n → ℤ) ⧸ LinearMap.ker f) :=
    (Pi.basisFun ℤ (Sum C plan.Roots)).map e.symm
  refine
    { Q := LinearMap.ker f
      le_colLat := ?_
      primitive := ker_primitive f
      basis := b
      blocks := plan.contractedBlocks
      live_coord := ?_ }
  · intro x hx
    have hx0 : f x = 0 := LinearMap.mem_ker.mp hx
    let z : Sum C V → ℤ := st.basis.equivFun (Submodule.Quotient.mk x)
    have hz : z ∈ LinearMap.ker plan.forestMap := by
      rw [LinearMap.mem_ker]
      exact hx0
    obtain ⟨k, hk⟩ := plan.exists_activeRowCoords_sum z hz
    let q : Fin n → ℤ := ∑ v : plan.Active, k v • plan.activeRow v
    have hqmem : q ∈ S.colLat P := by
      apply Submodule.sum_mem
      intro v hv
      exact (S.colLat P).smul_mem _ (plan.activeRow_mem v)
    have hqcoord : st.basis.equivFun (Submodule.Quotient.mk q) =
        ∑ v : plan.Active, k v • plan.activeRowCoords v := by
      change st.basis.equivFun (st.Q.mkQ
        (∑ v : plan.Active, k v • plan.activeRow v)) = _
      rw [map_sum]
      simp_rw [map_smul]
      ext i
      simp [Finset.sum_apply, activeRowCoords, activeRow]
    have hquot : (Submodule.Quotient.mk x : (Fin n → ℤ) ⧸ st.Q) =
        Submodule.Quotient.mk q := by
      apply st.basis.equivFun.injective
      rw [hqcoord]
      exact hk
    have hdiff : x - q ∈ st.Q := by
      have hquot' : st.Q.mkQ x = st.Q.mkQ q := hquot
      rw [← Submodule.ker_mkQ st.Q, LinearMap.mem_ker, map_sub, hquot', sub_self]
    have hdiff' := st.le_colLat hdiff
    have hadd := (S.colLat P).add_mem hdiff' hqmem
    (convert hadd using 1; module)
  · intro a w
    simp only [b, Module.Basis.map_repr, LinearEquiv.trans_apply, Pi.basisFun_repr,
      e]
    change (∑ v : V,
      st.basis.repr (Submodule.Quotient.mk (Pi.single a 1)) (Sum.inr v) *
        plan.rootImage v w) = _
    rcases howner : st.blocks.owner a with _ | v
    · have hzero : ∑ v : V,
          st.basis.repr (Submodule.Quotient.mk (Pi.single a 1)) (Sum.inr v) *
            plan.rootImage v w = 0 := by
        apply Finset.sum_eq_zero
        intro v hv
        rw [st.live_coord]
        simp [howner]
      rw [hzero]
      simp [contractedBlocks, howner]
    · rw [Finset.sum_eq_single v]
      · rw [st.live_coord]
        by_cases hr : plan.terminalRoot v = some w
        · have hri : plan.rootImage v w = 1 := by
            simp [rootImage, hr]
          simp [contractedBlocks, howner, hr, hri]
        · have hri : plan.rootImage v w = 0 := by
            rcases htr : plan.terminalRoot v with _ | q
            · simp [rootImage, htr]
            · have hqw : q ≠ w := by
                intro e
                apply hr
                rw [htr, e]
              simp [rootImage, htr, hqw]
          simp [contractedBlocks, howner, hr, hri]
      · intro u hu huv
        rw [st.live_coord]
        simp [howner, Ne.symm huv]
      · simp


theorem contract_core_coord (plan : ForestPivotPlan st R) (a : Fin n) (c : C) :
    (plan.contract).basis.repr (Submodule.Quotient.mk (Pi.single a 1)) (Sum.inl c) =
      st.basis.repr (Submodule.Quotient.mk (Pi.single a 1)) (Sum.inl c) +
        ∑ v : V, st.basis.repr (Submodule.Quotient.mk (Pi.single a 1))
          (Sum.inr v) * plan.coreImage v c := by
  simp only [contract, Module.Basis.map_repr]
  rfl


theorem contract_coreBound (plan : ForestPivotPlan st R) {M : ℤ}
    (hM : st.CoreBound M) (hR : 0 ≤ R) :
    plan.contract.CoreBound (M + 3 * R) := by
  classical
  intro a
  simp_rw [plan.contract_core_coord a]
  have hcorr :
      (∑ c : C, |∑ v : V,
        st.basis.repr (Submodule.Quotient.mk (Pi.single a 1)) (Sum.inr v) *
          plan.coreImage v c|) ≤ 3 * R := by
    cases howner : st.blocks.owner a with
    | none =>
        have hz : ∀ v : V,
            st.basis.repr (Submodule.Quotient.mk (Pi.single a 1)) (Sum.inr v) = 0 := by
          intro v
          rw [st.live_coord]
          simp [howner]
        simp_rw [hz]
        simpa using (mul_nonneg (show (0 : ℤ) ≤ 3 by norm_num) hR)
    | some w =>
        have hsum : ∀ c : C,
            (∑ v : V,
              st.basis.repr (Submodule.Quotient.mk (Pi.single a 1)) (Sum.inr v) *
                plan.coreImage v c) = plan.coreImage w c := by
          intro c
          rw [Finset.sum_eq_single w]
          · rw [st.live_coord]
            simp [howner]
          · intro v hv hvw
            rw [st.live_coord]
            simp [howner, Ne.symm hvw]
          · simp
        simp_rw [hsum]
        exact plan.coreImage_norm_le_three_mul hR w
  calc
    (∑ c : C,
      |st.basis.repr (Submodule.Quotient.mk (Pi.single a 1)) (Sum.inl c) +
        ∑ v : V, st.basis.repr (Submodule.Quotient.mk (Pi.single a 1))
          (Sum.inr v) * plan.coreImage v c|) ≤
        (∑ c : C,
          |st.basis.repr (Submodule.Quotient.mk (Pi.single a 1)) (Sum.inl c)|) +
        ∑ c : C, |∑ v : V,
          st.basis.repr (Submodule.Quotient.mk (Pi.single a 1)) (Sum.inr v) *
            plan.coreImage v c| := by
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_le_sum
              intro c hc
              exact abs_add_le _ _
    _ ≤ M + 3 * R := add_le_add (hM a) hcorr


noncomputable def finishRound (plan : ForestPivotPlan st R) (L : ℕ) :=
  plan.contract.promote (plan.contract.blocks.heavy L)

theorem finishRound_coreBound (plan : ForestPivotPlan st R) (L : ℕ) {M : ℤ}
    (hM : plan.contract.CoreBound M) : plan.finishRound L |>.CoreBound (M + 1) := by
  exact plan.contract.promote_coreBound _ hM

theorem finishRound_blocks_light (plan : ForestPivotPlan st R) (L : ℕ)
    (v : {v : plan.Roots // v ∉ plan.contract.blocks.heavy L}) :
    ((plan.finishRound L).blocks.block v).card < L := by
  exact plan.contract.blocks.promote_heavy_is_light L v

theorem finishRound_mass_add_heavy_le (plan : ForestPivotPlan st R) (L : ℕ) :
    (plan.finishRound L).blocks.mass +
        L * (plan.contract.blocks.heavy L).card ≤ st.blocks.mass := by
  have hremoved := plan.contract.blocks.heavy_card_mul_le_removed L
  have hsplit := plan.contract.blocks.mass_promote_add_removed
    (plan.contract.blocks.heavy L)
  have hcontract := plan.contractedBlocks_mass_le
  calc
    (plan.finishRound L).blocks.mass +
        L * (plan.contract.blocks.heavy L).card ≤
      (plan.finishRound L).blocks.mass +
        ∑ v ∈ plan.contract.blocks.heavy L,
          (plan.contract.blocks.block v).card := Nat.add_le_add_left hremoved _
    _ = plan.contract.blocks.mass := hsplit
    _ ≤ st.blocks.mass := hcontract

end ForestPivotPlan


theorem CompressionState.exists_bounded_forest_contract {p n : ℕ}
    {S : MinimalNUS p n} {P : S.Pairing} {C V : Type*}
    [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]
    (st : CompressionState S P C V) {M R : ℤ} (hM : st.CoreBound M)
    (hR : 0 ≤ R) (f : ℕ)
    (hf : (st.isolatedLive R).card ≤ f) :
    ∃ plan : ForestPivotPlan st R,
      2 * Fintype.card plan.Roots ≤ Fintype.card V + f ∧
      plan.contract.CoreBound (M + 3 * R) := by
  classical
  letI : DecidableRel (st.unitGraph R).Adj := Classical.decRel _
  have hf' : (Finset.univ.filter fun v : V =>
      ∀ w, ¬(st.unitGraph R).Adj (some v) w).card ≤ f := by
    simpa [CompressionState.isolatedLive] using hf
  obtain ⟨F, hFG, hacyc, hcount, plan, hroots⟩ :=
    st.exists_forestPivotPlan R f hf'
  exact ⟨plan, hroots, plan.contract_coreBound hM hR⟩


theorem CompressionState.exists_contract_after_sample {p n : ℕ}
    {S : MinimalNUS p n} {P : S.Pairing} {C V : Type*}
    [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]
    (st : CompressionState S P C V) {M : ℤ} (hM : st.CoreBound M) (hM1 : 1 ≤ M)
    (T : Finset V)
    (hiso : 8 * ((st.promote T).isolatedLive (8 * M)).card ≤ Fintype.card V) :
    ∃ plan : ForestPivotPlan (st.promote T) (8 * M),
      3 * Fintype.card plan.Roots ≤ 2 * Fintype.card V ∧
      plan.contract.CoreBound (26 * M) := by
  classical
  let f := Fintype.card V / 8
  have hf : ((st.promote T).isolatedLive (8 * M)).card ≤ f := by
    have hle : ((st.promote T).isolatedLive (8 * M)).card ≤ f := by
      dsimp [f]
      omega
    exact hle
  have hpM : (st.promote T).CoreBound (M + 1) := st.promote_coreBound T hM
  have hR : (0 : ℤ) ≤ 8 * M := by
    have hM0 : (0 : ℤ) ≤ M := le_trans (by norm_num) hM1
    positivity
  obtain ⟨plan, hcard, hcore⟩ :=
    (st.promote T).exists_bounded_forest_contract hpM hR f hf
  refine ⟨plan, ?_, ?_⟩
  · have hsub : Fintype.card {v : V // v ∉ T} ≤ Fintype.card V :=
      Fintype.card_subtype_le _
    dsimp [f] at hcard
    omega
  · intro a
    exact le_trans (hcore a) (by nlinarith)


theorem DepartingSystem.exists_low_anchor_contract {p n : ℕ}
    {S : MinimalNUS p n} {P : S.Pairing} {C V : Type*}
    [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]
    (st : CompressionState S P C V) {M : ℤ} (hM : st.CoreBound M)
    (D : DepartingSystem P st.blocks) (i : V) (hnd : ¬D.IsDirectAnchor i)
    (heasy : 8 * (D.easyLabels i).card < Fintype.card V)
    (htypes : 8 * (D.properTypes i).card < Fintype.card V)
    (hm : 12 ≤ Fintype.card V) :
    ∃ plan : ForestPivotPlan st (8 * M),
      3 * Fintype.card plan.Roots ≤ 2 * Fintype.card V ∧
      plan.contract.CoreBound (25 * M) := by
  classical
  let f := Fintype.card V / 4 + 1
  have hiso : (st.isolatedLive (8 * M)).card ≤ f := by
    have h := D.isolatedLive_card_le_anchor st hM i hnd
    dsimp [f]
    omega
  have hf : (st.isolatedLive (8 * M)).card ≤ f := hiso
  have hR : (0 : ℤ) ≤ 8 * M := by
    have hM0 := st.coreBound_nonneg hM
    positivity
  obtain ⟨plan, hcard, hcore⟩ :=
    st.exists_bounded_forest_contract hM hR f hf
  refine ⟨plan, ?_, ?_⟩
  · dsimp [f] at hcard
    omega
  · (convert hcore using 1; ring)


structure PackedCompressionState {p n : ℕ} (S : MinimalNUS p n) (P : S.Pairing) where
  C : Type
  V : Type
  fintypeC : Fintype C
  decEqC : DecidableEq C
  fintypeV : Fintype V
  decEqV : DecidableEq V
  st : @CompressionState p n S P C V fintypeC decEqC fintypeV decEqV

instance PackedCompressionState.instFintypeC {p n : ℕ} {S : MinimalNUS p n} {P : S.Pairing} (X : PackedCompressionState S P) : Fintype X.C := X.fintypeC
instance PackedCompressionState.instDecEqC {p n : ℕ} {S : MinimalNUS p n} {P : S.Pairing} (X : PackedCompressionState S P) : DecidableEq X.C := X.decEqC
instance PackedCompressionState.instFintypeV {p n : ℕ} {S : MinimalNUS p n} {P : S.Pairing} (X : PackedCompressionState S P) : Fintype X.V := X.fintypeV
instance PackedCompressionState.instDecEqV {p n : ℕ} {S : MinimalNUS p n} {P : S.Pairing} (X : PackedCompressionState S P) : DecidableEq X.V := X.decEqV

namespace PackedCompressionState

variable {p n : ℕ} {S : MinimalNUS p n} {P : S.Pairing}

private theorem sqrt_le_five_six_of_shrink {a b : ℕ} (h : 3 * a ≤ 2 * b) :
    Real.sqrt a ≤ (5 / 6 : ℝ) * Real.sqrt b := by
  have ha0 : (0 : ℝ) ≤ Real.sqrt a := Real.sqrt_nonneg _
  have hb0 : (0 : ℝ) ≤ Real.sqrt b := Real.sqrt_nonneg _
  have ha2 : (Real.sqrt a) ^ 2 = (a : ℝ) := Real.sq_sqrt (by positivity)
  have hb2 : (Real.sqrt b) ^ 2 = (b : ℝ) := Real.sq_sqrt (by positivity)
  have hr : (3 : ℝ) * a ≤ 2 * b := by exact_mod_cast h
  nlinarith

private theorem sqrt_le_two_thirds_of_two_shrinks {a b c : ℕ}
    (h₁ : 3 * b ≤ 2 * a) (h₂ : 3 * c ≤ 2 * b) :
    Real.sqrt c ≤ (2 / 3 : ℝ) * Real.sqrt a := by
  have ha0 : (0 : ℝ) ≤ Real.sqrt a := Real.sqrt_nonneg _
  have hc0 : (0 : ℝ) ≤ Real.sqrt c := Real.sqrt_nonneg _
  have ha2 : (Real.sqrt a) ^ 2 = (a : ℝ) := Real.sq_sqrt (by positivity)
  have hc2 : (Real.sqrt c) ^ 2 = (c : ℝ) := Real.sq_sqrt (by positivity)
  have hr₁ : (3 : ℝ) * b ≤ 2 * a := by exact_mod_cast h₁
  have hr₂ : (3 : ℝ) * c ≤ 2 * b := by exact_mod_cast h₂
  nlinarith

def coreCard (X : PackedCompressionState S P) : ℕ := @Fintype.card X.C X.fintypeC
def liveCard (X : PackedCompressionState S P) : ℕ := @Fintype.card X.V X.fintypeV
def mass (X : PackedCompressionState S P) : ℕ := @LiveBlocks.mass n X.V X.fintypeV X.st.blocks

noncomputable def initial (S : MinimalNUS p n) (P : S.Pairing) :
    PackedCompressionState S P where
  C := Empty
  V := Fin n
  fintypeC := inferInstance
  decEqC := inferInstance
  fintypeV := inferInstance
  decEqV := inferInstance
  st := initialCompressionState S P

structure RoundResult (X : PackedCompressionState S P) (M : ℤ) (L : ℕ) (D₀ : ℝ) where
  next : PackedCompressionState S P
  sampleCost : ℕ
  heavyCost : ℕ
  coreCard_eq : next.coreCard = X.coreCard + sampleCost + heavyCost
  live_shrink : 3 * next.liveCard ≤ 2 * X.liveCard
  sample_bound : (sampleCost : ℝ) ≤ D₀ * Real.sqrt X.liveCard
  coreBound : next.st.CoreBound (30 * M)
  light : ∀ v, (next.st.blocks.block v).card < L
  mass_charge : next.mass + L * heavyCost ≤ X.mass

structure IterationResult (X : PackedCompressionState S P) (M : ℤ)
    (L mstar : ℕ) (D₀ : ℝ) where
  final : PackedCompressionState S P
  rounds : ℕ
  sampleCost : ℕ
  heavyCost : ℕ
  terminal : final.liveCard < mstar
  coreCard_eq : final.coreCard = X.coreCard + sampleCost + heavyCost
  sample_bound : (sampleCost : ℝ) ≤ 12 * D₀ * Real.sqrt X.liveCard
  mass_charge : final.mass + L * heavyCost ≤ X.mass
  coreBound : final.st.CoreBound (30 ^ rounds * M)
  light : ∀ v, (final.st.blocks.block v).card < L
  rounds_le : rounds ≤ 2 * Nat.log 2 X.liveCard + 2


theorem exists_round_result (D₀ : ℝ) (m₀ : ℕ) (hD₀ : 0 < D₀)
    (hhigh : ∀ {p n : ℕ} {S : MinimalNUS p n} {P : S.Pairing} {C V : Type}
      [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]
      (st : CompressionState S P C V) {M : ℤ}, st.CoreBound M → 1 ≤ M →
      (D : DepartingSystem P st.blocks) → max m₀ 16 ≤ Fintype.card V →
      (∀ i, ¬D.IsDirectAnchor i →
        Fintype.card V ≤ 8 * (D.easyLabels i).card ∨
        Fintype.card V ≤ 8 * (D.properTypes i).card) →
      ∃ T : Finset V, (T.card : ℝ) ≤ D₀ * Real.sqrt (Fintype.card V) ∧
        8 * ((st.promote T).isolatedLive (8 * M)).card ≤ Fintype.card V)
    [Fact p.Prime] (X : PackedCompressionState S P) (M : ℤ) (hM : X.st.CoreBound M)
    (hM1 : 1 ≤ M) (hp : 64 ≤ p)
    (L : ℕ) (hL : L = Nat.log 2 p / 3)
    (hlight : ∀ v, (X.st.blocks.block v).card < L)
    (hm : max m₀ 16 ≤ X.liveCard) : Nonempty (RoundResult X M L D₀) := by
  classical
  letI : Fintype X.C := X.fintypeC
  letI : DecidableEq X.C := X.decEqC
  letI : Fintype X.V := X.fintypeV
  letI : DecidableEq X.V := X.decEqV
  have hpower : ∀ e : OrderedDistinct X.V,
      2 ^ ((X.st.blocks.block e.1.1).card + (X.st.blocks.block e.1.2).card - 2) < p := by
    apply light_blocks_power_lt X.st.blocks hp
    simpa [hL] using hlight
  let D : DepartingSystem P X.st.blocks := Classical.choice
    (exists_departingSystem S P X.st.blocks hpower)
  by_cases hlow : ∃ i : X.V, ¬D.IsDirectAnchor i ∧
      8 * (D.easyLabels i).card < Fintype.card X.V ∧
      8 * (D.properTypes i).card < Fintype.card X.V
  · obtain ⟨i, hnd, heasy, htypes⟩ := hlow
    obtain ⟨plan, hshrink, hcore⟩ := D.exists_low_anchor_contract X.st hM i hnd
      heasy htypes (by
        change 12 ≤ X.liveCard
        exact le_trans (by omega) hm)
    let H := plan.contract.blocks.heavy L
    let Y : PackedCompressionState S P :=
      { C := Sum X.C {v : plan.Roots // v ∈ H}
        V := {v : plan.Roots // v ∉ H}
        fintypeC := inferInstance
        decEqC := inferInstance
        fintypeV := inferInstance
        decEqV := inferInstance
        st := plan.finishRound L }
    refine ⟨⟨Y, 0, H.card, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · dsimp [Y, coreCard]
      rw [Fintype.card_sum, Fintype.card_subtype]
      simp [H]
    · have hsub : Fintype.card {v : plan.Roots // v ∉ H} ≤
          Fintype.card plan.Roots := Fintype.card_subtype_le _
      dsimp [Y, liveCard]
      omega
    · simp
      positivity
    · have hc := plan.finishRound_coreBound L hcore
      intro a
      exact le_trans (hc a) (by nlinarith)
    · exact plan.finishRound_blocks_light L
    · exact plan.finishRound_mass_add_heavy_le L
  · have hall : ∀ i : X.V, ¬D.IsDirectAnchor i →
        Fintype.card X.V ≤ 8 * (D.easyLabels i).card ∨
        Fintype.card X.V ≤ 8 * (D.properTypes i).card := by
      intro i hnd
      have hn : ¬(8 * (D.easyLabels i).card < Fintype.card X.V ∧
          8 * (D.properTypes i).card < Fintype.card X.V) := by
        intro hb
        exact hlow ⟨i, hnd, hb.1, hb.2⟩
      omega
    obtain ⟨T, hT, hiso⟩ := hhigh X.st hM hM1 D (by simpa [liveCard] using hm) hall
    obtain ⟨plan, hshrink, hcore⟩ := X.st.exists_contract_after_sample hM hM1 T hiso
    let H := plan.contract.blocks.heavy L
    let Y : PackedCompressionState S P :=
      { C := Sum (Sum X.C {v : X.V // v ∈ T}) {v : plan.Roots // v ∈ H}
        V := {v : plan.Roots // v ∉ H}
        fintypeC := inferInstance
        decEqC := inferInstance
        fintypeV := inferInstance
        decEqV := inferInstance
        st := plan.finishRound L }
    refine ⟨⟨Y, T.card, H.card, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · dsimp [Y, coreCard]
      rw [Fintype.card_sum, Fintype.card_sum, Fintype.card_subtype,
        Fintype.card_subtype]
      simp [H]
    · have hsub : Fintype.card {v : plan.Roots // v ∉ H} ≤
          Fintype.card plan.Roots := Fintype.card_subtype_le _
      dsimp [Y, liveCard]
      omega
    · simpa [PackedCompressionState.liveCard] using hT
    · have hc := plan.finishRound_coreBound L hcore
      intro a
      exact le_trans (hc a) (by nlinarith)
    · exact plan.finishRound_blocks_light L
    · have hplan := plan.finishRound_mass_add_heavy_le L
      have hpromEq := X.st.blocks.mass_promote_add_removed T
      have hprom : (X.st.promote T).blocks.mass ≤ X.st.blocks.mass :=
        Nat.le.intro hpromEq
      exact le_trans hplan hprom


theorem iterate_round_results (D₀ : ℝ) (hD₀ : 0 < D₀) (L mstar : ℕ)
    (hmstar16 : 16 ≤ mstar)
    (hstep : ∀ (X : PackedCompressionState S P) (M : ℤ),
      X.st.CoreBound M → 1 ≤ M →
      (∀ v, (X.st.blocks.block v).card < L) →
      mstar ≤ X.liveCard → Nonempty (RoundResult X M L D₀))
    (X : PackedCompressionState S P) (M : ℤ) (hM : X.st.CoreBound M)
    (hM1 : 1 ≤ M) (hlight : ∀ v, (X.st.blocks.block v).card < L) :
    Nonempty (IterationResult X M L mstar D₀) := by
  classical
  generalize hk : Nat.log 2 X.liveCard = k
  induction k using Nat.strong_induction_on generalizing X M with
  | h k ih =>
      subst k
      by_cases hterm : X.liveCard < mstar
      · refine ⟨
          { final := X
            rounds := 0
            sampleCost := 0
            heavyCost := 0
            terminal := hterm
            coreCard_eq := by simp
            sample_bound := by simp; positivity
            mass_charge := by simp
            coreBound := by simpa using hM
            light := hlight
            rounds_le := by omega }⟩
      · have hmstar : mstar ≤ X.liveCard := Nat.le_of_not_gt hterm
        let r₁ := Classical.choice (hstep X M hM hM1 hlight hmstar)
        by_cases hterm₁ : r₁.next.liveCard < mstar
        · refine ⟨
            { final := r₁.next
              rounds := 1
              sampleCost := r₁.sampleCost
              heavyCost := r₁.heavyCost
              terminal := hterm₁
              coreCard_eq := r₁.coreCard_eq
              sample_bound := by
                have hs := r₁.sample_bound
                have hsqrt : 0 ≤ Real.sqrt X.liveCard := Real.sqrt_nonneg _
                nlinarith
              mass_charge := r₁.mass_charge
              coreBound := by
                (convert r₁.coreBound using 1; norm_num)
              light := r₁.light
              rounds_le := by omega }⟩
        · have hmstar₁ : mstar ≤ r₁.next.liveCard := Nat.le_of_not_gt hterm₁
          have hM₁ : 1 ≤ 30 * M := by nlinarith
          let r₂ := Classical.choice
            (hstep r₁.next (30 * M) r₁.coreBound hM₁ r₁.light hmstar₁)
          by_cases hterm₂ : r₂.next.liveCard < mstar
          · refine ⟨
              { final := r₂.next
                rounds := 2
                sampleCost := r₁.sampleCost + r₂.sampleCost
                heavyCost := r₁.heavyCost + r₂.heavyCost
                terminal := hterm₂
                coreCard_eq := by
                  rw [r₂.coreCard_eq, r₁.coreCard_eq]
                  omega
                sample_bound := by
                  have hs₁ := r₁.sample_bound
                  have hs₂ := r₂.sample_bound
                  have hsqrt := sqrt_le_five_six_of_shrink r₁.live_shrink
                  have hsqrtD := mul_le_mul_of_nonneg_left hsqrt hD₀.le
                  have hroot : 0 ≤ Real.sqrt X.liveCard := Real.sqrt_nonneg _
                  norm_num [Nat.cast_add] at ⊢
                  nlinarith
                mass_charge := by
                  have h₁ := r₁.mass_charge
                  have h₂ := r₂.mass_charge
                  rw [Nat.mul_add]
                  omega
                coreBound := by
                  (convert r₂.coreBound using 1; norm_num; ring)
                light := r₂.light
                rounds_le := by omega }⟩
          · have hmstar₂ : mstar ≤ r₂.next.liveCard := Nat.le_of_not_gt hterm₂
            have hm₂pos : r₂.next.liveCard ≠ 0 := by omega
            have hhalf : 2 * r₂.next.liveCard ≤ X.liveCard := by
              have h₁ := r₁.live_shrink
              have h₂ := r₂.live_shrink
              omega
            have hpow : 2 ^ (Nat.log 2 r₂.next.liveCard + 1) ≤ X.liveCard := by
              rw [pow_succ]
              have hp := Nat.pow_log_le_self 2 hm₂pos
              omega
            have hlog : Nat.log 2 r₂.next.liveCard < Nat.log 2 X.liveCard := by
              have hl := Nat.le_log_of_pow_le (by norm_num) hpow
              omega
            let fut := Classical.choice
              (ih (Nat.log 2 r₂.next.liveCard) hlog r₂.next (30 * (30 * M))
                r₂.coreBound (by nlinarith) r₂.light rfl)
            refine ⟨
              { final := fut.final
                rounds := fut.rounds + 2
                sampleCost := r₁.sampleCost + r₂.sampleCost + fut.sampleCost
                heavyCost := r₁.heavyCost + r₂.heavyCost + fut.heavyCost
                terminal := fut.terminal
                coreCard_eq := by
                  rw [fut.coreCard_eq, r₂.coreCard_eq, r₁.coreCard_eq]
                  omega
                sample_bound := by
                  have hs₁ := r₁.sample_bound
                  have hs₂ := r₂.sample_bound
                  have hsf := fut.sample_bound
                  have hsqrt₁ := sqrt_le_five_six_of_shrink r₁.live_shrink
                  have hsqrt₂ := sqrt_le_two_thirds_of_two_shrinks
                    r₁.live_shrink r₂.live_shrink
                  have hsqrtD₁ := mul_le_mul_of_nonneg_left hsqrt₁ hD₀.le
                  have hsqrtD₂ := mul_le_mul_of_nonneg_left hsqrt₂ hD₀.le
                  have hroot : 0 ≤ Real.sqrt X.liveCard := Real.sqrt_nonneg _
                  norm_cast at hs₁ hs₂ hsf
                  norm_num [Nat.cast_add] at ⊢
                  nlinarith
                mass_charge := by
                  have h₁ := r₁.mass_charge
                  have h₂ := r₂.mass_charge
                  have hf := fut.mass_charge
                  rw [Nat.mul_add, Nat.mul_add]
                  omega
                coreBound := by
                  have hc := fut.coreBound
                  convert hc using 1
                  rw [pow_add]
                  ring
                light := fut.light
                rounds_le := by
                  have hr := fut.rounds_le
                  omega }⟩

end PackedCompressionState




theorem CompressionState.finish_any {p n E : ℕ} {S : MinimalNUS p n} {P : S.Pairing}
    {C V : Type*} [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]
    (st : CompressionState S P C V) {M : ℤ} (hM : st.CoreBound M)
    (hcard : (((Fintype.card C + Fintype.card V : ℕ) : ℝ)) ≤
      E * (Real.sqrt n + n / Real.log p))
    (hnorm : M + 1 ≤ (n : ℤ) ^ E) :
    ∃ (K : ℕ) (Q : Submodule ℤ (Fin n → ℤ)),
      Q ≤ S.colLat P ∧
      (∀ (v : Fin n → ℤ) (c : ℤ), c ≠ 0 → c • v ∈ Q → v ∈ Q) ∧
      Module.finrank ℤ Q = n - K ∧
      ((K : ℝ) ≤ E * (Real.sqrt n + n / Real.log p)) ∧
      ∃ b : Module.Basis (Fin K) ℤ ((Fin n → ℤ) ⧸ Q),
        ∀ i : Fin n,
          ∑ k, |b.repr (Submodule.Quotient.mk (Pi.single i 1)) k| ≤
            (n : ℤ) ^ E := by
  classical
  let b : Module.Basis (Fin (Fintype.card (Sum C V))) ℤ ((Fin n → ℤ) ⧸ st.Q) :=
    st.basis.reindex (Fintype.equivFin (Sum C V))
  refine ⟨Fintype.card (Sum C V), st.Q, st.le_colLat, st.primitive, ?_, ?_, b, ?_⟩
  · have hr := st.Q.finrank_quotient_add_finrank
    have hq : Module.finrank ℤ ((Fin n → ℤ) ⧸ st.Q) = Fintype.card (Sum C V) := by
      simpa using Module.finrank_eq_card_basis st.basis
    have ha : Module.finrank ℤ (Fin n → ℤ) = n := by
      simp
    have hr' : Fintype.card (Sum C V) + Module.finrank ℤ st.Q = n := by
      calc
        Fintype.card (Sum C V) + Module.finrank ℤ st.Q =
            Module.finrank ℤ ((Fin n → ℤ) ⧸ st.Q) + Module.finrank ℤ st.Q := by rw [hq]
        _ = Module.finrank ℤ (Fin n → ℤ) := hr
        _ = n := ha
    omega
  · simpa using hcard
  · intro i
    have hlive : (∑ v : V,
        |st.basis.repr (Submodule.Quotient.mk (Pi.single i 1)) (Sum.inr v)|) ≤ 1 := by
      rcases howner : st.blocks.owner i with _ | w
      · simp_rw [st.live_coord]
        simp [howner]
      · rw [Finset.sum_eq_single w]
        · rw [st.live_coord]
          simp [howner]
        · intro v hv hvw
          rw [st.live_coord]
          simp [howner, Ne.symm hvw]
        · simp
    calc
      ∑ k, |b.repr (Submodule.Quotient.mk (Pi.single i 1)) k| =
          ∑ q : Sum C V,
            |st.basis.repr (Submodule.Quotient.mk (Pi.single i 1)) q| := by
              simp only [b, Module.Basis.repr_reindex_apply]
              rw [← (Fintype.equivFin (Sum C V)).sum_comp]
              simp
      _ = (∑ c : C,
            |st.basis.repr (Submodule.Quotient.mk (Pi.single i 1)) (Sum.inl c)|) +
          ∑ v : V,
            |st.basis.repr (Submodule.Quotient.mk (Pi.single i 1)) (Sum.inr v)| := by
              rw [Fintype.sum_sum_type]
      _ ≤ M + 1 := add_le_add (hM i) hlive
      _ ≤ (n : ℤ) ^ E := hnorm


private theorem log_le_six_logThird (p : ℕ) (hp : 64 ≤ p) :
    Real.log p ≤ 6 * (Nat.log 2 p / 3 : ℕ) := by
  let ell := Nat.log 2 p
  let L := ell / 3
  have hell : 6 ≤ ell := by
    have hmono := Nat.log_mono_right (b := 2) hp
    norm_num at hmono ⊢
    exact hmono
  have hL : 2 ≤ L := by dsimp [L]; omega
  have hpPowN : p ≤ 2 ^ (ell + 1) :=
    Nat.le_of_lt (Nat.lt_pow_succ_log_self (by norm_num) p)
  have hpPowR : (p : ℝ) ≤ (2 : ℝ) ^ (ell + 1) := by exact_mod_cast hpPowN
  have hp0 : (0 : ℝ) < p := by positivity
  have hlog := Real.log_le_log hp0 hpPowR
  rw [Real.log_pow] at hlog
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at h
    exact h
  have hellL : ell + 1 ≤ 6 * L := by
    dsimp [L]
    omega
  have hcast : ((ell + 1 : ℕ) : ℝ) ≤ 6 * L := by exact_mod_cast hellL
  dsimp [ell, L] at hlog ⊢
  have hn : (0 : ℝ) ≤ ell + 1 := by positivity
  nlinarith

private theorem coefficient_growth_le {n r : ℕ} (hn : 2 ≤ n)
    (hr : r ≤ 2 * Nat.log 2 n + 2) :
    (30 : ℤ) ^ r + 1 ≤ (n : ℤ) ^ 22 := by
  have h30 : 30 ≤ 2 ^ 5 := by norm_num
  have hbase : 30 ^ r ≤ (2 ^ 5) ^ r := Nat.pow_le_pow_left h30 r
  have hexp : 5 * r ≤ 10 * Nat.log 2 n + 10 := by omega
  have hpowexp : 2 ^ (5 * r) ≤ 2 ^ (10 * Nat.log 2 n + 10) :=
    Nat.pow_le_pow_right (by norm_num) hexp
  have hlogpow : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by omega)
  have hten : (2 ^ Nat.log 2 n) ^ 10 ≤ n ^ 10 := Nat.pow_le_pow_left hlogpow 10
  have hn10 : 2 ^ 10 ≤ n ^ 10 := by
    have := Nat.pow_le_pow_left hn 10
    simpa using this
  have hmain : 30 ^ r ≤ n ^ 20 := by
    calc
      30 ^ r ≤ (2 ^ 5) ^ r := hbase
      _ = 2 ^ (5 * r) := by rw [← pow_mul]
      _ ≤ 2 ^ (10 * Nat.log 2 n + 10) := hpowexp
      _ = 2 ^ 10 * (2 ^ Nat.log 2 n) ^ 10 := by ring
      _ ≤ n ^ 10 * n ^ 10 := Nat.mul_le_mul hn10 hten
      _ = n ^ 20 := by rw [← pow_add]
  have hn20 : 1 ≤ n ^ 20 := one_le_pow₀ (by omega)
  have hnat : 30 ^ r + 1 ≤ n ^ 22 := by
    calc
      30 ^ r + 1 ≤ n ^ 20 + n ^ 20 := Nat.add_le_add hmain hn20
      _ ≤ n ^ 20 * n ^ 2 := by nlinarith [show 2 ≤ n ^ 2 by nlinarith]
      _ = n ^ 22 := by rw [← pow_add]
  exact_mod_cast hnat

theorem compression :
    ∃ C : ℕ, 0 < C ∧
      ∀ (p n : ℕ) (_ : Fact p.Prime) (S : MinimalNUS p n) (P : S.Pairing),
        64 ≤ p →
        ∃ (K : ℕ) (Q : Submodule ℤ (Fin n → ℤ)),
          Q ≤ S.colLat P ∧
          (∀ (v : Fin n → ℤ) (c : ℤ), c ≠ 0 → c • v ∈ Q → v ∈ Q) ∧
          Module.finrank ℤ Q = n - K ∧
          ((K : ℝ) ≤ C * (Real.sqrt n + n / Real.log p)) ∧
          ∃ b : Module.Basis (Fin K) ℤ ((Fin n → ℤ) ⧸ Q),
            ∀ i : Fin n,
              ∑ k, |b.repr (Submodule.Quotient.mk (Pi.single i 1)) k| ≤ (n : ℤ) ^ C := by
  classical
  obtain ⟨D₀, m₀, hD₀, hhigh⟩ := exists_high_anchor_sample
  let mstar := max m₀ 16
  obtain ⟨C, hC⟩ : ∃ C : ℕ,
      12 * D₀ + mstar + 6 + 22 ≤ (C : ℝ) := exists_nat_ge _
  have hCpos : 0 < C := by
    have hD : 0 < 12 * D₀ := by positivity
    exact_mod_cast (show (0 : ℝ) < C by linarith)
  refine ⟨C, hCpos, ?_⟩
  intro p n hpFact S P hp64
  let L := Nat.log 2 p / 3
  have hlog6 : 6 ≤ Nat.log 2 p := by
    have hmono := Nat.log_mono_right (b := 2) hp64
    norm_num at hmono ⊢
    exact hmono
  have hL2 : 2 ≤ L := by dsimp [L]; omega
  let X₀ := PackedCompressionState.initial S P
  have hX₀bound : X₀.st.CoreBound 1 := by
    intro a
    have h0 := initialCompressionState_coreBound S P a
    exact le_trans h0 (by norm_num)
  have hX₀light : ∀ v, (X₀.st.blocks.block v).card < L := by
    change ∀ v : Fin n, ((initialCompressionState S P).blocks.block v).card < L
    intro v
    change ({v} : Finset (Fin n)).card < L
    simp
    omega
  have hstep : ∀ (X : PackedCompressionState S P) (M : ℤ),
      X.st.CoreBound M → 1 ≤ M →
      (∀ v, (X.st.blocks.block v).card < L) →
      mstar ≤ X.liveCard →
      Nonempty (PackedCompressionState.RoundResult X M L D₀) := by
    intro X M hM hM1 hlight hm
    exact PackedCompressionState.exists_round_result D₀ m₀ hD₀ hhigh X M hM hM1
      hp64 L rfl hlight (by simpa [mstar] using hm)
  let out := Classical.choice
    (PackedCompressionState.iterate_round_results D₀ hD₀ L mstar
      (by simp [mstar]) hstep X₀ 1 hX₀bound (by norm_num) hX₀light)
  have hmass0 : X₀.mass ≤ n := by
    exact X₀.st.blocks.mass_le
  have hheavyNat : L * out.heavyCost ≤ n := by
    have hm := out.mass_charge
    omega
  have hlogp : 0 < Real.log p := Real.log_pos (by exact_mod_cast (lt_of_lt_of_le (by norm_num) hp64))
  have hlogL : Real.log p ≤ 6 * L := by
    simpa [L] using log_le_six_logThird p hp64
  have hheavy : (out.heavyCost : ℝ) ≤ 6 * (n : ℝ) / Real.log p := by
    have hnatR : (L : ℝ) * out.heavyCost ≤ n := by exact_mod_cast hheavyNat
    have hh0 : (0 : ℝ) ≤ out.heavyCost := by positivity
    have hmul : (out.heavyCost : ℝ) * Real.log p ≤ 6 * n := by
      calc
        (out.heavyCost : ℝ) * Real.log p ≤ out.heavyCost * (6 * L) :=
          mul_le_mul_of_nonneg_left hlogL hh0
        _ ≤ 6 * n := by nlinarith
    exact (le_div_iff₀ hlogp).mpr (by nlinarith)
  have hn1R : (1 : ℝ) ≤ n := by
    exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) S.two_le)
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt n := Real.one_le_sqrt.mpr hn1R
  have hlive : (out.final.liveCard : ℝ) ≤ mstar * Real.sqrt n := by
    have ht : out.final.liveCard ≤ mstar := Nat.le_of_lt out.terminal
    have htR : (out.final.liveCard : ℝ) ≤ mstar := by exact_mod_cast ht
    have hm0 : (0 : ℝ) ≤ mstar := by positivity
    nlinarith
  have hsample := out.sample_bound
  have hLive0 : X₀.liveCard = n := by
    simp [X₀, PackedCompressionState.liveCard, PackedCompressionState.initial]
  rw [hLive0] at hsample
  have hheavy' : (out.heavyCost : ℝ) ≤ 6 * (n / Real.log p) := by
    (convert hheavy using 1; ring)
  have hCcoef : 12 * D₀ + mstar + 6 ≤ (C : ℝ) := by linarith
  have hA0 : (0 : ℝ) ≤ Real.sqrt n := Real.sqrt_nonneg _
  have hB0 : (0 : ℝ) ≤ (n : ℝ) / Real.log p := by positivity
  have hcoefA : 12 * D₀ + mstar ≤ (C : ℝ) := by linarith
  have hcoefB : (6 : ℝ) ≤ C := by linarith
  have hmulA := mul_le_mul_of_nonneg_right hcoefA hA0
  have hmulB := mul_le_mul_of_nonneg_right hcoefB hB0
  have hcard : (((out.final.coreCard + out.final.liveCard : ℕ) : ℝ)) ≤
      C * (Real.sqrt n + n / Real.log p) := by
    rw [out.coreCard_eq]
    have hcore0 : X₀.coreCard = 0 := by simp [X₀, PackedCompressionState.coreCard,
      PackedCompressionState.initial]
    rw [hcore0]
    norm_num [Nat.cast_add]
    calc
      (out.sampleCost : ℝ) + out.heavyCost + out.final.liveCard ≤
          12 * D₀ * Real.sqrt n + 6 * (n / Real.log p) +
            mstar * Real.sqrt n := add_le_add (add_le_add hsample hheavy') hlive
      _ = (12 * D₀ + mstar) * Real.sqrt n +
          6 * (n / Real.log p) := by ring
      _ ≤ C * Real.sqrt n + C * (n / Real.log p) := add_le_add hmulA hmulB
      _ = C * (Real.sqrt n + n / Real.log p) := by ring
  have hC22 : 22 ≤ C := by exact_mod_cast (show (22 : ℝ) ≤ C by linarith)
  have hrounds : out.rounds ≤ 2 * Nat.log 2 n + 2 := by simpa [hLive0] using out.rounds_le
  have hgrowth := coefficient_growth_le S.two_le hrounds
  have hpowmono : (n : ℤ) ^ 22 ≤ (n : ℤ) ^ C := by
    exact pow_le_pow_right₀ (by
      exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) S.two_le)) hC22
  have hnorm : (30 : ℤ) ^ out.rounds + 1 ≤ (n : ℤ) ^ C :=
    le_trans hgrowth hpowmono
  have hfinalBound : out.final.st.CoreBound ((30 : ℤ) ^ out.rounds) := by
    simpa using out.coreBound
  exact out.final.st.finish_any hfinalBound (by simpa [PackedCompressionState.coreCard,
    PackedCompressionState.liveCard] using hcard) hnorm

end NUS




namespace NUS

open Finset Matrix




theorem abs_det_le_prod_col_l1 {N : ℕ} (A : Matrix (Fin N) (Fin N) ℤ) :
    |A.det| ≤ ∏ c, ∑ r, |A r c| := by
  classical
  rw [Matrix.det_apply]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have habs : ∀ σ : Equiv.Perm (Fin N),
      |Equiv.Perm.sign σ • ∏ i, A (σ i) i| = ∏ i, |A (σ i) i| := by
    intro σ
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;>
      simp [h, Units.smul_def, Finset.abs_prod]
  have hinj : Function.Injective (fun σ : Equiv.Perm (Fin N) => (⇑σ : Fin N → Fin N)) :=
    fun σ τ h => Equiv.coe_fn_injective h
  calc ∑ σ : Equiv.Perm (Fin N), |Equiv.Perm.sign σ • ∏ i, A (σ i) i|
      = ∑ σ : Equiv.Perm (Fin N), ∏ i, |A (σ i) i| :=
        Finset.sum_congr rfl fun σ _ => habs σ
    _ = ∑ f ∈ Finset.univ.map ⟨_, hinj⟩, ∏ i, |A (f i) i| :=
        (Finset.sum_map Finset.univ ⟨_, hinj⟩ (fun g => ∏ i, |A (g i) i|)).symm
    _ ≤ ∑ f : Fin N → Fin N, ∏ i, |A (f i) i| :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun f _ _ => Finset.prod_nonneg fun i _ => abs_nonneg _)
    _ = ∏ i, ∑ r, |A r i| := by
        rw [Finset.prod_univ_sum, Fintype.piFinset_univ]


theorem abs_det_le_prod_row_l1 {N : ℕ} (A : Matrix (Fin N) (Fin N) ℤ) :
    |A.det| ≤ ∏ r, ∑ c, |A r c| := by
  have h := abs_det_le_prod_col_l1 Aᵀ
  rw [Matrix.det_transpose] at h
  simpa using h




theorem lin_pi_decomp {n : ℕ} (ℓ : (Fin n → ℤ) →ₗ[ℤ] ℤ) (w : Fin n → ℤ) :
    ℓ w = ∑ i, w i * ℓ (Pi.single i 1) := by
  have hw : w = ∑ i, w i • (Pi.single i 1 : Fin n → ℤ) := by
    conv_lhs => rw [← Finset.univ_sum_single w]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  conv_lhs => rw [hw]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ℓ.map_smul, smul_eq_mul]


theorem exists_indep_family {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] {ι : Type*} (g : ι → V) (d : ℕ)
    (hd : d ≤ Module.finrank F (Submodule.span F (Set.range g))) :
    ∃ t : Fin d → ι, LinearIndependent F (fun j => g (t j)) := by
  classical
  obtain ⟨sb, hsub, hspan, hli⟩ := exists_linearIndependent F (Set.range g)
  have hfin : sb.Finite := hli.setFinite
  haveI := hfin.fintype
  have hcard : d ≤ Fintype.card sb := by
    have h1 : Module.finrank F (Submodule.span F sb) = sb.toFinset.card :=
      finrank_span_set_eq_card hli
    rw [hspan] at h1
    rw [Set.toFinset_card] at h1
    omega
  let emb : Fin d ↪ sb :=
    (Fin.castLEEmb hcard).trans (Fintype.equivFin sb).symm.toEmbedding
  have hsel : ∀ x : sb, ∃ i : ι, g i = (x : V) := fun x => hsub x.2
  choose sel hsel using hsel
  refine ⟨fun j => sel (emb j), ?_⟩
  have hfun : (fun j => g (sel (emb j))) = (fun x : sb => (x : V)) ∘ emb := by
    funext j
    simp [hsel]
  rw [hfun]
  exact hli.comp emb emb.injective


theorem exists_succAbove_det_ne_zero {F : Type*} [Field F] {m : ℕ}
    (A : Matrix (Fin m) (Fin (m + 1)) F) (hA : LinearIndependent F (fun i => A i)) :
    ∃ c : Fin (m + 1), (A.submatrix id c.succAbove).det ≠ 0 := by
  classical
  
  have hrank : A.rank = m := by
    have h := hA.rank_matrix
    simpa using h
  have hker : Module.finrank F (LinearMap.ker A.mulVecLin) = 1 := by
    have hrn := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
    rw [Module.finrank_pi] at hrn
    rw [Matrix.rank] at hrank
    simp only [Fintype.card_fin] at hrn
    omega
  let z' := Module.finBasisOfFinrankEq F (LinearMap.ker A.mulVecLin) hker
  have hz0 : ((z' 0 : LinearMap.ker A.mulVecLin) : Fin (m + 1) → F) ≠ 0 := by
    intro h
    exact z'.ne_zero 0 (Subtype.ext h)
  obtain ⟨c, hc⟩ : ∃ c, ((z' 0 : LinearMap.ker A.mulVecLin) : Fin (m + 1) → F) c ≠ 0 := by
    by_contra h
    push Not at h
    exact hz0 (funext h)
  refine ⟨c, fun hdet => ?_⟩
  obtain ⟨v, hv0, hvz⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  set w : Fin (m + 1) → F := c.insertNth 0 v with hwdef
  have hw : A *ᵥ w = 0 := by
    funext j
    rw [Matrix.mulVec, dotProduct, Fin.sum_univ_succAbove (fun k => A j k * w k) c]
    have hzero : w c = 0 := by rw [hwdef]; exact Fin.insertNth_apply_same (α := fun _ => F) c 0 v
    have hrest : ∀ j' : Fin m, w (c.succAbove j') = v j' := by
      intro j'
      rw [hwdef]
      exact Fin.insertNth_apply_succAbove (α := fun _ => F) c 0 v j'
    rw [hzero, mul_zero, zero_add]
    have := congrFun hvz j
    rw [Matrix.mulVec, dotProduct] at this
    simp only [Matrix.submatrix_apply, id_eq] at this
    simp only [hrest]
    exact this
  have hwker : w ∈ LinearMap.ker A.mulVecLin := by
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
    exact hw
  
  set q : LinearMap.ker A.mulVecLin := ⟨w, hwker⟩ with hqdef
  have hq : q = z'.repr q 0 • z' 0 := by
    conv_lhs => rw [← z'.sum_repr q]
    rw [Fin.sum_univ_one]
  have hwc : w c = z'.repr q 0 * ((z' 0 : LinearMap.ker A.mulVecLin) : Fin (m + 1) → F) c := by
    have := congrArg (fun x : LinearMap.ker A.mulVecLin => (x : Fin (m + 1) → F) c) hq
    simpa using this
  have hzc : w c = 0 := by rw [hwdef]; exact Fin.insertNth_apply_same (α := fun _ => F) c 0 v
  have hcoeff : z'.repr q 0 = 0 := by
    rw [hzc] at hwc
    rcases mul_eq_zero.mp hwc.symm with h | h
    · exact h
    · exact absurd h hc
  have hqzero : q = 0 := by
    rw [hq, hcoeff, zero_smul]
  have hwzero : w = 0 := congrArg (fun x : LinearMap.ker A.mulVecLin => (x : Fin (m + 1) → F)) hqzero
  apply hv0
  funext j'
  have h1 := congrFun hwzero (c.succAbove j')
  rw [hwdef] at h1
  rw [Fin.insertNth_apply_succAbove] at h1
  simpa using h1



def castZQ {n : ℕ} : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℚ) where
  toFun v i := v i
  map_add' x y := by ext i; simp
  map_smul' c x := by ext i; simp

theorem castZQ_injective {n : ℕ} : Function.Injective (castZQ (n := n)) := by
  intro x y h
  funext i
  have hi := congrFun h i
  change ((x i : ℤ) : ℚ) = ((y i : ℤ) : ℚ) at hi
  exact_mod_cast hi

theorem MinimalNUS.finrank_colLat {p n : ℕ} (S : MinimalNUS p n)
    (P : S.Pairing) : Module.finrank ℤ (S.colLat P) = n - 1 := by
  classical
  let f := (castZQ (n := n)).domRestrict (S.colLat P)
  have hf : Function.Injective f := castZQ_injective.comp Subtype.val_injective
  have hrange : f.range = Submodule.span ℤ (Set.range (S.rhoQ P)) := by
    rw [LinearMap.range_domRestrict, MinimalNUS.colLat, Submodule.map_span]
    congr 1
    ext x
    constructor
    · rintro ⟨y, ⟨t, rfl⟩, rfl⟩
      exact ⟨t, rfl⟩
    · rintro ⟨t, rfl⟩
      exact ⟨S.rho P t, ⟨t, rfl⟩, rfl⟩
  have heq := LinearEquiv.finrank_eq (LinearEquiv.ofInjective f hf)
  rw [hrange] at heq
  letI : Module.Finite ℤ (Submodule.span ℤ (Set.range (S.rhoQ P))) :=
    Module.Finite.span_of_finite ℤ (Set.finite_range _)
  calc
    Module.finrank ℤ (S.colLat P) =
        Module.finrank ℤ (Submodule.span ℤ (Set.range (S.rhoQ P))) := heq
    _ = Module.finrank ℚ (Submodule.span ℚ (Set.range (S.rhoQ P))) :=
      (Submodule.finrank_span_eq_finrank_span ℤ ℚ _).symm
    _ = n - 1 := S.finrank_span_rhoQ P

theorem MinimalNUS.quotient_collision_rank {p n K : ℕ} (S : MinimalNUS p n)
    (P : S.Pairing) (Q : Submodule ℤ (Fin n → ℤ)) (hQ : Q ≤ S.colLat P)
    (hQr : Module.finrank ℤ Q = n - K)
    (b : Module.Basis (Fin K) ℤ ((Fin n → ℤ) ⧸ Q)) :
    Module.finrank ℤ (Submodule.span ℤ
      (Set.range fun t => Submodule.Quotient.mk (S.rho P t) :
        Set ((Fin n → ℤ) ⧸ Q))) = K - 1 := by
  classical
  let f := Q.mkQ.domRestrict (S.colLat P)
  have hker : f.ker = Submodule.comap (S.colLat P).subtype Q := by
    simp [f, LinearMap.ker_domRestrict, Submodule.ker_mkQ]
  have hkerrank : Module.finrank ℤ f.ker = Module.finrank ℤ Q := by
    rw [hker]
    exact LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hQ)
  have hrange : f.range = Submodule.span ℤ
      (Set.range fun t => Submodule.Quotient.mk (S.rho P t) :
        Set ((Fin n → ℤ) ⧸ Q)) := by
    rw [LinearMap.range_domRestrict, MinimalNUS.colLat, Submodule.map_span]
    congr 1
    ext x
    constructor
    · rintro ⟨y, ⟨t, rfl⟩, rfl⟩
      exact ⟨t, rfl⟩
    · rintro ⟨t, rfl⟩
      exact ⟨S.rho P t, ⟨t, rfl⟩, rfl⟩
  have hequiv := LinearEquiv.finrank_eq f.quotKerEquivRange
  rw [hrange] at hequiv
  have hsum := f.ker.finrank_quotient_add_finrank
  rw [hequiv, hkerrank, hQr, S.finrank_colLat P] at hsum
  have hambient := Q.finrank_quotient_add_finrank
  have hbfin : Module.finrank ℤ ((Fin n → ℤ) ⧸ Q) = K := by
    simpa using Module.finrank_eq_card_basis b
  have hamb : Module.finrank ℤ (Fin n → ℤ) = n := by
    simp
  have hsumQ : K + (n - K) = n := by
    calc
      K + (n - K) = Module.finrank ℤ ((Fin n → ℤ) ⧸ Q) +
          Module.finrank ℤ Q := by rw [hbfin, hQr]
      _ = Module.finrank ℤ (Fin n → ℤ) := hambient
      _ = n := hamb
  have hKn : K ≤ n := by omega
  have hn := S.two_le
  have hK1 : 1 ≤ K := by omega
  have hleft := hsum
  rw [Nat.add_comm] at hleft
  have hright : (n - K) + (K - 1) = n - 1 := by omega
  apply Nat.add_left_cancel (n := n - K)
  exact hleft.trans hright.symm

noncomputable def quotientCoordsZ {n K : ℕ} {Q : Submodule ℤ (Fin n → ℤ)}
    (b : Module.Basis (Fin K) ℤ ((Fin n → ℤ) ⧸ Q))
    (x : (Fin n → ℤ) ⧸ Q) : Fin K → ℤ := fun k => b.repr x k

noncomputable def quotientCoordsQ {n K : ℕ} {Q : Submodule ℤ (Fin n → ℤ)}
    (b : Module.Basis (Fin K) ℤ ((Fin n → ℤ) ⧸ Q))
    (x : (Fin n → ℤ) ⧸ Q) : Fin K → ℚ := fun k => b.repr x k

theorem MinimalNUS.quotientCoordsQ_collision_rank {p n K : ℕ} (S : MinimalNUS p n)
    (P : S.Pairing) (Q : Submodule ℤ (Fin n → ℤ)) (hQ : Q ≤ S.colLat P)
    (hQr : Module.finrank ℤ Q = n - K)
    (b : Module.Basis (Fin K) ℤ ((Fin n → ℤ) ⧸ Q)) :
    Module.finrank ℚ (Submodule.span ℚ (Set.range fun t =>
      quotientCoordsQ b (Submodule.Quotient.mk (S.rho P t)))) = K - 1 := by
  classical
  let e := b.repr ≪≫ₗ Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin K)
  have hmap : Submodule.map e.toLinearMap (Submodule.span ℤ
      (Set.range fun t => (Submodule.Quotient.mk (S.rho P t) :
        (Fin n → ℤ) ⧸ Q))) =
      Submodule.span ℤ (Set.range fun t =>
        quotientCoordsZ b (Submodule.Quotient.mk (S.rho P t))) := by
    rw [Submodule.map_span]
    congr 1
    ext x
    constructor
    · rintro ⟨y, ⟨t, rfl⟩, rfl⟩
      exact ⟨t, rfl⟩
    · rintro ⟨t, rfl⟩
      exact ⟨Submodule.Quotient.mk (S.rho P t), ⟨t, rfl⟩, rfl⟩
  have he := LinearEquiv.finrank_map_eq e (Submodule.span ℤ
    (Set.range fun t => Submodule.Quotient.mk (S.rho P t)))
  rw [hmap, S.quotient_collision_rank P Q hQ hQr b] at he
  let f := (castZQ (n := K)).domRestrict (Submodule.span ℤ
    (Set.range fun t => quotientCoordsZ b (Submodule.Quotient.mk (S.rho P t))))
  have hf : Function.Injective f := castZQ_injective.comp Subtype.val_injective
  have hfrange : f.range = Submodule.span ℤ (Set.range fun t =>
      quotientCoordsQ b (Submodule.Quotient.mk (S.rho P t))) := by
    rw [LinearMap.range_domRestrict, Submodule.map_span]
    congr 1
    ext x
    constructor
    · rintro ⟨y, ⟨t, rfl⟩, rfl⟩
      exact ⟨t, rfl⟩
    · rintro ⟨t, rfl⟩
      exact ⟨quotientCoordsZ b (Submodule.Quotient.mk (S.rho P t)), ⟨t, rfl⟩, rfl⟩
  have hef := LinearEquiv.finrank_eq (LinearEquiv.ofInjective f hf)
  rw [hfrange] at hef
  letI : Module.Finite ℤ (Submodule.span ℤ (Set.range fun t =>
      quotientCoordsQ b (Submodule.Quotient.mk (S.rho P t)))) :=
    Module.Finite.span_of_finite ℤ (Set.finite_range _)
  calc
    Module.finrank ℚ (Submodule.span ℚ (Set.range fun t =>
        quotientCoordsQ b (Submodule.Quotient.mk (S.rho P t)))) =
      Module.finrank ℤ (Submodule.span ℤ (Set.range fun t =>
        quotientCoordsQ b (Submodule.Quotient.mk (S.rho P t)))) :=
        Submodule.finrank_span_eq_finrank_span ℤ ℚ _
    _ = Module.finrank ℤ (Submodule.span ℤ (Set.range fun t =>
        quotientCoordsZ b (Submodule.Quotient.mk (S.rho P t)))) := hef.symm
    _ = K - 1 := he


theorem MinimalNUS.p_dvd_quotient_minor {p n K : ℕ} [Fact p.Prime]
    (S : MinimalNUS p n) (P : S.Pairing)
    (Q : Submodule ℤ (Fin n → ℤ)) (hQ : Q ≤ S.colLat P)
    (hQr : Module.finrank ℤ Q = n - K)
    (b : Module.Basis (Fin K) ℤ ((Fin n → ℤ) ⧸ Q))
    (hKn : K ≤ n) (hK1 : 1 ≤ K)
    (t : Fin (K - 1) → Sym2 (Fin n)) (c : Fin ((K - 1) + 1)) :
    (p : ℤ) ∣ (Matrix.of fun i j =>
      b.repr (Submodule.Quotient.mk (S.rho P (t i)))
        (finCongr (Nat.sub_add_cancel hK1) (c.succAbove j))).det := by
  classical
  let inc : Fin (K - 1) ↪ Fin K :=
    ⟨fun j => finCongr (Nat.sub_add_cancel hK1) (c.succAbove j),
      fun _ _ h => by simpa using h⟩
  let bQ := Module.finBasisOfFinrankEq ℤ Q hQr
  let e := Module.Basis.sumQuot bQ b
  let I := Fin (n - K) ⊕ Fin (K - 1)
  let rows : I → (Fin n → ℤ) := Sum.elim (fun i => bQ i) (fun j => S.rho P (t j))
  let cols : I → (Fin (n - K) ⊕ Fin K) := Sum.map id inc
  have hcard : Fintype.card (Fin (n - 1)) = Fintype.card I := by
    simp [I]
    omega
  let er : Fin (n - 1) ≃ I := Fintype.equivOfCardEq hcard
  let v : Fin (n - 1) → (Fin n → ℤ) := fun r => rows (er r)
  have hv : ∀ r, v r ∈ S.colLat P := by
    intro r
    change rows (er r) ∈ S.colLat P
    rcases hri : er r with i | j
    · change (bQ i : Fin n → ℤ) ∈ S.colLat P
      exact hQ (bQ i).2
    · change S.rho P (t j) ∈ S.colLat P
      exact Submodule.subset_span (Set.mem_range_self (t j))
  let U : Matrix (Fin n) (Fin (n - 1)) ℤ := fun a j =>
    e.repr (Pi.single a 1) (cols (er j))
  have hmul : Matrix.of v * U =
      (Matrix.of fun r s => e.repr (rows r) (cols s)).reindex er.symm er.symm := by
    ext r j
    have h1 := (lin_pi_decomp (e.coord (cols (er j))) (rows (er r))).symm
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply, Equiv.symm_symm]
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply, v, U]
    simpa [Module.Basis.coord_apply] using h1
  have hp := S.p_dvd_det_mul P v hv U
  rw [hmul, Matrix.det_reindex_self] at hp
  have hblock : (Matrix.of fun r s => e.repr (rows r) (cols s)) =
      Matrix.fromBlocks (1 : Matrix (Fin (n - K)) (Fin (n - K)) ℤ) 0
        (Matrix.of fun i j => e.repr (S.rho P (t i)) (Sum.inl j))
        (Matrix.of fun i j =>
          b.repr (Submodule.Quotient.mk (S.rho P (t i))) (inc j)) := by
    ext r s
    rcases r with i | i <;> rcases s with j | j
    · simp [e, rows, cols, bQ, Matrix.one_apply, Finsupp.single_apply]
    · simp [e, rows, cols, bQ]
    · simp [rows, cols]
    · exact Module.Basis.sumQuot_repr_inr bQ b (S.rho P (t i)) (inc j)
  rw [hblock, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, one_mul] at hp
  simpa [inc] using hp

theorem sum_abs_uvec_le_two {n : ℕ} (t : Sym2 (Fin n)) :
    ∑ i, |uvec t i| ≤ 2 := by
  classical
  induction t using Sym2.ind with
  | _ a b =>
    rw [uvec_mk]
    have ha : (∑ i, |(Pi.single a 1 : Fin n → ℤ) i|) = 1 := by
      simp only [Pi.single_apply, abs_ite, abs_one, abs_zero]
      have h := Finset.sum_ite_eq' (Finset.univ : Finset (Fin n)) a
        (fun _ => (1 : ℤ))
      simpa only [Finset.mem_univ, if_true] using h
    have hb : (∑ i, |(Pi.single b 1 : Fin n → ℤ) i|) = 1 := by
      simp only [Pi.single_apply, abs_ite, abs_one, abs_zero]
      have h := Finset.sum_ite_eq' (Finset.univ : Finset (Fin n)) b
        (fun _ => (1 : ℤ))
      simpa only [Finset.mem_univ, if_true] using h
    calc
      ∑ i, |((Pi.single a 1 : Fin n → ℤ) + (Pi.single b 1 : Fin n → ℤ)) i| ≤
          ∑ i, (|(Pi.single a 1 : Fin n → ℤ) i| +
            |(Pi.single b 1 : Fin n → ℤ) i|) :=
        Finset.sum_le_sum fun i _ => abs_add_le _ _
      _ = (∑ i, |(Pi.single a 1 : Fin n → ℤ) i|) +
          ∑ i, |(Pi.single b 1 : Fin n → ℤ) i| := Finset.sum_add_distrib
      _ = 2 := by rw [ha, hb]; norm_num

theorem MinimalNUS.sum_abs_rho_le_four {p n : ℕ} (S : MinimalNUS p n)
    (P : S.Pairing) (t : Sym2 (Fin n)) : ∑ i, |S.rho P t i| ≤ 4 := by
  have ht := sum_abs_uvec_le_two t
  have hmu := sum_abs_uvec_le_two (P.μ t)
  calc
    ∑ i, |S.rho P t i| ≤ ∑ i, (|uvec t i| + |uvec (P.μ t) i|) := by
      apply Finset.sum_le_sum
      intro i hi
      exact abs_sub _ _
    _ = (∑ i, |uvec t i|) + ∑ i, |uvec (P.μ t) i| := Finset.sum_add_distrib
    _ ≤ 4 := by omega

theorem MinimalNUS.core_rho_norm_le {p n K : ℕ} (S : MinimalNUS p n)
    (P : S.Pairing) (Q : Submodule ℤ (Fin n → ℤ))
    (b : Module.Basis (Fin K) ℤ ((Fin n → ℤ) ⧸ Q)) (M : ℤ) (hM : 0 ≤ M)
    (hb : ∀ i : Fin n,
      ∑ k, |b.repr (Submodule.Quotient.mk (Pi.single i 1)) k| ≤ M)
    (t : Sym2 (Fin n)) :
    ∑ k, |b.repr (Submodule.Quotient.mk (S.rho P t)) k| ≤ 4 * M := by
  classical
  have hdecomp : ∀ k, b.repr (Submodule.Quotient.mk (S.rho P t)) k =
      ∑ i, S.rho P t i * b.repr (Submodule.Quotient.mk (Pi.single i 1)) k := by
    intro k
    exact lin_pi_decomp ((b.coord k).comp Q.mkQ) (S.rho P t)
  calc
    ∑ k, |b.repr (Submodule.Quotient.mk (S.rho P t)) k| =
        ∑ k, |∑ i, S.rho P t i *
          b.repr (Submodule.Quotient.mk (Pi.single i 1)) k| := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [hdecomp]
    _ ≤ ∑ k, ∑ i, |S.rho P t i *
          b.repr (Submodule.Quotient.mk (Pi.single i 1)) k| := by
      apply Finset.sum_le_sum
      intro k hk
      exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |S.rho P t i| *
          (∑ k, |b.repr (Submodule.Quotient.mk (Pi.single i 1)) k|) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      simp_rw [abs_mul]
      rw [Finset.mul_sum]
    _ ≤ ∑ i, |S.rho P t i| * M := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hb i) (abs_nonneg _)
    _ = (∑ i, |S.rho P t i|) * M := by rw [Finset.sum_mul]
    _ ≤ 4 * M := mul_le_mul_of_nonneg_right (S.sum_abs_rho_le_four P t) hM

theorem key_inequality_proof :
    ∃ C : ℝ, 0 < C ∧
      ∀ (p n : ℕ) (_ : Fact p.Prime) (S : MinimalNUS p n) (_ : S.Pairing),
        64 ≤ p →
        Real.log p ≤ C * (Real.sqrt n + n / Real.log p) * Real.log n := by
  classical
  obtain ⟨C₀, hC₀, hcomp⟩ := compression
  refine ⟨(C₀ : ℝ) * ((C₀ : ℝ) + 2), by positivity, ?_⟩
  intro p n hpFact S P hp64
  obtain ⟨K, Q, hQ, hprim, hQr, hKbound, b, hb⟩ := hcomp p n hpFact S P hp64
  have hn2 := S.two_le
  have hlogp : 0 < Real.log p :=
    Real.log_pos (by exact_mod_cast (lt_of_lt_of_le (by norm_num) hp64))
  have hM : (0 : ℤ) ≤ (n : ℤ) ^ C₀ := by positivity
  have hbfin : Module.finrank ℤ ((Fin n → ℤ) ⧸ Q) = K := by
    simpa using Module.finrank_eq_card_basis b
  have hambient := Q.finrank_quotient_add_finrank
  have hamb : Module.finrank ℤ (Fin n → ℤ) = n := by
    simp
  have hsumQ : K + (n - K) = n := by
    calc
      K + (n - K) = Module.finrank ℤ ((Fin n → ℤ) ⧸ Q) + Module.finrank ℤ Q := by
        rw [hbfin, hQr]
      _ = Module.finrank ℤ (Fin n → ℤ) := hambient
      _ = n := hamb
  have hKn : K ≤ n := by omega
  have hrank := S.quotient_collision_rank P Q hQ hQr b
  have hK1 : 1 ≤ K := by
    have hcol := S.finrank_colLat P
    have hmono := Submodule.finrank_mono hQ
    rw [hQr, hcol] at hmono
    omega
  have hspan := S.quotientCoordsQ_collision_rank P Q hQ hQr b
  obtain ⟨t, ht⟩ := exists_indep_family
    (fun z => quotientCoordsQ b (Submodule.Quotient.mk (S.rho P z))) (K - 1)
      (by rw [hspan])
  let A : Matrix (Fin (K - 1)) (Fin K) ℚ := Matrix.of fun i =>
    quotientCoordsQ b (Submodule.Quotient.mk (S.rho P (t i)))
  have hA : LinearIndependent ℚ (fun i => A i) := ht
  let ek : Fin ((K - 1) + 1) ≃ Fin K := finCongr (Nat.sub_add_cancel hK1)
  let le : (Fin K → ℚ) ≃ₗ[ℚ] (Fin ((K - 1) + 1) → ℚ) :=
    (LinearEquiv.piCongrLeft ℚ (fun _ : Fin K => ℚ) ek).symm
  let A' : Matrix (Fin (K - 1)) (Fin ((K - 1) + 1)) ℚ := A.submatrix id ek
  have hA' : LinearIndependent ℚ (fun i => A' i) := by
    change LinearIndependent ℚ (fun i => le (A i))
    exact hA.map' le.toLinearMap (LinearMap.ker_eq_bot.mpr le.injective)
  let c0 := Classical.choose (exists_succAbove_det_ne_zero A' hA')
  have hc0 : (A'.submatrix id c0.succAbove).det ≠ 0 :=
    Classical.choose_spec (exists_succAbove_det_ne_zero A' hA')
  let inc : Fin (K - 1) ↪ Fin K :=
    ⟨fun j => ek (c0.succAbove j), fun _ _ h => by simpa [ek] using h⟩
  let D : Matrix (Fin (K - 1)) (Fin (K - 1)) ℤ := Matrix.of fun i j =>
    b.repr (Submodule.Quotient.mk (S.rho P (t i))) (inc j)
  have hcastD : D.map (Int.castRingHom ℚ) = A'.submatrix id c0.succAbove := by
    ext i j
    simp [D, A', A, inc, ek, quotientCoordsQ]
  have hD0 : D.det ≠ 0 := by
    intro h
    apply hc0
    calc
      (A'.submatrix id c0.succAbove).det = (D.map (Int.castRingHom ℚ)).det :=
        congrArg Matrix.det hcastD.symm
      _ = (D.det : ℚ) := by simpa using (Int.cast_det (R := ℚ) D).symm
      _ = 0 := by simp [h]
  have hpD : (p : ℤ) ∣ D.det := by
    have hp := S.p_dvd_quotient_minor P Q hQ hQr b hKn hK1 t c0
    simpa [D, inc, ek] using hp
  have hpabs : p ≤ Int.natAbs D.det := by
    simpa using Int.natAbs_le_of_dvd_ne_zero hpD hD0
  have hrow : ∀ i, ∑ j, |D i j| ≤ 4 * (n : ℤ) ^ C₀ := by
    intro i
    calc
      ∑ j, |D i j| =
          ∑ j, |b.repr (Submodule.Quotient.mk (S.rho P (t i))) (inc j)| := rfl
      _ = ∑ k ∈ Finset.univ.map inc,
          |b.repr (Submodule.Quotient.mk (S.rho P (t i))) k| :=
        (Finset.sum_map Finset.univ inc fun k =>
          |b.repr (Submodule.Quotient.mk (S.rho P (t i))) k|).symm
      _ ≤ ∑ k, |b.repr (Submodule.Quotient.mk (S.rho P (t i))) k| :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun j _ _ => abs_nonneg _)
      _ ≤ 4 * (n : ℤ) ^ C₀ := S.core_rho_norm_le P Q b _ hM hb (t i)
  have hdet : |D.det| ≤ (4 * (n : ℤ) ^ C₀) ^ (K - 1) := by
    calc
      |D.det| ≤ ∏ i, ∑ j, |D i j| := abs_det_le_prod_row_l1 D
      _ ≤ ∏ _ : Fin (K - 1), (4 * (n : ℤ) ^ C₀) := by
        exact Finset.prod_le_prod (fun _ _ => by positivity) (fun i _ => hrow i)
      _ = (4 * (n : ℤ) ^ C₀) ^ (K - 1) := by simp
  have hpPowNat : p ≤ (4 * n ^ C₀) ^ (K - 1) := by
    have habsNat : Int.natAbs D.det ≤ (4 * n ^ C₀) ^ (K - 1) := by
      have hz : (Int.natAbs D.det : ℤ) ≤ (4 * (n : ℤ) ^ C₀) ^ (K - 1) := by
        simpa using hdet
      exact_mod_cast hz
    exact hpabs.trans habsNat
  have hbase : (0 : ℝ) < 4 * n ^ C₀ := by positivity
  have hlogPow : Real.log p ≤ ((K - 1 : ℕ) : ℝ) * Real.log (4 * n ^ C₀) := by
    calc
      Real.log p ≤ Real.log ((4 * n ^ C₀) ^ (K - 1)) := by
        apply Real.log_le_log (by positivity)
        exact_mod_cast hpPowNat
      _ = ((K - 1 : ℕ) : ℝ) * Real.log (4 * n ^ C₀) := by
        rw [Real.log_pow]
  have hlogn : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn2)
  have hlogbase : Real.log (4 * n ^ C₀) ≤ ((C₀ : ℝ) + 2) * Real.log n := by
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0)
      (by positivity : (n : ℝ) ^ C₀ ≠ 0), Real.log_pow]
    have hlog4 : Real.log 4 ≤ 2 * Real.log n := by
      have h2n : (2 : ℝ) ≤ n := by exact_mod_cast hn2
      have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 2) h2n
      calc
        Real.log 4 = 2 * Real.log 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
          norm_num
        _ ≤ 2 * Real.log n := mul_le_mul_of_nonneg_left hh (by norm_num)
    nlinarith
  have hKreal : ((K - 1 : ℕ) : ℝ) ≤ K := by exact_mod_cast Nat.sub_le K 1
  have hfactor0 : 0 ≤ ((C₀ : ℝ) + 2) * Real.log n := by positivity
  calc
    Real.log p ≤ ((K - 1 : ℕ) : ℝ) * Real.log (4 * n ^ C₀) := hlogPow
    _ ≤ ((K - 1 : ℕ) : ℝ) * (((C₀ : ℝ) + 2) * Real.log n) :=
      mul_le_mul_of_nonneg_left hlogbase (by positivity)
    _ ≤ (K : ℝ) * (((C₀ : ℝ) + 2) * Real.log n) :=
      mul_le_mul_of_nonneg_right hKreal hfactor0
    _ ≤ ((C₀ : ℝ) * (Real.sqrt n + n / Real.log p)) *
        (((C₀ : ℝ) + 2) * Real.log n) :=
      mul_le_mul_of_nonneg_right hKbound hfactor0
    _ = (C₀ : ℝ) * ((C₀ : ℝ) + 2) *
        (Real.sqrt n + n / Real.log p) * Real.log n := by ring

end NUS




namespace NUS

open MinimalNUS


theorem exists_enum {γ : Type*} (B : Finset γ) :
    ∃ a : Fin B.card ↪ γ, Finset.univ.map a = B := by
  classical
  let e : ↥B ≃ Fin B.card := Fintype.equivFinOfCardEq (Fintype.card_coe B)
  refine ⟨⟨fun i => (e.symm i : γ), fun i j hij => ?_⟩, ?_⟩
  · exact e.symm.injective (Subtype.coe_injective hij)
  · ext x
    simp only [Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨i, rfl⟩
      exact (e.symm i).2
    · intro hx
      exact ⟨e ⟨x, hx⟩, by show ((e.symm (e ⟨x, hx⟩) : ↥B) : γ) = x; rw [Equiv.symm_apply_apply]⟩


theorem key_inequality :
    ∃ C : ℝ, 0 < C ∧
      ∀ (p n : ℕ) (_ : Fact p.Prime) (S : MinimalNUS p n) (_ : S.Pairing),
        64 ≤ p →
        Real.log p ≤ C * (Real.sqrt n + n / Real.log p) * Real.log n := by
  exact key_inequality_proof


theorem numeric_reduction (C : ℝ) (hC : 0 < C) :
    ∃ c : ℝ, 0 < c ∧ ∀ p n : ℕ, 64 ≤ p → 2 ≤ n →
      Real.log p ≤ C * (Real.sqrt n + n / Real.log p) * Real.log n →
      c * (Real.log p / Real.log (Real.log p)) ^ 2 ≤ n := by
  refine ⟨min 1 (1 / (16 * C ^ 2)), by positivity, ?_⟩
  intro p n hp hn hkey
  set X := Real.log p with hXdef
  set L := Real.log X with hLdef
  
  have hX4 : 4 ≤ X := by
    have h1 : Real.log 64 ≤ X := by
      apply Real.log_le_log (by norm_num)
      exact_mod_cast hp
    have h2 : Real.log 64 = 6 * Real.log 2 := by
      rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]
      norm_num
    have h3 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    nlinarith
  have hX0 : 0 < X := by linarith
  have hL1 : 1 ≤ L := by
    have h1 : Real.log 4 ≤ L := by
      apply Real.log_le_log (by norm_num) hX4
    have h2 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    have h3 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    nlinarith
  have hL0 : 0 < L := by linarith
  have hn0 : (0 : ℝ) < n := by positivity
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_of_lt hn
  have hsn1 : 1 ≤ Real.sqrt n := Real.one_le_sqrt.mpr hn1
  have hsn0 : 0 < Real.sqrt n := by linarith
  have hlogn0 : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
  rcases le_or_gt (X ^ 2) (n : ℝ) with hcase | hcase
  · 
    have hXL : X / L ≤ X := by
      rw [div_le_iff₀ hL0]
      nlinarith
    have h1 : (X / L) ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ (by positivity) hXL 2
    calc min 1 (1 / (16 * C ^ 2)) * (X / L) ^ 2
        ≤ 1 * (X / L) ^ 2 := by
          apply mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)
      _ = (X / L) ^ 2 := one_mul _
      _ ≤ X ^ 2 := h1
      _ ≤ n := hcase
  · 
    have hsX : Real.sqrt n ≤ X := by
      have := Real.sqrt_le_sqrt hcase.le
      rwa [Real.sqrt_sq hX0.le] at this
    have hnX : (n : ℝ) / X ≤ Real.sqrt n := by
      rw [div_le_iff₀ hX0]
      calc (n : ℝ) = Real.sqrt n * Real.sqrt n := (Real.mul_self_sqrt hn0.le).symm
        _ ≤ Real.sqrt n * X := by
            apply mul_le_mul_of_nonneg_left hsX hsn0.le
    have hlogn : Real.log n ≤ 2 * L := by
      calc Real.log n ≤ Real.log (X ^ 2) := Real.log_le_log hn0 hcase.le
        _ = 2 * L := by rw [Real.log_pow, hLdef]; norm_num
    
    have hXb : X ≤ 4 * C * Real.sqrt n * L := by
      have hstep : C * (Real.sqrt n + n / X) * Real.log n ≤
          C * (Real.sqrt n + Real.sqrt n) * (2 * L) := by
        gcongr
      calc X ≤ C * (Real.sqrt n + n / X) * Real.log n := hkey
        _ ≤ C * (Real.sqrt n + Real.sqrt n) * (2 * L) := hstep
        _ = 4 * C * Real.sqrt n * L := by ring
    
    have hXsq : X ^ 2 ≤ 16 * C ^ 2 * n * L ^ 2 := by
      have h := pow_le_pow_left₀ hX0.le hXb 2
      calc X ^ 2 ≤ (4 * C * Real.sqrt n * L) ^ 2 := h
        _ = 16 * C ^ 2 * (Real.sqrt n * Real.sqrt n) * L ^ 2 := by ring
        _ = 16 * C ^ 2 * n * L ^ 2 := by rw [Real.mul_self_sqrt hn0.le]
    have hdiv : (X / L) ^ 2 ≤ 16 * C ^ 2 * n := by
      rw [div_pow, div_le_iff₀ (by positivity)]
      linarith
    calc min 1 (1 / (16 * C ^ 2)) * (X / L) ^ 2
        ≤ 1 / (16 * C ^ 2) * (X / L) ^ 2 := by
          apply mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
      _ ≤ 1 / (16 * C ^ 2) * (16 * C ^ 2 * n) := by
          apply mul_le_mul_of_nonneg_left hdiv (by positivity)
      _ = n := by field_simp


theorem main_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∃ p₀ : ℕ, ∀ p : ℕ, Fact p.Prime → p₀ ≤ p →
      ∀ A : Finset (ZMod p), 2 ≤ A.card → HasNoUniqueSum A →
        c * (Real.log p / Real.log (Real.log p)) ^ 2 ≤ A.card := by
  obtain ⟨C, hC, hkey⟩ := key_inequality
  obtain ⟨c, hc, hnum⟩ := numeric_reduction C hC
  refine ⟨c, hc, 64, ?_⟩
  intro p hp hp₀ A hA2 hAnus
  
  obtain ⟨B, hBA, hB2, hBnus, hBmin⟩ := exists_minimal A hA2 hAnus
  obtain ⟨a, ha⟩ := exists_enum B
  have hSnus : HasNoUniqueSum (Finset.univ.map a) := by rw [ha]; exact hBnus
  have hSmin : ∀ C', C' ⊂ Finset.univ.map a → 2 ≤ C'.card → ¬HasNoUniqueSum C' := by
    rw [ha]; exact hBmin
  let S : MinimalNUS p B.card := ⟨a, hB2, hSnus, hSmin⟩
  obtain ⟨P⟩ := S.exists_pairing
  have hkey' := hkey p B.card hp S P hp₀
  have hnum' := hnum p B.card hp₀ hB2 hkey'
  calc c * (Real.log p / Real.log (Real.log p)) ^ 2 ≤ B.card := hnum'
    _ ≤ A.card := by exact_mod_cast Finset.card_le_card hBA


end NUS

open Asymptotics Filter in
theorem NUS_bridge_nus {p : ℕ} (A : Finset (ZMod p)) (h : HasNoUniqueRepresentation A) :
    NUS.HasNoUniqueSum A := by
  intro t ⟨hcard, hmem⟩
  obtain ⟨a, b, rfl⟩ := Multiset.card_eq_two.mp hcard
  have ha : a ∈ A := hmem a (by simp)
  have hb : b ∈ A := hmem b (by simp)
  have hne : ¬ ((a + b) ∈ allUniqueSums (A : Set (ZMod p))) := by
    unfold HasNoUniqueRepresentation at h
    rw [h]; simp
  by_contra hcon
  apply hne
  refine ⟨(a, b), ha, hb, rfl, ?_⟩
  intro a1 h1 a2 h2 hs
  by_contra hno
  apply hcon
  refine ⟨{a1, a2}, ⟨rfl, ?_⟩, ?_, ?_⟩
  · intro x hx
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  · rw [Ne, NUS.multiset_pair_eq_pair]
    intro hh
    apply hno
    rcases hh with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact Or.inl ⟨e1, e2⟩
    · exact Or.inr ⟨e1, e2⟩
  · simp only [Multiset.insert_eq_cons, Multiset.sum_cons, Multiset.sum_singleton]
    exact hs

theorem NUS_bridge_rev {p : ℕ} (A : Finset (ZMod p)) (h : NUS.HasNoUniqueSum A) :
    HasNoUniqueRepresentation A := by
  unfold HasNoUniqueRepresentation
  apply Set.eq_empty_of_forall_notMem
  rintro n ⟨⟨x, y⟩, hx, hy, rfl, huniq⟩
  obtain ⟨t', ⟨hc, hm⟩, hne, hsum⟩ := h {x, y} ⟨rfl, by
    intro z hz
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> assumption⟩
  obtain ⟨a, b, rfl⟩ := Multiset.card_eq_two.mp hc
  have ha : a ∈ A := hm a (by simp)
  have hb : b ∈ A := hm b (by simp)
  simp only [Multiset.insert_eq_cons, Multiset.sum_cons, Multiset.sum_singleton] at hsum
  apply hne
  have := huniq a ha b hb hsum
  rw [NUS.multiset_pair_eq_pair]
  exact this

open Asymptotics Filter in
theorem OMA.solution : type_of% @Green27.green_27.variants.lower_be23 := by
  obtain ⟨c, hc, p0, hmain⟩ := NUS.main_lower_bound
  refine ⟨fun p => c * Real.log (p : ℝ) / (Real.log (Real.log (p : ℝ))) ^ 2, ?_, ?_⟩
  · have h1 : Tendsto (fun x : ℝ => Real.exp (Real.log x) / (Real.log x) ^ 2) atTop atTop :=
      (Real.tendsto_exp_div_pow_atTop 2).comp Real.tendsto_log_atTop
    have h2 : Tendsto (fun x : ℝ => x / (Real.log x) ^ 2) atTop atTop := by
      refine h1.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      rw [Real.exp_log hx]
    have h3 : Tendsto (fun x : ℝ => c * (x / (Real.log x) ^ 2)) atTop atTop :=
      h2.const_mul_atTop hc
    have h4 : Tendsto (fun p : ℕ => Real.log (p : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have h5 := h3.comp h4
    have h6 : Tendsto (fun p : ℕ => c * Real.log (p : ℝ) / (Real.log (Real.log (p : ℝ))) ^ 2)
        atTop atTop := by
      refine h5.congr (fun p => ?_)
      simp only [Function.comp]
      ring
    exact h6.mono_left inf_le_left
  · unfold Green27.primesAtTop
    rw [Filter.eventually_inf_principal]
    filter_upwards [eventually_ge_atTop (max p0 3)] with p hp hpp
    haveI : Fact p.Prime := ⟨hpp⟩
    have hp0 : p0 ≤ p := le_trans (le_max_left _ _) hp
    have hp3 : 3 ≤ p := le_trans (le_max_right _ _) hp
    have hp2 : p ≠ 2 := by omega
    have hlog : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hpp.one_lt)
    have hlow : ∀ x ∈ { (A.card : ℝ) | (A : Finset (ZMod p)) (_ : 2 ≤ A.card)
        (_ : HasNoUniqueRepresentation A) },
        c * (Real.log (p : ℝ) / Real.log (Real.log (p : ℝ))) ^ 2 ≤ x := by
      rintro x ⟨A, hA2, hAnus, rfl⟩
      exact hmain p ⟨hpp⟩ hp0 A hA2 (NUS_bridge_nus A hAnus)
    have hne : { (A.card : ℝ) | (A : Finset (ZMod p)) (_ : 2 ≤ A.card)
        (_ : HasNoUniqueRepresentation A) }.Nonempty := by
      refine ⟨(Finset.univ : Finset (ZMod p)).card, Finset.univ, ?_, ?_, rfl⟩
      · rw [Finset.card_univ, ZMod.card]; omega
      · exact NUS_bridge_rev _ (NUS.hasNoUniqueSum_univ p hp2)
    have := le_csInf hne hlow
    unfold Green27.m
    calc c * Real.log (p : ℝ) / (Real.log (Real.log (p : ℝ))) ^ 2 * Real.log (p : ℝ)
        = c * (Real.log (p : ℝ) / Real.log (Real.log (p : ℝ))) ^ 2 := by
          rw [div_pow]; ring
      _ ≤ _ := this
