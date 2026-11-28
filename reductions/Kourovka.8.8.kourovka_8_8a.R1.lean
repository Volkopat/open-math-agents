import FormalConjectures.Kourovka.«8_8»
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Finiteness
import Mathlib.Tactic

/-!
# Reduction of `Kourovka.«8.8».kourovka_8_8a`

Following V. S. Guba (*A finitely generated complete group*, Math. USSR-Izv. 29 (1986), 233–277),
A. Yu. Ol'shanskii (*On residualing homomorphisms and G-subgroups of hyperbolic groups*, Int. J.
Algebra Comput. 3 (1993), 365–409), and D. Osin (*Small cancellations over relatively hyperbolic
groups and embedding theorems*, Ann. of Math. 172 (2010), 1–39), we construct the required
non-cyclic 2-generated group `G = FreeGroup (Fin 2) ⧸ (⨆ k, N k)` as the direct limit of an
ascending chain of normal subgroups `N₀ ≤ N₁ ≤ …` of `FreeGroup (Fin 2)` whose quotients remain
torsion-free, non-abelian, word-hyperbolic, with primitive generator `ā = mk (of 0)`, reducing
the problem to two canonical theorems in hyperbolic and small-cancellation group theory:
1. `H1`: **Maximal cyclic / primitive root theorem for torsion-free word-hyperbolic quotients**
   (Gromov 1987 / Bridson–Haefliger III.Γ.3.10): in every torsion-free Gromov-hyperbolic
   2-generated quotient `Q = FreeGroup (Fin 2) ⧸ N`, every nontrivial element `g ≠ 1` is an
   integer power `c ^ r` of a primitive element `c ∈ Q` (`∀ h, ∀ n : ℤ, h ^ n = c → n = 1 ∨ n = -1`).
2. `H2`: **Small-cancellation conjugacy step preserving hyperbolicity, torsion-freeness, and
   primitivity** (Guba 1986 / Ol'shanskii 1993 / Osin 2010): for every torsion-free
   Gromov-hyperbolic quotient `Q = FreeGroup (Fin 2) ⧸ N` with `commutatorElement (of 0) (of 1) ∉ N`
   and `mk (of 0)` primitive, and every `c₀ : FreeGroup (Fin 2)` whose image `c̄` is primitive in
   `Q` and not conjugate to `mk (of 0)` or `(mk (of 0))⁻¹`, there exists a normal subgroup
   `N' ≥ N` such that `FreeGroup (Fin 2) ⧸ N'` retains all four invariants and `mk c₀` becomes
   conjugate to `mk (of 0)`.

Inside `main`, we prove from scratch:
- Complete verification of the base case `N₀ = ⊥` (`FreeGroup (Fin 2)`):
  * `0`-hyperbolicity via longest-common-prefix ultrametric on reduced words (`lcp`);
  * torsion-freeness via cyclic reduction of reduced words;
  * non-abelianness (`commutatorElement (of 0) (of 1) ≠ 1`);
  * primitivity of `of 0` via the projection `FreeGroup (Fin 2) →* Multiplicative ℤ`.
- Countable enumeration of `FreeGroup (Fin 2)` and inductive construction of the monotone chain
  `N : ℕ → Subgroup (FreeGroup (Fin 2))` making every word conjugate to a power of `of 0` at a
  finite stage.
- Direct-limit quotient `G = FreeGroup (Fin 2) ⧸ (⨆ k, N k)`: normality of `⨆ k, N k`,
  `Group.FG G`, `¬ IsCyclic G` (via directedness of `⨆` and `commutatorElement (of 0) (of 1) ∉ N k`),
  and `∀ g : G, ∃ n : ℤ, IsConj g (a ^ n)`.

Thanks to @MechaNuggan and @luciusacarr for the small-cancellation and HNN-extension analysis.
Credit: @tkaiman
-/

namespace OMA.R_Kourovka_8_8_kourovka_8_8a_R1

open FreeGroup

private abbrev F2 := FreeGroup (Fin 2)

private abbrev a0 : F2 := FreeGroup.of 0

private abbrev b0 : F2 := FreeGroup.of 1

private abbrev comm01 : F2 := a0 * b0 * a0⁻¹ * b0⁻¹

private def GoodQuot (N : Subgroup F2) [N.Normal] : Prop :=
  (∃ δ : ℕ, ∀ x y z w : F2 ⧸ N,
    let d (u v : F2 ⧸ N) : ℕ :=
      sInf {k : ℕ | ∃ s : F2, s.toWord.length = k ∧ QuotientGroup.mk s = u⁻¹ * v}
    d x y + d z w ≤ max (d x z + d y w) (d x w + d y z) + 2 * δ) ∧
  (∀ g : F2 ⧸ N, ∀ n : ℕ, n ≠ 0 → g ^ n = 1 → g = 1) ∧
  comm01 ∉ N ∧
  (∀ h : F2 ⧸ N, ∀ n : ℤ, h ^ n = QuotientGroup.mk a0 → n = 1 ∨ n = -1)

private def lcp {α : Type*} [DecidableEq α] : List α → List α → ℕ
  | x :: xs, y :: ys => if x = y then lcp xs ys + 1 else 0
  | _, _ => 0

private lemma lcp_ultrametric {α : Type*} [DecidableEq α] :
    ∀ l₁ l₂ l₃ : List α, min (lcp l₁ l₃) (lcp l₂ l₃) ≤ lcp l₁ l₂
  | [], _, _ => by simp [lcp]
  | _, [], _ => by simp [lcp]
  | _, _, [] => by simp [lcp]
  | x :: xs, y :: ys, z :: zs => by
    simp only [lcp]
    by_cases hxz : x = z
    · by_cases hyz : y = z
      · simp only [hxz, hyz, ↓reduceIte]
        have ih := lcp_ultrametric xs ys zs
        omega
      · simp [hxz, hyz]
    · simp [hxz]

private lemma isReduced_tail {α : Type*} {x : α × Bool} {L : List (α × Bool)}
    (h : FreeGroup.IsReduced (x :: L)) : FreeGroup.IsReduced L := by
  exact List.IsChain.tail h

private lemma isReduced_invRev {α : Type*} [DecidableEq α] {L : List (α × Bool)}
    (h : FreeGroup.IsReduced L) : FreeGroup.IsReduced (FreeGroup.invRev L) := by
  rw [FreeGroup.isReduced_iff_reduce_eq, FreeGroup.reduce_invRev, h.reduce_eq]

private lemma isReduced_append_of_join {α : Type*} [DecidableEq α]
    {L₁ L₂ : List (α × Bool)} {x y : α × Bool}
    (h₁ : FreeGroup.IsReduced (L₁ ++ [x])) (h₂ : FreeGroup.IsReduced (y :: L₂))
    (hjoin : ¬ (x.1 = y.1 ∧ x.2 = !y.2)) :
    FreeGroup.IsReduced (L₁ ++ [x] ++ y :: L₂) := by
  rw [FreeGroup.IsReduced] at h₁ h₂ ⊢
  rw [List.append_assoc, List.singleton_append]
  have hrel : (fun a b : α × Bool => a.1 = b.1 → a.2 = b.2) x y := by
    intro hfst
    cases hx : x.2 <;> cases hy : y.2
    · rfl
    · exfalso; exact hjoin ⟨hfst, by simp [hx, hy]⟩
    · exfalso; exact hjoin ⟨hfst, by simp [hx, hy]⟩
    · rfl
  have h2' : List.IsChain (fun a b : α × Bool => a.1 = b.1 → a.2 = b.2) (x :: y :: L₂) :=
    List.IsChain.cons_cons hrel h₂
  induction L₁ with
  | nil => exact h2'
  | cons hd tl ih =>
    simp only [List.cons_append] at h₁ ⊢
    cases tl with
    | nil =>
      simp only [List.nil_append] at h₁ ⊢
      exact List.IsChain.cons_cons (List.isChain_cons_cons.mp h₁).1 h2'
    | cons hd2 tl2 =>
      exact List.IsChain.cons_cons (List.isChain_cons_cons.mp h₁).1 (ih (List.IsChain.tail h₁))

private lemma reduce_invRev_append_length {α : Type*} [DecidableEq α] :
    ∀ (L₁ L₂ : List (α × Bool)),
      FreeGroup.IsReduced L₁ → FreeGroup.IsReduced L₂ →
      (FreeGroup.reduce (FreeGroup.invRev L₁ ++ L₂)).length + 2 * lcp L₁ L₂ =
        L₁.length + L₂.length
  | [], L₂, _, h₂ => by
    simp [lcp, FreeGroup.invRev, h₂.reduce_eq]
  | L₁, [], h₁, _ => by
    have hr := isReduced_invRev h₁
    simp [lcp, hr.reduce_eq, FreeGroup.invRev_length]
  | x :: xs, y :: ys, h₁, h₂ => by
    have hinv_cons : FreeGroup.invRev (x :: xs) = FreeGroup.invRev xs ++ [(x.1, !x.2)] := by
      simp [FreeGroup.invRev]
    by_cases hxy : x = y
    · subst hxy
      have hred_eq : FreeGroup.reduce (FreeGroup.invRev (x :: xs) ++ x :: ys) =
          FreeGroup.reduce (FreeGroup.invRev xs ++ ys) := by
        rw [hinv_cons, List.append_assoc, List.singleton_append]
        have hstep : FreeGroup.Red.Step (FreeGroup.invRev xs ++ (x.1, !x.2) :: x :: ys)
            (FreeGroup.invRev xs ++ ys) := by
          have hnot : (x.1, !!x.2) = x := by cases x; simp
          simpa [hnot] using
            (@FreeGroup.Red.Step.not α (FreeGroup.invRev xs) ys x.1 (!x.2))
        exact FreeGroup.reduce.Step.eq hstep
      rw [hred_eq]
      simp only [lcp, ↓reduceIte, List.length_cons]
      have ih := reduce_invRev_append_length xs ys (isReduced_tail h₁) (isReduced_tail h₂)
      omega
    · have hlcp : lcp (x :: xs) (y :: ys) = 0 := by simp [lcp, hxy]
      have hjoin : ¬ ((x.1, !x.2).1 = y.1 ∧ (x.1, !x.2).2 = !y.2) := by
        rintro ⟨h1, h2⟩
        apply hxy
        ext
        · exact h1
        · cases hx : x.2 <;> cases hy : y.2 <;> simp_all
      have hred_all : FreeGroup.IsReduced (FreeGroup.invRev (x :: xs) ++ y :: ys) := by
        rw [hinv_cons]
        have hinv_red : FreeGroup.IsReduced (FreeGroup.invRev xs ++ [(x.1, !x.2)]) := by
          rw [← hinv_cons]
          exact isReduced_invRev h₁
        exact isReduced_append_of_join hinv_red h₂ hjoin
      rw [hlcp, hred_all.reduce_eq, List.length_append, FreeGroup.invRev_length]
      omega

private lemma freeGroup_zero_hyperbolic (x y z w : F2) :
    (x⁻¹ * y).toWord.length + (z⁻¹ * w).toWord.length ≤
      max ((x⁻¹ * z).toWord.length + (y⁻¹ * w).toWord.length)
          ((x⁻¹ * w).toWord.length + (y⁻¹ * z).toWord.length) := by
  let u := w⁻¹ * x
  let v := w⁻¹ * y
  let t := w⁻¹ * z
  have hxy : x⁻¹ * y = u⁻¹ * v := by simp [u, v, mul_assoc]
  have hzw : z⁻¹ * w = t⁻¹ := by simp [t]
  have hxz : x⁻¹ * z = u⁻¹ * t := by simp [u, t, mul_assoc]
  have hyw : y⁻¹ * w = v⁻¹ := by simp [v]
  have hxw : x⁻¹ * w = u⁻¹ := by simp [u]
  have hyz : y⁻¹ * z = v⁻¹ * t := by simp [v, t, mul_assoc]
  rw [hxy, hzw, hxz, hyw, hxw, hyz]
  have hinv_len : ∀ g : F2, g⁻¹.toWord.length = g.toWord.length := fun g => by
    rw [FreeGroup.toWord_inv, FreeGroup.invRev_length]
  rw [hinv_len t, hinv_len v, hinv_len u]
  have hmul : ∀ p q : F2,
      (p⁻¹ * q).toWord.length + 2 * lcp p.toWord q.toWord =
        p.toWord.length + q.toWord.length := fun p q => by
    rw [FreeGroup.toWord_mul, FreeGroup.toWord_inv]
    exact reduce_invRev_append_length p.toWord q.toWord
      FreeGroup.isReduced_toWord FreeGroup.isReduced_toWord
  have h1 := hmul u v
  have h2 := hmul u t
  have h3 := hmul v t
  have hultra := lcp_ultrametric u.toWord v.toWord t.toWord
  omega

private lemma isReduced_replicate_flatten {α : Type*} [DecidableEq α]
    {L : List (α × Bool)} (hred : FreeGroup.IsReduced L)
    (hcyc : ∀ a b L', (hL : L = a :: L') → L.getLast (by simp [hL]) = b →
      ¬ (b.1 = a.1 ∧ b.2 = !a.2)) :
    ∀ n : ℕ, FreeGroup.IsReduced (List.replicate n L).flatten
  | 0 => by simp [FreeGroup.IsReduced]
  | 1 => by simpa using hred
  | n + 2 => by
    rw [List.replicate_succ, List.flatten_cons]
    cases hL : L with
    | nil => simp [FreeGroup.IsReduced]
    | cons a L' =>
      have hne : L ≠ [] := by simp [hL]
      have hsplit : L = L.dropLast ++ [L.getLast hne] := (List.dropLast_append_getLast hne).symm
      have htail_red : FreeGroup.IsReduced (List.replicate (n + 1) L).flatten :=
        isReduced_replicate_flatten hred hcyc (n + 1)
      have htail_cons : (List.replicate (n + 1) L).flatten =
          a :: (L' ++ (List.replicate n L).flatten) := by
        rw [List.replicate_succ, List.flatten_cons, hL, List.cons_append]
      have hjoin := hcyc a (L.getLast hne) L' hL rfl
      rw [htail_cons] at htail_red
      rw [← hL, htail_cons]
      have h1 : FreeGroup.IsReduced (L.dropLast ++ [L.getLast hne]) := hsplit ▸ hred
      have hres := isReduced_append_of_join h1 htail_red hjoin
      rwa [← hsplit] at hres

private lemma freeGroup_torsionFree (g : F2) (n : ℕ) (hn : n ≠ 0) (hg : g ^ n = 1) : g = 1 := by
  suffices ∀ k : ℕ, ∀ x : F2, x.toWord.length ≤ k → x ^ n = 1 → x = 1 from
    this g.toWord.length g le_rfl hg
  intro k
  induction k with
  | zero =>
    intro x hx _
    have h0 : x.toWord = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hx)
    exact FreeGroup.toWord_eq_nil_iff.mp h0
  | succ k ih =>
    intro x hx hxn
    cases hL : x.toWord with
    | nil => exact FreeGroup.toWord_eq_nil_iff.mp hL
    | cons a L' =>
      by_cases hcancel :
          (x.toWord.getLast (by simp [hL])).1 = a.1 ∧
          (x.toWord.getLast (by simp [hL])).2 = !a.2
      · cases L' with
        | nil =>
          simp [hL] at hcancel
        | cons c rest =>
          have hne : (a :: c :: rest).length ≥ 2 := by simp
          have hsplit := List.dropLast_append_getLast (l := c :: rest) (by simp)
          set b := (c :: rest).getLast (by simp)
          set m := (c :: rest).dropLast
          have hb_eq : x.toWord.getLast (by simp [hL]) = b := by
            simp [hL, b]
          have hb_inv : b = (a.1, !a.2) := by
            rw [hb_eq] at hcancel
            exact Prod.ext hcancel.1 hcancel.2
          have hx_eq : x = FreeGroup.mk [a] * FreeGroup.mk m * (FreeGroup.mk [a])⁻¹ := by
            rw [← FreeGroup.mk_toWord (x := x), hL, ← hsplit, hb_inv]
            have hinv_a : (FreeGroup.mk [a])⁻¹ = FreeGroup.mk [(a.1, !a.2)] := by
              rw [FreeGroup.inv_mk]; rfl
            rw [hinv_a, FreeGroup.mul_mk, FreeGroup.mul_mk]
            simp [List.cons_append]
          have hm_pow : (FreeGroup.mk m) ^ n = 1 := by
            have hconj : (FreeGroup.mk [a] * FreeGroup.mk m * (FreeGroup.mk [a])⁻¹) ^ n =
                FreeGroup.mk [a] * (FreeGroup.mk m) ^ n * (FreeGroup.mk [a])⁻¹ :=
              conj_pow
            rw [hx_eq, hconj] at hxn
            have h1 : FreeGroup.mk [a] * (FreeGroup.mk m) ^ n = FreeGroup.mk [a] * 1 := by
              calc FreeGroup.mk [a] * (FreeGroup.mk m) ^ n
                  = FreeGroup.mk [a] * (FreeGroup.mk m) ^ n * (FreeGroup.mk [a])⁻¹ *
                      FreeGroup.mk [a] := by rw [mul_assoc, inv_mul_cancel, mul_one]
                _ = 1 * FreeGroup.mk [a] := congrArg (· * FreeGroup.mk [a]) hxn
                _ = FreeGroup.mk [a] * 1 := by rw [one_mul, mul_one]
            exact mul_left_cancel h1
          have hm_len : (FreeGroup.mk m).toWord.length ≤ k := by
            have h1 : (FreeGroup.mk m).toWord.length ≤ m.length := FreeGroup.norm_mk_le
            have h2 : m.length + 1 = (c :: rest).length := by
              have hlen := congrArg List.length hsplit
              simp only [List.length_append, List.length_singleton] at hlen
              exact hlen
            have h3 : x.toWord.length = (c :: rest).length + 1 := by simp [hL]
            omega
          have hm1 : FreeGroup.mk m = 1 := ih (FreeGroup.mk m) hm_len hm_pow
          rw [hx_eq, hm1, mul_one, mul_inv_cancel]
      · have hred_rep : FreeGroup.IsReduced (List.replicate n x.toWord).flatten := by
          refine isReduced_replicate_flatten FreeGroup.isReduced_toWord ?_ n
          intro a' b' L'' hL'' hb'
          rw [hL] at hL''
          injection hL'' with ha' _
          subst ha' hb'
          exact hcancel
        have htw : (x ^ n).toWord = (List.replicate n x.toWord).flatten := by
          rw [FreeGroup.toWord_pow, hred_rep.reduce_eq]
        rw [hxn, FreeGroup.toWord_one] at htw
        have hlen := congrArg List.length htw
        simp only [List.length_nil, List.length_flatten, List.map_replicate, List.sum_replicate,
          smul_eq_mul, hL, List.length_cons] at hlen
        have hpos : 0 < n * (L'.length + 1) := Nat.mul_pos (Nat.pos_of_ne_zero hn) (Nat.succ_pos _)
        omega

private lemma commutator_ne_one_F2 : comm01 ≠ 1 := by
  intro h
  have htw := congrArg FreeGroup.toWord h
  have hcalc : comm01.toWord =
      [(0, true), (1, true), (0, false), (1, false)] := by
    change (a0 * b0 * a0⁻¹ * b0⁻¹).toWord = _
    simp [a0, b0, FreeGroup.toWord_mul, FreeGroup.toWord_inv, FreeGroup.invRev]
  rw [hcalc, FreeGroup.toWord_one] at htw
  cases htw

private lemma a0_primitive_F2 (g : F2) (n : ℤ) (h : g ^ n = a0) : n = 1 ∨ n = -1 := by
  let φ : F2 →* Multiplicative ℤ :=
    FreeGroup.lift fun i : Fin 2 => if i = 0 then Multiplicative.ofAdd (1 : ℤ) else 1
  have hφ := congrArg φ h
  rw [map_zpow] at hφ
  have hφa : φ a0 = Multiplicative.ofAdd (1 : ℤ) := by simp [φ, a0]
  rw [hφa] at hφ
  have hmul : n * Multiplicative.toAdd (φ g) = 1 := by
    have h1 := congrArg Multiplicative.toAdd hφ
    simpa [toAdd_zpow, zsmul_eq_mul] using h1
  exact Int.eq_one_or_neg_one_of_mul_eq_one hmul

/-- **Primitive root / maximal cyclic subgroup theorem for torsion-free word-hyperbolic quotients**
(Gromov 1987 / Bridson–Haefliger III.Γ.3.10): in every torsion-free Gromov-hyperbolic quotient
`Q = FreeGroup (Fin 2) ⧸ N`, every nontrivial element `g ≠ 1` is an integer power `c ^ r` of a
primitive element `c ∈ Q` (`∀ h : Q, ∀ n : ℤ, h ^ n = c → n = 1 ∨ n = -1`). -/
def H1 : Prop :=
  ∀ (N : Subgroup (FreeGroup (Fin 2))) [N.Normal],
    (∃ δ : ℕ, ∀ x y z w : FreeGroup (Fin 2) ⧸ N,
      let d (u v : FreeGroup (Fin 2) ⧸ N) : ℕ :=
        sInf {k : ℕ | ∃ s : FreeGroup (Fin 2), s.toWord.length = k ∧ QuotientGroup.mk s = u⁻¹ * v}
      d x y + d z w ≤ max (d x z + d y w) (d x w + d y z) + 2 * δ) →
    (∀ g : FreeGroup (Fin 2) ⧸ N, ∀ n : ℕ, n ≠ 0 → g ^ n = 1 → g = 1) →
    ∀ g : FreeGroup (Fin 2) ⧸ N, g ≠ 1 →
      ∃ (c : FreeGroup (Fin 2) ⧸ N) (r : ℤ),
        (∀ h : FreeGroup (Fin 2) ⧸ N, ∀ n : ℤ, h ^ n = c → n = 1 ∨ n = -1) ∧
        g = c ^ r

/-- **Small-cancellation conjugacy step preserving hyperbolicity, torsion-freeness, and
primitivity** (Guba 1986 / Ol'shanskii 1993 / Osin 2010): given a torsion-free Gromov-hyperbolic
quotient `Q = FreeGroup (Fin 2) ⧸ N` with `commutatorElement (of 0) (of 1) ∉ N` and `mk (of 0)`
primitive, and any `c₀ : FreeGroup (Fin 2)` whose image `c̄` is primitive in `Q` and not conjugate
to `mk (of 0)` or `(mk (of 0))⁻¹`, there exists a normal subgroup `N' ≥ N` such that
`FreeGroup (Fin 2) ⧸ N'` remains Gromov-hyperbolic, torsion-free, non-abelian with `mk (of 0)`
primitive, and `mk c₀` becomes conjugate to `mk (of 0)`. -/
def H2 : Prop :=
  ∀ (N : Subgroup (FreeGroup (Fin 2))) [N.Normal],
    (∃ δ : ℕ, ∀ x y z w : FreeGroup (Fin 2) ⧸ N,
      let d (u v : FreeGroup (Fin 2) ⧸ N) : ℕ :=
        sInf {k : ℕ | ∃ s : FreeGroup (Fin 2), s.toWord.length = k ∧ QuotientGroup.mk s = u⁻¹ * v}
      d x y + d z w ≤ max (d x z + d y w) (d x w + d y z) + 2 * δ) →
    (∀ g : FreeGroup (Fin 2) ⧸ N, ∀ n : ℕ, n ≠ 0 → g ^ n = 1 → g = 1) →
    (FreeGroup.of (0 : Fin 2) * FreeGroup.of 1 * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 1)⁻¹) ∉ N →
    (∀ h : FreeGroup (Fin 2) ⧸ N, ∀ n : ℤ,
      h ^ n = QuotientGroup.mk (FreeGroup.of 0) → n = 1 ∨ n = -1) →
    ∀ c₀ : FreeGroup (Fin 2),
      (∀ h : FreeGroup (Fin 2) ⧸ N, ∀ n : ℤ, h ^ n = QuotientGroup.mk c₀ → n = 1 ∨ n = -1) →
      ¬ IsConj (QuotientGroup.mk c₀ : FreeGroup (Fin 2) ⧸ N) (QuotientGroup.mk (FreeGroup.of 0)) →
      ¬ IsConj (QuotientGroup.mk c₀ : FreeGroup (Fin 2) ⧸ N)
          (QuotientGroup.mk (FreeGroup.of 0))⁻¹ →
      ∃ (N' : Subgroup (FreeGroup (Fin 2))) (_ : N'.Normal),
        N ≤ N' ∧
        (∃ δ : ℕ, ∀ x y z w : FreeGroup (Fin 2) ⧸ N',
          let d (u v : FreeGroup (Fin 2) ⧸ N') : ℕ :=
            sInf {k : ℕ | ∃ s : FreeGroup (Fin 2), s.toWord.length = k ∧
              QuotientGroup.mk s = u⁻¹ * v}
          d x y + d z w ≤ max (d x z + d y w) (d x w + d y z) + 2 * δ) ∧
        (∀ g : FreeGroup (Fin 2) ⧸ N', ∀ n : ℕ, n ≠ 0 → g ^ n = 1 → g = 1) ∧
        (FreeGroup.of (0 : Fin 2) * FreeGroup.of 1 * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 1)⁻¹) ∉ N' ∧
        (∀ h : FreeGroup (Fin 2) ⧸ N', ∀ n : ℤ,
          h ^ n = QuotientGroup.mk (FreeGroup.of 0) → n = 1 ∨ n = -1) ∧
        IsConj (QuotientGroup.mk c₀ : FreeGroup (Fin 2) ⧸ N') (QuotientGroup.mk (FreeGroup.of 0))

theorem main : H1 → H2 → type_of% @Kourovka.«8.8».kourovka_8_8a := by
  intro h1 h2
  -- Inductive invariant bundled as a record
  let Inv (N : Subgroup F2) : Prop := ∃ h : N.Normal, @GoodQuot N h
  -- Step 1: Verify the base case `N₀ = ⊥`
  have hbase : Inv ⊥ := by
    refine ⟨inferInstance, ?_, ?_, ?_, ?_⟩
    · refine ⟨0, fun x y z w => ?_⟩
      obtain ⟨x₀, rfl⟩ := QuotientGroup.mk_surjective x
      obtain ⟨y₀, rfl⟩ := QuotientGroup.mk_surjective y
      obtain ⟨z₀, rfl⟩ := QuotientGroup.mk_surjective z
      obtain ⟨w₀, rfl⟩ := QuotientGroup.mk_surjective w
      have hd : ∀ p q : F2,
          sInf {k : ℕ | ∃ s : F2, s.toWord.length = k ∧
            (QuotientGroup.mk s : F2 ⧸ (⊥ : Subgroup F2)) =
              (QuotientGroup.mk p)⁻¹ * QuotientGroup.mk q} = (p⁻¹ * q).toWord.length := by
        intro p q
        have hset : {k : ℕ | ∃ s : F2, s.toWord.length = k ∧
            (QuotientGroup.mk s : F2 ⧸ (⊥ : Subgroup F2)) =
              (QuotientGroup.mk p)⁻¹ * QuotientGroup.mk q} = {(p⁻¹ * q).toWord.length} := by
          ext k
          simp only [Set.mem_singleton_iff]
          constructor
          · rintro ⟨s, rfl, hmk⟩
            have heq : (QuotientGroup.mk s : F2 ⧸ (⊥ : Subgroup F2)) =
                QuotientGroup.mk (p⁻¹ * q) := by
              simpa [QuotientGroup.mk_mul, QuotientGroup.mk_inv] using hmk
            have hmem : (p⁻¹ * q)⁻¹ * s ∈ (⊥ : Subgroup F2) :=
              (QuotientGroup.eq).mp heq.symm
            rw [Subgroup.mem_bot] at hmem
            have hs : s = p⁻¹ * q := inv_mul_eq_one.mp hmem |>.symm
            rw [hs]
          · rintro rfl
            exact ⟨p⁻¹ * q, rfl, by simp [QuotientGroup.mk_mul, QuotientGroup.mk_inv]⟩
        rw [hset, csInf_singleton]
      simp only [hd, mul_zero, add_zero]
      exact freeGroup_zero_hyperbolic x₀ y₀ z₀ w₀
    · intro g n hn hgn
      obtain ⟨g₀, rfl⟩ := QuotientGroup.mk_surjective g
      have hmem : g₀ ^ n ∈ (⊥ : Subgroup F2) :=
        (QuotientGroup.eq_one_iff (g₀ ^ n)).mp (by simpa [QuotientGroup.mk_pow] using hgn)
      rw [Subgroup.mem_bot] at hmem
      rw [freeGroup_torsionFree g₀ n hn hmem]
      rfl
    · rw [Subgroup.mem_bot]
      exact commutator_ne_one_F2
    · intro h n hn
      obtain ⟨h₀, rfl⟩ := QuotientGroup.mk_surjective h
      have heq : (QuotientGroup.mk (h₀ ^ n) : F2 ⧸ (⊥ : Subgroup F2)) = QuotientGroup.mk a0 := by
        simpa [QuotientGroup.mk_zpow] using hn
      have hmem : a0⁻¹ * h₀ ^ n ∈ (⊥ : Subgroup F2) := (QuotientGroup.eq).mp heq.symm
      rw [Subgroup.mem_bot] at hmem
      exact a0_primitive_F2 h₀ n (inv_mul_eq_one.mp hmem |>.symm)
  -- Step 2: Single-word conjugacy extension step
  have hstep : ∀ (N : Subgroup F2), Inv N → ∀ w : F2,
      ∃ N' : Subgroup F2, N ≤ N' ∧ Inv N' ∧
        ∃ (u : F2) (n : ℤ), u * w * u⁻¹ * (a0 ^ n)⁻¹ ∈ N' := by
    intro N hN w
    obtain ⟨hN_norm, hN_hyp, hN_tf, hN_comm, hN_prim⟩ := hN
    have : N.Normal := hN_norm
    by_cases hw1 : (QuotientGroup.mk w : F2 ⧸ N) = 1
    · refine ⟨N, le_rfl, ⟨hN_norm, hN_hyp, hN_tf, hN_comm, hN_prim⟩, 1, 0, ?_⟩
      simpa [QuotientGroup.eq_one_iff] using hw1
    · obtain ⟨c, r, hc_prim, hwr⟩ := h1 N hN_hyp hN_tf (QuotientGroup.mk w) hw1
      have hconj_to_mem : ∀ (N' : Subgroup F2) [N'.Normal] (n : ℤ),
          IsConj (QuotientGroup.mk w : F2 ⧸ N') (QuotientGroup.mk a0 ^ n) →
          ∃ u : F2, u * w * u⁻¹ * (a0 ^ n)⁻¹ ∈ N' := by
        intro N' _ n hconj
        rw [isConj_iff] at hconj
        obtain ⟨uBar, huBar⟩ := hconj
        obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective uBar
        refine ⟨u, ?_⟩
        rw [← QuotientGroup.eq_one_iff]
        have hu' : (QuotientGroup.mk (u * w * u⁻¹) : F2 ⧸ N') = QuotientGroup.mk (a0 ^ n) := by
          simpa [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_zpow] using huBar
        simp [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hu']
      have isConj_zpow : ∀ {G : Type} [Group G] {x y : G},
          IsConj x y → ∀ k : ℤ, IsConj (x ^ k) (y ^ k) := by
        intro G _ x y hxy k
        rw [isConj_iff] at hxy ⊢
        obtain ⟨u, hu⟩ := hxy
        exact ⟨u, by rw [← conj_zpow, hu]⟩
      by_cases hc1 : IsConj c (QuotientGroup.mk a0)
      · have hw_conj : IsConj (QuotientGroup.mk w : F2 ⧸ N) (QuotientGroup.mk a0 ^ r) := by
          rw [hwr]
          exact isConj_zpow hc1 r
        obtain ⟨u, hu⟩ := hconj_to_mem N r hw_conj
        exact ⟨N, le_rfl, ⟨hN_norm, hN_hyp, hN_tf, hN_comm, hN_prim⟩, u, r, hu⟩
      · by_cases hc2 : IsConj c (QuotientGroup.mk a0)⁻¹
        · have hw_conj : IsConj (QuotientGroup.mk w : F2 ⧸ N) (QuotientGroup.mk a0 ^ (-r)) := by
            rw [hwr, zpow_neg, ← inv_zpow]
            exact isConj_zpow hc2 r
          obtain ⟨u, hu⟩ := hconj_to_mem N (-r) hw_conj
          exact ⟨N, le_rfl, ⟨hN_norm, hN_hyp, hN_tf, hN_comm, hN_prim⟩, u, -r, hu⟩
        · obtain ⟨c₀, rfl⟩ := QuotientGroup.mk_surjective c
          obtain ⟨N', hN'_norm, hle, hN'_hyp, hN'_tf, hN'_comm, hN'_prim, hc'_conj⟩ :=
            h2 N hN_hyp hN_tf hN_comm hN_prim c₀ hc_prim hc1 hc2
          have : N'.Normal := hN'_norm
          have hwr' : (QuotientGroup.mk w : F2 ⧸ N') = QuotientGroup.mk c₀ ^ r := by
            have hdiff : (c₀ ^ r)⁻¹ * w ∈ N := by
              rw [← QuotientGroup.eq]
              simpa [QuotientGroup.mk_zpow] using hwr.symm
            have hdiff' : (c₀ ^ r)⁻¹ * w ∈ N' := hle hdiff
            have := (QuotientGroup.eq).mpr hdiff'
            simpa [QuotientGroup.mk_zpow] using this.symm
          have hw_conj : IsConj (QuotientGroup.mk w : F2 ⧸ N') (QuotientGroup.mk a0 ^ r) := by
            rw [hwr']
            exact isConj_zpow hc'_conj r
          obtain ⟨u, hu⟩ := hconj_to_mem N' r hw_conj
          exact ⟨N', hle, ⟨hN'_norm, hN'_hyp, hN'_tf, hN'_comm, hN'_prim⟩, u, r, hu⟩
  -- Step 3: Enumerate `FreeGroup (Fin 2)` and build the ascending chain `N : ℕ → Subgroup F2`
  have hcount : Countable F2 := by
    refine Function.Injective.countable (f := FreeGroup.toWord) FreeGroup.toWord_injective
  obtain ⟨enum, henum⟩ := exists_surjective_nat F2
  let recChain : ℕ → {N : Subgroup F2 // Inv N} :=
    Nat.rec ⟨⊥, hbase⟩ fun k acc =>
      let hex := hstep acc.1 acc.2 (enum k)
      ⟨Classical.choose hex, (Classical.choose_spec hex).2.1⟩
  let N : ℕ → Subgroup F2 := fun k => (recChain k).1
  have hN_inv : ∀ k, Inv (N k) := fun k => (recChain k).2
  have hN_step : ∀ k, N k ≤ N (k + 1) ∧
      ∃ (u : F2) (n : ℤ), u * enum k * u⁻¹ * (a0 ^ n)⁻¹ ∈ N (k + 1) := by
    intro k
    have hspec := Classical.choose_spec (hstep (recChain k).1 (recChain k).2 (enum k))
    exact ⟨hspec.1, hspec.2.2⟩
  have hN_mono : Monotone N := monotone_nat_of_le_succ fun k => (hN_step k).1
  have hN_dir : Directed (· ≤ ·) N := hN_mono.directed_le
  -- Step 4: Form the direct limit quotient `G = F2 ⧸ (⨆ k, N k)`
  let Ninf : Subgroup F2 := ⨆ k, N k
  have hNinf_mem : ∀ x : F2, x ∈ Ninf ↔ ∃ k, x ∈ N k :=
    fun x => Subgroup.mem_iSup_of_directed hN_dir
  have hNinf_norm : Ninf.Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨k, hk⟩ := (hNinf_mem x).mp hx
    obtain ⟨hNk_norm, _⟩ := hN_inv k
    exact (hNinf_mem _).mpr ⟨k, hNk_norm.conj_mem x hk g⟩
  have : Ninf.Normal := hNinf_norm
  refine ⟨F2 ⧸ Ninf, inferInstance, ?_, ?_, QuotientGroup.mk a0, ?_⟩
  · -- `¬ IsCyclic (F2 ⧸ Ninf)` since `[a0, b0] ∉ Ninf`
    intro hcyc
    have hcomm : (QuotientGroup.mk a0 : F2 ⧸ Ninf) * QuotientGroup.mk b0 =
        QuotientGroup.mk b0 * QuotientGroup.mk a0 := by
      obtain ⟨g, hg⟩ := hcyc
      obtain ⟨m, hm⟩ := hg (QuotientGroup.mk a0)
      obtain ⟨n, hn⟩ := hg (QuotientGroup.mk b0)
      rw [← hm, ← hn, ← zpow_add, ← zpow_add, add_comm]
    have h1 : (QuotientGroup.mk comm01 : F2 ⧸ Ninf) = 1 := by
      change (QuotientGroup.mk a0 : F2 ⧸ Ninf) * QuotientGroup.mk b0 *
        (QuotientGroup.mk a0)⁻¹ * (QuotientGroup.mk b0)⁻¹ = 1
      rw [hcomm]
      group
    have hmem : comm01 ∈ Ninf := (QuotientGroup.eq_one_iff _).mp h1
    obtain ⟨k, hk⟩ := (hNinf_mem _).mp hmem
    obtain ⟨_, _, _, hNk_comm, _⟩ := hN_inv k
    exact hNk_comm hk
  · -- `Group.FG (F2 ⧸ Ninf)` as a quotient of the 2-generated group `FreeGroup (Fin 2)`
    classical
    let S : Finset (F2 ⧸ Ninf) := {QuotientGroup.mk a0, QuotientGroup.mk b0}
    have hof_mem : ∀ i : Fin 2, (QuotientGroup.mk (FreeGroup.of i) : F2 ⧸ Ninf) ∈
        Subgroup.closure (S : Set (F2 ⧸ Ninf)) := by
      intro i
      fin_cases i
      · exact Subgroup.subset_closure (by simp [S, a0])
      · exact Subgroup.subset_closure (by simp [S, b0])
    have hmemS : ∀ x : F2, (QuotientGroup.mk x : F2 ⧸ Ninf) ∈
        Subgroup.closure (S : Set (F2 ⧸ Ninf)) := by
      intro x
      induction x using FreeGroup.induction_on with
      | C1 => exact Subgroup.one_mem _
      | of i => exact hof_mem i
      | inv_of i => exact Subgroup.inv_mem _ (hof_mem i)
      | mul _ _ hx hy => exact Subgroup.mul_mem _ hx hy
    refine ⟨S, ?_⟩
    rw [eq_top_iff]
    intro g _
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
    exact hmemS x
  · -- Every element of `F2 ⧸ Ninf` is conjugate to a power of `QuotientGroup.mk a0`
    intro g
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨k, rfl⟩ := henum w
    obtain ⟨u, n, hu⟩ := (hN_step k).2
    refine ⟨n, ?_⟩
    rw [isConj_iff]
    refine ⟨QuotientGroup.mk u, ?_⟩
    have hmem : u * enum k * u⁻¹ * (a0 ^ n)⁻¹ ∈ Ninf :=
      (hNinf_mem _).mpr ⟨k + 1, hu⟩
    have h1 : (QuotientGroup.mk (u * enum k * u⁻¹ * (a0 ^ n)⁻¹) : F2 ⧸ Ninf) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hmem
    have h2 : (QuotientGroup.mk u : F2 ⧸ Ninf) * QuotientGroup.mk (enum k) *
        (QuotientGroup.mk u)⁻¹ * ((QuotientGroup.mk a0 : F2 ⧸ Ninf) ^ n)⁻¹ = 1 := by
      simpa [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_zpow] using h1
    exact mul_inv_eq_one.mp h2

end OMA.R_Kourovka_8_8_kourovka_8_8a_R1
