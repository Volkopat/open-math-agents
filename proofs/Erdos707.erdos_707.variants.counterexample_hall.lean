import FormalConjectures.ErdosProblems.«707»
import Mathlib.Tactic

/-!
# Proof of Erdos 707 Hall counterexample

Original Lean proof: @mattdorman, PR #276. The involution-parity and modular-cancellation
helpers use Mathlib’s fixed-point and unit APIs.
-/

section OMA707

lemma oma_even_card_of_fpf_involution {α : Type*} [DecidableEq α] :
    ∀ (n : ℕ) (T : Finset α) (f : α → α),
      T.card = n →
      (∀ x ∈ T, f x ∈ T) →
      (∀ x ∈ T, f (f x) = x) →
      (∀ x ∈ T, f x ≠ x) →
      Even T.card
  := by
  intro n T f _ hmem hinv hne
  classical
  let g : T → T := fun x => ⟨f x, hmem x x.property⟩
  have hg : Function.Involutive g := fun x => Subtype.ext (hinv x x.property)
  let e : Equiv.Perm T := hg.toPerm g
  rw [even_iff_two_dvd, ← Fintype.card_coe]
  by_contra hc
  have he : e ^ 2 ^ 1 = 1 := by
    apply Equiv.ext
    intro x
    exact hg x
  obtain ⟨x, hx⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := 2) (n := 1) hc he
  exact hne x x.property (congrArg Subtype.val hx)

structure IsFinsetPDS {v : ℕ} [NeZero v] (S : Finset (ZMod v)) : Prop where
  uniq_diff : ∀ d : ZMod v, d ≠ 0 →
    ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ a - b = d ∧
      ∀ a' ∈ S, ∀ b' ∈ S, a' ≠ b' → a' - b' = d → a' = a ∧ b' = b

lemma oma_finsetPDS_of_nat {B : Set ℕ} {v : ℕ} [NeZero v] (hB : IsPerfectDifferenceSet B v) :
    ∃ S : Finset (ZMod v),
      (∀ b ∈ B, (b : ZMod v) ∈ S) ∧
      (∀ b₁ ∈ B, ∀ b₂ ∈ B, (b₁ : ZMod v) = (b₂ : ZMod v) → b₁ = b₂) ∧
      IsFinsetPDS S := by
  classical
  let S : Finset (ZMod v) := Finset.univ.filter (fun x : ZMod v => ∃ b ∈ B, (b : ZMod v) = x)
  have hinj : ∀ b₁ ∈ B, ∀ b₂ ∈ B, (b₁ : ZMod v) = (b₂ : ZMod v) → b₁ = b₂ := by
    intro b₁ hb₁ b₂ hb₂ heq
    by_contra hne
    have hmem_off : (b₁, b₂) ∈ B.offDiag := Set.mem_offDiag.2 ⟨hb₁, hb₂, hne⟩
    have h0 := hB.mapsTo hmem_off
    simp only [Set.mem_ofPred] at h0
    exact h0 (sub_eq_zero.2 heq)
  refine ⟨S, ?_, hinj, ⟨?_⟩⟩
  · intro b hb
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, b, hb, rfl⟩
  · intro d hd
    obtain ⟨⟨a, b⟩, hab, hdiff⟩ := hB.surjOn hd
    simp only [Set.mem_offDiag] at hab
    rcases hab with ⟨ha, hb, hab_ne⟩
    have haS : (a : ZMod v) ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, a, ha, rfl⟩
    have hbS : (b : ZMod v) ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, b, hb, rfl⟩
    have habZ : (a : ZMod v) ≠ (b : ZMod v) := fun h => hab_ne (hinj a ha b hb h)
    refine ⟨(a : ZMod v), haS, (b : ZMod v), hbS, habZ, hdiff, ?_⟩
    intro x hx y hy hxy hxyd
    obtain ⟨a', ha', rfl⟩ := (Finset.mem_filter.1 hx).2
    obtain ⟨b', hb', rfl⟩ := (Finset.mem_filter.1 hy).2
    have hab'_ne : a' ≠ b' := fun h => hxy (congrArg Nat.cast h)
    have hm1 : (a', b') ∈ B.offDiag := Set.mem_offDiag.2 ⟨ha', hb', hab'_ne⟩
    have hm2 : (a, b) ∈ B.offDiag := Set.mem_offDiag.2 ⟨ha, hb, hab_ne⟩
    have heq := hB.injOn hm1 hm2 (hxyd.trans hdiff.symm)
    exact ⟨congrArg Nat.cast (congrArg Prod.fst heq), congrArg Nat.cast (congrArg Prod.snd heq)⟩

lemma oma_finsetPDS_shift {v : ℕ} [NeZero v] {S : Finset (ZMod v)} (hS : IsFinsetPDS S)
    (c : ZMod v) :
    IsFinsetPDS (S.map ⟨fun x => x + c, add_left_injective c⟩) := by
  refine ⟨fun d hd => ?_⟩
  obtain ⟨a, ha, b, hb, hab, hdiff, huniq⟩ := hS.uniq_diff d hd
  refine ⟨a + c, Finset.mem_map.2 ⟨a, ha, rfl⟩, b + c, Finset.mem_map.2 ⟨b, hb, rfl⟩,
    fun h => hab (add_right_cancel h), by linear_combination hdiff, ?_⟩
  intro a' ha' b' hb' hab' hdiff'
  obtain ⟨a₀, ha₀, rfl⟩ := Finset.mem_map.1 ha'
  obtain ⟨b₀, hb₀, rfl⟩ := Finset.mem_map.1 hb'
  dsimp at hab' hdiff'
  have hne₀ : a₀ ≠ b₀ := fun h => hab' (congrArg (· + c) h)
  have hd₀ : a₀ - b₀ = d := by linear_combination hdiff'
  obtain ⟨rfl, rfl⟩ := huniq a₀ ha₀ b₀ hb₀ hne₀ hd₀
  exact ⟨rfl, rfl⟩

lemma oma_finsetPDS_card_eq {v : ℕ} [NeZero v] {S : Finset (ZMod v)} (hS : IsFinsetPDS S) :
    S.card * (S.card - 1) = v - 1 := by
  have hv_pos : 0 < v := NeZero.pos v
  have hbij : S.offDiag.card = (Finset.univ.erase (0 : ZMod v)).card := by
    refine Finset.card_bij (fun p _ => p.1 - p.2) ?_ ?_ ?_
    · intro p hp
      rcases Finset.mem_offDiag.1 hp with ⟨_, _, hne⟩
      exact Finset.mem_erase.2 ⟨sub_ne_zero.2 hne, Finset.mem_univ _⟩
    · intro p₁ hp₁ p₂ hp₂ heq
      rcases Finset.mem_offDiag.1 hp₁ with ⟨h1a, h1b, h1ne⟩
      rcases Finset.mem_offDiag.1 hp₂ with ⟨h2a, h2b, h2ne⟩
      obtain ⟨_, _, _, _, _, _, huniq⟩ := hS.uniq_diff (p₁.1 - p₁.2) (sub_ne_zero.2 h1ne)
      have e1 := huniq p₁.1 h1a p₁.2 h1b h1ne rfl
      have e2 := huniq p₂.1 h2a p₂.2 h2b h2ne heq.symm
      exact Prod.ext (e1.1.trans e2.1.symm) (e1.2.trans e2.2.symm)
    · intro d hd
      have hd0 : d ≠ 0 := (Finset.mem_erase.1 hd).1
      obtain ⟨a, ha, b, hb, hab, hdiff, _⟩ := hS.uniq_diff d hd0
      exact ⟨(a, b), Finset.mem_offDiag.2 ⟨ha, hb, hab⟩, hdiff⟩
  have hoff : S.card * (S.card - 1) = S.offDiag.card := by
    rw [Finset.offDiag_card]
    rcases S.card with _ | k <;> simp [Nat.succ_mul, Nat.mul_succ]
  have huniv : (Finset.univ.erase (0 : ZMod v)).card = v - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]
  omega

lemma oma_two_mul_cancel {v : ℕ} [NeZero v] (hv_odd : Odd v) {x y : ZMod v}
    (h : (2 : ZMod v) * x = (2 : ZMod v) * y) : x = y :=
  ((ZMod.isUnit_iff_coprime 2 v).2 hv_odd.coprime_two_left).mul_left_cancel h

def omaLine {v : ℕ} (S : Finset (ZMod v)) (y : ZMod v) : Finset (ZMod v) :=
  S.map ⟨fun s => s + y, add_left_injective y⟩

lemma mem_omaLine {v : ℕ} {S : Finset (ZMod v)} {y x : ZMod v} :
    x ∈ omaLine S y ↔ x - y ∈ S := by
  simp only [omaLine, Finset.mem_map, Function.Embedding.coeFn_mk]
  exact ⟨fun ⟨s, hs, hsy⟩ => by simpa [← hsy] using hs, fun h => ⟨x - y, h, sub_add_cancel x y⟩⟩

lemma card_omaLine {v : ℕ} (S : Finset (ZMod v)) (y : ZMod v) :
    (omaLine S y).card = S.card :=
  Finset.card_map _

section PolarityEngine

variable {v : ℕ} [NeZero v]

def omaAbs (S : Finset (ZMod v)) : Finset (ZMod v) :=
  Finset.univ.filter (fun x : ZMod v => (2 : ZMod v) * x ∈ S)

lemma mem_omaAbs {S : Finset (ZMod v)} {x : ZMod v} :
    x ∈ omaAbs S ↔ (2 : ZMod v) * x ∈ S := by
  simp [omaAbs]

lemma card_omaAbs {S : Finset (ZMod v)} (hv_odd : Odd v) :
    (omaAbs S).card = S.card := by
  rcases hv_odd with ⟨m, hm⟩
  subst hm
  refine Finset.card_bij (fun x _ => (2 : ZMod (2 * m + 1)) * x) ?_ ?_ ?_
  · intro x hx
    exact mem_omaAbs.1 hx
  · intro x₁ _ x₂ _ heq
    exact oma_two_mul_cancel ⟨m, rfl⟩ heq
  · intro s hs
    let inv2 : ZMod (2 * m + 1) := ((m + 1 : ℕ) : ZMod (2 * m + 1))
    have h2 : (2 : ZMod (2 * m + 1)) * (inv2 * s) = s := by
      have h0 : ((2 * m + 1 : ℕ) : ZMod (2 * m + 1)) = 0 := ZMod.natCast_self (2 * m + 1)
      have h1 : (2 : ZMod (2 * m + 1)) * inv2 = 1 := by
        dsimp [inv2]
        push_cast at h0 ⊢
        linear_combination h0
      calc (2 : ZMod (2 * m + 1)) * (inv2 * s)
        _ = ((2 : ZMod (2 * m + 1)) * inv2) * s := (mul_assoc _ _ _).symm
        _ = 1 * s := by rw [h1]
        _ = s := one_mul s
    exact ⟨inv2 * s, mem_omaAbs.2 (by rw [h2]; exact hs), h2⟩

lemma oma_unique_line_of_pts {S : Finset (ZMod v)} (hS : IsFinsetPDS S)
    {x₁ x₂ : ZMod v} (hx : x₁ ≠ x₂) :
    ∃ y : ZMod v, x₁ ∈ omaLine S y ∧ x₂ ∈ omaLine S y ∧
      ∀ y' : ZMod v, x₁ ∈ omaLine S y' → x₂ ∈ omaLine S y' → y' = y := by
  obtain ⟨a, ha, b, hb, _, hdiff, huniq⟩ := hS.uniq_diff (x₁ - x₂) (sub_ne_zero.2 hx)
  refine ⟨x₁ - a, ?_, ?_, ?_⟩
  · rw [mem_omaLine]; convert ha using 1; ring
  · rw [mem_omaLine]
    have h2 : x₂ - (x₁ - a) = b := by linear_combination hdiff
    rw [h2]; exact hb
  · intro y' h1 h2
    rw [mem_omaLine] at h1 h2
    have hne' : x₁ - y' ≠ x₂ - y' := fun h => hx (by linear_combination h)
    have hd' : (x₁ - y') - (x₂ - y') = x₁ - x₂ := by ring
    obtain ⟨heq1, _⟩ := huniq (x₁ - y') h1 (x₂ - y') h2 hne' hd'
    linear_combination -heq1

lemma oma_abs_line_inter {S : Finset (ZMod v)} (hS : IsFinsetPDS S) {y : ZMod v}
    (hy : -(2 : ZMod v) * y ∈ S) :
    omaLine S y ∩ omaAbs S = {-y} := by
  ext p
  simp only [Finset.mem_inter, mem_omaLine, mem_omaAbs, Finset.mem_singleton]
  refine ⟨fun ⟨hpy, h2p⟩ => ?_, fun hp_eq => ?_⟩
  · by_contra hp_ne
    have hsum_ne : p + y ≠ 0 := fun h => hp_ne (by linear_combination h)
    obtain ⟨_, _, _, _, _, _, huniq⟩ := hS.uniq_diff (p + y) hsum_ne
    have hne1 : p - y ≠ -(2 : ZMod v) * y := fun h => hsum_ne (by linear_combination h)
    have hne2 : (2 : ZMod v) * p ≠ p - y := fun h => hsum_ne (by linear_combination h)
    have e1 := huniq (p - y) hpy (-(2 : ZMod v) * y) hy hne1 (by ring)
    have e2 := huniq ((2 : ZMod v) * p) h2p (p - y) hpy hne2 (by ring)
    have eq_a : p - y = (2 : ZMod v) * p := e1.1.trans e2.1.symm
    exact hp_ne (by linear_combination -eq_a)
  · subst hp_eq
    exact ⟨by convert hy using 1; ring, by convert hy using 1; ring⟩

lemma oma_non_abs_line_even {S : Finset (ZMod v)} (hS : IsFinsetPDS S) {y : ZMod v}
    (hy : -(2 : ZMod v) * y ∉ S) :
    Even (omaLine S y \ omaAbs S).card := by
  classical
  set T := omaLine S y \ omaAbs S
  have hpartner : ∀ p : ZMod v, p + y ≠ 0 →
      ∃ p' : ZMod v, p' ∈ omaLine S y ∧ p' + p ∈ S ∧
        ∀ q : ZMod v, q ∈ omaLine S y → q + p ∈ S → q = p' := by
    intro p hpy_ne
    obtain ⟨a, ha, b, hb, _, hdiff, huniq⟩ := hS.uniq_diff (p + y) hpy_ne
    refine ⟨b + y, ?_, ?_, ?_⟩
    · rw [mem_omaLine]; convert hb using 1; ring
    · have hbp : b + y + p = a := by linear_combination -hdiff
      rw [hbp]; exact ha
    · intro q hq1 hq2
      rw [mem_omaLine] at hq1
      have hne' : q + p ≠ q - y := fun h => hpy_ne (by linear_combination h)
      have hd' : (q + p) - (q - y) = p + y := by ring
      obtain ⟨_, heqb⟩ := huniq (q + p) hq2 (q - y) hq1 hne' hd'
      linear_combination heqb
  let f : ZMod v → ZMod v := fun p =>
    if h : p + y ≠ 0 then Classical.choose (hpartner p h) else p
  have hf_spec : ∀ p : ZMod v, (h : p + y ≠ 0) →
      f p ∈ omaLine S y ∧ f p + p ∈ S ∧
        ∀ q : ZMod v, q ∈ omaLine S y → q + p ∈ S → q = f p := by
    intro p h
    simp only [f, dif_pos h]
    exact Classical.choose_spec (hpartner p h)
  have hp_sum_ne : ∀ p ∈ omaLine S y, p + y ≠ 0 := by
    intro p hp h0
    rw [mem_omaLine] at hp
    have hp_eq : p = -y := by linear_combination h0
    rw [hp_eq] at hp
    exact hy (by convert hp using 1; ring)
  refine oma_even_card_of_fpf_involution T.card T f rfl ?_ ?_ ?_
  · intro p hp
    rcases Finset.mem_sdiff.1 hp with ⟨hpL, hpA⟩
    have hne := hp_sum_ne p hpL
    obtain ⟨hfpL, hfppS, _⟩ := hf_spec p hne
    refine Finset.mem_sdiff.2 ⟨hfpL, fun hfpA => ?_⟩
    rw [mem_omaAbs] at hfpA
    by_cases hfp_eq : f p = p
    · rw [hfp_eq] at hfpA
      exact hpA (mem_omaAbs.2 hfpA)
    · have hne_diff : f p - p ≠ 0 := sub_ne_zero.2 hfp_eq
      obtain ⟨_, _, _, _, _, _, huniq⟩ := hS.uniq_diff (f p - p) hne_diff
      have h1 : (2 : ZMod v) * f p ≠ f p + p := fun h => hne_diff (by linear_combination h)
      have h2 : f p - y ≠ p - y := fun h => hne_diff (by linear_combination h)
      have e1 := huniq ((2 : ZMod v) * f p) hfpA (f p + p) hfppS h1 (by ring)
      have e2 := huniq (f p - y) (mem_omaLine.1 hfpL) (p - y) (mem_omaLine.1 hpL) h2 (by ring)
      have heq_s : (2 : ZMod v) * f p = f p - y := e1.1.trans e2.1.symm
      exact hp_sum_ne (f p) hfpL (by linear_combination heq_s)
  · intro p hp
    rcases Finset.mem_sdiff.1 hp with ⟨hpL, _⟩
    have hne := hp_sum_ne p hpL
    obtain ⟨hfpL, hfppS, _⟩ := hf_spec p hne
    have hne' := hp_sum_ne (f p) hfpL
    obtain ⟨_, _, huniq'⟩ := hf_spec (f p) hne'
    exact (huniq' p hpL (by convert hfppS using 1; ring)).symm
  · intro p hp heq
    rcases Finset.mem_sdiff.1 hp with ⟨hpL, hpA⟩
    obtain ⟨_, hfppS, _⟩ := hf_spec p (hp_sum_ne p hpL)
    rw [heq] at hfppS
    exact hpA (mem_omaAbs.2 (by convert hfppS using 1; ring))

lemma oma_odd_q_at_most_two {S : Finset (ZMod v)} (hS : IsFinsetPDS S)
    {q : ℕ} (hq_card : S.card = q + 1) (hv_odd : Odd v) (hq_odd : Odd q) :
    ∀ y : ZMod v, (omaLine S y ∩ omaAbs S).card ≤ 2 := by
  classical
  have hline_even_or_one : ∀ y : ZMod v,
      (-(2 : ZMod v) * y ∈ S ∧ omaLine S y ∩ omaAbs S = {-y}) ∨
      (-(2 : ZMod v) * y ∉ S ∧ Even (omaLine S y ∩ omaAbs S).card) := by
    intro y
    by_cases hy : -(2 : ZMod v) * y ∈ S
    · exact Or.inl ⟨hy, oma_abs_line_inter hS hy⟩
    · refine Or.inr ⟨hy, ?_⟩
      have hev_sdiff := oma_non_abs_line_even hS hy
      have htot : (omaLine S y ∩ omaAbs S).card + (omaLine S y \ omaAbs S).card = q + 1 := by
        rw [Finset.card_inter_add_card_sdiff, card_omaLine, hq_card]
      rcases hq_odd with ⟨k, rfl⟩
      rcases hev_sdiff with ⟨m, hm⟩
      exact ⟨k + 1 - m, by omega⟩
  intro y₀
  by_cases hempty : (omaLine S y₀ ∩ omaAbs S).card = 0
  · omega
  obtain ⟨p, hp₀⟩ := Finset.card_pos.1 (Nat.pos_of_ne_zero hempty)
  rcases Finset.mem_inter.1 hp₀ with ⟨hpL₀, hpA⟩
  by_cases hy₀_neg : y₀ = -p
  · subst hy₀_neg
    have hy_in : -(2 : ZMod v) * (-p) ∈ S := by
      convert mem_omaAbs.1 hpA using 1; ring
    rw [oma_abs_line_inter hS hy_in]
    simp
  · let Yp : Finset (ZMod v) := Finset.univ.filter (fun y : ZMod v => p ∈ omaLine S y ∧ y ≠ -p)
    have hmem_Yp : ∀ y : ZMod v, y ∈ Yp ↔ p ∈ omaLine S y ∧ y ≠ -p := by
      intro y; simp [Yp]
    have hcard_Yp : Yp.card = q := by
      have hbij : Yp.card = (S.erase ((2 : ZMod v) * p)).card := by
        refine Finset.card_bij (fun y _ => p - y) ?_ ?_ ?_
        · intro y hy
          obtain ⟨hpLy, hy_ne⟩ := (hmem_Yp y).1 hy
          refine Finset.mem_erase.2 ⟨?_, mem_omaLine.1 hpLy⟩
          intro heq
          exact hy_ne (by linear_combination -heq)
        · intro y₁ _ y₂ _ heq
          linear_combination -heq
        · intro s hs
          rcases Finset.mem_erase.1 hs with ⟨hs_ne, hsS⟩
          refine ⟨p - s, (hmem_Yp (p - s)).2 ⟨?_, ?_⟩, by ring⟩
          · rw [mem_omaLine]; convert hsS using 1; ring
          · intro heq; exact hs_ne (by linear_combination -heq)
      rw [hbij, Finset.card_erase_of_mem (mem_omaAbs.1 hpA), hq_card]
      omega
    have hge1 : ∀ y ∈ Yp, 1 ≤ ((omaLine S y ∩ omaAbs S).erase p).card := by
      intro y hy
      obtain ⟨hpLy, hy_ne⟩ := (hmem_Yp y).1 hy
      have hp_in : p ∈ omaLine S y ∩ omaAbs S := Finset.mem_inter.2 ⟨hpLy, hpA⟩
      rcases hline_even_or_one y with ⟨_, heq_sing⟩ | ⟨_, hev_int⟩
      · rw [heq_sing] at hp_in
        exact (hy_ne (by linear_combination (Finset.mem_singleton.1 hp_in))).elim
      · rcases hev_int with ⟨m, hm⟩
        have hpos_m : 2 ≤ (omaLine S y ∩ omaAbs S).card := by
          have h1 : 1 ≤ (omaLine S y ∩ omaAbs S).card := Finset.card_pos.2 ⟨p, hp_in⟩
          omega
        have her := Finset.card_erase_of_mem hp_in
        omega
    have hbiU : Yp.biUnion (fun y => (omaLine S y ∩ omaAbs S).erase p) = (omaAbs S).erase p := by
      ext a
      simp only [Finset.mem_biUnion, Finset.mem_erase, ne_eq, Finset.mem_inter]
      refine ⟨fun ⟨y, _, ha_ne, _, haA⟩ => ⟨ha_ne, haA⟩, fun ⟨ha_ne, haA⟩ => ?_⟩
      obtain ⟨y, hpLy, haLy, _⟩ := oma_unique_line_of_pts hS (Ne.symm ha_ne)
      have hy_ne : y ≠ -p := by
        intro hy_eq
        subst hy_eq
        have hy_in : -(2 : ZMod v) * (-p) ∈ S := by convert mem_omaAbs.1 hpA using 1; ring
        have ha_in : a ∈ omaLine S (-p) ∩ omaAbs S := Finset.mem_inter.2 ⟨haLy, haA⟩
        rw [oma_abs_line_inter hS hy_in] at ha_in
        exact ha_ne (by simpa using Finset.mem_singleton.1 ha_in)
      exact ⟨y, (hmem_Yp y).2 ⟨hpLy, hy_ne⟩, ha_ne, haLy, haA⟩
    have hdisj : (Yp : Set (ZMod v)).PairwiseDisjoint (fun y => (omaLine S y ∩ omaAbs S).erase p) := by
      intro y₁ hy₁ y₂ hy₂ hy_ne
      dsimp [Function.onFun]
      rw [Finset.disjoint_left]
      intro a ha₁ ha₂
      have ha_ne : a ≠ p := (Finset.mem_erase.1 ha₁).1
      have hp₁ := ((hmem_Yp y₁).1 hy₁).1
      have hp₂ := ((hmem_Yp y₂).1 hy₂).1
      have haL₁ := (Finset.mem_inter.1 (Finset.mem_erase.1 ha₁).2).1
      have haL₂ := (Finset.mem_inter.1 (Finset.mem_erase.1 ha₂).2).1
      obtain ⟨y, _, _, huniq⟩ := oma_unique_line_of_pts hS (Ne.symm ha_ne)
      exact hy_ne ((huniq y₁ hp₁ haL₁).trans (huniq y₂ hp₂ haL₂).symm)
    have hsum : ∑ y ∈ Yp, ((omaLine S y ∩ omaAbs S).erase p).card = ∑ _y ∈ Yp, 1 := by
      rw [← Finset.card_biUnion hdisj, hbiU, Finset.card_erase_of_mem hpA, card_omaAbs hv_odd,
        hq_card, Finset.sum_const, smul_eq_mul, mul_one, hcard_Yp]
      omega
    have hall1 := (Finset.sum_eq_sum_iff_of_le hge1).1 hsum.symm
    have hy₀_mem : y₀ ∈ Yp := (hmem_Yp y₀).2 ⟨hpL₀, hy₀_neg⟩
    have h1 := (hall1 y₀ hy₀_mem).symm
    have her := Finset.card_erase_of_mem hp₀
    omega

lemma oma_even_q_collinear {S : Finset (ZMod v)} (hS : IsFinsetPDS S)
    {q : ℕ} (hq_card : S.card = q + 1) (hq_ge : 2 ≤ q) (hv_odd : Odd v) (hq_even : Even q) :
    ∃ y : ZMod v, omaAbs S = omaLine S y := by
  classical
  have hline_pos : ∀ y : ZMod v, 1 ≤ (omaLine S y ∩ omaAbs S).card := by
    intro y
    by_cases hy : -(2 : ZMod v) * y ∈ S
    · rw [oma_abs_line_inter hS hy]; simp
    · have hev_sdiff := oma_non_abs_line_even hS hy
      have htot : (omaLine S y ∩ omaAbs S).card + (omaLine S y \ omaAbs S).card = q + 1 := by
        rw [Finset.card_inter_add_card_sdiff, card_omaLine, hq_card]
      rcases hq_even with ⟨k, rfl⟩
      rcases hev_sdiff with ⟨m, hm⟩
      omega
  have hnonabs_one : ∀ p : ZMod v, p ∉ omaAbs S →
      ∀ y : ZMod v, p ∈ omaLine S y → (omaLine S y ∩ omaAbs S).card = 1 := by
    intro p hpA y₀ hpL₀
    let Yp : Finset (ZMod v) := Finset.univ.filter (fun y : ZMod v => p ∈ omaLine S y)
    have hmem_Yp : ∀ y : ZMod v, y ∈ Yp ↔ p ∈ omaLine S y := by
      intro y; simp [Yp]
    have hcard_Yp : Yp.card = q + 1 := by
      have hbij : Yp.card = S.card := by
        refine Finset.card_bij (fun y _ => p - y) ?_ ?_ ?_
        · intro y hy; exact mem_omaLine.1 ((hmem_Yp y).1 hy)
        · intro y₁ _ y₂ _ heq; linear_combination -heq
        · intro s hs
          refine ⟨p - s, (hmem_Yp (p - s)).2 ?_, by ring⟩
          rw [mem_omaLine]; convert hs using 1; ring
      rw [hbij, hq_card]
    have hbiU : Yp.biUnion (fun y => omaLine S y ∩ omaAbs S) = omaAbs S := by
      ext a
      simp only [Finset.mem_biUnion, Finset.mem_inter]
      refine ⟨fun ⟨_, _, _, haA⟩ => haA, fun haA => ?_⟩
      have ha_ne : p ≠ a := fun h => hpA (h ▸ haA)
      obtain ⟨y, hpLy, haLy, _⟩ := oma_unique_line_of_pts hS ha_ne
      exact ⟨y, (hmem_Yp y).2 hpLy, haLy, haA⟩
    have hdisj : (Yp : Set (ZMod v)).PairwiseDisjoint (fun y => omaLine S y ∩ omaAbs S) := by
      intro y₁ hy₁ y₂ hy₂ hy_ne
      dsimp [Function.onFun]
      rw [Finset.disjoint_left]
      intro a ha₁ ha₂
      rcases Finset.mem_inter.1 ha₁ with ⟨haL₁, haA⟩
      rcases Finset.mem_inter.1 ha₂ with ⟨haL₂, _⟩
      have ha_ne : p ≠ a := fun h => hpA (h ▸ haA)
      obtain ⟨y, _, _, huniq⟩ := oma_unique_line_of_pts hS ha_ne
      exact hy_ne ((huniq y₁ ((hmem_Yp y₁).1 hy₁) haL₁).trans
        (huniq y₂ ((hmem_Yp y₂).1 hy₂) haL₂).symm)
    have hsum : ∑ y ∈ Yp, (omaLine S y ∩ omaAbs S).card = ∑ _y ∈ Yp, 1 := by
      rw [← Finset.card_biUnion hdisj, hbiU, card_omaAbs hv_odd, hq_card, Finset.sum_const,
        smul_eq_mul, mul_one, hcard_Yp]
    have hall1 := (Finset.sum_eq_sum_iff_of_le (fun y _ => hline_pos y)).1 hsum.symm
    exact (hall1 y₀ ((hmem_Yp y₀).2 hpL₀)).symm
  have hAbs_gt : 1 < (omaAbs S).card := by
    rw [card_omaAbs hv_odd, hq_card]; omega
  obtain ⟨a₁, ha₁, a₂, ha₂, ha_ne⟩ := Finset.one_lt_card.1 hAbs_gt
  obtain ⟨y, ha₁L, ha₂L, _⟩ := oma_unique_line_of_pts hS ha_ne
  refine ⟨y, (Finset.eq_of_subset_of_card_le (fun p hpL => ?_) ?_).symm⟩
  · by_contra hpA
    have h1 := hnonabs_one p hpA y hpL
    have h2 : 2 ≤ (omaLine S y ∩ omaAbs S).card := by
      refine Finset.one_lt_card.2 ⟨a₁, Finset.mem_inter.2 ⟨ha₁L, ha₁⟩,
        a₂, Finset.mem_inter.2 ⟨ha₂L, ha₂⟩, ha_ne⟩
    omega
  · rw [card_omaAbs hv_odd, card_omaLine]

end PolarityEngine

lemma oma_natCast_ne_zero {v k : ℕ} (hk0 : 0 < k) (hkv : k < v) : (k : ZMod v) ≠ 0 := by
  intro h0
  have hdvd : v ∣ k := (ZMod.natCast_eq_zero_iff k v).1 h0
  exact absurd (Nat.le_of_dvd hk0 hdvd) (by omega)

end OMA707

theorem OMA.solution : type_of% @Erdos707.erdos_707.variants.counterexample_hall := by
  intro A hA
  subst hA
  refine ⟨(by simp : ({1, 3, 9, 10, 13} : Set ℕ).Finite).to_subtype, ?_, ?_⟩
  · have hdec : ∀ i₁ ∈ ({1, 3, 9, 10, 13} : Finset ℕ),
        ∀ j₁ ∈ ({1, 3, 9, 10, 13} : Finset ℕ),
        ∀ i₂ ∈ ({1, 3, 9, 10, 13} : Finset ℕ),
        ∀ j₂ ∈ ({1, 3, 9, 10, 13} : Finset ℕ),
        i₁ + i₂ = j₁ + j₂ → (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁) := by decide
    intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ hsum
    exact hdec i₁ (by simpa using hi₁) j₁ (by simpa using hj₁)
      i₂ (by simpa using hi₂) j₂ (by simpa using hj₂) hsum
  · intro B v hv hAB hPDS
    have : NeZero v := ⟨by omega⟩
    obtain ⟨S₀, hmem₀, hinj₀, hS₀⟩ := oma_finsetPDS_of_nat hPDS
    let A_fin : Finset ℕ := {1, 3, 9, 10, 13}
    have hA_sub : ∀ x ∈ A_fin, x ∈ B := by
      intro x hx
      apply hAB
      simpa [A_fin] using hx
    have hcard5 : 5 ≤ S₀.card := by
      have himg_sub : A_fin.image (Nat.cast : ℕ → ZMod v) ⊆ S₀ := by
        intro z hz
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hz
        exact hmem₀ x (hA_sub x hx)
      have hinj_A : Set.InjOn (Nat.cast : ℕ → ZMod v) (A_fin : Set ℕ) :=
        fun x₁ hx₁ x₂ hx₂ heq => hinj₀ x₁ (hA_sub x₁ hx₁) x₂ (hA_sub x₂ hx₂) heq
      have hcard_img : (A_fin.image (Nat.cast : ℕ → ZMod v)).card = 5 := by
        rw [Finset.card_image_of_injOn hinj_A]
        decide
      exact hcard_img ▸ Finset.card_le_card himg_sub
    let S : Finset (ZMod v) := S₀.map ⟨fun x => x + (-(9 : ZMod v)), add_left_injective _⟩
    have hS : IsFinsetPDS S := oma_finsetPDS_shift hS₀ (-(9 : ZMod v))
    have hS_card : S.card = S₀.card := Finset.card_map _
    set q := S.card - 1
    have hq_card : S.card = q + 1 := by omega
    have hq_ge : 4 ≤ q := by omega
    have hv_eq_sub : (q + 1) * q = v - 1 := by
      simpa [hq_card] using oma_finsetPDS_card_eq hS
    have hv_eq1 : (q + 1) * q + 1 = v := by omega
    have hv_eq : v = q ^ 2 + q + 1 := by nlinarith
    have hv_ge : 21 ≤ v := by nlinarith
    have hv_odd : Odd v := by
      rcases Nat.even_mul_succ_self q with ⟨m, hm⟩
      exact ⟨m, by nlinarith⟩
    have h_in_S : ∀ n ∈ ({1, 3, 9, 10, 13} : Set ℕ), ((n : ZMod v) - 9) ∈ S := by
      intro n hn
      simp only [S, Finset.mem_map, Function.Embedding.coeFn_mk]
      exact ⟨(n : ZMod v), hmem₀ n (hAB hn), by ring⟩
    have hm8 : -(8 : ZMod v) ∈ S := by
      convert h_in_S 1 (by simp) using 1; norm_num
    have hm6 : -(6 : ZMod v) ∈ S := by
      convert h_in_S 3 (by simp) using 1; norm_num
    have h0S : (0 : ZMod v) ∈ S := by
      convert h_in_S 9 (by simp) using 1; norm_num
    have h1S : (1 : ZMod v) ∈ S := by
      convert h_in_S 10 (by simp) using 1; norm_num
    have h4S : (4 : ZMod v) ∈ S := by
      convert h_in_S 13 (by simp) using 1; norm_num
    have ha_m4 : -(4 : ZMod v) ∈ omaAbs S := mem_omaAbs.2 (by convert hm8 using 1; ring)
    have ha_m3 : -(3 : ZMod v) ∈ omaAbs S := mem_omaAbs.2 (by convert hm6 using 1; ring)
    have ha_0 : (0 : ZMod v) ∈ omaAbs S := mem_omaAbs.2 (by convert h0S using 1; ring)
    have ha_2 : (2 : ZMod v) ∈ omaAbs S := mem_omaAbs.2 (by convert h4S using 1; ring)
    have hl_m4 : -(4 : ZMod v) ∈ omaLine S (-(4 : ZMod v)) :=
      mem_omaLine.2 (by convert h0S using 1; ring)
    have hl_m3 : -(3 : ZMod v) ∈ omaLine S (-(4 : ZMod v)) :=
      mem_omaLine.2 (by convert h1S using 1; ring)
    have hl_0 : (0 : ZMod v) ∈ omaLine S (-(4 : ZMod v)) :=
      mem_omaLine.2 (by convert h4S using 1; ring)
    have hne_1 : (1 : ZMod v) ≠ 0 := by
      simpa using oma_natCast_ne_zero (v := v) (k := 1) (by omega) (by omega)
    have hne_3 : (3 : ZMod v) ≠ 0 := by
      simpa using oma_natCast_ne_zero (v := v) (k := 3) (by omega) (by omega)
    have hne_4 : (4 : ZMod v) ≠ 0 := by
      simpa using oma_natCast_ne_zero (v := v) (k := 4) (by omega) (by omega)
    have hne_6 : (6 : ZMod v) ≠ 0 := by
      simpa using oma_natCast_ne_zero (v := v) (k := 6) (by omega) (by omega)
    have h_m4_ne_m3 : -(4 : ZMod v) ≠ -(3 : ZMod v) := fun h => hne_1 (by linear_combination -h)
    have h_m4_ne_0 : -(4 : ZMod v) ≠ (0 : ZMod v) := fun h => hne_4 (by linear_combination -h)
    have h_m3_ne_0 : -(3 : ZMod v) ≠ (0 : ZMod v) := fun h => hne_3 (by linear_combination -h)
    have hcard_inter3 : 3 ≤ (omaLine S (-(4 : ZMod v)) ∩ omaAbs S).card := by
      classical
      let T3 : Finset (ZMod v) := {-(4 : ZMod v), -(3 : ZMod v), (0 : ZMod v)}
      have hsub : T3 ⊆ omaLine S (-(4 : ZMod v)) ∩ omaAbs S := by
        intro x hx
        simp only [T3, Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · exact Finset.mem_inter.2 ⟨hl_m4, ha_m4⟩
        · exact Finset.mem_inter.2 ⟨hl_m3, ha_m3⟩
        · exact Finset.mem_inter.2 ⟨hl_0, ha_0⟩
      have hT3_card : T3.card = 3 := by
        dsimp [T3]
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
        · simp [h_m3_ne_0]
        · simp [h_m4_ne_m3, h_m4_ne_0]
      have hle_sub := Finset.card_le_card hsub
      omega
    rcases Nat.even_or_odd q with hq_even | hq_odd
    · obtain ⟨y, hy_eq⟩ := oma_even_q_collinear hS hq_card (by omega) hv_odd hq_even
      obtain ⟨_, _, _, huniqL⟩ := oma_unique_line_of_pts hS h_m4_ne_m3
      have hy_m4 : y = -(4 : ZMod v) := by
        have hm4_y : -(4 : ZMod v) ∈ omaLine S y := hy_eq ▸ ha_m4
        have hm3_y : -(3 : ZMod v) ∈ omaLine S y := hy_eq ▸ ha_m3
        exact (huniqL y hm4_y hm3_y).trans (huniqL (-(4 : ZMod v)) hl_m4 hl_m3).symm
      have h2_line : (2 : ZMod v) ∈ omaLine S (-(4 : ZMod v)) := by
        rw [← hy_m4, ← hy_eq]; exact ha_2
      have h6S : (6 : ZMod v) ∈ S := by
        have h := mem_omaLine.1 h2_line
        convert h using 1; ring
      obtain ⟨_, _, _, _, _, _, huniq6⟩ := hS.uniq_diff (6 : ZMod v) hne_6
      have hm6_ne : (0 : ZMod v) ≠ -(6 : ZMod v) := fun h => hne_6 (by linear_combination h)
      have e1 := huniq6 (6 : ZMod v) h6S 0 h0S hne_6 (by ring)
      have e2 := huniq6 0 h0S (-(6 : ZMod v)) hm6 hm6_ne (by ring)
      exact hne_6 (e1.1.trans e2.1.symm)
    · have hle2 := oma_odd_q_at_most_two hS hq_card hv_odd hq_odd (-(4 : ZMod v))
      omega
