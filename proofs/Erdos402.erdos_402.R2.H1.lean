import OMAReductions.R_Erdos402_erdos_402_R2
import Mathlib

/-!
Finite Graham bound through 7000. Elementary and configuration lemmas
adapted from Boris Alexeev's Lean development (formal authors Codex,
GPT-5.6 Sol), source blob f64dbcb0cb7d999a5205bdc380a23191b11d241b.
https://github.com/plby/lean-proofs/blob/main/src/latest/ErdosProblems/Erdos402.lean
The finite verification here uses kernel-checked interval certificates,
a verified square-root primality test, and no native evaluator.
-/
namespace OMA.GrahamFinite
open scoped Pointwise
open Filter Asymptotics
private def quickPrime (n : ℕ) : Bool :=
  decide (2 ≤ n) && (List.range (n.sqrt+1)).all (fun d => decide (d < 2 ∨ ¬d ∣ n))

private lemma quickPrime_spec (n : ℕ) : quickPrime n = true ↔ n.Prime := by
  rw [Nat.prime_def_le_sqrt]
  simp only [quickPrime, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range]
  constructor
  · rintro ⟨hn,h⟩
    refine ⟨hn,fun d hd hd' => ?_⟩
    exact (h d (by omega)).resolve_left (by omega)
  · rintro ⟨hn,h⟩
    refine ⟨hn,fun d hd => ?_⟩
    by_cases h2 : d < 2
    · exact Or.inl h2
    · exact Or.inr (h d (by omega) (by omega))

private instance (priority := 2000) quickPrimeDecidable (n : ℕ) : Decidable n.Prime :=
  if h : quickPrime n = true then isTrue ((quickPrime_spec n).mp h)
  else isFalse (fun hp => h ((quickPrime_spec n).mpr hp))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
def GrahamBound (A : Finset ℕ) : Prop :=
  ∃ a ∈ A, ∃ b ∈ A, A.card * a.gcd b ≤ a

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private def hasGrahamBound (A : Finset ℕ) : Bool :=
  decide (∃ a ∈ A, ∃ b ∈ A, A.card * a.gcd b ≤ a)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma hasGrahamBound_eq_true (A : Finset ℕ) :
    hasGrahamBound A = true ↔ GrahamBound A := by
  simp [hasGrahamBound, GrahamBound]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private def badSubsets (D : Finset ℕ) (n : ℕ) : Finset (Finset ℕ) :=
  (D.powersetCard n).filter fun A ↦ hasGrahamBound A = false

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma grahamBound_of_badSubsets_eq_empty {D A : Finset ℕ} {n : ℕ}
    (hcert : badSubsets D n = ∅) (hsub : A ⊆ D) (hcard : A.card = n) :
    GrahamBound A := by
  by_contra hbad
  have hbool : hasGrahamBound A = false := by
    apply Bool.eq_false_iff.mpr
    intro htrue
    exact hbad ((hasGrahamBound_eq_true A).mp htrue)
  have hmem : A ∈ badSubsets D n := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩, hbool⟩
  rw [hcert] at hmem
  exact Finset.notMem_empty A hmem

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma residue_inj_of_div_gcd_lt {p a b : ℕ} (hp : p.Prime)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hpa : ¬p ∣ a)
    (ha : a / a.gcd b < p) (hb : b / a.gcd b < p)
    (hc : (a : ZMod p) = (b : ZMod p)) : a = b := by
  letI : Fact p.Prime := ⟨hp⟩
  let g := a.gcd b
  let x := a / g
  let y := b / g
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left b (Nat.pos_of_ne_zero ha0)
  have hxlt : x < p := ha
  have hylt : y < p := hb
  have hga : g * x = a := Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)
  have hgb : g * y = b := Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)
  have hpg : ¬p ∣ g := fun h ↦ hpa (h.trans (Nat.gcd_dvd_left a b))
  have hcg0 : (g : ZMod p) ≠ 0 := by
    intro hz
    exact hpg ((ZMod.natCast_eq_zero_iff g p).mp hz)
  have hc' : (g : ZMod p) * x = (g : ZMod p) * y := by
    calc
      (g : ZMod p) * x = ((g * x : ℕ) : ZMod p) := (Nat.cast_mul g x).symm
      _ = (a : ZMod p) := congrArg (fun n : ℕ ↦ (n : ZMod p)) hga
      _ = (b : ZMod p) := hc
      _ = ((g * y : ℕ) : ZMod p) := congrArg (fun n : ℕ ↦ (n : ZMod p)) hgb.symm
      _ = (g : ZMod p) * y := Nat.cast_mul g y
  have hxyZ : (x : ZMod p) = y := mul_left_cancel₀ hcg0 hc'
  have hxy : x = y := by
    have hv := congrArg ZMod.val hxyZ
    simpa [ZMod.val_natCast, Nat.mod_eq_of_lt hxlt, Nat.mod_eq_of_lt hylt] using hv
  rw [← hga, ← hgb, hxy]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private def foldedResidue (p a : ℕ) : ℕ :=
  min (a % p) (p - a % p)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma foldedResidue_pos {p a : ℕ} (hp : 0 < p) (hpa : ¬p ∣ a) :
    0 < foldedResidue p a := by
  have hrlt : a % p < p := Nat.mod_lt a hp
  have hr0 : a % p ≠ 0 := by
    intro h
    exact hpa (Nat.dvd_of_mod_eq_zero h)
  unfold foldedResidue
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma foldedResidue_le_div_two {p a : ℕ} (hp : 0 < p) :
    foldedResidue p a ≤ p / 2 := by
  have hrlt : a % p < p := Nat.mod_lt a hp
  unfold foldedResidue
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma foldedResidue_eq_iff {p a b : ℕ} (hp : 0 < p)
    (hpa : ¬p ∣ a) (hpb : ¬p ∣ b)
    (h : foldedResidue p a = foldedResidue p b) :
    a % p = b % p ∨ a % p + b % p = p := by
  have halt : a % p < p := Nat.mod_lt a hp
  have hblt : b % p < p := Nat.mod_lt b hp
  have ha0 : a % p ≠ 0 := fun hz ↦ hpa (Nat.dvd_of_mod_eq_zero hz)
  have hb0 : b % p ≠ 0 := fun hz ↦ hpb (Nat.dvd_of_mod_eq_zero hz)
  unfold foldedResidue at h
  simp only [min_def] at h
  split at h <;> split at h <;> omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private noncomputable def foldedMin (A : Finset ℕ) (p a : ℕ) : ℕ := by
  classical
  exact if ha : a ∈ A then
    (A.filter fun b ↦ foldedResidue p b = foldedResidue p a).min'
      ⟨a, Finset.mem_filter.mpr ⟨ha, rfl⟩⟩
  else 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma foldedMin_mem {A : Finset ℕ} {p a : ℕ} (ha : a ∈ A) :
    foldedMin A p a ∈ A := by
  classical
  unfold foldedMin
  rw [dif_pos ha]
  exact (Finset.mem_filter.mp (Finset.min'_mem _ _)).1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma foldedMin_color {A : Finset ℕ} {p a : ℕ} (ha : a ∈ A) :
    foldedResidue p (foldedMin A p a) = foldedResidue p a := by
  classical
  unfold foldedMin
  rw [dif_pos ha]
  let S := A.filter fun b ↦ foldedResidue p b = foldedResidue p a
  have hS : S.Nonempty := ⟨a, Finset.mem_filter.mpr ⟨ha, rfl⟩⟩
  exact (Finset.mem_filter.mp (S.min'_mem hS)).2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma foldedMin_le {A : Finset ℕ} {p a b : ℕ} (ha : a ∈ A) (hb : b ∈ A)
    (hcolor : foldedResidue p b = foldedResidue p a) : foldedMin A p a ≤ b := by
  classical
  unfold foldedMin
  rw [dif_pos ha]
  apply Finset.min'_le
  exact Finset.mem_filter.mpr ⟨hb, hcolor⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma foldedMin_eq_of_color {A : Finset ℕ} {p a b : ℕ}
    (ha : a ∈ A) (hb : b ∈ A)
    (hcolor : foldedResidue p a = foldedResidue p b) :
    foldedMin A p a = foldedMin A p b := by
  apply Nat.le_antisymm
  · apply foldedMin_le ha (foldedMin_mem hb)
    exact (foldedMin_color hb).trans hcolor.symm
  · apply foldedMin_le hb (foldedMin_mem ha)
    exact (foldedMin_color ha).trans hcolor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private def representedMultipliers (A : Finset ℕ) (α β : ℕ) : Finset ℕ :=
  (A.image fun a ↦ a / α).filter fun d ↦ 0 < d ∧ α * d ∈ A ∧ β * d ∈ A

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma mem_representedMultipliers {A : Finset ℕ} {α β d : ℕ} (hα : 0 < α) :
    d ∈ representedMultipliers A α β ↔ 0 < d ∧ α * d ∈ A ∧ β * d ∈ A := by
  classical
  constructor
  · exact fun h ↦ (Finset.mem_filter.mp h).2
  · intro h
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨α * d, h.2.1, ?_⟩, h⟩
    exact Nat.mul_div_cancel_left d hα

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma representedMultipliers_nonzero {A : Finset ℕ} {α β : ℕ} (hα : 0 < α) :
    0 ∉ representedMultipliers A α β := by
  rw [mem_representedMultipliers hα]
  simp

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private def representationCount (A : Finset ℕ) (p α : ℕ) : ℕ :=
  (representedMultipliers A α (p - α)).card

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private def representationPairs (A : Finset ℕ) (p : ℕ) :
    Finset ((α : ℕ) × ℕ) :=
  (Finset.Icc ((p + 1) / 2) A.card).sigma fun α ↦
    representedMultipliers A α (p - α)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma zero_card_le_excess {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (f : ι → ℕ) (h : S.card ≤ S.sum f) :
    (S.filter fun x ↦ f x = 0).card ≤
      (S.filter fun x ↦ 2 ≤ f x).sum fun x ↦ f x - 1 := by
  let Z := S.filter fun x ↦ f x = 0
  let M := S.filter fun x ↦ 2 ≤ f x
  have hZ : Z.card = ∑ x ∈ S, if f x = 0 then 1 else 0 := by
    rw [Finset.card_eq_sum_ones]
    exact Finset.sum_filter (fun x ↦ f x = 0) (fun _ ↦ 1)
  have hM : M.sum (fun x ↦ f x - 1) =
      ∑ x ∈ S, if 2 ≤ f x then f x - 1 else 0 := by
    exact Finset.sum_filter (fun x ↦ 2 ≤ f x) (fun x ↦ f x - 1)
  have hid : S.sum f + Z.card = S.card + M.sum (fun x ↦ f x - 1) := by
    rw [hZ, hM, Finset.card_eq_sum_ones]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    split_ifs <;> omega
  change Z.card ≤ M.sum fun x ↦ f x - 1
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private def normalize (A : Finset ℕ) : Finset ℕ :=
  A.image fun a ↦ a / A.gcd id

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma gcd_pos (A : Finset ℕ) (h₀ : 0 ∉ A) (hA : A.Nonempty) :
    0 < A.gcd id := by
  apply Nat.pos_of_ne_zero
  intro hg
  obtain ⟨a, ha⟩ := hA
  have := Finset.gcd_eq_zero_iff.mp hg a ha
  exact h₀ (this ▸ ha)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma normalize_card (A : Finset ℕ) : (normalize A).card = A.card := by
  classical
  rw [normalize, Finset.card_image_of_injOn]
  intro a ha b hb hab
  have hda : A.gcd id ∣ a := by
    obtain ⟨c, hc⟩ := Finset.gcd_dvd (f := id) ha
    exact ⟨c, hc⟩
  have hdb : A.gcd id ∣ b := by
    obtain ⟨c, hc⟩ := Finset.gcd_dvd (f := id) hb
    exact ⟨c, hc⟩
  exact (Nat.div_left_inj hda hdb).mp hab

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma normalize_mem (A : Finset ℕ) {a : ℕ} (ha : a ∈ A) :
    a / A.gcd id ∈ normalize A := by
  classical
  exact Finset.mem_image.mpr ⟨a, ha, rfl⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma normalize_nonzero (A : Finset ℕ) (h₀ : 0 ∉ A) : 0 ∉ normalize A := by
  classical
  intro h
  obtain ⟨a, ha, hadiv⟩ := Finset.mem_image.mp h
  have hgda : A.gcd id ∣ a := Finset.gcd_dvd ha
  have ha0 : a ≠ 0 := fun hzero ↦ h₀ (hzero ▸ ha)
  have hdiv0 : a / A.gcd id ≠ 0 := by
    apply Nat.ne_of_gt
    exact Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero ha0) hgda)
      (gcd_pos A h₀ ⟨a, ha⟩)
  exact hdiv0 hadiv

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma normalize_gcd (A : Finset ℕ) (h₀ : 0 ∉ A) (hA : A.Nonempty) :
    (normalize A).gcd id = 1 := by
  classical
  unfold normalize
  rw [← Finset.gcd_eq_gcd_image]
  obtain ⟨a, ha⟩ := hA
  exact Finset.gcd_div_id_eq_one ha (fun h ↦ h₀ (h ▸ ha))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma div_gcd_lt_card_of_not_grahamBound (A : Finset ℕ)
    (hbad : ¬ GrahamBound A) {a b : ℕ} (ha : a ∈ A) (hb : b ∈ A)
    (ha0 : a ≠ 0) : a / a.gcd b < A.card := by
  have hgpos : 0 < a.gcd b := Nat.gcd_pos_of_pos_left b (Nat.pos_of_ne_zero ha0)
  rw [Nat.div_lt_iff_lt_mul hgpos]
  exact Nat.lt_of_not_ge fun h ↦ hbad ⟨a, ha, b, hb, by simpa [mul_comm] using h⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma prime_not_dvd_of_card_le (A : Finset ℕ) (h₀ : 0 ∉ A)
    (hgcd : A.gcd id = 1) (hbad : ¬ GrahamBound A) {p : ℕ} (hp : p.Prime)
    (hcard : A.card ≤ p) {a : ℕ} (ha : a ∈ A) : ¬p ∣ a := by
  intro hpa
  have hex : ∃ b ∈ A, ¬p ∣ b := by
    by_contra h
    push Not at h
    have hpgcd : p ∣ A.gcd id := Finset.dvd_gcd fun b hb ↦ h b hb
    rw [hgcd] at hpgcd
    exact hp.not_dvd_one hpgcd
  obtain ⟨b, hb, hpb⟩ := hex
  have ha0 : a ≠ 0 := fun hz ↦ h₀ (hz ▸ ha)
  have hgpos : 0 < a.gcd b := Nat.gcd_pos_of_pos_left b (Nat.pos_of_ne_zero ha0)
  have hpg : ¬p ∣ a.gcd b := fun h ↦ hpb (h.trans (Nat.gcd_dvd_right a b))
  have hpquot : p ∣ a / a.gcd b := by
    have hprod : (a / a.gcd b) * a.gcd b = a :=
      Nat.div_mul_cancel (Nat.gcd_dvd_left a b)
    have hp_prod : p ∣ (a / a.gcd b) * a.gcd b := by
      rw [hprod]
      exact hpa
    exact (hp.dvd_mul.mp hp_prod).resolve_right hpg
  have hqpos : 0 < a / a.gcd b :=
    Nat.div_pos (Nat.gcd_le_left b (Nat.pos_of_ne_zero ha0)) hgpos
  have hple : p ≤ a / a.gcd b := Nat.le_of_dvd hqpos hpquot
  have hlt := div_gcd_lt_card_of_not_grahamBound A hbad ha hb ha0
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma prime_not_dvd_of_card_le_two_mul (A : Finset ℕ) (h₀ : 0 ∉ A)
    (hgcd : A.gcd id = 1) (hbad : ¬ GrahamBound A) {q : ℕ} (hq : q.Prime)
    (hlarge : A.card ≤ 2 * q) {a : ℕ} (ha : a ∈ A) : ¬q ∣ a := by
  classical
  by_cases hcard : A.card ≤ q
  · exact prime_not_dvd_of_card_le A h₀ hgcd hbad hq hcard ha
  have hqn : q < A.card := Nat.lt_of_not_ge hcard
  intro hqa
  let C := A.filter fun x ↦ q ∣ x
  let V := A.filter fun x ↦ ¬q ∣ x
  let U := C.image fun x ↦ x / q
  have hCne : C.Nonempty := ⟨a, Finset.mem_filter.mpr ⟨ha, hqa⟩⟩
  have hVne : V.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have hall : ∀ x ∈ A, q ∣ x := by
      intro x hx
      by_contra hqx
      have : x ∈ V := Finset.mem_filter.mpr ⟨hx, hqx⟩
      simpa [h] using this
    have hqgcd : q ∣ A.gcd id := Finset.dvd_gcd hall
    rw [hgcd] at hqgcd
    exact hq.not_dvd_one hqgcd
  have hUne : U.Nonempty := hCne.image _
  have hUcard : U.card = C.card := by
    dsimp only [U]
    rw [Finset.card_image_of_injOn]
    intro x hx y hy hxy
    have hqx : q ∣ x := (Finset.mem_filter.mp hx).2
    have hqy : q ∣ y := (Finset.mem_filter.mp hy).2
    exact (Nat.div_left_inj hqx hqy).mp hxy
  have hpartition : C.card + V.card = A.card := by
    simpa only [C, V] using
      (Finset.card_filter_add_card_filter_not (s := A) (p := fun x ↦ q ∣ x))
  have hcross : ∀ c ∈ C, ∀ v ∈ V, c / q ∣ v := by
    intro c hc v hv
    have hcA : c ∈ A := (Finset.mem_filter.mp hc).1
    have hqc : q ∣ c := (Finset.mem_filter.mp hc).2
    have hvA : v ∈ A := (Finset.mem_filter.mp hv).1
    have hqv : ¬q ∣ v := (Finset.mem_filter.mp hv).2
    have hc0 : c ≠ 0 := fun hz ↦ h₀ (hz ▸ hcA)
    have hgpos : 0 < c.gcd v := Nat.gcd_pos_of_pos_left v (Nat.pos_of_ne_zero hc0)
    have hqg : ¬q ∣ c.gcd v := fun h ↦ hqv (h.trans (Nat.gcd_dvd_right c v))
    have hqquot : q ∣ c / c.gcd v := by
      have hprod : (c / c.gcd v) * c.gcd v = c :=
        Nat.div_mul_cancel (Nat.gcd_dvd_left c v)
      have : q ∣ (c / c.gcd v) * c.gcd v := by simpa [hprod] using hqc
      exact (hq.dvd_mul.mp this).resolve_right hqg
    have hquotpos : 0 < c / c.gcd v :=
      Nat.div_pos (Nat.gcd_le_left v (Nat.pos_of_ne_zero hc0)) hgpos
    have hquotlt : c / c.gcd v < A.card :=
      div_gcd_lt_card_of_not_grahamBound A hbad hcA hvA hc0
    have hquoteq : c / c.gcd v = q := by
      obtain ⟨k, hk⟩ := hqquot
      have hkpos : 0 < k := by
        exact Nat.pos_of_mul_pos_left (hk ▸ hquotpos)
      have hkle : k = 1 := by
        by_contra hk1
        have hk2 : 2 ≤ k := by omega
        have htwo : 2 * q ≤ c / c.gcd v := by
          calc
            2 * q = q * 2 := Nat.mul_comm 2 q
            _ ≤ q * k := Nat.mul_le_mul_left q hk2
            _ = c / c.gcd v := hk.symm
        omega
      simpa [hkle] using hk
    have hcprod : q * (c / q) = c := by
      simpa [mul_comm] using Nat.mul_div_cancel' hqc
    have hgprod : q * c.gcd v = c := by
      calc
        q * c.gcd v = (c / c.gcd v) * c.gcd v := by rw [hquoteq]
        _ = c := Nat.div_mul_cancel (Nat.gcd_dvd_left c v)
    have hg : c.gcd v = c / q := Nat.mul_left_cancel hq.pos (hgprod.trans hcprod.symm)
    rw [← hg]
    exact Nat.gcd_dvd_right c v
  have hcrossU : ∀ u ∈ U, ∀ v ∈ V, u ∣ v := by
    intro u hu v hv
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hu
    exact hcross c hc v hv
  let u₀ := U.min' hUne
  let v₀ := V.min' hVne
  have hu₀ : u₀ ∈ U := U.min'_mem hUne
  have hv₀ : v₀ ∈ V := V.min'_mem hVne
  have hu₀pos : 0 < u₀ := by
    obtain ⟨c, hc, hcu⟩ := Finset.mem_image.mp hu₀
    have hcA : c ∈ A := (Finset.mem_filter.mp hc).1
    have hc0 : c ≠ 0 := fun h ↦ h₀ (h ▸ hcA)
    have hqc : q ∣ c := (Finset.mem_filter.mp hc).2
    rw [← hcu]
    exact Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hc0) hqc) hq.pos
  have hv₀pos : 0 < v₀ := by
    exact Nat.pos_of_ne_zero fun h ↦ h₀ (h ▸ (Finset.mem_filter.mp hv₀).1)
  let S₁ := U.image fun u ↦ v₀ / u
  let S₂ := (V.erase v₀).image fun v ↦ v / u₀
  have hS₁card : S₁.card = U.card := by
    dsimp only [S₁]
    rw [Finset.card_image_of_injOn]
    intro u hu w hw huw
    have huv : u ∣ v₀ := hcrossU u hu v₀ hv₀
    have hwv : w ∣ v₀ := hcrossU w hw v₀ hv₀
    have hu0 : 0 < u := by
      exact Nat.pos_of_dvd_of_pos huv hv₀pos
    have hquotpos : 0 < v₀ / u := Nat.div_pos (Nat.le_of_dvd hv₀pos huv) hu0
    change v₀ / u = v₀ / w at huw
    apply Nat.mul_left_cancel hquotpos
    calc
      (v₀ / u) * u = v₀ := Nat.div_mul_cancel huv
      _ = (v₀ / w) * w := (Nat.div_mul_cancel hwv).symm
      _ = (v₀ / u) * w := congrArg (fun z ↦ z * w) huw.symm
  have hS₂card : S₂.card = V.card - 1 := by
    dsimp only [S₂]
    rw [Finset.card_image_of_injOn]
    · rw [Finset.card_erase_of_mem hv₀]
    · intro v hv w hw hvw
      have hvV : v ∈ V := Finset.mem_of_mem_erase hv
      have hwV : w ∈ V := Finset.mem_of_mem_erase hw
      have huv : u₀ ∣ v := hcrossU u₀ hu₀ v hvV
      have huw : u₀ ∣ w := hcrossU u₀ hu₀ w hwV
      change v / u₀ = w / u₀ at hvw
      calc
        v = (v / u₀) * u₀ := (Nat.div_mul_cancel huv).symm
        _ = (w / u₀) * u₀ := congrArg (fun z ↦ z * u₀) hvw
        _ = w := Nat.div_mul_cancel huw
  have hSdisj : Disjoint S₁ S₂ := by
    rw [Finset.disjoint_left]
    intro x hx₁ hx₂
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx₁
    obtain ⟨v, hv, huvEq⟩ := Finset.mem_image.mp hx₂
    have hvV : v ∈ V := Finset.mem_of_mem_erase hv
    have hvne : v ≠ v₀ := (Finset.mem_erase.mp hv).1
    have hv₀lt : v₀ < v := (V.min'_le v hvV).lt_of_ne (Ne.symm hvne)
    have hu₀le : u₀ ≤ u := U.min'_le u hu
    have huv₀ : u ∣ v₀ := hcrossU u hu v₀ hv₀
    have hu₀v : u₀ ∣ v := hcrossU u₀ hu₀ v hvV
    have hvle : v ≤ v₀ := by
      calc
        v = (v / u₀) * u₀ := (Nat.div_mul_cancel hu₀v).symm
        _ = (v₀ / u) * u₀ := by rw [huvEq]
        _ ≤ (v₀ / u) * u := Nat.mul_le_mul_left (v₀ / u) hu₀le
        _ = v₀ := Nat.div_mul_cancel huv₀
    exact (not_le_of_gt hv₀lt) hvle
  let R := S₁ ∪ S₂
  have hRcard : R.card = A.card - 1 := by
    dsimp only [R]
    rw [Finset.card_union_of_disjoint hSdisj, hS₁card, hS₂card, hUcard]
    have hVpos : 0 < V.card := Finset.card_pos.mpr hVne
    omega
  let T := (Finset.Ico 1 A.card).erase q
  have hratio_mem_T : ∀ u ∈ U, ∀ v ∈ V, v / u ∈ T := by
    intro u hu v hv
    have huv : u ∣ v := hcrossU u hu v hv
    have hvA : v ∈ A := (Finset.mem_filter.mp hv).1
    have hv0 : v ≠ 0 := fun h ↦ h₀ (h ▸ hvA)
    have hu0 : 0 < u := Nat.pos_of_dvd_of_pos huv (Nat.pos_of_ne_zero hv0)
    apply Finset.mem_erase.mpr
    refine ⟨?_, Finset.mem_Ico.mpr ⟨?_, ?_⟩⟩
    · intro heq
      have hqratio : q ∣ v / u := heq ▸ dvd_refl q
      have hqv : q ∣ v := by
        rw [← Nat.div_mul_cancel huv]
        exact dvd_mul_of_dvd_left hqratio u
      exact (Finset.mem_filter.mp hv).2 hqv
    · exact Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hv0) huv) hu0
    · obtain ⟨c, hc, hcu⟩ := Finset.mem_image.mp hu
      have hcA : c ∈ A := (Finset.mem_filter.mp hc).1
      have hc0 : c ≠ 0 := fun h ↦ h₀ (h ▸ hcA)
      have hqc : q ∣ c := (Finset.mem_filter.mp hc).2
      have hg : c.gcd v = u := by
        have hgprod : q * c.gcd v = c := by
          have hgpos : 0 < c.gcd v := Nat.gcd_pos_of_pos_left v (Nat.pos_of_ne_zero hc0)
          have hqv : ¬q ∣ v := (Finset.mem_filter.mp hv).2
          have hqg : ¬q ∣ c.gcd v := fun h ↦ hqv (h.trans (Nat.gcd_dvd_right c v))
          have hqquot : q ∣ c / c.gcd v := by
            have hp : q ∣ (c / c.gcd v) * c.gcd v := by
              rw [Nat.div_mul_cancel (Nat.gcd_dvd_left c v)]
              exact hqc
            exact (hq.dvd_mul.mp hp).resolve_right hqg
          have hquotpos : 0 < c / c.gcd v :=
            Nat.div_pos (Nat.gcd_le_left v (Nat.pos_of_ne_zero hc0)) hgpos
          have hquotlt := div_gcd_lt_card_of_not_grahamBound A hbad hcA hvA hc0
          obtain ⟨k, hk⟩ := hqquot
          have hkpos : 0 < k := Nat.pos_of_mul_pos_left (hk ▸ hquotpos)
          have hkone : k = 1 := by
            by_contra hk1
            have hk2 : 2 ≤ k := by omega
            have htwo : 2 * q ≤ c / c.gcd v := by
              calc
                2 * q = q * 2 := Nat.mul_comm 2 q
                _ ≤ q * k := Nat.mul_le_mul_left q hk2
                _ = c / c.gcd v := hk.symm
            omega
          have hquoteq : c / c.gcd v = q := by simpa [hkone] using hk
          calc
            q * c.gcd v = (c / c.gcd v) * c.gcd v := by rw [hquoteq]
            _ = c := Nat.div_mul_cancel (Nat.gcd_dvd_left c v)
        have hcprod : q * (c / q) = c := by
          simpa [mul_comm] using Nat.mul_div_cancel' hqc
        have hgg : c.gcd v = c / q :=
          Nat.mul_left_cancel hq.pos (hgprod.trans hcprod.symm)
        simpa [hcu] using hgg
      have hlt := div_gcd_lt_card_of_not_grahamBound A hbad hvA hcA hv0
      rw [Nat.gcd_comm v c, hg] at hlt
      exact hlt
  have hRsub : R ⊆ T := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
      exact hratio_mem_T u hu v₀ hv₀
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
      exact hratio_mem_T u₀ hu₀ v (Finset.mem_of_mem_erase hv)
  have hqT : q ∈ Finset.Ico 1 A.card := Finset.mem_Ico.mpr ⟨hq.one_le, hqn⟩
  have hTcard : T.card = A.card - 2 := by
    dsimp only [T]
    rw [Finset.card_erase_of_mem hqT, Nat.card_Ico]
    omega
  have hRupper : R.card ≤ A.card - 2 :=
    (Finset.card_le_card hRsub).trans_eq hTcard
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma gcd_mul_cross_of_coprime {a b c d : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : c ≠ 0) (hd : d ≠ 0) (hab : a.Coprime b) (hcd : c.Coprime d) :
    (a * c).gcd (b * d) = a.gcd d * b.gcd c := by
  apply Nat.eq_of_factorization_eq
    (Nat.gcd_pos_of_pos_left _
      (Nat.mul_pos (Nat.pos_of_ne_zero ha) (Nat.pos_of_ne_zero hc))).ne'
    (Nat.mul_ne_zero (Nat.gcd_ne_zero_left ha) (Nat.gcd_ne_zero_left hb))
  intro q
  have habf : min (a.factorization q) (b.factorization q) = 0 := by
    have h := congrArg (fun f ↦ f q) (Nat.factorization_gcd ha hb)
    rw [hab.gcd_eq_one, Nat.factorization_one] at h
    change 0 = min (a.factorization q) (b.factorization q) at h
    exact h.symm
  have hcdf : min (c.factorization q) (d.factorization q) = 0 := by
    have h := congrArg (fun f ↦ f q) (Nat.factorization_gcd hc hd)
    rw [hcd.gcd_eq_one, Nat.factorization_one] at h
    change 0 = min (c.factorization q) (d.factorization q) at h
    exact h.symm
  rw [Nat.factorization_gcd (Nat.mul_ne_zero ha hc) (Nat.mul_ne_zero hb hd),
    Nat.factorization_mul ha hc, Nat.factorization_mul hb hd,
    Nat.factorization_mul (Nat.gcd_ne_zero_left ha) (Nat.gcd_ne_zero_left hb),
    Nat.factorization_gcd ha hd, Nat.factorization_gcd hb hc]
  change min (a.factorization q + c.factorization q)
      (b.factorization q + d.factorization q) =
    min (a.factorization q) (d.factorization q) +
      min (b.factorization q) (c.factorization q)
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma div_gcd_mul_right (x y c : ℕ) (hc : 0 < c) :
    (x * c) / (x * c).gcd (y * c) = x / x.gcd y := by
  rw [Nat.gcd_mul_right, Nat.mul_div_mul_right _ _ hc]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma coprime_prime_sub {p α : ℕ} (hp : p.Prime) (hα : 0 < α)
    (hαp : α < p) : α.Coprime (p - α) := by
  rw [Nat.coprime_sub_self_right hαp.le]
  exact (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hα hαp)).symm

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma factor_closeness {N α β d₁ d₂ : ℕ}
    (hα : 0 < α) (hβ : 0 < β) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (hαβ : α.Coprime β) (hd : d₁.Coprime d₂)
    (hsq : N * N < 2 * (α * α))
    (hα₁₂ : (α * d₁) / (α * d₁).gcd (β * d₂) < N)
    (hα₂₁ : (α * d₂) / (α * d₂).gcd (β * d₁) < N)
    (hβ₁₂ : (β * d₁) / (β * d₁).gcd (α * d₂) < N)
    (hβ₂₁ : (β * d₂) / (β * d₂).gcd (α * d₁) < N) :
    d₁ = d₁.gcd α * d₁.gcd β ∧
    d₂ = d₂.gcd α * d₂.gcd β ∧
    α * d₁.gcd α < N * d₂.gcd α ∧
    α * d₂.gcd α < N * d₁.gcd α ∧
    β * d₁.gcd β < N * d₂.gcd β ∧
    β * d₂.gcd β < N * d₁.gcd β := by
  let X₁ := d₁.gcd α
  let Y₁ := d₁.gcd β
  let X₂ := d₂.gcd α
  let Y₂ := d₂.gcd β
  have hX₁ : 0 < X₁ := Nat.gcd_pos_of_pos_left α hd₁
  have hY₁ : 0 < Y₁ := Nat.gcd_pos_of_pos_left β hd₁
  have hX₂ : 0 < X₂ := Nat.gcd_pos_of_pos_left α hd₂
  have hY₂ : 0 < Y₂ := Nat.gcd_pos_of_pos_left β hd₂
  have hXY₁ : X₁ * Y₁ ∣ d₁ := by
    apply (hαβ.gcd_both d₁ d₁).mul_dvd_of_dvd_of_dvd
    · exact Nat.gcd_dvd_left d₁ α
    · exact Nat.gcd_dvd_left d₁ β
  have hXY₂ : X₂ * Y₂ ∣ d₂ := by
    apply (hαβ.gcd_both d₂ d₂).mul_dvd_of_dvd_of_dvd
    · exact Nat.gcd_dvd_left d₂ α
    · exact Nat.gcd_dvd_left d₂ β
  let Z₁ := d₁ / (X₁ * Y₁)
  let Z₂ := d₂ / (X₂ * Y₂)
  have hZ₁ : 0 < Z₁ := Nat.div_pos (Nat.le_of_dvd hd₁ hXY₁)
    (Nat.mul_pos hX₁ hY₁)
  have hZ₂ : 0 < Z₂ := Nat.div_pos (Nat.le_of_dvd hd₂ hXY₂)
    (Nat.mul_pos hX₂ hY₂)
  have hd₁eq : d₁ = X₁ * Y₁ * Z₁ := by
    simpa [Z₁, mul_comm] using (Nat.div_mul_cancel hXY₁).symm
  have hd₂eq : d₂ = X₂ * Y₂ * Z₂ := by
    simpa [Z₂, mul_comm] using (Nat.div_mul_cancel hXY₂).symm
  have hgα₁₂ : (α * d₁).gcd (β * d₂) = X₂ * Y₁ := by
    rw [gcd_mul_cross_of_coprime hα.ne' hβ.ne' hd₁.ne' hd₂.ne' hαβ hd]
    simp only [X₂, Y₁, Nat.gcd_comm]
  have hgα₂₁ : (α * d₂).gcd (β * d₁) = X₁ * Y₂ := by
    rw [gcd_mul_cross_of_coprime hα.ne' hβ.ne' hd₂.ne' hd₁.ne' hαβ hd.symm]
    simp only [X₁, Y₂, Nat.gcd_comm]
  have hgβ₁₂ : (β * d₁).gcd (α * d₂) = Y₂ * X₁ := by
    rw [gcd_mul_cross_of_coprime hβ.ne' hα.ne' hd₁.ne' hd₂.ne' hαβ.symm hd]
    simp only [Y₂, X₁, Nat.gcd_comm]
  have hgβ₂₁ : (β * d₂).gcd (α * d₁) = Y₁ * X₂ := by
    rw [gcd_mul_cross_of_coprime hβ.ne' hα.ne' hd₂.ne' hd₁.ne' hαβ.symm hd.symm]
    simp only [Y₁, X₂, Nat.gcd_comm]
  have hiα₁₂ : α * X₁ * Z₁ < N * X₂ := by
    rw [hgα₁₂, Nat.div_lt_iff_lt_mul (Nat.mul_pos hX₂ hY₁)] at hα₁₂
    rw [hd₁eq] at hα₁₂
    apply (Nat.mul_lt_mul_right hY₁).mp
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hα₁₂
  have hiα₂₁ : α * X₂ * Z₂ < N * X₁ := by
    rw [hgα₂₁, Nat.div_lt_iff_lt_mul (Nat.mul_pos hX₁ hY₂)] at hα₂₁
    rw [hd₂eq] at hα₂₁
    apply (Nat.mul_lt_mul_right hY₂).mp
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hα₂₁
  have hprod : α * α * (Z₁ * Z₂) < N * N := by
    have hm := mul_lt_mul hiα₁₂ hiα₂₁.le
      (Nat.mul_pos (Nat.mul_pos hα hX₂) hZ₂) (Nat.zero_le (N * X₂))
    have hm' : (α * α * (Z₁ * Z₂)) * (X₁ * X₂) <
        (N * N) * (X₁ * X₂) := by
      simpa only [mul_assoc, mul_comm, mul_left_comm] using hm
    exact (Nat.mul_lt_mul_right (Nat.mul_pos hX₁ hX₂)).mp hm'
  have hZone : Z₁ * Z₂ = 1 := by
    have hlt : α * α * (Z₁ * Z₂) < α * α * 2 := by
      exact hprod.trans (by simpa only [mul_comm] using hsq)
    have hlt' : Z₁ * Z₂ < 2 :=
      (Nat.mul_lt_mul_left (Nat.mul_pos hα hα)).mp hlt
    have hpos : 0 < Z₁ * Z₂ := Nat.mul_pos hZ₁ hZ₂
    omega
  have hz₁one : Z₁ = 1 := Nat.dvd_one.mp ⟨Z₂, hZone.symm⟩
  have hz₂one : Z₂ = 1 :=
    Nat.dvd_one.mp ⟨Z₁, by simpa [mul_comm] using hZone.symm⟩
  have hd₁fac : d₁ = X₁ * Y₁ := by simpa [hz₁one] using hd₁eq
  have hd₂fac : d₂ = X₂ * Y₂ := by simpa [hz₂one] using hd₂eq
  have hiβ₁₂ : β * Y₁ < N * Y₂ := by
    rw [hgβ₁₂, Nat.div_lt_iff_lt_mul (Nat.mul_pos hY₂ hX₁)] at hβ₁₂
    rw [hd₁fac] at hβ₁₂
    apply (Nat.mul_lt_mul_right hX₁).mp
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hβ₁₂
  have hiβ₂₁ : β * Y₂ < N * Y₁ := by
    rw [hgβ₂₁, Nat.div_lt_iff_lt_mul (Nat.mul_pos hY₁ hX₂)] at hβ₂₁
    rw [hd₂fac] at hβ₂₁
    apply (Nat.mul_lt_mul_right hX₂).mp
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hβ₂₁
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [X₁, Y₁] using hd₁fac
  · simpa only [X₂, Y₂] using hd₂fac
  · simpa only [X₁, X₂] using (by simpa [hz₁one] using hiα₁₂)
  · simpa only [X₁, X₂] using (by simpa [hz₂one] using hiα₂₁)
  · simpa only [Y₁, Y₂] using hiβ₁₂
  · simpa only [Y₁, Y₂] using hiβ₂₁

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma factor_closeness_of_counterexample (A : Finset ℕ)
    (hbad : ¬ GrahamBound A) {α β d₁ d₂ c : ℕ}
    (hα : 0 < α) (hβ : 0 < β) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hc : 0 < c)
    (hαβ : α.Coprime β) (hd : d₁.Coprime d₂)
    (hsq : A.card * A.card < 2 * (α * α))
    (hαd₁ : α * d₁ * c ∈ A) (hβd₁ : β * d₁ * c ∈ A)
    (hαd₂ : α * d₂ * c ∈ A) (hβd₂ : β * d₂ * c ∈ A) :
    d₁ = d₁.gcd α * d₁.gcd β ∧
    d₂ = d₂.gcd α * d₂.gcd β ∧
    α * d₁.gcd α < A.card * d₂.gcd α ∧
    α * d₂.gcd α < A.card * d₁.gcd α ∧
    β * d₁.gcd β < A.card * d₂.gcd β ∧
    β * d₂.gcd β < A.card * d₁.gcd β := by
  apply factor_closeness hα hβ hd₁ hd₂ hαβ hd hsq
  · have h := div_gcd_lt_card_of_not_grahamBound A hbad hαd₁ hβd₂
      (Nat.mul_ne_zero (Nat.mul_ne_zero hα.ne' hd₁.ne') hc.ne')
    simpa only [div_gcd_mul_right (α * d₁) (β * d₂) c hc] using h
  · have h := div_gcd_lt_card_of_not_grahamBound A hbad hαd₂ hβd₁
      (Nat.mul_ne_zero (Nat.mul_ne_zero hα.ne' hd₂.ne') hc.ne')
    simpa only [div_gcd_mul_right (α * d₂) (β * d₁) c hc] using h
  · have h := div_gcd_lt_card_of_not_grahamBound A hbad hβd₁ hαd₂
      (Nat.mul_ne_zero (Nat.mul_ne_zero hβ.ne' hd₁.ne') hc.ne')
    simpa only [div_gcd_mul_right (β * d₁) (α * d₂) c hc] using h
  · have h := div_gcd_lt_card_of_not_grahamBound A hbad hβd₂ hαd₁
      (Nat.mul_ne_zero (Nat.mul_ne_zero hβ.ne' hd₂.ne') hc.ne')
    simpa only [div_gcd_mul_right (β * d₂) (α * d₁) c hc] using h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma gcd_quotients_sum_prime_of_folded_eq (A : Finset ℕ)
    (h₀ : 0 ∉ A) (hgcd : A.gcd id = 1) (hbad : ¬ GrahamBound A)
    {p a b : ℕ} (hp : p.Prime) (hlower : A.card < p)
    (ha : a ∈ A) (hb : b ∈ A) (hab : a ≠ b)
    (hfold : foldedResidue p a = foldedResidue p b) :
    a / a.gcd b + b / a.gcd b = p := by
  letI : Fact p.Prime := ⟨hp⟩
  have hpfree {x : ℕ} (hx : x ∈ A) : ¬p ∣ x :=
    prime_not_dvd_of_card_le A h₀ hgcd hbad hp (Nat.le_of_lt hlower) hx
  have ha0 : a ≠ 0 := fun hz ↦ h₀ (hz ▸ ha)
  have hb0 : b ≠ 0 := fun hz ↦ h₀ (hz ▸ hb)
  have hqa : a / a.gcd b < p :=
    (div_gcd_lt_card_of_not_grahamBound A hbad ha hb ha0).trans hlower
  have hqbRaw : b / b.gcd a < p :=
    (div_gcd_lt_card_of_not_grahamBound A hbad hb ha hb0).trans hlower
  have hqb : b / a.gcd b < p := by simpa [Nat.gcd_comm] using hqbRaw
  rcases foldedResidue_eq_iff hp.pos (hpfree ha) (hpfree hb) hfold with hsame | hsum
  · have hcast : (a : ZMod p) = (b : ZMod p) :=
      (ZMod.natCast_eq_natCast_iff' a b p).mpr hsame
    exact (hab (residue_inj_of_div_gcd_lt hp ha0 hb0 (hpfree ha)
      hqa hqb hcast)).elim
  · let g := a.gcd b
    let x := a / g
    let y := b / g
    have hgpos : 0 < g := Nat.gcd_pos_of_pos_left b (Nat.pos_of_ne_zero ha0)
    have hga : g * x = a := Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)
    have hgb : g * y = b := Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)
    have hpg : ¬p ∣ g := fun h ↦ (hpfree ha) (h.trans (Nat.gcd_dvd_left a b))
    have hcg0 : (g : ZMod p) ≠ 0 := by
      intro hz
      exact hpg ((ZMod.natCast_eq_zero_iff g p).mp hz)
    have hpab : p ∣ a + b := by
      apply Nat.dvd_of_mod_eq_zero
      rw [Nat.add_mod, hsum, Nat.mod_self]
    have hcastsum : (a : ZMod p) + (b : ZMod p) = 0 := by
      rw [← Nat.cast_add, ZMod.natCast_eq_zero_iff]
      exact hpab
    have hfactor : (g : ZMod p) * ((x : ZMod p) + (y : ZMod p)) = 0 := by
      rw [mul_add]
      calc
        (g : ZMod p) * x + (g : ZMod p) * y =
            ((g * x : ℕ) : ZMod p) + ((g * y : ℕ) : ZMod p) := by
              rw [Nat.cast_mul, Nat.cast_mul]
        _ = (a : ZMod p) + (b : ZMod p) := by rw [hga, hgb]
        _ = 0 := hcastsum
    have hxycast : (x : ZMod p) + (y : ZMod p) = 0 :=
      (mul_eq_zero.mp hfactor).resolve_left hcg0
    have hpxy : p ∣ x + y := by
      apply (ZMod.natCast_eq_zero_iff (x + y) p).mp
      simpa only [Nat.cast_add] using hxycast
    have hxpos : 0 < x :=
      Nat.div_pos (Nat.gcd_le_left b (Nat.pos_of_ne_zero ha0)) hgpos
    have hypos : 0 < y :=
      Nat.div_pos (Nat.gcd_le_right a (Nat.pos_of_ne_zero hb0)) hgpos
    have hxlt : x < p := by simpa only [x, g] using hqa
    have hylt : y < p := by simpa only [y, g] using hqb
    have hxy : x + y = p :=
      Nat.eq_of_dvd_of_lt_two_mul (by omega) hpxy (by omega)
    simpa only [g, x, y] using hxy

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma card_J_le_representationPairs (A : Finset ℕ) (h₀ : 0 ∉ A)
    (hgcd : A.gcd id = 1) (hbad : ¬ GrahamBound A) {p : ℕ} (hp : p.Prime)
    (hlower : A.card < p) (hupper : p < 2 * A.card) :
    (Finset.Icc ((p + 1) / 2) A.card).card ≤ (representationPairs A p).card := by
  classical
  have hpfree {a : ℕ} (ha : a ∈ A) : ¬p ∣ a :=
    prime_not_dvd_of_card_le A h₀ hgcd hbad hp (Nat.le_of_lt hlower) ha
  let R := A.filter fun a ↦ foldedMin A p a = a
  let E := A.filter fun a ↦ foldedMin A p a ≠ a
  have hpartition : R.card + E.card = A.card := by
    simpa only [R, E] using
      (Finset.card_filter_add_card_filter_not
        (s := A) (p := fun a ↦ foldedMin A p a = a))
  let color : {a // a ∈ R} → Fin (p / 2) := fun a ↦
    ⟨foldedResidue p a.1 - 1, by
      have haA : a.1 ∈ A := (Finset.mem_filter.mp a.2).1
      have hpos := foldedResidue_pos hp.pos (hpfree haA)
      have hle := foldedResidue_le_div_two (a := a.1) hp.pos
      omega⟩
  have hcolor : Function.Injective color := by
    intro a b hab
    apply Subtype.ext
    have haA : a.1 ∈ A := (Finset.mem_filter.mp a.2).1
    have hbA : b.1 ∈ A := (Finset.mem_filter.mp b.2).1
    have hapos := foldedResidue_pos hp.pos (hpfree haA)
    have hbpos := foldedResidue_pos hp.pos (hpfree hbA)
    have hval := congrArg Fin.val hab
    have hfold : foldedResidue p a.1 = foldedResidue p b.1 := by
      dsimp only [color] at hval
      omega
    have hmins := foldedMin_eq_of_color haA hbA hfold
    have harep : foldedMin A p a.1 = a.1 := (Finset.mem_filter.mp a.2).2
    have hbrep : foldedMin A p b.1 = b.1 := (Finset.mem_filter.mp b.2).2
    exact harep.symm.trans (hmins.trans hbrep)
  have hRcard : R.card ≤ p / 2 := by
    have hle := Fintype.card_le_of_injective color hcolor
    simpa using hle
  have hpne : p ≠ 2 := by
    intro hp2
    rw [hp2] at hlower hupper
    omega
  have hpmod : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hpne)
  have hJcard : (Finset.Icc ((p + 1) / 2) A.card).card = A.card - p / 2 := by
    rw [Nat.card_Icc]
    omega
  have hJleE : (Finset.Icc ((p + 1) / 2) A.card).card ≤ E.card := by
    rw [hJcard]
    omega
  let collisionMap : ℕ → ((α : ℕ) × ℕ) := fun a ↦
    ⟨a / (foldedMin A p a).gcd a, (foldedMin A p a).gcd a⟩
  have hmaps : Set.MapsTo collisionMap (↑E : Set ℕ) (↑(representationPairs A p)) := by
    intro a haE
    have haE' : a ∈ E := haE
    have haA : a ∈ A := (Finset.mem_filter.mp haE').1
    have hne : foldedMin A p a ≠ a := (Finset.mem_filter.mp haE').2
    let b := foldedMin A p a
    let g := b.gcd a
    have hbA : b ∈ A := foldedMin_mem haA
    have hfold : foldedResidue p b = foldedResidue p a := foldedMin_color haA
    have hble : b ≤ a := foldedMin_le haA haA rfl
    have hblt : b < a := hble.lt_of_ne hne
    have hb0 : b ≠ 0 := fun hz ↦ h₀ (hz ▸ hbA)
    have ha0 : a ≠ 0 := fun hz ↦ h₀ (hz ▸ haA)
    have hgpos : 0 < g := Nat.gcd_pos_of_pos_left a (Nat.pos_of_ne_zero hb0)
    have hgb : (b / g) * g = b := by
      exact Nat.div_mul_cancel (Nat.gcd_dvd_left b a)
    have hga : (a / g) * g = a := by
      exact Nat.div_mul_cancel (Nat.gcd_dvd_right b a)
    have hsum : b / g + a / g = p := by
      simpa only [b, g] using gcd_quotients_sum_prime_of_folded_eq A h₀ hgcd hbad hp
        hlower hbA haA hne hfold
    have hquotorder : b / g < a / g := by
      apply (Nat.mul_lt_mul_right hgpos).mp
      simpa only [hgb, hga] using hblt
    have hαpos : 0 < a / g := by omega
    have hαlower : (p + 1) / 2 ≤ a / g := by omega
    have hαlt : a / g < A.card := by
      have h := div_gcd_lt_card_of_not_grahamBound A hbad haA hbA ha0
      simpa only [g, Nat.gcd_comm] using h
    have hβ : p - a / g = b / g := by omega
    change (⟨a / g, g⟩ : (α : ℕ) × ℕ) ∈ representationPairs A p
    apply Finset.mem_sigma.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨hαlower, hαlt.le⟩, ?_⟩
    rw [mem_representedMultipliers hαpos]
    refine ⟨hgpos, ?_, ?_⟩
    · rw [hga]
      exact haA
    rw [hβ]
    rw [hgb]
    exact hbA
  have hinj : Set.InjOn collisionMap (↑E : Set ℕ) := by
    intro a ha b hb hab
    have hprod := congrArg (fun z : (α : ℕ) × ℕ ↦ z.1 * z.2) hab
    dsimp only [collisionMap] at hprod
    calc
      a = (a / (foldedMin A p a).gcd a) * (foldedMin A p a).gcd a :=
        (Nat.div_mul_cancel (Nat.gcd_dvd_right (foldedMin A p a) a)).symm
      _ = (b / (foldedMin A p b).gcd b) * (foldedMin A p b).gcd b := hprod
      _ = b := Nat.div_mul_cancel (Nat.gcd_dvd_right (foldedMin A p b) b)
  exact hJleE.trans (Finset.card_le_card_of_injOn collisionMap hmaps hinj)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma zero_card_le_representation_excess (A : Finset ℕ) (h₀ : 0 ∉ A)
    (hgcd : A.gcd id = 1) (hbad : ¬ GrahamBound A) {p : ℕ} (hp : p.Prime)
    (hlower : A.card < p) (hupper : p < 2 * A.card) :
    ((Finset.Icc ((p + 1) / 2) A.card).filter fun α ↦
        representationCount A p α = 0).card ≤
      ((Finset.Icc ((p + 1) / 2) A.card).filter fun α ↦
        2 ≤ representationCount A p α).sum fun α ↦ representationCount A p α - 1 := by
  apply zero_card_le_excess
  calc
    (Finset.Icc ((p + 1) / 2) A.card).card ≤
        (representationPairs A p).card :=
      card_J_le_representationPairs A h₀ hgcd hbad hp hlower hupper
    _ = (Finset.Icc ((p + 1) / 2) A.card).sum
        (representationCount A p) := by
      rw [representationPairs, Finset.card_sigma]
      rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma grahamBound_of_normalize (A : Finset ℕ)
    (h : GrahamBound (normalize A)) : GrahamBound A := by
  classical
  obtain ⟨a₀, ha₀, b₀, hb₀, hab⟩ := h
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp ha₀
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hb₀
  refine ⟨a, ha, b, hb, ?_⟩
  have hga : A.gcd id ∣ a := Finset.gcd_dvd ha
  have hgb : A.gcd id ∣ b := Finset.gcd_dvd hb
  have hggcd : A.gcd id ∣ a.gcd b := Nat.dvd_gcd hga hgb
  have hcard : (normalize A).card = A.card := normalize_card A
  rw [hcard, Nat.gcd_div hga hgb] at hab
  have hmul := Nat.mul_le_mul_right (A.gcd id) hab
  simpa only [mul_assoc, Nat.div_mul_cancel hggcd, Nat.div_mul_cancel hga] using hmul

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma lcm_div_gcd_eq (a : ℕ) (ha : a ≠ 0) (S : Finset ℕ) :
    S.lcm (fun b ↦ a / a.gcd b) = a / a.gcd (S.gcd id) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [Nat.div_self (Nat.pos_of_ne_zero ha)]
  | @insert b S hb ih =>
      rw [Finset.lcm_insert, Finset.gcd_insert, ih]
      change Nat.lcm (a / a.gcd b) (a / a.gcd (S.gcd id)) =
        a / a.gcd (b.gcd (S.gcd id))
      rw [Nat.div_lcm_eq_div_gcd (Nat.gcd_dvd_left a b)
        (Nat.gcd_dvd_left a (S.gcd id))]
      have hden : (a.gcd b).gcd (a.gcd (S.gcd id)) =
          a.gcd (b.gcd (S.gcd id)) := by
        rw [Nat.gcd_assoc, Nat.gcd_left_comm b a (S.gcd id), ← Nat.gcd_assoc,
          Nat.gcd_self]
      rw [hden]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma normalize_represented_dvd_product (A : Finset ℕ)
    (hbad : ¬ GrahamBound A) {α β : ℕ}
    (hα : 0 < α) (hβ : 0 < β) (hαβ : α.Coprime β)
    (hsq : A.card * A.card < 2 * (α * α))
    (hD : (representedMultipliers A α β).Nonempty) :
    ∀ d ∈ normalize (representedMultipliers A α β), d ∣ α * β := by
  classical
  let D := representedMultipliers A α β
  let B := normalize D
  let c := D.gcd id
  have hD₀ : 0 ∉ D := representedMultipliers_nonzero hα
  have hc : 0 < c := gcd_pos D hD₀ hD
  have hBgcd : B.gcd id = 1 := normalize_gcd D hD₀ hD
  have hrepresented : ∀ {d}, d ∈ B →
      0 < d ∧ α * d * c ∈ A ∧ β * d * c ∈ A := by
    intro d hd
    change d ∈ D.image (fun e ↦ e / D.gcd id) at hd
    obtain ⟨e, heD, rfl⟩ := Finset.mem_image.mp hd
    have he := (mem_representedMultipliers hα).mp heD
    have hce : D.gcd id ∣ e := Finset.gcd_dvd heD
    have heq : e / D.gcd id * D.gcd id = e := Nat.div_mul_cancel hce
    refine ⟨?_, ?_, ?_⟩
    · exact Nat.div_pos (Nat.le_of_dvd he.1 hce) hc
    · change α * (e / D.gcd id) * D.gcd id ∈ A
      rw [mul_assoc, heq]
      exact he.2.1
    · change β * (e / D.gcd id) * D.gcd id ∈ A
      rw [mul_assoc, heq]
      exact he.2.2
  intro d hdB
  have hdpos := (hrepresented hdB).1
  have hlocal : ∀ e ∈ B, d / d.gcd e ∣ α * β := by
    intro e heB
    have hepos := (hrepresented heB).1
    let g := d.gcd e
    let d' := d / g
    let e' := e / g
    have hg : 0 < g := Nat.gcd_pos_of_pos_left e hdpos
    have hd' : 0 < d' := Nat.div_pos (Nat.gcd_le_left e hdpos) hg
    have he' : 0 < e' := Nat.div_pos (Nat.gcd_le_right d hepos) hg
    have hcop : d'.Coprime e' := Nat.coprime_div_gcd_div_gcd hg
    have hdexpand : d' * (g * c) = d * c := by
      calc
        d' * (g * c) = (d' * g) * c := by simp only [mul_assoc]
        _ = d * c := by rw [Nat.div_mul_cancel (Nat.gcd_dvd_left d e)]
    have heexpand : e' * (g * c) = e * c := by
      calc
        e' * (g * c) = (e' * g) * c := by simp only [mul_assoc]
        _ = e * c := by rw [Nat.div_mul_cancel (Nat.gcd_dvd_right d e)]
    have hfac := factor_closeness_of_counterexample A hbad hα hβ hd' he'
      (Nat.mul_pos hg hc) hαβ hcop hsq
      (by rw [mul_assoc, hdexpand, ← mul_assoc]; exact (hrepresented hdB).2.1)
      (by rw [mul_assoc, hdexpand, ← mul_assoc]; exact (hrepresented hdB).2.2)
      (by rw [mul_assoc, heexpand, ← mul_assoc]; exact (hrepresented heB).2.1)
      (by rw [mul_assoc, heexpand, ← mul_assoc]; exact (hrepresented heB).2.2)
    change d' ∣ α * β
    rw [hfac.1]
    exact Nat.mul_dvd_mul (Nat.gcd_dvd_right d' α) (Nat.gcd_dvd_right d' β)
  have hlcm : B.lcm (fun e ↦ d / d.gcd e) ∣ α * β := Finset.lcm_dvd hlocal
  rw [lcm_div_gcd_eq d hdpos.ne' B, hBgcd, Nat.gcd_one_right, Nat.div_one] at hlcm
  exact hlcm

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma gcd_div_gcd_eq_component {α β d e : ℕ}
    (hαβ : α.Coprime β) (hd : 0 < d) (he : 0 < e)
    (hdfac : d = d.gcd α * d.gcd β)
    (hefac : e = e.gcd α * e.gcd β) :
    (d / d.gcd e).gcd α = d.gcd α / (d.gcd α).gcd (e.gcd α) := by
  let u := d.gcd α
  let v := d.gcd β
  let x := e.gcd α
  let y := e.gcd β
  have hu : 0 < u := Nat.gcd_pos_of_pos_left α hd
  have hv : 0 < v := Nat.gcd_pos_of_pos_left β hd
  have hx : 0 < x := Nat.gcd_pos_of_pos_left α he
  have hy : 0 < y := Nat.gcd_pos_of_pos_left β he
  have huα : u ∣ α := Nat.gcd_dvd_right d α
  have hvβ : v ∣ β := Nat.gcd_dvd_right d β
  have hxα : x ∣ α := Nat.gcd_dvd_right e α
  have hyβ : y ∣ β := Nat.gcd_dvd_right e β
  have huy : u.Coprime y := Nat.Coprime.of_dvd huα hyβ hαβ
  have hvx : v.Coprime x := Nat.Coprime.of_dvd hvβ hxα hαβ.symm
  have hgde : d.gcd e = u.gcd x * v.gcd y := by
    rw [hdfac, hefac]
    change (u * v).gcd (x * y) = u.gcd x * v.gcd y
    rw [mul_comm x y,
      gcd_mul_cross_of_coprime hu.ne' hy.ne' hv.ne' hx.ne' huy hvx]
    simp only [Nat.gcd_comm y v]
  have hdiv : d / d.gcd e =
      (u / u.gcd x) * (v / v.gcd y) := by
    rw [hgde, hdfac]
    exact (Nat.div_mul_div_comm (Nat.gcd_dvd_left u x)
      (Nat.gcd_dvd_left v y)).symm
  have huv : u / u.gcd x ∣ α :=
    (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left u x)).trans huα
  have hvv : v / v.gcd y ∣ β :=
    (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left v y)).trans hvβ
  have hcop : (v / v.gcd y).Coprime α :=
    Nat.Coprime.of_dvd hvv dvd_rfl hαβ.symm
  rw [hdiv, mul_comm]
  exact Nat.gcd_mul_of_coprime_of_dvd hcop huv

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma component_eq_of_gap_square_lt {N α x y : ℕ}
    (hα : 0 < α) (hαN : α ≤ N)
    (hx : 0 < x) (hy : 0 < y) (hxα : x ∣ α) (hyα : y ∣ α)
    (hgap : (N - α) * (N - α) < α)
    (hxy : α * (x / x.gcd y) < N * (y / x.gcd y))
    (hyx : α * (y / x.gcd y) < N * (x / x.gcd y)) : x = y := by
  let g := x.gcd y
  let X := x / g
  let Y := y / g
  have hg : 0 < g := Nat.gcd_pos_of_pos_left y hx
  have hX : 0 < X := Nat.div_pos (Nat.gcd_le_left y hx) hg
  have hY : 0 < Y := Nat.div_pos (Nat.gcd_le_right x hy) hg
  have hcop : X.Coprime Y := Nat.coprime_div_gcd_div_gcd hg
  have hXα : X ∣ α := (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left x y)).trans hxα
  have hYα : Y ∣ α := (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right x y)).trans hyα
  have hprod : X * Y ∣ α := hcop.mul_dvd_of_dvd_of_dvd hXα hYα
  have hprodLe : X * Y ≤ α := Nat.le_of_dvd hα hprod
  have hNsplit : N - α + α = N := Nat.sub_add_cancel hαN
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hXY : X < Y :=
      (Nat.div_lt_div_right hg.ne' (Nat.gcd_dvd_left x y)
        (Nat.gcd_dvd_right x y)).mpr hlt
    have hstep : α * (X + 1) < N * X := by
      apply (Nat.mul_le_mul_left α (Nat.succ_le_iff.mpr hXY)).trans_lt
      simpa only [g, X, Y] using hyx
    have hAX : α < (N - α) * X := by
      rw [← hNsplit, add_mul, mul_add] at hstep
      omega
    have hXsq : X * X ≤ α :=
      (Nat.mul_le_mul_left X hXY.le).trans hprodLe
    have hm := mul_lt_mul hgap hXsq
      (Nat.mul_pos hX hX) (Nat.zero_le α)
    have hm' : ((N - α) * X) * ((N - α) * X) < α * α := by
      simpa only [mul_assoc, mul_comm, mul_left_comm] using hm
    exact (Nat.not_lt_of_ge (Nat.mul_self_lt_mul_self hAX).le) hm'
  · have hYX : Y < X :=
      (Nat.div_lt_div_right hg.ne' (Nat.gcd_dvd_right x y)
        (Nat.gcd_dvd_left x y)).mpr hgt
    have hstep : α * (Y + 1) < N * Y := by
      apply (Nat.mul_le_mul_left α (Nat.succ_le_iff.mpr hYX)).trans_lt
      simpa only [g, X, Y] using hxy
    have hAY : α < (N - α) * Y := by
      rw [← hNsplit, add_mul, mul_add] at hstep
      omega
    have hYsq : Y * Y ≤ α :=
      (Nat.mul_le_mul_left Y hYX.le).trans (by
        simpa only [mul_comm X Y] using hprodLe)
    have hm := mul_lt_mul hgap hYsq
      (Nat.mul_pos hY hY) (Nat.zero_le α)
    have hm' : ((N - α) * Y) * ((N - α) * Y) < α * α := by
      simpa only [mul_assoc, mul_comm, mul_left_comm] using hm
    exact (Nat.not_lt_of_ge (Nat.mul_self_lt_mul_self hAY).le) hm'

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma scaled_component_closeness (A : Finset ℕ)
    (hbad : ¬ GrahamBound A) {α β d e c : ℕ}
    (hα : 0 < α) (hβ : 0 < β) (hd : 0 < d) (he : 0 < e) (hc : 0 < c)
    (hαβ : α.Coprime β)
    (hsq : A.card * A.card < 2 * (α * α))
    (hdfac : d = d.gcd α * d.gcd β)
    (hefac : e = e.gcd α * e.gcd β)
    (hαd : α * d * c ∈ A) (hβd : β * d * c ∈ A)
    (hαe : α * e * c ∈ A) (hβe : β * e * c ∈ A) :
    α * (d.gcd α / (d.gcd α).gcd (e.gcd α)) <
        A.card * (e.gcd α / (d.gcd α).gcd (e.gcd α)) ∧
    α * (e.gcd α / (d.gcd α).gcd (e.gcd α)) <
        A.card * (d.gcd α / (d.gcd α).gcd (e.gcd α)) ∧
    β * (d.gcd β / (d.gcd β).gcd (e.gcd β)) <
        A.card * (e.gcd β / (d.gcd β).gcd (e.gcd β)) ∧
    β * (e.gcd β / (d.gcd β).gcd (e.gcd β)) <
        A.card * (d.gcd β / (d.gcd β).gcd (e.gcd β)) := by
  let g := d.gcd e
  let d' := d / g
  let e' := e / g
  have hg : 0 < g := Nat.gcd_pos_of_pos_left e hd
  have hd' : 0 < d' := Nat.div_pos (Nat.gcd_le_left e hd) hg
  have he' : 0 < e' := Nat.div_pos (Nat.gcd_le_right d he) hg
  have hcop : d'.Coprime e' := Nat.coprime_div_gcd_div_gcd hg
  have hdexpand : d' * (g * c) = d * c := by
    calc
      d' * (g * c) = (d' * g) * c := by rw [mul_assoc]
      _ = d * c := by rw [Nat.div_mul_cancel (Nat.gcd_dvd_left d e)]
  have heexpand : e' * (g * c) = e * c := by
    calc
      e' * (g * c) = (e' * g) * c := by rw [mul_assoc]
      _ = e * c := by rw [Nat.div_mul_cancel (Nat.gcd_dvd_right d e)]
  have hfac := factor_closeness_of_counterexample A hbad hα hβ hd' he'
    (Nat.mul_pos hg hc) hαβ hcop hsq
    (by rw [mul_assoc, hdexpand, ← mul_assoc]; exact hαd)
    (by rw [mul_assoc, hdexpand, ← mul_assoc]; exact hβd)
    (by rw [mul_assoc, heexpand, ← mul_assoc]; exact hαe)
    (by rw [mul_assoc, heexpand, ← mul_assoc]; exact hβe)
  have hdα : d'.gcd α = d.gcd α / (d.gcd α).gcd (e.gcd α) :=
    gcd_div_gcd_eq_component hαβ hd he hdfac hefac
  have heα : e'.gcd α = e.gcd α / (d.gcd α).gcd (e.gcd α) := by
    simpa only [e', g, Nat.gcd_comm e d,
      Nat.gcd_comm (e.gcd α) (d.gcd α)] using
      (gcd_div_gcd_eq_component hαβ he hd hefac hdfac)
  have hdβ : d'.gcd β = d.gcd β / (d.gcd β).gcd (e.gcd β) :=
    gcd_div_gcd_eq_component hαβ.symm hd he
      (by simpa only [mul_comm] using hdfac)
      (by simpa only [mul_comm] using hefac)
  have heβ : e'.gcd β = e.gcd β / (d.gcd β).gcd (e.gcd β) := by
    simpa only [e', g, Nat.gcd_comm e d,
      Nat.gcd_comm (e.gcd β) (d.gcd β)] using
      (gcd_div_gcd_eq_component hαβ.symm he hd
        (by simpa only [mul_comm] using hefac)
        (by simpa only [mul_comm] using hdfac))
  have hα₁ := hfac.2.2.1
  have hα₂ := hfac.2.2.2.1
  have hβ₁ := hfac.2.2.2.2.1
  have hβ₂ := hfac.2.2.2.2.2
  rw [hdα, heα] at hα₁ hα₂
  rw [hdβ, heβ] at hβ₁ hβ₂
  exact ⟨hα₁, hα₂, hβ₁, hβ₂⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma triple_product_dvd_mul_pairwise_gcds {n x y z : ℕ}
    (hn : 0 < n) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxn : x ∣ n) (hyn : y ∣ n) (hzn : z ∣ n)
    (hxyz : x.gcd (y.gcd z) = 1) :
    x * y * z ∣ n * x.gcd y * x.gcd z * y.gcd z := by
  rw [← Nat.factorization_le_iff_dvd
    (Nat.mul_ne_zero (Nat.mul_ne_zero hx.ne' hy.ne') hz.ne')
    (Nat.mul_ne_zero
      (Nat.mul_ne_zero (Nat.mul_ne_zero hn.ne'
        (Nat.gcd_pos_of_pos_left y hx).ne')
        (Nat.gcd_pos_of_pos_left z hx).ne')
      (Nat.gcd_pos_of_pos_left z hy).ne')]
  intro q
  have hxn' := (Nat.factorization_le_iff_dvd hx.ne' hn.ne').mpr hxn q
  have hyn' := (Nat.factorization_le_iff_dvd hy.ne' hn.ne').mpr hyn q
  have hzn' := (Nat.factorization_le_iff_dvd hz.ne' hn.ne').mpr hzn q
  have hmin := congrArg (fun f : ℕ →₀ ℕ ↦ f q)
    (Nat.factorization_gcd hx.ne'
      (Nat.gcd_pos_of_pos_left z hy).ne')
  rw [hxyz] at hmin
  simp only [Nat.factorization_one, Finsupp.inf_apply,
    Nat.factorization_gcd hy.ne' hz.ne'] at hmin
  rw [Nat.factorization_mul (Nat.mul_ne_zero hx.ne' hy.ne') hz.ne',
    Nat.factorization_mul hx.ne' hy.ne',
    Nat.factorization_mul
      (Nat.mul_ne_zero
        (Nat.mul_ne_zero hn.ne' (Nat.gcd_pos_of_pos_left y hx).ne')
        (Nat.gcd_pos_of_pos_left z hx).ne')
      (Nat.gcd_pos_of_pos_left z hy).ne',
    Nat.factorization_mul
      (Nat.mul_ne_zero hn.ne' (Nat.gcd_pos_of_pos_left y hx).ne')
      (Nat.gcd_pos_of_pos_left z hx).ne',
    Nat.factorization_mul hn.ne' (Nat.gcd_pos_of_pos_left y hx).ne',
    Nat.factorization_gcd hx.ne' hy.ne',
    Nat.factorization_gcd hx.ne' hz.ne',
    Nat.factorization_gcd hy.ne' hz.ne']
  simp only [Finsupp.add_apply, Finsupp.inf_apply]
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma reduced_divisors_diff_eq_one {N β y z : ℕ}
    (hβ : 0 < β) (hβN : β ≤ N)
    (hy : 0 < y) (hz : 0 < z) (hyz : y < z)
    (hyβ : y ∣ β) (hzβ : z ∣ β)
    (hgap : (N - β) * (N - β) ≤ 4 * N)
    (hclose : β * (z / y.gcd z) < N * (y / y.gcd z)) :
    z / y.gcd z = y / y.gcd z + 1 := by
  let g := y.gcd z
  let u := y / g
  let v := z / g
  let k := v - u
  have hg : 0 < g := Nat.gcd_pos_of_pos_left z hy
  have hu : 0 < u := Nat.div_pos (Nat.gcd_le_left z hy) hg
  have hv : 0 < v := Nat.div_pos (Nat.gcd_le_right y hz) hg
  have huv : u < v :=
    (Nat.div_lt_div_right hg.ne' (Nat.gcd_dvd_left y z)
      (Nat.gcd_dvd_right y z)).mpr hyz
  have hk : 0 < k := Nat.sub_pos_of_lt huv
  have hvsplit : u + k = v := Nat.add_sub_of_le huv.le
  have hcop : u.Coprime v := Nat.coprime_div_gcd_div_gcd hg
  have huβ : u ∣ β := (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left y z)).trans hyβ
  have hvβ : v ∣ β := (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right y z)).trans hzβ
  have huvβ : u * v ∣ β := hcop.mul_dvd_of_dvd_of_dvd huβ hvβ
  have huvle : u * v ≤ β := Nat.le_of_dvd hβ huvβ
  have hN : 0 < N := hβ.trans_le hβN
  have hNsplit : N - β + β = N := Nat.sub_add_cancel hβN
  have hβk : β * k < (N - β) * u := by
    change β * v < N * u at hclose
    rw [← hvsplit, mul_add, ← hNsplit, add_mul] at hclose
    omega
  have hNk : N * k < (N - β) * v := by
    calc
      N * k = (β + (N - β)) * k := by rw [add_comm, hNsplit]
      _ = β * k + (N - β) * k := by rw [add_mul]
      _ < (N - β) * u + (N - β) * k :=
        Nat.add_lt_add_right hβk _
      _ = (N - β) * v := by rw [← hvsplit, mul_add]
  have hm := mul_lt_mul hβk hNk.le (Nat.mul_pos hN hk)
    (Nat.zero_le ((N - β) * u))
  have hm' : β * N * (k * k) <
      ((N - β) * (N - β)) * (u * v) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hm
  have hright : ((N - β) * (N - β)) * (u * v) ≤
      (4 * N) * β := Nat.mul_le_mul hgap huvle
  have hkk : k * k < 4 := by
    apply (Nat.mul_lt_mul_left (Nat.mul_pos hβ hN)).mp
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hm'.trans_le hright
  have hkone : k = 1 := by
    have hklt : k < 2 := Nat.mul_self_lt_mul_self_iff.mp (by
      simpa only [show 2 * 2 = 4 by norm_num] using hkk)
    omega
  simpa only [u, v, k, hkone] using hvsplit.symm

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma spacing_polynomial_contradiction {N δ a b c : ℕ}
    (hN : 10 ≤ N) (hδ : 0 < δ) (ha : 0 < a) (hc : 0 < c)
    (hb : a + c = b) (hgap : δ * δ ≤ 4 * N)
    (hmain : (b * N) * (b * N) <
      (a * c * δ) * (δ * δ) + (b * N) * (c * δ)) : False := by
  have hNpos : 0 < N := by omega
  have hbpos : 0 < b := by omega
  let K := 4 * a + b
  have hfirst : (a * c * δ) * (δ * δ) ≤
      (a * c * δ) * (4 * N) := Nat.mul_le_mul_left _ hgap
  have hsmall : b * b * N < c * δ * K := by
    apply (Nat.mul_lt_mul_left hNpos).mp
    have ht := hmain.trans_le (Nat.add_le_add_right hfirst _)
    simpa only [K, mul_assoc, mul_comm, mul_left_comm,
      Nat.mul_add, Nat.add_mul] using ht
  have hsquare := Nat.mul_self_lt_mul_self hsmall
  have hright : (c * δ * K) * (c * δ * K) ≤
      4 * N * (c * c * (K * K)) := by
    have := Nat.mul_le_mul_left (c * c * (K * K)) hgap
    simpa only [mul_assoc, mul_comm, mul_left_comm] using this
  have hcore : b * b * b * b * N < 4 * c * c * (K * K) := by
    apply (Nat.mul_lt_mul_left hNpos).mp
    simpa only [mul_assoc, mul_comm, mul_left_comm] using
      hsquare.trans_le hright
  have hmax : 16 * c * K ≤ 25 * (b * b) := by
    have hs : 0 ≤ (5 * (a : ℤ) - 3 * (c : ℤ)) ^ 2 := sq_nonneg _
    dsimp only [K]
    nlinarith
  have hmaxsq := Nat.mul_le_mul hmax hmax
  have hmaxsq' : 256 * (c * c * (K * K)) ≤
      625 * (b * b * b * b) := by
    calc
      256 * (c * c * (K * K)) = (16 * c * K) * (16 * c * K) := by ring
      _ ≤ (25 * (b * b)) * (25 * (b * b)) := hmaxsq
      _ = 625 * (b * b * b * b) := by ring
  have hscaled := (Nat.mul_lt_mul_left (by norm_num : 0 < 256)).mpr hcore
  have hfinal : 256 * N * (b * b * b * b) <
      2500 * (b * b * b * b) := by
    calc
      256 * N * (b * b * b * b) =
          256 * (b * b * b * b * N) := by
            simp only [mul_assoc, mul_comm, mul_left_comm]
      _ < 256 * (4 * c * c * (K * K)) := hscaled
      _ ≤ 4 * (625 * (b * b * b * b)) := by
        simpa only [mul_assoc, mul_comm, mul_left_comm] using
          Nat.mul_le_mul_left 4 hmaxsq'
      _ = 2500 * (b * b * b * b) := by ring
  have hpowpos : 0 < b * b * b * b := by positivity
  have : 256 * N < 2500 := by
    apply (Nat.mul_lt_mul_right hpowpos).mp
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hfinal
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma no_three_close_divisors {N β y₁ y₂ y₃ : ℕ}
    (hN : 10 ≤ N) (hβ : 0 < β) (hβN : β < N)
    (hy₁ : 0 < y₁) (hy₂ : 0 < y₂) (hy₃ : 0 < y₃)
    (h₁₂ : y₁ < y₂) (h₂₃ : y₂ < y₃)
    (hy₁β : y₁ ∣ β) (hy₂β : y₂ ∣ β) (hy₃β : y₃ ∣ β)
    (hgcd : y₁.gcd (y₂.gcd y₃) = 1)
    (hgap : (N - β) * (N - β) ≤ 4 * N)
    (hclose₁₂ : β * (y₂ / y₁.gcd y₂) < N * (y₁ / y₁.gcd y₂))
    (hclose₁₃ : β * (y₃ / y₁.gcd y₃) < N * (y₁ / y₁.gcd y₃))
    (hclose₂₃ : β * (y₃ / y₂.gcd y₃) < N * (y₂ / y₂.gcd y₃)) :
    False := by
  let a := y₁.gcd y₂
  let b := y₁.gcd y₃
  let c := y₂.gcd y₃
  let δ := N - β
  have ha : 0 < a := Nat.gcd_pos_of_pos_left y₂ hy₁
  have hb : 0 < b := Nat.gcd_pos_of_pos_left y₃ hy₁
  have hc : 0 < c := Nat.gcd_pos_of_pos_left y₃ hy₂
  have hδ : 0 < δ := Nat.sub_pos_of_lt hβN
  have hdiff₁₂ : y₂ / a = y₁ / a + 1 := by
    exact reduced_divisors_diff_eq_one hβ hβN.le hy₁ hy₂ h₁₂
      hy₁β hy₂β hgap hclose₁₂
  have hdiff₁₃ : y₃ / b = y₁ / b + 1 := by
    exact reduced_divisors_diff_eq_one hβ hβN.le hy₁ hy₃ (h₁₂.trans h₂₃)
      hy₁β hy₃β hgap hclose₁₃
  have hdiff₂₃ : y₃ / c = y₂ / c + 1 := by
    exact reduced_divisors_diff_eq_one hβ hβN.le hy₂ hy₃ h₂₃
      hy₂β hy₃β hgap hclose₂₃
  have hy₂eq : y₂ = y₁ + a := by
    calc
      y₂ = (y₂ / a) * a := (Nat.div_mul_cancel (Nat.gcd_dvd_right y₁ y₂)).symm
      _ = (y₁ / a + 1) * a := by rw [hdiff₁₂]
      _ = y₁ + a := by rw [add_mul, Nat.div_mul_cancel (Nat.gcd_dvd_left y₁ y₂)]; simp
  have hy₃eq₁ : y₃ = y₁ + b := by
    calc
      y₃ = (y₃ / b) * b := (Nat.div_mul_cancel (Nat.gcd_dvd_right y₁ y₃)).symm
      _ = (y₁ / b + 1) * b := by rw [hdiff₁₃]
      _ = y₁ + b := by rw [add_mul, Nat.div_mul_cancel (Nat.gcd_dvd_left y₁ y₃)]; simp
  have hy₃eq₂ : y₃ = y₂ + c := by
    calc
      y₃ = (y₃ / c) * c := (Nat.div_mul_cancel (Nat.gcd_dvd_right y₂ y₃)).symm
      _ = (y₂ / c + 1) * c := by rw [hdiff₂₃]
      _ = y₂ + c := by rw [add_mul, Nat.div_mul_cancel (Nat.gcd_dvd_left y₂ y₃)]; simp
  have habc : a + c = b := by omega
  have hNsplit : δ + β = N := Nat.sub_add_cancel hβN.le
  have hβb : β * b < δ * y₁ := by
    have hbase : β < δ * (y₁ / b) := by
      change β * (y₃ / b) < N * (y₁ / b) at hclose₁₃
      rw [hdiff₁₃] at hclose₁₃
      rw [← hNsplit, add_mul, mul_add] at hclose₁₃
      omega
    have hm := (Nat.mul_lt_mul_right hb).mpr hbase
    calc
      β * b < (δ * (y₁ / b)) * b := hm
      _ = δ * ((y₁ / b) * b) := by rw [mul_assoc]
      _ = δ * y₁ := by rw [Nat.div_mul_cancel (Nat.gcd_dvd_left y₁ y₃)]
  have hNb : N * b < δ * y₃ := by
    calc
      N * b = (β + δ) * b := by rw [add_comm, hNsplit]
      _ = β * b + δ * b := by rw [add_mul]
      _ < δ * y₁ + δ * b := Nat.add_lt_add_right hβb _
      _ = δ * y₃ := by rw [hy₃eq₁, mul_add]
  have hNbmid : N * b < δ * y₂ + δ * c := by
    simpa only [hy₃eq₂, mul_add] using hNb
  have hprodDvd : y₁ * y₂ * y₃ ∣ β * a * b * c := by
    exact triple_product_dvd_mul_pairwise_gcds hβ hy₁ hy₂ hy₃
      hy₁β hy₂β hy₃β hgcd
  have hprodLe : y₁ * y₂ * y₃ ≤ β * a * b * c :=
    Nat.le_of_dvd (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hβ ha) hb) hc) hprodDvd
  let P := (β * b) * (N * b)
  have hP : 0 < P := by positivity
  have hpair : P < (δ * y₁) * (δ * y₃) := by
    exact mul_lt_mul hβb hNb.le (Nat.mul_pos (by omega) hb)
      (Nat.zero_le (δ * y₁))
  have hpairY₂ : P * (δ * y₂) <
      ((δ * y₁) * (δ * y₃)) * (δ * y₂) := by
    exact (Nat.mul_lt_mul_right (Nat.mul_pos hδ hy₂)).mpr hpair
  have hlarge : P * (N * b) <
      (δ * δ * δ) * (y₁ * y₂ * y₃) + P * (δ * c) := by
    calc
      P * (N * b) < P * (δ * y₂ + δ * c) :=
        (Nat.mul_lt_mul_left hP).mpr hNbmid
      _ = P * (δ * y₂) + P * (δ * c) := by rw [mul_add]
      _ < ((δ * y₁) * (δ * y₃)) * (δ * y₂) + P * (δ * c) :=
        Nat.add_lt_add_right hpairY₂ _
      _ = (δ * δ * δ) * (y₁ * y₂ * y₃) + P * (δ * c) := by
        simp only [mul_assoc, mul_comm, mul_left_comm]
  have hlarge' : P * (N * b) <
      (δ * δ * δ) * (β * a * b * c) + P * (δ * c) :=
    hlarge.trans_le (Nat.add_le_add_right
      (Nat.mul_le_mul_left (δ * δ * δ) hprodLe) _)
  have hmain : (b * N) * (b * N) <
      (a * c * δ) * (δ * δ) + (b * N) * (c * δ) := by
    apply (Nat.mul_lt_mul_left (Nat.mul_pos hβ hb)).mp
    calc
      (β * b) * ((b * N) * (b * N)) = P * (N * b) := by
        simp only [P]
        ring
      _ < (δ * δ * δ) * (β * a * b * c) + P * (δ * c) := hlarge'
      _ = (β * b) *
          ((a * c * δ) * (δ * δ) + (b * N) * (c * δ)) := by
        simp only [P]
        ring
  exact spacing_polynomial_contradiction hN hδ ha hc habc hgap hmain

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma exists_increasing_permutation {x y z : ℕ}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∃ a b c, a < b ∧ b < c ∧ ({a, b, c} : Finset ℕ) = {x, y, z} := by
  by_cases h₁ : x < y
  · by_cases h₂ : y < z
    · exact ⟨x, y, z, h₁, h₂, rfl⟩
    · by_cases h₃ : x < z
      · refine ⟨x, z, y, h₃, by omega, ?_⟩
        ext w
        simp only [Finset.mem_insert, Finset.mem_singleton]
        tauto
      · refine ⟨z, x, y, by omega, h₁, ?_⟩
        ext w
        simp only [Finset.mem_insert, Finset.mem_singleton]
        tauto
  · by_cases h₂ : x < z
    · refine ⟨y, x, z, by omega, h₂, ?_⟩
      ext w
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    · by_cases h₃ : y < z
      · refine ⟨y, z, x, h₃, by omega, ?_⟩
        ext w
        simp only [Finset.mem_insert, Finset.mem_singleton]
        tauto
      · refine ⟨z, y, x, by omega, by omega, ?_⟩
        ext w
        simp only [Finset.mem_insert, Finset.mem_singleton]
        tauto

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma representationCount_le_two_of_gaps (A : Finset ℕ)
    (hbad : ¬ GrahamBound A) {p α : ℕ} (hp : p.Prime)
    (hN : 10 ≤ A.card) (hα : 0 < α) (hαN : α ≤ A.card)
    (hαp : α < p) (hβN : p - α < A.card)
    (hsq : A.card * A.card < 2 * (α * α))
    (hgapα : (A.card - α) * (A.card - α) < α)
    (hgapβ : (A.card - (p - α)) * (A.card - (p - α)) ≤ 4 * A.card) :
    representationCount A p α ≤ 2 := by
  classical
  let β := p - α
  let R := representedMultipliers A α β
  have hβ : 0 < β := Nat.sub_pos_of_lt hαp
  have hαβ : α.Coprime β := coprime_prime_sub hp hα hαp
  change R.card ≤ 2
  by_contra hcard
  have hthree : 2 < R.card := by omega
  obtain ⟨x, hxR, y, hyR, z, hzR, hxy, hxz, hyz⟩ :=
    Finset.two_lt_card.mp hthree
  obtain ⟨e₁, e₂, e₃, he₁₂, he₂₃, hperm⟩ :=
    exists_increasing_permutation hxy hxz hyz
  have hsub : ({e₁, e₂, e₃} : Finset ℕ) ⊆ R := by
    rw [hperm]
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨hxR, hyR, hzR⟩
  have he₁R : e₁ ∈ R := hsub (by simp)
  have he₂R : e₂ ∈ R := hsub (by simp)
  have he₃R : e₃ ∈ R := hsub (by simp)
  have he₁data := (mem_representedMultipliers hα).mp he₁R
  have he₂data := (mem_representedMultipliers hα).mp he₂R
  have he₃data := (mem_representedMultipliers hα).mp he₃R
  let S : Finset ℕ := {e₁, e₂, e₃}
  let c := S.gcd id
  have hS₀ : 0 ∉ S := by
    simp only [S, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨he₁data.1.ne, he₂data.1.ne, he₃data.1.ne⟩
  have hSne : S.Nonempty := ⟨e₁, by simp [S]⟩
  have hc : 0 < c := gcd_pos S hS₀ hSne
  have he₁S : e₁ ∈ S := by simp [S]
  have he₂S : e₂ ∈ S := by simp [S]
  have he₃S : e₃ ∈ S := by simp [S]
  have hce₁ : c ∣ e₁ := Finset.gcd_dvd he₁S
  have hce₂ : c ∣ e₂ := Finset.gcd_dvd he₂S
  have hce₃ : c ∣ e₃ := Finset.gcd_dvd he₃S
  let d₁ := e₁ / c
  let d₂ := e₂ / c
  let d₃ := e₃ / c
  have hd₁ : 0 < d₁ := Nat.div_pos (Nat.le_of_dvd he₁data.1 hce₁) hc
  have hd₂ : 0 < d₂ := Nat.div_pos (Nat.le_of_dvd he₂data.1 hce₂) hc
  have hd₃ : 0 < d₃ := Nat.div_pos (Nat.le_of_dvd he₃data.1 hce₃) hc
  have hd₁₂ : d₁ < d₂ :=
    (Nat.div_lt_div_right hc.ne' hce₁ hce₂).mpr he₁₂
  have hd₂₃ : d₂ < d₃ :=
    (Nat.div_lt_div_right hc.ne' hce₂ hce₃).mpr he₂₃
  have hd₁c : d₁ * c = e₁ := Nat.div_mul_cancel hce₁
  have hd₂c : d₂ * c = e₂ := Nat.div_mul_cancel hce₂
  have hd₃c : d₃ * c = e₃ := Nat.div_mul_cancel hce₃
  have hRne : R.Nonempty := ⟨e₁, he₁R⟩
  have hRgcd_c : R.gcd id ∣ c := by
    apply Finset.dvd_gcd
    intro e heS
    exact Finset.gcd_dvd (hsub heS)
  have hdvd : ∀ i ∈ ({d₁, d₂, d₃} : Finset ℕ), i ∣ α * β := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · exact (Nat.div_dvd_div_left hce₁ hRgcd_c).trans
        (normalize_represented_dvd_product A hbad hα hβ hαβ hsq hRne
          (e₁ / R.gcd id) (normalize_mem R he₁R))
    · exact (Nat.div_dvd_div_left hce₂ hRgcd_c).trans
        (normalize_represented_dvd_product A hbad hα hβ hαβ hsq hRne
          (e₂ / R.gcd id) (normalize_mem R he₂R))
    · exact (Nat.div_dvd_div_left hce₃ hRgcd_c).trans
        (normalize_represented_dvd_product A hbad hα hβ hαβ hsq hRne
          (e₃ / R.gcd id) (normalize_mem R he₃R))
  have hfac : ∀ i ∈ ({d₁, d₂, d₃} : Finset ℕ),
      i = i.gcd α * i.gcd β := by
    intro i hi
    exact ((Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime hαβ).mpr
      (hdvd i hi)).symm
  have hfac₁ := hfac d₁ (by simp)
  have hfac₂ := hfac d₂ (by simp)
  have hfac₃ := hfac d₃ (by simp)
  have hmemα₁ : α * d₁ * c ∈ A := by rw [mul_assoc, hd₁c]; exact he₁data.2.1
  have hmemβ₁ : β * d₁ * c ∈ A := by rw [mul_assoc, hd₁c]; exact he₁data.2.2
  have hmemα₂ : α * d₂ * c ∈ A := by rw [mul_assoc, hd₂c]; exact he₂data.2.1
  have hmemβ₂ : β * d₂ * c ∈ A := by rw [mul_assoc, hd₂c]; exact he₂data.2.2
  have hmemα₃ : α * d₃ * c ∈ A := by rw [mul_assoc, hd₃c]; exact he₃data.2.1
  have hmemβ₃ : β * d₃ * c ∈ A := by rw [mul_assoc, hd₃c]; exact he₃data.2.2
  have hclose₁₂ := scaled_component_closeness A hbad hα hβ hd₁ hd₂ hc
    hαβ hsq hfac₁ hfac₂ hmemα₁ hmemβ₁ hmemα₂ hmemβ₂
  have hclose₁₃ := scaled_component_closeness A hbad hα hβ hd₁ hd₃ hc
    hαβ hsq hfac₁ hfac₃ hmemα₁ hmemβ₁ hmemα₃ hmemβ₃
  have hclose₂₃ := scaled_component_closeness A hbad hα hβ hd₂ hd₃ hc
    hαβ hsq hfac₂ hfac₃ hmemα₂ hmemβ₂ hmemα₃ hmemβ₃
  have hX₁₂ : d₁.gcd α = d₂.gcd α :=
    component_eq_of_gap_square_lt hα hαN
      (Nat.gcd_pos_of_pos_left α hd₁) (Nat.gcd_pos_of_pos_left α hd₂)
      (Nat.gcd_dvd_right d₁ α) (Nat.gcd_dvd_right d₂ α)
      hgapα hclose₁₂.1 hclose₁₂.2.1
  have hX₁₃ : d₁.gcd α = d₃.gcd α :=
    component_eq_of_gap_square_lt hα hαN
      (Nat.gcd_pos_of_pos_left α hd₁) (Nat.gcd_pos_of_pos_left α hd₃)
      (Nat.gcd_dvd_right d₁ α) (Nat.gcd_dvd_right d₃ α)
      hgapα hclose₁₃.1 hclose₁₃.2.1
  have hgcdNorm : d₁.gcd (d₂.gcd d₃) = 1 := by
    have hg := Finset.gcd_div_id_eq_one he₁S he₁data.1.ne'
    change S.gcd (fun e ↦ e / S.gcd id) = 1 at hg
    simpa only [S, c, d₁, d₂, d₃, Finset.gcd_insert,
      Finset.gcd_singleton, id_eq, normalize_eq, gcd_eq_nat_gcd] using hg
  have hXone : d₁.gcd α = 1 := by
    apply Nat.dvd_one.mp
    rw [← hgcdNorm]
    apply Nat.dvd_gcd (Nat.gcd_dvd_left d₁ α)
    apply Nat.dvd_gcd
    · rw [hX₁₂]
      exact Nat.gcd_dvd_left d₂ α
    · rw [hX₁₃]
      exact Nat.gcd_dvd_left d₃ α
  have hX₂one : d₂.gcd α = 1 := hX₁₂.symm.trans hXone
  have hX₃one : d₃.gcd α = 1 := hX₁₃.symm.trans hXone
  have hY₁ : d₁.gcd β = d₁ := by simpa [hXone] using hfac₁.symm
  have hY₂ : d₂.gcd β = d₂ := by simpa [hX₂one] using hfac₂.symm
  have hY₃ : d₃.gcd β = d₃ := by simpa [hX₃one] using hfac₃.symm
  have hd₁β : d₁ ∣ β := hY₁ ▸ Nat.gcd_dvd_right d₁ β
  have hd₂β : d₂ ∣ β := hY₂ ▸ Nat.gcd_dvd_right d₂ β
  have hd₃β : d₃ ∣ β := hY₃ ▸ Nat.gcd_dvd_right d₃ β
  apply no_three_close_divisors hN hβ hβN hd₁ hd₂ hd₃ hd₁₂ hd₂₃
    hd₁β hd₂β hd₃β hgcdNorm hgapβ
  · simpa only [hY₁, hY₂] using hclose₁₂.2.2.2
  · simpa only [hY₁, hY₃] using hclose₁₃.2.2.2
  · simpa only [hY₂, hY₃] using hclose₂₃.2.2.2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma representationCount_le_two_of_window (A : Finset ℕ)
    (hbad : ¬ GrahamBound A) {p α : ℕ} (hp : p.Prime)
    (hN : 10 ≤ A.card) (hpupper : p ≤ 2 * A.card)
    (hpwindow : (2 * A.card - p) * (2 * A.card - p) ≤ 4 * A.card)
    (hαJ : α ∈ Finset.Icc ((p + 1) / 2) A.card) :
    representationCount A p α ≤ 2 := by
  let N := A.card
  let t := 2 * N - p
  obtain ⟨hαlower, hαN⟩ := Finset.mem_Icc.mp hαJ
  have htadd : t + p = 2 * N := Nat.sub_add_cancel hpupper
  have hpN : N < p := by
    nlinarith [sq_nonneg ((t : ℤ) - N)]
  have hpne : p ≠ 2 := by omega
  obtain ⟨k, hk⟩ := hp.odd_of_ne_two hpne
  have hp2α : p < 2 * α := by
    omega
  have hα : 0 < α := by omega
  have hαp : α < p := hαN.trans_lt hpN
  have hβN : p - α < N := by omega
  have hδadd : N - α + α = N := Nat.sub_add_cancel hαN
  have h2δ : 2 * (N - α) < t := by omega
  have hgapα : (N - α) * (N - α) < α := by
    nlinarith
  have hsq : N * N < 2 * (α * α) := by
    nlinarith [sq_nonneg ((N : ℤ) - 3 * (N - α))]
  have hδβle : N - (p - α) ≤ t := by omega
  have hgapβ : (N - (p - α)) * (N - (p - α)) ≤ 4 * N := by
    exact (Nat.mul_self_le_mul_self hδβle).trans hpwindow
  apply representationCount_le_two_of_gaps A hbad hp hN hα hαN hαp hβN
  · simpa only [N] using hsq
  · simpa only [N] using hgapα
  · simpa only [N] using hgapβ

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private def primeFold (p q : ℕ) : ℕ := max q (p - q)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma primeFold_injective_on_odd_primes {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hp2 : 2 < p) (hq2 : 2 < q) (hr2 : 2 < r)
    (hqp : q ≤ p) (hrp : r ≤ p)
    (hfold : primeFold p q = primeFold p r) : q = r := by
  have hor : q = r ∨ q + r = p := by
    dsimp only [primeFold] at hfold
    by_cases hqside : q ≤ p - q
    · rw [max_eq_right hqside] at hfold
      by_cases hrside : r ≤ p - r
      · rw [max_eq_right hrside] at hfold
        left
        omega
      · rw [max_eq_left (Nat.le_of_lt (Nat.lt_of_not_ge hrside))] at hfold
        right
        omega
    · rw [max_eq_left (Nat.le_of_lt (Nat.lt_of_not_ge hqside))] at hfold
      by_cases hrside : r ≤ p - r
      · rw [max_eq_right hrside] at hfold
        right
        omega
      · rw [max_eq_left (Nat.le_of_lt (Nat.lt_of_not_ge hrside))] at hfold
        left
        exact hfold
  rcases hor with h | hsum
  · exact h
  · obtain ⟨kp, hkp⟩ := hp.odd_of_ne_two (by omega)
    obtain ⟨kq, hkq⟩ := hq.odd_of_ne_two (by omega)
    obtain ⟨kr, hkr⟩ := hr.odd_of_ne_two (by omega)
    omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma primeFold_mem_J {N p q : ℕ} (hpN : N < p) (hpupper : p ≤ 2 * N)
    (hq : q ∈ Finset.Icc (p - N) N) :
    primeFold p q ∈ Finset.Icc ((p + 1) / 2) N := by
  obtain ⟨hqlower, hqupper⟩ := Finset.mem_Icc.mp hq
  have hqp : q ≤ p := hqupper.trans hpN.le
  have hsubupper : p - q ≤ N := by omega
  apply Finset.mem_Icc.mpr
  constructor
  · dsimp only [primeFold]
    omega
  · exact max_le hqupper hsubupper

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma representationCount_primeFold_eq_zero (A : Finset ℕ)
    (h₀ : 0 ∉ A) (hgcd : A.gcd id = 1) (hbad : ¬ GrahamBound A)
    {p q : ℕ} (hq : q.Prime) (hqp : q ≤ p)
    (hlarge : A.card ≤ 2 * q) :
    representationCount A p (primeFold p q) = 0 := by
  rw [representationCount, Finset.card_eq_zero]
  apply Finset.not_nonempty_iff_eq_empty.mp
  rintro ⟨d, hd⟩
  have hαpos : 0 < primeFold p q :=
    lt_max_of_lt_left hq.pos
  have hdata := (mem_representedMultipliers hαpos).mp hd
  by_cases hside : q ≤ p - q
  · have hfold : primeFold p q = p - q := max_eq_right hside
    have hcomp : p - primeFold p q = q := by rw [hfold]; omega
    have hmem : q * d ∈ A := by simpa only [hcomp] using hdata.2.2
    exact (prime_not_dvd_of_card_le_two_mul A h₀ hgcd hbad hq hlarge hmem)
      (dvd_mul_right q d)
  · have hfold : primeFold p q = q :=
      max_eq_left (Nat.le_of_lt (Nat.lt_of_not_ge hside))
    have hmem : q * d ∈ A := by simpa only [hfold] using hdata.2.1
    exact (prime_not_dvd_of_card_le_two_mul A h₀ hgcd hbad hq hlarge hmem)
      (dvd_mul_right q d)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma primeInterval_card_le_zeroFibers (A : Finset ℕ)
    (h₀ : 0 ∉ A) (hgcd : A.gcd id = 1) (hbad : ¬ GrahamBound A)
    {p : ℕ} (hp : p.Prime) (hpN : A.card < p) (hpupper : p < 2 * A.card)
    (hlower : ∀ q ∈ (Finset.Icc (p - A.card) A.card).filter Nat.Prime,
      A.card ≤ 2 * q)
    (hq2 : ∀ q ∈ (Finset.Icc (p - A.card) A.card).filter Nat.Prime,
      2 < q) :
    ((Finset.Icc (p - A.card) A.card).filter Nat.Prime).card ≤
      ((Finset.Icc ((p + 1) / 2) A.card).filter fun α ↦
        representationCount A p α = 0).card := by
  classical
  let Q := (Finset.Icc (p - A.card) A.card).filter Nat.Prime
  let Z := (Finset.Icc ((p + 1) / 2) A.card).filter fun α ↦
    representationCount A p α = 0
  apply Finset.card_le_card_of_injOn (primeFold p)
  · intro q hqQ
    have hqI := (Finset.mem_filter.mp hqQ).1
    have hqprime := (Finset.mem_filter.mp hqQ).2
    apply Finset.mem_filter.mpr
    refine ⟨primeFold_mem_J hpN hpupper.le hqI, ?_⟩
    exact representationCount_primeFold_eq_zero A h₀ hgcd hbad hqprime
      ((Finset.mem_Icc.mp hqI).2.trans hpN.le) (hlower q hqQ)
  · intro q hqQ r hrQ hfold
    have hqI := (Finset.mem_filter.mp hqQ).1
    have hrI := (Finset.mem_filter.mp hrQ).1
    exact primeFold_injective_on_odd_primes hp
      (Finset.mem_filter.mp hqQ).2 (Finset.mem_filter.mp hrQ).2
      (by omega) (hq2 q hqQ) (hq2 r hrQ)
      ((Finset.mem_Icc.mp hqI).2.trans hpN.le)
      ((Finset.mem_Icc.mp hrI).2.trans hpN.le) hfold

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma grahamBound_of_collision_support_lt_primeInterval (A : Finset ℕ)
    (h₀ : 0 ∉ A) (hgcd : A.gcd id = 1) {p : ℕ} (hp : p.Prime)
    (hN : 10 ≤ A.card) (hpN : A.card < p) (hpupper : p < 2 * A.card)
    (hpwindow : (2 * A.card - p) * (2 * A.card - p) ≤ 4 * A.card)
    (hlower : ∀ q ∈ (Finset.Icc (p - A.card) A.card).filter Nat.Prime,
      A.card ≤ 2 * q)
    (hq2 : ∀ q ∈ (Finset.Icc (p - A.card) A.card).filter Nat.Prime,
      2 < q)
    (hsupport : ((Finset.Icc ((p + 1) / 2) A.card).filter fun α ↦
        2 ≤ representationCount A p α).card <
      ((Finset.Icc (p - A.card) A.card).filter Nat.Prime).card) :
    GrahamBound A := by
  by_contra hbad
  let J := Finset.Icc ((p + 1) / 2) A.card
  let M := J.filter fun α ↦ 2 ≤ representationCount A p α
  have hmult : ∀ α ∈ M, representationCount A p α ≤ 2 := by
    intro α hαM
    exact representationCount_le_two_of_window A hbad hp hN hpupper.le hpwindow
      (Finset.mem_filter.mp hαM).1
  have hexcess : M.sum (fun α ↦ representationCount A p α - 1) ≤ M.card := by
    calc
      M.sum (fun α ↦ representationCount A p α - 1) ≤ M.sum (fun _ ↦ 1) := by
        apply Finset.sum_le_sum
        intro α hαM
        have := hmult α hαM
        omega
      _ = M.card := by simp
  have hprimeZero := primeInterval_card_le_zeroFibers A h₀ hgcd hbad hp hpN hpupper
    hlower hq2
  have hzeroExcess := zero_card_le_representation_excess A h₀ hgcd hbad hp hpN hpupper
  change M.card < _ at hsupport
  change _ ≤ (J.filter fun α ↦ 2 ≤ representationCount A p α).sum
    (fun α ↦ representationCount A p α - 1) at hzeroExcess
  change M.sum (fun α ↦ representationCount A p α - 1) ≤ M.card at hexcess
  exact (not_lt_of_ge (hprimeZero.trans (hzeroExcess.trans hexcess))) hsupport

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma square_lt_twice_of_gap {N α : ℕ} (hN : 10 ≤ N)
    (hα : 0 < α) (hαN : α ≤ N) (hgap : (N - α) * (N - α) < α) :
    N * N < 2 * (α * α) := by
  have hδadd : N - α + α = N := Nat.sub_add_cancel hαN
  nlinarith [sq_nonneg ((N : ℤ) - 3 * (N - α))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma collision_fiber_shape (A : Finset ℕ)
    (hbad : ¬ GrahamBound A) {p α j : ℕ} (hp : p.Prime)
    (hN : 10 ≤ A.card) (hj : j ≤ 3) (hpupper : p ≤ 2 * A.card)
    (hpwindow : (2 * A.card - p) * (2 * A.card - p) ≤ (j + 1) * A.card)
    (hαJ : α ∈ Finset.Icc ((p + 1) / 2) A.card)
    (hr : 2 ≤ representationCount A p α) :
    ∃ ell Y : ℕ, 1 ≤ ell ∧ 1 ≤ Y ∧ ell ≤ j ∧
      p - α = ell * Y * (Y + 1) := by
  classical
  let N := A.card
  let β := p - α
  let t := 2 * N - p
  obtain ⟨hαlower, hαN⟩ := Finset.mem_Icc.mp hαJ
  have hwindow4 : t * t ≤ 4 * N := by
    exact hpwindow.trans (Nat.mul_le_mul_right N (by omega))
  have htadd : t + p = 2 * N := Nat.sub_add_cancel hpupper
  have hpN : N < p := by
    nlinarith [sq_nonneg ((t : ℤ) - N)]
  have hpne : p ≠ 2 := by omega
  obtain ⟨k, hk⟩ := hp.odd_of_ne_two hpne
  have hp2α : p < 2 * α := by omega
  have hα : 0 < α := by omega
  have hαp : α < p := hαN.trans_lt hpN
  have hβ : 0 < β := Nat.sub_pos_of_lt hαp
  have hβN : β < N := by omega
  have hαβ : α.Coprime β := coprime_prime_sub hp hα hαp
  have hδadd : N - α + α = N := Nat.sub_add_cancel hαN
  have h2δ : 2 * (N - α) < t := by omega
  have hgapα : (N - α) * (N - α) < α := by nlinarith
  have hsq : N * N < 2 * (α * α) := by
    exact square_lt_twice_of_gap hN hα hαN hgapα
  have hgapβ : (N - β) * (N - β) ≤ 4 * N := by
    have hle : N - β ≤ t := by omega
    exact (Nat.mul_self_le_mul_self hle).trans hwindow4
  let R := representedMultipliers A α β
  change 2 ≤ R.card at hr
  have hRtwo : 1 < R.card := hr
  obtain ⟨x, hxR, y, hyR, hxy⟩ := Finset.one_lt_card.mp hRtwo
  have hxdata := (mem_representedMultipliers hα).mp hxR
  have hydata := (mem_representedMultipliers hα).mp hyR
  let e₁ := min x y
  let e₂ := max x y
  have he₁R : e₁ ∈ R := by
    change min x y ∈ R
    rcases min_choice x y with h | h <;> rw [h]
    · exact hxR
    · exact hyR
  have he₂R : e₂ ∈ R := by
    change max x y ∈ R
    rcases max_choice x y with h | h <;> rw [h]
    · exact hxR
    · exact hyR
  have he₁data := (mem_representedMultipliers hα).mp he₁R
  have he₂data := (mem_representedMultipliers hα).mp he₂R
  have he₁₂ : e₁ < e₂ := by
    dsimp only [e₁, e₂]
    omega
  let c := e₁.gcd e₂
  let d₁ := e₁ / c
  let d₂ := e₂ / c
  have hc : 0 < c := Nat.gcd_pos_of_pos_left e₂ he₁data.1
  have hd₁ : 0 < d₁ := Nat.div_pos (Nat.gcd_le_left e₂ he₁data.1) hc
  have hd₂ : 0 < d₂ := Nat.div_pos (Nat.gcd_le_right e₁ he₂data.1) hc
  have hd₁₂ : d₁ < d₂ :=
    (Nat.div_lt_div_right hc.ne' (Nat.gcd_dvd_left e₁ e₂)
      (Nat.gcd_dvd_right e₁ e₂)).mpr he₁₂
  have hcop : d₁.Coprime d₂ := Nat.coprime_div_gcd_div_gcd hc
  have hd₁c : d₁ * c = e₁ := Nat.div_mul_cancel (Nat.gcd_dvd_left e₁ e₂)
  have hd₂c : d₂ * c = e₂ := Nat.div_mul_cancel (Nat.gcd_dvd_right e₁ e₂)
  have hmemα₁ : α * d₁ * c ∈ A := by rw [mul_assoc, hd₁c]; exact he₁data.2.1
  have hmemβ₁ : β * d₁ * c ∈ A := by rw [mul_assoc, hd₁c]; exact he₁data.2.2
  have hmemα₂ : α * d₂ * c ∈ A := by rw [mul_assoc, hd₂c]; exact he₂data.2.1
  have hmemβ₂ : β * d₂ * c ∈ A := by rw [mul_assoc, hd₂c]; exact he₂data.2.2
  have hfac := factor_closeness_of_counterexample A hbad hα hβ hd₁ hd₂ hc
    hαβ hcop hsq hmemα₁ hmemβ₁ hmemα₂ hmemβ₂
  have hXcop : (d₁.gcd α).Coprime (d₂.gcd α) :=
    (hcop.of_dvd_left (Nat.gcd_dvd_left d₁ α)).of_dvd_right
      (Nat.gcd_dvd_left d₂ α)
  have hXeq : d₁.gcd α = d₂.gcd α :=
    component_eq_of_gap_square_lt hα hαN
      (Nat.gcd_pos_of_pos_left α hd₁) (Nat.gcd_pos_of_pos_left α hd₂)
      (Nat.gcd_dvd_right d₁ α) (Nat.gcd_dvd_right d₂ α)
      hgapα
      (by simpa only [hXcop.gcd_eq_one, Nat.div_one] using hfac.2.2.1)
      (by simpa only [hXcop.gcd_eq_one, Nat.div_one] using hfac.2.2.2.1)
  have hXone : d₁.gcd α = 1 := by
    apply Nat.dvd_one.mp
    rw [← hcop.gcd_eq_one]
    apply Nat.dvd_gcd (Nat.gcd_dvd_left d₁ α)
    rw [hXeq]
    exact Nat.gcd_dvd_left d₂ α
  have hX₂one : d₂.gcd α = 1 := hXeq.symm.trans hXone
  have hY₁ : d₁.gcd β = d₁ := by simpa [hXone] using hfac.1.symm
  have hY₂ : d₂.gcd β = d₂ := by simpa [hX₂one] using hfac.2.1.symm
  have hd₁β : d₁ ∣ β := hY₁ ▸ Nat.gcd_dvd_right d₁ β
  have hd₂β : d₂ ∣ β := hY₂ ▸ Nat.gcd_dvd_right d₂ β
  have hdiff : d₂ = d₁ + 1 := by
    have h := reduced_divisors_diff_eq_one hβ hβN.le hd₁ hd₂ hd₁₂
      hd₁β hd₂β hgapβ
      (by simpa only [hY₁, hY₂, hcop.gcd_eq_one, Nat.div_one] using
        hfac.2.2.2.2.2)
    simpa only [hcop.gcd_eq_one, Nat.div_one] using h
  have hprodβ : d₁ * d₂ ∣ β := hcop.mul_dvd_of_dvd_of_dvd hd₁β hd₂β
  let ell := β / (d₁ * d₂)
  have hell : 0 < ell := Nat.div_pos (Nat.le_of_dvd hβ hprodβ)
    (Nat.mul_pos hd₁ hd₂)
  have hβeq : β = ell * d₁ * d₂ := by
    rw [← Nat.div_mul_cancel hprodβ]
    dsimp only [ell]
    ac_rfl
  have hcloseβ : β * d₂ < N * d₁ := by
    simpa only [hY₁, hY₂, N] using hfac.2.2.2.2.2
  let δ := N - β
  have hNsplit : δ + β = N := Nat.sub_add_cancel hβN.le
  have hβδ : β < δ * d₁ := by
    rw [hdiff, mul_add, ← hNsplit, add_mul] at hcloseβ
    omega
  have hellδ : ell * d₂ < δ := by
    apply (Nat.mul_lt_mul_right hd₁).mp
    calc
      ell * d₂ * d₁ = β := by rw [hβeq]; ac_rfl
      _ < δ * d₁ := hβδ
  have hδα : 0 < N - α := by
    have halphaClose : α < N := by
      simpa only [hXone, hX₂one, Nat.mul_one, N] using hfac.2.2.1
    exact Nat.sub_pos_of_lt halphaClose
  have htdecomp : t = (N - α) + δ := by omega
  have hellN : ell * N < t * t := by
    have hpart : ell * β < ell * (δ * d₁) := (Nat.mul_lt_mul_left hell).mpr hβδ
    have hδ : 0 < δ := (Nat.mul_pos hell hd₂).trans hellδ
    calc
      ell * N = ell * δ + ell * β := by rw [← hNsplit, mul_add]
      _ < ell * δ + ell * (δ * d₁) := Nat.add_lt_add_left hpart _
      _ = δ * (ell * d₂) := by rw [hdiff]; simp only [Nat.mul_add]; ac_rfl
      _ < δ * δ := (Nat.mul_lt_mul_left hδ).mpr hellδ
      _ < t * t := Nat.mul_self_lt_mul_self (by omega)
  have hellj : ell ≤ j := by
    have : ell * N < (j + 1) * N := hellN.trans_le hpwindow
    exact Nat.lt_succ_iff.mp ((Nat.mul_lt_mul_right (by omega : 0 < N)).mp this)
  refine ⟨ell, d₁, hell, hd₁, hellj, ?_⟩
  simpa only [β, hdiff] using hβeq

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private def collisionShapes (N p j : ℕ) : Finset ℕ :=
  Finset.Icc ((p + 1) / 2) N ∩
    (Finset.Icc 1 j).biUnion fun ell ↦
      (Finset.Icc 1 p.sqrt).image fun Y ↦ p - ell * Y * (Y + 1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma collision_support_subset_shapes (A : Finset ℕ)
    (hbad : ¬ GrahamBound A) {p j : ℕ} (hp : p.Prime)
    (hN : 10 ≤ A.card) (hj : j ≤ 3) (hpupper : p ≤ 2 * A.card)
    (hpwindow : (2 * A.card - p) * (2 * A.card - p) ≤ (j + 1) * A.card) :
    (Finset.Icc ((p + 1) / 2) A.card).filter
        (fun α ↦ 2 ≤ representationCount A p α) ⊆
      collisionShapes A.card p j := by
  intro α hα
  obtain ⟨hαJ, hr⟩ := Finset.mem_filter.mp hα
  obtain ⟨ell, Y, hell, hY, hellj, hshape⟩ :=
    collision_fiber_shape A hbad hp hN hj hpupper hpwindow hαJ hr
  apply Finset.mem_inter.mpr
  refine ⟨hαJ, Finset.mem_biUnion.mpr ⟨ell,
    Finset.mem_Icc.mpr ⟨hell, hellj⟩, ?_⟩⟩
  apply Finset.mem_image.mpr
  refine ⟨Y, Finset.mem_Icc.mpr ⟨hY, ?_⟩, ?_⟩
  · apply Nat.le_sqrt.mpr
    calc
      Y * Y ≤ Y * (ell * (Y + 1)) := Nat.mul_le_mul_left Y
        ((Nat.le_succ Y).trans (Nat.le_mul_of_pos_left (Y + 1) hell))
      _ = ell * Y * (Y + 1) := by ac_rfl
      _ = p - α := hshape.symm
      _ ≤ p := Nat.sub_le p α
  · have hprod : 0 < ell * Y * (Y + 1) := Nat.mul_pos (Nat.mul_pos hell hY) (by omega)
    omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma grahamBound_of_shape_certificate (A : Finset ℕ)
    (h₀ : 0 ∉ A) (hgcd : A.gcd id = 1) {p j : ℕ} (hp : p.Prime)
    (hN : 10 ≤ A.card) (hpN : A.card < p) (hpupper : p < 2 * A.card)
    (hj : j ≤ 3) (hthree : 3 * A.card ≤ 2 * p)
    (hqmin : 3 < p - A.card)
    (hpwindow : (2 * A.card - p) * (2 * A.card - p) ≤ (j + 1) * A.card)
    (hcert : (collisionShapes A.card p j).card <
      ((Finset.Icc (p - A.card) A.card).filter Nat.Prime).card) :
    GrahamBound A := by
  by_contra hbad
  apply hbad
  apply grahamBound_of_collision_support_lt_primeInterval A h₀ hgcd hp hN hpN hpupper
  · exact hpwindow.trans (Nat.mul_le_mul_right A.card (by omega))
  · intro q hq
    have hqlo := (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).1
    omega
  · intro q hq
    have hqlo := (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).1
    omega
  · exact (Finset.card_le_card
      (collision_support_subset_shapes A hbad hp hN hj hpupper.le hpwindow)).trans_lt hcert

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma grahamBound_of_short_prime_pair (A : Finset ℕ)
    (h₀ : 0 ∉ A) (hgcd : A.gcd id = 1) (hN : 10 ≤ A.card)
    {p q : ℕ} (hp : p.Prime) (hpN : A.card < p)
    (hpupper : p < 2 * A.card)
    (hpwindow : (2 * A.card - p) * (2 * A.card - p) ≤ A.card)
    (hq : q.Prime) (hqlower : p - A.card ≤ q) (hqupper : q ≤ A.card) :
    GrahamBound A := by
  apply grahamBound_of_shape_certificate A h₀ hgcd hp hN hpN hpupper
      (j := 0)
  · norm_num
  · have htadd : 2 * A.card - p + p = 2 * A.card :=
      Nat.sub_add_cancel hpupper.le
    have hsplit : p - A.card + (2 * A.card - p) = A.card := by
      omega
    nlinarith
  · have htadd : 2 * A.card - p + p = 2 * A.card :=
      Nat.sub_add_cancel hpupper.le
    have hsplit : p - A.card + (2 * A.card - p) = A.card := by
      omega
    nlinarith
  · simpa using hpwindow
  · have hqmem : q ∈
        (Finset.Icc (p - A.card) A.card).filter Nat.Prime :=
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hqlower, hqupper⟩, hq⟩
    have hprimepos : 0 <
        ((Finset.Icc (p - A.card) A.card).filter Nat.Prime).card :=
      Finset.card_pos.mpr ⟨q, hqmem⟩
    have hshapezero : (collisionShapes A.card p 0).card = 0 := by
      simp [collisionShapes]
    omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private def componentClose (N α β d e : ℕ) : Prop :=
  α * (d.gcd α / (d.gcd α).gcd (e.gcd α)) <
      N * (e.gcd α / (d.gcd α).gcd (e.gcd α)) ∧
  α * (e.gcd α / (d.gcd α).gcd (e.gcd α)) <
      N * (d.gcd α / (d.gcd α).gcd (e.gcd α)) ∧
  β * (d.gcd β / (d.gcd β).gcd (e.gcd β)) <
      N * (e.gcd β / (d.gcd β).gcd (e.gcd β)) ∧
  β * (e.gcd β / (d.gcd β).gcd (e.gcd β)) <
      N * (d.gcd β / (d.gcd β).gcd (e.gcd β))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private def pairConfiguration (N α β d e : ℕ) : Prop :=
  0 < d ∧ d < e ∧
  d = d.gcd α * d.gcd β ∧ e = e.gcd α * e.gcd β ∧
  componentClose N α β d e

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private def tripleConfiguration (N α β d₁ d₂ d₃ : ℕ) : Prop :=
  0 < d₁ ∧ d₁ < d₂ ∧ d₂ < d₃ ∧
  d₁ = d₁.gcd α * d₁.gcd β ∧
  d₂ = d₂.gcd α * d₂.gcd β ∧
  d₃ = d₃.gcd α * d₃.gcd β ∧
  componentClose N α β d₁ d₂ ∧
  componentClose N α β d₁ d₃ ∧
  componentClose N α β d₂ d₃

private instance instDecidablePairConfiguration (N α β d e : ℕ) :
    Decidable (pairConfiguration N α β d e) := by
  unfold pairConfiguration componentClose
  infer_instance

private instance instDecidableTripleConfiguration (N α β d₁ d₂ d₃ : ℕ) :
    Decidable (tripleConfiguration N α β d₁ d₂ d₃) := by
  unfold tripleConfiguration componentClose
  infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private def possiblePair (N α β : ℕ) : Bool :=
  decide (∃ d ∈ Nat.divisors (α*β), ∃ e ∈ Nat.divisors (α*β),
    pairConfiguration N α β d e)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private def possibleTriple (N α β : ℕ) : Bool :=
  decide (∃ d₁ ∈ Nat.divisors (α*β), ∃ d₂ ∈ Nat.divisors (α*β),
    ∃ d₃ ∈ Nat.divisors (α*β), tripleConfiguration N α β d₁ d₂ d₃)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma possiblePair_eq_true {N α β : ℕ} :
    possiblePair N α β = true ↔
      ∃ d ∈ Nat.divisors (α*β), ∃ e ∈ Nat.divisors (α*β),
        pairConfiguration N α β d e := by simp [possiblePair]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma possibleTriple_eq_true {N α β : ℕ} :
    possibleTriple N α β = true ↔
      ∃ d₁ ∈ Nat.divisors (α*β), ∃ d₂ ∈ Nat.divisors (α*β),
        ∃ d₃ ∈ Nat.divisors (α*β), tripleConfiguration N α β d₁ d₂ d₃ := by
  simp [possibleTriple]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private def possiblePairAlphas (N p : ℕ) : Finset ℕ :=
  (Finset.Icc ((p + 1) / 2) N).filter fun α ↦
    possiblePair N α (p - α) = true

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private def possibleTripleAlphas (N p : ℕ) : Finset ℕ :=
  (Finset.Icc ((p + 1) / 2) N).filter fun α ↦
    possibleTriple N α (p - α) = true

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma normalized_multiplier_data (A : Finset ℕ)
    (hbad : ¬ GrahamBound A) {p α d : ℕ} (hp : p.Prime)
    (hα : 0 < α) (hαp : α < p)
    (hsq : A.card * A.card < 2 * (α * α))
    (hR : (representedMultipliers A α (p - α)).Nonempty)
    (hd : d ∈ normalize (representedMultipliers A α (p - α))) :
    0 < d ∧ d ∣ α * (p - α) ∧
      d = d.gcd α * d.gcd (p - α) ∧
      α * d * (representedMultipliers A α (p - α)).gcd id ∈ A ∧
      (p - α) * d * (representedMultipliers A α (p - α)).gcd id ∈ A := by
  let β := p - α
  let R := representedMultipliers A α β
  have hβ : 0 < β := Nat.sub_pos_of_lt hαp
  have hαβ : α.Coprime β := coprime_prime_sub hp hα hαp
  have hR₀ : 0 ∉ R := representedMultipliers_nonzero hα
  have hc : 0 < R.gcd id := gcd_pos R hR₀ hR
  have hdpos : 0 < d := Nat.pos_of_ne_zero fun hz ↦
    normalize_nonzero R hR₀ (hz ▸ hd)
  have hdvd : d ∣ α * β :=
    normalize_represented_dvd_product A hbad hα hβ hαβ hsq hR d hd
  have hfac : d = d.gcd α * d.gcd β :=
    ((Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime hαβ).mpr hdvd).symm
  change d ∈ R.image (fun e ↦ e / R.gcd id) at hd
  obtain ⟨e, heR, rfl⟩ := Finset.mem_image.mp hd
  have hedata := (mem_representedMultipliers hα).mp heR
  have hce : R.gcd id ∣ e := Finset.gcd_dvd heR
  have heq : e / R.gcd id * R.gcd id = e := Nat.div_mul_cancel hce
  refine ⟨hdpos, hdvd, hfac, ?_, ?_⟩
  · change α * (e / R.gcd id) * R.gcd id ∈ A
    rw [mul_assoc, heq]
    exact hedata.2.1
  · change β * (e / R.gcd id) * R.gcd id ∈ A
    rw [mul_assoc, heq]
    exact hedata.2.2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma possiblePair_of_collision (A : Finset ℕ)
    (hbad : ¬ GrahamBound A) {p α : ℕ} (hp : p.Prime)
    (hα : 0 < α) (hαp : α < p)
    (hsq : A.card * A.card < 2 * (α * α))
    (hr : 2 ≤ representationCount A p α) :
    possiblePair A.card α (p - α) = true := by
  classical
  let β := p - α
  let R := representedMultipliers A α β
  let B := normalize R
  change 2 ≤ R.card at hr
  have hR : R.Nonempty := Finset.card_pos.mp (by omega)
  have hR₀ : 0 ∉ R := representedMultipliers_nonzero hα
  have hc : 0 < R.gcd id := gcd_pos R hR₀ hR
  have hBtwo : 1 < B.card := by
    change 1 < (normalize R).card
    rw [normalize_card]
    omega
  obtain ⟨x, hxB, y, hyB, hxy⟩ := Finset.one_lt_card.mp hBtwo
  let d := min x y
  let e := max x y
  have hdB : d ∈ B := by
    change min x y ∈ B
    rcases min_choice x y with h | h <;> rw [h]
    · exact hxB
    · exact hyB
  have heB : e ∈ B := by
    change max x y ∈ B
    rcases max_choice x y with h | h <;> rw [h]
    · exact hxB
    · exact hyB
  have hde : d < e := by dsimp only [d, e]; omega
  have hddata := normalized_multiplier_data A hbad hp hα hαp hsq hR hdB
  have hedata := normalized_multiplier_data A hbad hp hα hαp hsq hR heB
  have hβ : 0 < β := Nat.sub_pos_of_lt hαp
  have hαβ : α.Coprime β := coprime_prime_sub hp hα hαp
  have hclose := scaled_component_closeness A hbad hα hβ hddata.1 hedata.1 hc
    hαβ hsq hddata.2.2.1 hedata.2.2.1
    hddata.2.2.2.1 hddata.2.2.2.2 hedata.2.2.2.1 hedata.2.2.2.2
  rw [possiblePair_eq_true]
  refine ⟨d, Nat.mem_divisors.mpr ⟨hddata.2.1, Nat.mul_ne_zero hα.ne' hβ.ne'⟩,
    e, Nat.mem_divisors.mpr ⟨hedata.2.1, Nat.mul_ne_zero hα.ne' hβ.ne'⟩, ?_⟩
  exact ⟨hddata.1, hde, hddata.2.2.1, hedata.2.2.1, hclose⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma possibleTriple_of_three_representations (A : Finset ℕ)
    (hbad : ¬ GrahamBound A) {p α : ℕ} (hp : p.Prime)
    (hα : 0 < α) (hαp : α < p)
    (hsq : A.card * A.card < 2 * (α * α))
    (hr : 3 ≤ representationCount A p α) :
    possibleTriple A.card α (p - α) = true := by
  classical
  let β := p - α
  let R := representedMultipliers A α β
  let B := normalize R
  change 3 ≤ R.card at hr
  have hR : R.Nonempty := Finset.card_pos.mp (by omega)
  have hR₀ : 0 ∉ R := representedMultipliers_nonzero hα
  have hc : 0 < R.gcd id := gcd_pos R hR₀ hR
  have hBthree : 2 < B.card := by
    change 2 < (normalize R).card
    rw [normalize_card]
    omega
  obtain ⟨x, hxB, y, hyB, z, hzB, hxy, hxz, hyz⟩ :=
    Finset.two_lt_card.mp hBthree
  obtain ⟨d₁, d₂, d₃, hd₁₂, hd₂₃, hperm⟩ :=
    exists_increasing_permutation hxy hxz hyz
  have hsub : ({d₁, d₂, d₃} : Finset ℕ) ⊆ B := by
    rw [hperm]
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨hxB, hyB, hzB⟩
  have hd₁B : d₁ ∈ B := hsub (by simp)
  have hd₂B : d₂ ∈ B := hsub (by simp)
  have hd₃B : d₃ ∈ B := hsub (by simp)
  have hd₁data := normalized_multiplier_data A hbad hp hα hαp hsq hR hd₁B
  have hd₂data := normalized_multiplier_data A hbad hp hα hαp hsq hR hd₂B
  have hd₃data := normalized_multiplier_data A hbad hp hα hαp hsq hR hd₃B
  have hβ : 0 < β := Nat.sub_pos_of_lt hαp
  have hαβ : α.Coprime β := coprime_prime_sub hp hα hαp
  have hclose₁₂ := scaled_component_closeness A hbad hα hβ
    hd₁data.1 hd₂data.1 hc hαβ hsq hd₁data.2.2.1 hd₂data.2.2.1
    hd₁data.2.2.2.1 hd₁data.2.2.2.2 hd₂data.2.2.2.1 hd₂data.2.2.2.2
  have hclose₁₃ := scaled_component_closeness A hbad hα hβ
    hd₁data.1 hd₃data.1 hc hαβ hsq hd₁data.2.2.1 hd₃data.2.2.1
    hd₁data.2.2.2.1 hd₁data.2.2.2.2 hd₃data.2.2.2.1 hd₃data.2.2.2.2
  have hclose₂₃ := scaled_component_closeness A hbad hα hβ
    hd₂data.1 hd₃data.1 hc hαβ hsq hd₂data.2.2.1 hd₃data.2.2.1
    hd₂data.2.2.2.1 hd₂data.2.2.2.2 hd₃data.2.2.2.1 hd₃data.2.2.2.2
  rw [possibleTriple_eq_true]
  refine ⟨d₁, Nat.mem_divisors.mpr
      ⟨hd₁data.2.1, Nat.mul_ne_zero hα.ne' hβ.ne'⟩,
    d₂, Nat.mem_divisors.mpr
      ⟨hd₂data.2.1, Nat.mul_ne_zero hα.ne' hβ.ne'⟩,
    d₃, Nat.mem_divisors.mpr
      ⟨hd₃data.2.1, Nat.mul_ne_zero hα.ne' hβ.ne'⟩, ?_⟩
  exact ⟨hd₁data.1, hd₁₂, hd₂₃,
    hd₁data.2.2.1, hd₂data.2.2.1, hd₃data.2.2.1,
    hclose₁₂, hclose₁₃, hclose₂₃⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma grahamBound_of_configuration_certificate (A : Finset ℕ)
    (h₀ : 0 ∉ A) (hgcd : A.gcd id = 1) {p : ℕ} (hp : p.Prime)
    (hpN : A.card < p) (hpupper : p < 2 * A.card)
    (hthree : 3 * A.card ≤ 2 * p) (hqmin : 3 < p - A.card)
    (hsq : ∀ α ∈ Finset.Icc ((p + 1) / 2) A.card,
      A.card * A.card < 2 * (α * α))
    (hpair : (possiblePairAlphas A.card p).card <
      ((Finset.Icc (p - A.card) A.card).filter Nat.Prime).card)
    (htriple : possibleTripleAlphas A.card p = ∅) :
    GrahamBound A := by
  by_contra hbad
  let J := Finset.Icc ((p + 1) / 2) A.card
  let M := J.filter fun α ↦ 2 ≤ representationCount A p α
  have hmult : ∀ α ∈ M, representationCount A p α ≤ 2 := by
    intro α hαM
    have hαJ := (Finset.mem_filter.mp hαM).1
    by_contra hnot
    have hr : 3 ≤ representationCount A p α := by omega
    have hαpos : 0 < α := by
      have := (Finset.mem_Icc.mp hαJ).1
      omega
    have hαp : α < p := (Finset.mem_Icc.mp hαJ).2.trans_lt hpN
    have hpossible := possibleTriple_of_three_representations A hbad hp
      hαpos hαp (hsq α hαJ) hr
    have hmem : α ∈ possibleTripleAlphas A.card p :=
      Finset.mem_filter.mpr ⟨hαJ, hpossible⟩
    rw [htriple] at hmem
    exact Finset.notMem_empty α hmem
  have hsupport : M.card <
      ((Finset.Icc (p - A.card) A.card).filter Nat.Prime).card := by
    apply (Finset.card_le_card ?_).trans_lt hpair
    intro α hαM
    have hαJ := (Finset.mem_filter.mp hαM).1
    have hr := (Finset.mem_filter.mp hαM).2
    have hαpos : 0 < α := by
      have := (Finset.mem_Icc.mp hαJ).1
      omega
    have hαp : α < p := (Finset.mem_Icc.mp hαJ).2.trans_lt hpN
    apply Finset.mem_filter.mpr
    exact ⟨hαJ, possiblePair_of_collision A hbad hp hαpos hαp (hsq α hαJ) hr⟩
  have hexcess : M.sum (fun α ↦ representationCount A p α - 1) ≤ M.card := by
    calc
      M.sum (fun α ↦ representationCount A p α - 1) ≤ M.sum (fun _ ↦ 1) := by
        apply Finset.sum_le_sum
        intro α hαM
        have := hmult α hαM
        omega
      _ = M.card := by simp
  have hlower : ∀ q ∈ (Finset.Icc (p - A.card) A.card).filter Nat.Prime,
      A.card ≤ 2 * q := by
    intro q hq
    have hqlo := (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).1
    omega
  have hq2 : ∀ q ∈ (Finset.Icc (p - A.card) A.card).filter Nat.Prime,
      2 < q := by
    intro q hq
    have hqlo := (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).1
    omega
  have hprimeZero := primeInterval_card_le_zeroFibers A h₀ hgcd hbad hp hpN hpupper
    hlower hq2
  have hzeroExcess := zero_card_le_representation_excess A h₀ hgcd hbad hp hpN hpupper
  change M.card < _ at hsupport
  change _ ≤ (J.filter fun α ↦ 2 ≤ representationCount A p α).sum
    (fun α ↦ representationCount A p α - 1) at hzeroExcess
  change M.sum (fun α ↦ representationCount A p α - 1) ≤ M.card at hexcess
  exact (not_lt_of_ge (hprimeZero.trans (hzeroExcess.trans hexcess))) hsupport

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma grahamBound_of_card_27 (A : Finset ℕ) (h₀ : 0 ∉ A)
    (hA : A.Nonempty) (hcard : A.card = 27) : GrahamBound A := by
  apply grahamBound_of_normalize A
  let B := normalize A
  have hB₀ : 0 ∉ B := normalize_nonzero A h₀
  have hBgcd : B.gcd id = 1 := normalize_gcd A h₀ hA
  have hBcard : B.card = 27 := (normalize_card A).trans hcard
  apply grahamBound_of_configuration_certificate B hB₀ hBgcd (p := 43)
      (by decide +kernel) (by omega) (by omega) (by omega) (by omega)
  · intro α hα
    have hlo := (Finset.mem_Icc.mp hα).1
    have hs := Nat.mul_self_le_mul_self hlo
    norm_num [hBcard] at hs ⊢
    omega
  · simpa only [hBcard] using (show
      (possiblePairAlphas 27 43).card <
        ((Finset.Icc (43 - 27) 27).filter Nat.Prime).card by decide +kernel)
  · simpa only [hBcard] using (show
      possibleTripleAlphas 27 43 = ∅ by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma grahamBound_of_card_65 (A : Finset ℕ) (h₀ : 0 ∉ A)
    (hA : A.Nonempty) (hcard : A.card = 65) : GrahamBound A := by
  apply grahamBound_of_normalize A
  let B := normalize A
  have hB₀ : 0 ∉ B := normalize_nonzero A h₀
  have hBgcd : B.gcd id = 1 := normalize_gcd A h₀ hA
  have hBcard : B.card = 65 := (normalize_card A).trans hcard
  apply grahamBound_of_configuration_certificate B hB₀ hBgcd (p := 113)
      (by decide +kernel) (by omega) (by omega) (by omega) (by omega)
  · intro α hα
    have hlo := (Finset.mem_Icc.mp hα).1
    have hs := Nat.mul_self_le_mul_self hlo
    norm_num [hBcard] at hs ⊢
    omega
  · simpa only [hBcard] using (show
      (possiblePairAlphas 65 113).card <
        ((Finset.Icc (113 - 65) 65).filter Nat.Prime).card by decide +kernel)
  · simpa only [hBcard] using (show
      possibleTripleAlphas 65 113 = ∅ by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma dvd_lcm_Ico_of_not_grahamBound (A : Finset ℕ) (h₀ : 0 ∉ A)
    (hgcd : A.gcd id = 1) (hbad : ¬ GrahamBound A) {a : ℕ} (ha : a ∈ A) :
    a ∣ (Finset.Ico 1 A.card).lcm id := by
  classical
  have ha0 : a ≠ 0 := fun h ↦ h₀ (h ▸ ha)
  have hquot : ∀ b ∈ A, a / a.gcd b ∈ Finset.Ico 1 A.card := by
    intro b hb
    have hgpos : 0 < a.gcd b := Nat.gcd_pos_of_pos_left b (Nat.pos_of_ne_zero ha0)
    have hqpos : 0 < a / a.gcd b :=
      Nat.div_pos (Nat.gcd_le_left b (Nat.pos_of_ne_zero ha0)) hgpos
    have hlt : a / a.gcd b < A.card := by
      rw [Nat.div_lt_iff_lt_mul hgpos]
      exact Nat.lt_of_not_ge fun hle ↦ hbad ⟨a, ha, b, hb, by simpa [mul_comm] using hle⟩
    exact Finset.mem_Ico.mpr ⟨hqpos, hlt⟩
  have hlcm : A.lcm (fun b ↦ a / a.gcd b) ∣ (Finset.Ico 1 A.card).lcm id :=
    Finset.lcm_dvd fun b hb ↦ Finset.dvd_lcm (hquot b hb)
  rw [lcm_div_gcd_eq a ha0 A, hgcd, Nat.gcd_one_right, Nat.div_one] at hlcm
  exact hlcm

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma grahamBound_of_card_le_four (A : Finset ℕ) (h₀ : 0 ∉ A)
    (hA : A.Nonempty) (hcard : A.card ≤ 4) : GrahamBound A := by
  apply grahamBound_of_normalize A
  by_contra hbad
  let B := normalize A
  change ¬ GrahamBound B at hbad
  have hB₀ : 0 ∉ B := normalize_nonzero A h₀
  have hBgcd : B.gcd id = 1 := normalize_gcd A h₀ hA
  have hBcard : B.card = A.card := normalize_card A
  have hBne : B.Nonempty := by
    apply Finset.card_pos.mp
    rw [hBcard]
    exact Finset.card_pos.mpr hA
  have hdvd : ∀ b ∈ B, b ∣ (Finset.Ico 1 B.card).lcm id :=
    fun b hb ↦ dvd_lcm_Ico_of_not_grahamBound B hB₀ hBgcd hbad hb
  have hBcard_le : B.card ≤ 4 := hBcard.trans_le hcard
  have hBcard_pos : 0 < B.card := Finset.card_pos.mpr hBne
  rcases (show B.card = 1 ∨ B.card = 2 ∨ B.card = 3 ∨ B.card = 4 by omega) with
    h₁ | h₂ | h₃ | h₄
  · obtain ⟨a, ha⟩ := hBne
    apply hbad
    refine ⟨a, ha, a, ha, ?_⟩
    simp [h₁]
  · have hsub : B ⊆ Nat.divisors 1 := by
      intro b hb
      apply Nat.mem_divisors.mpr
      refine ⟨?_, by norm_num⟩
      simpa [h₂] using hdvd b hb
    have hle := Finset.card_le_card hsub
    rw [h₂, Nat.divisors_one, Finset.card_singleton] at hle
    omega
  · have hsub : B ⊆ Nat.divisors 2 := by
      intro b hb
      apply Nat.mem_divisors.mpr
      refine ⟨?_, by norm_num⟩
      have hbdiv := hdvd b hb
      rw [h₃, show (Finset.Ico 1 3).lcm id = 2 by decide +kernel] at hbdiv
      exact hbdiv
    have hle := Finset.card_le_card hsub
    rw [h₃] at hle
    have hdivcard : (Nat.divisors 2).card = 2 := by decide +kernel
    rw [hdivcard] at hle
    omega
  · have hsub : B ⊆ Nat.divisors 6 := by
      intro b hb
      apply Nat.mem_divisors.mpr
      refine ⟨?_, by norm_num⟩
      have hbdiv := hdvd b hb
      rw [h₄, show (Finset.Ico 1 4).lcm id = 6 by decide +kernel] at hbdiv
      exact hbdiv
    have heq : B = Nat.divisors 6 := by
      apply Finset.eq_of_subset_of_card_le hsub
      rw [h₄]
      decide
    have h6 : 6 ∈ B := heq ▸ by norm_num
    have h1 : 1 ∈ B := heq ▸ by norm_num
    apply hbad
    exact ⟨6, h6, 1, h1, by norm_num [h₄]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma grahamBound_of_lcm_certificate (A : Finset ℕ) (h₀ : 0 ∉ A)
    (hA : A.Nonempty) {n L : ℕ} (hcard : A.card = n) (hL₀ : L ≠ 0)
    (hlcm : (Finset.Ico 1 n).lcm id = L)
    (hcert : badSubsets (Nat.divisors L) n = ∅) : GrahamBound A := by
  apply grahamBound_of_normalize A
  by_contra hbad
  let B := normalize A
  change ¬ GrahamBound B at hbad
  have hB₀ : 0 ∉ B := normalize_nonzero A h₀
  have hBgcd : B.gcd id = 1 := normalize_gcd A h₀ hA
  have hBcardA : B.card = A.card := normalize_card A
  have hBcard : B.card = n := hBcardA.trans hcard
  have hsub : B ⊆ Nat.divisors L := by
    intro b hb
    apply Nat.mem_divisors.mpr
    refine ⟨?_, hL₀⟩
    have hdvd := dvd_lcm_Ico_of_not_grahamBound B hB₀ hBgcd hbad hb
    simpa [hBcard, hlcm] using hdvd
  exact hbad (grahamBound_of_badSubsets_eq_empty hcert hsub hBcard)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma grahamBound_of_card_le_seven (A : Finset ℕ) (h₀ : 0 ∉ A)
    (hA : A.Nonempty) (hcard : A.card ≤ 7) : GrahamBound A := by
  by_cases hsmall : A.card ≤ 4
  · exact grahamBound_of_card_le_four A h₀ hA hsmall
  have hpos : 0 < A.card := Finset.card_pos.mpr hA
  rcases (show A.card = 5 ∨ A.card = 6 ∨ A.card = 7 by omega) with h₅ | h₆ | h₇
  · apply grahamBound_of_lcm_certificate A h₀ hA (n := 5) (L := 12) h₅ (by norm_num)
      (by decide +kernel)
    decide +kernel
  · apply grahamBound_of_lcm_certificate A h₀ hA (n := 6) (L := 60) h₆ (by norm_num)
      (by decide +kernel)
    decide +kernel
  · apply grahamBound_of_lcm_certificate A h₀ hA (n := 7) (L := 60) h₇ (by norm_num)
      (by decide +kernel)
    decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma grahamBound_of_card_le_eight (A : Finset ℕ) (h₀ : 0 ∉ A)
    (hA : A.Nonempty) (hcard : A.card ≤ 8) : GrahamBound A := by
  by_cases hsmall : A.card ≤ 7
  · exact grahamBound_of_card_le_seven A h₀ hA hsmall
  have hcard8 : A.card = 8 := by omega
  apply grahamBound_of_normalize A
  by_contra hbad
  let B := normalize A
  change ¬ GrahamBound B at hbad
  have hB₀ : 0 ∉ B := normalize_nonzero A h₀
  have hBgcd : B.gcd id = 1 := normalize_gcd A h₀ hA
  have hBcard : B.card = 8 := (normalize_card A).trans hcard8
  let T := (Nat.divisors 420).filter fun b ↦ ¬5 ∣ b ∧ ¬7 ∣ b
  have hsub : B ⊆ T := by
    intro b hb
    apply Finset.mem_filter.mpr
    refine ⟨Nat.mem_divisors.mpr ⟨?_, by norm_num⟩, ?_, ?_⟩
    · have hdvd := dvd_lcm_Ico_of_not_grahamBound B hB₀ hBgcd hbad hb
      rw [hBcard, show (Finset.Ico 1 8).lcm id = 420 by decide +kernel] at hdvd
      exact hdvd
    · exact prime_not_dvd_of_card_le_two_mul B hB₀ hBgcd hbad
        (q := 5) (by decide +kernel) (by norm_num [hBcard]) hb
    · exact prime_not_dvd_of_card_le_two_mul B hB₀ hBgcd hbad
        (q := 7) (by decide +kernel) (by norm_num [hBcard]) hb
  have hle := Finset.card_le_card hsub
  have hTcard : T.card = 6 := by decide +kernel
  rw [hBcard, hTcard] at hle
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma grahamBound_of_card_le_nine (A : Finset ℕ) (h₀ : 0 ∉ A)
    (hA : A.Nonempty) (hcard : A.card ≤ 9) : GrahamBound A := by
  by_cases hsmall : A.card ≤ 8
  · exact grahamBound_of_card_le_eight A h₀ hA hsmall
  have hcard9 : A.card = 9 := by omega
  apply grahamBound_of_normalize A
  by_contra hbad
  let B := normalize A
  change ¬ GrahamBound B at hbad
  have hB₀ : 0 ∉ B := normalize_nonzero A h₀
  have hBgcd : B.gcd id = 1 := normalize_gcd A h₀ hA
  have hBcard : B.card = 9 := (normalize_card A).trans hcard9
  let T := (Nat.divisors 840).filter fun b ↦ ¬5 ∣ b ∧ ¬7 ∣ b
  have hsub : B ⊆ T := by
    intro b hb
    apply Finset.mem_filter.mpr
    refine ⟨Nat.mem_divisors.mpr ⟨?_, by norm_num⟩, ?_, ?_⟩
    · have hdvd := dvd_lcm_Ico_of_not_grahamBound B hB₀ hBgcd hbad hb
      rw [hBcard, show (Finset.Ico 1 9).lcm id = 840 by decide +kernel] at hdvd
      exact hdvd
    · exact prime_not_dvd_of_card_le_two_mul B hB₀ hBgcd hbad
        (q := 5) (by decide +kernel) (by norm_num [hBcard]) hb
    · exact prime_not_dvd_of_card_le_two_mul B hB₀ hBgcd hbad
        (q := 7) (by decide +kernel) (by norm_num [hBcard]) hb
  have hle := Finset.card_le_card hsub
  have hTcard : T.card = 8 := by decide +kernel
  rw [hBcard, hTcard] at hle
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma grahamBound_of_card_le_ten (A : Finset ℕ) (h₀ : 0 ∉ A)
    (hA : A.Nonempty) (hcard : A.card ≤ 10) : GrahamBound A := by
  by_cases hsmall : A.card ≤ 9
  · exact grahamBound_of_card_le_nine A h₀ hA hsmall
  have hcard10 : A.card = 10 := by omega
  apply grahamBound_of_normalize A
  by_contra hbad
  let B := normalize A
  change ¬ GrahamBound B at hbad
  have hB₀ : 0 ∉ B := normalize_nonzero A h₀
  have hBgcd : B.gcd id = 1 := normalize_gcd A h₀ hA
  have hBcard : B.card = 10 := (normalize_card A).trans hcard10
  let T := (Nat.divisors 2520).filter fun b ↦ ¬5 ∣ b ∧ ¬7 ∣ b
  have hsub : B ⊆ T := by
    intro b hb
    apply Finset.mem_filter.mpr
    refine ⟨Nat.mem_divisors.mpr ⟨?_, by norm_num⟩, ?_, ?_⟩
    · have hdvd := dvd_lcm_Ico_of_not_grahamBound B hB₀ hBgcd hbad hb
      rw [hBcard, show (Finset.Ico 1 10).lcm id = 2520 by decide +kernel] at hdvd
      exact hdvd
    · exact prime_not_dvd_of_card_le_two_mul B hB₀ hBgcd hbad
        (q := 5) (by decide +kernel) (by norm_num [hBcard]) hb
    · exact prime_not_dvd_of_card_le_two_mul B hB₀ hBgcd hbad
        (q := 7) (by decide +kernel) (by norm_num [hBcard]) hb
  have hcert : badSubsets T 10 = ∅ := by decide +kernel
  exact hbad (grahamBound_of_badSubsets_eq_empty hcert hsub hBcard)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma pair_block (lo hi p q : ℕ)
    (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : lo ≤ A.card) (hhi : A.card ≤ hi)
    (hlo10 : 10 ≤ lo := by omega) (hp : p.Prime := by norm_num) (hpN : hi < p := by omega)
    (hupper : p < 2*lo := by omega) (hwin : (2*hi-p)*(2*hi-p) ≤ lo := by omega)
    (hq : q.Prime := by norm_num) (hql : p-lo ≤ q := by omega) (hqu : q ≤ lo := by omega) : GrahamBound A := by
  apply grahamBound_of_short_prime_pair A h0 hg (by omega) hp (by omega) (by omega)
  · have hsub : 2*A.card-p ≤ 2*hi-p := Nat.sub_le_sub_right (by omega) p
    exact (Nat.mul_self_le_mul_self hsub).trans (hwin.trans hlo)
  · exact hq
  · omega
  · omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_2 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 14 ≤ A.card) (hhi : A.card ≤ 14) : GrahamBound A := by
  have hn : A.card = 14 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=23) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_3 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 15 ≤ A.card) (hhi : A.card ≤ 15) : GrahamBound A := by
  have hn : A.card = 15 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=23) (j:=3)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_6 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 18 ≤ A.card) (hhi : A.card ≤ 18) : GrahamBound A := by
  have hn : A.card = 18 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=31) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_8 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 21 ≤ A.card) (hhi : A.card ≤ 21) : GrahamBound A := by
  have hn : A.card = 21 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=37) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_13 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 27 ≤ A.card) (hhi : A.card ≤ 27) : GrahamBound A := by
  exact grahamBound_of_card_27 A h0 (Finset.card_pos.mp (by omega)) (by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_14 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 28 ≤ A.card) (hhi : A.card ≤ 28) : GrahamBound A := by
  have hn : A.card = 28 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=47) (j:=2)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_18 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 34 ≤ A.card) (hhi : A.card ≤ 34) : GrahamBound A := by
  have hn : A.card = 34 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=61) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_19 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 35 ≤ A.card) (hhi : A.card ≤ 35) : GrahamBound A := by
  have hn : A.card = 35 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=61) (j:=2)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_22 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 40 ≤ A.card) (hhi : A.card ≤ 40) : GrahamBound A := by
  have hn : A.card = 40 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=73) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_25 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 45 ≤ A.card) (hhi : A.card ≤ 45) : GrahamBound A := by
  have hn : A.card = 45 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=83) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_27 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 48 ≤ A.card) (hhi : A.card ≤ 48) : GrahamBound A := by
  have hn : A.card = 48 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=89) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_28 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 49 ≤ A.card) (hhi : A.card ≤ 49) : GrahamBound A := by
  have hn : A.card = 49 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=89) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_33 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 61 ≤ A.card) (hhi : A.card ≤ 61) : GrahamBound A := by
  have hn : A.card = 61 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=113) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_34 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 62 ≤ A.card) (hhi : A.card ≤ 62) : GrahamBound A := by
  have hn : A.card = 62 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=113) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_35 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 63 ≤ A.card) (hhi : A.card ≤ 63) : GrahamBound A := by
  have hn : A.card = 63 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=113) (j:=2)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_36 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 64 ≤ A.card) (hhi : A.card ≤ 64) : GrahamBound A := by
  have hn : A.card = 64 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=113) (j:=3)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_37 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 65 ≤ A.card) (hhi : A.card ≤ 65) : GrahamBound A := by
  exact grahamBound_of_card_65 A h0 (Finset.card_pos.mp (by omega)) (by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_42 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 74 ≤ A.card) (hhi : A.card ≤ 74) : GrahamBound A := by
  have hn : A.card = 74 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=139) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_43 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 75 ≤ A.card) (hhi : A.card ≤ 75) : GrahamBound A := by
  have hn : A.card = 75 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=139) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_50 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 96 ≤ A.card) (hhi : A.card ≤ 96) : GrahamBound A := by
  have hn : A.card = 96 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=179) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_53 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 105 ≤ A.card) (hhi : A.card ≤ 105) : GrahamBound A := by
  have hn : A.card = 105 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=199) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_54 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 106 ≤ A.card) (hhi : A.card ≤ 106) : GrahamBound A := by
  have hn : A.card = 106 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=199) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_56 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 111 ≤ A.card) (hhi : A.card ≤ 111) : GrahamBound A := by
  have hn : A.card = 111 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=211) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_57 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 112 ≤ A.card) (hhi : A.card ≤ 112) : GrahamBound A := by
  have hn : A.card = 112 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=211) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_62 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 123 ≤ A.card) (hhi : A.card ≤ 123) : GrahamBound A := by
  have hn : A.card = 123 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=229) (j:=2)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_63 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 124 ≤ A.card) (hhi : A.card ≤ 124) : GrahamBound A := by
  have hn : A.card = 124 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=233) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_64 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 125 ≤ A.card) (hhi : A.card ≤ 125) : GrahamBound A := by
  have hn : A.card = 125 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=229) (j:=3)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_65 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 126 ≤ A.card) (hhi : A.card ≤ 126) : GrahamBound A := by
  have hn : A.card = 126 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=239) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_71 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 148 ≤ A.card) (hhi : A.card ≤ 148) : GrahamBound A := by
  have hn : A.card = 148 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=283) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_73 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 153 ≤ A.card) (hhi : A.card ≤ 153) : GrahamBound A := by
  have hn : A.card = 153 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=293) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_74 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 154 ≤ A.card) (hhi : A.card ≤ 154) : GrahamBound A := by
  have hn : A.card = 154 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=293) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_75 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 155 ≤ A.card) (hhi : A.card ≤ 155) : GrahamBound A := by
  have hn : A.card = 155 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=293) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_78 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 165 ≤ A.card) (hhi : A.card ≤ 165) : GrahamBound A := by
  have hn : A.card = 165 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=317) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_79 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 166 ≤ A.card) (hhi : A.card ≤ 166) : GrahamBound A := by
  have hn : A.card = 166 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=317) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_88 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 208 ≤ A.card) (hhi : A.card ≤ 208) : GrahamBound A := by
  have hn : A.card = 208 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=401) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_89 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 209 ≤ A.card) (hhi : A.card ≤ 209) : GrahamBound A := by
  have hn : A.card = 209 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=401) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_92 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 218 ≤ A.card) (hhi : A.card ≤ 218) : GrahamBound A := by
  have hn : A.card = 218 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=419) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_93 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 219 ≤ A.card) (hhi : A.card ≤ 219) : GrahamBound A := by
  have hn : A.card = 219 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=419) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_103 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 270 ≤ A.card) (hhi : A.card ≤ 270) : GrahamBound A := by
  have hn : A.card = 270 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=523) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_130 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 430 ≤ A.card) (hhi : A.card ≤ 430) : GrahamBound A := by
  have hn : A.card = 430 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=839) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_134 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 455 ≤ A.card) (hhi : A.card ≤ 455) : GrahamBound A := by
  have hn : A.card = 455 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=887) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_135 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 456 ≤ A.card) (hhi : A.card ≤ 456) : GrahamBound A := by
  have hn : A.card = 456 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=887) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_161 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 677 ≤ A.card) (hhi : A.card ≤ 677) : GrahamBound A := by
  have hn : A.card = 677 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=1327) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_162 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 678 ≤ A.card) (hhi : A.card ≤ 678) : GrahamBound A := by
  have hn : A.card = 678 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=1327) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_163 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 679 ≤ A.card) (hhi : A.card ≤ 679) : GrahamBound A := by
  have hn : A.card = 679 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=1327) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_164 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 680 ≤ A.card) (hhi : A.card ≤ 680) : GrahamBound A := by
  have hn : A.card = 680 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=1327) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_165 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 681 ≤ A.card) (hhi : A.card ≤ 681) : GrahamBound A := by
  have hn : A.card = 681 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=1327) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_166 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 682 ≤ A.card) (hhi : A.card ≤ 682) : GrahamBound A := by
  have hn : A.card = 682 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=1327) (j:=2)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_184 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 850 ≤ A.card) (hhi : A.card ≤ 850) : GrahamBound A := by
  have hn : A.card = 850 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=1669) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_185 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 851 ≤ A.card) (hhi : A.card ≤ 851) : GrahamBound A := by
  have hn : A.card = 851 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=1669) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_186 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 852 ≤ A.card) (hhi : A.card ≤ 852) : GrahamBound A := by
  have hn : A.card = 852 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=1669) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_253 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 1656 ≤ A.card) (hhi : A.card ≤ 1656) : GrahamBound A := by
  have hn : A.card = 1656 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=3271) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma finite_normalized_core (A : Finset ℕ) (h0 : 0 ∉ A)
    (hg : A.gcd id=1) (hl : 11 ≤ A.card) (hu : A.card ≤ 7000) : GrahamBound A := by
  by_cases h235 : A.card ≤ 1402
  · by_cases h117 : A.card ≤ 339
    · by_cases h58 : A.card ≤ 112
      · by_cases h29 : A.card ≤ 49
        · by_cases h14 : A.card ≤ 27
          · by_cases h7 : A.card ≤ 18
            · by_cases h3 : A.card ≤ 14
              · by_cases h1 : A.card ≤ 11
                · exact pair_block 11 11 19 11 A h0 hg (by omega) (by omega)
                · by_cases h2 : A.card ≤ 13
                  · exact pair_block 12 13 23 11 A h0 hg (by omega) (by omega)
                  · exact block_2 A h0 hg (by omega) (by omega)
              · by_cases h5 : A.card ≤ 16
                · by_cases h4 : A.card ≤ 15
                  · exact block_3 A h0 hg (by omega) (by omega)
                  · exact pair_block 16 16 29 13 A h0 hg (by omega) (by omega)
                · by_cases h6 : A.card ≤ 17
                  · exact pair_block 17 17 31 17 A h0 hg (by omega) (by omega)
                  · exact block_6 A h0 hg (by omega) (by omega)
            · by_cases h10 : A.card ≤ 22
              · by_cases h8 : A.card ≤ 20
                · exact pair_block 19 20 37 19 A h0 hg (by omega) (by omega)
                · by_cases h9 : A.card ≤ 21
                  · exact block_8 A h0 hg (by omega) (by omega)
                  · exact pair_block 22 22 41 19 A h0 hg (by omega) (by omega)
              · by_cases h12 : A.card ≤ 25
                · by_cases h11 : A.card ≤ 23
                  · exact pair_block 23 23 43 23 A h0 hg (by omega) (by omega)
                  · exact pair_block 24 25 47 23 A h0 hg (by omega) (by omega)
                · by_cases h13 : A.card ≤ 26
                  · exact pair_block 26 26 47 23 A h0 hg (by omega) (by omega)
                  · exact block_13 A h0 hg (by omega) (by omega)
          · by_cases h21 : A.card ≤ 36
            · by_cases h17 : A.card ≤ 32
              · by_cases h15 : A.card ≤ 28
                · exact block_14 A h0 hg (by omega) (by omega)
                · by_cases h16 : A.card ≤ 29
                  · exact pair_block 29 29 53 29 A h0 hg (by omega) (by omega)
                  · exact pair_block 30 32 59 29 A h0 hg (by omega) (by omega)
              · by_cases h19 : A.card ≤ 34
                · by_cases h18 : A.card ≤ 33
                  · exact pair_block 33 33 61 29 A h0 hg (by omega) (by omega)
                  · exact block_18 A h0 hg (by omega) (by omega)
                · by_cases h20 : A.card ≤ 35
                  · exact block_19 A h0 hg (by omega) (by omega)
                  · exact pair_block 36 36 67 31 A h0 hg (by omega) (by omega)
            · by_cases h25 : A.card ≤ 44
              · by_cases h23 : A.card ≤ 40
                · by_cases h22 : A.card ≤ 39
                  · exact pair_block 37 39 73 37 A h0 hg (by omega) (by omega)
                  · exact block_22 A h0 hg (by omega) (by omega)
                · by_cases h24 : A.card ≤ 42
                  · exact pair_block 41 42 79 41 A h0 hg (by omega) (by omega)
                  · exact pair_block 43 44 83 41 A h0 hg (by omega) (by omega)
              · by_cases h27 : A.card ≤ 47
                · by_cases h26 : A.card ≤ 45
                  · exact block_25 A h0 hg (by omega) (by omega)
                  · exact pair_block 46 47 89 43 A h0 hg (by omega) (by omega)
                · by_cases h28 : A.card ≤ 48
                  · exact block_27 A h0 hg (by omega) (by omega)
                  · exact block_28 A h0 hg (by omega) (by omega)
        · by_cases h43 : A.card ≤ 74
          · by_cases h36 : A.card ≤ 63
            · by_cases h32 : A.card ≤ 58
              · by_cases h30 : A.card ≤ 52
                · exact pair_block 50 52 97 47 A h0 hg (by omega) (by omega)
                · by_cases h31 : A.card ≤ 55
                  · exact pair_block 53 55 103 53 A h0 hg (by omega) (by omega)
                  · exact pair_block 56 58 109 53 A h0 hg (by omega) (by omega)
              · by_cases h34 : A.card ≤ 61
                · by_cases h33 : A.card ≤ 60
                  · exact pair_block 59 60 113 59 A h0 hg (by omega) (by omega)
                  · exact block_33 A h0 hg (by omega) (by omega)
                · by_cases h35 : A.card ≤ 62
                  · exact block_34 A h0 hg (by omega) (by omega)
                  · exact block_35 A h0 hg (by omega) (by omega)
            · by_cases h39 : A.card ≤ 67
              · by_cases h37 : A.card ≤ 64
                · exact block_36 A h0 hg (by omega) (by omega)
                · by_cases h38 : A.card ≤ 65
                  · exact block_37 A h0 hg (by omega) (by omega)
                  · exact pair_block 66 67 127 61 A h0 hg (by omega) (by omega)
              · by_cases h41 : A.card ≤ 72
                · by_cases h40 : A.card ≤ 69
                  · exact pair_block 68 69 131 67 A h0 hg (by omega) (by omega)
                  · exact pair_block 70 72 137 67 A h0 hg (by omega) (by omega)
                · by_cases h42 : A.card ≤ 73
                  · exact pair_block 73 73 139 67 A h0 hg (by omega) (by omega)
                  · exact block_42 A h0 hg (by omega) (by omega)
          · by_cases h50 : A.card ≤ 95
            · by_cases h46 : A.card ≤ 82
              · by_cases h44 : A.card ≤ 75
                · exact block_43 A h0 hg (by omega) (by omega)
                · by_cases h45 : A.card ≤ 78
                  · exact pair_block 76 78 149 73 A h0 hg (by omega) (by omega)
                  · exact pair_block 79 82 157 79 A h0 hg (by omega) (by omega)
              · by_cases h48 : A.card ≤ 88
                · by_cases h47 : A.card ≤ 86
                  · exact pair_block 83 86 163 83 A h0 hg (by omega) (by omega)
                  · exact pair_block 87 88 167 83 A h0 hg (by omega) (by omega)
                · by_cases h49 : A.card ≤ 91
                  · exact pair_block 89 91 173 89 A h0 hg (by omega) (by omega)
                  · exact pair_block 92 95 181 89 A h0 hg (by omega) (by omega)
            · by_cases h54 : A.card ≤ 105
              · by_cases h52 : A.card ≤ 101
                · by_cases h51 : A.card ≤ 96
                  · exact block_50 A h0 hg (by omega) (by omega)
                  · exact pair_block 97 101 193 97 A h0 hg (by omega) (by omega)
                · by_cases h53 : A.card ≤ 104
                  · exact pair_block 102 104 199 97 A h0 hg (by omega) (by omega)
                  · exact block_53 A h0 hg (by omega) (by omega)
              · by_cases h56 : A.card ≤ 110
                · by_cases h55 : A.card ≤ 106
                  · exact block_54 A h0 hg (by omega) (by omega)
                  · exact pair_block 107 110 211 107 A h0 hg (by omega) (by omega)
                · by_cases h57 : A.card ≤ 111
                  · exact block_56 A h0 hg (by omega) (by omega)
                  · exact block_57 A h0 hg (by omega) (by omega)
      · by_cases h87 : A.card ≤ 201
        · by_cases h72 : A.card ≤ 148
          · by_cases h65 : A.card ≤ 125
            · by_cases h61 : A.card ≤ 121
              · by_cases h59 : A.card ≤ 116
                · exact pair_block 113 116 223 113 A h0 hg (by omega) (by omega)
                · by_cases h60 : A.card ≤ 119
                  · exact pair_block 117 119 229 113 A h0 hg (by omega) (by omega)
                  · exact pair_block 120 121 233 113 A h0 hg (by omega) (by omega)
              · by_cases h63 : A.card ≤ 123
                · by_cases h62 : A.card ≤ 122
                  · exact pair_block 122 122 233 113 A h0 hg (by omega) (by omega)
                  · exact block_62 A h0 hg (by omega) (by omega)
                · by_cases h64 : A.card ≤ 124
                  · exact block_63 A h0 hg (by omega) (by omega)
                  · exact block_64 A h0 hg (by omega) (by omega)
            · by_cases h68 : A.card ≤ 137
              · by_cases h66 : A.card ≤ 126
                · exact block_65 A h0 hg (by omega) (by omega)
                · by_cases h67 : A.card ≤ 131
                  · exact pair_block 127 131 251 127 A h0 hg (by omega) (by omega)
                  · exact pair_block 132 137 263 131 A h0 hg (by omega) (by omega)
              · by_cases h70 : A.card ≤ 146
                · by_cases h69 : A.card ≤ 141
                  · exact pair_block 138 141 271 137 A h0 hg (by omega) (by omega)
                  · exact pair_block 142 146 281 139 A h0 hg (by omega) (by omega)
                · by_cases h71 : A.card ≤ 147
                  · exact pair_block 147 147 283 137 A h0 hg (by omega) (by omega)
                  · exact block_71 A h0 hg (by omega) (by omega)
          · by_cases h79 : A.card ≤ 165
            · by_cases h75 : A.card ≤ 154
              · by_cases h73 : A.card ≤ 152
                · exact pair_block 149 152 293 149 A h0 hg (by omega) (by omega)
                · by_cases h74 : A.card ≤ 153
                  · exact block_73 A h0 hg (by omega) (by omega)
                  · exact block_74 A h0 hg (by omega) (by omega)
              · by_cases h77 : A.card ≤ 159
                · by_cases h76 : A.card ≤ 155
                  · exact block_75 A h0 hg (by omega) (by omega)
                  · exact pair_block 156 159 307 151 A h0 hg (by omega) (by omega)
                · by_cases h78 : A.card ≤ 164
                  · exact pair_block 160 164 317 157 A h0 hg (by omega) (by omega)
                  · exact block_78 A h0 hg (by omega) (by omega)
            · by_cases h83 : A.card ≤ 181
              · by_cases h81 : A.card ≤ 171
                · by_cases h80 : A.card ≤ 166
                  · exact block_79 A h0 hg (by omega) (by omega)
                  · exact pair_block 167 171 331 167 A h0 hg (by omega) (by omega)
                · by_cases h82 : A.card ≤ 175
                  · exact pair_block 172 175 337 167 A h0 hg (by omega) (by omega)
                  · exact pair_block 176 181 349 173 A h0 hg (by omega) (by omega)
              · by_cases h85 : A.card ≤ 190
                · by_cases h84 : A.card ≤ 186
                  · exact pair_block 182 186 359 179 A h0 hg (by omega) (by omega)
                  · exact pair_block 187 190 367 181 A h0 hg (by omega) (by omega)
                · by_cases h86 : A.card ≤ 196
                  · exact pair_block 191 196 379 191 A h0 hg (by omega) (by omega)
                  · exact pair_block 197 201 389 193 A h0 hg (by omega) (by omega)
        · by_cases h102 : A.card ≤ 262
          · by_cases h94 : A.card ≤ 219
            · by_cases h90 : A.card ≤ 209
              · by_cases h88 : A.card ≤ 207
                · exact pair_block 202 207 401 199 A h0 hg (by omega) (by omega)
                · by_cases h89 : A.card ≤ 208
                  · exact block_88 A h0 hg (by omega) (by omega)
                  · exact block_89 A h0 hg (by omega) (by omega)
              · by_cases h92 : A.card ≤ 217
                · by_cases h91 : A.card ≤ 211
                  · exact pair_block 210 211 409 199 A h0 hg (by omega) (by omega)
                  · exact pair_block 212 217 421 211 A h0 hg (by omega) (by omega)
                · by_cases h93 : A.card ≤ 218
                  · exact block_92 A h0 hg (by omega) (by omega)
                  · exact block_93 A h0 hg (by omega) (by omega)
            · by_cases h98 : A.card ≤ 241
              · by_cases h96 : A.card ≤ 228
                · by_cases h95 : A.card ≤ 222
                  · exact pair_block 220 222 431 211 A h0 hg (by omega) (by omega)
                  · exact pair_block 223 228 443 223 A h0 hg (by omega) (by omega)
                · by_cases h97 : A.card ≤ 236
                  · exact pair_block 229 236 457 229 A h0 hg (by omega) (by omega)
                  · exact pair_block 237 241 467 233 A h0 hg (by omega) (by omega)
              · by_cases h100 : A.card ≤ 251
                · by_cases h99 : A.card ≤ 247
                  · exact pair_block 242 247 479 239 A h0 hg (by omega) (by omega)
                  · exact pair_block 248 251 487 239 A h0 hg (by omega) (by omega)
                · by_cases h101 : A.card ≤ 259
                  · exact pair_block 252 259 503 251 A h0 hg (by omega) (by omega)
                  · exact pair_block 260 262 509 251 A h0 hg (by omega) (by omega)
          · by_cases h109 : A.card ≤ 302
            · by_cases h105 : A.card ≤ 278
              · by_cases h103 : A.card ≤ 269
                · exact pair_block 263 269 523 263 A h0 hg (by omega) (by omega)
                · by_cases h104 : A.card ≤ 270
                  · exact block_103 A h0 hg (by omega) (by omega)
                  · exact pair_block 271 278 541 271 A h0 hg (by omega) (by omega)
              · by_cases h107 : A.card ≤ 289
                · by_cases h106 : A.card ≤ 281
                  · exact pair_block 279 281 547 269 A h0 hg (by omega) (by omega)
                  · exact pair_block 282 289 563 281 A h0 hg (by omega) (by omega)
                · by_cases h108 : A.card ≤ 294
                  · exact pair_block 290 294 571 281 A h0 hg (by omega) (by omega)
                  · exact pair_block 295 302 587 293 A h0 hg (by omega) (by omega)
            · by_cases h113 : A.card ≤ 318
              · by_cases h111 : A.card ≤ 308
                · by_cases h110 : A.card ≤ 305
                  · exact pair_block 303 305 593 293 A h0 hg (by omega) (by omega)
                  · exact pair_block 306 308 599 293 A h0 hg (by omega) (by omega)
                · by_cases h112 : A.card ≤ 315
                  · exact pair_block 309 315 613 307 A h0 hg (by omega) (by omega)
                  · exact pair_block 316 318 619 307 A h0 hg (by omega) (by omega)
              · by_cases h115 : A.card ≤ 329
                · by_cases h114 : A.card ≤ 324
                  · exact pair_block 319 324 631 313 A h0 hg (by omega) (by omega)
                  · exact pair_block 325 329 641 317 A h0 hg (by omega) (by omega)
                · by_cases h116 : A.card ≤ 332
                  · exact pair_block 330 332 647 317 A h0 hg (by omega) (by omega)
                  · exact pair_block 333 339 661 331 A h0 hg (by omega) (by omega)
    · by_cases h176 : A.card ≤ 769
      · by_cases h146 : A.card ≤ 537
        · by_cases h131 : A.card ≤ 430
          · by_cases h124 : A.card ≤ 390
            · by_cases h120 : A.card ≤ 359
              · by_cases h118 : A.card ≤ 347
                · exact pair_block 340 347 677 337 A h0 hg (by omega) (by omega)
                · by_cases h119 : A.card ≤ 354
                  · exact pair_block 348 354 691 347 A h0 hg (by omega) (by omega)
                  · exact pair_block 355 359 701 347 A h0 hg (by omega) (by omega)
              · by_cases h122 : A.card ≤ 376
                · by_cases h121 : A.card ≤ 368
                  · exact pair_block 360 368 719 359 A h0 hg (by omega) (by omega)
                  · exact pair_block 369 376 733 367 A h0 hg (by omega) (by omega)
                · by_cases h123 : A.card ≤ 381
                  · exact pair_block 377 381 743 367 A h0 hg (by omega) (by omega)
                  · exact pair_block 382 390 761 379 A h0 hg (by omega) (by omega)
            · by_cases h127 : A.card ≤ 408
              · by_cases h125 : A.card ≤ 396
                · exact pair_block 391 396 773 383 A h0 hg (by omega) (by omega)
                · by_cases h126 : A.card ≤ 403
                  · exact pair_block 397 403 787 397 A h0 hg (by omega) (by omega)
                  · exact pair_block 404 408 797 397 A h0 hg (by omega) (by omega)
              · by_cases h129 : A.card ≤ 421
                · by_cases h128 : A.card ≤ 415
                  · exact pair_block 409 415 811 409 A h0 hg (by omega) (by omega)
                  · exact pair_block 416 421 823 409 A h0 hg (by omega) (by omega)
                · by_cases h130 : A.card ≤ 429
                  · exact pair_block 422 429 839 419 A h0 hg (by omega) (by omega)
                  · exact block_130 A h0 hg (by omega) (by omega)
          · by_cases h138 : A.card ≤ 475
            · by_cases h134 : A.card ≤ 454
              · by_cases h132 : A.card ≤ 439
                · exact pair_block 431 439 859 431 A h0 hg (by omega) (by omega)
                · by_cases h133 : A.card ≤ 448
                  · exact pair_block 440 448 877 439 A h0 hg (by omega) (by omega)
                  · exact pair_block 449 454 887 439 A h0 hg (by omega) (by omega)
              · by_cases h136 : A.card ≤ 456
                · by_cases h135 : A.card ≤ 455
                  · exact block_134 A h0 hg (by omega) (by omega)
                  · exact block_135 A h0 hg (by omega) (by omega)
                · by_cases h137 : A.card ≤ 466
                  · exact pair_block 457 466 911 457 A h0 hg (by omega) (by omega)
                  · exact pair_block 467 475 929 463 A h0 hg (by omega) (by omega)
            · by_cases h142 : A.card ≤ 502
              · by_cases h140 : A.card ≤ 487
                · by_cases h139 : A.card ≤ 481
                  · exact pair_block 476 481 941 467 A h0 hg (by omega) (by omega)
                  · exact pair_block 482 487 953 479 A h0 hg (by omega) (by omega)
                · by_cases h141 : A.card ≤ 496
                  · exact pair_block 488 496 971 487 A h0 hg (by omega) (by omega)
                  · exact pair_block 497 502 983 487 A h0 hg (by omega) (by omega)
              · by_cases h144 : A.card ≤ 520
                · by_cases h143 : A.card ≤ 509
                  · exact pair_block 503 509 997 499 A h0 hg (by omega) (by omega)
                  · exact pair_block 510 520 1019 509 A h0 hg (by omega) (by omega)
                · by_cases h145 : A.card ≤ 530
                  · exact pair_block 521 530 1039 521 A h0 hg (by omega) (by omega)
                  · exact pair_block 531 537 1051 521 A h0 hg (by omega) (by omega)
        · by_cases h161 : A.card ≤ 676
          · by_cases h153 : A.card ≤ 597
            · by_cases h149 : A.card ≤ 558
              · by_cases h147 : A.card ≤ 542
                · exact pair_block 538 542 1061 523 A h0 hg (by omega) (by omega)
                · by_cases h148 : A.card ≤ 546
                  · exact pair_block 543 546 1069 541 A h0 hg (by omega) (by omega)
                  · exact pair_block 547 558 1093 547 A h0 hg (by omega) (by omega)
              · by_cases h151 : A.card ≤ 576
                · by_cases h150 : A.card ≤ 566
                  · exact pair_block 559 566 1109 557 A h0 hg (by omega) (by omega)
                  · exact pair_block 567 576 1129 563 A h0 hg (by omega) (by omega)
                · by_cases h152 : A.card ≤ 588
                  · exact pair_block 577 588 1153 577 A h0 hg (by omega) (by omega)
                  · exact pair_block 589 597 1171 587 A h0 hg (by omega) (by omega)
            · by_cases h157 : A.card ≤ 630
              · by_cases h155 : A.card ≤ 612
                · by_cases h154 : A.card ≤ 605
                  · exact pair_block 598 605 1187 593 A h0 hg (by omega) (by omega)
                  · exact pair_block 606 612 1201 599 A h0 hg (by omega) (by omega)
                · by_cases h156 : A.card ≤ 623
                  · exact pair_block 613 623 1223 613 A h0 hg (by omega) (by omega)
                  · exact pair_block 624 630 1237 613 A h0 hg (by omega) (by omega)
              · by_cases h159 : A.card ≤ 654
                · by_cases h158 : A.card ≤ 642
                  · exact pair_block 631 642 1259 631 A h0 hg (by omega) (by omega)
                  · exact pair_block 643 654 1283 641 A h0 hg (by omega) (by omega)
                · by_cases h160 : A.card ≤ 666
                  · exact pair_block 655 666 1307 653 A h0 hg (by omega) (by omega)
                  · exact pair_block 667 676 1327 661 A h0 hg (by omega) (by omega)
          · by_cases h168 : A.card ≤ 693
            · by_cases h164 : A.card ≤ 679
              · by_cases h162 : A.card ≤ 677
                · exact block_161 A h0 hg (by omega) (by omega)
                · by_cases h163 : A.card ≤ 678
                  · exact block_162 A h0 hg (by omega) (by omega)
                  · exact block_163 A h0 hg (by omega) (by omega)
              · by_cases h166 : A.card ≤ 681
                · by_cases h165 : A.card ≤ 680
                  · exact block_164 A h0 hg (by omega) (by omega)
                  · exact block_165 A h0 hg (by omega) (by omega)
                · by_cases h167 : A.card ≤ 682
                  · exact block_166 A h0 hg (by omega) (by omega)
                  · exact pair_block 683 693 1361 683 A h0 hg (by omega) (by omega)
            · by_cases h172 : A.card ≤ 726
              · by_cases h170 : A.card ≤ 712
                · by_cases h169 : A.card ≤ 703
                  · exact pair_block 694 703 1381 691 A h0 hg (by omega) (by omega)
                  · exact pair_block 704 712 1399 701 A h0 hg (by omega) (by omega)
                · by_cases h171 : A.card ≤ 717
                  · exact pair_block 713 717 1409 701 A h0 hg (by omega) (by omega)
                  · exact pair_block 718 726 1427 709 A h0 hg (by omega) (by omega)
              · by_cases h174 : A.card ≤ 749
                · by_cases h173 : A.card ≤ 739
                  · exact pair_block 727 739 1453 727 A h0 hg (by omega) (by omega)
                  · exact pair_block 740 749 1471 733 A h0 hg (by omega) (by omega)
                · by_cases h175 : A.card ≤ 760
                  · exact pair_block 750 760 1493 743 A h0 hg (by omega) (by omega)
                  · exact pair_block 761 769 1511 751 A h0 hg (by omega) (by omega)
      · by_cases h205 : A.card ≤ 1056
        · by_cases h190 : A.card ≤ 891
          · by_cases h183 : A.card ≤ 842
            · by_cases h179 : A.card ≤ 799
              · by_cases h177 : A.card ≤ 779
                · exact pair_block 770 779 1531 761 A h0 hg (by omega) (by omega)
                · by_cases h178 : A.card ≤ 790
                  · exact pair_block 780 790 1553 773 A h0 hg (by omega) (by omega)
                  · exact pair_block 791 799 1571 787 A h0 hg (by omega) (by omega)
              · by_cases h181 : A.card ≤ 824
                · by_cases h180 : A.card ≤ 812
                  · exact pair_block 800 812 1597 797 A h0 hg (by omega) (by omega)
                  · exact pair_block 813 824 1621 809 A h0 hg (by omega) (by omega)
                · by_cases h182 : A.card ≤ 832
                  · exact pair_block 825 832 1637 821 A h0 hg (by omega) (by omega)
                  · exact pair_block 833 842 1657 827 A h0 hg (by omega) (by omega)
            · by_cases h186 : A.card ≤ 851
              · by_cases h184 : A.card ≤ 849
                · exact pair_block 843 849 1669 827 A h0 hg (by omega) (by omega)
                · by_cases h185 : A.card ≤ 850
                  · exact block_184 A h0 hg (by omega) (by omega)
                  · exact block_185 A h0 hg (by omega) (by omega)
              · by_cases h188 : A.card ≤ 864
                · by_cases h187 : A.card ≤ 852
                  · exact block_186 A h0 hg (by omega) (by omega)
                  · exact pair_block 853 864 1699 853 A h0 hg (by omega) (by omega)
                · by_cases h189 : A.card ≤ 876
                  · exact pair_block 865 876 1723 859 A h0 hg (by omega) (by omega)
                  · exact pair_block 877 891 1753 877 A h0 hg (by omega) (by omega)
          · by_cases h197 : A.card ≤ 959
            · by_cases h193 : A.card ≤ 920
              · by_cases h191 : A.card ≤ 903
                · exact pair_block 892 903 1777 887 A h0 hg (by omega) (by omega)
                · by_cases h192 : A.card ≤ 909
                  · exact pair_block 904 909 1789 887 A h0 hg (by omega) (by omega)
                  · exact pair_block 910 920 1811 907 A h0 hg (by omega) (by omega)
              · by_cases h195 : A.card ≤ 938
                · by_cases h194 : A.card ≤ 930
                  · exact pair_block 921 930 1831 911 A h0 hg (by omega) (by omega)
                  · exact pair_block 931 938 1847 919 A h0 hg (by omega) (by omega)
                · by_cases h196 : A.card ≤ 951
                  · exact pair_block 939 951 1873 937 A h0 hg (by omega) (by omega)
                  · exact pair_block 952 959 1889 937 A h0 hg (by omega) (by omega)
            · by_cases h201 : A.card ≤ 1005
              · by_cases h199 : A.card ≤ 982
                · by_cases h198 : A.card ≤ 971
                  · exact pair_block 960 971 1913 953 A h0 hg (by omega) (by omega)
                  · exact pair_block 972 982 1933 967 A h0 hg (by omega) (by omega)
                · by_cases h200 : A.card ≤ 991
                  · exact pair_block 983 991 1951 971 A h0 hg (by omega) (by omega)
                  · exact pair_block 992 1005 1979 991 A h0 hg (by omega) (by omega)
              · by_cases h203 : A.card ≤ 1030
                · by_cases h202 : A.card ≤ 1017
                  · exact pair_block 1006 1017 2003 997 A h0 hg (by omega) (by omega)
                  · exact pair_block 1018 1030 2029 1013 A h0 hg (by omega) (by omega)
                · by_cases h204 : A.card ≤ 1042
                  · exact pair_block 1031 1042 2053 1031 A h0 hg (by omega) (by omega)
                  · exact pair_block 1043 1056 2081 1039 A h0 hg (by omega) (by omega)
        · by_cases h220 : A.card ≤ 1228
          · by_cases h212 : A.card ≤ 1135
            · by_cases h208 : A.card ≤ 1087
              · by_cases h206 : A.card ≤ 1065
                · exact pair_block 1057 1065 2099 1049 A h0 hg (by omega) (by omega)
                · by_cases h207 : A.card ≤ 1080
                  · exact pair_block 1066 1080 2129 1063 A h0 hg (by omega) (by omega)
                  · exact pair_block 1081 1087 2143 1063 A h0 hg (by omega) (by omega)
              · by_cases h210 : A.card ≤ 1106
                · by_cases h209 : A.card ≤ 1096
                  · exact pair_block 1088 1096 2161 1087 A h0 hg (by omega) (by omega)
                  · exact pair_block 1097 1106 2179 1087 A h0 hg (by omega) (by omega)
                · by_cases h211 : A.card ≤ 1120
                  · exact pair_block 1107 1120 2207 1103 A h0 hg (by omega) (by omega)
                  · exact pair_block 1121 1135 2237 1117 A h0 hg (by omega) (by omega)
            · by_cases h216 : A.card ≤ 1172
              · by_cases h214 : A.card ≤ 1151
                · by_cases h213 : A.card ≤ 1142
                  · exact pair_block 1136 1142 2251 1117 A h0 hg (by omega) (by omega)
                  · exact pair_block 1143 1151 2269 1129 A h0 hg (by omega) (by omega)
                · by_cases h215 : A.card ≤ 1165
                  · exact pair_block 1152 1165 2297 1151 A h0 hg (by omega) (by omega)
                  · exact pair_block 1166 1172 2311 1151 A h0 hg (by omega) (by omega)
              · by_cases h218 : A.card ≤ 1202
                · by_cases h217 : A.card ≤ 1187
                  · exact pair_block 1173 1187 2341 1171 A h0 hg (by omega) (by omega)
                  · exact pair_block 1188 1202 2371 1187 A h0 hg (by omega) (by omega)
                · by_cases h219 : A.card ≤ 1216
                  · exact pair_block 1203 1216 2399 1201 A h0 hg (by omega) (by omega)
                  · exact pair_block 1217 1228 2423 1213 A h0 hg (by omega) (by omega)
          · by_cases h227 : A.card ≤ 1328
            · by_cases h223 : A.card ≤ 1269
              · by_cases h221 : A.card ≤ 1241
                · exact pair_block 1229 1241 2447 1223 A h0 hg (by omega) (by omega)
                · by_cases h222 : A.card ≤ 1256
                  · exact pair_block 1242 1256 2477 1237 A h0 hg (by omega) (by omega)
                  · exact pair_block 1257 1269 2503 1249 A h0 hg (by omega) (by omega)
              · by_cases h225 : A.card ≤ 1296
                · by_cases h224 : A.card ≤ 1278
                  · exact pair_block 1270 1278 2521 1259 A h0 hg (by omega) (by omega)
                  · exact pair_block 1279 1296 2557 1279 A h0 hg (by omega) (by omega)
                · by_cases h226 : A.card ≤ 1314
                  · exact pair_block 1297 1314 2593 1297 A h0 hg (by omega) (by omega)
                  · exact pair_block 1315 1328 2621 1307 A h0 hg (by omega) (by omega)
            · by_cases h231 : A.card ≤ 1359
              · by_cases h229 : A.card ≤ 1349
                · by_cases h228 : A.card ≤ 1341
                  · exact pair_block 1329 1341 2647 1319 A h0 hg (by omega) (by omega)
                  · exact pair_block 1342 1349 2663 1321 A h0 hg (by omega) (by omega)
                · by_cases h230 : A.card ≤ 1356
                  · exact pair_block 1350 1356 2677 1327 A h0 hg (by omega) (by omega)
                  · exact pair_block 1357 1359 2683 1327 A h0 hg (by omega) (by omega)
              · by_cases h233 : A.card ≤ 1377
                · by_cases h232 : A.card ≤ 1361
                  · exact pair_block 1360 1361 2687 1327 A h0 hg (by omega) (by omega)
                  · exact pair_block 1362 1377 2719 1361 A h0 hg (by omega) (by omega)
                · by_cases h234 : A.card ≤ 1393
                  · exact pair_block 1378 1393 2749 1373 A h0 hg (by omega) (by omega)
                  · exact pair_block 1394 1402 2767 1373 A h0 hg (by omega) (by omega)
  · by_cases h352 : A.card ≤ 3558
    · by_cases h293 : A.card ≤ 2322
      · by_cases h264 : A.card ≤ 1800
        · by_cases h249 : A.card ≤ 1604
          · by_cases h242 : A.card ≤ 1504
            · by_cases h238 : A.card ≤ 1447
              · by_cases h236 : A.card ≤ 1419
                · exact pair_block 1403 1419 2801 1399 A h0 hg (by omega) (by omega)
                · by_cases h237 : A.card ≤ 1428
                  · exact pair_block 1420 1428 2819 1399 A h0 hg (by omega) (by omega)
                  · exact pair_block 1429 1447 2857 1429 A h0 hg (by omega) (by omega)
              · by_cases h240 : A.card ≤ 1477
                · by_cases h239 : A.card ≤ 1462
                  · exact pair_block 1448 1462 2887 1439 A h0 hg (by omega) (by omega)
                  · exact pair_block 1463 1477 2917 1459 A h0 hg (by omega) (by omega)
                · by_cases h241 : A.card ≤ 1488
                  · exact pair_block 1478 1488 2939 1471 A h0 hg (by omega) (by omega)
                  · exact pair_block 1489 1504 2971 1483 A h0 hg (by omega) (by omega)
            · by_cases h245 : A.card ≤ 1550
              · by_cases h243 : A.card ≤ 1519
                · exact pair_block 1505 1519 3001 1499 A h0 hg (by omega) (by omega)
                · by_cases h244 : A.card ≤ 1530
                  · exact pair_block 1520 1530 3023 1511 A h0 hg (by omega) (by omega)
                  · exact pair_block 1531 1550 3061 1531 A h0 hg (by omega) (by omega)
              · by_cases h247 : A.card ≤ 1580
                · by_cases h246 : A.card ≤ 1564
                  · exact pair_block 1551 1564 3089 1543 A h0 hg (by omega) (by omega)
                  · exact pair_block 1565 1580 3121 1559 A h0 hg (by omega) (by omega)
                · by_cases h248 : A.card ≤ 1588
                  · exact pair_block 1581 1588 3137 1559 A h0 hg (by omega) (by omega)
                  · exact pair_block 1589 1604 3169 1583 A h0 hg (by omega) (by omega)
          · by_cases h256 : A.card ≤ 1691
            · by_cases h252 : A.card ≤ 1649
              · by_cases h250 : A.card ≤ 1621
                · exact pair_block 1605 1621 3203 1601 A h0 hg (by omega) (by omega)
                · by_cases h251 : A.card ≤ 1634
                  · exact pair_block 1622 1634 3229 1607 A h0 hg (by omega) (by omega)
                  · exact pair_block 1635 1649 3259 1627 A h0 hg (by omega) (by omega)
              · by_cases h254 : A.card ≤ 1656
                · by_cases h253 : A.card ≤ 1655
                  · exact pair_block 1650 1655 3271 1621 A h0 hg (by omega) (by omega)
                  · exact block_253 A h0 hg (by omega) (by omega)
                · by_cases h255 : A.card ≤ 1676
                  · exact pair_block 1657 1676 3313 1657 A h0 hg (by omega) (by omega)
                  · exact pair_block 1677 1691 3343 1667 A h0 hg (by omega) (by omega)
            · by_cases h260 : A.card ≤ 1745
              · by_cases h258 : A.card ≤ 1716
                · by_cases h257 : A.card ≤ 1701
                  · exact pair_block 1692 1701 3361 1669 A h0 hg (by omega) (by omega)
                  · exact pair_block 1702 1716 3391 1693 A h0 hg (by omega) (by omega)
                · by_cases h259 : A.card ≤ 1727
                  · exact pair_block 1717 1727 3413 1697 A h0 hg (by omega) (by omega)
                  · exact pair_block 1728 1745 3449 1721 A h0 hg (by omega) (by omega)
              · by_cases h262 : A.card ≤ 1770
                · by_cases h261 : A.card ≤ 1755
                  · exact pair_block 1746 1755 3469 1723 A h0 hg (by omega) (by omega)
                  · exact pair_block 1756 1770 3499 1747 A h0 hg (by omega) (by omega)
                · by_cases h263 : A.card ≤ 1785
                  · exact pair_block 1771 1785 3529 1759 A h0 hg (by omega) (by omega)
                  · exact pair_block 1786 1800 3559 1777 A h0 hg (by omega) (by omega)
        · by_cases h278 : A.card ≤ 2035
          · by_cases h271 : A.card ≤ 1923
            · by_cases h267 : A.card ≤ 1850
              · by_cases h265 : A.card ≤ 1817
                · exact pair_block 1801 1817 3593 1801 A h0 hg (by omega) (by omega)
                · by_cases h266 : A.card ≤ 1832
                  · exact pair_block 1818 1832 3623 1811 A h0 hg (by omega) (by omega)
                  · exact pair_block 1833 1850 3659 1831 A h0 hg (by omega) (by omega)
              · by_cases h269 : A.card ≤ 1891
                · by_cases h268 : A.card ≤ 1870
                  · exact pair_block 1851 1870 3697 1847 A h0 hg (by omega) (by omega)
                  · exact pair_block 1871 1891 3739 1871 A h0 hg (by omega) (by omega)
                · by_cases h270 : A.card ≤ 1911
                  · exact pair_block 1892 1911 3779 1889 A h0 hg (by omega) (by omega)
                  · exact pair_block 1912 1923 3803 1901 A h0 hg (by omega) (by omega)
            · by_cases h274 : A.card ≤ 1966
              · by_cases h272 : A.card ≤ 1938
                · exact pair_block 1924 1938 3833 1913 A h0 hg (by omega) (by omega)
                · by_cases h273 : A.card ≤ 1953
                  · exact pair_block 1939 1953 3863 1931 A h0 hg (by omega) (by omega)
                  · exact pair_block 1954 1966 3889 1949 A h0 hg (by omega) (by omega)
              · by_cases h276 : A.card ≤ 1995
                · by_cases h275 : A.card ≤ 1980
                  · exact pair_block 1967 1980 3917 1951 A h0 hg (by omega) (by omega)
                  · exact pair_block 1981 1995 3947 1973 A h0 hg (by omega) (by omega)
                · by_cases h277 : A.card ≤ 2016
                  · exact pair_block 1996 2016 3989 1993 A h0 hg (by omega) (by omega)
                  · exact pair_block 2017 2035 4027 2011 A h0 hg (by omega) (by omega)
          · by_cases h285 : A.card ≤ 2171
            · by_cases h281 : A.card ≤ 2089
              · by_cases h279 : A.card ≤ 2051
                · exact pair_block 2036 2051 4057 2027 A h0 hg (by omega) (by omega)
                · by_cases h280 : A.card ≤ 2068
                  · exact pair_block 2052 2068 4091 2039 A h0 hg (by omega) (by omega)
                  · exact pair_block 2069 2089 4133 2069 A h0 hg (by omega) (by omega)
              · by_cases h283 : A.card ≤ 2132
                · by_cases h282 : A.card ≤ 2111
                  · exact pair_block 2090 2111 4177 2087 A h0 hg (by omega) (by omega)
                  · exact pair_block 2112 2132 4219 2111 A h0 hg (by omega) (by omega)
                · by_cases h284 : A.card ≤ 2153
                  · exact pair_block 2133 2153 4261 2129 A h0 hg (by omega) (by omega)
                  · exact pair_block 2154 2171 4297 2143 A h0 hg (by omega) (by omega)
            · by_cases h289 : A.card ≤ 2244
              · by_cases h287 : A.card ≤ 2204
                · by_cases h286 : A.card ≤ 2186
                  · exact pair_block 2172 2186 4327 2161 A h0 hg (by omega) (by omega)
                  · exact pair_block 2187 2204 4363 2179 A h0 hg (by omega) (by omega)
                · by_cases h288 : A.card ≤ 2221
                  · exact pair_block 2205 2221 4397 2203 A h0 hg (by omega) (by omega)
                  · exact pair_block 2222 2244 4441 2221 A h0 hg (by omega) (by omega)
              · by_cases h291 : A.card ≤ 2282
                · by_cases h290 : A.card ≤ 2265
                  · exact pair_block 2245 2265 4483 2239 A h0 hg (by omega) (by omega)
                  · exact pair_block 2266 2282 4517 2251 A h0 hg (by omega) (by omega)
                · by_cases h292 : A.card ≤ 2304
                  · exact pair_block 2283 2304 4561 2281 A h0 hg (by omega) (by omega)
                  · exact pair_block 2305 2322 4597 2293 A h0 hg (by omega) (by omega)
      · by_cases h322 : A.card ≤ 2885
        · by_cases h307 : A.card ≤ 2584
          · by_cases h300 : A.card ≤ 2440
            · by_cases h296 : A.card ≤ 2375
              · by_cases h294 : A.card ≤ 2334
                · exact pair_block 2323 2334 4621 2309 A h0 hg (by omega) (by omega)
                · by_cases h295 : A.card ≤ 2355
                  · exact pair_block 2335 2355 4663 2333 A h0 hg (by omega) (by omega)
                  · exact pair_block 2356 2375 4703 2347 A h0 hg (by omega) (by omega)
              · by_cases h298 : A.card ≤ 2403
                · by_cases h297 : A.card ≤ 2390
                  · exact pair_block 2376 2390 4733 2357 A h0 hg (by omega) (by omega)
                  · exact pair_block 2391 2403 4759 2371 A h0 hg (by omega) (by omega)
                · by_cases h299 : A.card ≤ 2425
                  · exact pair_block 2404 2425 4801 2399 A h0 hg (by omega) (by omega)
                  · exact pair_block 2426 2440 4831 2411 A h0 hg (by omega) (by omega)
            · by_cases h303 : A.card ≤ 2503
              · by_cases h301 : A.card ≤ 2463
                · exact pair_block 2441 2463 4877 2437 A h0 hg (by omega) (by omega)
                · by_cases h302 : A.card ≤ 2484
                  · exact pair_block 2464 2484 4919 2459 A h0 hg (by omega) (by omega)
                  · exact pair_block 2485 2503 4957 2473 A h0 hg (by omega) (by omega)
              · by_cases h305 : A.card ≤ 2544
                · by_cases h304 : A.card ≤ 2526
                  · exact pair_block 2504 2526 5003 2503 A h0 hg (by omega) (by omega)
                  · exact pair_block 2527 2544 5039 2521 A h0 hg (by omega) (by omega)
                · by_cases h306 : A.card ≤ 2568
                  · exact pair_block 2545 2568 5087 2543 A h0 hg (by omega) (by omega)
                  · exact pair_block 2569 2584 5119 2551 A h0 hg (by omega) (by omega)
          · by_cases h314 : A.card ≤ 2725
            · by_cases h310 : A.card ≤ 2644
              · by_cases h308 : A.card ≤ 2601
                · exact pair_block 2585 2601 5153 2579 A h0 hg (by omega) (by omega)
                · by_cases h309 : A.card ≤ 2620
                  · exact pair_block 2602 2620 5189 2591 A h0 hg (by omega) (by omega)
                  · exact pair_block 2621 2644 5237 2617 A h0 hg (by omega) (by omega)
              · by_cases h312 : A.card ≤ 2687
                · by_cases h311 : A.card ≤ 2662
                  · exact pair_block 2645 2662 5273 2633 A h0 hg (by omega) (by omega)
                  · exact pair_block 2663 2687 5323 2663 A h0 hg (by omega) (by omega)
                · by_cases h313 : A.card ≤ 2701
                  · exact pair_block 2688 2701 5351 2663 A h0 hg (by omega) (by omega)
                  · exact pair_block 2702 2725 5399 2699 A h0 hg (by omega) (by omega)
            · by_cases h318 : A.card ≤ 2816
              · by_cases h316 : A.card ≤ 2767
                · by_cases h315 : A.card ≤ 2747
                  · exact pair_block 2726 2747 5443 2719 A h0 hg (by omega) (by omega)
                  · exact pair_block 2748 2767 5483 2741 A h0 hg (by omega) (by omega)
                · by_cases h317 : A.card ≤ 2791
                  · exact pair_block 2768 2791 5531 2767 A h0 hg (by omega) (by omega)
                  · exact pair_block 2792 2816 5581 2789 A h0 hg (by omega) (by omega)
              · by_cases h320 : A.card ≤ 2847
                · by_cases h319 : A.card ≤ 2822
                  · exact pair_block 2817 2822 5591 2777 A h0 hg (by omega) (by omega)
                  · exact pair_block 2823 2847 5641 2819 A h0 hg (by omega) (by omega)
                · by_cases h321 : A.card ≤ 2871
                  · exact pair_block 2848 2871 5689 2843 A h0 hg (by omega) (by omega)
                  · exact pair_block 2872 2885 5717 2851 A h0 hg (by omega) (by omega)
        · by_cases h337 : A.card ≤ 3214
          · by_cases h329 : A.card ≤ 3020
            · by_cases h325 : A.card ≤ 2946
              · by_cases h323 : A.card ≤ 2901
                · exact pair_block 2886 2901 5749 2879 A h0 hg (by omega) (by omega)
                · by_cases h324 : A.card ≤ 2922
                  · exact pair_block 2902 2922 5791 2897 A h0 hg (by omega) (by omega)
                  · exact pair_block 2923 2946 5839 2917 A h0 hg (by omega) (by omega)
              · by_cases h327 : A.card ≤ 2990
                · by_cases h326 : A.card ≤ 2967
                  · exact pair_block 2947 2967 5881 2939 A h0 hg (by omega) (by omega)
                  · exact pair_block 2968 2990 5927 2963 A h0 hg (by omega) (by omega)
                · by_cases h328 : A.card ≤ 3003
                  · exact pair_block 2991 3003 5953 2963 A h0 hg (by omega) (by omega)
                  · exact pair_block 3004 3020 5987 2999 A h0 hg (by omega) (by omega)
            · by_cases h333 : A.card ≤ 3114
              · by_cases h331 : A.card ≤ 3067
                · by_cases h330 : A.card ≤ 3045
                  · exact pair_block 3021 3045 6037 3019 A h0 hg (by omega) (by omega)
                  · exact pair_block 3046 3067 6079 3037 A h0 hg (by omega) (by omega)
                · by_cases h332 : A.card ≤ 3094
                  · exact pair_block 3068 3094 6133 3067 A h0 hg (by omega) (by omega)
                  · exact pair_block 3095 3114 6173 3079 A h0 hg (by omega) (by omega)
              · by_cases h335 : A.card ≤ 3163
                · by_cases h334 : A.card ≤ 3138
                  · exact pair_block 3115 3138 6221 3109 A h0 hg (by omega) (by omega)
                  · exact pair_block 3139 3163 6271 3137 A h0 hg (by omega) (by omega)
                · by_cases h336 : A.card ≤ 3189
                  · exact pair_block 3164 3189 6323 3163 A h0 hg (by omega) (by omega)
                  · exact pair_block 3190 3214 6373 3187 A h0 hg (by omega) (by omega)
          · by_cases h344 : A.card ≤ 3359
            · by_cases h340 : A.card ≤ 3274
              · by_cases h338 : A.card ≤ 3238
                · exact pair_block 3215 3238 6421 3209 A h0 hg (by omega) (by omega)
                · by_cases h339 : A.card ≤ 3253
                  · exact pair_block 3239 3253 6451 3217 A h0 hg (by omega) (by omega)
                  · exact pair_block 3254 3274 6491 3251 A h0 hg (by omega) (by omega)
              · by_cases h342 : A.card ≤ 3310
                · by_cases h341 : A.card ≤ 3293
                  · exact pair_block 3275 3293 6529 3257 A h0 hg (by omega) (by omega)
                  · exact pair_block 3294 3310 6563 3271 A h0 hg (by omega) (by omega)
                · by_cases h343 : A.card ≤ 3332
                  · exact pair_block 3311 3332 6607 3299 A h0 hg (by omega) (by omega)
                  · exact pair_block 3333 3359 6661 3329 A h0 hg (by omega) (by omega)
            · by_cases h348 : A.card ≤ 3449
              · by_cases h346 : A.card ≤ 3410
                · by_cases h345 : A.card ≤ 3388
                  · exact pair_block 3360 3388 6719 3359 A h0 hg (by omega) (by omega)
                  · exact pair_block 3389 3410 6763 3389 A h0 hg (by omega) (by omega)
                · by_cases h347 : A.card ≤ 3430
                  · exact pair_block 3411 3430 6803 3407 A h0 hg (by omega) (by omega)
                  · exact pair_block 3431 3449 6841 3413 A h0 hg (by omega) (by omega)
              · by_cases h350 : A.card ≤ 3502
                · by_cases h349 : A.card ≤ 3478
                  · exact pair_block 3450 3478 6899 3449 A h0 hg (by omega) (by omega)
                  · exact pair_block 3479 3502 6947 3469 A h0 hg (by omega) (by omega)
                · by_cases h351 : A.card ≤ 3530
                  · exact pair_block 3503 3530 7001 3499 A h0 hg (by omega) (by omega)
                  · exact pair_block 3531 3558 7057 3527 A h0 hg (by omega) (by omega)
    · by_cases h411 : A.card ≤ 5132
      · by_cases h381 : A.card ≤ 4296
        · by_cases h366 : A.card ≤ 3910
          · by_cases h359 : A.card ≤ 3726
            · by_cases h355 : A.card ≤ 3636
              · by_cases h353 : A.card ≤ 3584
                · exact pair_block 3559 3584 7109 3557 A h0 hg (by omega) (by omega)
                · by_cases h354 : A.card ≤ 3609
                  · exact pair_block 3585 3609 7159 3581 A h0 hg (by omega) (by omega)
                  · exact pair_block 3610 3636 7213 3607 A h0 hg (by omega) (by omega)
              · by_cases h357 : A.card ≤ 3678
                · by_cases h356 : A.card ≤ 3656
                  · exact pair_block 3637 3656 7253 3617 A h0 hg (by omega) (by omega)
                  · exact pair_block 3657 3678 7297 3643 A h0 hg (by omega) (by omega)
                · by_cases h358 : A.card ≤ 3705
                  · exact pair_block 3679 3705 7351 3673 A h0 hg (by omega) (by omega)
                  · exact pair_block 3706 3726 7393 3691 A h0 hg (by omega) (by omega)
            · by_cases h362 : A.card ≤ 3801
              · by_cases h360 : A.card ≤ 3756
                · exact pair_block 3727 3756 7451 3727 A h0 hg (by omega) (by omega)
                · by_cases h361 : A.card ≤ 3775
                  · exact pair_block 3757 3775 7489 3733 A h0 hg (by omega) (by omega)
                  · exact pair_block 3776 3801 7541 3767 A h0 hg (by omega) (by omega)
              · by_cases h364 : A.card ≤ 3855
                · by_cases h363 : A.card ≤ 3826
                  · exact pair_block 3802 3826 7591 3793 A h0 hg (by omega) (by omega)
                  · exact pair_block 3827 3855 7649 3823 A h0 hg (by omega) (by omega)
                · by_cases h365 : A.card ≤ 3882
                  · exact pair_block 3856 3882 7703 3847 A h0 hg (by omega) (by omega)
                  · exact pair_block 3883 3910 7759 3877 A h0 hg (by omega) (by omega)
          · by_cases h373 : A.card ≤ 4090
            · by_cases h369 : A.card ≤ 3984
              · by_cases h367 : A.card ≤ 3939
                · exact pair_block 3911 3939 7817 3907 A h0 hg (by omega) (by omega)
                · by_cases h368 : A.card ≤ 3964
                  · exact pair_block 3940 3964 7867 3929 A h0 hg (by omega) (by omega)
                  · exact pair_block 3965 3984 7907 3943 A h0 hg (by omega) (by omega)
              · by_cases h371 : A.card ≤ 4037
                · by_cases h370 : A.card ≤ 4007
                  · exact pair_block 3985 4007 7951 3967 A h0 hg (by omega) (by omega)
                  · exact pair_block 4008 4037 8011 4003 A h0 hg (by omega) (by omega)
                · by_cases h372 : A.card ≤ 4061
                  · exact pair_block 4038 4061 8059 4021 A h0 hg (by omega) (by omega)
                  · exact pair_block 4062 4090 8117 4057 A h0 hg (by omega) (by omega)
            · by_cases h377 : A.card ≤ 4196
              · by_cases h375 : A.card ≤ 4148
                · by_cases h374 : A.card ≤ 4121
                  · exact pair_block 4091 4121 8179 4091 A h0 hg (by omega) (by omega)
                  · exact pair_block 4122 4148 8233 4111 A h0 hg (by omega) (by omega)
                · by_cases h376 : A.card ≤ 4175
                  · exact pair_block 4149 4175 8287 4139 A h0 hg (by omega) (by omega)
                  · exact pair_block 4176 4196 8329 4153 A h0 hg (by omega) (by omega)
              · by_cases h379 : A.card ≤ 4247
                · by_cases h378 : A.card ≤ 4216
                  · exact pair_block 4197 4216 8369 4177 A h0 hg (by omega) (by omega)
                  · exact pair_block 4217 4247 8431 4217 A h0 hg (by omega) (by omega)
                · by_cases h380 : A.card ≤ 4266
                  · exact pair_block 4248 4266 8467 4219 A h0 hg (by omega) (by omega)
                  · exact pair_block 4267 4296 8527 4261 A h0 hg (by omega) (by omega)
        · by_cases h396 : A.card ≤ 4695
          · by_cases h388 : A.card ≤ 4479
            · by_cases h384 : A.card ≤ 4367
              · by_cases h382 : A.card ≤ 4323
                · exact pair_block 4297 4323 8581 4289 A h0 hg (by omega) (by omega)
                · by_cases h383 : A.card ≤ 4337
                  · exact pair_block 4324 4337 8609 4289 A h0 hg (by omega) (by omega)
                  · exact pair_block 4338 4367 8669 4337 A h0 hg (by omega) (by omega)
              · by_cases h386 : A.card ≤ 4424
                · by_cases h385 : A.card ≤ 4398
                  · exact pair_block 4368 4398 8731 4363 A h0 hg (by omega) (by omega)
                  · exact pair_block 4399 4424 8783 4391 A h0 hg (by omega) (by omega)
                · by_cases h387 : A.card ≤ 4452
                  · exact pair_block 4425 4452 8839 4421 A h0 hg (by omega) (by omega)
                  · exact pair_block 4453 4479 8893 4441 A h0 hg (by omega) (by omega)
            · by_cases h392 : A.card ≤ 4579
              · by_cases h390 : A.card ≤ 4519
                · by_cases h389 : A.card ≤ 4503
                  · exact pair_block 4480 4503 8941 4463 A h0 hg (by omega) (by omega)
                  · exact pair_block 4504 4519 8971 4481 A h0 hg (by omega) (by omega)
                · by_cases h391 : A.card ≤ 4548
                  · exact pair_block 4520 4548 9029 4513 A h0 hg (by omega) (by omega)
                  · exact pair_block 4549 4579 9091 4547 A h0 hg (by omega) (by omega)
              · by_cases h394 : A.card ≤ 4635
                · by_cases h393 : A.card ≤ 4602
                  · exact pair_block 4580 4602 9137 4561 A h0 hg (by omega) (by omega)
                  · exact pair_block 4603 4635 9203 4603 A h0 hg (by omega) (by omega)
                · by_cases h395 : A.card ≤ 4662
                  · exact pair_block 4636 4662 9257 4621 A h0 hg (by omega) (by omega)
                  · exact pair_block 4663 4695 9323 4663 A h0 hg (by omega) (by omega)
          · by_cases h403 : A.card ≤ 4895
            · by_cases h399 : A.card ≤ 4782
              · by_cases h397 : A.card ≤ 4722
                · exact pair_block 4696 4722 9377 4691 A h0 hg (by omega) (by omega)
                · by_cases h398 : A.card ≤ 4753
                  · exact pair_block 4723 4753 9439 4721 A h0 hg (by omega) (by omega)
                  · exact pair_block 4754 4782 9497 4751 A h0 hg (by omega) (by omega)
              · by_cases h401 : A.card ≤ 4835
                · by_cases h400 : A.card ≤ 4810
                  · exact pair_block 4783 4810 9551 4783 A h0 hg (by omega) (by omega)
                  · exact pair_block 4811 4835 9601 4793 A h0 hg (by omega) (by omega)
                · by_cases h402 : A.card ≤ 4865
                  · exact pair_block 4836 4865 9661 4831 A h0 hg (by omega) (by omega)
                  · exact pair_block 4866 4895 9721 4861 A h0 hg (by omega) (by omega)
            · by_cases h407 : A.card ≤ 5009
              · by_cases h405 : A.card ≤ 4954
                · by_cases h404 : A.card ≤ 4925
                  · exact pair_block 4896 4925 9781 4889 A h0 hg (by omega) (by omega)
                  · exact pair_block 4926 4954 9839 4919 A h0 hg (by omega) (by omega)
                · by_cases h406 : A.card ≤ 4985
                  · exact pair_block 4955 4985 9901 4951 A h0 hg (by omega) (by omega)
                  · exact pair_block 4986 5009 9949 4967 A h0 hg (by omega) (by omega)
              · by_cases h409 : A.card ≤ 5074
                · by_cases h408 : A.card ≤ 5039
                  · exact pair_block 5010 5039 10009 4999 A h0 hg (by omega) (by omega)
                  · exact pair_block 5040 5074 10079 5039 A h0 hg (by omega) (by omega)
                · by_cases h410 : A.card ≤ 5102
                  · exact pair_block 5075 5102 10133 5059 A h0 hg (by omega) (by omega)
                  · exact pair_block 5103 5132 10193 5099 A h0 hg (by omega) (by omega)
      · by_cases h440 : A.card ≤ 6000
        · by_cases h425 : A.card ≤ 5550
          · by_cases h418 : A.card ≤ 5342
            · by_cases h414 : A.card ≤ 5220
              · by_cases h412 : A.card ≤ 5159
                · exact pair_block 5133 5159 10247 5119 A h0 hg (by omega) (by omega)
                · by_cases h413 : A.card ≤ 5192
                  · exact pair_block 5160 5192 10313 5153 A h0 hg (by omega) (by omega)
                  · exact pair_block 5193 5220 10369 5179 A h0 hg (by omega) (by omega)
              · by_cases h416 : A.card ≤ 5279
                · by_cases h415 : A.card ≤ 5250
                  · exact pair_block 5221 5250 10429 5209 A h0 hg (by omega) (by omega)
                  · exact pair_block 5251 5279 10487 5237 A h0 hg (by omega) (by omega)
                · by_cases h417 : A.card ≤ 5315
                  · exact pair_block 5280 5315 10559 5279 A h0 hg (by omega) (by omega)
                  · exact pair_block 5316 5342 10613 5297 A h0 hg (by omega) (by omega)
            · by_cases h421 : A.card ≤ 5427
              · by_cases h419 : A.card ≤ 5370
                · exact pair_block 5343 5370 10667 5333 A h0 hg (by omega) (by omega)
                · by_cases h420 : A.card ≤ 5392
                  · exact pair_block 5371 5392 10711 5347 A h0 hg (by omega) (by omega)
                  · exact pair_block 5393 5427 10781 5393 A h0 hg (by omega) (by omega)
              · by_cases h423 : A.card ≤ 5491
                · by_cases h422 : A.card ≤ 5460
                  · exact pair_block 5428 5460 10847 5419 A h0 hg (by omega) (by omega)
                  · exact pair_block 5461 5491 10909 5449 A h0 hg (by omega) (by omega)
                · by_cases h424 : A.card ≤ 5523
                  · exact pair_block 5492 5523 10973 5483 A h0 hg (by omega) (by omega)
                  · exact pair_block 5524 5550 11027 5503 A h0 hg (by omega) (by omega)
          · by_cases h432 : A.card ≤ 5761
            · by_cases h428 : A.card ≤ 5625
              · by_cases h426 : A.card ≤ 5572
                · exact pair_block 5551 5572 11071 5521 A h0 hg (by omega) (by omega)
                · by_cases h427 : A.card ≤ 5602
                  · exact pair_block 5573 5602 11131 5563 A h0 hg (by omega) (by omega)
                  · exact pair_block 5603 5625 11177 5581 A h0 hg (by omega) (by omega)
              · by_cases h430 : A.card ≤ 5696
                · by_cases h429 : A.card ≤ 5659
                  · exact pair_block 5626 5659 11243 5623 A h0 hg (by omega) (by omega)
                  · exact pair_block 5660 5696 11317 5657 A h0 hg (by omega) (by omega)
                · by_cases h431 : A.card ≤ 5729
                  · exact pair_block 5697 5729 11383 5689 A h0 hg (by omega) (by omega)
                  · exact pair_block 5730 5761 11447 5717 A h0 hg (by omega) (by omega)
            · by_cases h436 : A.card ≤ 5882
              · by_cases h434 : A.card ≤ 5813
                · by_cases h433 : A.card ≤ 5789
                  · exact pair_block 5762 5789 11503 5741 A h0 hg (by omega) (by omega)
                  · exact pair_block 5790 5813 11551 5779 A h0 hg (by omega) (by omega)
                · by_cases h435 : A.card ≤ 5848
                  · exact pair_block 5814 5848 11621 5807 A h0 hg (by omega) (by omega)
                  · exact pair_block 5849 5882 11689 5843 A h0 hg (by omega) (by omega)
              · by_cases h438 : A.card ≤ 5944
                · by_cases h437 : A.card ≤ 5909
                  · exact pair_block 5883 5909 11743 5861 A h0 hg (by omega) (by omega)
                  · exact pair_block 5910 5944 11813 5903 A h0 hg (by omega) (by omega)
                · by_cases h439 : A.card ≤ 5972
                  · exact pair_block 5945 5972 11867 5923 A h0 hg (by omega) (by omega)
                  · exact pair_block 5973 6000 11923 5953 A h0 hg (by omega) (by omega)
        · by_cases h455 : A.card ≤ 6498
          · by_cases h447 : A.card ≤ 6212
            · by_cases h443 : A.card ≤ 6095
              · by_cases h441 : A.card ≤ 6032
                · exact pair_block 6001 6032 11987 5987 A h0 hg (by omega) (by omega)
                · by_cases h442 : A.card ≤ 6063
                  · exact pair_block 6033 6063 12049 6029 A h0 hg (by omega) (by omega)
                  · exact pair_block 6064 6095 12113 6053 A h0 hg (by omega) (by omega)
              · by_cases h445 : A.card ≤ 6159
                · by_cases h444 : A.card ≤ 6120
                  · exact pair_block 6096 6120 12163 6067 A h0 hg (by omega) (by omega)
                  · exact pair_block 6121 6159 12241 6121 A h0 hg (by omega) (by omega)
                · by_cases h446 : A.card ≤ 6189
                  · exact pair_block 6160 6189 12301 6143 A h0 hg (by omega) (by omega)
                  · exact pair_block 6190 6212 12347 6163 A h0 hg (by omega) (by omega)
            · by_cases h451 : A.card ≤ 6363
              · by_cases h449 : A.card ≤ 6288
                · by_cases h448 : A.card ≤ 6249
                  · exact pair_block 6213 6249 12421 6211 A h0 hg (by omega) (by omega)
                  · exact pair_block 6250 6288 12497 6247 A h0 hg (by omega) (by omega)
                · by_cases h450 : A.card ≤ 6324
                  · exact pair_block 6289 6324 12569 6287 A h0 hg (by omega) (by omega)
                  · exact pair_block 6325 6363 12647 6323 A h0 hg (by omega) (by omega)
              · by_cases h453 : A.card ≤ 6435
                · by_cases h452 : A.card ≤ 6400
                  · exact pair_block 6364 6400 12721 6359 A h0 hg (by omega) (by omega)
                  · exact pair_block 6401 6435 12791 6397 A h0 hg (by omega) (by omega)
                · by_cases h454 : A.card ≤ 6466
                  · exact pair_block 6436 6466 12853 6421 A h0 hg (by omega) (by omega)
                  · exact pair_block 6467 6498 12917 6451 A h0 hg (by omega) (by omega)
          · by_cases h462 : A.card ≤ 6740
            · by_cases h458 : A.card ≤ 6604
              · by_cases h456 : A.card ≤ 6531
                · exact pair_block 6499 6531 12983 6491 A h0 hg (by omega) (by omega)
                · by_cases h457 : A.card ≤ 6564
                  · exact pair_block 6532 6564 13049 6521 A h0 hg (by omega) (by omega)
                  · exact pair_block 6565 6604 13127 6563 A h0 hg (by omega) (by omega)
              · by_cases h460 : A.card ≤ 6665
                · by_cases h459 : A.card ≤ 6634
                  · exact pair_block 6605 6634 13187 6599 A h0 hg (by omega) (by omega)
                  · exact pair_block 6635 6665 13249 6619 A h0 hg (by omega) (by omega)
                · by_cases h461 : A.card ≤ 6704
                  · exact pair_block 6666 6704 13327 6661 A h0 hg (by omega) (by omega)
                  · exact pair_block 6705 6740 13399 6701 A h0 hg (by omega) (by omega)
            · by_cases h466 : A.card ≤ 6886
              · by_cases h464 : A.card ≤ 6817
                · by_cases h463 : A.card ≤ 6779
                  · exact pair_block 6741 6779 13477 6737 A h0 hg (by omega) (by omega)
                  · exact pair_block 6780 6817 13553 6779 A h0 hg (by omega) (by omega)
                · by_cases h465 : A.card ≤ 6850
                  · exact pair_block 6818 6850 13619 6803 A h0 hg (by omega) (by omega)
                  · exact pair_block 6851 6886 13691 6841 A h0 hg (by omega) (by omega)
              · by_cases h468 : A.card ≤ 6957
                · by_cases h467 : A.card ≤ 6922
                  · exact pair_block 6887 6922 13763 6883 A h0 hg (by omega) (by omega)
                  · exact pair_block 6923 6957 13831 6911 A h0 hg (by omega) (by omega)
                · by_cases h469 : A.card ≤ 6995
                  · exact pair_block 6958 6995 13907 6949 A h0 hg (by omega) (by omega)
                  · exact pair_block 6996 7000 13967 6971 A h0 hg (by omega) (by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem finite_bound (A : Finset ℕ) (h0 : 0 ∉ A) (hne : A.Nonempty)
    (hc : A.card ≤ 7000) : GrahamBound A := by
  by_cases hs : A.card ≤ 10
  · exact grahamBound_of_card_le_ten A h0 hne hs
  apply grahamBound_of_normalize A
  have hbc := normalize_card A
  exact finite_normalized_core (normalize A) (normalize_nonzero A h0)
    (normalize_gcd A h0 hne) (by omega) (by omega)
end OMA.GrahamFinite

theorem OMA.solution : OMA.R_Erdos402_erdos_402_R2.H1 := by
  intro A h0 _hg h4 h7000 _hp _hsq _hd _hsmooth
  exact OMA.GrahamFinite.finite_bound A h0 (Finset.card_pos.mp (by omega)) h7000
