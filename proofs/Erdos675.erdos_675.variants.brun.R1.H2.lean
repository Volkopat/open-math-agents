import OMAReductions.R_Erdos675_erdos_675_variants_brun_R1
import Mathlib

/-!
Hypothesis H2 of the Erdos675 Brun reduction: a large-modulus estimate along
infinitely many trial lengths, proved by combining double-exponential record lows
of the reciprocal sum, dyadic-scale averaging, and an upper-bound Brun-Hooley sieve.

Credits: adapts Brun-Hooley sieve components and Chebyshev coprime sparsity from
@LordMike (PR #7395, Erdos675.erdos_675.variants.brun.R1.H1).
-/

namespace OMA.BrunH2

open Finset Asymptotics Filter
open scoped Classical

/- ## Part 1: Shifted upper-bound Brun-Hooley sieve on `range L` -/

/-- `W` is an admissible set of moduli: pairwise coprime, larger than `N`, coprime to `M'`. -/
def Adm (A : Finset ℕ) (N M' : ℕ) (W : Finset ℕ) : Prop :=
  A ⊆ Icc 1 N ∧ (W : Set ℕ).Pairwise Nat.Coprime ∧ ∀ b ∈ W, N < b ∧ Nat.Coprime M' b

/-- Indicator that every modulus in `S` divides some `a + s + M' * k` with `a ∈ A`. -/
noncomputable def ind (A : Finset ℕ) (s M' : ℕ) (S : Finset ℕ) (k : ℕ) : ℝ :=
  if ∀ b ∈ S, ∃ a ∈ A, b ∣ a + s + M' * k then 1 else 0

/-- Weight of a block `P`; the coefficient of `S ⊆ P` is `c S.card`. -/
noncomputable def phi (A : Finset ℕ) (s M' : ℕ) (P : Finset ℕ) (c : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ S ∈ P.powerset, c S.card * ind A s M' S k

/-- Density of a block weight. -/
noncomputable def dens (g : ℝ) (P : Finset ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ S ∈ P.powerset, c S.card * ∏ b ∈ S, (g / (b : ℝ))

/-- Mass of a block weight (bounds the remainder). -/
noncomputable def mass (g : ℝ) (P : Finset ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ S ∈ P.powerset, |c S.card| * g ^ S.card

/-- Number of moduli in `P` that divide some `a + s + M' * k` with `a ∈ A`. -/
def nu (A : Finset ℕ) (s M' : ℕ) (P : Finset ℕ) (k : ℕ) : ℕ :=
  (P.filter (fun b => ∃ a ∈ A, b ∣ a + s + M' * k)).card

/-- Coefficients of the inclusion-exclusion sum truncated at order `m`. -/
noncomputable def cU (m : ℕ) (i : ℕ) : ℝ := if i ≤ m then (-1) ^ i else 0

/-- Coefficients of the first omitted term of order `m + 1`. -/
noncomputable def cE (m : ℕ) (i : ℕ) : ℝ := if i = m + 1 then 1 else 0

/-- Elementary symmetric sum of degree `i` of the numbers `t b`, `b ∈ P`. -/
noncomputable def esym (t : ℕ → ℝ) (P : Finset ℕ) (i : ℕ) : ℝ :=
  ∑ S ∈ P.powersetCard i, ∏ b ∈ S, t b

/-- Lower end (exclusive) of block `j`. -/
def lo (j : ℕ) : ℕ := if j = 0 then 0 else 2 ^ 2 ^ j

/-- Upper end (inclusive) of block `j`. -/
def hi (j : ℕ) : ℕ := 2 ^ 2 ^ (j + 1)

/-- Block `j` of the moduli: those in `(lo j, hi j]`. -/
def blk (W : Finset ℕ) (j : ℕ) : Finset ℕ := W.filter (fun b => lo j < b ∧ b ≤ hi j)

/-- Truncation order of block `j` when there are `n` blocks. Always even. -/
def mm (a n j : ℕ) : ℕ := 2 * (a + (n - j))

/-- The integers `k ∈ range L` such that no modulus in `W` divides any `a + s + M' * k`. -/
def siftR (A : Finset ℕ) (s M' : ℕ) (W : Finset ℕ) (L : ℕ) : Finset ℕ :=
  (range L).filter (fun k => ∀ b ∈ W, ∀ a ∈ A, ¬ b ∣ a + s + M' * k)

theorem adm_card_lt (A : Finset ℕ) (N M' : ℕ) (W : Finset ℕ) (hadm : Adm A N M' W) :
    ∀ b ∈ W, A.card < b := by
  intro b hb
  have h1 : A.card ≤ N := by
    have := Finset.card_le_card hadm.1
    simpa using this
  have h2 := (hadm.2.2 b hb).1
  omega

theorem hit_mod_s (b a s M' k : ℕ) : b ∣ a + s + M' * (k % b) ↔ b ∣ a + s + M' * k :=
  Nat.ModEq.dvd_iff (((Nat.mod_modEq k b).mul_left M').add_left (a + s)) dvd_rfl

theorem hit_mod_of_dvd_s (b d a s M' k : ℕ) (hbd : b ∣ d) :
    b ∣ a + s + M' * (k % d) ↔ b ∣ a + s + M' * k :=
  Nat.ModEq.dvd_iff ((((Nat.mod_modEq k d).of_dvd hbd).mul_left M').add_left (a + s)) dvd_rfl

theorem hit_unique_s (A : Finset ℕ) (N s M' b k a a' : ℕ) (hA : A ⊆ Icc 1 N) (hb : N < b)
    (ha : a ∈ A) (ha' : a' ∈ A) (h : b ∣ a + s + M' * k) (h' : b ∣ a' + s + M' * k) : a = a' := by
  have hA1 := Finset.mem_Icc.mp (hA ha)
  have hA2 := Finset.mem_Icc.mp (hA ha')
  rcases le_total a a' with hle | hle
  · have key : b ∣ (a' + s + M' * k) - (a + s + M' * k) := Nat.dvd_sub h' h
    have e : (a' + s + M' * k) - (a + s + M' * k) = a' - a := by omega
    rw [e] at key
    have := Nat.eq_zero_of_dvd_of_lt key (by omega)
    omega
  · have key : b ∣ (a + s + M' * k) - (a' + s + M' * k) := Nat.dvd_sub h h'
    have e : (a + s + M' * k) - (a' + s + M' * k) = a - a' := by omega
    rw [e] at key
    have := Nat.eq_zero_of_dvd_of_lt key (by omega)
    omega

theorem hit_exists_s (s M' b a : ℕ) (hb : 0 < b) (hc : Nat.Coprime M' b) :
    ∃ r, r < b ∧ b ∣ a + s + M' * r := by
  have : NeZero b := ⟨hb.ne'⟩
  refine ⟨(-((a + s : ℕ) : ZMod b) * ((ZMod.unitOfCoprime M' hc)⁻¹ : (ZMod b)ˣ)).val,
    ZMod.val_lt _, ?_⟩
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  rw [ZMod.natCast_zmod_val, ← ZMod.coe_unitOfCoprime M' hc,
    mul_comm (-((a : ZMod b) + (s : ZMod b))) _, Units.mul_inv_cancel_left]
  exact add_neg_cancel _

theorem hit_inj_s (s M' b a r r' : ℕ) (hc : Nat.Coprime M' b) (hr : r < b) (hr' : r' < b)
    (h : b ∣ a + s + M' * r) (h' : b ∣ a + s + M' * r') : r = r' := by
  rcases le_total r r' with hle | hle
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
    have e : a + s + M' * (r + d) = (a + s + M' * r) + M' * d := by ring
    rw [e] at h'
    have h2 : b ∣ M' * d := (Nat.dvd_add_right h).mp h'
    have h3 : b ∣ d := Nat.Coprime.dvd_of_dvd_mul_left hc.symm h2
    have := Nat.eq_zero_of_dvd_of_lt h3 (by omega)
    omega
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
    have e : a + s + M' * (r' + d) = (a + s + M' * r') + M' * d := by ring
    rw [e] at h
    have h2 : b ∣ M' * d := (Nat.dvd_add_right h').mp h
    have h3 : b ∣ d := Nat.Coprime.dvd_of_dvd_mul_left hc.symm h2
    have := Nat.eq_zero_of_dvd_of_lt h3 (by omega)
    omega

theorem res_card_s (A : Finset ℕ) (N s M' b : ℕ) (hA : A ⊆ Icc 1 N) (hb : N < b)
    (hc : Nat.Coprime M' b) :
    ((range b).filter (fun r => ∃ a ∈ A, b ∣ a + s + M' * r)).card = A.card := by
  choose f hf using fun a => hit_exists_s s M' b a (by omega) hc
  have himg : (range b).filter (fun r => ∃ a ∈ A, b ∣ a + s + M' * r) = A.image f := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hr, a, ha, hdvd⟩
      exact ⟨a, ha, (hit_inj_s s M' b a r (f a) hc hr (hf a).1 hdvd (hf a).2).symm⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨(hf a).1, a, ha, (hf a).2⟩
  rw [himg, Finset.card_image_of_injOn]
  intro a ha a' ha' heq
  have h1 := (hf a).2
  rw [heq] at h1
  exact hit_unique_s A N s M' b (f a') a a' hA hb ha ha' h1 (hf a').2

theorem crt_card (m n : ℕ) (h : Nat.Coprime m n) (hm : 0 < m) (hn : 0 < n) (P Q : ℕ → Prop)
    [DecidablePred P] [DecidablePred Q] :
    ((range (m * n)).filter (fun k => P (k % m) ∧ Q (k % n))).card =
      ((range m).filter P).card * ((range n).filter Q).card := by
  rw [← Finset.card_product]
  apply Finset.card_bij (fun k _ => (k % m, k % n))
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_range]
    exact ⟨⟨Nat.mod_lt _ hm, hk.2.1⟩, Nat.mod_lt _ hn, hk.2.2⟩
  · intro k hk k' hk' heq
    simp only [Finset.mem_filter, Finset.mem_range] at hk hk'
    simp only [Prod.mk.injEq] at heq
    have h1 : k ≡ k' [MOD m] := heq.1
    have h2 : k ≡ k' [MOD n] := heq.2
    have h3 : k ≡ k' [MOD m * n] := (Nat.modEq_and_modEq_iff_modEq_mul h).mp ⟨h1, h2⟩
    unfold Nat.ModEq at h3
    rwa [Nat.mod_eq_of_lt hk.1, Nat.mod_eq_of_lt hk'.1] at h3
  · rintro ⟨r, s⟩ hrs
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_range] at hrs
    obtain ⟨⟨hrm, hPr⟩, hsn, hQs⟩ := hrs
    have hex : ∃ c, c < m * n ∧ c % m = r ∧ c % n = s := by
      refine ⟨(Nat.chineseRemainder h r s).1, Nat.chineseRemainder_lt_mul h r s hm.ne' hn.ne', ?_, ?_⟩
      · have := (Nat.chineseRemainder h r s).2.1
        unfold Nat.ModEq at this
        exact this.trans (Nat.mod_eq_of_lt hrm)
      · have := (Nat.chineseRemainder h r s).2.2
        unfold Nat.ModEq at this
        exact this.trans (Nat.mod_eq_of_lt hsn)
    obtain ⟨c, hlt, hcm, hcn⟩ := hex
    exact ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt, by rw [hcm, hcn]; exact ⟨hPr, hQs⟩⟩,
      by simp [hcm, hcn]⟩

theorem period_card_s (A : Finset ℕ) (N s M' : ℕ) (W : Finset ℕ) (hadm : Adm A N M' W)
    (S : Finset ℕ) (hS : S ⊆ W) :
    ((range (∏ b ∈ S, b)).filter (fun k => ∀ b ∈ S, ∃ a ∈ A, b ∣ a + s + M' * k)).card =
      A.card ^ S.card := by
  revert hS
  induction S using Finset.induction_on with
  | empty => intro _; simp
  | @insert b S hbS ih =>
    intro hS
    have hbW : b ∈ W := hS (Finset.mem_insert_self b S)
    have hSW : S ⊆ W := fun x hx => hS (Finset.mem_insert_of_mem hx)
    have ih' := ih hSW
    have hbN := (hadm.2.2 b hbW).1
    have hc : Nat.Coprime M' b := (hadm.2.2 b hbW).2
    have hbpos : 0 < b := by omega
    have hSpos : 0 < ∏ x ∈ S, x := Finset.prod_pos (fun x hx => by
      have := (hadm.2.2 x (hSW hx)).1
      omega)
    have hcop : Nat.Coprime b (∏ x ∈ S, x) := by
      apply Nat.Coprime.prod_right
      intro x hx
      apply hadm.2.1 (Finset.mem_coe.mpr hbW) (Finset.mem_coe.mpr (hSW hx))
      rintro rfl
      exact hbS hx
    have hfilt : (range (b * ∏ x ∈ S, x)).filter (fun k => ∀ y ∈ insert b S, ∃ a ∈ A, y ∣ a + s + M' * k) =
        (range (b * ∏ x ∈ S, x)).filter (fun k => (∃ a ∈ A, b ∣ a + s + M' * (k % b)) ∧
          (∀ y ∈ S, ∃ a ∈ A, y ∣ a + s + M' * (k % ∏ x ∈ S, x))) := by
      apply Finset.filter_congr
      intro k _
      have hb' : (∃ a ∈ A, b ∣ a + s + M' * k) ↔ (∃ a ∈ A, b ∣ a + s + M' * (k % b)) := by
        simp only [hit_mod_s]
      have hS' : (∀ y ∈ S, ∃ a ∈ A, y ∣ a + s + M' * k) ↔
          (∀ y ∈ S, ∃ a ∈ A, y ∣ a + s + M' * (k % ∏ x ∈ S, x)) := by
        constructor
        · intro h y hy
          obtain ⟨a, ha, hd⟩ := h y hy
          have hdv : y ∣ ∏ x ∈ S, x := Finset.dvd_prod_of_mem (fun c => c) hy
          exact ⟨a, ha, (hit_mod_of_dvd_s y _ a s M' k hdv).mpr hd⟩
        · intro h y hy
          obtain ⟨a, ha, hd⟩ := h y hy
          have hdv : y ∣ ∏ x ∈ S, x := Finset.dvd_prod_of_mem (fun c => c) hy
          exact ⟨a, ha, (hit_mod_of_dvd_s y _ a s M' k hdv).mp hd⟩
      simp only [Finset.forall_mem_insert]
      exact and_congr hb' hS'
    have hcrt : ((range (b * ∏ x ∈ S, x)).filter (fun k => (∃ a ∈ A, b ∣ a + s + M' * (k % b)) ∧
          (∀ y ∈ S, ∃ a ∈ A, y ∣ a + s + M' * (k % ∏ x ∈ S, x)))).card =
        ((range b).filter (fun r => ∃ a ∈ A, b ∣ a + s + M' * r)).card *
          ((range (∏ x ∈ S, x)).filter (fun r => ∀ y ∈ S, ∃ a ∈ A, y ∣ a + s + M' * r)).card :=
      crt_card b (∏ x ∈ S, x) hcop hbpos hSpos (fun r => ∃ a ∈ A, b ∣ a + s + M' * r)
        (fun r => ∀ y ∈ S, ∃ a ∈ A, y ∣ a + s + M' * r)
    rw [Finset.prod_insert hbS, Finset.card_insert_of_notMem hbS, pow_succ', hfilt, hcrt,
      res_card_s A N s M' b hadm.1 hbN hc, ih']

theorem periodic_count_ico (P : ℕ → Prop) [DecidablePred P] (d : ℕ)
    (hper : ∀ k, P (k + d) ↔ P k) (s : ℕ) :
    ((Ico s (s + d)).filter P).card = ((range d).filter P).card := by
  have hP : Function.Periodic P d := fun k => propext (hper k)
  rw [Nat.filter_Ico_card_eq_of_periodic s d P hP, Nat.count_eq_card_filter_range]

theorem periodic_count_mul_zero (P : ℕ → Prop) [DecidablePred P] (d : ℕ)
    (hper : ∀ k, P (k + d) ↔ P k) (q : ℕ) :
    ((Ico 0 (q * d)).filter P).card = q * ((range d).filter P).card := by
  induction q with
  | zero => simp
  | succ q ih =>
    have e : (q + 1) * d = q * d + d := by ring
    rw [e, ← Finset.Ico_union_Ico_eq_Ico (Nat.zero_le _) (Nat.le_add_right _ _),
      Finset.filter_union, Finset.card_union_of_disjoint
        (Finset.disjoint_filter_filter (Finset.Ico_disjoint_Ico_consecutive _ _ _)),
      ih, periodic_count_ico P d hper (q * d)]
    ring

theorem periodic_window (P : ℕ → Prop) [DecidablePred P] (d : ℕ)
    (hper : ∀ k, P (k + d) ↔ P k) (s r : ℕ) (hr : r ≤ d) :
    ((Ico s (s + r)).filter P).card ≤ ((range d).filter P).card := by
  rw [← periodic_count_ico P d hper s]
  exact Finset.card_le_card
    (Finset.filter_subset_filter _ (Finset.Ico_subset_Ico_right (by omega)))

theorem periodic_count_range_nat (P : ℕ → Prop) [DecidablePred P] (d : ℕ) (hd : 0 < d)
    (hper : ∀ k, P (k + d) ↔ P k) (L : ℕ) :
    L / d * ((range d).filter P).card ≤ ((range L).filter P).card ∧
      ((range L).filter P).card ≤
        L / d * ((range d).filter P).card + ((range d).filter P).card := by
  have hI : range L = Ico 0 (L / d * d) ∪ Ico (L / d * d) (L / d * d + L % d) := by
    ext k
    simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
    have h := Nat.div_add_mod' L d
    omega
  have hsplit : (range L).filter P = (Ico 0 (L / d * d)).filter P ∪
      (Ico (L / d * d) (L / d * d + L % d)).filter P := by
    rw [hI, Finset.filter_union]
  have hA := periodic_count_mul_zero P d hper (L / d)
  have hB := periodic_window P d hper (L / d * d) (L % d) (Nat.mod_lt L hd).le
  have hU := Finset.card_union_le ((Ico 0 (L / d * d)).filter P)
    ((Ico (L / d * d) (L / d * d + L % d)).filter P)
  have hL := Finset.card_le_card (Finset.subset_union_left
    (s₁ := (Ico 0 (L / d * d)).filter P)
    (s₂ := (Ico (L / d * d) (L / d * d + L % d)).filter P))
  rw [← hsplit] at hU hL
  constructor <;> omega

theorem periodic_count_range (P : ℕ → Prop) [DecidablePred P] (d : ℕ) (hd : 0 < d)
    (hper : ∀ k, P (k + d) ↔ P k) (L : ℕ) :
    |(((range L).filter P).card : ℝ) - L * ((((range d).filter P).card : ℝ) / d)| ≤
      (((range d).filter P).card : ℝ) := by
  obtain ⟨h1, h2⟩ := periodic_count_range_nat P d hd hper L
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hq := Nat.div_add_mod' L d
  have hr := Nat.mod_lt L hd
  have h1R : ((L / d : ℕ) : ℝ) * (((range d).filter P).card : ℝ) ≤
      (((range L).filter P).card : ℝ) := by exact_mod_cast h1
  have h2R : (((range L).filter P).card : ℝ) ≤
      ((L / d : ℕ) : ℝ) * (((range d).filter P).card : ℝ) + (((range d).filter P).card : ℝ) := by
    exact_mod_cast h2
  have hLR : (L : ℝ) = ((L / d : ℕ) : ℝ) * d + ((L % d : ℕ) : ℝ) := by exact_mod_cast hq.symm
  have hrd : ((L % d : ℕ) : ℝ) ≤ d := by exact_mod_cast hr.le
  have hr0 : (0 : ℝ) ≤ ((L % d : ℕ) : ℝ) := Nat.cast_nonneg _
  have hcdiv0 : (0 : ℝ) ≤ (((range d).filter P).card : ℝ) / d :=
    div_nonneg (Nat.cast_nonneg _) hdR.le
  have hE : (d : ℝ) * ((((range d).filter P).card : ℝ) / d) = (((range d).filter P).card : ℝ) := by
    field_simp
  have he0 : 0 ≤ ((L % d : ℕ) : ℝ) * ((((range d).filter P).card : ℝ) / d) :=
    mul_nonneg hr0 hcdiv0
  have he1 : ((L % d : ℕ) : ℝ) * ((((range d).filter P).card : ℝ) / d) ≤
      (((range d).filter P).card : ℝ) := by
    have := mul_le_mul_of_nonneg_right hrd hcdiv0
    linarith
  have hkey : (L : ℝ) * ((((range d).filter P).card : ℝ) / d) =
      ((L / d : ℕ) : ℝ) * (((range d).filter P).card : ℝ) +
        ((L % d : ℕ) : ℝ) * ((((range d).filter P).card : ℝ) / d) := by
    rw [hLR]
    linear_combination ((L / d : ℕ) : ℝ) * hE
  rw [abs_le]
  constructor <;> linarith

theorem cnt_bound_range (A : Finset ℕ) (N s M' : ℕ) (W : Finset ℕ) (hadm : Adm A N M' W)
    (S : Finset ℕ) (hS : S ⊆ W) (L : ℕ) :
    |∑ k ∈ range L, ind A s M' S k - L * ∏ b ∈ S, ((A.card : ℝ) / (b : ℝ))| ≤
      (A.card : ℝ) ^ S.card := by
  have hdpos : 0 < ∏ b ∈ S, b := Finset.prod_pos (fun b hb => by
    have := (hadm.2.2 b (hS hb)).1
    omega)
  have key : ∀ k, ∀ b ∈ S, ∀ a, b ∣ a + s + M' * (k + ∏ c ∈ S, c) ↔ b ∣ a + s + M' * k := by
    intro k b hb a
    have hbd : b ∣ ∏ c ∈ S, c := Finset.dvd_prod_of_mem (fun c => c) hb
    have h := hit_mod_of_dvd_s b (∏ c ∈ S, c) a s M' (k + ∏ c ∈ S, c) hbd
    rw [Nat.add_mod_right, hit_mod_of_dvd_s b (∏ c ∈ S, c) a s M' k hbd] at h
    exact h.symm
  have hper : ∀ k, (∀ b ∈ S, ∃ a ∈ A, b ∣ a + s + M' * (k + ∏ c ∈ S, c)) ↔
      (∀ b ∈ S, ∃ a ∈ A, b ∣ a + s + M' * k) := by
    intro k
    constructor
    · intro h b hb
      obtain ⟨a, ha, hd⟩ := h b hb
      exact ⟨a, ha, (key k b hb a).mp hd⟩
    · intro h b hb
      obtain ⟨a, ha, hd⟩ := h b hb
      exact ⟨a, ha, (key k b hb a).mpr hd⟩
  have hpc := periodic_count_range (fun k => ∀ b ∈ S, ∃ a ∈ A, b ∣ a + s + M' * k)
    (∏ c ∈ S, c) hdpos hper L
  have hcard : ((((range (∏ b ∈ S, b)).filter (fun k => ∀ b ∈ S, ∃ a ∈ A, b ∣ a + s + M' * k)).card : ℕ) : ℝ) =
      (A.card : ℝ) ^ S.card := by
    rw [period_card_s A N s M' W hadm S hS]
    push_cast
    ring
  have hprod : ∏ b ∈ S, ((A.card : ℝ) / (b : ℝ)) =
      (A.card : ℝ) ^ S.card / ((∏ b ∈ S, b : ℕ) : ℝ) := by
    rw [Finset.prod_div_distrib, Finset.prod_const, Nat.cast_prod]
  simp only [ind, Finset.sum_boole]
  rw [hprod]
  rw [hcard] at hpc
  exact hpc

theorem ind_union (A : Finset ℕ) (s M' : ℕ) (R S : Finset ℕ) (k : ℕ) :
    ind A s M' (R ∪ S) k = ind A s M' R k * ind A s M' S k := by
  simp only [ind, Finset.forall_mem_union]
  split_ifs <;> simp_all

theorem block_lhs (A : Finset ℕ) (s M' : ℕ) (R P : Finset ℕ) (c : ℕ → ℝ) (F : ℕ → ℝ) (L : ℕ) :
    ∑ k ∈ range L, ind A s M' R k * (F k * phi A s M' P c k) =
      ∑ S ∈ P.powerset, c S.card * ∑ k ∈ range L, ind A s M' (R ∪ S) k * F k := by
  have h : ∀ k, ind A s M' R k * (F k * phi A s M' P c k) =
      ∑ S ∈ P.powerset, c S.card * (ind A s M' (R ∪ S) k * F k) := by
    intro k
    simp only [phi, Finset.mul_sum, ind_union]
    refine Finset.sum_congr rfl (fun S _ => ?_)
    ring
  simp only [h, Finset.mul_sum]
  exact Finset.sum_comm

theorem block_rhs (g : ℝ) (R P : Finset ℕ) (hRP : Disjoint R P) (c : ℕ → ℝ) (δ X : ℝ) :
    X * (∏ b ∈ R, (g / (b : ℝ))) * (δ * dens g P c) =
      ∑ S ∈ P.powerset, c S.card * (X * (∏ b ∈ R ∪ S, (g / (b : ℝ))) * δ) := by
  simp only [dens, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun S hS => ?_)
  rw [Finset.prod_union (Finset.disjoint_of_subset_right (Finset.mem_powerset.mp hS) hRP)]
  ring

theorem block_err (g : ℝ) (R P : Finset ℕ) (hRP : Disjoint R P) (c : ℕ → ℝ) (E : ℝ) :
    ∑ S ∈ P.powerset, |c S.card| * (g ^ (R ∪ S).card * E) = g ^ R.card * (E * mass g P c) := by
  simp only [mass, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun S hS => ?_)
  rw [Finset.card_union_of_disjoint (Finset.disjoint_of_subset_right (Finset.mem_powerset.mp hS) hRP),
    pow_add]
  ring

theorem block_step (A : Finset ℕ) (s M' : ℕ) (R P : Finset ℕ) (hRP : Disjoint R P) (c : ℕ → ℝ)
    (F : ℕ → ℝ) (δ E : ℝ) (L : ℕ)
    (h : ∀ S, S ⊆ P → |∑ k ∈ range L, ind A s M' (R ∪ S) k * F k
        - L * (∏ b ∈ R ∪ S, ((A.card : ℝ) / (b : ℝ))) * δ| ≤ (A.card : ℝ) ^ (R ∪ S).card * E) :
    |∑ k ∈ range L, ind A s M' R k * (F k * phi A s M' P c k)
        - L * (∏ b ∈ R, ((A.card : ℝ) / (b : ℝ))) * (δ * dens A.card P c)| ≤
      (A.card : ℝ) ^ R.card * (E * mass A.card P c) := by
  rw [block_lhs, block_rhs _ _ _ hRP, ← block_err _ _ _ hRP, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun S hS => ?_)
  rw [← mul_sub, abs_mul]
  exact mul_le_mul_of_nonneg_left (h S (Finset.mem_powerset.mp hS)) (abs_nonneg _)

theorem prod_main (A : Finset ℕ) (N s M' : ℕ) (W : Finset ℕ) (hadm : Adm A N M' W)
    (P : ℕ → Finset ℕ) (hPW : ∀ j, P j ⊆ W) (hdisj : ∀ i j, i ≠ j → Disjoint (P i) (P j))
    (c : ℕ → ℕ → ℝ) (L n : ℕ) (R : Finset ℕ) (hR : R ⊆ W) (hRP : ∀ j, j < n → Disjoint R (P j)) :
    |∑ k ∈ range L, ind A s M' R k * ∏ j ∈ range n, phi A s M' (P j) (c j) k
        - L * (∏ b ∈ R, ((A.card : ℝ) / (b : ℝ))) * ∏ j ∈ range n, dens A.card (P j) (c j)| ≤
      (A.card : ℝ) ^ R.card * ∏ j ∈ range n, mass A.card (P j) (c j) := by
  induction n generalizing R with
  | zero =>
    simp only [Finset.prod_range_zero, mul_one]
    exact cnt_bound_range A N s M' W hadm R hR L
  | succ n ih =>
    simp only [Finset.prod_range_succ]
    exact block_step A s M' R (P n) (hRP n (Nat.lt_succ_self n)) (c n)
      (fun k => ∏ j ∈ range n, phi A s M' (P j) (c j) k)
      (∏ j ∈ range n, dens A.card (P j) (c j)) (∏ j ∈ range n, mass A.card (P j) (c j)) L
      (fun S hS => ih (R ∪ S) (Finset.union_subset hR (hS.trans (hPW n)))
        (fun j hj => Finset.disjoint_union_left.mpr
          ⟨hRP j (by omega), Finset.disjoint_of_subset_left hS (hdisj n j (by omega))⟩))

theorem sum_prod_phi (A : Finset ℕ) (N s M' : ℕ) (W : Finset ℕ) (hadm : Adm A N M' W)
    (P : ℕ → Finset ℕ) (hPW : ∀ j, P j ⊆ W) (hdisj : ∀ i j, i ≠ j → Disjoint (P i) (P j))
    (c : ℕ → ℕ → ℝ) (L n : ℕ) :
    |∑ k ∈ range L, ∏ j ∈ range n, phi A s M' (P j) (c j) k
        - L * ∏ j ∈ range n, dens A.card (P j) (c j)| ≤
      ∏ j ∈ range n, mass A.card (P j) (c j) := by
  have h := prod_main A N s M' W hadm P hPW hdisj c L n ∅ (Finset.empty_subset _)
    (fun j _ => Finset.disjoint_empty_left _)
  simpa [ind] using h

theorem phi_eq_sum (A : Finset ℕ) (s M' : ℕ) (P : Finset ℕ) (c : ℕ → ℝ) (k : ℕ) :
    phi A s M' P c k =
      ∑ S ∈ (P.filter (fun b => ∃ a ∈ A, b ∣ a + s + M' * k)).powerset, c S.card := by
  simp only [phi, ind, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  congr 1
  ext S
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_iff]
  constructor
  · rintro ⟨h1, h2⟩ x hx
    exact ⟨h1 hx, h2 x hx⟩
  · intro h
    exact ⟨fun x hx => (h hx).1, fun x hx => (h hx).2⟩

theorem phi_eq_choose (A : Finset ℕ) (s M' : ℕ) (P : Finset ℕ) (c : ℕ → ℝ) (k L : ℕ)
    (hL : nu A s M' P k ≤ L) :
    phi A s M' P c k = ∑ i ∈ range (L + 1), c i * ((nu A s M' P k).choose i : ℝ) := by
  have hc : (P.filter (fun b => ∃ a ∈ A, b ∣ a + s + M' * k)).card = nu A s M' P k := rfl
  have hsub : Finset.range (nu A s M' P k + 1) ⊆ Finset.range (L + 1) :=
    Finset.range_subset_range.mpr (by omega)
  rw [phi_eq_sum, Finset.sum_powerset_apply_card, hc, Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [nsmul_eq_mul, mul_comm]
  · intro i _ hi
    rw [Finset.mem_range, not_lt] at hi
    rw [Nat.choose_eq_zero_of_lt (show nu A s M' P k < i by omega), zero_smul]

theorem phiU_eq (A : Finset ℕ) (s M' : ℕ) (P : Finset ℕ) (m k : ℕ) :
    phi A s M' P (cU m) k = ∑ i ∈ range (m + 1), (-1 : ℝ) ^ i * ((nu A s M' P k).choose i : ℝ) := by
  have hL : nu A s M' P k ≤ nu A s M' P k + m := Nat.le_add_right _ _
  rw [phi_eq_choose A s M' P (cU m) k (nu A s M' P k + m) hL]
  have hsub : Finset.range (m + 1) ⊆ Finset.range (nu A s M' P k + m + 1) :=
    Finset.range_subset_range.mpr (by omega)
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl (fun i hi => ?_)
    have hi' : i ≤ m := by rw [Finset.mem_range] at hi; omega
    simp only [cU, if_pos hi']
  · intro i _ hi
    have hi' : ¬ i ≤ m := by rw [Finset.mem_range, not_lt] at hi; omega
    simp only [cU, if_neg hi', zero_mul]

theorem alt_choose_ge (m n : ℕ) (hm : Even m) :
    (if n = 0 then (1 : ℝ) else 0) ≤ ∑ i ∈ range (m + 1), (-1 : ℝ) ^ i * (n.choose i : ℝ) := by
  rcases n with _ | n
  · have hs : ∑ i ∈ range (m + 1), (-1 : ℝ) ^ i * ((0 : ℕ).choose i : ℝ) = 1 := by
      rw [Finset.sum_eq_single 0]
      · simp
      · intro b _ hb
        rw [Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hb)]
        simp
      · intro h
        exact absurd (Finset.mem_range.mpr (Nat.succ_pos m)) h
    rw [hs]; simp
  · have hs : ∑ i ∈ range (m + 1), (-1 : ℝ) ^ i * ((n + 1).choose i : ℝ) = (n.choose m : ℝ) := by
      have h2 := congrArg (Int.cast : ℤ → ℝ) (Int.alternating_sum_range_choose_eq_choose (n := n) (m := m))
      push_cast at h2
      simpa [hm.neg_one_pow] using h2
    rw [hs, if_neg (by omega : ¬ (n + 1 = 0))]
    exact Nat.cast_nonneg _

theorem ind_sift (A : Finset ℕ) (s M' : ℕ) (W : Finset ℕ) (P : ℕ → Finset ℕ) (n : ℕ)
    (hPW : ∀ j, P j ⊆ W) (hcov : ∀ b ∈ W, ∃ j, j < n ∧ b ∈ P j) (k : ℕ) :
    (if ∀ b ∈ W, ∀ a ∈ A, ¬ b ∣ a + s + M' * k then (1 : ℝ) else 0) =
      ∏ j ∈ range n, (if nu A s M' (P j) k = 0 then (1 : ℝ) else 0) := by
  have hiff : (∀ b ∈ W, ∀ a ∈ A, ¬ b ∣ a + s + M' * k) ↔ (∀ j ∈ range n, nu A s M' (P j) k = 0) := by
    constructor
    · intro h j _
      unfold nu
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro b hb hex
      obtain ⟨a, ha, hdiv⟩ := hex
      exact h b (hPW j hb) a ha hdiv
    · intro h b hb a ha hdiv
      obtain ⟨j, hj, hbj⟩ := hcov b hb
      have h0 := h j (Finset.mem_range.mpr hj)
      have hpos : 0 < nu A s M' (P j) k := by
        unfold nu
        apply Finset.card_pos.mpr
        exact ⟨b, Finset.mem_filter.mpr ⟨hbj, a, ha, hdiv⟩⟩
      omega
  rw [Finset.prod_boole]
  by_cases h : ∀ b ∈ W, ∀ a ∈ A, ¬ b ∣ a + s + M' * k
  · rw [if_pos h, if_pos (hiff.mp h)]
  · rw [if_neg h, if_neg (fun h' => h (hiff.mpr h'))]

theorem sieve_upper (A : Finset ℕ) (N s M' : ℕ) (W : Finset ℕ) (hadm : Adm A N M' W)
    (P : ℕ → Finset ℕ) (n : ℕ) (hPW : ∀ j, P j ⊆ W)
    (hdisj : ∀ i j, i ≠ j → Disjoint (P i) (P j)) (hcov : ∀ b ∈ W, ∃ j, j < n ∧ b ∈ P j)
    (m : ℕ → ℕ) (hm : ∀ j, Even (m j)) (L : ℕ) :
    ((siftR A s M' W L).card : ℝ) ≤
      (L : ℝ) * ∏ j ∈ range n, dens A.card (P j) (cU (m j))
        + ∏ j ∈ range n, mass A.card (P j) (cU (m j)) := by
  have hpt : ∀ k ∈ range L,
      (if ∀ b ∈ W, ∀ a ∈ A, ¬ b ∣ a + s + M' * k then (1 : ℝ) else 0) ≤
        ∏ j ∈ range n, phi A s M' (P j) (cU (m j)) k := by
    intro k _
    rw [ind_sift A s M' W P n hPW hcov k]
    apply Finset.prod_le_prod
    · intro j _; split_ifs <;> norm_num
    · intro j _
      rw [phiU_eq]
      exact alt_choose_ge (m j) _ (hm j)
  have hsum : ((siftR A s M' W L).card : ℝ) ≤
      ∑ k ∈ range L, ∏ j ∈ range n, phi A s M' (P j) (cU (m j)) k := by
    unfold siftR
    rw [Finset.natCast_card_filter]
    exact Finset.sum_le_sum hpt
  have hphi := sum_prod_phi A N s M' W hadm P hPW hdisj (fun j => cU (m j)) L n
  linarith [(abs_le.mp hphi).2]

/- ## Remainder and main term bounds (adapted from H1) -/

theorem mass_nonneg (g : ℝ) (hg : 0 ≤ g) (P : Finset ℕ) (c : ℕ → ℝ) : 0 ≤ mass g P c := by
  unfold mass
  exact Finset.sum_nonneg (fun S _ => mul_nonneg (abs_nonneg _) (pow_nonneg hg _))

theorem mass_eq (g : ℝ) (P : Finset ℕ) (c : ℕ → ℝ) :
    mass g P c = ∑ i ∈ range (P.card + 1), (P.card.choose i : ℝ) * (|c i| * g ^ i) := by
  unfold mass
  rw [Finset.sum_powerset_apply_card (fun i => |c i| * g ^ i)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [nsmul_eq_mul]

theorem choose_sum_le (p m : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    ∑ i ∈ range (m + 2), (p.choose i : ℝ) * t ^ i ≤ (1 + t * p) ^ (m + 1) := by
  rw [add_comm 1, add_pow (t * (p : ℝ)) 1 (m + 1)]
  apply Finset.sum_le_sum
  intro i hi
  have hi' : i ≤ m + 1 := by rw [Finset.mem_range] at hi; omega
  have h1 : (p.choose i : ℝ) ≤ (p : ℝ) ^ i := by exact_mod_cast Nat.choose_le_pow p i
  have h2 : (1 : ℝ) ≤ ((m + 1).choose i : ℝ) := by exact_mod_cast Nat.choose_pos hi'
  have h3 : 0 ≤ t ^ i := pow_nonneg ht i
  have h4 : (p.choose i : ℝ) * t ^ i ≤ (p : ℝ) ^ i * t ^ i := mul_le_mul_of_nonneg_right h1 h3
  have h5 : t ^ i * (p : ℝ) ^ i * 1 ≤ t ^ i * (p : ℝ) ^ i * ((m + 1).choose i : ℝ) :=
    mul_le_mul_of_nonneg_left h2 (mul_nonneg h3 (pow_nonneg (Nat.cast_nonneg p) i))
  rw [one_pow, mul_one, mul_pow]
  nlinarith [h4, h5]

theorem mass_cU_le (g : ℝ) (hg : 0 ≤ g) (P : Finset ℕ) (m : ℕ) :
    mass g P (cU m) ≤ (1 + g * P.card) ^ (m + 1) := by
  have hterm : ∀ i, (P.card.choose i : ℝ) * (|cU m i| * g ^ i) =
      if i ≤ m then (P.card.choose i : ℝ) * g ^ i else 0 := by
    intro i
    unfold cU
    by_cases h1 : i ≤ m <;> simp [h1, abs_pow]
  rw [mass_eq]
  calc ∑ i ∈ range (P.card + 1), (P.card.choose i : ℝ) * (|cU m i| * g ^ i)
      = ∑ i ∈ range (P.card + 1), (if i ≤ m then (P.card.choose i : ℝ) * g ^ i else 0) :=
        Finset.sum_congr rfl (fun i _ => hterm i)
    _ = ∑ i ∈ (range (P.card + 1)).filter (fun i => i ≤ m), (P.card.choose i : ℝ) * g ^ i :=
        (Finset.sum_filter _ _).symm
    _ ≤ ∑ i ∈ range (m + 2), (P.card.choose i : ℝ) * g ^ i := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro i hi
          simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
          omega
        · intro i _ _
          exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hg _)
    _ ≤ (1 + g * (P.card : ℝ)) ^ (m + 1) := choose_sum_le P.card m g hg

theorem one_add_le (g Z : ℕ) (hZ : 2 ≤ Z) : 1 + g * Z ≤ Z ^ (g + 1) := by
  induction g with
  | zero => simp <;> omega
  | succ g ih =>
    have h1 : Z ≤ Z ^ (g + 1) := le_self_pow (by omega) (by omega)
    have h3 : 2 * Z ^ (g + 1) ≤ Z * Z ^ (g + 1) := Nat.mul_le_mul_right _ hZ
    have h4 : Z ^ (g + 1 + 1) = Z * Z ^ (g + 1) := by ring
    rw [h4]
    nlinarith [ih, h1, h3]

theorem wsum_le (c n : ℕ) :
    ∑ j ∈ range n, 2 ^ (j + 1) * (c + 2 * (n - j)) ≤ 2 ^ (n + 1) * (c + 4) := by
  have key : ∀ n : ℕ, (∑ j ∈ range n, 2 ^ (j + 1) * (c + 2 * (n - j))) + 2 * c + 4 * n + 8
      = 2 ^ (n + 1) * (c + 4) := by
    intro n
    induction n with
    | zero => simp <;> ring
    | succ n ih =>
      rw [Finset.sum_range_succ']
      have h : ∀ j ∈ range n, 2 ^ (j + 1 + 1) * (c + 2 * (n + 1 - (j + 1)))
          = 2 * (2 ^ (j + 1) * (c + 2 * (n - j))) := by
        intro j _
        have hj : n + 1 - (j + 1) = n - j := by omega
        rw [hj]; ring
      rw [Finset.sum_congr rfl h, ← Finset.mul_sum]
      simp only [Nat.sub_zero, zero_add, pow_one]
      rw [pow_succ 2 (n + 1)]
      nlinarith [ih]
  linarith [key n]

theorem mm_even (a n j : ℕ) : Even (mm a n j) := by
  unfold mm; exact even_two_mul _

theorem rem_factor (g a n j : ℕ) (P : Finset ℕ) (hP : P.card ≤ hi j) :
    (1 + (g : ℝ) * P.card) ^ (mm a n j + 1) ≤
      (2 : ℝ) ^ ((g + 1) * (2 ^ (j + 1) * ((2 * a + 1) + 2 * (n - j)))) := by
  have h2 : 2 ≤ hi j := by
    unfold hi
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ 2 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) Nat.one_le_two_pow
  have hn : 1 + g * P.card ≤ (hi j) ^ (g + 1) :=
    le_trans (Nat.add_le_add_left (Nat.mul_le_mul_left g hP) 1) (one_add_le g (hi j) h2)
  have hR : (1 + (g : ℝ) * P.card) ≤ ((hi j : ℕ) : ℝ) ^ (g + 1) := by exact_mod_cast hn
  have hmm : mm a n j + 1 = (2 * a + 1) + 2 * (n - j) := by unfold mm; omega
  have hhi : ((hi j : ℕ) : ℝ) = (2 : ℝ) ^ (2 ^ (j + 1)) := by unfold hi; norm_num
  calc (1 + (g : ℝ) * P.card) ^ (mm a n j + 1)
      ≤ (((hi j : ℕ) : ℝ) ^ (g + 1)) ^ (mm a n j + 1) :=
        pow_le_pow_left₀ (by positivity) hR _
    _ = (2 : ℝ) ^ (2 ^ (j + 1) * ((g + 1) * (mm a n j + 1))) := by
        rw [hhi, ← pow_mul, ← pow_mul]
    _ ≤ (2 : ℝ) ^ ((g + 1) * (2 ^ (j + 1) * ((2 * a + 1) + 2 * (n - j)))) := by
        apply pow_le_pow_right₀ (by norm_num)
        rw [← hmm]; apply le_of_eq; ring

theorem rem_bound (g a n : ℕ) (P : ℕ → Finset ℕ) (hP : ∀ j, (P j).card ≤ hi j) :
    ∏ j ∈ range n, (1 + (g : ℝ) * (P j).card) ^ (mm a n j + 1) ≤
      ((2 : ℝ) ^ 2 ^ n) ^ (2 * (g + 1) * (2 * a + 5)) := by
  have hE : ∑ j ∈ range n, (g + 1) * (2 ^ (j + 1) * ((2 * a + 1) + 2 * (n - j)))
      ≤ 2 ^ n * (2 * (g + 1) * (2 * a + 5)) := by
    rw [← Finset.mul_sum]
    calc (g + 1) * ∑ j ∈ range n, 2 ^ (j + 1) * ((2 * a + 1) + 2 * (n - j))
        ≤ (g + 1) * (2 ^ (n + 1) * (2 * a + 1 + 4)) :=
          Nat.mul_le_mul_left _ (wsum_le (2 * a + 1) n)
      _ = 2 ^ n * (2 * (g + 1) * (2 * a + 5)) := by ring
  calc ∏ j ∈ range n, (1 + (g : ℝ) * (P j).card) ^ (mm a n j + 1)
      ≤ ∏ j ∈ range n, (2 : ℝ) ^ ((g + 1) * (2 ^ (j + 1) * ((2 * a + 1) + 2 * (n - j)))) :=
        Finset.prod_le_prod (fun j _ => by positivity)
          (fun j _ => rem_factor g a n j (P j) (hP j))
    _ = (2 : ℝ) ^ (∑ j ∈ range n, (g + 1) * (2 ^ (j + 1) * ((2 * a + 1) + 2 * (n - j)))) := by
        rw [Finset.prod_pow_eq_pow_sum]
    _ ≤ (2 : ℝ) ^ (2 ^ n * (2 * (g + 1) * (2 * a + 5))) :=
        pow_le_pow_right₀ (by norm_num) hE
    _ = ((2 : ℝ) ^ 2 ^ n) ^ (2 * (g + 1) * (2 * a + 5)) := by rw [← pow_mul]

theorem esym_zero (t : ℕ → ℝ) (P : Finset ℕ) : esym t P 0 = 1 := by
  unfold esym; simp

theorem esym_insert (t : ℕ → ℝ) (P : Finset ℕ) (b : ℕ) (hb : b ∉ P) (i : ℕ) :
    esym t (insert b P) (i + 1) = esym t P (i + 1) + t b * esym t P i := by
  have hdisj : Disjoint (P.powersetCard (i + 1)) ((P.powersetCard i).image (insert b)) := by
    rw [Finset.disjoint_left]
    intro S hS hS'
    obtain ⟨T, _, rfl⟩ := Finset.mem_image.mp hS'
    exact hb ((Finset.mem_powersetCard.mp hS).1 (Finset.mem_insert_self b T))
  have hinj : Set.InjOn (insert b) ((P.powersetCard i : Finset (Finset ℕ)) : Set (Finset ℕ)) := by
    intro T hT T' hT' h
    have hTb : b ∉ T := fun h' => hb ((Finset.mem_powersetCard.mp (Finset.mem_coe.mp hT)).1 h')
    have hT'b : b ∉ T' := fun h' => hb ((Finset.mem_powersetCard.mp (Finset.mem_coe.mp hT')).1 h')
    have h1 : (insert b T).erase b = (insert b T').erase b := by rw [h]
    rwa [Finset.erase_insert hTb, Finset.erase_insert hT'b] at h1
  unfold esym
  rw [Finset.powersetCard_succ_insert hb, Finset.sum_union hdisj, Finset.sum_image hinj,
    Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro T hT
  have hTb : b ∉ T := fun h' => hb ((Finset.mem_powersetCard.mp hT).1 h')
  rw [Finset.prod_insert hTb]

theorem esym_nonneg (t : ℕ → ℝ) (P : Finset ℕ) (ht : ∀ b ∈ P, 0 ≤ t b) (i : ℕ) :
    0 ≤ esym t P i := by
  unfold esym
  apply Finset.sum_nonneg
  intro S hS
  apply Finset.prod_nonneg
  intro b hb
  exact ht b ((Finset.mem_powersetCard.mp hS).1 hb)

theorem dens_eq (g : ℝ) (P : Finset ℕ) (c : ℕ → ℝ) :
    dens g P c = ∑ i ∈ range (P.card + 1), c i * esym (fun b => g / (b : ℝ)) P i := by
  unfold dens esym
  have hmaps : ∀ S ∈ P.powerset, S.card ∈ range (P.card + 1) := fun S hS => by
    rw [Finset.mem_range]
    have := Finset.card_le_card (Finset.mem_powerset.mp hS)
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.powersetCard_eq_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  rw [(Finset.mem_powersetCard.mp hS).2]

theorem dens_cU (g : ℝ) (P : Finset ℕ) (m : ℕ) :
    dens g P (cU m) = ∑ i ∈ range (m + 1), (-1 : ℝ) ^ i * esym (fun b => g / (b : ℝ)) P i := by
  have hz : ∀ x, P.card < x → esym (fun b => g / (b : ℝ)) P x = 0 := by
    intro x hx
    unfold esym
    rw [Finset.powersetCard_eq_empty.mpr hx, Finset.sum_empty]
  rw [dens_eq]
  calc ∑ i ∈ range (P.card + 1), cU m i * esym (fun b => g / (b : ℝ)) P i
      = ∑ i ∈ range (P.card + m + 2), cU m i * esym (fun b => g / (b : ℝ)) P i := by
        apply Finset.sum_subset
        · intro x hx; simp only [Finset.mem_range] at hx ⊢; omega
        · intro x _ hx; simp only [Finset.mem_range, not_lt] at hx; rw [hz x (by omega), mul_zero]
    _ = ∑ i ∈ range (m + 1), cU m i * esym (fun b => g / (b : ℝ)) P i := by
        symm
        apply Finset.sum_subset
        · intro x hx; simp only [Finset.mem_range] at hx ⊢; omega
        · intro x _ hx; simp only [Finset.mem_range, not_lt] at hx
          simp [cU, show ¬ x ≤ m by omega]
    _ = ∑ i ∈ range (m + 1), (-1 : ℝ) ^ i * esym (fun b => g / (b : ℝ)) P i := by
        apply Finset.sum_congr rfl
        intro x hx
        have hx' : x ≤ m := by simp only [Finset.mem_range] at hx; omega
        simp [cU, hx']

theorem dens_cE (g : ℝ) (P : Finset ℕ) (m : ℕ) :
    dens g P (cE m) = esym (fun b => g / (b : ℝ)) P (m + 1) := by
  rw [dens_eq, Finset.sum_eq_single (m + 1)]
  · simp [cE]
  · intro i _ hi; simp [cE, hi]
  · intro hn
    have hn' : P.card < m + 1 := by simp only [Finset.mem_range, not_lt] at hn; omega
    unfold esym
    rw [Finset.powersetCard_eq_empty.mpr hn', Finset.sum_empty]
    simp

theorem altsum_insert (t : ℕ → ℝ) (P : Finset ℕ) (b : ℕ) (hb : b ∉ P) (m : ℕ) :
    ∑ i ∈ range (m + 2), (-1 : ℝ) ^ i * esym t (insert b P) i =
      ∑ i ∈ range (m + 2), (-1 : ℝ) ^ i * esym t P i
        - t b * ∑ i ∈ range (m + 1), (-1 : ℝ) ^ i * esym t P i := by
  have e1 : ∑ i ∈ range (m + 1), (-1 : ℝ) ^ (i + 1) * esym t (insert b P) (i + 1)
      = ∑ i ∈ range (m + 1), (-1 : ℝ) ^ (i + 1) * esym t P (i + 1)
        - t b * ∑ i ∈ range (m + 1), (-1 : ℝ) ^ i * esym t P i := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [esym_insert t P b hb i]
    ring
  rw [show m + 2 = m + 1 + 1 from rfl]
  rw [Finset.sum_range_succ' (fun i => (-1 : ℝ) ^ i * esym t (insert b P) i) (m + 1),
    Finset.sum_range_succ' (fun i => (-1 : ℝ) ^ i * esym t P i) (m + 1)]
  rw [e1]
  simp only [esym_zero]
  ring

theorem bonf_aux1 (t : ℕ → ℝ) (i : ℕ) : esym t ∅ (i + 1) = 0 := by
  unfold esym
  rw [Finset.powersetCard_eq_empty.mpr (show (∅ : Finset ℕ).card < i + 1 by simp)]
  simp

theorem bonf_aux2 (t : ℕ → ℝ) (m : ℕ) :
    ∑ i ∈ range (m + 1), (-1 : ℝ) ^ i * esym t ∅ i = 1 := by
  rw [Finset.sum_range_succ']
  simp [bonf_aux1, esym_zero]

theorem bonf (t : ℕ → ℝ) (P : Finset ℕ) (ht : ∀ b ∈ P, 0 ≤ t b ∧ t b ≤ 1) (m : ℕ) :
    (Even m → ∏ b ∈ P, (1 - t b) ≤ ∑ i ∈ range (m + 1), (-1 : ℝ) ^ i * esym t P i) ∧
      (Odd m → ∑ i ∈ range (m + 1), (-1 : ℝ) ^ i * esym t P i ≤ ∏ b ∈ P, (1 - t b)) := by
  revert ht m
  refine Finset.induction_on P ?_ ?_
  · intro ht m
    rw [Finset.prod_empty, bonf_aux2]
    exact ⟨fun _ => le_rfl, fun _ => le_rfl⟩
  · intro b P hb ih ht m
    have htb : 0 ≤ t b ∧ t b ≤ 1 := ht b (Finset.mem_insert_self b P)
    have hPt : ∀ c ∈ P, 0 ≤ t c ∧ t c ≤ 1 := fun c hc => ht c (Finset.mem_insert_of_mem hc)
    rw [Finset.prod_insert hb]
    have hP1 : ∏ c ∈ P, (1 - t c) ≤ 1 :=
      Finset.prod_le_one (fun c hc => by linarith [(hPt c hc).2])
        (fun c hc => by linarith [(hPt c hc).1])
    have hP0 : 0 ≤ ∏ c ∈ P, (1 - t c) :=
      Finset.prod_nonneg (fun c hc => by linarith [(hPt c hc).2])
    cases m with
    | zero =>
      simp only [zero_add, Finset.sum_range_one, esym_zero, pow_zero, one_mul]
      refine ⟨fun _ => ?_, fun h => absurd (Nat.odd_iff.mp h) (by norm_num)⟩
      nlinarith [mul_nonneg htb.1 hP0]
    | succ m' =>
      have hA : ∑ i ∈ range (m' + 1 + 1), (-1 : ℝ) ^ i * esym t (insert b P) i =
          ∑ i ∈ range (m' + 1 + 1), (-1 : ℝ) ^ i * esym t P i
            - t b * ∑ i ∈ range (m' + 1), (-1 : ℝ) ^ i * esym t P i :=
        altsum_insert t P b hb m'
      have ihA := ih hPt (m' + 1)
      have ihB := ih hPt m'
      rw [hA]
      rcases Nat.even_or_odd m' with he | ho
      · have hodd : Odd (m' + 1) := he.add_one
        refine ⟨fun h => absurd h (Nat.not_even_iff_odd.mpr hodd), fun _ => ?_⟩
        nlinarith [ihA.2 hodd, ihB.1 he, mul_nonneg htb.1 (sub_nonneg.2 (ihB.1 he))]
      · have hev : Even (m' + 1) := ho.add_one
        refine ⟨fun _ => ?_, fun h => absurd h (Nat.not_odd_iff_even.mpr hev)⟩
        nlinarith [ihA.1 hev, ihB.2 ho, mul_nonneg htb.1 (sub_nonneg.2 (ihB.2 ho))]

theorem pow_succ_add_le (s u : ℝ) (hs : 0 ≤ s) (hu : 0 ≤ u) (i : ℕ) :
    s ^ (i + 1) + (i + 1) * u * s ^ i ≤ (s + u) ^ (i + 1) := by
  induction i with
  | zero => simp
  | succ k ih =>
    push_cast
    have h1 := mul_le_mul_of_nonneg_right ih (add_nonneg hs hu)
    have h2 : 0 ≤ ((k : ℝ) + 1) * u * u * s ^ k := by positivity
    have e1 : (s + u) ^ (k + 1 + 1) = (s + u) ^ (k + 1) * (s + u) := pow_succ _ _
    have e2 : s ^ (k + 1 + 1) = s ^ k * s * s := by ring
    have e3 : s ^ (k + 1) = s ^ k * s := by ring
    rw [e3] at h1
    rw [e1, e2, e3]
    nlinarith [h1, h2]

theorem esym_le (t : ℕ → ℝ) (P : Finset ℕ) (ht : ∀ b ∈ P, 0 ≤ t b) (i : ℕ) :
    esym t P i ≤ (∑ b ∈ P, t b) ^ i / (i.factorial : ℝ) := by
  revert ht i
  refine Finset.induction_on P ?_ ?_
  · intro ht i
    cases i with
    | zero => simp [esym_zero]
    | succ k => rw [bonf_aux1]; simp
  · intro b P hb ih ht i
    have htb : 0 ≤ t b := ht b (Finset.mem_insert_self b P)
    have hPt : ∀ c ∈ P, 0 ≤ t c := fun c hc => ht c (Finset.mem_insert_of_mem hc)
    have hS : 0 ≤ ∑ c ∈ P, t c := Finset.sum_nonneg hPt
    rw [Finset.sum_insert hb]
    cases i with
    | zero => simp [esym_zero]
    | succ k =>
      rw [esym_insert t P b hb k]
      have ih1 := ih hPt (k + 1)
      have ih0 := ih hPt k
      have key := pow_succ_add_le (∑ c ∈ P, t c) (t b) hS htb k
      have hF : (0 : ℝ) < ((k + 1).factorial : ℝ) := by positivity
      have hk : (0 : ℝ) < (k.factorial : ℝ) := by positivity
      have hfac : ((k + 1).factorial : ℝ) = ((k : ℝ) + 1) * (k.factorial : ℝ) := by
        rw [Nat.factorial_succ]; push_cast; ring
      have eq1 : (∑ c ∈ P, t c) ^ (k + 1) / ((k + 1).factorial : ℝ)
          + t b * ((∑ c ∈ P, t c) ^ k / (k.factorial : ℝ))
          = ((∑ c ∈ P, t c) ^ (k + 1) + ((k : ℝ) + 1) * t b * (∑ c ∈ P, t c) ^ k)
              / ((k + 1).factorial : ℝ) := by
        rw [hfac]; field_simp
      have hle : ((∑ c ∈ P, t c) ^ (k + 1) + ((k : ℝ) + 1) * t b * (∑ c ∈ P, t c) ^ k)
            / ((k + 1).factorial : ℝ)
          ≤ (t b + ∑ c ∈ P, t c) ^ (k + 1) / ((k + 1).factorial : ℝ) := by
        refine div_le_div_of_nonneg_right ?_ hF.le
        rw [add_comm (t b) (∑ c ∈ P, t c)]
        exact key
      calc esym t P (k + 1) + t b * esym t P k
          ≤ (∑ c ∈ P, t c) ^ (k + 1) / ((k + 1).factorial : ℝ)
              + t b * ((∑ c ∈ P, t c) ^ k / (k.factorial : ℝ)) :=
            add_le_add ih1 (mul_le_mul_of_nonneg_left ih0 htb)
        _ = _ := eq1
        _ ≤ _ := hle

theorem one_sub_ge_exp (G t : ℝ) (hG : 0 ≤ G) (ht : 0 ≤ t) (h : t * (G + 1) ≤ G) :
    Real.exp (-((G + 1) * t)) ≤ 1 - t := by
  have h1 : 0 ≤ 1 - t := by nlinarith
  have h2 := Real.add_one_le_exp ((G + 1) * t)
  have key : 1 ≤ (1 - t) * Real.exp ((G + 1) * t) := by
    nlinarith [mul_le_mul_of_nonneg_left h2 h1, mul_nonneg ht (sub_nonneg.mpr h)]
  rw [Real.exp_neg, inv_eq_one_div, div_le_iff₀ (Real.exp_pos _)]
  linarith

theorem V_ge_exp (G : ℝ) (hG : 0 ≤ G) (t : ℕ → ℝ) (P : Finset ℕ)
    (ht : ∀ b ∈ P, 0 ≤ t b ∧ t b * (G + 1) ≤ G) :
    Real.exp (-((G + 1) * ∑ b ∈ P, t b)) ≤ ∏ b ∈ P, (1 - t b) := by
  have hsum : -((G + 1) * ∑ b ∈ P, t b) = ∑ b ∈ P, -((G + 1) * t b) := by
    rw [Finset.mul_sum, Finset.sum_neg_distrib]
  rw [hsum, Real.exp_sum]
  exact Finset.prod_le_prod (fun b _ => Real.exp_nonneg _)
    (fun b hb => one_sub_ge_exp G (t b) hG (ht b hb).1 (ht b hb).2)

theorem block_V (A : Finset ℕ) (N M' : ℕ) (W : Finset ℕ) (hadm : Adm A N M' W) (P : Finset ℕ)
    (hP : P ⊆ W) (m : ℕ) (hm : Even m) :
    0 < ∏ b ∈ P, (1 - (A.card : ℝ) / (b : ℝ)) ∧
      ∏ b ∈ P, (1 - (A.card : ℝ) / (b : ℝ)) ≤ dens A.card P (cU m) := by
  have hbd : ∀ b ∈ P, (A.card : ℝ) < (b : ℝ) ∧ 0 < (b : ℝ) := by
    intro b hb
    have h1 : A.card < b := adm_card_lt A N M' W hadm b (hP hb)
    have h2 : (A.card : ℝ) < (b : ℝ) := by exact_mod_cast h1
    exact ⟨h2, lt_of_le_of_lt (Nat.cast_nonneg _) h2⟩
  constructor
  · apply Finset.prod_pos
    intro b hb
    have h3 : (A.card : ℝ) / (b : ℝ) < 1 := (div_lt_one (hbd b hb).2).mpr (hbd b hb).1
    linarith
  · rw [dens_cU]
    exact (bonf (fun b => (A.card : ℝ) / (b : ℝ)) P
      (fun b hb => ⟨div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _),
        (div_le_one (hbd b hb).2).mpr (hbd b hb).1.le⟩) m).1 hm

theorem block_dens_upper (A : Finset ℕ) (N M' : ℕ) (W : Finset ℕ) (hadm : Adm A N M' W)
    (P : Finset ℕ) (hP : P ⊆ W) (m' : ℕ) (hm' : Odd m') :
    dens A.card P (cU (m' + 1)) ≤
      ∏ b ∈ P, (1 - (A.card : ℝ) / (b : ℝ)) + dens A.card P (cE m') := by
  have hbd : ∀ b ∈ P, 0 ≤ (A.card : ℝ) / (b : ℝ) ∧ (A.card : ℝ) / (b : ℝ) ≤ 1 := by
    intro b hb
    have h1 : A.card < b := adm_card_lt A N M' W hadm b (hP hb)
    have h2 : (A.card : ℝ) < (b : ℝ) := by exact_mod_cast h1
    have hb0 : (0 : ℝ) < (b : ℝ) := lt_of_le_of_lt (Nat.cast_nonneg _) h2
    exact ⟨div_nonneg (Nat.cast_nonneg _) hb0.le, (div_le_one hb0).mpr h2.le⟩
  rw [dens_cU, dens_cE, Finset.sum_range_succ]
  have hev : Even (m' + 1) := hm'.add_one
  rw [hev.neg_one_pow, one_mul]
  have hbonf := (bonf (fun b => (A.card : ℝ) / (b : ℝ)) P hbd m').2 hm'
  linarith

theorem block_eps_num (g : ℝ) (hg : 0 ≤ g) (P : Finset ℕ)
    (hsum : ∑ b ∈ P, (1 / (b : ℝ)) ≤ 18) (m : ℕ) :
    0 ≤ dens g P (cE m) ∧
      dens g P (cE m) ≤ (18 * g) ^ (m + 1) / ((m + 1).factorial : ℝ) := by
  have hnn : ∀ b ∈ P, 0 ≤ g / (b : ℝ) := fun b _ => div_nonneg hg (Nat.cast_nonneg _)
  rw [dens_cE]
  refine ⟨esym_nonneg _ P hnn (m + 1), ?_⟩
  have e : ∑ b ∈ P, g / (b : ℝ) = g * ∑ b ∈ P, 1 / (b : ℝ) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro b _; ring
  have hs : ∑ b ∈ P, g / (b : ℝ) ≤ 18 * g := by
    rw [e]; have := mul_le_mul_of_nonneg_left hsum hg; linarith
  have hs0 : 0 ≤ ∑ b ∈ P, g / (b : ℝ) := Finset.sum_nonneg hnn
  calc esym (fun b => g / (b : ℝ)) P (m + 1)
      ≤ (∑ b ∈ P, g / (b : ℝ)) ^ (m + 1) / ((m + 1).factorial : ℝ) := esym_le _ P hnn (m + 1)
    _ ≤ (18 * g) ^ (m + 1) / ((m + 1).factorial : ℝ) := by gcongr

theorem block_V_exp (A : Finset ℕ) (N M' : ℕ) (W : Finset ℕ) (hadm : Adm A N M' W)
    (P : Finset ℕ) (hP : P ⊆ W) (hsum : ∑ b ∈ P, (1 / (b : ℝ)) ≤ 18) :
    Real.exp (-(((A.card : ℝ) + 1) * (18 * (A.card : ℝ)))) ≤
      ∏ b ∈ P, (1 - (A.card : ℝ) / (b : ℝ)) := by
  have hcond : ∀ b ∈ P, 0 ≤ (A.card : ℝ) / (b : ℝ) ∧
      (A.card : ℝ) / (b : ℝ) * ((A.card : ℝ) + 1) ≤ (A.card : ℝ) := by
    intro b hb
    have h1 : A.card < b := adm_card_lt A N M' W hadm b (hP hb)
    have h3 : (A.card : ℝ) < (b : ℝ) := by exact_mod_cast h1
    have h2 : (A.card : ℝ) + 1 ≤ (b : ℝ) := by exact_mod_cast h1
    have hb0 : (0 : ℝ) < (b : ℝ) := lt_of_le_of_lt (Nat.cast_nonneg _) h3
    refine ⟨div_nonneg (Nat.cast_nonneg _) hb0.le, ?_⟩
    rw [div_mul_eq_mul_div, div_le_iff₀ hb0]
    exact mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _)
  have hV := V_ge_exp (A.card : ℝ) (Nat.cast_nonneg _) (fun b => (A.card : ℝ) / (b : ℝ)) P hcond
  have hsum' : ∑ b ∈ P, (A.card : ℝ) / (b : ℝ) ≤ 18 * (A.card : ℝ) := by
    have e : ∑ b ∈ P, (A.card : ℝ) / (b : ℝ) = (A.card : ℝ) * ∑ b ∈ P, 1 / (b : ℝ) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro b _; ring
    rw [e]
    have := mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg (α := ℝ) A.card)
    linarith
  have hle : Real.exp (-(((A.card : ℝ) + 1) * (18 * (A.card : ℝ)))) ≤
      Real.exp (-(((A.card : ℝ) + 1) * ∑ b ∈ P, (A.card : ℝ) / (b : ℝ))) := by
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_left hsum' (by positivity : (0 : ℝ) ≤ (A.card : ℝ) + 1)
    linarith
  exact le_trans hle hV

theorem block_eps (A : Finset ℕ) (N M' : ℕ) (W : Finset ℕ) (hadm : Adm A N M' W) (P : Finset ℕ)
    (hP : P ⊆ W) (hsum : ∑ b ∈ P, (1 / (b : ℝ)) ≤ 18) (m : ℕ) :
    0 ≤ dens A.card P (cE m) ∧
      dens A.card P (cE m) / ∏ b ∈ P, (1 - (A.card : ℝ) / (b : ℝ)) ≤
        (18 * (A.card : ℝ)) ^ (m + 1) / ((m + 1).factorial : ℝ) *
          Real.exp (((A.card : ℝ) + 1) * (18 * (A.card : ℝ))) := by
  obtain ⟨h0, hle⟩ := block_eps_num (A.card : ℝ) (Nat.cast_nonneg _) P hsum m
  have hV := block_V A N M' W hadm P hP 0 ⟨0, rfl⟩
  have hVe := block_V_exp A N M' W hadm P hP hsum
  refine ⟨h0, ?_⟩
  have h1 : Real.exp (((A.card : ℝ) + 1) * (18 * (A.card : ℝ))) *
      Real.exp (-(((A.card : ℝ) + 1) * (18 * (A.card : ℝ)))) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have h2 : 1 ≤ Real.exp (((A.card : ℝ) + 1) * (18 * (A.card : ℝ))) *
      ∏ b ∈ P, (1 - (A.card : ℝ) / (b : ℝ)) := by
    have := mul_le_mul_of_nonneg_left hVe (Real.exp_pos (((A.card : ℝ) + 1) * (18 * (A.card : ℝ)))).le
    linarith
  have hQ : 0 ≤ (18 * (A.card : ℝ)) ^ (m + 1) / ((m + 1).factorial : ℝ) := by positivity
  rw [div_le_iff₀ hV.1]
  calc dens (A.card : ℝ) P (cE m)
      ≤ (18 * (A.card : ℝ)) ^ (m + 1) / ((m + 1).factorial : ℝ) := hle
    _ ≤ (18 * (A.card : ℝ)) ^ (m + 1) / ((m + 1).factorial : ℝ) *
          (Real.exp (((A.card : ℝ) + 1) * (18 * (A.card : ℝ))) *
            ∏ b ∈ P, (1 - (A.card : ℝ) / (b : ℝ))) := le_mul_of_one_le_right hQ h2
    _ = (18 * (A.card : ℝ)) ^ (m + 1) / ((m + 1).factorial : ℝ) *
          Real.exp (((A.card : ℝ) + 1) * (18 * (A.card : ℝ))) *
            ∏ b ∈ P, (1 - (A.card : ℝ) / (b : ℝ)) := by ring

/- ## Sparsity of pairwise coprime moduli (adapted from H1) -/

theorem lcmUpto_le (n : ℕ) : (Nat.lcmUpto n : ℝ) ≤ Real.exp (6 * (n : ℝ)) := by
  have hpos : (0 : ℝ) < (Nat.lcmUpto n : ℝ) := by exact_mod_cast Nat.lcmUpto_pos n
  rw [← Real.exp_log hpos]
  apply Real.exp_le_exp.mpr
  rw [← Chebyshev.psi_eq_log_lcmUpto]
  have h := Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg (α := ℝ) n)
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have h2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have h4 : Real.log 4 + 4 ≤ 6 := by
    have : (0.6931471808 : ℝ) < 1 := by norm_num
    linarith
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith [mul_le_mul_of_nonneg_right h4 hn]

theorem prod_dvd_lcmUpto (W : Finset ℕ) (hco : (W : Set ℕ).Pairwise Nat.Coprime) (n : ℕ)
    (hW : ∀ b ∈ W, 1 ≤ b ∧ b ≤ n) : (∏ b ∈ W, b) ∣ Nat.lcmUpto n := by
  have hrel : (W : Set ℕ).Pairwise (fun a b : ℕ => IsRelPrime a b) := fun a ha b hb hab =>
    Nat.coprime_iff_isRelPrime.mp (hco ha hb hab)
  have hdvd : ∀ b ∈ W, (fun b : ℕ => b) b ∣ Nat.lcmUpto n := by
    intro b hb
    unfold Nat.lcmUpto
    exact Finset.dvd_lcm (Finset.mem_Icc.mpr (hW b hb))
  exact Finset.prod_dvd_of_isRelPrime hrel hdvd

theorem dyadic_card (W : Finset ℕ) (hco : (W : Set ℕ).Pairwise Nat.Coprime) (i : ℕ)
    (hW : ∀ b ∈ W, 2 ^ i < b ∧ b ≤ 2 ^ (i + 1)) : (W.card : ℝ) * i ≤ 18 * 2 ^ i := by
  have hW' : ∀ b ∈ W, 1 ≤ b ∧ b ≤ 2 ^ (i + 1) := fun b hb =>
    ⟨Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le _) (hW b hb).1), (hW b hb).2⟩
  have hnat : (2 ^ i) ^ W.card ≤ Nat.lcmUpto (2 ^ (i + 1)) := by
    calc (2 ^ i) ^ W.card ≤ ∏ b ∈ W, b :=
          Finset.pow_card_le_prod W (fun b => b) (2 ^ i) (fun b hb => (hW b hb).1.le)
      _ ≤ Nat.lcmUpto (2 ^ (i + 1)) :=
          Nat.le_of_dvd (Nat.lcmUpto_pos _) (prod_dvd_lcmUpto W hco _ hW')
  have hreal : ((2 : ℝ) ^ i) ^ W.card ≤ Real.exp (6 * (2 : ℝ) ^ (i + 1)) := by
    have h2 : (((2 ^ i) ^ W.card : ℕ) : ℝ) ≤ (Nat.lcmUpto (2 ^ (i + 1)) : ℝ) := by
      exact_mod_cast hnat
    have h3 := lcmUpto_le (2 ^ (i + 1))
    push_cast at h2 h3
    exact le_trans h2 h3
  have hlog := Real.log_le_log (by positivity) hreal
  rw [Real.log_pow, Real.log_exp, Real.log_pow] at hlog
  have e : (2 : ℝ) ^ (i + 1) = 2 * 2 ^ i := by ring
  rw [e] at hlog
  have hl2 : (2 : ℝ) / 3 < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
  have hc : 0 ≤ (W.card : ℝ) * i := by positivity
  have h3 : (W.card : ℝ) * i * (2 / 3) ≤ (W.card : ℝ) * i * Real.log 2 :=
    mul_le_mul_of_nonneg_left hl2.le hc
  nlinarith

theorem dyadic_sum (W : Finset ℕ) (hco : (W : Set ℕ).Pairwise Nat.Coprime) (i : ℕ) (hi : 1 ≤ i)
    (hW : ∀ b ∈ W, 2 ^ i < b ∧ b ≤ 2 ^ (i + 1)) : ∑ b ∈ W, (1 / (b : ℝ)) ≤ 18 / i := by
  have hi' : (1 : ℝ) ≤ i := by exact_mod_cast hi
  have hc := dyadic_card W hco i hW
  have hpos : (0 : ℝ) < 2 ^ i := by positivity
  have hle : ∀ b ∈ W, 1 / (b : ℝ) ≤ 1 / (2 : ℝ) ^ i := by
    intro b hb
    have h1 : (2 : ℝ) ^ i < b := by exact_mod_cast (hW b hb).1
    exact one_div_le_one_div_of_le hpos h1.le
  have hsum := Finset.sum_le_card_nsmul W (fun b => 1 / (b : ℝ)) (1 / (2 : ℝ) ^ i) hle
  rw [nsmul_eq_mul] at hsum
  have hfin : (W.card : ℝ) * (1 / (2 : ℝ) ^ i) ≤ 18 / i := by
    rw [mul_one_div, div_le_div_iff₀ hpos (by linarith)]
    linarith
  exact le_trans hsum hfin

theorem dyadic_cover (j b : ℕ) (h1 : 2 ^ 2 ^ j < b) (h2 : b ≤ 2 ^ 2 ^ (j + 1)) :
    ∃ i, i ∈ Ico (2 ^ j) (2 ^ (j + 1)) ∧ 2 ^ i < b ∧ b ≤ 2 ^ (i + 1) := by
  have hp1 : 1 ≤ 2 ^ 2 ^ j := Nat.one_le_two_pow
  have hx1 : 2 ^ 2 ^ j ≤ b - 1 := by omega
  have hx0 : b - 1 ≠ 0 := by omega
  have hA : 2 ^ Nat.log 2 (b - 1) ≤ b - 1 := Nat.pow_log_le_self 2 hx0
  have hB : b - 1 < 2 ^ (Nat.log 2 (b - 1) + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have hi1 : 2 ^ j < Nat.log 2 (b - 1) + 1 :=
    (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℕ) < 2)).mp (lt_of_le_of_lt hx1 hB)
  have hi2 : Nat.log 2 (b - 1) < 2 ^ (j + 1) :=
    (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℕ) < 2)).mp
      (lt_of_le_of_lt hA (lt_of_lt_of_le (by omega) h2))
  exact ⟨Nat.log 2 (b - 1), Finset.mem_Ico.mpr ⟨by omega, hi2⟩, by omega, by omega⟩

theorem dyadic_split (j b : ℕ) (h1 : 2 ^ 2 ^ j < b) (h2 : b ≤ 2 ^ 2 ^ (j + 1)) (f : ℝ)
    (hf : 0 ≤ f) :
    f ≤ ∑ i ∈ Ico (2 ^ j) (2 ^ (j + 1)), (if 2 ^ i < b ∧ b ≤ 2 ^ (i + 1) then f else 0) := by
  obtain ⟨i, hI, hlt, hle⟩ := dyadic_cover j b h1 h2
  calc f = (if 2 ^ i < b ∧ b ≤ 2 ^ (i + 1) then f else 0) := by rw [if_pos ⟨hlt, hle⟩]
    _ ≤ ∑ i ∈ Ico (2 ^ j) (2 ^ (j + 1)), (if 2 ^ i < b ∧ b ≤ 2 ^ (i + 1) then f else 0) :=
      Finset.single_le_sum (f := fun i => if 2 ^ i < b ∧ b ≤ 2 ^ (i + 1) then f else 0)
        (fun k _ => by split_ifs <;> linarith) hI

theorem superdyadic_sum (W : Finset ℕ) (hco : (W : Set ℕ).Pairwise Nat.Coprime) (j : ℕ)
    (hW : ∀ b ∈ W, 2 ^ 2 ^ j < b ∧ b ≤ 2 ^ 2 ^ (j + 1)) : ∑ b ∈ W, (1 / (b : ℝ)) ≤ 18 := by
  have hstep : ∀ b ∈ W, (1 / (b : ℝ)) ≤ ∑ i ∈ Ico (2 ^ j) (2 ^ (j + 1)),
      (if 2 ^ i < b ∧ b ≤ 2 ^ (i + 1) then (1 / (b : ℝ)) else 0) := by
    intro b hb
    exact dyadic_split j b (hW b hb).1 (hW b hb).2 _ (by positivity)
  have hsum : ∑ b ∈ W, (1 / (b : ℝ)) ≤ ∑ b ∈ W, ∑ i ∈ Ico (2 ^ j) (2 ^ (j + 1)),
      (if 2 ^ i < b ∧ b ≤ 2 ^ (i + 1) then (1 / (b : ℝ)) else 0) :=
    Finset.sum_le_sum hstep
  rw [Finset.sum_comm] at hsum
  have hblock : ∀ i ∈ Ico (2 ^ j) (2 ^ (j + 1)),
      ∑ b ∈ W, (if 2 ^ i < b ∧ b ≤ 2 ^ (i + 1) then (1 / (b : ℝ)) else 0) ≤ 18 / 2 ^ j := by
    intro i hI
    have hI' : 2 ^ j ≤ i := (Finset.mem_Ico.mp hI).1
    have hpos : 1 ≤ i := le_trans Nat.one_le_two_pow hI'
    have hd := dyadic_sum (W.filter (fun b => 2 ^ i < b ∧ b ≤ 2 ^ (i + 1)))
      (Set.Pairwise.mono (Finset.coe_subset.mpr (Finset.filter_subset _ _)) hco) i hpos
      (fun b hb => (Finset.mem_filter.mp hb).2)
    rw [← Finset.sum_filter]
    have hcast : (2 : ℝ) ^ j ≤ (i : ℝ) := by exact_mod_cast hI'
    calc ∑ b ∈ W.filter (fun b => 2 ^ i < b ∧ b ≤ 2 ^ (i + 1)), (1 / (b : ℝ))
        ≤ 18 / (i : ℝ) := hd
      _ ≤ 18 / 2 ^ j := div_le_div_of_nonneg_left (by norm_num) (by positivity) hcast
  have hc : 2 ^ (j + 1) - 2 ^ j = 2 ^ j := by rw [pow_succ]; omega
  calc ∑ b ∈ W, (1 / (b : ℝ))
      ≤ ∑ i ∈ Ico (2 ^ j) (2 ^ (j + 1)), ∑ b ∈ W,
          (if 2 ^ i < b ∧ b ≤ 2 ^ (i + 1) then (1 / (b : ℝ)) else 0) := hsum
    _ ≤ ∑ i ∈ Ico (2 ^ j) (2 ^ (j + 1)), (18 / 2 ^ j : ℝ) := Finset.sum_le_sum hblock
    _ = 18 := by
      rw [Finset.sum_const, Nat.card_Ico, hc, nsmul_eq_mul]
      push_cast; field_simp

theorem blk_sum (A : Finset ℕ) (N M' : ℕ) (W : Finset ℕ) (hadm : Adm A N M' W) (j : ℕ) :
    ∑ b ∈ blk W j, (1 / (b : ℝ)) ≤ 18 := by
  have hsub : blk W j ⊆ W := Finset.filter_subset _ _
  have hco : (blk W j : Set ℕ).Pairwise Nat.Coprime :=
    Set.Pairwise.mono (Finset.coe_subset.mpr hsub) hadm.2.1
  rcases Nat.eq_zero_or_pos j with hj | hj
  · subst hj
    have hlo0 : lo 0 = 0 := by unfold lo; rw [if_pos rfl]
    have hhi0 : hi 0 = 4 := by unfold hi; norm_num
    have hI : blk W 0 ⊆ Icc 1 4 := by
      intro b hb
      unfold blk at hb
      obtain ⟨hbW, hb1, hb2⟩ := Finset.mem_filter.mp hb
      rw [hlo0] at hb1; rw [hhi0] at hb2
      have hN := (hadm.2.2 b hbW).1
      exact Finset.mem_Icc.mpr ⟨by omega, hb2⟩
    have hcard : (blk W 0).card ≤ 4 := by
      have h := Finset.card_le_card hI
      rw [Nat.card_Icc] at h; omega
    have hle1 : ∀ b ∈ blk W 0, 1 / (b : ℝ) ≤ 1 := by
      intro b hb
      have hbW := hsub hb
      have hN := (hadm.2.2 b hbW).1
      have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast (show 1 ≤ b by omega)
      rw [div_le_iff₀ (by linarith)]; linarith
    have h := Finset.sum_le_card_nsmul (blk W 0) (fun b => 1 / (b : ℝ)) 1 hle1
    rw [nsmul_eq_mul, mul_one] at h
    have hc : ((blk W 0).card : ℝ) ≤ 4 := by exact_mod_cast hcard
    linarith
  · have hlo : lo j = 2 ^ 2 ^ j := by unfold lo; rw [if_neg (by omega)]
    refine superdyadic_sum (blk W j) hco j (fun b hb => ?_)
    unfold blk at hb
    obtain ⟨_, hb1, hb2⟩ := Finset.mem_filter.mp hb
    rw [hlo] at hb1
    exact ⟨hb1, hb2⟩

theorem blk_sub (W : Finset ℕ) (j : ℕ) : blk W j ⊆ W := Finset.filter_subset _ _

theorem blk_disj (W : Finset ℕ) (i j : ℕ) (hij : i ≠ j) : Disjoint (blk W i) (blk W j) := by
  have key : ∀ p q : ℕ, p < q → Disjoint (blk W p) (blk W q) := by
    intro p q hpq
    rw [Finset.disjoint_left]
    intro b hbp hbq
    unfold blk at hbp hbq
    have h1 := (Finset.mem_filter.mp hbp).2.2
    have h2 := (Finset.mem_filter.mp hbq).2.1
    have hq : q ≠ 0 := by omega
    have hlo : lo q = 2 ^ 2 ^ q := by unfold lo; rw [if_neg hq]
    have hle : hi p ≤ lo q := by
      rw [hlo]; unfold hi
      have h3 : 2 ^ (p + 1) ≤ 2 ^ q := Nat.pow_le_pow_right (by norm_num) (by omega)
      exact Nat.pow_le_pow_right (by norm_num) h3
    omega
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · exact key i j h
  · exact (key j i h).symm

theorem blk_cover_aux1 (b : ℕ) (hb : 1 ≤ b) (m : ℕ) :
    b ≤ 2 ^ 2 ^ (m + 1) → ∃ j, j < m + 1 ∧ lo j < b ∧ b ≤ hi j := by
  induction m with
  | zero =>
    intro hm
    refine ⟨0, by norm_num, ?_, hm⟩
    show (if (0 : ℕ) = 0 then 0 else 2 ^ 2 ^ 0) < b
    rw [if_pos rfl]; omega
  | succ m ih =>
    intro hm
    by_cases h : b ≤ 2 ^ 2 ^ (m + 1)
    · obtain ⟨j, hj, h1, h2⟩ := ih h
      exact ⟨j, by omega, h1, h2⟩
    · refine ⟨m + 1, by omega, ?_, hm⟩
      unfold lo; rw [if_neg (by omega)]; omega

theorem blk_cover (W : Finset ℕ) (n : ℕ) (hn : 1 ≤ n) (hW : ∀ b ∈ W, 1 ≤ b ∧ b ≤ 2 ^ 2 ^ n) :
    ∀ b ∈ W, ∃ j, j < n ∧ b ∈ blk W j := by
  intro b hb
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨j, hj, h1, h2⟩ := blk_cover_aux1 b (hW b hb).1 m (hW b hb).2
  exact ⟨j, hj, by unfold blk; exact Finset.mem_filter.mpr ⟨hb, h1, h2⟩⟩

theorem blk_card (W : Finset ℕ) (j : ℕ) : (blk W j).card ≤ hi j := by
  have hsub : blk W j ⊆ Ioc (lo j) (hi j) := by
    intro b hb
    unfold blk at hb
    rw [Finset.mem_filter] at hb
    exact Finset.mem_Ioc.mpr hb.2
  have h1 := Finset.card_le_card hsub
  rw [Nat.card_Ioc] at h1
  omega

theorem prod_blk (W : Finset ℕ) (n : ℕ) (hcov : ∀ b ∈ W, ∃ j, j < n ∧ b ∈ blk W j)
    (f : ℕ → ℝ) : ∏ j ∈ range n, ∏ b ∈ blk W j, f b = ∏ b ∈ W, f b := by
  have hU : (range n).biUnion (blk W) = W := by
    ext b
    constructor
    · intro hb
      obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hb
      exact blk_sub W j hj
    · intro hb
      obtain ⟨j, hj, hbj⟩ := hcov b hb
      exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hj, hbj⟩
  have hdisj : ((range n : Finset ℕ) : Set ℕ).PairwiseDisjoint (blk W) :=
    fun i _ j _ hij => blk_disj W i j hij
  conv_rhs => rw [← hU]
  rw [Finset.prod_biUnion hdisj]

theorem pow_fact_le (s : ℝ) (hs : 0 ≤ s) (q0 q : ℕ) (h0 : 2 * s ≤ q0) (hq : q0 ≤ q) :
    s ^ q / (q.factorial : ℝ) ≤ Real.exp s * 2 ^ q0 / 2 ^ q := by
  induction q, hq using Nat.le_induction with
  | base =>
    have h := Real.pow_div_factorial_le_exp s hs q0
    have e : Real.exp s * 2 ^ q0 / 2 ^ q0 = Real.exp s := by field_simp
    rw [e]; exact h
  | succ q hq ih =>
    have hfac : s ^ (q + 1) / ((q + 1).factorial : ℝ) = s ^ q / (q.factorial : ℝ) * (s / ((q : ℝ) + 1)) := by
      rw [Nat.factorial_succ]; push_cast; field_simp; ring
    have hqR : (q0 : ℝ) ≤ q := by exact_mod_cast hq
    have hratio : s / ((q : ℝ) + 1) ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]; linarith
    have hnn : 0 ≤ s / ((q : ℝ) + 1) := by positivity
    have hE : 0 ≤ Real.exp s * 2 ^ q0 / 2 ^ q := by positivity
    rw [hfac]
    calc s ^ q / (q.factorial : ℝ) * (s / ((q : ℝ) + 1))
        ≤ (Real.exp s * 2 ^ q0 / 2 ^ q) * (1 / 2) := mul_le_mul ih hratio hnn hE
      _ = Real.exp s * 2 ^ q0 / 2 ^ (q + 1) := by rw [pow_succ]; field_simp

theorem geom_tail (n : ℕ) : ∑ j ∈ range n, (1 / 4 : ℝ) ^ (n - j) ≤ 1 / 3 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have key : ∑ j ∈ range (n + 1), (1 / 4 : ℝ) ^ (n + 1 - j)
        = 1 / 4 * ∑ j ∈ range n, (1 / 4 : ℝ) ^ (n - j) + 1 / 4 := by
      rw [Finset.sum_range_succ, Finset.mul_sum]
      congr 1
      · apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.mem_range] at hj
        have hsub : n + 1 - j = (n - j) + 1 := by omega
        rw [hsub, pow_succ]; ring
      · simp
    rw [key]; linarith

theorem exists_params (g : ℕ) :
    ∃ q0 a : ℕ, 2 * (18 * (g : ℝ)) ≤ q0 ∧ q0 ≤ 2 * a + 1 ∧
      Real.exp (((g : ℝ) + 2) * (18 * (g : ℝ))) * 2 ^ q0 ≤ 2 ^ (2 * a) := by
  obtain ⟨a0, ha0⟩ := pow_unbounded_of_one_lt
    (Real.exp (((g : ℝ) + 2) * (18 * (g : ℝ))) * 2 ^ (36 * g)) (by norm_num : (1 : ℝ) < 4)
  refine ⟨36 * g, a0 + 36 * g, ?_, by omega, ?_⟩
  · push_cast; linarith
  · have h4 : (4 : ℝ) ^ a0 ≤ 4 ^ (a0 + 36 * g) := pow_le_pow_right₀ (by norm_num) (by omega)
    have e : (2 : ℝ) ^ (2 * (a0 + 36 * g)) = 4 ^ (a0 + 36 * g) := by rw [pow_mul]; norm_num
    rw [e]; linarith

theorem ratio_term_upper (s G : ℝ) (hs : 0 ≤ s) (q0 a n j : ℕ) (h0 : 2 * s ≤ q0)
    (ha1 : q0 ≤ 2 * a + 1) (ha2 : Real.exp ((G + 2) * s) * 2 ^ q0 ≤ 2 ^ (2 * a)) :
    s ^ (2 * (a + (n - j)) + 2) / ((2 * (a + (n - j)) + 2).factorial : ℝ) * Real.exp ((G + 1) * s) ≤
      1 / 2 * (1 / 4 : ℝ) ^ (n - j) := by
  have hq : q0 ≤ 2 * (a + (n - j)) + 2 := by omega
  have h1 := pow_fact_le s hs q0 (2 * (a + (n - j)) + 2) h0 hq
  have hE : Real.exp s * Real.exp ((G + 1) * s) = Real.exp ((G + 2) * s) := by
    rw [← Real.exp_add]; ring_nf
  have hpos : 0 ≤ Real.exp ((G + 1) * s) := (Real.exp_pos _).le
  have h4 : (4 : ℝ) ^ (n - j) = 2 ^ (2 * (n - j)) := by rw [pow_mul]; norm_num
  have hpow : (2 : ℝ) ^ (2 * (a + (n - j)) + 2) = 2 ^ (2 * a) * 4 * 4 ^ (n - j) := by
    rw [h4]; ring
  calc s ^ (2 * (a + (n - j)) + 2) / ((2 * (a + (n - j)) + 2).factorial : ℝ) * Real.exp ((G + 1) * s)
      ≤ (Real.exp s * 2 ^ q0 / 2 ^ (2 * (a + (n - j)) + 2)) * Real.exp ((G + 1) * s) :=
        mul_le_mul_of_nonneg_right h1 hpos
    _ = Real.exp ((G + 2) * s) * 2 ^ q0 / 2 ^ (2 * (a + (n - j)) + 2) := by
        rw [← hE]; ring
    _ ≤ 2 ^ (2 * a) / 2 ^ (2 * (a + (n - j)) + 2) := by gcongr
    _ = 1 / 4 * (1 / 4 : ℝ) ^ (n - j) := by rw [hpow, one_div_pow]; field_simp
    _ ≤ 1 / 2 * (1 / 4 : ℝ) ^ (n - j) := by
        have : (0 : ℝ) ≤ (1 / 4 : ℝ) ^ (n - j) := by positivity
        linarith

theorem exp_half_le_two : Real.exp (1 / 2 : ℝ) ≤ 2 := by
  have hsq : Real.exp (1 / 2 : ℝ) * Real.exp (1 / 2 : ℝ) = Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  have he : Real.exp 1 < 4 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hpos : 0 < Real.exp (1 / 2 : ℝ) := Real.exp_pos _
  nlinarith

theorem dens_prod_upper (A : Finset ℕ) (N M' : ℕ) (W : Finset ℕ) (hadm : Adm A N M' W)
    (n q0 a : ℕ) (hn : 1 ≤ n) (hWn : ∀ b ∈ W, b ≤ 2 ^ 2 ^ n)
    (h0 : 2 * (18 * (A.card : ℝ)) ≤ q0) (ha1 : q0 ≤ 2 * a + 1)
    (ha2 : Real.exp (((A.card : ℝ) + 2) * (18 * (A.card : ℝ))) * 2 ^ q0 ≤ 2 ^ (2 * a)) :
    ∏ j ∈ range n, dens A.card (blk W j) (cU (mm (a + 1) n j)) ≤
      2 * ∏ b ∈ W, (1 - (A.card : ℝ) / (b : ℝ)) := by
  have hn' : ∀ b ∈ W, 1 ≤ b ∧ b ≤ 2 ^ 2 ^ n := fun b hb =>
    ⟨by have := (hadm.2.2 b hb).1; omega, hWn b hb⟩
  have hcov := blk_cover W n hn hn'
  have hWeq : ∏ b ∈ W, (1 - (A.card : ℝ) / (b : ℝ)) =
      ∏ j ∈ range n, ∏ b ∈ blk W j, (1 - (A.card : ℝ) / (b : ℝ)) :=
    (prod_blk W n hcov _).symm
  let Vj : ℕ → ℝ := fun j => ∏ b ∈ blk W j, (1 - (A.card : ℝ) / (b : ℝ))
  let ej : ℕ → ℝ := fun j => dens A.card (blk W j) (cE (2 * (a + (n - j)) + 1))
  have hVpos : ∀ j, 0 < Vj j := fun j =>
    (block_V A N M' W hadm (blk W j) (blk_sub W j) 0 ⟨0, rfl⟩).1
  have hfactor : ∀ j, dens A.card (blk W j) (cU (mm (a + 1) n j)) ≤
      Vj j * Real.exp (ej j / Vj j) := by
    intro j
    have hm_eq : mm (a + 1) n j = (2 * (a + (n - j)) + 1) + 1 := by unfold mm; omega
    have hodd : Odd (2 * (a + (n - j)) + 1) := ⟨a + (n - j), by ring⟩
    have hdu := block_dens_upper A N M' W hadm (blk W j) (blk_sub W j) _ hodd
    rw [← hm_eq] at hdu
    have hexp : 1 + ej j / Vj j ≤ Real.exp (ej j / Vj j) := by
      linarith [Real.add_one_le_exp (ej j / Vj j)]
    have hmul : Vj j * (1 + ej j / Vj j) = Vj j + ej j := by
      have hne : Vj j ≠ 0 := (hVpos j).ne'
      field_simp
    calc dens A.card (blk W j) (cU (mm (a + 1) n j))
        ≤ Vj j + ej j := hdu
      _ = Vj j * (1 + ej j / Vj j) := hmul.symm
      _ ≤ Vj j * Real.exp (ej j / Vj j) := mul_le_mul_of_nonneg_left hexp (hVpos j).le
  have hdens_nn : ∀ j, 0 ≤ dens A.card (blk W j) (cU (mm (a + 1) n j)) := fun j =>
    le_trans (hVpos j).le
      (block_V A N M' W hadm (blk W j) (blk_sub W j) (mm (a + 1) n j) (mm_even (a + 1) n j)).2
  have hsum_eps : ∑ j ∈ range n, ej j / Vj j ≤ 1 / 2 := by
    calc ∑ j ∈ range n, ej j / Vj j
        ≤ ∑ j ∈ range n, (18 * (A.card : ℝ)) ^ (2 * (a + (n - j)) + 2) /
            ((2 * (a + (n - j)) + 2).factorial : ℝ) *
              Real.exp (((A.card : ℝ) + 1) * (18 * (A.card : ℝ))) := by
          apply Finset.sum_le_sum
          intro j _
          exact (block_eps A N M' W hadm (blk W j) (blk_sub W j) (blk_sum A N M' W hadm j)
            (2 * (a + (n - j)) + 1)).2
      _ ≤ ∑ j ∈ range n, 1 / 2 * (1 / 4 : ℝ) ^ (n - j) :=
          Finset.sum_le_sum fun j _ =>
            ratio_term_upper (18 * (A.card : ℝ)) (A.card : ℝ) (by positivity) q0 a n j h0 ha1 ha2
      _ = 1 / 2 * ∑ j ∈ range n, (1 / 4 : ℝ) ^ (n - j) := by rw [Finset.mul_sum]
      _ ≤ 1 / 2 * (1 / 3) := mul_le_mul_of_nonneg_left (geom_tail n) (by norm_num)
      _ ≤ 1 / 2 := by norm_num
  have hVprod_nn : 0 ≤ ∏ j ∈ range n, Vj j := Finset.prod_nonneg (fun j _ => (hVpos j).le)
  calc ∏ j ∈ range n, dens A.card (blk W j) (cU (mm (a + 1) n j))
      ≤ ∏ j ∈ range n, (Vj j * Real.exp (ej j / Vj j)) :=
        Finset.prod_le_prod (fun j _ => hdens_nn j) (fun j _ => hfactor j)
    _ = (∏ j ∈ range n, Vj j) * Real.exp (∑ j ∈ range n, ej j / Vj j) := by
        rw [Finset.prod_mul_distrib, Real.exp_sum]
    _ ≤ (∏ j ∈ range n, Vj j) * Real.exp (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hsum_eps) hVprod_nn
    _ ≤ (∏ j ∈ range n, Vj j) * 2 := mul_le_mul_of_nonneg_left exp_half_le_two hVprod_nn
    _ = 2 * ∏ b ∈ W, (1 - (A.card : ℝ) / (b : ℝ)) := by rw [← hWeq]; ring

theorem prod_Ioc_choose (g y : ℕ) (hgy : g ≤ y) :
    (∏ b ∈ Ioc g y, (1 - (g : ℝ) / (b : ℝ))) * (y.choose g : ℝ) = 1 := by
  induction y, hgy using Nat.le_induction with
  | base => simp
  | succ y hgy ih =>
    have hyne : (y : ℝ) + 1 ≠ 0 := by positivity
    have hc : (y.choose g : ℝ) * ((y : ℝ) + 1) = ((y + 1).choose g : ℝ) * ((y : ℝ) + 1 - g) := by
      have h := Nat.choose_mul_succ_eq y g
      have h' : ((y.choose g * (y + 1) : ℕ) : ℝ) = (((y + 1).choose g * (y + 1 - g) : ℕ) : ℝ) := by
        rw [h]
      rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (by omega : g ≤ y + 1)] at h'
      push_cast at h'
      linear_combination h'
    rw [Finset.prod_Ioc_succ_top hgy]
    have key : (1 - (g : ℝ) / ((y + 1 : ℕ) : ℝ)) * ((y + 1).choose g : ℝ) = (y.choose g : ℝ) := by
      push_cast
      rw [one_sub_div hyne, div_mul_eq_mul_div, div_eq_iff hyne]
      linear_combination (-1 : ℝ) * hc
    calc (∏ b ∈ Ioc g y, (1 - (g : ℝ) / (b : ℝ))) * (1 - (g : ℝ) / ((y + 1 : ℕ) : ℝ))
          * ((y + 1).choose g : ℝ)
        = (∏ b ∈ Ioc g y, (1 - (g : ℝ) / (b : ℝ))) *
            ((1 - (g : ℝ) / ((y + 1 : ℕ) : ℝ)) * ((y + 1).choose g : ℝ)) := by ring
      _ = 1 := by rw [key]; exact ih

theorem V_ge (g y : ℕ) (hy : 1 ≤ y) (W : Finset ℕ) (hW : ∀ b ∈ W, g < b ∧ b ≤ y) :
    1 ≤ (y : ℝ) ^ g * ∏ b ∈ W, (1 - (g : ℝ) / (b : ℝ)) := by
  by_cases hgy : g ≤ y
  · have hsub : W ⊆ Ioc g y := fun b hb => Finset.mem_Ioc.mpr (hW b hb)
    have hfac : ∀ b : ℕ, g < b → 0 ≤ 1 - (g : ℝ) / (b : ℝ) := by
      intro b hb
      have hbpos : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (show 0 < b by omega)
      have hgb : (g : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb.le
      have : (g : ℝ) / (b : ℝ) ≤ 1 := (div_le_one hbpos).mpr hgb
      linarith
    have hprod : ∏ b ∈ Ioc g y, (1 - (g : ℝ) / (b : ℝ)) ≤ ∏ b ∈ W, (1 - (g : ℝ) / (b : ℝ)) := by
      apply Finset.prod_le_prod_of_subset_of_le_one hsub
      · intro b hb; exact hfac b (Finset.mem_Ioc.mp hb).1
      · intro b _ _
        have : (0 : ℝ) ≤ (g : ℝ) / (b : ℝ) := by positivity
        linarith
    have hPW0 : 0 ≤ ∏ b ∈ W, (1 - (g : ℝ) / (b : ℝ)) :=
      Finset.prod_nonneg fun b hb => hfac b (hW b hb).1
    have hC := prod_Ioc_choose g y hgy
    have hCle : ((y.choose g : ℕ) : ℝ) ≤ (y : ℝ) ^ g := by exact_mod_cast Nat.choose_le_pow y g
    have hC0 : (0 : ℝ) ≤ (y.choose g : ℝ) := Nat.cast_nonneg _
    have h1 : (∏ b ∈ Ioc g y, (1 - (g : ℝ) / (b : ℝ))) * (y.choose g : ℝ) ≤
        (∏ b ∈ W, (1 - (g : ℝ) / (b : ℝ))) * (y.choose g : ℝ) :=
      mul_le_mul_of_nonneg_right hprod hC0
    have h2 : (∏ b ∈ W, (1 - (g : ℝ) / (b : ℝ))) * (y.choose g : ℝ) ≤
        (∏ b ∈ W, (1 - (g : ℝ) / (b : ℝ))) * (y : ℝ) ^ g :=
      mul_le_mul_of_nonneg_left hCle hPW0
    rw [hC] at h1
    linarith
  · have hempty : ∏ b ∈ W, (1 - (g : ℝ) / (b : ℝ)) = 1 := by
      apply Finset.prod_eq_one
      intro b hb; exfalso; have := hW b hb; omega
    rw [hempty, mul_one]
    exact one_le_pow₀ (by exact_mod_cast hy)

/-- Packaged upper-bound sieve on `range L` with double-exponential cutoff `2 ^ 2 ^ k`. -/
theorem upper_sieve_core (A : Finset ℕ) (N s M' : ℕ) (W : Finset ℕ) (hadm : Adm A N M' W)
    (k q0 a L : ℕ) (hk : 1 ≤ k) (hWk : ∀ b ∈ W, b ≤ 2 ^ 2 ^ k)
    (h0 : 2 * (18 * (A.card : ℝ)) ≤ q0) (ha1 : q0 ≤ 2 * a + 1)
    (ha2 : Real.exp (((A.card : ℝ) + 2) * (18 * (A.card : ℝ))) * 2 ^ q0 ≤ 2 ^ (2 * a))
    (hL : (2 ^ 2 ^ k) ^ (2 * (A.card + 1) * (2 * a + 7) + A.card) ≤ L) :
    ((siftR A s M' W L).card : ℝ) ≤
      3 * (L : ℝ) * ∏ b ∈ W, (1 - (A.card : ℝ) / (b : ℝ)) := by
  have hk' : ∀ b ∈ W, 1 ≤ b ∧ b ≤ 2 ^ 2 ^ k := fun b hb =>
    ⟨by have := (hadm.2.2 b hb).1; omega, hWk b hb⟩
  have hcov := blk_cover W k hk hk'
  have hup := sieve_upper A N s M' W hadm (blk W) k (blk_sub W) (blk_disj W) hcov
    (fun j => mm (a + 1) k j) (fun j => mm_even (a + 1) k j) L
  have hdens := dens_prod_upper A N M' W hadm k q0 a hk hWk h0 ha1 ha2
  have hmass : ∏ j ∈ range k, mass A.card (blk W j) (cU (mm (a + 1) k j)) ≤
      ((2 : ℝ) ^ 2 ^ k) ^ (2 * (A.card + 1) * (2 * a + 7)) := by
    have h1 : ∏ j ∈ range k, mass A.card (blk W j) (cU (mm (a + 1) k j)) ≤
        ∏ j ∈ range k, (1 + (A.card : ℝ) * ((blk W j).card : ℝ)) ^ (mm (a + 1) k j + 1) :=
      Finset.prod_le_prod (fun j _ => mass_nonneg _ (Nat.cast_nonneg _) _ _)
        (fun j _ => mass_cU_le _ (Nat.cast_nonneg _) _ _)
    have h2 := rem_bound A.card (a + 1) k (blk W) (blk_card W)
    have heq : 2 * (A.card + 1) * (2 * (a + 1) + 5) = 2 * (A.card + 1) * (2 * a + 7) := by ring
    rw [heq] at h2
    exact le_trans h1 h2
  have hV := V_ge A.card (2 ^ 2 ^ k) Nat.one_le_two_pow W
    (fun b hb => ⟨adm_card_lt A N M' W hadm b hb, hWk b hb⟩)
  have hLR : ((2 : ℝ) ^ 2 ^ k) ^ (2 * (A.card + 1) * (2 * a + 7) + A.card) ≤ (L : ℝ) := by
    exact_mod_cast hL
  have hrem_le : ((2 : ℝ) ^ 2 ^ k) ^ (2 * (A.card + 1) * (2 * a + 7)) ≤
      (L : ℝ) * ∏ b ∈ W, (1 - (A.card : ℝ) / (b : ℝ)) := by
    have hV0 : 0 ≤ ∏ b ∈ W, (1 - (A.card : ℝ) / (b : ℝ)) := by
      apply Finset.prod_nonneg
      intro b hb
      have h1 : A.card < b := adm_card_lt A N M' W hadm b hb
      have h2 : (A.card : ℝ) < (b : ℝ) := by exact_mod_cast h1
      have hb0 : (0 : ℝ) < (b : ℝ) := lt_of_le_of_lt (Nat.cast_nonneg _) h2
      linarith [(div_le_one hb0).mpr h2.le]
    have hpow0 : (0 : ℝ) ≤ ((2 : ℝ) ^ 2 ^ k) ^ (2 * (A.card + 1) * (2 * a + 7)) := by positivity
    calc ((2 : ℝ) ^ 2 ^ k) ^ (2 * (A.card + 1) * (2 * a + 7))
        ≤ ((2 : ℝ) ^ 2 ^ k) ^ (2 * (A.card + 1) * (2 * a + 7)) *
            (((2 ^ 2 ^ k : ℕ) : ℝ) ^ A.card * ∏ b ∈ W, (1 - (A.card : ℝ) / (b : ℝ))) :=
          le_mul_of_one_le_right hpow0 hV
      _ = ((2 : ℝ) ^ 2 ^ k) ^ (2 * (A.card + 1) * (2 * a + 7) + A.card) *
            ∏ b ∈ W, (1 - (A.card : ℝ) / (b : ℝ)) := by
          push_cast; rw [pow_add]; ring
      _ ≤ (L : ℝ) * ∏ b ∈ W, (1 - (A.card : ℝ) / (b : ℝ)) :=
          mul_le_mul_of_nonneg_right hLR hV0
  have hLnn : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
  have hmain := mul_le_mul_of_nonneg_left hdens hLnn
  linarith

/- ## Part 2: Per-modulus hit bounds (sieved and unsieved) -/

/-- Sieved upper bound for a single large modulus `b > y` with cutoff `2 ^ 2 ^ k ≤ y`. -/
theorem hit_sieve_bound (B : Set ℕ) (A : Finset ℕ) (N M : ℕ)
    (hB : B.Pairwise Nat.Coprime) (hA : A ⊆ Icc 1 N)
    (hcop : ∀ b ∈ B, N < b → Nat.Coprime M b)
    (x y b k q0 a : ℕ)
    (hbB : b ∈ B) (hbN : N < b) (hby : y < b) (hk : 1 ≤ k) (hky : 2 ^ 2 ^ k ≤ y)
    (h0 : 2 * (18 * (A.card : ℝ)) ≤ q0) (ha1 : q0 ≤ 2 * a + 1)
    (ha2 : Real.exp (((A.card : ℝ) + 2) * (18 * (A.card : ℝ))) * 2 ^ q0 ≤ 2 ^ (2 * a))
    (hxb : b * (2 ^ 2 ^ k) ^ (2 * (A.card + 1) * (2 * a + 7) + A.card) ≤ x) :
    let T := (Icc 1 x).filter fun t => ∀ b' ∈ B, N < b' → b' ≤ y → ∀ a' ∈ A, ¬b' ∣ a' + M * t
    let W := (Ioc N (2 ^ 2 ^ k)).filter (· ∈ B)
    ((T.filter (fun t => ∃ a0 ∈ A, b ∣ a0 + M * t)).card : ℝ) ≤
      6 * (A.card : ℝ) * ((x : ℝ) / (b : ℝ)) *
        ∏ b' ∈ W, (1 - (A.card : ℝ) / (b' : ℝ)) := by
  classical
  intro T W
  have hbpos : 0 < b := by omega
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hbpos
  have hE1 : 1 ≤ (2 ^ 2 ^ k) ^ (2 * (A.card + 1) * (2 * a + 7) + A.card) :=
    Nat.one_le_pow _ _ Nat.one_le_two_pow
  have hbx : b ≤ x := le_trans (by simpa using Nat.mul_le_mul_left b hE1) hxb
  have hdiv_ge : (2 ^ 2 ^ k) ^ (2 * (A.card + 1) * (2 * a + 7) + A.card) ≤ x / b + 1 := by
    have : (2 ^ 2 ^ k) ^ (2 * (A.card + 1) * (2 * a + 7) + A.card) ≤ x / b :=
      (Nat.le_div_iff_mul_le hbpos).mpr (by rwa [mul_comm])
    omega
  have hadm : Adm A N (M * b) W := by
    refine ⟨hA, ?_, ?_⟩
    · intro b1 hb1 b2 hb2 hne
      exact hB (Finset.mem_filter.mp (Finset.mem_coe.mp hb1)).2
        (Finset.mem_filter.mp (Finset.mem_coe.mp hb2)).2 hne
    · intro b' hb'
      obtain ⟨hb'I, hb'B⟩ := Finset.mem_filter.mp hb'
      obtain ⟨hb'N, hb'k⟩ := Finset.mem_Ioc.mp hb'I
      refine ⟨hb'N, Nat.Coprime.mul_left (hcop b' hb'B hb'N) ?_⟩
      exact hB hbB hb'B (by omega)
  have hWk : ∀ b' ∈ W, b' ≤ 2 ^ 2 ^ k := fun b' hb' =>
    (Finset.mem_Ioc.mp (Finset.mem_filter.mp hb').1).2
  have hL_le : ((x / b + 1 : ℕ) : ℝ) ≤ 2 * ((x : ℝ) / (b : ℝ)) := by
    have h1 : ((x / b : ℕ) : ℝ) ≤ (x : ℝ) / (b : ℝ) := Nat.cast_div_le
    have h2 : (1 : ℝ) ≤ (x : ℝ) / (b : ℝ) := (one_le_div hbR).mpr (by exact_mod_cast hbx)
    push_cast; linarith
  have hper_a : ∀ a0 ∈ A,
      ((T.filter (fun t => b ∣ a0 + M * t)).card : ℝ) ≤
        6 * ((x : ℝ) / (b : ℝ)) * ∏ b' ∈ W, (1 - (A.card : ℝ) / (b' : ℝ)) := by
    intro a0 _
    obtain ⟨r0, hr0, hdvd0⟩ := hit_exists_s 0 M b a0 hbpos (hcop b hbB hbN)
    simp only [add_zero] at hdvd0
    have hcard_le : (T.filter (fun t => b ∣ a0 + M * t)).card ≤
        (siftR A (M * r0) (M * b) W (x / b + 1)).card := by
      apply Finset.card_le_card_of_injOn (fun t => t / b)
      · intro t ht
        obtain ⟨htT, ht_dvd⟩ := Finset.mem_filter.mp ht
        obtain ⟨htI, htS⟩ := Finset.mem_filter.mp htT
        have htx : t ≤ x := (Finset.mem_Icc.mp htI).2
        have hmod : t % b = r0 := by
          have hd' : b ∣ a0 + 0 + M * (t % b) := by
            simpa only [add_zero] using (hit_mod_s b a0 0 M t).mpr (by simpa only [add_zero] using ht_dvd)
          exact hit_inj_s 0 M b a0 (t % b) r0 (hcop b hbB hbN) (Nat.mod_lt t hbpos) hr0 hd'
            (by simpa only [add_zero] using hdvd0)
        have hteq : t = r0 + b * (t / b) := by
          have := Nat.mod_add_div t b
          omega
        refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ?_⟩
        · exact Nat.lt_succ_of_le (Nat.div_le_div_right htx)
        · intro b' hb' a' ha' hdiv
          obtain ⟨hb'I, hb'B⟩ := Finset.mem_filter.mp hb'
          obtain ⟨hb'N, hb'k⟩ := Finset.mem_Ioc.mp hb'I
          have hrew : a' + M * r0 + M * b * (t / b) = a' + M * t := by
            conv_rhs => rw [hteq]
            ring
          rw [hrew] at hdiv
          exact htS b' hb'B hb'N (le_trans hb'k hky) a' ha' hdiv
      · intro t1 ht1 t2 ht2 hdiv_eq
        have ht1d := (Finset.mem_filter.mp ht1).2
        have ht2d := (Finset.mem_filter.mp ht2).2
        have hm1 : t1 % b = r0 := by
          have hd' : b ∣ a0 + 0 + M * (t1 % b) := by
            simpa only [add_zero] using (hit_mod_s b a0 0 M t1).mpr (by simpa only [add_zero] using ht1d)
          exact hit_inj_s 0 M b a0 (t1 % b) r0 (hcop b hbB hbN) (Nat.mod_lt t1 hbpos) hr0 hd'
            (by simpa only [add_zero] using hdvd0)
        have hm2 : t2 % b = r0 := by
          have hd' : b ∣ a0 + 0 + M * (t2 % b) := by
            simpa only [add_zero] using (hit_mod_s b a0 0 M t2).mpr (by simpa only [add_zero] using ht2d)
          exact hit_inj_s 0 M b a0 (t2 % b) r0 (hcop b hbB hbN) (Nat.mod_lt t2 hbpos) hr0 hd'
            (by simpa only [add_zero] using hdvd0)
        have e1 := Nat.mod_add_div t1 b
        have e2 := Nat.mod_add_div t2 b
        dsimp only at hdiv_eq
        rw [← e1, ← e2, hm1, hm2, hdiv_eq]
    have hVnn : 0 ≤ ∏ b' ∈ W, (1 - (A.card : ℝ) / (b' : ℝ)) := by
      exact (block_V A N (M * b) W hadm W (Finset.Subset.refl W) 0 ⟨0, rfl⟩).1.le
    have hs := upper_sieve_core A N (M * r0) (M * b) W hadm k q0 a (x / b + 1) hk hWk h0 ha1 ha2 hdiv_ge
    calc ((T.filter (fun t => b ∣ a0 + M * t)).card : ℝ)
        ≤ ((siftR A (M * r0) (M * b) W (x / b + 1)).card : ℝ) := by exact_mod_cast hcard_le
      _ ≤ 3 * ((x / b + 1 : ℕ) : ℝ) * ∏ b' ∈ W, (1 - (A.card : ℝ) / (b' : ℝ)) := hs
      _ ≤ 3 * (2 * ((x : ℝ) / (b : ℝ))) * ∏ b' ∈ W, (1 - (A.card : ℝ) / (b' : ℝ)) := by
          have := mul_le_mul_of_nonneg_left hL_le (by norm_num : (0 : ℝ) ≤ 3)
          exact mul_le_mul_of_nonneg_right this hVnn
      _ = 6 * ((x : ℝ) / (b : ℝ)) * ∏ b' ∈ W, (1 - (A.card : ℝ) / (b' : ℝ)) := by ring
  have hsub : T.filter (fun t => ∃ a0 ∈ A, b ∣ a0 + M * t) ⊆
      A.biUnion (fun a0 => T.filter (fun t => b ∣ a0 + M * t)) := by
    intro t ht
    obtain ⟨htT, a0, ha0, hd⟩ := Finset.mem_filter.mp ht
    exact Finset.mem_biUnion.mpr ⟨a0, ha0, Finset.mem_filter.mpr ⟨htT, hd⟩⟩
  have hbi : ((T.filter (fun t => ∃ a0 ∈ A, b ∣ a0 + M * t)).card : ℝ) ≤
      ∑ a0 ∈ A, ((T.filter (fun t => b ∣ a0 + M * t)).card : ℝ) := by
    have hnat : (T.filter (fun t => ∃ a0 ∈ A, b ∣ a0 + M * t)).card ≤
        ∑ a0 ∈ A, (T.filter (fun t => b ∣ a0 + M * t)).card :=
      le_trans (Finset.card_le_card hsub) Finset.card_biUnion_le
    exact_mod_cast hnat
  calc ((T.filter (fun t => ∃ a0 ∈ A, b ∣ a0 + M * t)).card : ℝ)
      ≤ ∑ a0 ∈ A, ((T.filter (fun t => b ∣ a0 + M * t)).card : ℝ) := hbi
    _ ≤ ∑ _a0 ∈ A, (6 * ((x : ℝ) / (b : ℝ)) * ∏ b' ∈ W, (1 - (A.card : ℝ) / (b' : ℝ))) :=
        Finset.sum_le_sum hper_a
    _ = 6 * (A.card : ℝ) * ((x : ℝ) / (b : ℝ)) * ∏ b' ∈ W, (1 - (A.card : ℝ) / (b' : ℝ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- Trivial (unsieved) upper bound for a single large modulus `b ≤ 2 ^ LM * x`. -/
theorem hit_trivial_bound (A : Finset ℕ) (M x b LM : ℕ) (S : Finset ℕ)
    (hS : S ⊆ Icc 1 x) (hbpos : 0 < b) (hcb : Nat.Coprime M b) (hbM : b ≤ 2 ^ LM * x) :
    ((S.filter (fun t => ∃ a0 ∈ A, b ∣ a0 + M * t)).card : ℝ) ≤
      (A.card : ℝ) * ((2 : ℝ) ^ LM + 1) * ((x : ℝ) / (b : ℝ)) := by
  classical
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hbpos
  have h1le : (1 : ℝ) ≤ (2 : ℝ) ^ LM * ((x : ℝ) / (b : ℝ)) := by
    rw [mul_div_assoc', one_le_div hbR]
    exact_mod_cast hbM
  have hL_le : ((x / b + 1 : ℕ) : ℝ) ≤ ((2 : ℝ) ^ LM + 1) * ((x : ℝ) / (b : ℝ)) := by
    have h1 : ((x / b : ℕ) : ℝ) ≤ (x : ℝ) / (b : ℝ) := Nat.cast_div_le
    push_cast; linarith
  have hper_a : ∀ a0 ∈ A,
      ((S.filter (fun t => b ∣ a0 + M * t)).card : ℝ) ≤
        ((2 : ℝ) ^ LM + 1) * ((x : ℝ) / (b : ℝ)) := by
    intro a0 _
    obtain ⟨r0, hr0, hdvd0⟩ := hit_exists_s 0 M b a0 hbpos hcb
    simp only [add_zero] at hdvd0
    have hcard_le : (S.filter (fun t => b ∣ a0 + M * t)).card ≤ (range (x / b + 1)).card := by
      apply Finset.card_le_card_of_injOn (fun t => t / b)
      · intro t ht
        have htx : t ≤ x := (Finset.mem_Icc.mp (hS (Finset.mem_filter.mp ht).1)).2
        exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right htx))
      · intro t1 ht1 t2 ht2 hdiv_eq
        have ht1d := (Finset.mem_filter.mp ht1).2
        have ht2d := (Finset.mem_filter.mp ht2).2
        have hm1 : t1 % b = r0 := by
          have hd' : b ∣ a0 + 0 + M * (t1 % b) := by
            simpa only [add_zero] using (hit_mod_s b a0 0 M t1).mpr (by simpa only [add_zero] using ht1d)
          exact hit_inj_s 0 M b a0 (t1 % b) r0 hcb (Nat.mod_lt t1 hbpos) hr0 hd'
            (by simpa only [add_zero] using hdvd0)
        have hm2 : t2 % b = r0 := by
          have hd' : b ∣ a0 + 0 + M * (t2 % b) := by
            simpa only [add_zero] using (hit_mod_s b a0 0 M t2).mpr (by simpa only [add_zero] using ht2d)
          exact hit_inj_s 0 M b a0 (t2 % b) r0 hcb (Nat.mod_lt t2 hbpos) hr0 hd'
            (by simpa only [add_zero] using hdvd0)
        have e1 := Nat.mod_add_div t1 b
        have e2 := Nat.mod_add_div t2 b
        dsimp only at hdiv_eq
        rw [← e1, ← e2, hm1, hm2, hdiv_eq]
    rw [Finset.card_range] at hcard_le
    exact le_trans (by exact_mod_cast hcard_le) hL_le
  have hsub : S.filter (fun t => ∃ a0 ∈ A, b ∣ a0 + M * t) ⊆
      A.biUnion (fun a0 => S.filter (fun t => b ∣ a0 + M * t)) := by
    intro t ht
    obtain ⟨htS, a0, ha0, hd⟩ := Finset.mem_filter.mp ht
    exact Finset.mem_biUnion.mpr ⟨a0, ha0, Finset.mem_filter.mpr ⟨htS, hd⟩⟩
  have hbi : ((S.filter (fun t => ∃ a0 ∈ A, b ∣ a0 + M * t)).card : ℝ) ≤
      ∑ a0 ∈ A, ((S.filter (fun t => b ∣ a0 + M * t)).card : ℝ) := by
    have hnat : (S.filter (fun t => ∃ a0 ∈ A, b ∣ a0 + M * t)).card ≤
        ∑ a0 ∈ A, (S.filter (fun t => b ∣ a0 + M * t)).card :=
      le_trans (Finset.card_le_card hsub) Finset.card_biUnion_le
    exact_mod_cast hnat
  calc ((S.filter (fun t => ∃ a0 ∈ A, b ∣ a0 + M * t)).card : ℝ)
      ≤ ∑ a0 ∈ A, ((S.filter (fun t => b ∣ a0 + M * t)).card : ℝ) := hbi
    _ ≤ ∑ _a0 ∈ A, (((2 : ℝ) ^ LM + 1) * ((x : ℝ) / (b : ℝ))) := Finset.sum_le_sum hper_a
    _ = (A.card : ℝ) * ((2 : ℝ) ^ LM + 1) * ((x : ℝ) / (b : ℝ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring

/- ## Part 3: Double-exponential reciprocal sums, record lows, and density ratios -/

/-- Double-exponential reciprocal sum `S B n = ∑_{1 ≤ b ≤ 2^{2^n}, b ∈ B} 1 / b`. -/
noncomputable def Ssum (B : Set ℕ) (n : ℕ) : ℝ := by
  classical
  exact ∑ b ∈ (Icc 1 (2 ^ 2 ^ n)).filter (· ∈ B), (1 : ℝ) / (b : ℝ)

theorem Ssum_sub_eq (B : Set ℕ) (j n : ℕ) (hjn : j ≤ n) :
    letI := Classical.propDecidable
    ∑ b ∈ (Ioc (2 ^ 2 ^ j) (2 ^ 2 ^ n)).filter (· ∈ B), (1 : ℝ) / (b : ℝ) =
      Ssum B n - Ssum B j := by
  classical
  have hle : 2 ^ 2 ^ j ≤ 2 ^ 2 ^ n :=
    Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by norm_num) hjn)
  have h1 : 1 ≤ 2 ^ 2 ^ j := Nat.one_le_two_pow
  have hu : (Icc 1 (2 ^ 2 ^ n)).filter (· ∈ B) =
      (Icc 1 (2 ^ 2 ^ j)).filter (· ∈ B) ∪ (Ioc (2 ^ 2 ^ j) (2 ^ 2 ^ n)).filter (· ∈ B) := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨hb1, hbn⟩, hbB⟩
      by_cases hbj : b ≤ 2 ^ 2 ^ j
      · exact Or.inl ⟨⟨hb1, hbj⟩, hbB⟩
      · exact Or.inr ⟨⟨by omega, hbn⟩, hbB⟩
    · rintro (⟨⟨hb1, hbj⟩, hbB⟩ | ⟨⟨hbj, hbn⟩, hbB⟩)
      · exact ⟨⟨hb1, le_trans hbj hle⟩, hbB⟩
      · exact ⟨⟨by omega, hbn⟩, hbB⟩
  have hdisj : Disjoint ((Icc 1 (2 ^ 2 ^ j)).filter (· ∈ B))
      ((Ioc (2 ^ 2 ^ j) (2 ^ 2 ^ n)).filter (· ∈ B)) := by
    rw [Finset.disjoint_left]
    intro b h1' h2'
    have a := (Finset.mem_Icc.mp (Finset.mem_filter.mp h1').1).2
    have c := (Finset.mem_Ioc.mp (Finset.mem_filter.mp h2').1).1
    omega
  have hsum : Ssum B n = Ssum B j +
      ∑ b ∈ (Ioc (2 ^ 2 ^ j) (2 ^ 2 ^ n)).filter (· ∈ B), (1 : ℝ) / (b : ℝ) := by
    unfold Ssum
    rw [hu, Finset.sum_union hdisj]
  linarith

theorem Ssum_eventually_le (B : Set ℕ)
    (hsum : (fun x : ℕ ↦ ∑ b ∈ range x with b ∈ B, (1 : ℝ) / (b : ℝ)) =o[atTop]
      fun x : ℕ ↦ Real.log (Real.log (x : ℝ)))
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, Ssum B n ≤ δ * (n : ℝ) := by
  classical
  have hlit := hsum.def (show 0 < δ / 4 by linarith)
  rw [Filter.eventually_atTop] at hlit ⊢
  obtain ⟨X0, hX0⟩ := hlit
  refine ⟨max (X0 + 2) 4, fun n hn => ?_⟩
  have hnX : X0 ≤ 2 ^ 2 ^ n + 1 := by
    have h1 : n ≤ 2 ^ n := Nat.lt_two_pow_self.le
    have h2 : 2 ^ n ≤ 2 ^ 2 ^ n := Nat.lt_two_pow_self.le
    have : X0 + 2 ≤ n := le_trans (le_max_left _ _) hn
    omega
  have hn4 : 4 ≤ n := le_trans (le_max_right _ _) hn
  have hspec := hX0 (2 ^ 2 ^ n + 1) hnX
  have hS_le : Ssum B n ≤ ∑ b ∈ (range (2 ^ 2 ^ n + 1)).filter (· ∈ B), (1 : ℝ) / (b : ℝ) := by
    unfold Ssum
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro b hb
      obtain ⟨hbI, hbB⟩ := Finset.mem_filter.mp hb
      have := (Finset.mem_Icc.mp hbI).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hbB⟩
    · intro b _ _; positivity
  have hsum_nn : 0 ≤ ∑ b ∈ (range (2 ^ 2 ^ n + 1)).filter (· ∈ B), (1 : ℝ) / (b : ℝ) :=
    Finset.sum_nonneg (fun b _ => by positivity)
  have hlog2_lt : Real.log 2 < 1 := lt_trans Real.log_two_lt_d9 (by norm_num)
  have hpow_le : ((2 ^ 2 ^ n + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (2 ^ (n + 1)) := by
    have hnat : 2 ^ 2 ^ n + 1 ≤ 2 ^ 2 ^ (n + 1) := by
      have h2n : 2 ^ n + 1 ≤ 2 ^ (n + 1) := by rw [pow_succ]; have := @Nat.one_le_two_pow n; omega
      have h1 : 2 ^ 2 ^ n + 1 ≤ 2 ^ 2 ^ n + 2 ^ 2 ^ n := by
        have := @Nat.one_le_two_pow (2 ^ n); omega
      calc 2 ^ 2 ^ n + 1 ≤ 2 * 2 ^ 2 ^ n := by omega
        _ = 2 ^ (2 ^ n + 1) := by rw [pow_succ']
        _ ≤ 2 ^ 2 ^ (n + 1) := Nat.pow_le_pow_right (by norm_num) h2n
    exact_mod_cast hnat
  have hge_e : Real.exp 1 ≤ ((2 ^ 2 ^ n + 1 : ℕ) : ℝ) := by
    have he3 : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    have h3 : (3 : ℝ) ≤ ((2 ^ 2 ^ n + 1 : ℕ) : ℝ) := by
      have : 3 ≤ 2 ^ 2 ^ n + 1 := by
        have : 2 ≤ 2 ^ 2 ^ n := by
          calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ 2 ^ n := Nat.pow_le_pow_right (by norm_num) Nat.one_le_two_pow
        omega
      exact_mod_cast this
    linarith
  have hlog1_ge1 : (1 : ℝ) ≤ Real.log ((2 ^ 2 ^ n + 1 : ℕ) : ℝ) := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hge_e
  have hlog2_nn : 0 ≤ Real.log (Real.log ((2 ^ 2 ^ n + 1 : ℕ) : ℝ)) :=
    Real.log_nonneg hlog1_ge1
  have hlog1_le : Real.log ((2 ^ 2 ^ n + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (n + 1) := by
    have hpos : (0 : ℝ) < ((2 ^ 2 ^ n + 1 : ℕ) : ℝ) := by positivity
    calc Real.log ((2 ^ 2 ^ n + 1 : ℕ) : ℝ)
        ≤ Real.log ((2 : ℝ) ^ (2 ^ (n + 1))) := Real.log_le_log hpos hpow_le
      _ = ((2 ^ (n + 1) : ℕ) : ℝ) * Real.log 2 := Real.log_pow 2 _
      _ ≤ ((2 ^ (n + 1) : ℕ) : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left hlog2_lt.le (Nat.cast_nonneg _)
      _ = (2 : ℝ) ^ (n + 1) := by push_cast; ring
  have hlog2_le : Real.log (Real.log ((2 ^ 2 ^ n + 1 : ℕ) : ℝ)) ≤ (n : ℝ) + 1 := by
    calc Real.log (Real.log ((2 ^ 2 ^ n + 1 : ℕ) : ℝ))
        ≤ Real.log ((2 : ℝ) ^ (n + 1)) := Real.log_le_log (by linarith) hlog1_le
      _ = ((n + 1 : ℕ) : ℝ) * Real.log 2 := Real.log_pow 2 _
      _ ≤ ((n + 1 : ℕ) : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left hlog2_lt.le (Nat.cast_nonneg _)
      _ = (n : ℝ) + 1 := by push_cast; ring
  rw [Real.norm_of_nonneg hsum_nn, Real.norm_of_nonneg hlog2_nn] at hspec
  have hnR : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn4
  have hbound : δ / 4 * ((n : ℝ) + 1) ≤ δ * (n : ℝ) := by nlinarith
  calc Ssum B n
      ≤ ∑ b ∈ (range (2 ^ 2 ^ n + 1)).filter (· ∈ B), (1 : ℝ) / (b : ℝ) := hS_le
    _ ≤ δ / 4 * Real.log (Real.log ((2 ^ 2 ^ n + 1 : ℕ) : ℝ)) := hspec
    _ ≤ δ / 4 * ((n : ℝ) + 1) := mul_le_mul_of_nonneg_left hlog2_le (by linarith)
    _ ≤ δ * (n : ℝ) := hbound

/-- Arbitrarily large record lows of `n ↦ Ssum B n - ε * n`. -/
theorem exists_record_low (B : Set ℕ)
    (hsum : (fun x : ℕ ↦ ∑ b ∈ range x with b ∈ B, (1 : ℝ) / (b : ℝ)) =o[atTop]
      fun x : ℕ ↦ Real.log (Real.log (x : ℝ)))
    (ε : ℝ) (hε : 0 < ε) (Mmin : ℕ) :
    ∃ M0 : ℕ, Mmin ≤ M0 ∧ ∀ j ≤ M0, Ssum B M0 - Ssum B j ≤ ε * ((M0 : ℝ) - (j : ℝ)) := by
  have hev := Ssum_eventually_le B hsum (ε / 2) (by linarith)
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N0, hN0⟩ := hev
  let f : ℕ → ℝ := fun j => Ssum B j - ε * (j : ℝ)
  have hne : (range (Mmin + 1)).Nonempty := ⟨0, Finset.mem_range.mpr (Nat.succ_pos Mmin)⟩
  obtain ⟨jmin, hjmin_mem, hjmin⟩ := Finset.exists_min_image (range (Mmin + 1)) f hne
  obtain ⟨K, hK⟩ := exists_nat_gt (2 * (|f jmin| + 1) / ε)
  let N1 := max (max N0 (Mmin + 1)) K
  have hN1_lt : f N1 < f jmin := by
    have hS : Ssum B N1 ≤ (ε / 2) * (N1 : ℝ) :=
      hN0 N1 (le_trans (le_max_left _ _) (le_max_left _ _))
    have hKN1 : (K : ℝ) ≤ (N1 : ℝ) := by exact_mod_cast le_max_right (max N0 (Mmin + 1)) K
    have hK' : 2 * (|f jmin| + 1) < ε * (N1 : ℝ) := by
      have := (div_lt_iff₀ hε).mp hK
      have := mul_le_mul_of_nonneg_left hKN1 hε.le
      linarith
    have hfj : -|f jmin| ≤ f jmin := neg_abs_le _
    dsimp only [f]
    linarith
  have hne1 : (range (N1 + 1)).Nonempty := ⟨0, Finset.mem_range.mpr (Nat.succ_pos N1)⟩
  obtain ⟨M0, hM0_mem, hM0⟩ := Finset.exists_min_image (range (N1 + 1)) f hne1
  have hM0_le : M0 ≤ N1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hM0_mem)
  have hM0_ge : Mmin ≤ M0 := by
    by_contra hlt
    push_neg at hlt
    have hM0_in : M0 ∈ range (Mmin + 1) := Finset.mem_range.mpr (by omega)
    have h1 : f jmin ≤ f M0 := hjmin M0 hM0_in
    have h2 : f M0 ≤ f N1 := hM0 N1 (Finset.mem_range.mpr (Nat.lt_succ_self N1))
    linarith
  refine ⟨M0, hM0_ge, fun j hj => ?_⟩
  have hj_in : j ∈ range (N1 + 1) := Finset.mem_range.mpr (by omega)
  have hle : f M0 ≤ f j := hM0 j hj_in
  dsimp only [f] at hle
  linarith

/-- Density ratio bound when lowering the sieve cutoff from `y` to `2 ^ 2 ^ k`. -/
theorem V_ratio_bound (B : Set ℕ) (A : Finset ℕ) (N k y n : ℕ) (hA : A ⊆ Icc 1 N)
    (hky : 2 ^ 2 ^ k ≤ y) (hyn : y ≤ 2 ^ 2 ^ n) (hkn : k ≤ n) :
    letI := Classical.propDecidable
    (∏ b ∈ (Ioc N (2 ^ 2 ^ k)).filter (· ∈ B), (1 - (A.card : ℝ) / (b : ℝ))) ≤
      Real.exp ((A.card : ℝ) * ((A.card : ℝ) + 1) * (Ssum B n - Ssum B k)) *
        ∏ b ∈ (Ioc N y).filter (· ∈ B), (1 - (A.card : ℝ) / (b : ℝ)) := by
  classical
  have hAg : A.card ≤ N := by
    have := Finset.card_le_card hA; simpa using this
  let Plow := (Ioc N (2 ^ 2 ^ k)).filter (· ∈ B)
  let Pmid := (Ioc (max N (2 ^ 2 ^ k)) y).filter (· ∈ B)
  have hunion : (Ioc N y).filter (· ∈ B) = Plow ∪ Pmid := by
    ext b
    simp only [Plow, Pmid, Finset.mem_filter, Finset.mem_union, Finset.mem_Ioc, max_lt_iff]
    constructor
    · rintro ⟨⟨hbN, hby⟩, hbB⟩
      by_cases hbk : b ≤ 2 ^ 2 ^ k
      · exact Or.inl ⟨⟨hbN, hbk⟩, hbB⟩
      · exact Or.inr ⟨⟨⟨hbN, by omega⟩, hby⟩, hbB⟩
    · rintro (⟨⟨hbN, hbk⟩, hbB⟩ | ⟨⟨⟨hbN, _⟩, hby⟩, hbB⟩)
      · exact ⟨⟨hbN, le_trans hbk hky⟩, hbB⟩
      · exact ⟨⟨hbN, hby⟩, hbB⟩
  have hdisj : Disjoint Plow Pmid := by
    rw [Finset.disjoint_left]
    intro b h1 h2
    have a := (Finset.mem_Ioc.mp (Finset.mem_filter.mp h1).1).2
    have c := (Finset.mem_Ioc.mp (Finset.mem_filter.mp h2).1).1
    omega
  have hVsplit : (∏ b ∈ (Ioc N y).filter (· ∈ B), (1 - (A.card : ℝ) / (b : ℝ))) =
      (∏ b ∈ Plow, (1 - (A.card : ℝ) / (b : ℝ))) *
        ∏ b ∈ Pmid, (1 - (A.card : ℝ) / (b : ℝ)) := by
    rw [hunion, Finset.prod_union hdisj]
  have hcond : ∀ b ∈ Pmid, 0 ≤ (A.card : ℝ) / (b : ℝ) ∧
      (A.card : ℝ) / (b : ℝ) * ((A.card : ℝ) + 1) ≤ (A.card : ℝ) := by
    intro b hb
    have hbN : N < b := lt_of_le_of_lt (le_max_left _ _) (Finset.mem_Ioc.mp (Finset.mem_filter.mp hb).1).1
    have h1 : A.card < b := by omega
    have h2 : (A.card : ℝ) + 1 ≤ (b : ℝ) := by exact_mod_cast h1
    have hb0 : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (show 0 < b by omega)
    refine ⟨div_nonneg (Nat.cast_nonneg _) hb0.le, ?_⟩
    rw [div_mul_eq_mul_div, div_le_iff₀ hb0]
    exact mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _)
  have hVmid := V_ge_exp (A.card : ℝ) (Nat.cast_nonneg _) (fun b => (A.card : ℝ) / (b : ℝ)) Pmid hcond
  have hsub : Pmid ⊆ (Ioc (2 ^ 2 ^ k) (2 ^ 2 ^ n)).filter (· ∈ B) := by
    intro b hb
    obtain ⟨hbI, hbB⟩ := Finset.mem_filter.mp hb
    obtain ⟨hb1, hb2⟩ := Finset.mem_Ioc.mp hbI
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨lt_of_le_of_lt (le_max_right _ _) hb1,
      le_trans hb2 hyn⟩, hbB⟩
  have hsum_le : ∑ b ∈ Pmid, (A.card : ℝ) / (b : ℝ) ≤ (A.card : ℝ) * (Ssum B n - Ssum B k) := by
    have e : ∑ b ∈ Pmid, (A.card : ℝ) / (b : ℝ) = (A.card : ℝ) * ∑ b ∈ Pmid, (1 : ℝ) / (b : ℝ) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro b _; ring
    rw [e, ← Ssum_sub_eq B k n hkn]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun b _ _ => by positivity)
  have hexp_le : Real.exp (-((A.card : ℝ) * ((A.card : ℝ) + 1) * (Ssum B n - Ssum B k))) ≤
      ∏ b ∈ Pmid, (1 - (A.card : ℝ) / (b : ℝ)) := by
    refine le_trans (Real.exp_le_exp.mpr ?_) hVmid
    have := mul_le_mul_of_nonneg_left hsum_le (by positivity : (0 : ℝ) ≤ (A.card : ℝ) + 1)
    linarith
  have hPlow_nn : 0 ≤ ∏ b ∈ Plow, (1 - (A.card : ℝ) / (b : ℝ)) := by
    apply Finset.prod_nonneg
    intro b hb
    have hbN := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hb).1).1
    have hb0 : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (show 0 < b by omega)
    have hgb : (A.card : ℝ) ≤ (b : ℝ) := by exact_mod_cast (show A.card ≤ b by omega)
    linarith [(div_le_one hb0).mpr hgb]
  rw [hVsplit]
  have hcancel : Real.exp ((A.card : ℝ) * ((A.card : ℝ) + 1) * (Ssum B n - Ssum B k)) *
      Real.exp (-((A.card : ℝ) * ((A.card : ℝ) + 1) * (Ssum B n - Ssum B k))) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have h1 : 1 ≤ Real.exp ((A.card : ℝ) * ((A.card : ℝ) + 1) * (Ssum B n - Ssum B k)) *
      ∏ b ∈ Pmid, (1 - (A.card : ℝ) / (b : ℝ)) := by
    have := mul_le_mul_of_nonneg_left hexp_le
      (Real.exp_pos ((A.card : ℝ) * ((A.card : ℝ) + 1) * (Ssum B n - Ssum B k))).le
    linarith
  calc ∏ b ∈ Plow, (1 - (A.card : ℝ) / (b : ℝ))
      ≤ (∏ b ∈ Plow, (1 - (A.card : ℝ) / (b : ℝ))) *
          (Real.exp ((A.card : ℝ) * ((A.card : ℝ) + 1) * (Ssum B n - Ssum B k)) *
            ∏ b ∈ Pmid, (1 - (A.card : ℝ) / (b : ℝ))) := le_mul_of_one_le_right hPlow_nn h1
    _ = Real.exp ((A.card : ℝ) * ((A.card : ℝ) + 1) * (Ssum B n - Ssum B k)) *
          ((∏ b ∈ Plow, (1 - (A.card : ℝ) / (b : ℝ))) *
            ∏ b ∈ Pmid, (1 - (A.card : ℝ) / (b : ℝ))) := by ring

/-- Uniform lower bound on `V(y)` for `y ≤ 2 ^ 2 ^ n`. -/
theorem V_lower_bound (B : Set ℕ) (A : Finset ℕ) (N y n : ℕ) (hA : A ⊆ Icc 1 N)
    (hyn : y ≤ 2 ^ 2 ^ n) :
    letI := Classical.propDecidable
    Real.exp (-((A.card : ℝ) * ((A.card : ℝ) + 1) * Ssum B n)) ≤
      ∏ b ∈ (Ioc N y).filter (· ∈ B), (1 - (A.card : ℝ) / (b : ℝ)) := by
  classical
  have hAg : A.card ≤ N := by have := Finset.card_le_card hA; simpa using this
  let Py := (Ioc N y).filter (· ∈ B)
  have hcond : ∀ b ∈ Py, 0 ≤ (A.card : ℝ) / (b : ℝ) ∧
      (A.card : ℝ) / (b : ℝ) * ((A.card : ℝ) + 1) ≤ (A.card : ℝ) := by
    intro b hb
    have hbN := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hb).1).1
    have h1 : A.card < b := by omega
    have h2 : (A.card : ℝ) + 1 ≤ (b : ℝ) := by exact_mod_cast h1
    have hb0 : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (show 0 < b by omega)
    refine ⟨div_nonneg (Nat.cast_nonneg _) hb0.le, ?_⟩
    rw [div_mul_eq_mul_div, div_le_iff₀ hb0]
    exact mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _)
  have hV := V_ge_exp (A.card : ℝ) (Nat.cast_nonneg _) (fun b => (A.card : ℝ) / (b : ℝ)) Py hcond
  have hsub : Py ⊆ (Icc 1 (2 ^ 2 ^ n)).filter (· ∈ B) := by
    intro b hb
    obtain ⟨hbI, hbB⟩ := Finset.mem_filter.mp hb
    obtain ⟨hbN, hby⟩ := Finset.mem_Ioc.mp hbI
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, le_trans hby hyn⟩, hbB⟩
  have hsum_le : ∑ b ∈ Py, (A.card : ℝ) / (b : ℝ) ≤ (A.card : ℝ) * Ssum B n := by
    have e : ∑ b ∈ Py, (A.card : ℝ) / (b : ℝ) = (A.card : ℝ) * ∑ b ∈ Py, (1 : ℝ) / (b : ℝ) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro b _; ring
    rw [e]; unfold Ssum
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun b _ _ => by positivity)
  refine le_trans (Real.exp_le_exp.mpr ?_) hV
  have := mul_le_mul_of_nonneg_left hsum_le (by positivity : (0 : ℝ) ≤ (A.card : ℝ) + 1)
  linarith

theorem V_pos (B : Set ℕ) (A : Finset ℕ) (N y : ℕ) (hA : A ⊆ Icc 1 N) :
    letI := Classical.propDecidable
    0 < ∏ b ∈ (Ioc N y).filter (· ∈ B), (1 - (A.card : ℝ) / (b : ℝ)) := by
  classical
  have hAg : A.card ≤ N := by have := Finset.card_le_card hA; simpa using this
  apply Finset.prod_pos
  intro b hb
  have hbN := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hb).1).1
  have h1 : A.card < b := by omega
  have h2 : (A.card : ℝ) < (b : ℝ) := by exact_mod_cast h1
  have hb0 : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (show 0 < b by omega)
  linarith [(div_lt_one hb0).mpr h2]

theorem exp_le_three_halves {t : ℝ} (ht : t ≤ 1 / 4) : Real.exp t ≤ 3 / 2 := by
  have h1 : 1 - t ≤ Real.exp (-t) := by linarith [Real.add_one_le_exp (-t)]
  rw [Real.exp_neg] at h1
  have hpos : 0 < Real.exp t := Real.exp_pos t
  have h2 : (3 / 4 : ℝ) ≤ (Real.exp t)⁻¹ := by linarith
  have h3 : (3 / 4 : ℝ) * Real.exp t ≤ 1 := by
    have := mul_le_mul_of_nonneg_right h2 hpos.le
    rwa [inv_mul_cancel₀ hpos.ne'] at this
  linarith

/- ## Part 4: Dyadic window counting, shell covering, and geometric sum -/

theorem card_pow2_window_sub (I : Finset ℕ) (b d1 d2 : ℕ) (hd : d2 ≤ d1) (hI : ∀ r ∈ I, d1 ≤ r) :
    (I.filter (fun r => 2 ^ (r - d1) < b ∧ b ≤ 2 ^ (r - d2))).card ≤ d1 - d2 := by
  set F := I.filter (fun r => 2 ^ (r - d1) < b ∧ b ≤ 2 ^ (r - d2))
  by_cases hF : F.Nonempty
  · let r0 := F.min' hF
    have hr0 : r0 ∈ F := F.min'_mem hF
    have hr0_ub : b ≤ 2 ^ (r0 - d2) := (Finset.mem_filter.mp hr0).2.2
    have hr0_ge : d1 ≤ r0 := hI r0 (Finset.mem_filter.mp hr0).1
    have hsub : F ⊆ Ico r0 (r0 + (d1 - d2)) := by
      intro r hr
      have hge : r0 ≤ r := F.min'_le r hr
      have hr_lb : 2 ^ (r - d1) < b := (Finset.mem_filter.mp hr).2.1
      have hr_ge : d1 ≤ r := hI r (Finset.mem_filter.mp hr).1
      have hpow : 2 ^ (r - d1) < 2 ^ (r0 - d2) := lt_of_lt_of_le hr_lb hr0_ub
      have hlt : r - d1 < r0 - d2 :=
        (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℕ) < 2)).mp hpow
      exact Finset.mem_Ico.mpr ⟨hge, by omega⟩
    have hle := Finset.card_le_card hsub
    rw [Nat.card_Ico] at hle
    omega
  · rw [Finset.not_nonempty_iff_eq_empty.mp hF]
    simp

theorem card_pow2_window_add (I : Finset ℕ) (b d1 d2 : ℕ) (hI : ∀ r ∈ I, d1 ≤ r) :
    (I.filter (fun r => 2 ^ (r - d1) < b ∧ b ≤ 2 ^ (r + d2))).card ≤ d1 + d2 := by
  set F := I.filter (fun r => 2 ^ (r - d1) < b ∧ b ≤ 2 ^ (r + d2))
  by_cases hF : F.Nonempty
  · let r0 := F.min' hF
    have hr0 : r0 ∈ F := F.min'_mem hF
    have hr0_ub : b ≤ 2 ^ (r0 + d2) := (Finset.mem_filter.mp hr0).2.2
    have hsub : F ⊆ Ico r0 (r0 + (d1 + d2)) := by
      intro r hr
      have hge : r0 ≤ r := F.min'_le r hr
      have hr_lb : 2 ^ (r - d1) < b := (Finset.mem_filter.mp hr).2.1
      have hr_ge : d1 ≤ r := hI r (Finset.mem_filter.mp hr).1
      have hpow : 2 ^ (r - d1) < 2 ^ (r0 + d2) := lt_of_lt_of_le hr_lb hr0_ub
      have hlt : r - d1 < r0 + d2 :=
        (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℕ) < 2)).mp hpow
      exact Finset.mem_Ico.mpr ⟨hge, by omega⟩
    have hle := Finset.card_le_card hsub
    rw [Nat.card_Ico] at hle
    omega
  · rw [Finset.not_nonempty_iff_eq_empty.mp hF]
    simp

theorem geom_three_fourths (n : ℕ) : ∑ t ∈ range n, (3 / 4 : ℝ) ^ (t + 1) ≤ 3 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have key : ∑ t ∈ range (n + 1), (3 / 4 : ℝ) ^ (t + 1) =
        3 / 4 * (∑ t ∈ range n, (3 / 4 : ℝ) ^ (t + 1)) + 3 / 4 := by
      rw [Finset.sum_range_succ', Finset.mul_sum]
      congr 1
      · apply Finset.sum_congr rfl
        intro t _; rw [pow_succ']
      · simp
    rw [key]; linarith

theorem sum_three_fourths_shell (s0 m : ℕ) :
    ∑ s ∈ Ico s0 (m - 2), (3 / 4 : ℝ) ^ (m - s) ≤ 3 := by
  have hmaps : ∀ s ∈ Ico s0 (m - 2), m - s - 1 ∈ range m := by
    intro s hs
    obtain ⟨_, h2⟩ := Finset.mem_Ico.mp hs
    exact Finset.mem_range.mpr (by omega)
  have hinj : Set.InjOn (fun s => m - s - 1) ((Ico s0 (m - 2) : Finset ℕ) : Set ℕ) := by
    intro s1 hs1 s2 hs2 heq
    have h1 := (Finset.mem_Ico.mp (Finset.mem_coe.mp hs1)).2
    have h2 := (Finset.mem_Ico.mp (Finset.mem_coe.mp hs2)).2
    dsimp only at heq
    omega
  have h1 : ∑ s ∈ Ico s0 (m - 2), (3 / 4 : ℝ) ^ (m - s) =
      ∑ t ∈ (Ico s0 (m - 2)).image (fun s => m - s - 1), (3 / 4 : ℝ) ^ (t + 1) := by
    rw [Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro s hs
    have h2 := (Finset.mem_Ico.mp hs).2
    have he : m - s - 1 + 1 = m - s := by omega
    rw [he]
  rw [h1]
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity))
    (geom_three_fourths m)
  intro t ht
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
  exact hmaps s hs

/-- Shell covering: every `b` in `(2^(r - 2^(m-2)), 2^(r - 2^s0)]` lies in some shell `s ∈ Ico s0 (m-2)`. -/
theorem shell_cover (r s0 m b : ℕ) (hsm : s0 < m - 2) (hr : 2 ^ (m - 2) ≤ r)
    (h1 : 2 ^ (r - 2 ^ (m - 2)) < b) (h2 : b ≤ 2 ^ (r - 2 ^ s0)) :
    ∃ s ∈ Ico s0 (m - 2), 2 ^ (r - 2 ^ (s + 1)) < b ∧ b ≤ 2 ^ (r - 2 ^ s) := by
  have key : ∀ k : ℕ, 2 ^ (r - 2 ^ (s0 + k)) < b → b ≤ 2 ^ (r - 2 ^ s0) →
      ∃ s ∈ Ico s0 (s0 + k), 2 ^ (r - 2 ^ (s + 1)) < b ∧ b ≤ 2 ^ (r - 2 ^ s) := by
    intro k
    induction k with
    | zero =>
      intro ha hb; simp at ha; omega
    | succ k ih =>
      intro ha hb
      by_cases hmid : b ≤ 2 ^ (r - 2 ^ (s0 + k))
      · refine ⟨s0 + k, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, ?_, hmid⟩
        simpa only [Nat.add_assoc] using ha
      · obtain ⟨s, hs, hs1, hs2⟩ := ih (by omega) hb
        obtain ⟨ha', hb'⟩ := Finset.mem_Ico.mp hs
        exact ⟨s, Finset.mem_Ico.mpr ⟨ha', by omega⟩, hs1, hs2⟩
  have heq : s0 + (m - 2 - s0) = m - 2 := by omega
  obtain ⟨s, hs, hs1, hs2⟩ := key (m - 2 - s0) (by rwa [heq]) h2
  rw [heq] at hs
  exact ⟨s, hs, hs1, hs2⟩

/-- Bounds on `y = ⌊(2 ^ r : ℝ) ^ ((D : ℝ)⁻¹)⌋₊`. -/
theorem y_pow2_bounds (r m D : ℕ) (hD : 2 ≤ D) (hm : D + 2 ≤ m) (hr : 2 ^ (m - 1) ≤ r) :
    2 ^ 2 ^ (m - 1 - D) ≤ ⌊((2 ^ r : ℕ) : ℝ) ^ ((D : ℝ)⁻¹)⌋₊ ∧
      ⌊((2 ^ r : ℕ) : ℝ) ^ ((D : ℝ)⁻¹)⌋₊ ≤ 2 ^ r := by
  have hD0 : D ≠ 0 := by omega
  have hD_le : D ≤ 2 ^ D := Nat.lt_two_pow_self.le
  have hexp : 2 ^ (m - 1 - D) * D ≤ r := by
    calc 2 ^ (m - 1 - D) * D ≤ 2 ^ (m - 1 - D) * 2 ^ D := Nat.mul_le_mul_left _ hD_le
      _ = 2 ^ (m - 1 - D + D) := (pow_add 2 _ _).symm
      _ = 2 ^ (m - 1) := by congr 1; omega
      _ ≤ r := hr
  constructor
  · apply Nat.le_floor
    have hnat : (2 ^ 2 ^ (m - 1 - D)) ^ D ≤ 2 ^ r := by
      rw [← pow_mul]
      exact Nat.pow_le_pow_right (by norm_num) hexp
    have hreal : (((2 ^ 2 ^ (m - 1 - D) : ℕ) : ℝ) ^ D) ≤ ((2 ^ r : ℕ) : ℝ) := by
      exact_mod_cast hnat
    have h1 := Real.rpow_le_rpow (by positivity) hreal (by positivity : (0 : ℝ) ≤ (D : ℝ)⁻¹)
    rwa [Real.pow_rpow_inv_natCast (by positivity) hD0] at h1
  · have hle : ((⌊((2 ^ r : ℕ) : ℝ) ^ ((D : ℝ)⁻¹)⌋₊ : ℕ) : ℝ) ≤ ((2 ^ r : ℕ) : ℝ) ^ ((D : ℝ)⁻¹) :=
      Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    have hpow : ((⌊((2 ^ r : ℕ) : ℝ) ^ ((D : ℝ)⁻¹)⌋₊ : ℕ) : ℝ) ^ D ≤ ((2 ^ r : ℕ) : ℝ) := by
      calc ((⌊((2 ^ r : ℕ) : ℝ) ^ ((D : ℝ)⁻¹)⌋₊ : ℕ) : ℝ) ^ D
          ≤ (((2 ^ r : ℕ) : ℝ) ^ ((D : ℝ)⁻¹)) ^ D := pow_le_pow_left₀ (Nat.cast_nonneg _) hle D
        _ = ((2 ^ r : ℕ) : ℝ) := Real.rpow_inv_natCast_pow (Nat.cast_nonneg _) hD0
    have hnat : ⌊((2 ^ r : ℕ) : ℝ) ^ ((D : ℝ)⁻¹)⌋₊ ^ D ≤ 2 ^ r := by exact_mod_cast hpow
    exact le_trans (Nat.le_self_pow hD0 _) hnat

/-- Double-sum interchange bound for a window family over `I = Ico (2^(m-1)) (2^m)`. -/
theorem sum_window_sub_bound (B : Set ℕ) (m d1 d2 : ℕ) (hd : d2 ≤ d1) (hd1 : d1 ≤ 2 ^ (m - 2))
    (hm : 3 ≤ m) :
    letI := Classical.propDecidable
    let I := Ico (2 ^ (m - 1)) (2 ^ m)
    ∑ r ∈ I, ∑ b ∈ (Ioc (2 ^ (r - d1)) (2 ^ (r - d2))).filter (· ∈ B), (1 : ℝ) / (b : ℝ) ≤
      ((d1 - d2 : ℕ) : ℝ) * (Ssum B (m + 1) - Ssum B (m - 2)) := by
  classical
  intro I
  let U := (Ioc (2 ^ 2 ^ (m - 2)) (2 ^ 2 ^ (m + 1))).filter (· ∈ B)
  have hI_ge : ∀ r ∈ I, d1 ≤ r := by
    intro r hr
    have h1 := (Finset.mem_Ico.mp hr).1
    have h2 : 2 ^ (m - 2) ≤ 2 ^ (m - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hsub : ∀ r ∈ I, (Ioc (2 ^ (r - d1)) (2 ^ (r - d2))).filter (· ∈ B) ⊆ U := by
    intro r hr b hb
    obtain ⟨hbI, hbB⟩ := Finset.mem_filter.mp hb
    obtain ⟨hb1, hb2⟩ := Finset.mem_Ioc.mp hbI
    obtain ⟨hr1, hr2⟩ := Finset.mem_Ico.mp hr
    have hlow : 2 ^ 2 ^ (m - 2) ≤ 2 ^ (r - d1) := by
      apply Nat.pow_le_pow_right (by norm_num)
      have hpow : 2 ^ (m - 1) = 2 * 2 ^ (m - 2) := by
        have : m - 1 = (m - 2) + 1 := by omega
        rw [this, pow_succ']
      omega
    have hhigh : 2 ^ (r - d2) ≤ 2 ^ 2 ^ (m + 1) := by
      apply Nat.pow_le_pow_right (by norm_num)
      have : 2 ^ m ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨lt_of_le_of_lt hlow hb1, le_trans hb2 hhigh⟩, hbB⟩
  have hrew : ∀ r ∈ I,
      ∑ b ∈ (Ioc (2 ^ (r - d1)) (2 ^ (r - d2))).filter (· ∈ B), (1 : ℝ) / (b : ℝ) =
        ∑ b ∈ U, if 2 ^ (r - d1) < b ∧ b ≤ 2 ^ (r - d2) then (1 : ℝ) / (b : ℝ) else 0 := by
    intro r hr
    rw [← Finset.sum_filter]
    congr 1
    ext b
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · intro hb
      exact ⟨hsub r hr (Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr hb.1, hb.2⟩), hb.1⟩
    · rintro ⟨hbU, hbI⟩
      exact ⟨hbI, (Finset.mem_filter.mp hbU).2⟩
  calc ∑ r ∈ I, ∑ b ∈ (Ioc (2 ^ (r - d1)) (2 ^ (r - d2))).filter (· ∈ B), (1 : ℝ) / (b : ℝ)
      = ∑ r ∈ I, ∑ b ∈ U, if 2 ^ (r - d1) < b ∧ b ≤ 2 ^ (r - d2) then (1 : ℝ) / (b : ℝ) else 0 :=
        Finset.sum_congr rfl hrew
    _ = ∑ b ∈ U, ∑ r ∈ I, if 2 ^ (r - d1) < b ∧ b ≤ 2 ^ (r - d2) then (1 : ℝ) / (b : ℝ) else 0 :=
        Finset.sum_comm
    _ ≤ ∑ b ∈ U, ((d1 - d2 : ℕ) : ℝ) * ((1 : ℝ) / (b : ℝ)) := by
        apply Finset.sum_le_sum
        intro b _
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast card_pow2_window_sub I b d1 d2 hd hI_ge
    _ = ((d1 - d2 : ℕ) : ℝ) * ∑ b ∈ U, (1 : ℝ) / (b : ℝ) := by rw [← Finset.mul_sum]
    _ = ((d1 - d2 : ℕ) : ℝ) * (Ssum B (m + 1) - Ssum B (m - 2)) := by
        rw [Ssum_sub_eq B (m - 2) (m + 1) (by omega)]

/-- Double-sum interchange bound for the near-`x` / super-`x` window. -/
theorem sum_window_add_bound (B : Set ℕ) (m d1 d2 : ℕ) (hd1 : d1 ≤ 2 ^ (m - 2))
    (hd2 : d2 ≤ 2 ^ m) (hm : 3 ≤ m) :
    letI := Classical.propDecidable
    let I := Ico (2 ^ (m - 1)) (2 ^ m)
    ∑ r ∈ I, ∑ b ∈ (Ioc (2 ^ (r - d1)) (2 ^ (r + d2))).filter (· ∈ B), (1 : ℝ) / (b : ℝ) ≤
      ((d1 + d2 : ℕ) : ℝ) * (Ssum B (m + 1) - Ssum B (m - 2)) := by
  classical
  intro I
  let U := (Ioc (2 ^ 2 ^ (m - 2)) (2 ^ 2 ^ (m + 1))).filter (· ∈ B)
  have hI_ge : ∀ r ∈ I, d1 ≤ r := by
    intro r hr
    have h1 := (Finset.mem_Ico.mp hr).1
    have h2 : 2 ^ (m - 2) ≤ 2 ^ (m - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hsub : ∀ r ∈ I, (Ioc (2 ^ (r - d1)) (2 ^ (r + d2))).filter (· ∈ B) ⊆ U := by
    intro r hr b hb
    obtain ⟨hbI, hbB⟩ := Finset.mem_filter.mp hb
    obtain ⟨hb1, hb2⟩ := Finset.mem_Ioc.mp hbI
    obtain ⟨hr1, hr2⟩ := Finset.mem_Ico.mp hr
    have hlow : 2 ^ 2 ^ (m - 2) ≤ 2 ^ (r - d1) := by
      apply Nat.pow_le_pow_right (by norm_num)
      have hpow : 2 ^ (m - 1) = 2 * 2 ^ (m - 2) := by
        have : m - 1 = (m - 2) + 1 := by omega
        rw [this, pow_succ']
      omega
    have hhigh : 2 ^ (r + d2) ≤ 2 ^ 2 ^ (m + 1) := by
      apply Nat.pow_le_pow_right (by norm_num)
      have : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ']
      omega
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨lt_of_le_of_lt hlow hb1, le_trans hb2 hhigh⟩, hbB⟩
  have hrew : ∀ r ∈ I,
      ∑ b ∈ (Ioc (2 ^ (r - d1)) (2 ^ (r + d2))).filter (· ∈ B), (1 : ℝ) / (b : ℝ) =
        ∑ b ∈ U, if 2 ^ (r - d1) < b ∧ b ≤ 2 ^ (r + d2) then (1 : ℝ) / (b : ℝ) else 0 := by
    intro r hr
    rw [← Finset.sum_filter]
    congr 1
    ext b
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · intro hb
      exact ⟨hsub r hr (Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr hb.1, hb.2⟩), hb.1⟩
    · rintro ⟨hbU, hbI⟩
      exact ⟨hbI, (Finset.mem_filter.mp hbU).2⟩
  calc ∑ r ∈ I, ∑ b ∈ (Ioc (2 ^ (r - d1)) (2 ^ (r + d2))).filter (· ∈ B), (1 : ℝ) / (b : ℝ)
      = ∑ r ∈ I, ∑ b ∈ U, if 2 ^ (r - d1) < b ∧ b ≤ 2 ^ (r + d2) then (1 : ℝ) / (b : ℝ) else 0 :=
        Finset.sum_congr rfl hrew
    _ = ∑ b ∈ U, ∑ r ∈ I, if 2 ^ (r - d1) < b ∧ b ≤ 2 ^ (r + d2) then (1 : ℝ) / (b : ℝ) else 0 :=
        Finset.sum_comm
    _ ≤ ∑ b ∈ U, ((d1 + d2 : ℕ) : ℝ) * ((1 : ℝ) / (b : ℝ)) := by
        apply Finset.sum_le_sum
        intro b _
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast card_pow2_window_add I b d1 d2 hI_ge
    _ = ((d1 + d2 : ℕ) : ℝ) * ∑ b ∈ U, (1 : ℝ) / (b : ℝ) := by rw [← Finset.mul_sum]
    _ = ((d1 + d2 : ℕ) : ℝ) * (Ssum B (m + 1) - Ssum B (m - 2)) := by
        rw [Ssum_sub_eq B (m - 2) (m + 1) (by omega)]

end OMA.BrunH2

set_option maxHeartbeats 1600000 in
theorem OMA.solution : OMA.R_Erdos675_erdos_675_variants_brun_R1.H2 := by
  classical
  intro B A N M D c hB hA hM hcop hD hc hsum
  rw [Filter.frequently_atTop]
  -- Trivial case: A is empty
  by_cases hAempty : A = ∅
  · subst hAempty
    intro X0
    refine ⟨max X0 1, le_max_left _ _, ?_⟩
    intro y T U V
    have hU : U = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro k _
      rintro ⟨b, _, _, _, a, ha, _⟩
      exact Finset.notMem_empty a ha
    have hV : V = 1 := by
      apply Finset.prod_eq_one
      intro b _; simp
    rw [hU, hV, Finset.card_empty]
    simp only [Nat.cast_zero, mul_one]
    have hxpos : (0 : ℝ) < ((max X0 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < max X0 1 by omega)
    exact mul_pos hc hxpos
  -- Main case: A is nonempty, g = A.card ≥ 1
  have hg_pos : 1 ≤ A.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hAempty)
  let g := A.card
  have hgR : (1 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg_pos
  obtain ⟨q0, a, h0, ha1, ha2⟩ := OMA.BrunH2.exists_params g
  let E0 := 2 * (g + 1) * (2 * a + 7)
  let C0 := E0 + g
  let s0 := C0 + 1
  let LD := D
  let LM := M + 1
  let C1 := max (C0 + 2) (LD + 1)
  let CB : ℝ := 6 * (g : ℝ) * (3 / 2 : ℝ) ^ (C1 + 1)
  have hCB_pos : 0 < CB := by positivity
  -- Choose ε > 0 small enough for Ranges A, B, and exponential growth ≤ 3/2
  let ε : ℝ := min (1 / (4 * (g : ℝ) * ((g : ℝ) + 1)))
    (min (c / (36 * (g : ℝ) * ((LD : ℝ) + 2) * (3 / 2 : ℝ) ^ (C1 + 1)))
         (c / (216 * CB + 1)))
  have hε_pos : 0 < ε := by
    apply lt_min (by positivity)
    apply lt_min (by positivity) (by positivity)
  have hε1 : ε ≤ 1 / (4 * (g : ℝ) * ((g : ℝ) + 1)) := min_le_left _ _
  have hε2 : ε ≤ c / (36 * (g : ℝ) * ((LD : ℝ) + 2) * (3 / 2 : ℝ) ^ (C1 + 1)) :=
    le_trans (min_le_right _ _) (min_le_left _ _)
  have hε3 : ε ≤ c / (216 * CB + 1) :=
    le_trans (min_le_right _ _) (min_le_right _ _)
  have hggε : (g : ℝ) * ((g : ℝ) + 1) * ε ≤ 1 / 4 := by
    have hden : 0 < 4 * (g : ℝ) * ((g : ℝ) + 1) := by positivity
    have := (le_div_iff₀ hden).mp hε1
    linarith
  have hexp_step : Real.exp ((g : ℝ) * ((g : ℝ) + 1) * ε) ≤ 3 / 2 :=
    OMA.BrunH2.exp_le_three_halves hggε
  -- Find M_C large enough so Range C average / V_min < c / 6
  let CC : ℝ := (g : ℝ) * ((2 : ℝ) ^ LM + 1) *
    Real.exp ((g : ℝ) * ((g : ℝ) + 1) * OMA.BrunH2.Ssum B 0) *
    ((2 ^ s0 + LM : ℕ) : ℝ) * (12 * ε)
  have hCC_nn : 0 ≤ CC := by positivity
  have hlimC : Filter.Tendsto (fun m : ℕ => CC * (3 / 4 : ℝ) ^ (m + 1)) Filter.atTop (nhds 0) := by
    have ht1 : Filter.Tendsto (fun m : ℕ => (3 / 4 : ℝ) ^ (m + 1)) Filter.atTop (nhds 0) := by
      have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 3 / 4)
        (by norm_num : (3 / 4 : ℝ) < 1)
      exact ht.comp (Filter.tendsto_add_atTop_nat 1)
    simpa only [mul_zero] using ht1.const_mul CC
  have hevC : ∀ᶠ m : ℕ in Filter.atTop, CC * (3 / 4 : ℝ) ^ (m + 1) < c / 6 :=
    hlimC.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < c / 6))
  rw [Filter.eventually_atTop] at hevC
  obtain ⟨MC, hMC⟩ := hevC
  -- Now prove the main frequently-atTop statement
  intro X0
  let Mmin := max (max (MC + 1) (max (s0 + 6) (C1 + 6)))
    (max (X0 + N + LM + 6) (LD + N + 6))
  obtain ⟨M0, hM0_ge, hRL⟩ := OMA.BrunH2.exists_record_low B hsum ε hε_pos Mmin
  have hM0_pos : 1 ≤ M0 := by omega
  let m := M0 - 1
  have hm_succ : m + 1 = M0 := by omega
  have hm_MC : MC ≤ m := by
    have : MC + 1 ≤ M0 := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hM0_ge)
    omega
  have hm_s0 : s0 + 5 ≤ m := by
    have : s0 + 6 ≤ M0 := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hM0_ge))
    omega
  have hm_C1 : C1 + 5 ≤ m := by
    have : C1 + 6 ≤ M0 := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hM0_ge))
    omega
  have hm_X0 : X0 + N + LM + 5 ≤ m := by
    have : X0 + N + LM + 6 ≤ M0 := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hM0_ge)
    omega
  have hm_LD : LD + N + 5 ≤ m := by
    have : LD + N + 6 ≤ M0 := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hM0_ge)
    omega
  have hm_3 : 3 ≤ m := by omega
  have h2s0_le : 2 ^ s0 ≤ 2 ^ (m - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hLM_le : LM ≤ 2 ^ m := le_trans (by omega : LM ≤ m) Nat.lt_two_pow_self.le
  have hS_RL : ∀ j ≤ m + 1, OMA.BrunH2.Ssum B (m + 1) - OMA.BrunH2.Ssum B j ≤
      ε * (((m + 1 : ℕ) : ℝ) - (j : ℝ)) := by
    intro j hj; rw [hm_succ]; exact hRL j (by omega)
  -- Key record-low exponential bound: exp(g(g+1)(S(m+1) - S(k))) ≤ (3/2)^(m+1-k)
  have hexp_RL : ∀ k ≤ m + 1,
      Real.exp ((g : ℝ) * ((g : ℝ) + 1) * (OMA.BrunH2.Ssum B (m + 1) - OMA.BrunH2.Ssum B k)) ≤
        (3 / 2 : ℝ) ^ (m + 1 - k) := by
    intro k hk
    have h1 := hS_RL k hk
    have hdiff : ((m + 1 : ℕ) : ℝ) - (k : ℝ) = ((m + 1 - k : ℕ) : ℝ) := by
      rw [Nat.cast_sub hk]
    rw [hdiff] at h1
    have h2 : (g : ℝ) * ((g : ℝ) + 1) * (OMA.BrunH2.Ssum B (m + 1) - OMA.BrunH2.Ssum B k) ≤
        ((m + 1 - k : ℕ) : ℝ) * ((g : ℝ) * ((g : ℝ) + 1) * ε) := by
      have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ (g : ℝ) * ((g : ℝ) + 1))
      linarith
    calc Real.exp ((g : ℝ) * ((g : ℝ) + 1) * (OMA.BrunH2.Ssum B (m + 1) - OMA.BrunH2.Ssum B k))
        ≤ Real.exp (((m + 1 - k : ℕ) : ℝ) * ((g : ℝ) * ((g : ℝ) + 1) * ε)) :=
          Real.exp_le_exp.mpr h2
      _ = (Real.exp ((g : ℝ) * ((g : ℝ) + 1) * ε)) ^ (m + 1 - k) := by
          rw [← Real.exp_nat_mul]
      _ ≤ (3 / 2 : ℝ) ^ (m + 1 - k) :=
          pow_le_pow_left₀ (Real.exp_nonneg _) hexp_step _
  -- Uniform lower bound Vmin on V(y) for all r ∈ Finset.Ico (2^(m-1)) (2^m)
  let Vmin : ℝ := Real.exp (-((g : ℝ) * ((g : ℝ) + 1) * OMA.BrunH2.Ssum B (m + 1)))
  have hVmin_pos : 0 < Vmin := Real.exp_pos _
  have hVmin_inv : Vmin⁻¹ ≤
      Real.exp ((g : ℝ) * ((g : ℝ) + 1) * OMA.BrunH2.Ssum B 0) * (3 / 2 : ℝ) ^ (m + 1) := by
    have h1 : Vmin⁻¹ = Real.exp ((g : ℝ) * ((g : ℝ) + 1) * OMA.BrunH2.Ssum B (m + 1)) := by
      simp [Vmin, Real.exp_neg]
    rw [h1]
    have hsplit : (g : ℝ) * ((g : ℝ) + 1) * OMA.BrunH2.Ssum B (m + 1) =
        (g : ℝ) * ((g : ℝ) + 1) * OMA.BrunH2.Ssum B 0 +
          (g : ℝ) * ((g : ℝ) + 1) * (OMA.BrunH2.Ssum B (m + 1) - OMA.BrunH2.Ssum B 0) := by ring
    rw [hsplit, Real.exp_add]
    have hrl0 := hexp_RL 0 (Nat.zero_le _)
    simp only [Nat.sub_zero] at hrl0
    exact mul_le_mul_of_nonneg_left hrl0 (Real.exp_pos _).le
  -- Define FB and FC on I = Finset.Ico (2^(m-1)) (2^m)
  let I := Finset.Ico (2 ^ (m - 1)) (2 ^ m)
  let FB : ℕ → ℝ := fun r =>
    ∑ s ∈ Finset.Ico s0 (m - 2), (3 / 2 : ℝ) ^ (m - s) *
      ∑ b ∈ (Finset.Ioc (2 ^ (r - 2 ^ (s + 1))) (2 ^ (r - 2 ^ s))).filter (· ∈ B), (1 : ℝ) / (b : ℝ)
  let FC : ℕ → ℝ := fun r =>
    ∑ b ∈ (Finset.Ioc (2 ^ (r - 2 ^ s0)) (2 ^ (r + LM))).filter (· ∈ B), (1 : ℝ) / (b : ℝ)
  let G : ℕ → ℝ := fun r => CB * FB r + (g : ℝ) * ((2 : ℝ) ^ LM + 1) * Vmin⁻¹ * FC r
  -- Bound ∑ r ∈ I, FB r
  have hS3 : OMA.BrunH2.Ssum B (m + 1) - OMA.BrunH2.Ssum B (m - 2) ≤ 3 * ε := by
    have h := hS_RL (m - 2) (by omega)
    have he : (((m + 1 : ℕ) : ℝ) - ((m - 2 : ℕ) : ℝ)) = 3 := by
      have hm2 : m - 2 ≤ m + 1 := by omega
      rw [← Nat.cast_sub hm2]
      have : m + 1 - (m - 2) = 3 := by omega
      rw [this]; norm_num
    rw [he] at h; linarith
  have hsum_FB : ∑ r ∈ I, FB r ≤ (2 : ℝ) ^ (m - 1) * (18 * ε) := by
    have hswap : ∑ r ∈ I, FB r =
        ∑ s ∈ Finset.Ico s0 (m - 2), (3 / 2 : ℝ) ^ (m - s) *
          ∑ r ∈ I, ∑ b ∈ (Finset.Ioc (2 ^ (r - 2 ^ (s + 1))) (2 ^ (r - 2 ^ s))).filter (· ∈ B),
            (1 : ℝ) / (b : ℝ) := by
      simp only [FB]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s _
      rw [← Finset.mul_sum]
    rw [hswap]
    have hterm : ∀ s ∈ Finset.Ico s0 (m - 2),
        (3 / 2 : ℝ) ^ (m - s) *
          (∑ r ∈ I, ∑ b ∈ (Finset.Ioc (2 ^ (r - 2 ^ (s + 1))) (2 ^ (r - 2 ^ s))).filter (· ∈ B),
            (1 : ℝ) / (b : ℝ)) ≤
        (2 : ℝ) ^ (m - 1) * (6 * ε) * (3 / 4 : ℝ) ^ (m - s) := by
      intro s hs
      obtain ⟨hs1, hs2⟩ := Finset.mem_Ico.mp hs
      have hd : 2 ^ s ≤ 2 ^ (s + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hd1 : 2 ^ (s + 1) ≤ 2 ^ (m - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hw := OMA.BrunH2.sum_window_sub_bound B m (2 ^ (s + 1)) (2 ^ s) hd hd1 hm_3
      have hsub_pow : 2 ^ (s + 1) - 2 ^ s = 2 ^ s := by rw [pow_succ]; omega
      rw [hsub_pow] at hw
      have hw2 : (∑ r ∈ I, ∑ b ∈ (Finset.Ioc (2 ^ (r - 2 ^ (s + 1))) (2 ^ (r - 2 ^ s))).filter (· ∈ B),
            (1 : ℝ) / (b : ℝ)) ≤ (2 : ℝ) ^ s * (3 * ε) := by
        have hcast : ((2 ^ s : ℕ) : ℝ) = (2 : ℝ) ^ s := by push_cast; rfl
        rw [hcast] at hw
        exact le_trans hw (mul_le_mul_of_nonneg_left hS3 (by positivity))
      have hpow_id : (3 / 2 : ℝ) ^ (m - s) * ((2 : ℝ) ^ s * (3 * ε)) =
          (2 : ℝ) ^ (m - 1) * (6 * ε) * (3 / 4 : ℝ) ^ (m - s) := by
        have h2m : (2 : ℝ) ^ m = (2 : ℝ) ^ (m - s) * (2 : ℝ) ^ s := by
          rw [← pow_add]; congr 1; omega
        have h2m1 : (2 : ℝ) ^ m = 2 * (2 : ℝ) ^ (m - 1) := by
          have : m = (m - 1) + 1 := by omega
          conv_lhs => rw [this, pow_succ']
        have h34 : (3 / 4 : ℝ) ^ (m - s) * (2 : ℝ) ^ (m - s) = (3 / 2 : ℝ) ^ (m - s) := by
          rw [← mul_pow]; norm_num
        have h2pos : (2 : ℝ) ^ (m - s) ≠ 0 := by positivity
        apply mul_right_cancel₀ h2pos
        calc (3 / 2 : ℝ) ^ (m - s) * ((2 : ℝ) ^ s * (3 * ε)) * (2 : ℝ) ^ (m - s)
            = (3 / 2 : ℝ) ^ (m - s) * ((2 : ℝ) ^ (m - s) * (2 : ℝ) ^ s) * (3 * ε) := by ring
          _ = (3 / 2 : ℝ) ^ (m - s) * (2 * (2 : ℝ) ^ (m - 1)) * (3 * ε) := by rw [← h2m, h2m1]
          _ = (2 : ℝ) ^ (m - 1) * (6 * ε) * ((3 / 4 : ℝ) ^ (m - s) * (2 : ℝ) ^ (m - s)) := by
              rw [h34]; ring
          _ = (2 : ℝ) ^ (m - 1) * (6 * ε) * (3 / 4 : ℝ) ^ (m - s) * (2 : ℝ) ^ (m - s) := by ring
      calc (3 / 2 : ℝ) ^ (m - s) *
            (∑ r ∈ I, ∑ b ∈ (Finset.Ioc (2 ^ (r - 2 ^ (s + 1))) (2 ^ (r - 2 ^ s))).filter (· ∈ B),
              (1 : ℝ) / (b : ℝ))
          ≤ (3 / 2 : ℝ) ^ (m - s) * ((2 : ℝ) ^ s * (3 * ε)) :=
            mul_le_mul_of_nonneg_left hw2 (by positivity)
        _ = (2 : ℝ) ^ (m - 1) * (6 * ε) * (3 / 4 : ℝ) ^ (m - s) := hpow_id
    calc ∑ s ∈ Finset.Ico s0 (m - 2), (3 / 2 : ℝ) ^ (m - s) *
            (∑ r ∈ I, ∑ b ∈ (Finset.Ioc (2 ^ (r - 2 ^ (s + 1))) (2 ^ (r - 2 ^ s))).filter (· ∈ B),
              (1 : ℝ) / (b : ℝ))
        ≤ ∑ s ∈ Finset.Ico s0 (m - 2), (2 : ℝ) ^ (m - 1) * (6 * ε) * (3 / 4 : ℝ) ^ (m - s) :=
          Finset.sum_le_sum hterm
      _ = (2 : ℝ) ^ (m - 1) * (6 * ε) * ∑ s ∈ Finset.Ico s0 (m - 2), (3 / 4 : ℝ) ^ (m - s) := by
          rw [← Finset.mul_sum]
      _ ≤ (2 : ℝ) ^ (m - 1) * (6 * ε) * 3 :=
          mul_le_mul_of_nonneg_left (OMA.BrunH2.sum_three_fourths_shell s0 m) (by positivity)
      _ = (2 : ℝ) ^ (m - 1) * (18 * ε) := by ring
  -- Bound ∑ r ∈ I, FC r
  have hsum_FC : ∑ r ∈ I, FC r ≤ ((2 ^ s0 + LM : ℕ) : ℝ) * (3 * ε) := by
    have hw := OMA.BrunH2.sum_window_add_bound B m (2 ^ s0) LM h2s0_le hLM_le hm_3
    exact le_trans hw (mul_le_mul_of_nonneg_left hS3 (by positivity))
  -- Total sum of G over I is < |I| * (c / 3)
  have hI_card : (I.card : ℝ) = (2 : ℝ) ^ (m - 1) := by
    have hnat : I.card = 2 ^ (m - 1) := by
      simp only [I, Nat.card_Ico]
      have h2m : 2 ^ m = 2 * 2 ^ (m - 1) := by
        have : m = (m - 1) + 1 := by omega
        conv_lhs => rw [this, pow_succ']
      rw [h2m]; omega
    exact_mod_cast hnat
  have hI_pos : (0 : ℝ) < (2 : ℝ) ^ (m - 1) := by positivity
  have hCB_lt : CB * (18 * ε) < c / 6 := by
    have h1 : ε * (216 * CB + 1) ≤ c := (le_div_iff₀ (by positivity)).mp hε3
    nlinarith
  have hC_term_lt : (g : ℝ) * ((2 : ℝ) ^ LM + 1) * Vmin⁻¹ *
      (((2 ^ s0 + LM : ℕ) : ℝ) * (3 * ε)) < (2 : ℝ) ^ (m - 1) * (c / 6) := by
    have h2eq : (3 / 2 : ℝ) ^ (m + 1) = (2 : ℝ) ^ (m - 1) * 4 * (3 / 4 : ℝ) ^ (m + 1) := by
      have h2m1 : (2 : ℝ) ^ (m + 1) = (2 : ℝ) ^ (m - 1) * 4 := by
        have : m + 1 = (m - 1) + 2 := by omega
        rw [this, pow_add]; norm_num
      have h34 : (3 / 4 : ℝ) ^ (m + 1) * (2 : ℝ) ^ (m + 1) = (3 / 2 : ℝ) ^ (m + 1) := by
        rw [← mul_pow]; norm_num
      rw [← h34, h2m1]; ring
    have hle1 : (g : ℝ) * ((2 : ℝ) ^ LM + 1) * Vmin⁻¹ * (((2 ^ s0 + LM : ℕ) : ℝ) * (3 * ε)) ≤
        (2 : ℝ) ^ (m - 1) * (CC * (3 / 4 : ℝ) ^ (m + 1)) := by
      have hmul := mul_le_mul_of_nonneg_left hVmin_inv
        (by positivity : (0 : ℝ) ≤ (g : ℝ) * ((2 : ℝ) ^ LM + 1))
      have hmul2 := mul_le_mul_of_nonneg_right hmul
        (by positivity : (0 : ℝ) ≤ ((2 ^ s0 + LM : ℕ) : ℝ) * (3 * ε))
      refine le_trans hmul2 (le_of_eq ?_)
      rw [h2eq]
      dsimp only [CC]; ring
    have hCC_lt : CC * (3 / 4 : ℝ) ^ (m + 1) < c / 6 := hMC m hm_MC
    have hmul3 := mul_lt_mul_of_pos_left hCC_lt hI_pos
    linarith
  have hsum_G : ∑ r ∈ I, G r < (I.card : ℝ) * (c / 3) := by
    have hsplit : ∑ r ∈ I, G r =
        CB * (∑ r ∈ I, FB r) + (g : ℝ) * ((2 : ℝ) ^ LM + 1) * Vmin⁻¹ * (∑ r ∈ I, FC r) := by
      simp only [G, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hsplit, hI_card]
    have hB1 : CB * (∑ r ∈ I, FB r) ≤ (2 : ℝ) ^ (m - 1) * (CB * (18 * ε)) := by
      have := mul_le_mul_of_nonneg_left hsum_FB hCB_pos.le
      linarith
    have hB2 : (2 : ℝ) ^ (m - 1) * (CB * (18 * ε)) < (2 : ℝ) ^ (m - 1) * (c / 6) :=
      mul_lt_mul_of_pos_left hCB_lt hI_pos
    have hC1 : (g : ℝ) * ((2 : ℝ) ^ LM + 1) * Vmin⁻¹ * (∑ r ∈ I, FC r) ≤
        (g : ℝ) * ((2 : ℝ) ^ LM + 1) * Vmin⁻¹ * (((2 ^ s0 + LM : ℕ) : ℝ) * (3 * ε)) :=
      mul_le_mul_of_nonneg_left hsum_FC (by positivity)
    linarith
  -- Pigeonhole: pick r ∈ I with G r < c / 3
  have hex_r : ∃ r ∈ I, G r < c / 3 := by
    by_contra hall
    push_neg at hall
    have hge : (I.card : ℝ) * (c / 3) ≤ ∑ r ∈ I, G r := by
      calc (I.card : ℝ) * (c / 3) = ∑ _r ∈ I, (c / 3) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ r ∈ I, G r := Finset.sum_le_sum hall
    linarith
  obtain ⟨r, hrI, hGr⟩ := hex_r
  obtain ⟨hr1, hr2⟩ := Finset.mem_Ico.mp hrI
  -- Witness x := 2 ^ r
  refine ⟨2 ^ r, ?_, ?_⟩
  · have h1 : X0 ≤ m - 1 := by omega
    have h2 : m - 1 ≤ 2 ^ (m - 1) := Nat.lt_two_pow_self.le
    have h3 : r ≤ 2 ^ r := Nat.lt_two_pow_self.le
    omega
  intro y T U V
  have hxpos : (0 : ℝ) < ((2 ^ r : ℕ) : ℝ) := by positivity
  have hVpos : 0 < V := OMA.BrunH2.V_pos B A N y hA
  have hy_bounds := OMA.BrunH2.y_pow2_bounds r m D hD (by omega) hr1
  have hy_ge : 2 ^ 2 ^ (m - 1 - LD) ≤ y := hy_bounds.1
  have hy_le : y ≤ 2 ^ r := hy_bounds.2
  have hr_le_m1 : 2 ^ r ≤ 2 ^ 2 ^ (m + 1) :=
    Nat.pow_le_pow_right (by norm_num) (le_trans hr2.le (Nat.pow_le_pow_right (by norm_num) (by omega)))
  have hy_le_m1 : y ≤ 2 ^ 2 ^ (m + 1) := le_trans hy_le hr_le_m1
  have hV_ge_min : Vmin ≤ V := OMA.BrunH2.V_lower_bound B A N y (m + 1) hA hy_le_m1
  have hN_lt_y : N < y := by
    have h1 : N < m - 1 - LD := by omega
    have h2 : m - 1 - LD ≤ 2 ^ (m - 1 - LD) := Nat.lt_two_pow_self.le
    have h3 : 2 ^ (m - 1 - LD) ≤ 2 ^ 2 ^ (m - 1 - LD) := Nat.lt_two_pow_self.le
    omega
  have hN_le_x : N ≤ 2 ^ r := le_trans hN_lt_y.le hy_le
  -- Bound every b dividing a + M * k (k ∈ U) by 2 ^ (r + LM)
  have hb_ub : ∀ b, (∃ k ∈ Finset.Icc 1 (2 ^ r), ∃ a0 ∈ A, b ∣ a0 + M * k) → b ≤ 2 ^ (r + LM) := by
    rintro b ⟨k, hk, a0, ha0, hdvd⟩
    obtain ⟨hk1, hkx⟩ := Finset.mem_Icc.mp hk
    obtain ⟨ha1', haN⟩ := Finset.mem_Icc.mp (hA ha0)
    have hpos_sum : 0 < a0 + M * k := by omega
    have hle1 : b ≤ a0 + M * k := Nat.le_of_dvd hpos_sum hdvd
    have hle2 : a0 + M * k ≤ (M + 1) * 2 ^ r := by
      have : M * k ≤ M * 2 ^ r := Nat.mul_le_mul_left M hkx
      nlinarith
    have hle3 : M + 1 ≤ 2 ^ LM := Nat.lt_two_pow_self.le
    calc b ≤ (M + 1) * 2 ^ r := le_trans hle1 hle2
      _ ≤ 2 ^ LM * 2 ^ r := Nat.mul_le_mul_right _ hle3
      _ = 2 ^ (r + LM) := by rw [← pow_add, add_comm]
  -- Partition moduli into RA, RB s (s ∈ Finset.Ico s0 (m-2)), RC
  let RA := (Finset.Ioc y (2 ^ (r - 2 ^ (m - 2)))).filter (· ∈ B)
  let RB : ℕ → Finset ℕ := fun s =>
    (Finset.Ioc (2 ^ (r - 2 ^ (s + 1))) (2 ^ (r - 2 ^ s))).filter (· ∈ B)
  let RC := (Finset.Ioc (2 ^ (r - 2 ^ s0)) (2 ^ (r + LM))).filter (· ∈ B)
  let hit : ℕ → Finset ℕ := fun b => T.filter (fun k => ∃ a0 ∈ A, b ∣ a0 + M * k)
  have hU_sub : U ⊆ RA.biUnion hit ∪
      ((Finset.Ico s0 (m - 2)).biUnion (fun s => ((RB s).filter (fun b => y < b)).biUnion hit)) ∪
      ((RC.filter (fun b => y < b)).biUnion hit) := by
    intro k hkU
    obtain ⟨hkT, b, hbB, hbN, hby, a0, ha0, hdvd⟩ := Finset.mem_filter.mp hkU
    have hkI : k ∈ Finset.Icc 1 (2 ^ r) := (Finset.mem_filter.mp hkT).1
    have hble : b ≤ 2 ^ (r + LM) := hb_ub b ⟨k, hkI, a0, ha0, hdvd⟩
    have hkhit : k ∈ hit b := Finset.mem_filter.mpr ⟨hkT, a0, ha0, hdvd⟩
    by_cases h1 : b ≤ 2 ^ (r - 2 ^ (m - 2))
    · apply Finset.mem_union_left; apply Finset.mem_union_left
      exact Finset.mem_biUnion.mpr ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hby, h1⟩, hbB⟩, hkhit⟩
    · by_cases h2 : b ≤ 2 ^ (r - 2 ^ s0)
      · apply Finset.mem_union_left; apply Finset.mem_union_right
        have h2m2 : 2 ^ (m - 2) ≤ r := le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) hr1
        obtain ⟨s, hs, hs1, hs2⟩ := OMA.BrunH2.shell_cover r s0 m b (by omega) h2m2 (by omega) h2
        refine Finset.mem_biUnion.mpr ⟨s, hs, Finset.mem_biUnion.mpr ⟨b, ?_, hkhit⟩⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hs1, hs2⟩, hbB⟩, hby⟩
      · apply Finset.mem_union_right
        refine Finset.mem_biUnion.mpr ⟨b, ?_, hkhit⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega, hble⟩, hbB⟩, hby⟩
  have hU_card : (U.card : ℝ) ≤
      (∑ b ∈ RA, ((hit b).card : ℝ)) +
      (∑ s ∈ Finset.Ico s0 (m - 2), ∑ b ∈ (RB s).filter (fun b => y < b), ((hit b).card : ℝ)) +
      (∑ b ∈ RC.filter (fun b => y < b), ((hit b).card : ℝ)) := by
    have hnat : U.card ≤
        (∑ b ∈ RA, (hit b).card) +
        (∑ s ∈ Finset.Ico s0 (m - 2), ∑ b ∈ (RB s).filter (fun b => y < b), (hit b).card) +
        (∑ b ∈ RC.filter (fun b => y < b), (hit b).card) := by
      calc U.card
          ≤ (RA.biUnion hit ∪
              ((Finset.Ico s0 (m - 2)).biUnion (fun s => ((RB s).filter (fun b => y < b)).biUnion hit)) ∪
              ((RC.filter (fun b => y < b)).biUnion hit)).card := Finset.card_le_card hU_sub
        _ ≤ (RA.biUnion hit ∪
              ((Finset.Ico s0 (m - 2)).biUnion (fun s => ((RB s).filter (fun b => y < b)).biUnion hit))).card +
              ((RC.filter (fun b => y < b)).biUnion hit).card := Finset.card_union_le _ _
        _ ≤ (RA.biUnion hit).card +
              ((Finset.Ico s0 (m - 2)).biUnion (fun s => ((RB s).filter (fun b => y < b)).biUnion hit)).card +
              ((RC.filter (fun b => y < b)).biUnion hit).card := by
            have := Finset.card_union_le (RA.biUnion hit)
              ((Finset.Ico s0 (m - 2)).biUnion (fun s => ((RB s).filter (fun b => y < b)).biUnion hit))
            omega
        _ ≤ (∑ b ∈ RA, (hit b).card) +
              (∑ s ∈ Finset.Ico s0 (m - 2), (((RB s).filter (fun b => y < b)).biUnion hit).card) +
              (∑ b ∈ RC.filter (fun b => y < b), (hit b).card) := by
            have h1 := Finset.card_biUnion_le (s := RA) (t := hit)
            have h2 := Finset.card_biUnion_le (s := Finset.Ico s0 (m - 2))
              (t := fun s => ((RB s).filter (fun b => y < b)).biUnion hit)
            have h3 := Finset.card_biUnion_le (s := RC.filter (fun b => y < b)) (t := hit)
            omega
        _ ≤ (∑ b ∈ RA, (hit b).card) +
              (∑ s ∈ Finset.Ico s0 (m - 2), ∑ b ∈ (RB s).filter (fun b => y < b), (hit b).card) +
              (∑ b ∈ RC.filter (fun b => y < b), (hit b).card) := by
            have h4 : ∑ s ∈ Finset.Ico s0 (m - 2), (((RB s).filter (fun b => y < b)).biUnion hit).card ≤
                ∑ s ∈ Finset.Ico s0 (m - 2), ∑ b ∈ (RB s).filter (fun b => y < b), (hit b).card :=
              Finset.sum_le_sum (fun s _ => Finset.card_biUnion_le)
            omega
    exact_mod_cast hnat
  -- Bound Range A
  have hRangeA : (∑ b ∈ RA, ((hit b).card : ℝ)) ≤ (c / 3) * ((2 ^ r : ℕ) : ℝ) * V := by
    let kA := m - C1
    have hkA1 : 1 ≤ kA := by omega
    have hkA_le : kA ≤ m + 1 := by omega
    have hkA_y : 2 ^ 2 ^ kA ≤ y := by
      refine le_trans ?_ hy_ge
      apply Nat.pow_le_pow_right (by norm_num)
      apply Nat.pow_le_pow_right (by norm_num)
      have : LD + 1 ≤ C1 := le_max_right _ _
      omega
    have hkA_exp : (2 ^ 2 ^ kA) ^ (2 * (A.card + 1) * (2 * a + 7) + A.card) ≤ 2 ^ 2 ^ (m - 2) := by
      have hC0_le : 2 * (A.card + 1) * (2 * a + 7) + A.card ≤ 2 ^ C0 := Nat.lt_two_pow_self.le
      have hkA_C0 : kA + C0 ≤ m - 2 := by
        have : C0 + 2 ≤ C1 := le_max_left _ _
        omega
      calc (2 ^ 2 ^ kA) ^ (2 * (A.card + 1) * (2 * a + 7) + A.card)
          ≤ (2 ^ 2 ^ kA) ^ (2 ^ C0) := Nat.pow_le_pow_right Nat.one_le_two_pow hC0_le
        _ = 2 ^ (2 ^ kA * 2 ^ C0) := (pow_mul 2 _ _).symm
        _ = 2 ^ 2 ^ (kA + C0) := by rw [← pow_add]
        _ ≤ 2 ^ 2 ^ (m - 2) := Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by norm_num) hkA_C0)
    have hVratioA :
        (∏ b' ∈ (Finset.Ioc N (2 ^ 2 ^ kA)).filter (· ∈ B), (1 - (A.card : ℝ) / (b' : ℝ))) ≤
          (3 / 2 : ℝ) ^ (C1 + 1) * V := by
      have hrA := OMA.BrunH2.V_ratio_bound B A N kA y (m + 1) hA hkA_y hy_le_m1 hkA_le
      have hexpA := hexp_RL kA hkA_le
      have hsubA : m + 1 - kA = C1 + 1 := by omega
      rw [hsubA] at hexpA
      exact le_trans hrA (mul_le_mul_of_nonneg_right hexpA hVpos.le)
    have hperA : ∀ b ∈ RA,
        ((hit b).card : ℝ) ≤
          6 * (g : ℝ) * (3 / 2 : ℝ) ^ (C1 + 1) * ((2 ^ r : ℕ) : ℝ) * V * ((1 : ℝ) / (b : ℝ)) := by
      intro b hb
      obtain ⟨hbI, hbB⟩ := Finset.mem_filter.mp hb
      obtain ⟨hby, hb_ub'⟩ := Finset.mem_Ioc.mp hbI
      have hbN : N < b := lt_trans hN_lt_y hby
      have hxb : b * (2 ^ 2 ^ kA) ^ (2 * (A.card + 1) * (2 * a + 7) + A.card) ≤ 2 ^ r := by
        have h2m2 : 2 ^ (m - 2) ≤ r := le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) hr1
        calc b * (2 ^ 2 ^ kA) ^ (2 * (A.card + 1) * (2 * a + 7) + A.card)
            ≤ 2 ^ (r - 2 ^ (m - 2)) * 2 ^ 2 ^ (m - 2) := Nat.mul_le_mul hb_ub' hkA_exp
          _ = 2 ^ (r - 2 ^ (m - 2) + 2 ^ (m - 2)) := (pow_add 2 _ _).symm
          _ = 2 ^ r := by congr 1; omega
      have hs := OMA.BrunH2.hit_sieve_bound B A N M hB hA hcop (2 ^ r) y b kA q0 a
        hbB hbN hby hkA1 hkA_y h0 ha1 ha2 hxb
      calc ((hit b).card : ℝ)
          ≤ 6 * (g : ℝ) * (((2 ^ r : ℕ) : ℝ) / (b : ℝ)) *
              ∏ b' ∈ (Finset.Ioc N (2 ^ 2 ^ kA)).filter (· ∈ B), (1 - (A.card : ℝ) / (b' : ℝ)) := hs
        _ ≤ 6 * (g : ℝ) * (((2 ^ r : ℕ) : ℝ) / (b : ℝ)) * ((3 / 2 : ℝ) ^ (C1 + 1) * V) :=
            mul_le_mul_of_nonneg_left hVratioA (by positivity)
        _ = 6 * (g : ℝ) * (3 / 2 : ℝ) ^ (C1 + 1) * ((2 ^ r : ℕ) : ℝ) * V * ((1 : ℝ) / (b : ℝ)) := by ring
    have hsumRA : ∑ b ∈ RA, (1 : ℝ) / (b : ℝ) ≤ ε * ((LD : ℝ) + 2) := by
      have hsub : RA ⊆ (Finset.Ioc (2 ^ 2 ^ (m - 1 - LD)) (2 ^ 2 ^ (m + 1))).filter (· ∈ B) := by
        intro b hb
        obtain ⟨hbI, hbB⟩ := Finset.mem_filter.mp hb
        obtain ⟨hby, hb_ub'⟩ := Finset.mem_Ioc.mp hbI
        have hle_m1 : 2 ^ (r - 2 ^ (m - 2)) ≤ 2 ^ 2 ^ (m + 1) :=
          le_trans (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le r _)) hr_le_m1
        exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨lt_of_le_of_lt hy_ge hby,
          le_trans hb_ub' hle_m1⟩, hbB⟩
      have h1 : ∑ b ∈ RA, (1 : ℝ) / (b : ℝ) ≤
          OMA.BrunH2.Ssum B (m + 1) - OMA.BrunH2.Ssum B (m - 1 - LD) := by
        rw [← OMA.BrunH2.Ssum_sub_eq B (m - 1 - LD) (m + 1) (by omega)]
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      have h2 := hS_RL (m - 1 - LD) (by omega)
      have he : (((m + 1 : ℕ) : ℝ) - ((m - 1 - LD : ℕ) : ℝ)) = (LD : ℝ) + 2 := by
        have hle' : m - 1 - LD ≤ m + 1 := by omega
        rw [← Nat.cast_sub hle']
        have : m + 1 - (m - 1 - LD) = LD + 2 := by omega
        rw [this]; push_cast; ring
      rw [he] at h2
      linarith
    have hcoefA : 6 * (g : ℝ) * (3 / 2 : ℝ) ^ (C1 + 1) * (ε * ((LD : ℝ) + 2)) ≤ c / 3 := by
      have hden : 0 < 36 * (g : ℝ) * ((LD : ℝ) + 2) * (3 / 2 : ℝ) ^ (C1 + 1) := by positivity
      have := (le_div_iff₀ hden).mp hε2
      linarith
    calc ∑ b ∈ RA, ((hit b).card : ℝ)
        ≤ ∑ b ∈ RA, (6 * (g : ℝ) * (3 / 2 : ℝ) ^ (C1 + 1) * ((2 ^ r : ℕ) : ℝ) * V * ((1 : ℝ) / (b : ℝ))) :=
          Finset.sum_le_sum hperA
      _ = 6 * (g : ℝ) * (3 / 2 : ℝ) ^ (C1 + 1) * ((2 ^ r : ℕ) : ℝ) * V * ∑ b ∈ RA, (1 : ℝ) / (b : ℝ) := by
          rw [← Finset.mul_sum]
      _ ≤ 6 * (g : ℝ) * (3 / 2 : ℝ) ^ (C1 + 1) * ((2 ^ r : ℕ) : ℝ) * V * (ε * ((LD : ℝ) + 2)) :=
          mul_le_mul_of_nonneg_left hsumRA (by positivity)
      _ = (6 * (g : ℝ) * (3 / 2 : ℝ) ^ (C1 + 1) * (ε * ((LD : ℝ) + 2))) * (((2 ^ r : ℕ) : ℝ) * V) := by ring
      _ ≤ (c / 3) * (((2 ^ r : ℕ) : ℝ) * V) := mul_le_mul_of_nonneg_right hcoefA (by positivity)
      _ = (c / 3) * ((2 ^ r : ℕ) : ℝ) * V := by ring
  -- Bound Range B
  have hRangeB :
      (∑ s ∈ Finset.Ico s0 (m - 2), ∑ b ∈ (RB s).filter (fun b => y < b), ((hit b).card : ℝ)) ≤
        CB * FB r * ((2 ^ r : ℕ) : ℝ) * V := by
    have hperS : ∀ s ∈ Finset.Ico s0 (m - 2),
        (∑ b ∈ (RB s).filter (fun b => y < b), ((hit b).card : ℝ)) ≤
          CB * (3 / 2 : ℝ) ^ (m - s) * ((2 ^ r : ℕ) : ℝ) * V *
            ∑ b ∈ RB s, (1 : ℝ) / (b : ℝ) := by
      intro s hs
      obtain ⟨hs1, hs2⟩ := Finset.mem_Ico.mp hs
      let ks := min (s - C0) (m - 1 - LD)
      have hks1 : 1 ≤ ks := by omega
      have hks_le : ks ≤ m + 1 := by omega
      have hks_y : 2 ^ 2 ^ ks ≤ y := by
        refine le_trans ?_ hy_ge
        apply Nat.pow_le_pow_right (by norm_num)
        apply Nat.pow_le_pow_right (by norm_num)
        exact min_le_right _ _
      have hks_exp : (2 ^ 2 ^ ks) ^ (2 * (A.card + 1) * (2 * a + 7) + A.card) ≤ 2 ^ 2 ^ s := by
        have hC0_le : 2 * (A.card + 1) * (2 * a + 7) + A.card ≤ 2 ^ C0 := Nat.lt_two_pow_self.le
        have hks_C0 : ks + C0 ≤ s := by
          have : ks ≤ s - C0 := min_le_left _ _
          omega
        calc (2 ^ 2 ^ ks) ^ (2 * (A.card + 1) * (2 * a + 7) + A.card)
            ≤ (2 ^ 2 ^ ks) ^ (2 ^ C0) := Nat.pow_le_pow_right Nat.one_le_two_pow hC0_le
          _ = 2 ^ (2 ^ ks * 2 ^ C0) := (pow_mul 2 _ _).symm
          _ = 2 ^ 2 ^ (ks + C0) := by rw [← pow_add]
          _ ≤ 2 ^ 2 ^ s := Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by norm_num) hks_C0)
      have hVratioS :
          (∏ b' ∈ (Finset.Ioc N (2 ^ 2 ^ ks)).filter (· ∈ B), (1 - (A.card : ℝ) / (b' : ℝ))) ≤
            (3 / 2 : ℝ) ^ (C1 + 1) * (3 / 2 : ℝ) ^ (m - s) * V := by
        have hrS := OMA.BrunH2.V_ratio_bound B A N ks y (m + 1) hA hks_y hy_le_m1 hks_le
        have hexpS := hexp_RL ks hks_le
        have hdiff_le : m + 1 - ks ≤ (C1 + 1) + (m - s) := by
          have hC1_1 : C0 + 2 ≤ C1 := le_max_left _ _
          have hC1_2 : LD + 1 ≤ C1 := le_max_right _ _
          omega
        have hpow_le : (3 / 2 : ℝ) ^ (m + 1 - ks) ≤ (3 / 2 : ℝ) ^ (C1 + 1) * (3 / 2 : ℝ) ^ (m - s) := by
          rw [← pow_add]
          exact pow_le_pow_right₀ (by norm_num) hdiff_le
        exact le_trans hrS (mul_le_mul_of_nonneg_right (le_trans hexpS hpow_le) hVpos.le)
      have hperB : ∀ b ∈ (RB s).filter (fun b => y < b),
          ((hit b).card : ℝ) ≤
            CB * (3 / 2 : ℝ) ^ (m - s) * ((2 ^ r : ℕ) : ℝ) * V * ((1 : ℝ) / (b : ℝ)) := by
        intro b hb
        obtain ⟨hbRB, hby⟩ := Finset.mem_filter.mp hb
        obtain ⟨hbI, hbB⟩ := Finset.mem_filter.mp hbRB
        obtain ⟨_, hb_ub'⟩ := Finset.mem_Ioc.mp hbI
        have hbN : N < b := lt_trans hN_lt_y hby
        have hxb : b * (2 ^ 2 ^ ks) ^ (2 * (A.card + 1) * (2 * a + 7) + A.card) ≤ 2 ^ r := by
          have h2s : 2 ^ s ≤ r := le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) hr1
          calc b * (2 ^ 2 ^ ks) ^ (2 * (A.card + 1) * (2 * a + 7) + A.card)
              ≤ 2 ^ (r - 2 ^ s) * 2 ^ 2 ^ s := Nat.mul_le_mul hb_ub' hks_exp
            _ = 2 ^ (r - 2 ^ s + 2 ^ s) := (pow_add 2 _ _).symm
            _ = 2 ^ r := by congr 1; omega
        have hsb := OMA.BrunH2.hit_sieve_bound B A N M hB hA hcop (2 ^ r) y b ks q0 a
          hbB hbN hby hks1 hks_y h0 ha1 ha2 hxb
        calc ((hit b).card : ℝ)
            ≤ 6 * (g : ℝ) * (((2 ^ r : ℕ) : ℝ) / (b : ℝ)) *
                ∏ b' ∈ (Finset.Ioc N (2 ^ 2 ^ ks)).filter (· ∈ B), (1 - (A.card : ℝ) / (b' : ℝ)) := hsb
          _ ≤ 6 * (g : ℝ) * (((2 ^ r : ℕ) : ℝ) / (b : ℝ)) *
                ((3 / 2 : ℝ) ^ (C1 + 1) * (3 / 2 : ℝ) ^ (m - s) * V) :=
              mul_le_mul_of_nonneg_left hVratioS (by positivity)
          _ = CB * (3 / 2 : ℝ) ^ (m - s) * ((2 ^ r : ℕ) : ℝ) * V * ((1 : ℝ) / (b : ℝ)) := by
              dsimp only [CB]; ring
      calc ∑ b ∈ (RB s).filter (fun b => y < b), ((hit b).card : ℝ)
          ≤ ∑ b ∈ (RB s).filter (fun b => y < b),
              (CB * (3 / 2 : ℝ) ^ (m - s) * ((2 ^ r : ℕ) : ℝ) * V * ((1 : ℝ) / (b : ℝ))) :=
            Finset.sum_le_sum hperB
        _ = CB * (3 / 2 : ℝ) ^ (m - s) * ((2 ^ r : ℕ) : ℝ) * V *
              ∑ b ∈ (RB s).filter (fun b => y < b), (1 : ℝ) / (b : ℝ) := by rw [← Finset.mul_sum]
        _ ≤ CB * (3 / 2 : ℝ) ^ (m - s) * ((2 ^ r : ℕ) : ℝ) * V *
              ∑ b ∈ RB s, (1 : ℝ) / (b : ℝ) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => by positivity)
    calc ∑ s ∈ Finset.Ico s0 (m - 2), ∑ b ∈ (RB s).filter (fun b => y < b), ((hit b).card : ℝ)
        ≤ ∑ s ∈ Finset.Ico s0 (m - 2),
            (CB * (3 / 2 : ℝ) ^ (m - s) * ((2 ^ r : ℕ) : ℝ) * V * ∑ b ∈ RB s, (1 : ℝ) / (b : ℝ)) :=
          Finset.sum_le_sum hperS
      _ = CB * ((2 ^ r : ℕ) : ℝ) * V *
            ∑ s ∈ Finset.Ico s0 (m - 2), (3 / 2 : ℝ) ^ (m - s) * ∑ b ∈ RB s, (1 : ℝ) / (b : ℝ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro s _; ring
      _ = CB * FB r * ((2 ^ r : ℕ) : ℝ) * V := by dsimp only [FB, RB]; ring
  -- Bound Range C
  have hRangeC :
      (∑ b ∈ RC.filter (fun b => y < b), ((hit b).card : ℝ)) ≤
        (g : ℝ) * ((2 : ℝ) ^ LM + 1) * Vmin⁻¹ * FC r * ((2 ^ r : ℕ) : ℝ) * V := by
    have hVratioC : (1 : ℝ) ≤ Vmin⁻¹ * V := by
      have h1 : Vmin⁻¹ * Vmin = 1 := inv_mul_cancel₀ hVmin_pos.ne'
      have h2 := mul_le_mul_of_nonneg_left hV_ge_min (inv_nonneg.mpr hVmin_pos.le)
      linarith
    have hperC : ∀ b ∈ RC.filter (fun b => y < b),
        ((hit b).card : ℝ) ≤
          (g : ℝ) * ((2 : ℝ) ^ LM + 1) * ((2 ^ r : ℕ) : ℝ) * ((1 : ℝ) / (b : ℝ)) := by
      intro b hb
      obtain ⟨hbRC, hby⟩ := Finset.mem_filter.mp hb
      obtain ⟨hbI, hbB⟩ := Finset.mem_filter.mp hbRC
      obtain ⟨_, hb_ub'⟩ := Finset.mem_Ioc.mp hbI
      have hbN : N < b := lt_trans hN_lt_y hby
      have hbpos : 0 < b := by omega
      have hbM : b ≤ 2 ^ LM * 2 ^ r := by
        simpa only [← pow_add, add_comm] using hb_ub'
      have htriv := OMA.BrunH2.hit_trivial_bound A M (2 ^ r) b LM T (Finset.filter_subset _ _)
        hbpos (hcop b hbB hbN) hbM
      calc ((hit b).card : ℝ)
          ≤ (g : ℝ) * ((2 : ℝ) ^ LM + 1) * (((2 ^ r : ℕ) : ℝ) / (b : ℝ)) := htriv
        _ = (g : ℝ) * ((2 : ℝ) ^ LM + 1) * ((2 ^ r : ℕ) : ℝ) * ((1 : ℝ) / (b : ℝ)) := by ring
    have hC_raw : ∑ b ∈ RC.filter (fun b => y < b), ((hit b).card : ℝ) ≤
        (g : ℝ) * ((2 : ℝ) ^ LM + 1) * FC r * ((2 ^ r : ℕ) : ℝ) := by
      calc ∑ b ∈ RC.filter (fun b => y < b), ((hit b).card : ℝ)
          ≤ ∑ b ∈ RC.filter (fun b => y < b),
              ((g : ℝ) * ((2 : ℝ) ^ LM + 1) * ((2 ^ r : ℕ) : ℝ) * ((1 : ℝ) / (b : ℝ))) :=
            Finset.sum_le_sum hperC
        _ = (g : ℝ) * ((2 : ℝ) ^ LM + 1) * ((2 ^ r : ℕ) : ℝ) *
              ∑ b ∈ RC.filter (fun b => y < b), (1 : ℝ) / (b : ℝ) := by rw [← Finset.mul_sum]
        _ ≤ (g : ℝ) * ((2 : ℝ) ^ LM + 1) * ((2 ^ r : ℕ) : ℝ) * FC r := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => by positivity)
        _ = (g : ℝ) * ((2 : ℝ) ^ LM + 1) * FC r * ((2 ^ r : ℕ) : ℝ) := by ring
    have hnn : 0 ≤ (g : ℝ) * ((2 : ℝ) ^ LM + 1) * FC r * ((2 ^ r : ℕ) : ℝ) := by
      have hFC_nn : 0 ≤ FC r := Finset.sum_nonneg (fun _ _ => by positivity)
      positivity
    calc ∑ b ∈ RC.filter (fun b => y < b), ((hit b).card : ℝ)
        ≤ (g : ℝ) * ((2 : ℝ) ^ LM + 1) * FC r * ((2 ^ r : ℕ) : ℝ) := hC_raw
      _ ≤ (g : ℝ) * ((2 : ℝ) ^ LM + 1) * FC r * ((2 ^ r : ℕ) : ℝ) * (Vmin⁻¹ * V) :=
          le_mul_of_one_le_right hnn hVratioC
      _ = (g : ℝ) * ((2 : ℝ) ^ LM + 1) * Vmin⁻¹ * FC r * ((2 ^ r : ℕ) : ℝ) * V := by ring
  -- Combine Ranges A, B, C using G r < c / 3
  have hBC : CB * FB r * ((2 ^ r : ℕ) : ℝ) * V +
      (g : ℝ) * ((2 : ℝ) ^ LM + 1) * Vmin⁻¹ * FC r * ((2 ^ r : ℕ) : ℝ) * V =
      G r * (((2 ^ r : ℕ) : ℝ) * V) := by
    dsimp only [G]; ring
  have hG_lt : G r * (((2 ^ r : ℕ) : ℝ) * V) < (c / 3) * (((2 ^ r : ℕ) : ℝ) * V) :=
    mul_lt_mul_of_pos_right hGr (mul_pos hxpos hVpos)
  have hfinal : (U.card : ℝ) < (2 * c / 3) * ((2 ^ r : ℕ) : ℝ) * V := by linarith
  have hthird : (2 * c / 3) * ((2 ^ r : ℕ) : ℝ) * V < c * ((2 ^ r : ℕ) : ℝ) * V := by
    have : 0 < (c / 3) * (((2 ^ r : ℕ) : ℝ) * V) := mul_pos (by linarith) (mul_pos hxpos hVpos)
    linarith
  exact lt_trans hfinal hthird
