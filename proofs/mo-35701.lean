import OMAStatements.S_mo_35701
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.ULift
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Group
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace Mo35701

/-! Section 1: Generic Frobenius group Frob p q r = ZMod p ⋊_r ZMod q -/

structure Frob (p q : ℕ) (r : ZMod p) where
  a : ZMod p
  b : ZMod q
  deriving DecidableEq

lemma Frob.ext {p q : ℕ} {r : ZMod p} {x y : Frob p q r}
    (ha : x.a = y.a) (hb : x.b = y.b) : x = y := by
  cases x; cases y; simp_all

class FrobSpec (p q : ℕ) (r : ZMod p) : Prop where
  hq : 1 < q
  hrq : r ^ q = 1
  hr_ord : ∀ b : ZMod q, r ^ b.val = 1 ↔ b = 0
  hpq : (p : ZMod q) = 1
  hr_ne : r ≠ 1
  h10 : (1 : ZMod p) ≠ 0
  hinv : ∀ x : ZMod p, x ≠ 0 → ∃ y : ZMod p, y * x = 1

def Frob.g10 {p q : ℕ} {r : ZMod p} : Frob p q r := ⟨1, 0⟩
def Frob.g01 {p q : ℕ} {r : ZMod p} : Frob p q r := ⟨0, 1⟩

section FrobTheory

variable {p q : ℕ} {r : ZMod p} [NeZero q] [hs : FrobSpec p q r]

omit [NeZero q] in
private lemma r_pow_mod (k : ℕ) : r ^ (k % q) = r ^ k := by
  have hdiv : q * (k / q) + k % q = k := Nat.div_add_mod k q
  conv_rhs => rw [← hdiv, pow_add, pow_mul, hs.hrq, one_pow, one_mul]

private lemma r_pow_add (b₁ b₂ : ZMod q) :
    r ^ (b₁ + b₂).val = r ^ b₁.val * r ^ b₂.val := by
  rw [ZMod.val_add, r_pow_mod (p := p) (q := q) (r := r), pow_add]

private lemma r_pow_neg_mul (b : ZMod q) :
    r ^ (-b).val * r ^ b.val = 1 := by
  rw [← r_pow_add (p := p) (q := q) (r := r), neg_add_cancel, ZMod.val_zero, pow_zero]

private lemma r_pow_mul_neg (b : ZMod q) :
    r ^ b.val * r ^ (-b).val = 1 := by
  rw [mul_comm]; exact r_pow_neg_mul (p := p) (q := q) (r := r) b

instance instGroupFrob : Group (Frob p q r) where
  mul x y := ⟨x.a + r ^ x.b.val * y.a, x.b + y.b⟩
  one := ⟨0, 0⟩
  inv x := ⟨-(r ^ (-x.b).val * x.a), -x.b⟩
  mul_assoc x y z := by
    apply Frob.ext
    · change (x.a + r ^ x.b.val * y.a) + r ^ (x.b + y.b).val * z.a =
        x.a + r ^ x.b.val * (y.a + r ^ y.b.val * z.a)
      rw [r_pow_add (p := p) (q := q) (r := r) x.b y.b]
      ring
    · change (x.b + y.b) + z.b = x.b + (y.b + z.b)
      ring
  one_mul x := by
    apply Frob.ext
    · change 0 + r ^ (0 : ZMod q).val * x.a = x.a
      rw [ZMod.val_zero, pow_zero]; ring
    · change 0 + x.b = x.b; ring
  mul_one x := by
    apply Frob.ext
    · change x.a + r ^ x.b.val * 0 = x.a; ring
    · change x.b + 0 = x.b; ring
  inv_mul_cancel x := by
    apply Frob.ext
    · change -(r ^ (-x.b).val * x.a) + r ^ (-x.b).val * x.a = 0; ring
    · change -x.b + x.b = 0; ring

lemma Frob.mul_a (x y : Frob p q r) : (x * y).a = x.a + r ^ x.b.val * y.a := rfl
lemma Frob.mul_b (x y : Frob p q r) : (x * y).b = x.b + y.b := rfl
lemma Frob.one_a : (1 : Frob p q r).a = 0 := rfl
lemma Frob.one_b : (1 : Frob p q r).b = 0 := rfl
lemma Frob.inv_a (x : Frob p q r) : (x⁻¹).a = -(r ^ (-x.b).val * x.a) := rfl
lemma Frob.inv_b (x : Frob p q r) : (x⁻¹).b = -x.b := rfl

lemma Frob.pow_b (x : Frob p q r) (n : ℕ) : (x ^ n).b = (n : ZMod q) * x.b := by
  induction n with
  | zero => simp [Frob.one_b]
  | succ n ih =>
    rw [pow_succ, Frob.mul_b, ih, Nat.cast_succ]
    ring

lemma Frob.pow_of_b_eq_zero {x : Frob p q r} (hb : x.b = 0) (n : ℕ) :
    x ^ n = ⟨(n : ZMod p) * x.a, 0⟩ := by
  induction n with
  | zero =>
    apply Frob.ext <;> simp [Frob.one_a, Frob.one_b]
  | succ n ih =>
    rw [pow_succ, ih]
    apply Frob.ext
    · rw [Frob.mul_a]
      rw [ZMod.val_zero, pow_zero, Nat.cast_succ]; ring
    · rw [Frob.mul_b]; rw [hb, zero_add]

lemma Frob.pow_qp_eq_one (x : Frob p q r) : x ^ (q * p) = 1 := by
  rw [pow_mul]
  have hb : (x ^ q).b = 0 := by
    rw [Frob.pow_b, ZMod.natCast_self, zero_mul]
  rw [Frob.pow_of_b_eq_zero hb p]
  apply Frob.ext
  · rw [ZMod.natCast_self, zero_mul, Frob.one_a]
  · rw [Frob.one_b]

lemma Frob.g10_ne_one : (Frob.g10 : Frob p q r) ≠ 1 := by
  intro h
  have h1 : (1 : ZMod p) = 0 := congrArg Frob.a h
  exact hs.h10 h1

lemma Frob.commutator_b (u v : Frob p q r) : (u * v * u⁻¹ * v⁻¹).b = 0 := by
  simp only [Frob.mul_b, Frob.inv_b]
  ring

lemma Frob.commutator_gens :
    (Frob.g01 : Frob p q r) * Frob.g10 * Frob.g01⁻¹ * Frob.g10⁻¹ = ⟨r - 1, 0⟩ := by
  have hv1 : (1 : ZMod q).val = 1 := ZMod.val_one'' (ne_of_gt hs.hq)
  apply Frob.ext
  · simp only [Frob.mul_a, Frob.mul_b, Frob.inv_a, Frob.inv_b, Frob.g01, Frob.g10,
      zero_add, add_zero, hv1, pow_one, add_neg_cancel, ZMod.val_zero, pow_zero]
    rw [neg_zero, ZMod.val_zero, pow_zero]
    ring
  · simp only [Frob.mul_b, Frob.inv_b, Frob.g01, Frob.g10]; ring

lemma Frob.commutator_gens_ne_one :
    (Frob.g01 : Frob p q r) * Frob.g10 * Frob.g01⁻¹ * Frob.g10⁻¹ ≠ 1 := by
  rw [Frob.commutator_gens]
  intro h
  have h1 : r - 1 = 0 := congrArg Frob.a h
  exact hs.hr_ne (sub_eq_zero.mp h1)

lemma Frob.comm_g10_iff (w : Frob p q r) :
    w * Frob.g10 = Frob.g10 * w ↔ w.b = 0 := by
  constructor
  · intro h
    have ha := congrArg Frob.a h
    simp only [Frob.mul_a, Frob.g10, ZMod.val_zero, pow_zero, mul_one, one_mul] at ha
    have hpow : r ^ w.b.val = 1 := by
      have : w.a + r ^ w.b.val = w.a + 1 := by rw [ha]; ring
      exact add_left_cancel this
    exact (hs.hr_ord w.b).mp hpow
  · intro hb
    apply Frob.ext
    · simp only [Frob.mul_a, Frob.g10, hb, ZMod.val_zero, pow_zero, mul_one, one_mul]; ring
    · simp only [Frob.mul_b, Frob.g10]; ring

lemma Frob.center_eq_one (w : Frob p q r) (hw : ∀ x, w * x = x * w) : w = 1 := by
  have hb : w.b = 0 := (Frob.comm_g10_iff w).mp (hw Frob.g10)
  have h01 := congrArg Frob.a (hw Frob.g01)
  have hv1 : (1 : ZMod q).val = 1 := ZMod.val_one'' (ne_of_gt hs.hq)
  simp only [Frob.mul_a, Frob.g01, hb, ZMod.val_zero, pow_zero, mul_zero, add_zero, zero_add] at h01
  rw [hv1, pow_one] at h01
  have hmul : (r - 1) * w.a = 0 := by
    have : r * w.a - w.a = 0 := sub_eq_zero.mpr h01.symm
    linear_combination this
  have hrsub : r - 1 ≠ 0 := sub_ne_zero.mpr hs.hr_ne
  obtain ⟨y, hy⟩ := hs.hinv (r - 1) hrsub
  have ha : w.a = 0 := by
    calc
      w.a = 1 * w.a := (one_mul _).symm
      _ = (y * (r - 1)) * w.a := by rw [hy]
      _ = y * ((r - 1) * w.a) := mul_assoc _ _ _
      _ = 0 := by rw [hmul, mul_zero]
  exact Frob.ext ha hb

lemma Frob.g10_mem_of_b_zero_ne_one [NeZero p] {N : Subgroup (Frob p q r)} {c : Frob p q r}
    (hcN : c ∈ N) (hcb : c.b = 0) (hcne : c ≠ 1) : Frob.g10 ∈ N := by
  have hca : c.a ≠ 0 := by
    intro h0; exact hcne (Frob.ext h0 hcb)
  obtain ⟨y, hy⟩ := hs.hinv c.a hca
  let k : ℕ := y.val
  have hk : c ^ k = Frob.g10 := by
    rw [Frob.pow_of_b_eq_zero hcb k]
    apply Frob.ext
    · dsimp only [Frob.g10, k]
      rw [ZMod.natCast_zmod_val, hy]
    · rfl
  rw [← hk]
  exact N.pow_mem hcN k

private lemma list_prod_comm_left {M : Type*} [Monoid M] {x : M} {ys : List M}
    (h : ∀ y ∈ ys, x * y = y * x) : x * ys.prod = ys.prod * x := by
  induction ys with
  | nil => simp
  | cons y ys ih =>
    rw [List.prod_cons, ← mul_assoc, h y (by simp), mul_assoc,
      ih (fun z hz => h z (by simp [hz])), mul_assoc]

private lemma list_map_prod_mul {ι M : Type*} [Monoid M]
    (L : List ι) (hL : L.Nodup) (a b : ι → M)
    (hcomm : ∀ s ∈ L, ∀ t ∈ L, s ≠ t → a s * b t = b t * a s) :
    (L.map a).prod * (L.map b).prod = (L.map (fun s => a s * b s)).prod := by
  induction L with
  | nil => simp
  | cons s L ih =>
    rw [List.nodup_cons] at hL
    simp only [List.map_cons, List.prod_cons]
    have h1 : b s * (L.map a).prod = (L.map a).prod * b s := by
      apply list_prod_comm_left
      intro y hy
      rw [List.mem_map] at hy
      obtain ⟨t, htL, rfl⟩ := hy
      have hts : t ≠ s := fun h => hL.1 (h ▸ htL)
      exact (hcomm t (by simp [htL]) s (by simp) hts).symm
    calc
      a s * (L.map a).prod * (b s * (L.map b).prod)
          = a s * ((L.map a).prod * b s) * (L.map b).prod := by simp only [mul_assoc]
      _ = a s * (b s * (L.map a).prod) * (L.map b).prod := by rw [← h1]
      _ = a s * b s * ((L.map a).prod * (L.map b).prod) := by simp only [mul_assoc]
      _ = a s * b s * (L.map (fun t => a t * b t)).prod := by
          rw [ih hL.2 (fun u hu v hv hne => hcomm u (by simp [hu]) v (by simp [hv]) hne)]

private lemma list_map_prod_inv {ι G' : Type*} [Group G']
    (L : List ι) (hL : L.Nodup) (a : ι → G')
    (hcomm : ∀ s ∈ L, ∀ t ∈ L, s ≠ t → a s * a t = a t * a s) :
    ((L.map a).prod)⁻¹ = (L.map (fun s => (a s)⁻¹)).prod := by
  apply inv_eq_of_mul_eq_one_right
  rw [list_map_prod_mul L hL a (fun s => (a s)⁻¹)]
  · induction L with
    | nil => simp
    | cons s L _ => simp
  · intro s hs t ht hne
    have h := hcomm s hs t ht hne
    calc
      a s * (a t)⁻¹ = (a t)⁻¹ * (a t * a s) * (a t)⁻¹ := by group
      _ = (a t)⁻¹ * (a s * a t) * (a t)⁻¹ := by rw [h]
      _ = (a t)⁻¹ * a s := by group

private lemma list_map_prod_eq_single {ι M : Type*} [Monoid M]
    (L : List ι) (hL : L.Nodup) (s₀ : ι) (hs₀ : s₀ ∈ L) (a : ι → M)
    (h1 : ∀ s ∈ L, s ≠ s₀ → a s = 1) :
    (L.map a).prod = a s₀ := by
  induction L with
  | nil => cases hs₀
  | cons s L ih =>
    rw [List.nodup_cons] at hL
    simp only [List.map_cons, List.prod_cons]
    by_cases hss : s = s₀
    · subst hss
      have hrest : (L.map a).prod = 1 := by
        apply List.prod_eq_one
        intro y hy
        rw [List.mem_map] at hy
        obtain ⟨t, htL, rfl⟩ := hy
        exact h1 t (by simp [htL]) (fun h => hL.1 (h ▸ htL))
      rw [hrest, mul_one]
    · rw [h1 s (by simp) hss, one_mul]
      have hs₀' : s₀ ∈ L := (List.mem_cons.mp hs₀).resolve_left (Ne.symm hss)
      exact ih hL.2 hs₀' (fun t ht hne => h1 t (by simp [ht]) hne)

lemma Frob.commuting_gen_unique [NeZero p] {ι : Type*} [DecidableEq ι]
    (L : List ι) (hL : L.Nodup) (N : ι → Subgroup (Frob p q r))
    (hcomm : ∀ s ∈ L, ∀ t ∈ L, s ≠ t → ∀ x ∈ N s, ∀ y ∈ N t, x * y = y * x)
    (hgen : ∀ z : Frob p q r, ∃ d : ι → Frob p q r, (∀ s ∈ L, d s ∈ N s) ∧ (L.map d).prod = z) :
    ∃ s₀ ∈ L, N s₀ = ⊤ ∧ ∀ s ∈ L, s ≠ s₀ → N s = ⊥ := by
  obtain ⟨a, haN, hap⟩ := hgen Frob.g01
  obtain ⟨b, hbN, hbp⟩ := hgen Frob.g10
  have hcomm_prod :
      Frob.g01 * Frob.g10 * (Frob.g01 : Frob p q r)⁻¹ * Frob.g10⁻¹ =
      (L.map (fun s => a s * b s * (a s)⁻¹ * (b s)⁻¹)).prod := by
    rw [← hap, ← hbp]
    rw [list_map_prod_mul L hL a b (fun s hs t ht hne => hcomm s hs t ht hne _ (haN s hs) _ (hbN t ht))]
    rw [list_map_prod_inv L hL a (fun s hs t ht hne => hcomm s hs t ht hne _ (haN s hs) _ (haN t ht))]
    rw [list_map_prod_inv L hL b (fun s hs t ht hne => hcomm s hs t ht hne _ (hbN s hs) _ (hbN t ht))]
    rw [list_map_prod_mul L hL (fun s => a s * b s) (fun s => (a s)⁻¹)
      (fun s hs t ht hne => hcomm s hs t ht hne _ ((N s).mul_mem (haN s hs) (hbN s hs)) _ ((N t).inv_mem (haN t ht)))]
    rw [list_map_prod_mul L hL (fun s => a s * b s * (a s)⁻¹) (fun s => (b s)⁻¹)
      (fun s hs t ht hne => hcomm s hs t ht hne _
        ((N s).mul_mem ((N s).mul_mem (haN s hs) (hbN s hs)) ((N s).inv_mem (haN s hs)))
        _ ((N t).inv_mem (hbN t ht)))]
  have hex : ∃ s₀ ∈ L, a s₀ * b s₀ * (a s₀)⁻¹ * (b s₀)⁻¹ ≠ 1 := by
    by_contra hall
    push Not at hall
    have h1 : (L.map (fun s => a s * b s * (a s)⁻¹ * (b s)⁻¹)).prod = 1 := by
      apply List.prod_eq_one
      intro y hy
      rw [List.mem_map] at hy
      obtain ⟨s, hsL, rfl⟩ := hy
      exact hall s hsL
    rw [h1] at hcomm_prod
    exact Frob.commutator_gens_ne_one hcomm_prod
  obtain ⟨s₀, hs₀L, hne₀⟩ := hex
  have hcN : a s₀ * b s₀ * (a s₀)⁻¹ * (b s₀)⁻¹ ∈ N s₀ :=
    (N s₀).mul_mem ((N s₀).mul_mem ((N s₀).mul_mem (haN s₀ hs₀L) (hbN s₀ hs₀L))
      ((N s₀).inv_mem (haN s₀ hs₀L))) ((N s₀).inv_mem (hbN s₀ hs₀L))
  have hg10_s₀ : Frob.g10 ∈ N s₀ :=
    Frob.g10_mem_of_b_zero_ne_one hcN (Frob.commutator_b (a s₀) (b s₀)) hne₀
  have hbot : ∀ s ∈ L, s ≠ s₀ → N s = ⊥ := by
    intro s hsL hss
    rw [Subgroup.eq_bot_iff_forall]
    intro w hwN
    have hwb : w.b = 0 :=
      (Frob.comm_g10_iff w).mp (hcomm s hsL s₀ hs₀L hss w hwN Frob.g10 hg10_s₀)
    by_contra hwne
    have hg10_s : Frob.g10 ∈ N s := Frob.g10_mem_of_b_zero_ne_one hwN hwb hwne
    have hab : (a s₀).b = 0 :=
      (Frob.comm_g10_iff (a s₀)).mp (hcomm s₀ hs₀L s hsL (Ne.symm hss) (a s₀) (haN s₀ hs₀L) Frob.g10 hg10_s)
    have hbb : (b s₀).b = 0 :=
      (Frob.comm_g10_iff (b s₀)).mp (hcomm s₀ hs₀L s hsL (Ne.symm hss) (b s₀) (hbN s₀ hs₀L) Frob.g10 hg10_s)
    have hcomm0 : a s₀ * b s₀ = b s₀ * a s₀ := by
      apply Frob.ext
      · simp only [Frob.mul_a, hab, hbb, ZMod.val_zero, pow_zero, one_mul]; ring
      · simp only [Frob.mul_b, hab, hbb]
    have htriv : a s₀ * b s₀ * (a s₀)⁻¹ * (b s₀)⁻¹ = 1 := by
      rw [hcomm0]; group
    exact hne₀ htriv
  refine ⟨s₀, hs₀L, ?_, hbot⟩
  rw [Subgroup.eq_top_iff']
  intro z
  obtain ⟨d, hdN, hdp⟩ := hgen z
  have hz : z = d s₀ := by
    rw [← hdp]
    apply list_map_prod_eq_single L hL s₀ hs₀L d
    intro s hsL hss
    have := hbot s hsL hss
    rw [Subgroup.eq_bot_iff_forall] at this
    exact this (d s) (hdN s hsL)
  rw [hz]
  exact hdN s₀ hs₀L

lemma Frob.aut_b [NeZero p] (α : Frob p q r ≃* Frob p q r) (w : Frob p q r) : (α w).b = w.b := by
  let u := α Frob.g10
  let v := α Frob.g01
  have hu_pow : u ^ p = 1 := by
    rw [← map_pow]
    have hg : (Frob.g10 : Frob p q r) ^ p = 1 := by
      rw [Frob.pow_of_b_eq_zero rfl p]
      apply Frob.ext
      · dsimp only [Frob.g10]; rw [ZMod.natCast_self, zero_mul, Frob.one_a]
      · rfl
    rw [hg, map_one]
  have hub : u.b = 0 := by
    have h0 := congrArg Frob.b hu_pow
    rw [Frob.pow_b, hs.hpq, one_mul, Frob.one_b] at h0
    exact h0
  have hua : u.a ≠ 0 := by
    intro h0
    have hu1 : u = 1 := Frob.ext h0 hub
    have h1 : (Frob.g10 : Frob p q r) = 1 := α.injective (hu1.trans (map_one α).symm)
    exact Frob.g10_ne_one h1
  have hv1 : (1 : ZMod q).val = 1 := ZMod.val_one'' (ne_of_gt hs.hq)
  have hconj : (Frob.g01 : Frob p q r) * Frob.g10 * Frob.g01⁻¹ = Frob.g10 ^ r.val := by
    rw [Frob.pow_of_b_eq_zero rfl r.val]
    apply Frob.ext
    · simp only [Frob.mul_a, Frob.mul_b, Frob.inv_a, Frob.g01, Frob.g10]
      rw [zero_add, hv1, pow_one, mul_one, ZMod.natCast_zmod_val, mul_one]
      ring
    · simp only [Frob.mul_b, Frob.inv_b, Frob.g01, Frob.g10]; ring
  have hconj_α : v * u * v⁻¹ = u ^ r.val := by
    calc
      v * u * v⁻¹ = α (Frob.g01 * Frob.g10 * Frob.g01⁻¹) := by simp [u, v]
      _ = α (Frob.g10 ^ r.val) := by rw [hconj]
      _ = u ^ r.val := map_pow α Frob.g10 r.val
  have hca := congrArg Frob.a hconj_α
  rw [Frob.pow_of_b_eq_zero hub r.val] at hca
  simp only [Frob.mul_a, Frob.mul_b, Frob.inv_a, hub, add_zero, ZMod.natCast_zmod_val] at hca
  have hlhs : v.a + r ^ v.b.val * u.a + r ^ v.b.val * -(r ^ (-v.b).val * v.a) = r ^ v.b.val * u.a := by
    have hmul : r ^ v.b.val * -(r ^ (-v.b).val * v.a) = -(r ^ v.b.val * r ^ (-v.b).val) * v.a := by ring
    rw [hmul, r_pow_mul_neg (p := p) (q := q) (r := r) v.b]; ring
  rw [hlhs] at hca
  obtain ⟨y, hy⟩ := hs.hinv u.a hua
  have hrpow : r ^ v.b.val = r := by
    have hmul := congrArg (fun t => y * t) hca
    calc
      r ^ v.b.val = r ^ v.b.val * 1 := (mul_one _).symm
      _ = r ^ v.b.val * (y * u.a) := by rw [hy]
      _ = y * (r ^ v.b.val * u.a) := by ring
      _ = y * (r * u.a) := hmul
      _ = r * (y * u.a) := by ring
      _ = r * 1 := by rw [hy]
      _ = r := mul_one _
  have hrsub : r ^ (v.b - 1).val = 1 := by
    rw [sub_eq_add_neg, r_pow_add (p := p) (q := q) (r := r) v.b (-1), hrpow]
    have : r = r ^ (1 : ZMod q).val := by rw [hv1, pow_one]
    nth_rw 1 [this]
    exact r_pow_mul_neg (p := p) (q := q) (r := r) 1
  have hvb : v.b = 1 := sub_eq_zero.mp ((hs.hr_ord (v.b - 1)).mp hrsub)
  have hw_decomp : w = (Frob.g10 : Frob p q r) ^ w.a.val * Frob.g01 ^ w.b.val := by
    have hg01_pow : ∀ k : ℕ, (Frob.g01 : Frob p q r) ^ k = ⟨0, (k : ZMod q)⟩ := by
      intro k
      induction k with
      | zero => apply Frob.ext <;> simp [Frob.one_a, Frob.one_b]
      | succ k ih =>
        rw [pow_succ, ih]
        apply Frob.ext
        · simp [Frob.mul_a, Frob.g01]
        · simp [Frob.mul_b, Frob.g01, Nat.cast_succ]
    rw [Frob.pow_of_b_eq_zero rfl w.a.val, hg01_pow w.b.val]
    apply Frob.ext
    · simp [Frob.mul_a, Frob.g10]
    · simp [Frob.mul_b]
  conv_lhs => rw [hw_decomp]
  rw [map_mul, map_pow, map_pow, Frob.mul_b, Frob.pow_b, Frob.pow_b]
  change (w.a.val : ZMod q) * u.b + (w.b.val : ZMod q) * v.b = w.b
  rw [hub, hvb, mul_zero, zero_add, mul_one, ZMod.natCast_zmod_val]

end FrobTheory

/-! Section 2: Concrete Frobenius groups F42 and F110 -/

abbrev F42 := Frob 7 6 (3 : ZMod 7)
abbrev F110 := Frob 11 10 (2 : ZMod 11)

instance : FrobSpec 7 6 (3 : ZMod 7) where
  hq := by decide
  hrq := by decide
  hr_ord := by decide
  hpq := by decide
  hr_ne := by decide
  h10 := by decide
  hinv := by decide

instance : FrobSpec 11 10 (2 : ZMod 11) where
  hq := by decide
  hrq := by decide
  hr_ord := by decide
  hpq := by decide
  hr_ne := by decide
  h10 := by decide
  hinv := by decide

def equivF42 : (ZMod 7 × ZMod 6) ≃ F42 where
  toFun p := ⟨p.1, p.2⟩
  invFun x := (x.a, x.b)
  left_inv _ := rfl
  right_inv _ := rfl

def equivF110 : (ZMod 11 × ZMod 10) ≃ F110 where
  toFun p := ⟨p.1, p.2⟩
  invFun x := (x.a, x.b)
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype F42 := Fintype.ofEquiv (ZMod 7 × ZMod 6) equivF42
instance : Fintype F110 := Fintype.ofEquiv (ZMod 11 × ZMod 10) equivF110

lemma card_F42 : Fintype.card F42 = 42 := by
  rw [← Fintype.card_congr equivF42]
  simp [Fintype.card_prod, ZMod.card]

lemma card_F110 : Fintype.card F110 = 110 := by
  rw [← Fintype.card_congr equivF110]
  simp [Fintype.card_prod, ZMod.card]

lemma not_equiv_F42_F110 (e : F42 ≃ F110) : False := by
  have h := Fintype.card_congr e
  rw [card_F42, card_F110] at h
  omega

lemma F42_pow_2310 (x : F42) : x ^ 2310 = 1 := by
  have h : (2310 : ℕ) = (6 * 7) * 55 := by norm_num
  rw [h, pow_mul, Frob.pow_qp_eq_one, one_pow]

lemma F110_pow_2310 (x : F110) : x ^ 2310 = 1 := by
  have h : (2310 : ℕ) = (10 * 11) * 21 := by norm_num
  rw [h, pow_mul, Frob.pow_qp_eq_one, one_pow]

/-! Section 3: Fiber-product group G and parity-diagonal subgroup H -/

structure G where
  z : ℤ
  u : F42
  v : F110
  h3 : z % 3 = (u.b.val : ℤ) % 3
  h5 : z % 5 = (v.b.val : ℤ) % 5

lemma G.ext {x y : G} (hz : x.z = y.z) (hu : x.u = y.u) (hv : x.v = y.v) : x = y := by
  cases x; cases y; simp_all

private lemma zmod6_add_mod3 (a b : ZMod 6) :
    ((a + b).val : ℤ) % 3 = ((a.val : ℤ) + (b.val : ℤ)) % 3 := by
  rw [ZMod.val_add]; push_cast; omega

private lemma zmod10_add_mod5 (a b : ZMod 10) :
    ((a + b).val : ℤ) % 5 = ((a.val : ℤ) + (b.val : ℤ)) % 5 := by
  rw [ZMod.val_add]; push_cast; omega

private lemma zmod6_neg_mod3 (a : ZMod 6) :
    ((-a).val : ℤ) % 3 = (-(a.val : ℤ)) % 3 := by
  have h := ZMod.val_add (-a) a
  rw [neg_add_cancel, ZMod.val_zero] at h
  have hlt1 := a.val_lt
  have hlt2 := (-a).val_lt
  omega

private lemma zmod10_neg_mod5 (a : ZMod 10) :
    ((-a).val : ℤ) % 5 = (-(a.val : ℤ)) % 5 := by
  have h := ZMod.val_add (-a) a
  rw [neg_add_cancel, ZMod.val_zero] at h
  have hlt1 := a.val_lt
  have hlt2 := (-a).val_lt
  omega

private lemma zmod6_add_mod2 (a b : ZMod 6) :
    (a + b).val % 2 = (a.val + b.val) % 2 := by
  rw [ZMod.val_add]; omega

private lemma zmod10_add_mod2 (a b : ZMod 10) :
    (a + b).val % 2 = (a.val + b.val) % 2 := by
  rw [ZMod.val_add]; omega

private lemma zmod6_neg_mod2 (a : ZMod 6) :
    (-a).val % 2 = a.val % 2 := by
  have h := ZMod.val_add (-a) a
  rw [neg_add_cancel, ZMod.val_zero] at h
  have hlt1 := a.val_lt
  have hlt2 := (-a).val_lt
  omega

private lemma zmod10_neg_mod2 (a : ZMod 10) :
    (-a).val % 2 = a.val % 2 := by
  have h := ZMod.val_add (-a) a
  rw [neg_add_cancel, ZMod.val_zero] at h
  have hlt1 := a.val_lt
  have hlt2 := (-a).val_lt
  omega

instance instGroupG : Group G where
  mul x y :=
    { z := x.z + y.z
      u := x.u * y.u
      v := x.v * y.v
      h3 := by
        rw [Frob.mul_b, zmod6_add_mod3]
        have hx := x.h3; have hy := y.h3; omega
      h5 := by
        rw [Frob.mul_b, zmod10_add_mod5]
        have hx := x.h5; have hy := y.h5; omega }
  one := ⟨0, 1, 1, rfl, rfl⟩
  inv x :=
    { z := -x.z
      u := x.u⁻¹
      v := x.v⁻¹
      h3 := by
        rw [Frob.inv_b, zmod6_neg_mod3]
        have hx := x.h3; omega
      h5 := by
        rw [Frob.inv_b, zmod10_neg_mod5]
        have hx := x.h5; omega }
  mul_assoc x y z := G.ext (add_assoc _ _ _) (mul_assoc _ _ _) (mul_assoc _ _ _)
  one_mul x := G.ext (zero_add _) (one_mul _) (one_mul _)
  mul_one x := G.ext (add_zero _) (mul_one _) (mul_one _)
  inv_mul_cancel x := G.ext (neg_add_cancel _) (inv_mul_cancel _) (inv_mul_cancel _)

lemma G.mul_z (x y : G) : (x * y).z = x.z + y.z := rfl
lemma G.mul_u (x y : G) : (x * y).u = x.u * y.u := rfl
lemma G.mul_v (x y : G) : (x * y).v = x.v * y.v := rfl
lemma G.one_z : (1 : G).z = 0 := rfl
lemma G.one_u : (1 : G).u = 1 := rfl
lemma G.one_v : (1 : G).v = 1 := rfl
lemma G.inv_z (x : G) : (x⁻¹).z = -x.z := rfl
lemma G.inv_u (x : G) : (x⁻¹).u = x.u⁻¹ := rfl
lemma G.inv_v (x : G) : (x⁻¹).v = x.v⁻¹ := rfl

lemma G.npow_z (x : G) (n : ℕ) : (x ^ n).z = (n : ℤ) * x.z := by
  induction n with
  | zero => simp [G.one_z]
  | succ n ih => rw [pow_succ, G.mul_z, ih, Nat.cast_succ]; ring

lemma G.npow_u (x : G) (n : ℕ) : (x ^ n).u = x.u ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, pow_succ, G.mul_u, ih]

lemma G.npow_v (x : G) (n : ℕ) : (x ^ n).v = x.v ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, pow_succ, G.mul_v, ih]

lemma G.zpow_z (x : G) (k : ℤ) : (x ^ k).z = k * x.z := by
  cases k with
  | ofNat n =>
    simp only [Int.ofNat_eq_natCast, zpow_natCast, G.npow_z]
  | negSucc n =>
    rw [zpow_negSucc, G.inv_z, G.npow_z, Int.negSucc_eq]
    push_cast
    ring

lemma G.zpow_u (x : G) (k : ℤ) : (x ^ k).u = x.u ^ k := by
  cases k with
  | ofNat n => simp [G.npow_u]
  | negSucc n => simp [G.inv_u, G.npow_u]

lemma G.zpow_v (x : G) (k : ℤ) : (x ^ k).v = x.v ^ k := by
  cases k with
  | ofNat n => simp [G.npow_v]
  | negSucc n => simp [G.inv_v, G.npow_v]

def H : Subgroup G where
  carrier := { g | g.u.b.val % 2 = g.v.b.val % 2 }
  mul_mem' {x y} hx hy := by
    change (x.u * y.u).b.val % 2 = (x.v * y.v).b.val % 2
    rw [Frob.mul_b, Frob.mul_b, zmod6_add_mod2, zmod10_add_mod2]
    change x.u.b.val % 2 = x.v.b.val % 2 at hx
    change y.u.b.val % 2 = y.v.b.val % 2 at hy
    omega
  one_mem' := rfl
  inv_mem' {x} hx := by
    change (x.u⁻¹).b.val % 2 = (x.v⁻¹).b.val % 2
    rw [Frob.inv_b, Frob.inv_b, zmod6_neg_mod2, zmod10_neg_mod2]
    exact hx

/-! Section 4: Center, quotient projection, and Aut(P_n) structure -/

abbrev Gn (n : ℕ) := Fin n → G
abbrev Pn (n : ℕ) := (Fin n → F42) × (Fin n → F110)

def qMap (n : ℕ) : Gn n →* Pn n where
  toFun g := (fun i => (g i).u, fun i => (g i).v)
  map_one' := rfl
  map_mul' _ _ := rfl

def qLift (n : ℕ) (x : Pn n) : Gn n :=
  fun i =>
    { z := 10 * ((x.1 i).b.val : ℤ) + 6 * ((x.2 i).b.val : ℤ)
      u := x.1 i
      v := x.2 i
      h3 := by omega
      h5 := by omega }

lemma qMap_qLift (n : ℕ) (x : Pn n) : qMap n (qLift n x) = x := rfl

lemma ker_qMap_iff_comm (n : ℕ) (g : Gn n) :
    qMap n g = 1 ↔ ∀ h : Gn n, g * h = h * g := by
  constructor
  · intro hq h
    ext i
    have hu : (g i).u = 1 := congrFun (congrArg Prod.fst hq) i
    have hv : (g i).v = 1 := congrFun (congrArg Prod.snd hq) i
    apply G.ext
    · simp only [Pi.mul_apply, G.mul_z]; ring
    · simp only [Pi.mul_apply, G.mul_u, hu, one_mul, mul_one]
    · simp only [Pi.mul_apply, G.mul_v, hv, one_mul, mul_one]
  · intro hcomm
    apply Prod.ext
    · ext i
      apply Frob.center_eq_one
      intro x
      let p : Pn n := (fun j => if j = i then x else 1, fun _ => 1)
      have hc := congrArg (fun k => (qMap n k).1 i) (hcomm (qLift n p))
      simpa [qMap, qLift, p, G.mul_u] using hc
    · ext i
      apply Frob.center_eq_one
      intro x
      let p : Pn n := (fun _ => 1, fun j => if j = i then x else 1)
      have hc := congrArg (fun k => (qMap n k).2 i) (hcomm (qLift n p))
      simpa [qMap, qLift, p, G.mul_v] using hc

lemma qMap_f_eq_of_qMap_eq {n : ℕ} (f : Gn n ≃* Gn n) {g₁ g₂ : Gn n}
    (h : qMap n g₁ = qMap n g₂) : qMap n (f g₁) = qMap n (f g₂) := by
  have hker : qMap n (g₁ * g₂⁻¹) = 1 := by
    rw [map_mul, map_inv, h, mul_inv_cancel]
  have hcomm : ∀ y : Gn n, (g₁ * g₂⁻¹) * y = y * (g₁ * g₂⁻¹) :=
    (ker_qMap_iff_comm n _).mp hker
  have hfcomm : ∀ y : Gn n, f (g₁ * g₂⁻¹) * y = y * f (g₁ * g₂⁻¹) := by
    intro y
    have := congrArg f (hcomm (f.symm y))
    simpa only [map_mul, MulEquiv.apply_symm_apply] using this
  have hfker : qMap n (f (g₁ * g₂⁻¹)) = 1 := (ker_qMap_iff_comm n _).mpr hfcomm
  rw [map_mul, map_inv, map_mul, map_inv] at hfker
  exact mul_inv_eq_one.mp hfker

def inducedAut {n : ℕ} (f : Gn n ≃* Gn n) : Pn n ≃* Pn n where
  toFun x := qMap n (f (qLift n x))
  invFun x := qMap n (f.symm (qLift n x))
  left_inv x := by
    dsimp only
    have h1 : qMap n (f.symm (qLift n (qMap n (f (qLift n x))))) =
        qMap n (f.symm (f (qLift n x))) :=
      qMap_f_eq_of_qMap_eq f.symm (qMap_qLift n _)
    rw [h1, MulEquiv.symm_apply_apply, qMap_qLift]
  right_inv x := by
    dsimp only
    have h1 : qMap n (f (qLift n (qMap n (f.symm (qLift n x))))) =
        qMap n (f (f.symm (qLift n x))) :=
      qMap_f_eq_of_qMap_eq f (qMap_qLift n _)
    rw [h1, MulEquiv.apply_symm_apply, qMap_qLift]
  map_mul' x y := by
    have hq : qMap n (qLift n (x * y)) = qMap n (qLift n x * qLift n y) := by
      rw [map_mul, qMap_qLift, qMap_qLift, qMap_qLift]
    rw [qMap_f_eq_of_qMap_eq f hq, map_mul, map_mul]

lemma inducedAut_qMap {n : ℕ} (f : Gn n ≃* Gn n) (g : Gn n) :
    inducedAut f (qMap n g) = qMap n (f g) :=
  qMap_f_eq_of_qMap_eq f (qMap_qLift n (qMap n g))

private def inclL (n : ℕ) (j : Fin n) : F42 →* Pn n where
  toFun a := (fun k => if k = j then a else 1, fun _ => 1)
  map_one' := by
    apply Prod.ext <;> ext k <;> simp
  map_mul' a b := by
    apply Prod.ext
    · ext k; by_cases h : k = j <;> simp [h]
    · ext k; simp

private def inclR (n : ℕ) (j : Fin n) : F110 →* Pn n where
  toFun a := (fun _ => 1, fun k => if k = j then a else 1)
  map_one' := by
    apply Prod.ext <;> ext k <;> simp
  map_mul' a b := by
    apply Prod.ext
    · ext k; simp
    · ext k; by_cases h : k = j <;> simp [h]

private def projL (n : ℕ) (i : Fin n) : Pn n →* F42 where
  toFun x := x.1 i
  map_one' := rfl
  map_mul' _ _ := rfl

private def projR (n : ℕ) (i : Fin n) : Pn n →* F110 where
  toFun x := x.2 i
  map_one' := rfl
  map_mul' _ _ := rfl

private def compSub (n : ℕ) : Fin n ⊕ Fin n → Subgroup (Pn n)
  | Sum.inl j => (inclL n j).range
  | Sum.inr j => (inclR n j).range

private def piece (n : ℕ) (x : Pn n) : Fin n ⊕ Fin n → Pn n
  | Sum.inl j => inclL n j (x.1 j)
  | Sum.inr j => inclR n j (x.2 j)

private def idxList (n : ℕ) : List (Fin n ⊕ Fin n) :=
  (List.finRange n).map Sum.inl ++ (List.finRange n).map Sum.inr

private lemma idxList_nodup (n : ℕ) : (idxList n).Nodup := by
  unfold idxList
  rw [List.nodup_append]
  refine ⟨(List.nodup_finRange n).map Sum.inl_injective,
    (List.nodup_finRange n).map Sum.inr_injective, ?_⟩
  intro a ha b hb
  rw [List.mem_map] at ha hb
  obtain ⟨_, _, rfl⟩ := ha
  obtain ⟨_, _, rfl⟩ := hb
  simp

private lemma mem_idxList (n : ℕ) (s : Fin n ⊕ Fin n) : s ∈ idxList n := by
  unfold idxList
  cases s with
  | inl j => exact List.mem_append_left _ (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩)
  | inr j => exact List.mem_append_right _ (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩)

private lemma piece_mem_compSub (n : ℕ) (x : Pn n) (s : Fin n ⊕ Fin n) :
    piece n x s ∈ compSub n s := by
  cases s with
  | inl j => exact ⟨x.1 j, rfl⟩
  | inr j => exact ⟨x.2 j, rfl⟩

private lemma compSub_comm (n : ℕ) {s t : Fin n ⊕ Fin n} (hst : s ≠ t)
    {x y : Pn n} (hx : x ∈ compSub n s) (hy : y ∈ compSub n t) :
    x * y = y * x := by
  cases s with
  | inl j =>
    obtain ⟨a, rfl⟩ := hx
    cases t with
    | inl k =>
      obtain ⟨b, rfl⟩ := hy
      have hjk : j ≠ k := fun h => hst (congrArg Sum.inl h)
      apply Prod.ext
      · ext r
        by_cases hrj : r = j
        · subst hrj; simp [inclL, hjk]
        · by_cases hrk : r = k
          · subst hrk; simp [inclL, hjk.symm]
          · simp [inclL, hrj, hrk]
      · ext r; simp [inclL]
    | inr k =>
      obtain ⟨b, rfl⟩ := hy
      apply Prod.ext <;> ext r <;> simp [inclL, inclR]
  | inr j =>
    obtain ⟨a, rfl⟩ := hx
    cases t with
    | inl k =>
      obtain ⟨b, rfl⟩ := hy
      apply Prod.ext <;> ext r <;> simp [inclL, inclR]
    | inr k =>
      obtain ⟨b, rfl⟩ := hy
      have hjk : j ≠ k := fun h => hst (congrArg Sum.inr h)
      apply Prod.ext
      · ext r; simp [inclR]
      · ext r
        by_cases hrj : r = j
        · subst hrj; simp [inclR, hjk]
        · by_cases hrk : r = k
          · subst hrk; simp [inclR, hjk.symm]
          · simp [inclR, hrj, hrk]

private lemma list_map_monoidHom_prod {α M N : Type*} [Monoid M] [Monoid N]
    (φ : M →* N) (L : List α) (f : α → M) :
    φ (L.map f).prod = (L.map (fun s => φ (f s))).prod := by
  induction L with
  | nil => simp
  | cons s L ih => simp [ih]

private lemma prod_piece_eq (n : ℕ) (x : Pn n) :
    ((idxList n).map (piece n x)).prod = x := by
  apply Prod.ext
  · ext i
    change projL n i ((idxList n).map (piece n x)).prod = x.1 i
    rw [list_map_monoidHom_prod]
    rw [list_map_prod_eq_single (idxList n) (idxList_nodup n) (Sum.inl i) (mem_idxList n _)]
    · simp [projL, piece, inclL]
    · intro s _ hne
      cases s with
      | inl j =>
        have hji : i ≠ j := fun h => hne (congrArg Sum.inl h.symm)
        simp [projL, piece, inclL, hji]
      | inr j => simp [projL, piece, inclR]
  · ext i
    change projR n i ((idxList n).map (piece n x)).prod = x.2 i
    rw [list_map_monoidHom_prod]
    rw [list_map_prod_eq_single (idxList n) (idxList_nodup n) (Sum.inr i) (mem_idxList n _)]
    · simp [projR, piece, inclR]
    · intro s _ hne
      cases s with
      | inl j => simp [projR, piece, inclL]
      | inr j =>
        have hji : i ≠ j := fun h => hne (congrArg Sum.inr h.symm)
        simp [projR, piece, inclR, hji]

lemma aut_Pn_b {n : ℕ} (fbar : Pn n ≃* Pn n) :
    ∃ σ τ : Equiv.Perm (Fin n),
      ∀ (x : Pn n) (i : Fin n),
        ((fbar x).1 i).b = (x.1 (σ i)).b ∧ ((fbar x).2 i).b = (x.2 (τ i)).b := by
  have hL_ex : ∀ i : Fin n, ∃ s₀ : Fin n ⊕ Fin n,
      (compSub n s₀).map ((projL n i).comp fbar.toMonoidHom) = ⊤ ∧
      ∀ s : Fin n ⊕ Fin n, s ≠ s₀ →
        (compSub n s).map ((projL n i).comp fbar.toMonoidHom) = ⊥ := by
    intro i
    let φ : Pn n →* F42 := (projL n i).comp fbar.toMonoidHom
    have huniq := Frob.commuting_gen_unique (p := 7) (q := 6) (r := (3 : ZMod 7))
      (idxList n) (idxList_nodup n) (fun s => (compSub n s).map φ)
      (by
        intro s _ t _ hst x hx y hy
        obtain ⟨x', hx', rfl⟩ := hx
        obtain ⟨y', hy', rfl⟩ := hy
        rw [← map_mul, compSub_comm n hst hx' hy', map_mul])
      (by
        intro z
        let y : Pn n := fbar.symm (inclL n i z)
        refine ⟨fun s => φ (piece n y s),
          fun s _ => Subgroup.mem_map_of_mem φ (piece_mem_compSub n y s), ?_⟩
        rw [← list_map_monoidHom_prod, prod_piece_eq n y]
        change (fbar (fbar.symm (inclL n i z))).1 i = z
        rw [MulEquiv.apply_symm_apply]
        simp [inclL])
    obtain ⟨s₀, _, htop, hbot⟩ := huniq
    exact ⟨s₀, htop, fun s hne => hbot s (mem_idxList n s) hne⟩
  have hR_ex : ∀ i : Fin n, ∃ s₀ : Fin n ⊕ Fin n,
      (compSub n s₀).map ((projR n i).comp fbar.toMonoidHom) = ⊤ ∧
      ∀ s : Fin n ⊕ Fin n, s ≠ s₀ →
        (compSub n s).map ((projR n i).comp fbar.toMonoidHom) = ⊥ := by
    intro i
    let φ : Pn n →* F110 := (projR n i).comp fbar.toMonoidHom
    have huniq := Frob.commuting_gen_unique (p := 11) (q := 10) (r := (2 : ZMod 11))
      (idxList n) (idxList_nodup n) (fun s => (compSub n s).map φ)
      (by
        intro s _ t _ hst x hx y hy
        obtain ⟨x', hx', rfl⟩ := hx
        obtain ⟨y', hy', rfl⟩ := hy
        rw [← map_mul, compSub_comm n hst hx' hy', map_mul])
      (by
        intro z
        let y : Pn n := fbar.symm (inclR n i z)
        refine ⟨fun s => φ (piece n y s),
          fun s _ => Subgroup.mem_map_of_mem φ (piece_mem_compSub n y s), ?_⟩
        rw [← list_map_monoidHom_prod, prod_piece_eq n y]
        change (fbar (fbar.symm (inclR n i z))).2 i = z
        rw [MulEquiv.apply_symm_apply]
        simp [inclR])
    obtain ⟨s₀, _, htop, hbot⟩ := huniq
    exact ⟨s₀, htop, fun s hne => hbot s (mem_idxList n s) hne⟩
  choose ρL hρL_top hρL_bot using hL_ex
  choose ρR hρR_top hρR_bot using hR_ex
  let ρ : (Fin n ⊕ Fin n) → (Fin n ⊕ Fin n) := Sum.elim ρL ρR
  have hρ_surj : Function.Surjective ρ := by
    intro s
    by_contra hnot
    have hneL : ∀ i : Fin n, s ≠ ρL i := fun i h => hnot ⟨Sum.inl i, h.symm⟩
    have hneR : ∀ i : Fin n, s ≠ ρR i := fun i h => hnot ⟨Sum.inr i, h.symm⟩
    have hkill : ∀ y ∈ compSub n s, fbar y = 1 := by
      intro y hy
      apply Prod.ext
      · ext i
        have hbot := hρL_bot i s (hneL i)
        rw [Subgroup.eq_bot_iff_forall] at hbot
        exact hbot _ (Subgroup.mem_map_of_mem _ hy)
      · ext i
        have hbot := hρR_bot i s (hneR i)
        rw [Subgroup.eq_bot_iff_forall] at hbot
        exact hbot _ (Subgroup.mem_map_of_mem _ hy)
    cases s with
    | inl j =>
      have hy1 : inclL n j Frob.g10 = 1 :=
        fbar.injective ((hkill _ ⟨Frob.g10, rfl⟩).trans (map_one fbar).symm)
      have h1 : (Frob.g10 : F42) = 1 := by
        have := congrFun (congrArg Prod.fst hy1) j
        simpa [inclL] using this
      exact Frob.g10_ne_one h1
    | inr j =>
      have hy1 : inclR n j Frob.g10 = 1 :=
        fbar.injective ((hkill _ ⟨Frob.g10, rfl⟩).trans (map_one fbar).symm)
      have h1 : (Frob.g10 : F110) = 1 := by
        have := congrFun (congrArg Prod.snd hy1) j
        simpa [inclR] using this
      exact Frob.g10_ne_one h1
  have hρ_bij : Function.Bijective ρ :=
    ⟨Finite.injective_iff_surjective.mpr hρ_surj, hρ_surj⟩
  have hρL_inl : ∀ i : Fin n, ∃ j : Fin n, ρL i = Sum.inl j := by
    intro i
    cases h : ρL i with
    | inl j => exact ⟨j, rfl⟩
    | inr j =>
      let θ : F110 →* F42 := ((projL n i).comp fbar.toMonoidHom).comp (inclR n j)
      have hθ_surj : Function.Surjective θ := by
        intro z
        have hz : z ∈ (compSub n (Sum.inr j)).map ((projL n i).comp fbar.toMonoidHom) := by
          rw [← h, hρL_top i]; trivial
        obtain ⟨y, ⟨a, rfl⟩, rfl⟩ := hz
        exact ⟨a, rfl⟩
      have hθ_inj : Function.Injective θ := by
        intro a b hab
        have hker : θ (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
        have hf1 : fbar (inclR n j (a * b⁻¹)) = 1 := by
          apply Prod.ext
          · ext i'
            by_cases hi : i' = i
            · subst hi; exact hker
            · have hne : Sum.inr j ≠ ρL i' := by
                intro heq
                have : ρ (Sum.inl i) = ρ (Sum.inl i') := by simp [ρ, h, heq]
                exact hi (Sum.inl.inj (hρ_bij.1 this)).symm
              have hbot := hρL_bot i' (Sum.inr j) hne
              rw [Subgroup.eq_bot_iff_forall] at hbot
              exact hbot _ (Subgroup.mem_map_of_mem _ ⟨a * b⁻¹, rfl⟩)
          · ext i'
            have hne : Sum.inr j ≠ ρR i' := by
              intro heq
              have : ρ (Sum.inl i) = ρ (Sum.inr i') := by simp [ρ, h, heq]
              cases hρ_bij.1 this
            have hbot := hρR_bot i' (Sum.inr j) hne
            rw [Subgroup.eq_bot_iff_forall] at hbot
            exact hbot _ (Subgroup.mem_map_of_mem _ ⟨a * b⁻¹, rfl⟩)
        have hincl : inclR n j (a * b⁻¹) = 1 :=
          fbar.injective (hf1.trans (map_one fbar).symm)
        have h1 : a * b⁻¹ = 1 := by
          have := congrFun (congrArg Prod.snd hincl) j
          simpa [inclR] using this
        exact mul_inv_eq_one.mp h1
      exact (not_equiv_F42_F110 (Equiv.ofBijective θ ⟨hθ_inj, hθ_surj⟩).symm).elim
  have hρR_inr : ∀ i : Fin n, ∃ j : Fin n, ρR i = Sum.inr j := by
    intro i
    cases h : ρR i with
    | inr j => exact ⟨j, rfl⟩
    | inl j =>
      let θ : F42 →* F110 := ((projR n i).comp fbar.toMonoidHom).comp (inclL n j)
      have hθ_surj : Function.Surjective θ := by
        intro z
        have hz : z ∈ (compSub n (Sum.inl j)).map ((projR n i).comp fbar.toMonoidHom) := by
          rw [← h, hρR_top i]; trivial
        obtain ⟨y, ⟨a, rfl⟩, rfl⟩ := hz
        exact ⟨a, rfl⟩
      have hθ_inj : Function.Injective θ := by
        intro a b hab
        have hker : θ (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
        have hf1 : fbar (inclL n j (a * b⁻¹)) = 1 := by
          apply Prod.ext
          · ext i'
            have hne : Sum.inl j ≠ ρL i' := by
              intro heq
              have : ρ (Sum.inr i) = ρ (Sum.inl i') := by simp [ρ, h, heq]
              cases hρ_bij.1 this
            have hbot := hρL_bot i' (Sum.inl j) hne
            rw [Subgroup.eq_bot_iff_forall] at hbot
            exact hbot _ (Subgroup.mem_map_of_mem _ ⟨a * b⁻¹, rfl⟩)
          · ext i'
            by_cases hi : i' = i
            · subst hi; exact hker
            · have hne : Sum.inl j ≠ ρR i' := by
                intro heq
                have : ρ (Sum.inr i) = ρ (Sum.inr i') := by simp [ρ, h, heq]
                exact hi (Sum.inr.inj (hρ_bij.1 this)).symm
              have hbot := hρR_bot i' (Sum.inl j) hne
              rw [Subgroup.eq_bot_iff_forall] at hbot
              exact hbot _ (Subgroup.mem_map_of_mem _ ⟨a * b⁻¹, rfl⟩)
        have hincl : inclL n j (a * b⁻¹) = 1 :=
          fbar.injective (hf1.trans (map_one fbar).symm)
        have h1 : a * b⁻¹ = 1 := by
          have := congrFun (congrArg Prod.fst hincl) j
          simpa [inclL] using this
        exact mul_inv_eq_one.mp h1
      exact (not_equiv_F42_F110 (Equiv.ofBijective θ ⟨hθ_inj, hθ_surj⟩)).elim
  choose σf hσf using hρL_inl
  choose τf hτf using hρR_inr
  have hσ_inj : Function.Injective σf := by
    intro i₁ i₂ h
    have : ρ (Sum.inl i₁) = ρ (Sum.inl i₂) := by simp [ρ, hσf, h]
    exact Sum.inl.inj (hρ_bij.1 this)
  have hτ_inj : Function.Injective τf := by
    intro i₁ i₂ h
    have : ρ (Sum.inr i₁) = ρ (Sum.inr i₂) := by simp [ρ, hτf, h]
    exact Sum.inr.inj (hρ_bij.1 this)
  let σ : Equiv.Perm (Fin n) :=
    Equiv.ofBijective σf ⟨hσ_inj, Finite.injective_iff_surjective.mp hσ_inj⟩
  let τ : Equiv.Perm (Fin n) :=
    Equiv.ofBijective τf ⟨hτ_inj, Finite.injective_iff_surjective.mp hτ_inj⟩
  refine ⟨σ, τ, fun x i => ⟨?_, ?_⟩⟩
  · let α : F42 →* F42 := ((projL n i).comp fbar.toMonoidHom).comp (inclL n (σ i))
    have hα_surj : Function.Surjective α := by
      intro z
      have hz : z ∈ (compSub n (Sum.inl (σ i))).map ((projL n i).comp fbar.toMonoidHom) := by
        change z ∈ (compSub n (Sum.inl (σf i))).map _
        rw [← hσf i, hρL_top i]; trivial
      obtain ⟨y, ⟨a, rfl⟩, rfl⟩ := hz
      exact ⟨a, rfl⟩
    have hα_bij : Function.Bijective α :=
      ⟨Finite.injective_iff_surjective.mpr hα_surj, hα_surj⟩
    let αe : F42 ≃* F42 := MulEquiv.ofBijective α hα_bij
    have hproj : (fbar x).1 i = αe (x.1 (σ i)) := by
      change ((projL n i).comp fbar.toMonoidHom) x = α (x.1 (σ i))
      conv_lhs => rw [← prod_piece_eq n x]
      rw [list_map_monoidHom_prod]
      rw [list_map_prod_eq_single (idxList n) (idxList_nodup n) (Sum.inl (σ i)) (mem_idxList n _)]
      · rfl
      · intro s _ hne
        have hne' : s ≠ ρL i := by
          rw [hσf i]; exact hne
        have hbot := hρL_bot i s hne'
        rw [Subgroup.eq_bot_iff_forall] at hbot
        exact hbot _ (Subgroup.mem_map_of_mem _ (piece_mem_compSub n x s))
    rw [hproj]
    exact Frob.aut_b αe (x.1 (σ i))
  · let β : F110 →* F110 := ((projR n i).comp fbar.toMonoidHom).comp (inclR n (τ i))
    have hβ_surj : Function.Surjective β := by
      intro z
      have hz : z ∈ (compSub n (Sum.inr (τ i))).map ((projR n i).comp fbar.toMonoidHom) := by
        change z ∈ (compSub n (Sum.inr (τf i))).map _
        rw [← hτf i, hρR_top i]; trivial
      obtain ⟨y, ⟨a, rfl⟩, rfl⟩ := hz
      exact ⟨a, rfl⟩
    have hβ_bij : Function.Bijective β :=
      ⟨Finite.injective_iff_surjective.mpr hβ_surj, hβ_surj⟩
    let βe : F110 ≃* F110 := MulEquiv.ofBijective β hβ_bij
    have hproj : (fbar x).2 i = βe (x.2 (τ i)) := by
      change ((projR n i).comp fbar.toMonoidHom) x = β (x.2 (τ i))
      conv_lhs => rw [← prod_piece_eq n x]
      rw [list_map_monoidHom_prod]
      rw [list_map_prod_eq_single (idxList n) (idxList_nodup n) (Sum.inr (τ i)) (mem_idxList n _)]
      · rfl
      · intro s _ hne
        have hne' : s ≠ ρR i := by
          rw [hτf i]; exact hne
        have hbot := hρR_bot i s hne'
        rw [Subgroup.eq_bot_iff_forall] at hbot
        exact hbot _ (Subgroup.mem_map_of_mem _ (piece_mem_compSub n x s))
    rw [hproj]
    exact Frob.aut_b βe (x.2 (τ i))

/-! Section 5: Integer matrix M ∈ GL_n(ℤ) and congruences mod 3 and mod 5 -/

private def eGen (n : ℕ) (j : Fin n) : Gn n :=
  fun k => if k = j then ⟨15, 1, 1, rfl, rfl⟩ else 1

private def gGen (n : ℕ) (j : Fin n) : Gn n :=
  fun k => if k = j then ⟨1, Frob.g01, Frob.g01, by decide, by decide⟩ else 1

private def zMat {n : ℕ} (f : Gn n ≃* Gn n) (i j : Fin n) : ℤ :=
  (f (eGen n j) i).z / 15

private lemma qMap_eGen (n : ℕ) (j : Fin n) : qMap n (eGen n j) = 1 := by
  apply Prod.ext <;> ext k <;> by_cases h : k = j <;> simp [qMap, eGen, h, G.one_u, G.one_v]

private lemma qMap_f_eGen {n : ℕ} (f : Gn n ≃* Gn n) (j : Fin n) :
    qMap n (f (eGen n j)) = 1 := by
  rw [← inducedAut_qMap, qMap_eGen, map_one]

private lemma fifteen_mul_zMat {n : ℕ} (f : Gn n ≃* Gn n) (i j : Fin n) :
    15 * zMat f i j = (f (eGen n j) i).z := by
  unfold zMat
  have hq := qMap_f_eGen f j
  have hu : (f (eGen n j) i).u = 1 := congrFun (congrArg Prod.fst hq) i
  have hv : (f (eGen n j) i).v = 1 := congrFun (congrArg Prod.snd hq) i
  have h3 := (f (eGen n j) i).h3
  have h5 := (f (eGen n j) i).h5
  rw [hu, Frob.one_b, ZMod.val_zero] at h3
  rw [hv, Frob.one_b, ZMod.val_zero] at h5
  omega

private lemma gn_zpow_apply {n : ℕ} (g : Gn n) (k : ℤ) (i : Fin n) :
    (g ^ k) i = (g i) ^ k := rfl

private lemma list_prod_z (n : ℕ) (i : Fin n) (L : List (Gn n)) :
    (L.prod i).z = (L.map (fun g => (g i).z)).sum := by
  induction L with
  | nil => rfl
  | cons g L ih =>
    simp only [List.prod_cons, List.map_cons, List.sum_cons, Pi.mul_apply, G.mul_z, ih]

private lemma list_prod_u (n : ℕ) (i : Fin n) (L : List (Gn n)) :
    (L.prod i).u = (L.map (fun g => (g i).u)).prod := by
  induction L with
  | nil => rfl
  | cons g L ih =>
    simp only [List.prod_cons, List.map_cons, Pi.mul_apply, G.mul_u, ih]

private lemma list_prod_v (n : ℕ) (i : Fin n) (L : List (Gn n)) :
    (L.prod i).v = (L.map (fun g => (g i).v)).prod := by
  induction L with
  | nil => rfl
  | cons g L ih =>
    simp only [List.prod_cons, List.map_cons, Pi.mul_apply, G.mul_v, ih]

private lemma list_sum_eq_finset_sum {α : Type*} [DecidableEq α]
    (L : List α) (hL : L.Nodup) (a : α → ℤ) :
    (L.map a).sum = ∑ j ∈ L.toFinset, a j := by
  induction L with
  | nil => simp
  | cons x L ih =>
    rw [List.nodup_cons] at hL
    rw [List.map_cons, List.sum_cons, List.toFinset_cons, Finset.sum_insert (by simp [hL.1]), ih hL.2]

private lemma list_finRange_sum {n : ℕ} (a : Fin n → ℤ) :
    ((List.finRange n).map a).sum = ∑ j : Fin n, a j := by
  rw [list_sum_eq_finset_sum _ (List.nodup_finRange n)]
  congr 1
  ext j
  simp

private lemma ker_decomp {n : ℕ} (g : Gn n) (hq : qMap n g = 1) :
    g = ((List.finRange n).map (fun j => (eGen n j) ^ ((g j).z / 15))).prod := by
  ext i
  have hu : (g i).u = 1 := congrFun (congrArg Prod.fst hq) i
  have hv : (g i).v = 1 := congrFun (congrArg Prod.snd hq) i
  have h3 := (g i).h3
  have h5 := (g i).h5
  rw [hu, Frob.one_b, ZMod.val_zero] at h3
  rw [hv, Frob.one_b, ZMod.val_zero] at h5
  apply G.ext
  · rw [list_prod_z, List.map_map, list_finRange_sum]
    have hsum : ∑ j : Fin n, (((eGen n j) ^ ((g j).z / 15)) i).z =
        ∑ j : Fin n, if i = j then ((g j).z / 15) * 15 else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      rw [gn_zpow_apply, G.zpow_z]
      by_cases hij : i = j
      · simp [eGen, hij]
      · simp [eGen, hij, G.one_z]
    dsimp only [Function.comp_apply]
    rw [hsum, Finset.sum_ite_eq Finset.univ i]
    simp only [Finset.mem_univ, if_true]
    omega
  · rw [hu, list_prod_u, List.map_map]
    symm
    apply List.prod_eq_one
    intro y hy
    rw [List.mem_map] at hy
    obtain ⟨j, _, rfl⟩ := hy
    dsimp only [Function.comp_apply]
    rw [gn_zpow_apply, G.zpow_u]
    by_cases hij : i = j
    · simp [eGen, hij]
    · simp [eGen, hij, G.one_u]
  · rw [hv, list_prod_v, List.map_map]
    symm
    apply List.prod_eq_one
    intro y hy
    rw [List.mem_map] at hy
    obtain ⟨j, _, rfl⟩ := hy
    dsimp only [Function.comp_apply]
    rw [gn_zpow_apply, G.zpow_v]
    by_cases hij : i = j
    · simp [eGen, hij]
    · simp [eGen, hij, G.one_v]

private lemma f_ker_z {n : ℕ} (f : Gn n ≃* Gn n) (g : Gn n) (hq : qMap n g = 1) (i : Fin n) :
    (f g i).z = 15 * ∑ j : Fin n, zMat f i j * ((g j).z / 15) := by
  have hd := ker_decomp g hq
  conv_lhs =>
    rw [hd]
    change (f.toMonoidHom _ i).z
    rw [list_map_monoidHom_prod]
  rw [list_prod_z, List.map_map, list_finRange_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  change (f ((eGen n j) ^ ((g j).z / 15)) i).z = 15 * (zMat f i j * ((g j).z / 15))
  rw [map_zpow, gn_zpow_apply, G.zpow_z, ← fifteen_mul_zMat f i j]
  ring

lemma zMat_mul_inv {n : ℕ} (f : Gn n ≃* Gn n) (i k : Fin n) :
    ∑ j : Fin n, zMat f i j * zMat f.symm j k = if i = k then 1 else 0 := by
  have h1 := f_ker_z f (f.symm (eGen n k)) (qMap_f_eGen f.symm k) i
  rw [MulEquiv.apply_symm_apply] at h1
  have hlhs : (eGen n k i).z = 15 * (if i = k then 1 else 0) := by
    by_cases hik : i = k <;> simp [eGen, hik, G.one_z]
  rw [hlhs] at h1
  have hrhs : ∑ j : Fin n, zMat f i j * ((f.symm (eGen n k) j).z / 15) =
      ∑ j : Fin n, zMat f i j * zMat f.symm j k := rfl
  rw [hrhs] at h1
  omega

lemma f_z_linear {n : ℕ} (f : Gn n ≃* Gn n) (g : Gn n) (i : Fin n) :
    (f g i).z = ∑ j : Fin n, zMat f i j * (g j).z := by
  have hq : qMap n (g ^ (2310 : ℕ)) = 1 := by
    rw [map_pow]
    apply Prod.ext
    · ext j; exact F42_pow_2310 (g j).u
    · ext j; exact F110_pow_2310 (g j).v
  have h1 := f_ker_z f (g ^ (2310 : ℕ)) hq i
  rw [map_pow, Pi.pow_apply, G.npow_z] at h1
  have h2 : 15 * ∑ j : Fin n, zMat f i j * (((g ^ (2310 : ℕ)) j).z / 15) =
      2310 * ∑ j : Fin n, zMat f i j * (g j).z := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [Pi.pow_apply, G.npow_z]
    have hdiv : ((2310 : ℕ) : ℤ) * (g j).z / 15 = 154 * (g j).z := by omega
    rw [hdiv]
    ring
  rw [h2] at h1
  norm_cast at h1
  omega

lemma aut_Gn_data {n : ℕ} (f : Gn n ≃* Gn n) :
    ∃ σ τ : Equiv.Perm (Fin n),
      (∀ (g : Gn n) (i : Fin n),
        ((f g i).u).b = ((g (σ i)).u).b ∧ ((f g i).v).b = ((g (τ i)).v).b) ∧
      (∀ i j : Fin n,
        zMat f i j % 3 = (if σ i = j then 1 else 0) ∧
        zMat f i j % 5 = (if τ i = j then 1 else 0)) := by
  obtain ⟨σ, τ, hστ⟩ := aut_Pn_b (inducedAut f)
  have hb : ∀ (g : Gn n) (i : Fin n),
      ((f g i).u).b = ((g (σ i)).u).b ∧ ((f g i).v).b = ((g (τ i)).v).b := by
    intro g i
    have h := hστ (qMap n g) i
    rw [inducedAut_qMap] at h
    exact h
  refine ⟨σ, τ, hb, ?_⟩
  intro i j
  have hz : (f (gGen n j) i).z = zMat f i j := by
    rw [f_z_linear f (gGen n j) i]
    have hsum : ∑ k : Fin n, zMat f i k * (gGen n j k).z =
        ∑ k : Fin n, if k = j then zMat f i k else 0 := by
      apply Finset.sum_congr rfl
      intro k _
      by_cases hkj : k = j <;> simp [gGen, hkj, G.one_z]
    rw [hsum, Finset.sum_ite_eq' Finset.univ j]
    simp
  have hbu := (hb (gGen n j) i).1
  have hbv := (hb (gGen n j) i).2
  have h3 := (f (gGen n j) i).h3
  have h5 := (f (gGen n j) i).h5
  rw [hz, hbu] at h3
  rw [hz, hbv] at h5
  constructor
  · by_cases h : σ i = j
    · simp only [gGen, h, if_true] at h3 ⊢
      exact h3
    · simp only [gGen, h, if_false, G.one_u, Frob.one_b, ZMod.val_zero] at h3 ⊢
      exact h3
  · by_cases h : τ i = j
    · simp only [gGen, h, if_true] at h5 ⊢
      exact h5
    · simp only [gGen, h, if_false, G.one_v, Frob.one_b, ZMod.val_zero] at h5 ⊢
      exact h5

/-! Section 6: H is characteristic in G and H.prod H is characteristic in G × G -/

private lemma Hn_map_of_eq {n : ℕ} (f : Gn n ≃* Gn n)
    (σ : Equiv.Perm (Fin n))
    (hb : ∀ (g : Gn n) (i : Fin n),
      ((f g i).u).b = ((g (σ i)).u).b ∧ ((f g i).v).b = ((g (σ i)).v).b)
    (g : Gn n) (hg : ∀ i : Fin n, g i ∈ H) (i : Fin n) : f g i ∈ H := by
  change ((f g i).u).b.val % 2 = ((f g i).v).b.val % 2
  rw [(hb g i).1, (hb g i).2]
  exact hg (σ i)

lemma H_char : H.Characteristic := by
  rw [Subgroup.characteristic_iff_le_comap]
  intro e x hx
  let eq1 : G ≃* Gn 1 :=
    { toFun := fun g _ => g
      invFun := fun f => f 0
      left_inv := fun _ => rfl
      right_inv := fun f => by ext i; rw [Subsingleton.elim i 0]
      map_mul' := fun _ _ => rfl }
  let f : Gn 1 ≃* Gn 1 := eq1.symm.trans (e.trans eq1)
  obtain ⟨σ, τ, hb, _⟩ := aut_Gn_data f
  have hστ : σ = τ := Subsingleton.elim σ τ
  subst hστ
  have hmem := Hn_map_of_eq f σ hb (eq1 x) (fun _ => hx) 0
  simpa [f, eq1] using hmem

lemma H_prod_char : (H.prod H).Characteristic := by
  rw [Subgroup.characteristic_iff_le_comap]
  intro e p hp
  let eq2 : (G × G) ≃* Gn 2 :=
    { toFun := fun q i => if i = 0 then q.1 else q.2
      invFun := fun g => (g 0, g 1)
      left_inv := fun _ => rfl
      right_inv := fun g => by ext i; fin_cases i <;> rfl
      map_mul' := fun q₁ q₂ => by ext i; fin_cases i <;> rfl }
  let f : Gn 2 ≃* Gn 2 := eq2.symm.trans (e.trans eq2)
  obtain ⟨σ, τ, hb, hmod⟩ := aut_Gn_data f
  let m00 := zMat f 0 0
  let m01 := zMat f 0 1
  let m10 := zMat f 1 0
  let m11 := zMat f 1 1
  let n00 := zMat f.symm 0 0
  let n01 := zMat f.symm 0 1
  let n10 := zMat f.symm 1 0
  let n11 := zMat f.symm 1 1
  have h00 : m00 * n00 + m01 * n10 = 1 := by
    have := zMat_mul_inv f 0 0; simpa [Fin.sum_univ_two, m00, m01, n00, n10] using this
  have h01 : m00 * n01 + m01 * n11 = 0 := by
    have := zMat_mul_inv f 0 1; simpa [Fin.sum_univ_two, m00, m01, n01, n11] using this
  have h10 : m10 * n00 + m11 * n10 = 0 := by
    have := zMat_mul_inv f 1 0; simpa [Fin.sum_univ_two, m10, m11, n00, n10] using this
  have h11 : m10 * n01 + m11 * n11 = 1 := by
    have := zMat_mul_inv f 1 1; simpa [Fin.sum_univ_two, m10, m11, n01, n11] using this
  have hdet_mul : (m00 * m11 - m01 * m10) * (n00 * n11 - n01 * n10) = 1 := by
    have heq : (m00 * m11 - m01 * m10) * (n00 * n11 - n01 * n10) =
        (m00 * n00 + m01 * n10) * (m10 * n01 + m11 * n11) -
        (m00 * n01 + m01 * n11) * (m10 * n00 + m11 * n10) := by ring
    rw [heq, h00, h11, h01, h10]
    ring
  have hdet_pm : m00 * m11 - m01 * m10 = 1 ∨ m00 * m11 - m01 * m10 = -1 :=
    Int.eq_one_or_neg_one_of_mul_eq_one hdet_mul
  have hm00_3 := (hmod 0 0).1
  have hm01_3 := (hmod 0 1).1
  have hm10_3 := (hmod 1 0).1
  have hm11_3 := (hmod 1 1).1
  have hm00_5 := (hmod 0 0).2
  have hm01_5 := (hmod 0 1).2
  have hm10_5 := (hmod 1 0).2
  have hm11_5 := (hmod 1 1).2
  have hdet_mod3 : (m00 * m11 - m01 * m10) % 3 =
      ((m00 % 3) * (m11 % 3) - (m01 % 3) * (m10 % 3)) % 3 := by
    have h1 := Int.mul_emod m00 m11 3
    have h2 := Int.mul_emod m01 m10 3
    omega
  have hdet_mod5 : (m00 * m11 - m01 * m10) % 5 =
      ((m00 % 5) * (m11 % 5) - (m01 % 5) * (m10 % 5)) % 5 := by
    have h1 := Int.mul_emod m00 m11 5
    have h2 := Int.mul_emod m01 m10 5
    omega
  have hfin2 : ∀ x : Fin 2, x = 0 ∨ x = 1 := fun x => by fin_cases x <;> simp
  have hperm2 : ∀ π : Equiv.Perm (Fin 2), (π 0 = 0 ∧ π 1 = 1) ∨ (π 0 = 1 ∧ π 1 = 0) := by
    intro π
    rcases hfin2 (π 0) with h0 | h0 <;> rcases hfin2 (π 1) with h1 | h1
    · exfalso; exact absurd (π.injective (h0.trans h1.symm)) (by decide)
    · exact Or.inl ⟨h0, h1⟩
    · exact Or.inr ⟨h0, h1⟩
    · exfalso; exact absurd (π.injective (h0.trans h1.symm)) (by decide)
  have hσ_det : σ 0 = 0 ↔ m00 * m11 - m01 * m10 = 1 := by
    rcases hperm2 σ with ⟨hσ0, hσ1⟩ | ⟨hσ0, hσ1⟩
    · simp only [hσ0, hσ1] at hm00_3 hm01_3 hm10_3 hm11_3
      change m00 % 3 = 1 at hm00_3; change m01 % 3 = 0 at hm01_3
      change m10 % 3 = 0 at hm10_3; change m11 % 3 = 1 at hm11_3
      rw [hm00_3, hm01_3, hm10_3, hm11_3] at hdet_mod3
      exact ⟨fun _ => by omega, fun _ => hσ0⟩
    · simp only [hσ0, hσ1] at hm00_3 hm01_3 hm10_3 hm11_3
      change m00 % 3 = 0 at hm00_3; change m01 % 3 = 1 at hm01_3
      change m10 % 3 = 1 at hm10_3; change m11 % 3 = 0 at hm11_3
      rw [hm00_3, hm01_3, hm10_3, hm11_3] at hdet_mod3
      exact ⟨fun h => (by rw [hσ0] at h; cases h), fun h => by omega⟩
  have hτ_det : τ 0 = 0 ↔ m00 * m11 - m01 * m10 = 1 := by
    rcases hperm2 τ with ⟨hτ0, hτ1⟩ | ⟨hτ0, hτ1⟩
    · simp only [hτ0, hτ1] at hm00_5 hm01_5 hm10_5 hm11_5
      change m00 % 5 = 1 at hm00_5; change m01 % 5 = 0 at hm01_5
      change m10 % 5 = 0 at hm10_5; change m11 % 5 = 1 at hm11_5
      rw [hm00_5, hm01_5, hm10_5, hm11_5] at hdet_mod5
      exact ⟨fun _ => by omega, fun _ => hτ0⟩
    · simp only [hτ0, hτ1] at hm00_5 hm01_5 hm10_5 hm11_5
      change m00 % 5 = 0 at hm00_5; change m01 % 5 = 1 at hm01_5
      change m10 % 5 = 1 at hm10_5; change m11 % 5 = 0 at hm11_5
      rw [hm00_5, hm01_5, hm10_5, hm11_5] at hdet_mod5
      exact ⟨fun h => (by rw [hτ0] at h; cases h), fun h => by omega⟩
  have hστ : σ = τ := by
    ext i
    rcases hperm2 σ with ⟨hσ0, hσ1⟩ | ⟨hσ0, hσ1⟩ <;> rcases hperm2 τ with ⟨hτ0, hτ1⟩ | ⟨hτ0, hτ1⟩
    · fin_cases i <;> simp [hσ0, hσ1, hτ0, hτ1]
    · exfalso; have h := hτ_det.mpr (hσ_det.mp hσ0); rw [hτ0] at h; cases h
    · exfalso; have h := hσ_det.mpr (hτ_det.mp hτ0); rw [hσ0] at h; cases h
    · fin_cases i <;> simp [hσ0, hσ1, hτ0, hτ1]
  subst hστ
  have hpg : ∀ i : Fin 2, eq2 p i ∈ H := by
    intro i; fin_cases i
    · exact hp.1
    · exact hp.2
  have hm0 := Hn_map_of_eq f σ hb (eq2 p) hpg 0
  have hm1 := Hn_map_of_eq f σ hb (eq2 p) hpg 1
  exact ⟨by simpa [f, eq2] using hm0, by simpa [f, eq2] using hm1⟩

/-! Section 7: Explicit automorphism Φ ∈ Aut(G^3) violating H^3.Characteristic -/

private def phiFun (g : Gn 3) (i : Fin 3) : G :=
  match i with
  | 0 =>
    { z := -9 * (g 0).z - 5 * (g 2).z
      u := (g 2).u
      v := (g 0).v
      h3 := by have h := (g 2).h3; omega
      h5 := by have h := (g 0).h5; omega }
  | 1 =>
    { z := -5 * (g 0).z + 6 * (g 1).z
      u := (g 0).u
      v := (g 1).v
      h3 := by have h := (g 0).h3; omega
      h5 := by have h := (g 1).h5; omega }
  | 2 =>
    { z := 15 * (g 0).z - 5 * (g 1).z + 6 * (g 2).z
      u := (g 1).u
      v := (g 2).v
      h3 := by have h := (g 1).h3; omega
      h5 := by have h := (g 2).h5; omega }

private def psiFun (g : Gn 3) (i : Fin 3) : G :=
  match i with
  | 0 =>
    { z := 36 * (g 0).z + 25 * (g 1).z + 30 * (g 2).z
      u := (g 1).u
      v := (g 0).v
      h3 := by have h := (g 1).h3; omega
      h5 := by have h := (g 0).h5; omega }
  | 1 =>
    { z := 30 * (g 0).z + 21 * (g 1).z + 25 * (g 2).z
      u := (g 2).u
      v := (g 1).v
      h3 := by have h := (g 2).h3; omega
      h5 := by have h := (g 1).h5; omega }
  | 2 =>
    { z := -65 * (g 0).z - 45 * (g 1).z - 54 * (g 2).z
      u := (g 0).u
      v := (g 2).v
      h3 := by have h := (g 0).h3; omega
      h5 := by have h := (g 2).h5; omega }

private def phiAut : Gn 3 ≃* Gn 3 where
  toFun := phiFun
  invFun := psiFun
  left_inv g := by
    ext i
    fin_cases i
    · apply G.ext; · dsimp [phiFun, psiFun]; ring
      · rfl
      · rfl
    · apply G.ext; · dsimp [phiFun, psiFun]; ring
      · rfl
      · rfl
    · apply G.ext; · dsimp [phiFun, psiFun]; ring
      · rfl
      · rfl
  right_inv g := by
    ext i
    fin_cases i
    · apply G.ext; · dsimp [phiFun, psiFun]; ring
      · rfl
      · rfl
    · apply G.ext; · dsimp [phiFun, psiFun]; ring
      · rfl
      · rfl
    · apply G.ext; · dsimp [phiFun, psiFun]; ring
      · rfl
      · rfl
  map_mul' g₁ g₂ := by
    ext i
    fin_cases i
    · apply G.ext
      · simp only [phiFun, Pi.mul_apply, G.mul_z]; ring
      · rfl
      · rfl
    · apply G.ext
      · simp only [phiFun, Pi.mul_apply, G.mul_z]; ring
      · rfl
      · rfl
    · apply G.ext
      · simp only [phiFun, Pi.mul_apply, G.mul_z]; ring
      · rfl
      · rfl

private def hWitness : Gn 3
  | 0 => ⟨0, ⟨0, 3⟩, ⟨0, 5⟩, by decide, by decide⟩
  | 1 => 1
  | 2 => 1

lemma not_H3_char : ¬ (Subgroup.pi Set.univ (fun _ : Fin 3 => H)).Characteristic := by
  intro hchar
  have hmem : hWitness ∈ Subgroup.pi Set.univ (fun _ : Fin 3 => H) := by
    intro i _
    fin_cases i
    · change (3 : ZMod 6).val % 2 = (5 : ZMod 10).val % 2; decide
    · exact H.one_mem
    · exact H.one_mem
  have hfixed := hchar.fixed phiAut.symm
  have hcomap : phiAut hWitness ∈
      (Subgroup.pi Set.univ (fun _ : Fin 3 => H)).comap phiAut.symm.toMonoidHom := by
    change phiAut.symm (phiAut hWitness) ∈ Subgroup.pi Set.univ (fun _ : Fin 3 => H)
    rw [MulEquiv.symm_apply_apply]
    exact hmem
  rw [hfixed] at hcomap
  have h0 : phiAut hWitness 0 ∈ H := hcomap 0 trivial
  change (0 : ZMod 6).val % 2 = (5 : ZMod 10).val % 2 at h0
  exact absurd h0 (by decide)

/-! Section 8: Universe-polymorphic lift via ULift -/

lemma characteristic_comap_mulEquiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (K : Subgroup B) :
    (K.comap e.toMonoidHom).Characteristic ↔ K.Characteristic := by
  simp only [Subgroup.characteristic_iff_le_comap]
  constructor
  · intro hA φ x hx
    have h1 := hA (e.trans (φ.trans e.symm)) (show e.symm x ∈ K.comap e.toMonoidHom by simpa using hx)
    simpa using h1
  · intro hB φ x hx
    have h1 := hB (e.symm.trans (φ.trans e)) hx
    simpa using h1

def uliftMulEquiv.{u} : ULift.{u} G ≃* G where
  toFun x := x.down
  invFun x := ULift.up x
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

def Hu.{u} : Subgroup (ULift.{u} G) :=
  H.comap uliftMulEquiv.toMonoidHom

lemma Hu_char.{u} : Hu.{u}.Characteristic :=
  (characteristic_comap_mulEquiv uliftMulEquiv H).mpr H_char

lemma Hu_prod_char.{u} : (Hu.{u}.prod Hu.{u}).Characteristic := by
  have heq : Hu.{u}.prod Hu.{u} =
      (H.prod H).comap (uliftMulEquiv.prodCongr uliftMulEquiv).toMonoidHom := by
    ext ⟨x, y⟩; rfl
  rw [heq]
  exact (characteristic_comap_mulEquiv (uliftMulEquiv.prodCongr uliftMulEquiv) (H.prod H)).mpr
    H_prod_char

lemma not_Hu3_char.{u} :
    ¬ (Subgroup.pi Set.univ (fun _ : Fin 3 => Hu.{u})).Characteristic := by
  let e3 : (Fin 3 → ULift.{u} G) ≃* Gn 3 := MulEquiv.piCongrRight (fun _ => uliftMulEquiv)
  have heq : Subgroup.pi Set.univ (fun _ : Fin 3 => Hu.{u}) =
      (Subgroup.pi Set.univ (fun _ : Fin 3 => H)).comap e3.toMonoidHom := by
    ext g
    simp [Subgroup.mem_pi, Hu, e3]
  rw [heq, characteristic_comap_mulEquiv e3]
  exact not_H3_char

end Mo35701

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_35701.main) :=
  fun h => Mo35701.not_Hu3_char (h (ULift Mo35701.G) Mo35701.Hu Mo35701.Hu_char Mo35701.Hu_prod_char 3)
