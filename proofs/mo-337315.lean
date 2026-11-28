import OMAStatements.S_mo_337315
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Positivity

namespace RectCertificate

structure Bounds (α : Type) where
  x₀ : α
  x₁ : α
  y₀ : α
  y₁ : α
deriving Repr

abbrev IB := Bounds ℤ
abbrev RB := Bounds ℝ

def good (r : RB) : Prop := r.x₀ ≤ r.x₁ ∧ r.y₀ ≤ r.y₁
def vol (r : RB) : ℝ := (r.x₁-r.x₀)*(r.y₁-r.y₀)
def fits (r : RB) (s : IB) : Prop :=
  r.x₀ ≤ s.x₁ ∧ (s.x₀ : ℝ) ≤ r.x₁ ∧ r.y₀ ≤ s.y₁ ∧ (s.y₀ : ℝ) ≤ r.y₁

def meet (s a : IB) : IB :=
  ⟨max s.x₀ a.x₀, min s.x₁ a.x₁, max s.y₀ a.y₀, min s.y₁ a.y₁⟩

def fitsOpt (r : RB) (s : Option IB) : Prop := s.elim True (fits r)
def add (s : Option IB) (a : IB) : Option IB := some (s.elim a (meet a))
def cost (s : Option IB) : ℤ :=
  s.elim 0 (fun a => max 0 (a.x₀-a.x₁) * max 0 (a.y₀-a.y₁))

theorem fits_add {r : RB} {s : Option IB} {a : IB}
    (hs : fitsOpt r s) (ha : fits r a) : fitsOpt r (add s a) := by
  cases s with
  | none => exact ha
  | some b =>
    rcases ha with ⟨h₁,h₂,h₃,h₄⟩
    change fits r b at hs
    rcases hs with ⟨h₅,h₆,h₇,h₈⟩
    simpa [add, fitsOpt, fits, meet] using
      And.intro (le_min h₁ h₅) (And.intro (max_le h₂ h₆)
        (And.intro (le_min h₃ h₇) (max_le h₄ h₈)))

theorem cost_le {r : RB} (hr : good r) {s : Option IB} (hs : fitsOpt r s) :
    (cost s : ℝ) ≤ vol r := by
  rcases hr with ⟨hx,hy⟩
  cases s with
  | none =>
    simpa [cost,vol] using mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hy)
  | some a =>
    change fits r a at hs
    rcases hs with ⟨h₁,h₂,h₃,h₄⟩
    simp [cost, vol]
    apply mul_le_mul
    · exact max_le (sub_nonneg.mpr hx) (by linarith)
    · exact max_le (sub_nonneg.mpr hy) (by linarith)
    · exact le_max_left _ _
    · exact sub_nonneg.mpr hx

def has (s : Option IB) (a : IB) : Bool :=
  s.elim false (fun b => decide (a.x₀ ≤ b.x₀ ∧ b.x₁ ≤ a.x₁ ∧ a.y₀ ≤ b.y₀ ∧ b.y₁ ≤ a.y₁))

def check (q goal : ℤ) (s t : Option IB) : List IB → Bool
  | [] => decide (goal < q*(cost s+cost t))
  | a::as => decide (goal < q*(cost s+cost t)) ||
      (if has s a || has t a then check q goal s t as
       else check q goal (add s a) t as && check q goal s (add t a) as)

theorem early {q goal : ℤ} (hq : 0 ≤ q) {A B : RB} (hA : good A) (hB : good B)
    {s t : Option IB} (hs : fitsOpt A s) (ht : fitsOpt B t) (h : goal < q*(cost s + cost t)) :
    (goal : ℝ) < q * (vol A + vol B) := by
  have hb := add_le_add (cost_le hA hs) (cost_le hB ht)
  have hh : (goal:ℝ) < (q:ℝ) * ((cost s:ℝ) + (cost t:ℝ)) := by exact_mod_cast h
  exact hh.trans_le (mul_le_mul_of_nonneg_left hb (by exact_mod_cast hq))

theorem check_sound {q goal : ℤ} (hq : 0 ≤ q) {A B : RB}
    (hA : good A) (hB : good B) (xs : List IB) (s t : Option IB)
    (hs : fitsOpt A s) (ht : fitsOpt B t)
    (hcov : ∀ p ∈ xs, fits A p ∨ fits B p) (hc : check q goal s t xs = true) :
    (goal : ℝ) < q * (vol A + vol B) := by
  induction xs generalizing s t with
  | nil => exact early hq hA hB hs ht (by simpa [check] using hc)
  | cons p ps ih =>
    simp only [check, Bool.or_eq_true, decide_eq_true_eq] at hc
    rcases hc with hh|hh
    · exact early hq hA hB hs ht hh
    · have htail := fun a (ha : a ∈ ps) => hcov a (List.mem_cons_of_mem _ ha)
      split at hh
      · exact ih s t hs ht htail hh
      · simp only [Bool.and_eq_true] at hh
        rcases hh with ⟨h₁,h₂⟩
        rcases hcov p (List.mem_cons_self) with hp|hp
        · exact ih (add s p) t (fits_add hs hp) ht htail h₁
        · exact ih s (add t p) hs (fits_add ht hp) htail h₂

abbrev Pt := ℤ × ℤ

def projected (d k : ℤ) (p : Pt) : IB :=
  let x := d*p.1+k*p.2
  let y := d*p.2-k*p.1
  ⟨min x (x+p.2), max x (x+p.2), min y (y-p.1), max y (y-p.1)⟩

theorem between {u : ℝ} (hu : 0 ≤ u) (hv : u ≤ 1) (a b : ℤ) :
    (min a (a+b) : ℤ) ≤ (a:ℝ)+u*b ∧ (a:ℝ)+u*b ≤ (max a (a+b) : ℤ) := by
  rcases le_total 0 b with hb|hb
  · have hb' : (0:ℝ) ≤ b := by exact_mod_cast hb
    simp only [min_eq_left (show a ≤ a+b by omega), max_eq_right (show a ≤ a+b by omega), Int.cast_add]
    constructor <;> nlinarith [mul_nonneg hu hb', mul_nonneg (sub_nonneg.mpr hv) hb']
  · have hb' : (b:ℝ) ≤ 0 := by exact_mod_cast hb
    simp only [min_eq_right (show a+b ≤ a by omega), max_eq_left (show a+b ≤ a by omega), Int.cast_add]
    constructor <;> nlinarith [mul_nonpos_of_nonneg_of_nonpos hu hb',
      mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hv) hb']

def scale (d : ℝ) (r : RB) : RB := ⟨d*r.x₀,d*r.x₁,d*r.y₀,d*r.y₁⟩

def inside (r : RB) (t x y : ℝ) : Prop :=
  r.x₀ ≤ x+t*y ∧ x+t*y ≤ r.x₁ ∧ r.y₀ ≤ y-t*x ∧ y-t*x ≤ r.y₁

theorem proj_fits {r : RB} {d k : ℤ} (hd : (0:ℝ) ≤ d) {t : ℝ}
    (hk : (k:ℝ) ≤ d*t) (hl : d*t ≤ (k:ℝ)+1) (p : Pt)
    (hi : inside r t p.1 p.2) : fits (scale d r) (projected d k p) := by
  rcases hi with ⟨h₁,h₂,h₃,h₄⟩
  have hu : 0 ≤ (d:ℝ)*t-k := by linarith
  have hv : (d:ℝ)*t-k ≤ 1 := by linarith
  have hx := between hu hv (d*p.1+k*p.2) p.2
  have hy := between hu hv (d*p.2-k*p.1) (-p.1)
  dsimp [fits,scale,projected]
  push_cast at hx hy ⊢
  simp only [sub_eq_add_neg] at hx hy ⊢
  refine ⟨?_,?_,?_,?_⟩
  · nlinarith only [hx.2, mul_le_mul_of_nonneg_left h₁ hd]
  · nlinarith only [hx.1, mul_le_mul_of_nonneg_left h₂ hd]
  · nlinarith only [hy.2, mul_le_mul_of_nonneg_left h₃ hd]
  · nlinarith only [hy.1, mul_le_mul_of_nonneg_left h₄ hd]

def slopeCheck (ps : List Pt) (D q num k : ℤ) : Bool :=
  check q (num*(D^2+max (k^2) ((k+1)^2))) none none (ps.map (projected D k))

theorem slope_sound {ps : List Pt} {D q num k : ℤ} (hd : 0 < D) (hq : 0 ≤ q)
    (hn : 0 ≤ num) {A B : RB} (ha : good A) (hb : good B) {t : ℝ}
    (hk : (k:ℝ) ≤ D*t) (hl : D*t ≤ (k:ℝ)+1)
    (hc : ∀ p ∈ ps, inside A t p.1 p.2 ∨ inside B t p.1 p.2)
    (hs : slopeCheck ps D q num k = true) :
    (num:ℝ)*(1+t^2) < q*(vol A + vol B) := by
  have hd' : (0:ℝ) < D := by exact_mod_cast hd
  have sc (r : RB) (h : good r) : good (scale D r) := by
    exact ⟨mul_le_mul_of_nonneg_left h.1 hd'.le, mul_le_mul_of_nonneg_left h.2 hd'.le⟩
  have scaled := check_sound hq (sc A ha) (sc B hb) _ none none trivial trivial (by
    intro z hz
    rcases List.mem_map.mp hz with ⟨p,hp,rfl⟩
    exact (hc p hp).imp (proj_fits hd'.le hk hl p) (proj_fits hd'.le hk hl p)) hs
  have sqbd : ((D:ℝ)*t)^2 ≤ max ((k:ℝ)^2) (((k:ℝ)+1)^2) := by
    rcases le_total 0 ((D:ℝ)*t) with h|h
    · apply le_trans _ (le_max_right _ _)
      nlinarith only [mul_nonneg (sub_nonneg.mpr hl) (by linarith : 0 ≤ (k:ℝ)+1+D*t)]
    · apply le_trans _ (le_max_left _ _)
      nlinarith only [mul_nonneg (sub_nonneg.mpr hk) (by linarith : 0 ≤ -(k:ℝ)-D*t)]
  push_cast at scaled
  have bound := mul_le_mul_of_nonneg_left (add_le_add (le_refl ((D:ℝ)^2)) sqbd)
    (show (0:ℝ) ≤ num by exact_mod_cast hn)
  have hlarge : (D:ℝ)^2*((num:ℝ)*(1+t^2)) < (D:ℝ)^2*((q:ℝ)*(vol A+vol B)) := by
    calc
      _ = (num:ℝ) * ((D:ℝ)^2 + (D*t)^2) := by ring
      _ < (q:ℝ)*(vol (scale D A) + vol (scale D B)) := bound.trans_lt scaled
      _ = _ := by unfold vol scale; dsimp; ring
  exact lt_of_mul_lt_mul_left hlarge (sq_nonneg _)

def valid (ps : List Pt) (q n d k : ℤ) : Prop :=
  ∀ (A B : RB), good A → good B → ∀ (t : ℝ), (k:ℝ) ≤ d*t → d*t ≤ (k:ℝ)+1 →
    (∀ p ∈ ps, inside A t p.1 p.2 ∨ inside B t p.1 p.2) →
    (n:ℝ)*(1+t^2) < q*(vol A+vol B)

theorem leaf {ps : List Pt} {q n d k : ℤ} (hd : 0 < d) (hq : 0 ≤ q) (hn : 0 ≤ n)
    (hs : slopeCheck ps d q n k = true) : valid ps q n d k := by
  intro A B hA hB t hl hr hc
  exact slope_sound hd hq hn hA hB hl hr hc hs

theorem node {ps : List Pt} {q n d k : ℤ}
    (h₁ : valid ps q n (2*d) (2*k)) (h₂ : valid ps q n (2*d) (2*k+1)) :
    valid ps q n d k := by
  intro A B hA hB t hl hr hc
  by_cases h : (2:ℝ)*d*t ≤ 2*k+1
  · apply h₁ A B hA hB t _ _ hc <;> push_cast <;> linarith
  · apply h₂ A B hA hB t _ _ hc <;> push_cast <;> linarith

end RectCertificate

namespace RectCertificate
def witnesses : List Pt := [(0,512), (1792,1536), (3072,3584), (768,3328), (1794,3442), (2432,2560), (384,1920), (896,1024), (243,1403), (1386,1304), (448,768), (534,2470), (2361,3505), (2787,3128), (2147,2104), (1162,1176), (171,1139), (1589,1420), (1452,3404), (2118,3478), (312,1656), (714,920), (2292,2336), (287,676), (1029,1100), (2597,2824), (1274,1240), (459,2195), (123,963), (2028,3468), (1992,1856), (623,868), (1687,1476), (1686,3430), (1491,1364), (182,616), (1920,3456), (1119,3367), (2253,3493), (1099,1140), (1605,3421), (1218,1208), (805,972), (1330,1272), (560,832), (1272,3384), (2073,3473), (225,1337), (1435,1332), (966,1064), (348,1788)]
end RectCertificate

namespace RectCertificate
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell0 : valid witnesses 100 (9501*256^2) 64 (-64) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell1 : valid witnesses 100 (9501*256^2) 64 (-63) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell2 : valid witnesses 100 (9501*256^2) 64 (-62) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell3 : valid witnesses 100 (9501*256^2) 64 (-61) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell4 : valid witnesses 100 (9501*256^2) 64 (-60) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell5 : valid witnesses 100 (9501*256^2) 64 (-59) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell6 : valid witnesses 100 (9501*256^2) 64 (-58) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell7 : valid witnesses 100 (9501*256^2) 64 (-57) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell8 : valid witnesses 100 (9501*256^2) 64 (-56) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell9 : valid witnesses 100 (9501*256^2) 64 (-55) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell10 : valid witnesses 100 (9501*256^2) 64 (-54) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell11 : valid witnesses 100 (9501*256^2) 64 (-53) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
end RectCertificate

namespace RectCertificate
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell12 : valid witnesses 100 (9501*256^2) 64 (-52) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell13 : valid witnesses 100 (9501*256^2) 64 (-51) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell14 : valid witnesses 100 (9501*256^2) 128 (-100) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell15 : valid witnesses 100 (9501*256^2) 128 (-99) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell16 : valid witnesses 100 (9501*256^2) 128 (-98) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell17 : valid witnesses 100 (9501*256^2) 128 (-97) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell18 : valid witnesses 100 (9501*256^2) 64 (-48) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell19 : valid witnesses 100 (9501*256^2) 128 (-94) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell20 : valid witnesses 100 (9501*256^2) 128 (-93) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell21 : valid witnesses 100 (9501*256^2) 128 (-92) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell22 : valid witnesses 100 (9501*256^2) 128 (-91) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell23 : valid witnesses 100 (9501*256^2) 128 (-90) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
end RectCertificate

namespace RectCertificate
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell24 : valid witnesses 100 (9501*256^2) 128 (-89) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell25 : valid witnesses 100 (9501*256^2) 128 (-88) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell26 : valid witnesses 100 (9501*256^2) 256 (-174) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell27 : valid witnesses 100 (9501*256^2) 256 (-173) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell28 : valid witnesses 100 (9501*256^2) 256 (-172) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell29 : valid witnesses 100 (9501*256^2) 256 (-171) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell30 : valid witnesses 100 (9501*256^2) 256 (-170) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell31 : valid witnesses 100 (9501*256^2) 256 (-169) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell32 : valid witnesses 100 (9501*256^2) 256 (-168) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell33 : valid witnesses 100 (9501*256^2) 256 (-167) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell34 : valid witnesses 100 (9501*256^2) 256 (-166) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell35 : valid witnesses 100 (9501*256^2) 256 (-165) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
end RectCertificate

namespace RectCertificate
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell36 : valid witnesses 100 (9501*256^2) 128 (-82) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell37 : valid witnesses 100 (9501*256^2) 128 (-81) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell38 : valid witnesses 100 (9501*256^2) 256 (-160) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell39 : valid witnesses 100 (9501*256^2) 256 (-159) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell40 : valid witnesses 100 (9501*256^2) 128 (-79) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell41 : valid witnesses 100 (9501*256^2) 128 (-78) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell42 : valid witnesses 100 (9501*256^2) 128 (-77) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell43 : valid witnesses 100 (9501*256^2) 128 (-76) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell44 : valid witnesses 100 (9501*256^2) 128 (-75) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell45 : valid witnesses 100 (9501*256^2) 128 (-74) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell46 : valid witnesses 100 (9501*256^2) 128 (-73) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell47 : valid witnesses 100 (9501*256^2) 128 (-72) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
end RectCertificate

namespace RectCertificate
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell48 : valid witnesses 100 (9501*256^2) 128 (-71) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell49 : valid witnesses 100 (9501*256^2) 128 (-70) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell50 : valid witnesses 100 (9501*256^2) 128 (-69) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell51 : valid witnesses 100 (9501*256^2) 128 (-68) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell52 : valid witnesses 100 (9501*256^2) 128 (-67) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell53 : valid witnesses 100 (9501*256^2) 128 (-66) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell54 : valid witnesses 100 (9501*256^2) 128 (-65) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell55 : valid witnesses 100 (9501*256^2) 128 (-64) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell56 : valid witnesses 100 (9501*256^2) 128 (-63) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell57 : valid witnesses 100 (9501*256^2) 128 (-62) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell58 : valid witnesses 100 (9501*256^2) 128 (-61) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell59 : valid witnesses 100 (9501*256^2) 128 (-60) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
end RectCertificate

namespace RectCertificate
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell60 : valid witnesses 100 (9501*256^2) 128 (-59) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell61 : valid witnesses 100 (9501*256^2) 128 (-58) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell62 : valid witnesses 100 (9501*256^2) 128 (-57) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell63 : valid witnesses 100 (9501*256^2) 128 (-56) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell64 : valid witnesses 100 (9501*256^2) 128 (-55) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell65 : valid witnesses 100 (9501*256^2) 128 (-54) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell66 : valid witnesses 100 (9501*256^2) 128 (-53) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell67 : valid witnesses 100 (9501*256^2) 128 (-52) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell68 : valid witnesses 100 (9501*256^2) 128 (-51) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell69 : valid witnesses 100 (9501*256^2) 128 (-50) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell70 : valid witnesses 100 (9501*256^2) 128 (-49) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell71 : valid witnesses 100 (9501*256^2) 128 (-48) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
end RectCertificate

namespace RectCertificate
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell72 : valid witnesses 100 (9501*256^2) 128 (-47) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell73 : valid witnesses 100 (9501*256^2) 128 (-46) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell74 : valid witnesses 100 (9501*256^2) 128 (-45) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell75 : valid witnesses 100 (9501*256^2) 128 (-44) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell76 : valid witnesses 100 (9501*256^2) 128 (-43) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell77 : valid witnesses 100 (9501*256^2) 256 (-84) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell78 : valid witnesses 100 (9501*256^2) 256 (-83) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell79 : valid witnesses 100 (9501*256^2) 256 (-82) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell80 : valid witnesses 100 (9501*256^2) 256 (-81) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell81 : valid witnesses 100 (9501*256^2) 256 (-80) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell82 : valid witnesses 100 (9501*256^2) 256 (-79) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell83 : valid witnesses 100 (9501*256^2) 256 (-78) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
end RectCertificate

namespace RectCertificate
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell84 : valid witnesses 100 (9501*256^2) 256 (-77) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell85 : valid witnesses 100 (9501*256^2) 256 (-76) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell86 : valid witnesses 100 (9501*256^2) 256 (-75) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell87 : valid witnesses 100 (9501*256^2) 256 (-74) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell88 : valid witnesses 100 (9501*256^2) 256 (-73) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell89 : valid witnesses 100 (9501*256^2) 256 (-72) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell90 : valid witnesses 100 (9501*256^2) 256 (-71) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell91 : valid witnesses 100 (9501*256^2) 256 (-70) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell92 : valid witnesses 100 (9501*256^2) 256 (-69) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell93 : valid witnesses 100 (9501*256^2) 128 (-34) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell94 : valid witnesses 100 (9501*256^2) 128 (-33) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell95 : valid witnesses 100 (9501*256^2) 128 (-32) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
end RectCertificate

namespace RectCertificate
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell96 : valid witnesses 100 (9501*256^2) 128 (-31) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell97 : valid witnesses 100 (9501*256^2) 64 (-15) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell98 : valid witnesses 100 (9501*256^2) 64 (-14) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell99 : valid witnesses 100 (9501*256^2) 64 (-13) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell100 : valid witnesses 100 (9501*256^2) 32 (-6) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell101 : valid witnesses 100 (9501*256^2) 32 (-5) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell102 : valid witnesses 100 (9501*256^2) 32 (-4) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell103 : valid witnesses 100 (9501*256^2) 32 (-3) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell104 : valid witnesses 100 (9501*256^2) 32 (-2) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell105 : valid witnesses 100 (9501*256^2) 32 (-1) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell106 : valid witnesses 100 (9501*256^2) 64 (0) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell107 : valid witnesses 100 (9501*256^2) 64 (1) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
end RectCertificate

namespace RectCertificate
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell108 : valid witnesses 100 (9501*256^2) 64 (2) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell109 : valid witnesses 100 (9501*256^2) 64 (3) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell110 : valid witnesses 100 (9501*256^2) 64 (4) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell111 : valid witnesses 100 (9501*256^2) 128 (10) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell112 : valid witnesses 100 (9501*256^2) 128 (11) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell113 : valid witnesses 100 (9501*256^2) 256 (24) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell114 : valid witnesses 100 (9501*256^2) 256 (25) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell115 : valid witnesses 100 (9501*256^2) 256 (26) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell116 : valid witnesses 100 (9501*256^2) 256 (27) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell117 : valid witnesses 100 (9501*256^2) 128 (14) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell118 : valid witnesses 100 (9501*256^2) 128 (15) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell119 : valid witnesses 100 (9501*256^2) 64 (8) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
end RectCertificate

namespace RectCertificate
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell120 : valid witnesses 100 (9501*256^2) 64 (9) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell121 : valid witnesses 100 (9501*256^2) 32 (5) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell122 : valid witnesses 100 (9501*256^2) 64 (12) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell123 : valid witnesses 100 (9501*256^2) 64 (13) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell124 : valid witnesses 100 (9501*256^2) 32 (7) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell125 : valid witnesses 100 (9501*256^2) 32 (8) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell126 : valid witnesses 100 (9501*256^2) 32 (9) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell127 : valid witnesses 100 (9501*256^2) 32 (10) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell128 : valid witnesses 100 (9501*256^2) 32 (11) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell129 : valid witnesses 100 (9501*256^2) 32 (12) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell130 : valid witnesses 100 (9501*256^2) 32 (13) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell131 : valid witnesses 100 (9501*256^2) 32 (14) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
end RectCertificate

namespace RectCertificate
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell132 : valid witnesses 100 (9501*256^2) 32 (15) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell133 : valid witnesses 100 (9501*256^2) 64 (32) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell134 : valid witnesses 100 (9501*256^2) 64 (33) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell135 : valid witnesses 100 (9501*256^2) 64 (34) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell136 : valid witnesses 100 (9501*256^2) 64 (35) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell137 : valid witnesses 100 (9501*256^2) 64 (36) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell138 : valid witnesses 100 (9501*256^2) 64 (37) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell139 : valid witnesses 100 (9501*256^2) 128 (76) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell140 : valid witnesses 100 (9501*256^2) 128 (77) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell141 : valid witnesses 100 (9501*256^2) 128 (78) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell142 : valid witnesses 100 (9501*256^2) 128 (79) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell143 : valid witnesses 100 (9501*256^2) 128 (80) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
end RectCertificate

namespace RectCertificate
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell144 : valid witnesses 100 (9501*256^2) 128 (81) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell145 : valid witnesses 100 (9501*256^2) 64 (41) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell146 : valid witnesses 100 (9501*256^2) 64 (42) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell147 : valid witnesses 100 (9501*256^2) 64 (43) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell148 : valid witnesses 100 (9501*256^2) 64 (44) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell149 : valid witnesses 100 (9501*256^2) 64 (45) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell150 : valid witnesses 100 (9501*256^2) 32 (23) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell151 : valid witnesses 100 (9501*256^2) 64 (48) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell152 : valid witnesses 100 (9501*256^2) 64 (49) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell153 : valid witnesses 100 (9501*256^2) 64 (50) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell154 : valid witnesses 100 (9501*256^2) 64 (51) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell155 : valid witnesses 100 (9501*256^2) 32 (26) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
end RectCertificate

namespace RectCertificate
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell156 : valid witnesses 100 (9501*256^2) 32 (27) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell157 : valid witnesses 100 (9501*256^2) 32 (28) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell158 : valid witnesses 100 (9501*256^2) 32 (29) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell159 : valid witnesses 100 (9501*256^2) 32 (30) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell160 : valid witnesses 100 (9501*256^2) 64 (62) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cell161 : valid witnesses 100 (9501*256^2) 64 (63) := leaf (by decide) (by decide) (by decide) (by decide +kernel)
end RectCertificate

namespace RectCertificate
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem lowerNeg : valid witnesses 100 (9501*256^2) 1 (-1) := (@node witnesses 100 (9501*256^2) 1 (-1) (@node witnesses 100 (9501*256^2) 2 (-2) (@node witnesses 100 (9501*256^2) 4 (-4) (@node witnesses 100 (9501*256^2) 8 (-8) (@node witnesses 100 (9501*256^2) 16 (-16) (@node witnesses 100 (9501*256^2) 32 (-32) cell0 cell1) (@node witnesses 100 (9501*256^2) 32 (-31) cell2 cell3)) (@node witnesses 100 (9501*256^2) 16 (-15) (@node witnesses 100 (9501*256^2) 32 (-30) cell4 cell5) (@node witnesses 100 (9501*256^2) 32 (-29) cell6 cell7))) (@node witnesses 100 (9501*256^2) 8 (-7) (@node witnesses 100 (9501*256^2) 16 (-14) (@node witnesses 100 (9501*256^2) 32 (-28) cell8 cell9) (@node witnesses 100 (9501*256^2) 32 (-27) cell10 cell11)) (@node witnesses 100 (9501*256^2) 16 (-13) (@node witnesses 100 (9501*256^2) 32 (-26) cell12 cell13) (@node witnesses 100 (9501*256^2) 32 (-25) (@node witnesses 100 (9501*256^2) 64 (-50) cell14 cell15) (@node witnesses 100 (9501*256^2) 64 (-49) cell16 cell17))))) (@node witnesses 100 (9501*256^2) 4 (-3) (@node witnesses 100 (9501*256^2) 8 (-6) (@node witnesses 100 (9501*256^2) 16 (-12) (@node witnesses 100 (9501*256^2) 32 (-24) cell18 (@node witnesses 100 (9501*256^2) 64 (-47) cell19 cell20)) (@node witnesses 100 (9501*256^2) 32 (-23) (@node witnesses 100 (9501*256^2) 64 (-46) cell21 cell22) (@node witnesses 100 (9501*256^2) 64 (-45) cell23 cell24))) (@node witnesses 100 (9501*256^2) 16 (-11) (@node witnesses 100 (9501*256^2) 32 (-22) (@node witnesses 100 (9501*256^2) 64 (-44) cell25 (@node witnesses 100 (9501*256^2) 128 (-87) cell26 cell27)) (@node witnesses 100 (9501*256^2) 64 (-43) (@node witnesses 100 (9501*256^2) 128 (-86) cell28 cell29) (@node witnesses 100 (9501*256^2) 128 (-85) cell30 cell31))) (@node witnesses 100 (9501*256^2) 32 (-21) (@node witnesses 100 (9501*256^2) 64 (-42) (@node witnesses 100 (9501*256^2) 128 (-84) cell32 cell33) (@node witnesses 100 (9501*256^2) 128 (-83) cell34 cell35)) (@node witnesses 100 (9501*256^2) 64 (-41) cell36 cell37)))) (@node witnesses 100 (9501*256^2) 8 (-5) (@node witnesses 100 (9501*256^2) 16 (-10) (@node witnesses 100 (9501*256^2) 32 (-20) (@node witnesses 100 (9501*256^2) 64 (-40) (@node witnesses 100 (9501*256^2) 128 (-80) cell38 cell39) cell40) (@node witnesses 100 (9501*256^2) 64 (-39) cell41 cell42)) (@node witnesses 100 (9501*256^2) 32 (-19) (@node witnesses 100 (9501*256^2) 64 (-38) cell43 cell44) (@node witnesses 100 (9501*256^2) 64 (-37) cell45 cell46))) (@node witnesses 100 (9501*256^2) 16 (-9) (@node witnesses 100 (9501*256^2) 32 (-18) (@node witnesses 100 (9501*256^2) 64 (-36) cell47 cell48) (@node witnesses 100 (9501*256^2) 64 (-35) cell49 cell50)) (@node witnesses 100 (9501*256^2) 32 (-17) (@node witnesses 100 (9501*256^2) 64 (-34) cell51 cell52) (@node witnesses 100 (9501*256^2) 64 (-33) cell53 cell54)))))) (@node witnesses 100 (9501*256^2) 2 (-1) (@node witnesses 100 (9501*256^2) 4 (-2) (@node witnesses 100 (9501*256^2) 8 (-4) (@node witnesses 100 (9501*256^2) 16 (-8) (@node witnesses 100 (9501*256^2) 32 (-16) (@node witnesses 100 (9501*256^2) 64 (-32) cell55 cell56) (@node witnesses 100 (9501*256^2) 64 (-31) cell57 cell58)) (@node witnesses 100 (9501*256^2) 32 (-15) (@node witnesses 100 (9501*256^2) 64 (-30) cell59 cell60) (@node witnesses 100 (9501*256^2) 64 (-29) cell61 cell62))) (@node witnesses 100 (9501*256^2) 16 (-7) (@node witnesses 100 (9501*256^2) 32 (-14) (@node witnesses 100 (9501*256^2) 64 (-28) cell63 cell64) (@node witnesses 100 (9501*256^2) 64 (-27) cell65 cell66)) (@node witnesses 100 (9501*256^2) 32 (-13) (@node witnesses 100 (9501*256^2) 64 (-26) cell67 cell68) (@node witnesses 100 (9501*256^2) 64 (-25) cell69 cell70)))) (@node witnesses 100 (9501*256^2) 8 (-3) (@node witnesses 100 (9501*256^2) 16 (-6) (@node witnesses 100 (9501*256^2) 32 (-12) (@node witnesses 100 (9501*256^2) 64 (-24) cell71 cell72) (@node witnesses 100 (9501*256^2) 64 (-23) cell73 cell74)) (@node witnesses 100 (9501*256^2) 32 (-11) (@node witnesses 100 (9501*256^2) 64 (-22) cell75 cell76) (@node witnesses 100 (9501*256^2) 64 (-21) (@node witnesses 100 (9501*256^2) 128 (-42) cell77 cell78) (@node witnesses 100 (9501*256^2) 128 (-41) cell79 cell80)))) (@node witnesses 100 (9501*256^2) 16 (-5) (@node witnesses 100 (9501*256^2) 32 (-10) (@node witnesses 100 (9501*256^2) 64 (-20) (@node witnesses 100 (9501*256^2) 128 (-40) cell81 cell82) (@node witnesses 100 (9501*256^2) 128 (-39) cell83 cell84)) (@node witnesses 100 (9501*256^2) 64 (-19) (@node witnesses 100 (9501*256^2) 128 (-38) cell85 cell86) (@node witnesses 100 (9501*256^2) 128 (-37) cell87 cell88))) (@node witnesses 100 (9501*256^2) 32 (-9) (@node witnesses 100 (9501*256^2) 64 (-18) (@node witnesses 100 (9501*256^2) 128 (-36) cell89 cell90) (@node witnesses 100 (9501*256^2) 128 (-35) cell91 cell92)) (@node witnesses 100 (9501*256^2) 64 (-17) cell93 cell94))))) (@node witnesses 100 (9501*256^2) 4 (-1) (@node witnesses 100 (9501*256^2) 8 (-2) (@node witnesses 100 (9501*256^2) 16 (-4) (@node witnesses 100 (9501*256^2) 32 (-8) (@node witnesses 100 (9501*256^2) 64 (-16) cell95 cell96) cell97) (@node witnesses 100 (9501*256^2) 32 (-7) cell98 cell99)) (@node witnesses 100 (9501*256^2) 16 (-3) cell100 cell101)) (@node witnesses 100 (9501*256^2) 8 (-1) (@node witnesses 100 (9501*256^2) 16 (-2) cell102 cell103) (@node witnesses 100 (9501*256^2) 16 (-1) cell104 cell105)))))
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem lowerPos : valid witnesses 100 (9501*256^2) 1 0 := (@node witnesses 100 (9501*256^2) 1 (0) (@node witnesses 100 (9501*256^2) 2 (0) (@node witnesses 100 (9501*256^2) 4 (0) (@node witnesses 100 (9501*256^2) 8 (0) (@node witnesses 100 (9501*256^2) 16 (0) (@node witnesses 100 (9501*256^2) 32 (0) cell106 cell107) (@node witnesses 100 (9501*256^2) 32 (1) cell108 cell109)) (@node witnesses 100 (9501*256^2) 16 (1) (@node witnesses 100 (9501*256^2) 32 (2) cell110 (@node witnesses 100 (9501*256^2) 64 (5) cell111 cell112)) (@node witnesses 100 (9501*256^2) 32 (3) (@node witnesses 100 (9501*256^2) 64 (6) (@node witnesses 100 (9501*256^2) 128 (12) cell113 cell114) (@node witnesses 100 (9501*256^2) 128 (13) cell115 cell116)) (@node witnesses 100 (9501*256^2) 64 (7) cell117 cell118)))) (@node witnesses 100 (9501*256^2) 8 (1) (@node witnesses 100 (9501*256^2) 16 (2) (@node witnesses 100 (9501*256^2) 32 (4) cell119 cell120) cell121) (@node witnesses 100 (9501*256^2) 16 (3) (@node witnesses 100 (9501*256^2) 32 (6) cell122 cell123) cell124))) (@node witnesses 100 (9501*256^2) 4 (1) (@node witnesses 100 (9501*256^2) 8 (2) (@node witnesses 100 (9501*256^2) 16 (4) cell125 cell126) (@node witnesses 100 (9501*256^2) 16 (5) cell127 cell128)) (@node witnesses 100 (9501*256^2) 8 (3) (@node witnesses 100 (9501*256^2) 16 (6) cell129 cell130) (@node witnesses 100 (9501*256^2) 16 (7) cell131 cell132)))) (@node witnesses 100 (9501*256^2) 2 (1) (@node witnesses 100 (9501*256^2) 4 (2) (@node witnesses 100 (9501*256^2) 8 (4) (@node witnesses 100 (9501*256^2) 16 (8) (@node witnesses 100 (9501*256^2) 32 (16) cell133 cell134) (@node witnesses 100 (9501*256^2) 32 (17) cell135 cell136)) (@node witnesses 100 (9501*256^2) 16 (9) (@node witnesses 100 (9501*256^2) 32 (18) cell137 cell138) (@node witnesses 100 (9501*256^2) 32 (19) (@node witnesses 100 (9501*256^2) 64 (38) cell139 cell140) (@node witnesses 100 (9501*256^2) 64 (39) cell141 cell142)))) (@node witnesses 100 (9501*256^2) 8 (5) (@node witnesses 100 (9501*256^2) 16 (10) (@node witnesses 100 (9501*256^2) 32 (20) (@node witnesses 100 (9501*256^2) 64 (40) cell143 cell144) cell145) (@node witnesses 100 (9501*256^2) 32 (21) cell146 cell147)) (@node witnesses 100 (9501*256^2) 16 (11) (@node witnesses 100 (9501*256^2) 32 (22) cell148 cell149) cell150))) (@node witnesses 100 (9501*256^2) 4 (3) (@node witnesses 100 (9501*256^2) 8 (6) (@node witnesses 100 (9501*256^2) 16 (12) (@node witnesses 100 (9501*256^2) 32 (24) cell151 cell152) (@node witnesses 100 (9501*256^2) 32 (25) cell153 cell154)) (@node witnesses 100 (9501*256^2) 16 (13) cell155 cell156)) (@node witnesses 100 (9501*256^2) 8 (7) (@node witnesses 100 (9501*256^2) 16 (14) cell157 cell158) (@node witnesses 100 (9501*256^2) 16 (15) cell159 (@node witnesses 100 (9501*256^2) 32 (31) cell160 cell161))))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem common_lower {A B : RB} (ha : good A) (hb : good B) {t : ℝ}
    (ht₀ : -1 ≤ t) (ht₁ : t ≤ 1)
    (hc : ∀ p ∈ witnesses, inside A t ((p.1:ℝ)/256) ((p.2:ℝ)/256) ∨
      inside B t ((p.1:ℝ)/256) ((p.2:ℝ)/256)) :
    (95.01:ℝ)*(1+t^2) < vol A + vol B := by
  let S : RB → RB := scale 256
  have sg (r : RB) (h : good r) : good (S r) :=
    ⟨mul_le_mul_of_nonneg_left h.1 (by norm_num), mul_le_mul_of_nonneg_left h.2 (by norm_num)⟩
  have si (r : RB) (p : Pt) (h : inside r t ((p.1:ℝ)/256) ((p.2:ℝ)/256)) :
      inside (S r) t p.1 p.2 := by
    rcases h with ⟨h₁,h₂,h₃,h₄⟩
    refine ⟨?_,?_,?_,?_⟩ <;> dsimp [S,scale] <;> linarith
  have hc' : ∀ p ∈ witnesses, inside (S A) t p.1 p.2 ∨ inside (S B) t p.1 p.2 :=
    fun p hp => (hc p hp).imp (si A p) (si B p)
  have hlarge : ((9501*256^2:ℤ):ℝ) * (1+t^2) < 100*(vol (S A)+vol (S B)) := by
    by_cases h : t ≤ 0
    · apply lowerNeg (S A) (S B) (sg A ha) (sg B hb) t _ _ hc' <;> norm_num <;> assumption
    · apply lowerPos (S A) (S B) (sg A ha) (sg B hb) t _ _ hc' <;> norm_num <;> linarith
  norm_num [S,scale,vol] at hlarge ⊢
  linarith
end RectCertificate

namespace Mixed337315
open OMA.S_mo_337315

def half (a b c : ℝ) : Set (ℝ × ℝ) := {p | a*p.1+b*p.2 ≤ c}

def box : Set (ℝ × ℝ) := Set.Icc (0,2) (12,14)
def body : Set (ℝ × ℝ) := (((box ∩ half 4 (-7) (-14)) ∩ half 8 (-5) 26)
    ∩ half (-1) 9 114) ∩ half (-11) 3 6

theorem half_closed (a b c : ℝ) : IsClosed (half a b c) := by
  apply isClosed_le _ continuous_const
  fun_prop

theorem half_convex (a b c : ℝ) : Convex ℝ (half a b c) := by
  intro x hx y hy u v hu hv huv
  change a*x.1+b*x.2 ≤ c at hx
  change a*y.1+b*y.2 ≤ c at hy
  change a*(u*x.1+v*y.1)+b*(u*x.2+v*y.2) ≤ c
  calc
    _ = u*(a*x.1+b*x.2)+v*(a*y.1+b*y.2) := by ring
    _ ≤ u*c+v*c := add_le_add (mul_le_mul_of_nonneg_left hx hu) (mul_le_mul_of_nonneg_left hy hv)
    _ = c := by rw [← add_mul, huv, one_mul]

theorem body_compact : IsCompact body := by
  apply (isCompact_Icc : IsCompact box).of_isClosed_subset
  · exact (((isClosed_Icc.inter (half_closed _ _ _)).inter (half_closed _ _ _)).inter
      (half_closed _ _ _)).inter (half_closed _ _ _)
  · intro p hp
    exact hp.1.1.1.1

theorem box_convex : Convex ℝ box := by
  intro x hx y hy u v hu hv huv
  obtain ⟨⟨hx₀,hx₁⟩,hx₂,hx₃⟩ := hx
  obtain ⟨⟨hy₀,hy₁⟩,hy₂,hy₃⟩ := hy
  change 0 ≤ x.1 at hx₀
  change 2 ≤ x.2 at hx₁
  change x.1 ≤ 12 at hx₂
  change x.2 ≤ 14 at hx₃
  change 0 ≤ y.1 at hy₀
  change 2 ≤ y.2 at hy₁
  change y.1 ≤ 12 at hy₂
  change y.2 ≤ 14 at hy₃
  refine ⟨⟨?_,?_⟩,?_,?_⟩
  · change 0 ≤ u*x.1+v*y.1
    exact add_nonneg (mul_nonneg hu hx₀) (mul_nonneg hv hy₀)
  · change 2 ≤ u*x.2+v*y.2
    nlinarith [mul_nonneg hu (sub_nonneg.mpr hx₁), mul_nonneg hv (sub_nonneg.mpr hy₁)]
  · change u*x.1+v*y.1 ≤ 12
    nlinarith [mul_nonneg hu (sub_nonneg.mpr hx₂), mul_nonneg hv (sub_nonneg.mpr hy₂)]
  · change u*x.2+v*y.2 ≤ 14
    nlinarith [mul_nonneg hu (sub_nonneg.mpr hx₃), mul_nonneg hv (sub_nonneg.mpr hy₃)]

theorem body_convex : Convex ℝ body :=
  (((box_convex.inter (half_convex _ _ _)).inter (half_convex _ _ _)).inter
    (half_convex _ _ _)).inter (half_convex _ _ _)

theorem body_open_part : (interior body).Nonempty := by
  let U := Set.Ioo (3:ℝ) 4 ×ˢ Set.Ioo (6:ℝ) 7
  have ho : IsOpen U := isOpen_Ioo.prod isOpen_Ioo
  have hsub : U ⊆ body := by
    rintro ⟨x,y⟩ ⟨⟨hx,hx'⟩,hy,hy'⟩
    refine ⟨⟨⟨⟨⟨⟨?_,?_⟩,⟨?_,?_⟩⟩,?_⟩,?_⟩,?_⟩,?_⟩ <;>
      simp only [half, Set.mem_ofPred_eq] <;> linarith
  exact ⟨(7/2,13/2), interior_maximal hsub ho (by norm_num [U])⟩

noncomputable def angled : Fin 2 → Rectangle := ![
  ⟨-5/8,-307/256,13/4,811/104,43/2⟩,
  ⟨-3/11,-6/11,39/11,2,247/16⟩]

theorem angled_covers : Covers body angled := by
  constructor
  · intro i
    fin_cases i <;> norm_num [angled, Rectangle.valid, Matrix.cons_val_zero, Matrix.cons_val_one]
  · rintro ⟨x,y⟩ ⟨⟨⟨⟨_, h₁⟩, h₂⟩, h₃⟩, h₄⟩
    change 4*x+-7*y ≤ -14 at h₁
    change 8*x+-5*y ≤ 26 at h₂
    change -1*x+9*y ≤ 114 at h₃
    change -11*x+3*y ≤ 6 at h₄
    by_cases cut : -11*x+3*y+39 ≤ 0
    · refine ⟨0, ?_⟩
      norm_num [Rectangle.contains,angled] <;>
        refine ⟨?_,?_,?_,?_⟩ <;> linarith
    · refine ⟨1, ?_⟩
      norm_num [Rectangle.contains,angled] <;>
        refine ⟨?_,?_,?_,?_⟩ <;> linarith

theorem angled_area : (∑ i, (angled i).area) = (109920:ℝ)/1157 := by
  norm_num [Fin.sum_univ_two, angled, Rectangle.area]

end Mixed337315

namespace Mixed337315
open RectCertificate

private def inScaledBody (p : Pt) : Bool :=
  decide (0 ≤ p.1 ∧ 512 ≤ p.2 ∧ p.1 ≤ 3072 ∧ p.2 ≤ 3584 ∧
    4*p.1-7*p.2 ≤ -3584 ∧ 8*p.1-5*p.2 ≤ 6656 ∧
    -p.1+9*p.2 ≤ 29184 ∧ -11*p.1+3*p.2 ≤ 1536)

set_option maxRecDepth 3000 in
private theorem all_scaled : witnesses.all inScaledBody = true := by decide +kernel

theorem witness_mem {p : Pt} (hp : p ∈ witnesses) :
    ((p.1 : ℝ)/256, (p.2 : ℝ)/256) ∈ body := by
  have h := List.all_eq_true.mp all_scaled p hp
  simp only [inScaledBody, decide_eq_true_eq] at h
  rcases h with ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩
  have q0 : (0:ℝ) ≤ p.1 := by exact_mod_cast h0
  have q1 : (512:ℝ) ≤ p.2 := by exact_mod_cast h1
  have q2 : (p.1:ℝ) ≤ 3072 := by exact_mod_cast h2
  have q3 : (p.2:ℝ) ≤ 3584 := by exact_mod_cast h3
  have q4 : 4*(p.1:ℝ)-7*(p.2:ℝ) ≤ -3584 := by exact_mod_cast h4
  have q5 : 8*(p.1:ℝ)-5*(p.2:ℝ) ≤ 6656 := by exact_mod_cast h5
  have q6 : -(p.1:ℝ)+9*(p.2:ℝ) ≤ 29184 := by exact_mod_cast h6
  have q7 : -11*(p.1:ℝ)+3*(p.2:ℝ) ≤ 1536 := by exact_mod_cast h7
  refine ⟨⟨⟨⟨⟨⟨?_,?_⟩,⟨?_,?_⟩⟩,?_⟩,?_⟩,?_⟩,?_⟩ <;>
    simp only [half, Set.mem_ofPred_eq] <;> linarith
end Mixed337315

open OMA.S_mo_337315
open Mixed337315

private def measuredBounds (r : Rectangle) : RectCertificate.RB :=
  ⟨r.left,r.right,r.bottom,r.top⟩

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_337315.main) := by
  intro claim
  obtain ⟨r,hr,hparallel,_hlong,hbest⟩ := claim body body_compact body_convex body_open_part 2 (by decide)
  let t := (r 0).slope
  have heq : (r 1).slope = (r 0).slope := hparallel 1 0
  have gr (i : Fin 2) : RectCertificate.good (measuredBounds (r i)) :=
    ⟨(hr.1 i).2.2.1.le, (hr.1 i).2.2.2.le⟩
  have hc : ∀ p ∈ RectCertificate.witnesses,
      RectCertificate.inside (measuredBounds (r 0)) t ((p.1:ℝ)/256) ((p.2:ℝ)/256) ∨
      RectCertificate.inside (measuredBounds (r 1)) t ((p.1:ℝ)/256) ((p.2:ℝ)/256) := by
    intro p hp
    obtain ⟨i, hi⟩ := hr.2 _ (Mixed337315.witness_mem hp)
    fin_cases i
    · exact Or.inl hi
    · right
      change (r 1).contains ((p.1:ℝ)/256, (p.2:ℝ)/256) at hi
      simpa only [Rectangle.contains, heq, t, measuredBounds, RectCertificate.inside] using hi
  have hlow := RectCertificate.common_lower (gr 0) (gr 1) (hr.1 0).1 (hr.1 0).2.1 hc
  have htop := hbest angled angled_covers
  rw [angled_area, Fin.sum_univ_two] at htop
  unfold Rectangle.area at htop
  rw [heq, ← add_div] at htop
  have hpos : 0 < 1+(r 0).slope^2 := by positivity
  have hbound := (div_le_iff₀ hpos).mp htop
  dsimp [t,measuredBounds,RectCertificate.vol] at hlow
  nlinarith [sq_nonneg (r 0).slope]
