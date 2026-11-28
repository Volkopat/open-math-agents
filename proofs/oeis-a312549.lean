import OMAStatements.S_oeis_a312549
import Mathlib

/-!
Proof of the conjectured recurrence and generating function for A312549.

Method: an explicit distance certificate. Every vertex outside the origin cell lies on one of the
rays through the vertices of the growth polygon or in one of the open cones between them, and is
written as base + k T + j U with a base from a finite list. The certificate gives the distance of
each code as v + L (k + j). A Boolean checker, evaluated by the kernel, verifies that every
neighbour of a coded vertex has a code of value at most one more, that every coded vertex other
than the base vertex has a neighbour of value exactly one less, and that codes are injective. So
the ball of radius n is the image of the codes of value at most n, and the coordination sequence
is a sum of explicit quasi-linear counts, which satisfies both conjectures.
The certificate data was produced by a script written with the help of an AI agent (Claude Code).
-/

namespace GalCert

/-- A target code given by affine forms in two free variables `k1 j1`. -/
structure Tgt where
  r : ℕ
  b : ℕ
  ka : ℕ
  kb : ℕ
  kc : ℕ
  ja : ℕ
  jb : ℕ
  jc : ℕ
  e : ℕ

def Tgt.dflt : Tgt := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩

structure Base (m : ℕ) where
  x : ℤ
  y : ℤ
  i : Fin m
  v : ℕ
  out : List (List Tgt)
  pred : List Tgt

structure Region (m : ℕ) where
  kind : ℕ
  Tx : ℤ
  Ty : ℤ
  Ux : ℤ
  Uy : ℤ
  tests : List (ℤ × ℤ × ℤ)
  px : ℤ
  py : ℤ
  pc : ℤ
  pM : ℤ
  qx : ℤ
  qy : ℤ
  qc : ℤ
  qM : ℤ
  bases : List (Base m)

structure Cfg (m : ℕ) where
  adj : Fin m → List (ℤ × ℤ × Fin m)
  x0 : ℤ × ℤ × Fin m
  L : ℕ
  regs : List (Region m)
  certs : List (List (List (Bool × ℕ × ℕ)))
  r0 : ℕ
  b0 : ℕ

variable {m : ℕ} [NeZero m]

def Base.dflt : Base m := ⟨0, 0, 0, 0, [], []⟩
def Region.dflt : Region m := ⟨0, 0, 0, 0, 0, [], 0, 0, 0, 0, 0, 0, 0, 0, []⟩
def edflt : ℤ × ℤ × Fin m := (0, 0, 0)

def nbrs (adj : Fin m → List (ℤ × ℤ × Fin m)) (v : ℤ × ℤ × Fin m) : Finset (ℤ × ℤ × Fin m) :=
  ((adj v.2.2).map (fun d => (v.1 + d.1, v.2.1 + d.2.1, d.2.2))).toFinset

def ball (adj : Fin m → List (ℤ × ℤ × Fin m)) (x0 : ℤ × ℤ × Fin m) : ℕ → Finset (ℤ × ℤ × Fin m)
  | 0 => {x0}
  | n + 1 => ball adj x0 n ∪ (ball adj x0 n).biUnion (nbrs adj)

def sh (p d : ℤ × ℤ × Fin m) : ℤ × ℤ × Fin m := (p.1 + d.1, p.2.1 + d.2.1, d.2.2)

namespace Cfg
variable (C : Cfg m)

def reg (r : ℕ) : Region m := C.regs.getD r Region.dflt
def bas (r b : ℕ) : Base m := (C.reg r).bases.getD b Base.dflt

def dec (r b k j : ℕ) : ℤ × ℤ × Fin m :=
  ((C.bas r b).x + (k : ℤ) * (C.reg r).Tx + (j : ℤ) * (C.reg r).Ux,
   (C.bas r b).y + (k : ℤ) * (C.reg r).Ty + (j : ℤ) * (C.reg r).Uy, (C.bas r b).i)

def val (r b k j : ℕ) : ℕ := (C.bas r b).v + C.L * (k + j)

def Valid (r b k j : ℕ) : Prop :=
  r < C.regs.length ∧ b < (C.reg r).bases.length ∧ (1 ≤ (C.reg r).kind ∨ k = 0) ∧
    (2 ≤ (C.reg r).kind ∨ j = 0)

def ncases (kind : ℕ) : ℕ := if kind = 0 then 1 else if kind = 1 then 2 else 4

/-- Closure/Lipschitz rule check for source base `B` in region `R`, edge `d`, case `(kk, jj)`. -/
def okOut (R : Region m) (B : Base m) (d : ℤ × ℤ × Fin m) (kk jj : ℕ) (t : Tgt) : Bool :=
  let R' := C.reg t.r
  let B' := C.bas t.r t.b
  decide (t.r < C.regs.length) && decide (t.b < R'.bases.length) &&
  (decide (1 ≤ R'.kind) || (t.ka == 0 && t.kb == 0 && t.kc == 0)) &&
  (decide (2 ≤ R'.kind) || (t.ja == 0 && t.jb == 0 && t.jc == 0)) &&
  decide ((t.ka : ℤ) * R'.Tx + (t.ja : ℤ) * R'.Ux = (kk : ℤ) * R.Tx) &&
  decide ((t.kb : ℤ) * R'.Tx + (t.jb : ℤ) * R'.Ux = (jj : ℤ) * R.Ux) &&
  decide (B'.x + (t.kc : ℤ) * R'.Tx + (t.jc : ℤ) * R'.Ux = B.x + d.1 + (kk : ℤ) * R.Tx + (jj : ℤ) * R.Ux) &&
  decide ((t.ka : ℤ) * R'.Ty + (t.ja : ℤ) * R'.Uy = (kk : ℤ) * R.Ty) &&
  decide ((t.kb : ℤ) * R'.Ty + (t.jb : ℤ) * R'.Uy = (jj : ℤ) * R.Uy) &&
  decide (B'.y + (t.kc : ℤ) * R'.Ty + (t.jc : ℤ) * R'.Uy = B.y + d.2.1 + (kk : ℤ) * R.Ty + (jj : ℤ) * R.Uy) &&
  decide (B'.i = d.2.2) &&
  decide (C.L * (t.ka + t.ja) ≤ C.L * kk) && decide (C.L * (t.kb + t.jb) ≤ C.L * jj) &&
  decide (B'.v + C.L * (t.kc + t.jc) ≤ B.v + C.L * (kk + jj) + 1)

/-- Descending rule check: the target code is a neighbour one step closer. -/
def okPred (R : Region m) (B : Base m) (kk jj : ℕ) (t : Tgt) : Bool :=
  let R' := C.reg t.r
  let B' := C.bas t.r t.b
  let d := (C.adj B'.i).getD t.e edflt
  decide (t.r < C.regs.length) && decide (t.b < R'.bases.length) &&
  decide (t.e < (C.adj B'.i).length) &&
  (decide (1 ≤ R'.kind) || (t.ka == 0 && t.kb == 0 && t.kc == 0)) &&
  (decide (2 ≤ R'.kind) || (t.ja == 0 && t.jb == 0 && t.jc == 0)) &&
  decide ((t.ka : ℤ) * R'.Tx + (t.ja : ℤ) * R'.Ux = (kk : ℤ) * R.Tx) &&
  decide ((t.kb : ℤ) * R'.Tx + (t.jb : ℤ) * R'.Ux = (jj : ℤ) * R.Ux) &&
  decide (B'.x + (t.kc : ℤ) * R'.Tx + (t.jc : ℤ) * R'.Ux + d.1 = B.x + (kk : ℤ) * R.Tx + (jj : ℤ) * R.Ux) &&
  decide ((t.ka : ℤ) * R'.Ty + (t.ja : ℤ) * R'.Uy = (kk : ℤ) * R.Ty) &&
  decide ((t.kb : ℤ) * R'.Ty + (t.jb : ℤ) * R'.Uy = (jj : ℤ) * R.Uy) &&
  decide (B'.y + (t.kc : ℤ) * R'.Ty + (t.jc : ℤ) * R'.Uy + d.2.1 = B.y + (kk : ℤ) * R.Ty + (jj : ℤ) * R.Uy) &&
  decide (d.2.2 = B.i) &&
  decide (C.L * (t.ka + t.ja) = C.L * kk) && decide (C.L * (t.kb + t.jb) = C.L * jj) &&
  decide (B'.v + C.L * (t.kc + t.jc) + 1 = B.v + C.L * (kk + jj))

def tst (f : ℤ × ℤ × ℤ) (x y : ℤ) : Prop := f.2.2 ≤ f.1 * x + f.2.1 * y

/-- Zone membership of a base, and invariance of the zone under the region's translations. -/
def okZone (R : Region m) (B : Base m) : Bool :=
  R.tests.all (fun f => decide (f.2.2 ≤ f.1 * B.x + f.2.1 * B.y) &&
    (decide (R.kind = 0) || decide (0 ≤ f.1 * R.Tx + f.2.1 * R.Ty)) &&
    (decide (R.kind ≤ 1) || decide (0 ≤ f.1 * R.Ux + f.2.1 * R.Uy)))

def okCoord (R : Region m) (B : Base m) : Bool :=
  (decide (R.kind = 0) ||
    (decide (R.pc ≤ R.px * B.x + R.py * B.y) && decide (R.px * B.x + R.py * B.y < R.pc + R.pM))) &&
  (decide (R.kind ≤ 1) ||
    (decide (R.qc ≤ R.qx * B.x + R.qy * B.y) && decide (R.qx * B.x + R.qy * B.y < R.qc + R.qM)))

def okRegCoord (R : Region m) : Bool :=
  (decide (R.kind = 0) || (decide (0 < R.pM) && decide (R.px * R.Tx + R.py * R.Ty = R.pM))) &&
  (decide (R.kind ≤ 1) || (decide (R.px * R.Ux + R.py * R.Uy = 0) && decide (0 < R.qM) &&
    decide (R.qx * R.Ux + R.qy * R.Uy = R.qM) && decide (R.qx * R.Tx + R.qy * R.Ty = 0)))

def ci (k j : ℕ) : ℕ := (if k = 0 then 0 else 1) + (if j = 0 then 0 else 2)
def kkOf (c : ℕ) : ℕ := c % 2
def jjOf (c : ℕ) : ℕ := c / 2

def okBase (r b : ℕ) : Bool :=
  let R := C.reg r
  let B := C.bas r b
  okZone R B && okCoord R B && decide (R.kind ≤ 2) &&
  (!decide (B.v = 0) || decide (C.dec r b 0 0 = C.x0)) &&
  (List.range (C.adj B.i).length).all (fun e => (List.range (ncases R.kind)).all (fun c =>
    C.okOut R B ((C.adj B.i).getD e edflt) (kkOf c) (jjOf c) ((B.out.getD e []).getD c Tgt.dflt))) &&
  (List.range (ncases R.kind)).all (fun c =>
    (decide (kkOf c = 0 ∧ jjOf c = 0 ∧ B.v = 0)) || C.okPred R B (kkOf c) (jjOf c) (B.pred.getD c Tgt.dflt)) &&
  (List.range R.bases.length).all (fun b2 =>
    decide (b2 = b) || !(decide ((C.bas r b2).x = B.x ∧ (C.bas r b2).y = B.y ∧ (C.bas r b2).i = B.i)))

def testOf (r : ℕ) (s : Bool) (r2 idx : ℕ) : ℤ × ℤ × ℤ :=
  (C.reg (if s then r2 else r)).tests.getD idx (0, 0, 0)

def okCert (r1 r2 : ℕ) (l : List (Bool × ℕ × ℕ)) : Bool :=
  decide ((l.map (fun t => (t.2.2 : ℤ) * (C.testOf r1 t.1 r2 t.2.1).1)).sum = 0) &&
  decide ((l.map (fun t => (t.2.2 : ℤ) * (C.testOf r1 t.1 r2 t.2.1).2.1)).sum = 0) &&
  decide (0 < (l.map (fun t => (t.2.2 : ℤ) * (C.testOf r1 t.1 r2 t.2.1).2.2)).sum)

def hasCert (r1 r2 : ℕ) : Bool :=
  C.okCert r1 r2 ((C.certs.getD r1 []).getD r2 [])

def check : Bool :=
  decide (0 < C.L) &&
  decide (C.r0 < C.regs.length) && decide (C.b0 < (C.reg C.r0).bases.length) &&
  decide ((C.bas C.r0 C.b0).v = 0) && decide (C.dec C.r0 C.b0 0 0 = C.x0) &&
  (List.range C.regs.length).all (fun r => okRegCoord (C.reg r) &&
    (List.range (C.reg r).bases.length).all (fun b => C.okBase r b)) &&
  (List.range C.regs.length).all (fun r1 => (List.range C.regs.length).all (fun r2 =>
    decide (r1 = r2) || C.hasCert r1 r2))

end Cfg
end GalCert
namespace GalCert
namespace Cfg
variable {m : ℕ} [NeZero m] (C : Cfg m)

theorem all_range {p : ℕ → Bool} {n : ℕ} (h : (List.range n).all p = true) {i : ℕ} (hi : i < n) :
    p i = true := by
  rw [List.all_eq_true] at h
  exact h i (List.mem_range.mpr hi)

theorem kk_ci (k j : ℕ) : kkOf (ci k j) = if k = 0 then 0 else 1 := by
  unfold kkOf ci; split_ifs <;> simp_all

theorem jj_ci (k j : ℕ) : jjOf (ci k j) = if j = 0 then 0 else 1 := by
  unfold jjOf ci; split_ifs <;> simp_all

theorem ci_lt {K k j : ℕ} (hK : K ≤ 2) (h1 : 1 ≤ K ∨ k = 0) (h2 : 2 ≤ K ∨ j = 0) :
    ci k j < ncases K := by
  unfold ci ncases; split_ifs <;> omega

theorem kk_eq (k : ℕ) : ((k : ℤ)) = ((if k = 0 then 0 else 1 : ℕ) : ℤ) * ((k - 1 : ℕ) : ℤ) +
    ((if k = 0 then 0 else 1 : ℕ) : ℤ) := by
  split_ifs with h
  · simp [h]
  · have : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr h
    push_cast [Nat.cast_sub this]; ring

theorem kk_eqN (k : ℕ) : k = (if k = 0 then 0 else 1) * (k - 1) + (if k = 0 then 0 else 1) := by
  split_ifs with h <;> omega

theorem aff_le {vB vB' L ka kb kc ja jb jc kk jj K1 J1 : ℕ} (h1 : L * (ka + ja) ≤ L * kk)
    (h2 : L * (kb + jb) ≤ L * jj) (h3 : vB' + L * (kc + jc) ≤ vB + L * (kk + jj) + 1) :
    vB' + L * ((ka * K1 + kb * J1 + kc) + (ja * K1 + jb * J1 + jc)) ≤
      vB + L * ((kk * K1 + kk) + (jj * J1 + jj)) + 1 := by
  have e1 : vB' + L * ((ka * K1 + kb * J1 + kc) + (ja * K1 + jb * J1 + jc)) =
      (vB' + L * (kc + jc)) + K1 * (L * (ka + ja)) + J1 * (L * (kb + jb)) := by ring
  have e2 : vB + L * ((kk * K1 + kk) + (jj * J1 + jj)) + 1 =
      (vB + L * (kk + jj) + 1) + K1 * (L * kk) + J1 * (L * jj) := by ring
  rw [e1, e2]
  exact Nat.add_le_add (Nat.add_le_add h3 (Nat.mul_le_mul_left _ h1)) (Nat.mul_le_mul_left _ h2)

theorem aff_eq {vB vB' L ka kb kc ja jb jc kk jj K1 J1 : ℕ} (h1 : L * (ka + ja) = L * kk)
    (h2 : L * (kb + jb) = L * jj) (h3 : vB' + L * (kc + jc) + 1 = vB + L * (kk + jj)) :
    vB' + L * ((ka * K1 + kb * J1 + kc) + (ja * K1 + jb * J1 + jc)) + 1 =
      vB + L * ((kk * K1 + kk) + (jj * J1 + jj)) := by
  have e1 : vB' + L * ((ka * K1 + kb * J1 + kc) + (ja * K1 + jb * J1 + jc)) + 1 =
      (vB' + L * (kc + jc) + 1) + K1 * (L * (ka + ja)) + J1 * (L * (kb + jb)) := by ring
  have e2 : vB + L * ((kk * K1 + kk) + (jj * J1 + jj)) =
      (vB + L * (kk + jj)) + K1 * (L * kk) + J1 * (L * jj) := by ring
  rw [e1, e2, h1, h2, h3]

structure Facts (C : Cfg m) : Prop where
  Lpos : 0 < C.L
  r0 : C.r0 < C.regs.length
  b0 : C.b0 < (C.reg C.r0).bases.length
  v0 : (C.bas C.r0 C.b0).v = 0
  d0 : C.dec C.r0 C.b0 0 0 = C.x0
  reg : ∀ r < C.regs.length, okRegCoord (C.reg r) = true
  base : ∀ r < C.regs.length, ∀ b < (C.reg r).bases.length, C.okBase r b = true
  cert : ∀ r1 < C.regs.length, ∀ r2 < C.regs.length, r1 ≠ r2 → C.hasCert r1 r2 = true

theorem facts (hc : C.check = true) : Facts C := by
  unfold check at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hc
  refine ⟨h1, h2, h3, h4, h5, ?_, ?_, ?_⟩
  · intro r hr
    have := all_range h6 hr
    simp only [Bool.and_eq_true] at this
    exact this.1
  · intro r hr b hb
    have := all_range h6 hr
    simp only [Bool.and_eq_true] at this
    exact all_range this.2 hb
  · intro r1 h1' r2 h2' hne
    have := all_range (all_range h7 h1') h2'
    simp only [Bool.or_eq_true, decide_eq_true_eq] at this
    exact this.resolve_left hne

section
variable {C}

theorem okBase_parts {r b : ℕ} (h : C.okBase r b = true) :
    okZone (C.reg r) (C.bas r b) = true ∧ okCoord (C.reg r) (C.bas r b) = true ∧ (C.reg r).kind ≤ 2 ∧
    ((C.bas r b).v = 0 → C.dec r b 0 0 = C.x0) ∧
    (∀ e < (C.adj (C.bas r b).i).length, ∀ c < ncases (C.reg r).kind,
      C.okOut (C.reg r) (C.bas r b) ((C.adj (C.bas r b).i).getD e edflt) (kkOf c) (jjOf c)
        (((C.bas r b).out.getD e []).getD c Tgt.dflt) = true) ∧
    (∀ c < ncases (C.reg r).kind, (kkOf c = 0 ∧ jjOf c = 0 ∧ (C.bas r b).v = 0) ∨
      C.okPred (C.reg r) (C.bas r b) (kkOf c) (jjOf c) ((C.bas r b).pred.getD c Tgt.dflt) = true) ∧
    (∀ b2 < (C.reg r).bases.length, (C.bas r b2).x = (C.bas r b).x → (C.bas r b2).y = (C.bas r b).y →
      (C.bas r b2).i = (C.bas r b).i → b2 = b) := by
  unfold okBase at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    decide_eq_false_iff_not] at h
  obtain ⟨⟨⟨⟨⟨⟨hz, hco⟩, hk⟩, h0⟩, ho⟩, hp⟩, hd⟩ := h
  refine ⟨hz, hco, hk, ?_, ?_, ?_, ?_⟩
  · intro hv; rcases h0 with h0 | h0
    · exact absurd hv h0
    · exact h0
  · intro e he c hc
    exact all_range (all_range ho he) hc
  · intro c hc
    have := all_range hp hc
    simp only [Bool.or_eq_true, decide_eq_true_eq] at this
    exact this
  · intro b2 hb2 hx hy hi
    have := all_range hd hb2
    simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not] at this
    rcases this with h | h
    · exact h
    · exact absurd ⟨hx, hy, hi⟩ h

theorem out_sound (hc : C.check = true) {r b k j : ℕ} (hv : C.Valid r b k j) {e : ℕ}
    (he : e < (C.adj (C.bas r b).i).length) :
    ∃ r' b' k' j', C.Valid r' b' k' j' ∧
      C.dec r' b' k' j' = sh (C.dec r b k j) ((C.adj (C.bas r b).i).getD e edflt) ∧
      C.val r' b' k' j' ≤ C.val r b k j + 1 := by
  obtain ⟨hr, hb, hk1, hj1⟩ := hv
  have F := facts C hc
  obtain ⟨-, -, hK, -, ho, -, -⟩ := okBase_parts (F.base r hr b hb)
  have hci := ci_lt hK hk1 hj1
  have h := ho e he (ci k j) hci
  set t := ((C.bas r b).out.getD e []).getD (ci k j) Tgt.dflt
  set d := (C.adj (C.bas r b).i).getD e edflt
  rw [kk_ci, jj_ci] at h
  unfold okOut at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hr', hb'⟩, hK1⟩, hK2⟩, ex1⟩, ex2⟩, ex3⟩, ey1⟩, ey2⟩, ey3⟩, hi⟩, hv1⟩, hv2⟩, hv3⟩ := h
  refine ⟨t.r, t.b, t.ka * (k - 1) + t.kb * (j - 1) + t.kc, t.ja * (k - 1) + t.jb * (j - 1) + t.jc,
    ⟨hr', hb', ?_, ?_⟩, ?_, ?_⟩
  · obtain h | h := hK1
    · exact Or.inl h
    · right; rw [h.1.1, h.1.2, h.2]; simp
  · obtain h | h := hK2
    · exact Or.inl h
    · right; rw [h.1.1, h.1.2, h.2]; simp
  · have ek := kk_eq k
    have ej := kk_eq j
    set kk := (if k = 0 then 0 else 1 : ℕ)
    set jj := (if j = 0 then 0 else 1 : ℕ)
    unfold dec sh
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · simp only
      push_cast
      rw [ek, ej]
      linear_combination ex3 + ((k - 1 : ℕ) : ℤ) * ex1 + ((j - 1 : ℕ) : ℤ) * ex2
    · simp only
      push_cast
      rw [ek, ej]
      linear_combination ey3 + ((k - 1 : ℕ) : ℤ) * ey1 + ((j - 1 : ℕ) : ℤ) * ey2
    · exact hi
  · have ek := kk_eqN k
    have ej := kk_eqN j
    set kk := (if k = 0 then 0 else 1 : ℕ)
    set jj := (if j = 0 then 0 else 1 : ℕ)
    unfold val
    have := aff_le (K1 := k - 1) (J1 := j - 1) hv1 hv2 hv3
    rw [← ek, ← ej] at this
    exact this

theorem pred_sound (hc : C.check = true) {r b k j : ℕ} (hv : C.Valid r b k j)
    (hpos : 0 < C.val r b k j) :
    ∃ r' b' k' j', C.Valid r' b' k' j' ∧ C.val r' b' k' j' + 1 = C.val r b k j ∧
      C.dec r b k j ∈ nbrs C.adj (C.dec r' b' k' j') := by
  obtain ⟨hr, hb, hk1, hj1⟩ := hv
  have F := facts C hc
  obtain ⟨-, -, hK, -, -, hp, -⟩ := okBase_parts (F.base r hr b hb)
  have hci := ci_lt hK hk1 hj1
  have h := hp (ci k j) hci
  rw [kk_ci, jj_ci] at h
  rcases h with ⟨h1, h2, h3⟩ | h
  · exfalso
    unfold val at hpos
    split_ifs at h1 h2 with hk0 hj0 <;> simp_all
  set t := (C.bas r b).pred.getD (ci k j) Tgt.dflt
  unfold okPred at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hr', hb'⟩, he⟩, hK1⟩, hK2⟩, ex1⟩, ex2⟩, ex3⟩, ey1⟩, ey2⟩, ey3⟩, hi⟩, hv1⟩, hv2⟩, hv3⟩ := h
  refine ⟨t.r, t.b, t.ka * (k - 1) + t.kb * (j - 1) + t.kc, t.ja * (k - 1) + t.jb * (j - 1) + t.jc,
    ⟨hr', hb', ?_, ?_⟩, ?_, ?_⟩
  · obtain h | h := hK1
    · exact Or.inl h
    · right; rw [h.1.1, h.1.2, h.2]; simp
  · obtain h | h := hK2
    · exact Or.inl h
    · right; rw [h.1.1, h.1.2, h.2]; simp
  · have ek := kk_eqN k
    have ej := kk_eqN j
    set kk := (if k = 0 then 0 else 1 : ℕ)
    set jj := (if j = 0 then 0 else 1 : ℕ)
    unfold val
    have := aff_eq (K1 := k - 1) (J1 := j - 1) hv1 hv2 hv3
    rw [← ek, ← ej] at this
    exact this
  · unfold nbrs
    rw [List.mem_toFinset, List.mem_map]
    refine ⟨(C.adj (C.bas t.r t.b).i).getD t.e edflt, ?_, ?_⟩
    · rw [List.getD_eq_getElem _ _ he]; exact List.getElem_mem he
    · have ek := kk_eq k
      have ej := kk_eq j
      set kk := (if k = 0 then 0 else 1 : ℕ)
      set jj := (if j = 0 then 0 else 1 : ℕ)
      unfold dec
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · simp only
        push_cast
        rw [ek, ej]
        linear_combination ex3 + ((k - 1 : ℕ) : ℤ) * ex1 + ((j - 1 : ℕ) : ℤ) * ex2
      · simp only
        push_cast
        rw [ek, ej]
        linear_combination ey3 + ((k - 1 : ℕ) : ℤ) * ey1 + ((j - 1 : ℕ) : ℤ) * ey2
      · exact hi

end
end Cfg
end GalCert
namespace GalCert
namespace Cfg
variable {m : ℕ} [NeZero m] {C : Cfg m}

theorem zone_sound (hc : C.check = true) {r b k j : ℕ} (hv : C.Valid r b k j) :
    ∀ f ∈ (C.reg r).tests, f.2.2 ≤ f.1 * (C.dec r b k j).1 + f.2.1 * (C.dec r b k j).2.1 := by
  obtain ⟨hr, hb, hk1, hj1⟩ := hv
  have F := facts C hc
  obtain ⟨hz, -, -, -, -, -, -⟩ := okBase_parts (F.base r hr b hb)
  intro f hf
  unfold okZone at hz
  rw [List.all_eq_true] at hz
  have h := hz f hf
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h0, h1⟩, h2⟩ := h
  have t1 : 0 ≤ (k : ℤ) * (f.1 * (C.reg r).Tx + f.2.1 * (C.reg r).Ty) := by
    rcases h1 with h1 | h1
    · rcases hk1 with h | h
      · omega
      · simp [h]
    · exact mul_nonneg (by positivity) h1
  have t2 : 0 ≤ (j : ℤ) * (f.1 * (C.reg r).Ux + f.2.1 * (C.reg r).Uy) := by
    rcases h2 with h2 | h2
    · rcases hj1 with h | h
      · omega
      · simp [h]
    · exact mul_nonneg (by positivity) h2
  unfold dec
  linarith

theorem cert_sum (x y : ℤ) (l : List (Bool × ℕ × ℕ)) (tf : Bool → ℕ → ℤ × ℤ × ℤ)
    (h : ∀ t ∈ l, (tf t.1 t.2.1).2.2 ≤ (tf t.1 t.2.1).1 * x + (tf t.1 t.2.1).2.1 * y) :
    (l.map (fun t => (t.2.2 : ℤ) * (tf t.1 t.2.1).2.2)).sum ≤
      x * (l.map (fun t => (t.2.2 : ℤ) * (tf t.1 t.2.1).1)).sum +
      y * (l.map (fun t => (t.2.2 : ℤ) * (tf t.1 t.2.1).2.1)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    have ha := h a (List.mem_cons_self ..)
    have hl := ih (fun t ht => h t (List.mem_cons_of_mem _ ht))
    have : (a.2.2 : ℤ) * (tf a.1 a.2.1).2.2 ≤ (a.2.2 : ℤ) * ((tf a.1 a.2.1).1 * x + (tf a.1 a.2.1).2.1 * y) :=
      mul_le_mul_of_nonneg_left ha (by positivity)
    nlinarith [this, hl]

theorem getD_test {l : List (ℤ × ℤ × ℤ)} {x y : ℤ}
    (h : ∀ f ∈ l, f.2.2 ≤ f.1 * x + f.2.1 * y) (i : ℕ) :
    (l.getD i (0, 0, 0)).2.2 ≤ (l.getD i (0, 0, 0)).1 * x + (l.getD i (0, 0, 0)).2.1 * y := by
  rcases lt_or_ge i l.length with hi | hi
  · rw [List.getD_eq_getElem _ _ hi]; exact h _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ hi]; simp

theorem no_two_zones (hc : C.check = true) {r1 r2 : ℕ} (h1 : r1 < C.regs.length)
    (h2 : r2 < C.regs.length) (hne : r1 ≠ r2) (x y : ℤ)
    (z1 : ∀ f ∈ (C.reg r1).tests, f.2.2 ≤ f.1 * x + f.2.1 * y)
    (z2 : ∀ f ∈ (C.reg r2).tests, f.2.2 ≤ f.1 * x + f.2.1 * y) : False := by
  have F := facts C hc
  have hh := F.cert r1 h1 r2 h2 hne
  unfold hasCert okCert at hh
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hh
  obtain ⟨⟨s1, s2⟩, s3⟩ := hh
  have := cert_sum x y ((C.certs.getD r1 []).getD r2 []) (fun s i => C.testOf r1 s r2 i) (by
    intro t _
    unfold testOf
    split_ifs
    · exact getD_test z2 _
    · exact getD_test z1 _)
  beta_reduce at this
  rw [s1, s2] at this
  linarith

theorem coord_unique {a a' c M : ℤ} {k k' : ℕ} (hM : 0 < M) (ha : c ≤ a) (ha' : a < c + M)
    (hb : c ≤ a') (hb' : a' < c + M) (h : a + k * M = a' + k' * M) : k = k' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hl | hl
  · have : (k : ℤ) + 1 ≤ k' := by exact_mod_cast hl
    nlinarith
  · have : (k' : ℤ) + 1 ≤ k := by exact_mod_cast hl
    nlinarith

theorem dec_inj (hc : C.check = true) {r b k j r' b' k' j' : ℕ} (hv : C.Valid r b k j)
    (hv' : C.Valid r' b' k' j') (h : C.dec r b k j = C.dec r' b' k' j') :
    r = r' ∧ b = b' ∧ k = k' ∧ j = j' := by
  have F := facts C hc
  by_cases hr : r = r'
  · subst hr
    refine ⟨rfl, ?_⟩
    obtain ⟨hr, hb, hk1, hj1⟩ := hv
    obtain ⟨-, hb', hk1', hj1'⟩ := hv'
    obtain ⟨-, hco, hK, -, -, -, hd⟩ := okBase_parts (F.base r hr b hb)
    obtain ⟨-, hco', -, -, -, -, -⟩ := okBase_parts (F.base r hr b' hb')
    have hrc := F.reg r hr
    unfold okRegCoord at hrc
    unfold okCoord at hco hco'
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hrc hco hco'
    unfold dec at h
    simp only [Prod.mk.injEq] at h
    obtain ⟨hx, hy, hi⟩ := h
    have hkk : k = k' := by
      rcases hrc.1 with h0 | ⟨hM, hT⟩
      · rcases hk1 with h | h
        · omega
        · rcases hk1' with h' | h'
          · omega
          · omega
      · rcases hco.1 with h0 | ⟨p1, p2⟩
        · omega
        rcases hco'.1 with h0 | ⟨q1, q2⟩
        · omega
        have hU : (j : ℤ) * ((C.reg r).px * (C.reg r).Ux + (C.reg r).py * (C.reg r).Uy) =
            (j' : ℤ) * ((C.reg r).px * (C.reg r).Ux + (C.reg r).py * (C.reg r).Uy) := by
          rcases hrc.2 with h2 | ⟨⟨⟨hU0, -⟩, -⟩, -⟩
          · rcases hj1 with h | h
            · omega
            rcases hj1' with h' | h'
            · omega
            simp [h, h']
          · rw [hU0]; simp
        refine coord_unique hM p1 p2 q1 q2 ?_
        rw [← hT]
        have := congrArg (fun z => (C.reg r).px * z) hx
        have h2 := congrArg (fun z => (C.reg r).py * z) hy
        linear_combination this + h2 - hU
    subst hkk
    have hjj : j = j' := by
      rcases hrc.2 with h0 | ⟨⟨⟨hU0, hM⟩, hQ⟩, hT0⟩
      · rcases hj1 with h | h
        · omega
        · rcases hj1' with h' | h'
          · omega
          · omega
      · rcases hco.2 with h0 | ⟨p1, p2⟩
        · omega
        rcases hco'.2 with h0 | ⟨q1, q2⟩
        · omega
        refine coord_unique hM p1 p2 q1 q2 ?_
        rw [← hQ]
        have := congrArg (fun z => (C.reg r).qx * z) hx
        have h2 := congrArg (fun z => (C.reg r).qy * z) hy
        linear_combination this + h2 - (k : ℤ) * hT0 + (k : ℤ) * hT0
    subst hjj
    refine ⟨?_, rfl, rfl⟩
    exact (hd b' hb' (by linarith) (by linarith) hi.symm).symm
  · exfalso
    have z1 := zone_sound hc hv
    have z2 := zone_sound hc hv'
    rw [← h] at z2
    exact no_two_zones hc hv.1 hv'.1 hr _ _ z1 z2

theorem val_zero (hc : C.check = true) {r b k j : ℕ} (hv : C.Valid r b k j)
    (h0 : C.val r b k j = 0) : C.dec r b k j = C.x0 := by
  have F := facts C hc
  obtain ⟨hr, hb, -, -⟩ := hv
  obtain ⟨-, -, -, hz, -, -, -⟩ := okBase_parts (F.base r hr b hb)
  unfold val at h0
  have hv0 : (C.bas r b).v = 0 := by omega
  have hkj : C.L * (k + j) = 0 := by omega
  rcases Nat.mul_eq_zero.mp hkj with h | h
  · exact absurd h (Nat.pos_iff_ne_zero.mp F.Lpos)
  · have hk : k = 0 := by omega
    have hj : j = 0 := by omega
    subst hk hj
    exact hz hv0

theorem mem_nbrs {adj : Fin m → List (ℤ × ℤ × Fin m)} {x y : ℤ × ℤ × Fin m} :
    y ∈ nbrs adj x ↔ ∃ e < (adj x.2.2).length, y = sh x ((adj x.2.2).getD e edflt) := by
  unfold nbrs sh
  rw [List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨d, hd, rfl⟩
    obtain ⟨e, he, rfl⟩ := List.getElem_of_mem hd
    exact ⟨e, he, by rw [List.getD_eq_getElem _ _ he]⟩
  · rintro ⟨e, he, rfl⟩
    exact ⟨_, by rw [List.getD_eq_getElem _ _ he]; exact List.getElem_mem he, rfl⟩

theorem ball_iff (hc : C.check = true) (n : ℕ) (x : ℤ × ℤ × Fin m) :
    x ∈ ball C.adj C.x0 n ↔ ∃ r b k j, C.Valid r b k j ∧ C.val r b k j ≤ n ∧ C.dec r b k j = x := by
  have F := facts C hc
  induction n generalizing x with
  | zero =>
    simp only [ball, Finset.mem_singleton, Nat.le_zero]
    constructor
    · rintro rfl
      refine ⟨C.r0, C.b0, 0, 0, ⟨F.r0, F.b0, Or.inr rfl, Or.inr rfl⟩, ?_, F.d0⟩
      unfold val; rw [F.v0]; simp
    · rintro ⟨r, b, k, j, hv, h0, rfl⟩
      exact val_zero hc hv h0
  | succ n ih =>
    simp only [ball, Finset.mem_union, Finset.mem_biUnion]
    constructor
    · rintro (h | ⟨z, hz, hxz⟩)
      · obtain ⟨r, b, k, j, hv, hle, hd⟩ := (ih x).mp h
        exact ⟨r, b, k, j, hv, by omega, hd⟩
      · obtain ⟨r, b, k, j, hv, hle, rfl⟩ := (ih z).mp hz
        obtain ⟨e, he, rfl⟩ := mem_nbrs.mp hxz
        have he' : e < (C.adj (C.bas r b).i).length := he
        obtain ⟨r', b', k', j', hv', hd', hval⟩ := out_sound hc hv he'
        exact ⟨r', b', k', j', hv', by omega, hd'⟩
    · rintro ⟨r, b, k, j, hv, hle, rfl⟩
      rcases Nat.lt_or_ge n (C.val r b k j) with hlt | hge
      · right
        obtain ⟨r', b', k', j', hv', hval, hmem⟩ := pred_sound hc hv (by omega)
        exact ⟨C.dec r' b' k' j', (ih _).mpr ⟨r', b', k', j', hv', by omega, rfl⟩, hmem⟩
      · left
        exact (ih _).mpr ⟨r, b, k, j, hv, hge, rfl⟩

end Cfg
end GalCert
namespace GalCert
namespace Cfg
variable {m : ℕ} [NeZero m]

def pcard (C : Cfg m) (r b n : ℕ) : ℕ :=
  if (C.reg r).kind = 0 then (if (C.bas r b).v = n then 1 else 0)
  else if (C.bas r b).v ≤ n ∧ C.L ∣ (n - (C.bas r b).v) then
    (if (C.reg r).kind = 1 then 1 else (n - (C.bas r b).v) / C.L + 1) else 0

def A (C : Cfg m) (n : ℕ) : ℕ :=
  ((List.range C.regs.length).map (fun r =>
    ((List.range (C.reg r).bases.length).map (fun b => C.pcard r b n)).sum)).sum

theorem emb_inj (r b : ℕ) : Function.Injective (fun p : ℕ × ℕ => (r, b, p.1, p.2)) := by
  intro p q h
  simp only [Prod.mk.injEq] at h
  exact Prod.ext h.2.2.1 h.2.2.2

def piece (C : Cfg m) (r b n : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  if (C.reg r).kind = 0 then (if (C.bas r b).v = n then {(r, b, 0, 0)} else ∅)
  else if (C.bas r b).v ≤ n ∧ C.L ∣ (n - (C.bas r b).v) then
    (if (C.reg r).kind = 1 then {(r, b, (n - (C.bas r b).v) / C.L, 0)}
     else (Finset.HasAntidiagonal.antidiagonal ((n - (C.bas r b).v) / C.L) : Finset (ℕ × ℕ)).map ⟨_, emb_inj r b⟩)
  else ∅

def Sph (C : Cfg m) (n : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  (Finset.range C.regs.length).biUnion fun r =>
    (Finset.range (C.reg r).bases.length).biUnion fun b => C.piece r b n

variable {C : Cfg m}

theorem val_iff {v L s n : ℕ} (hL : 0 < L) :
    v + L * s = n ↔ v ≤ n ∧ L ∣ (n - v) ∧ s = (n - v) / L := by
  constructor
  · rintro rfl
    refine ⟨by omega, ⟨s, by omega⟩, ?_⟩
    rw [show v + L * s - v = L * s by omega, Nat.mul_div_cancel_left _ hL]
  · rintro ⟨h1, h2, rfl⟩
    rw [Nat.mul_div_cancel' h2]; omega

theorem mem_piece (hL : 0 < C.L) {r b n r' b' k j : ℕ} :
    (r', b', k, j) ∈ C.piece r b n ↔ r' = r ∧ b' = b ∧ (1 ≤ (C.reg r).kind ∨ k = 0) ∧
      (2 ≤ (C.reg r).kind ∨ j = 0) ∧ C.val r b k j = n := by
  unfold piece val
  by_cases h0 : (C.reg r).kind = 0
  · simp only [h0, if_true]
    by_cases h1 : (C.bas r b).v = n
    · simp only [h1, if_true, Finset.mem_singleton, Prod.mk.injEq]
      constructor
      · rintro ⟨rfl, rfl, rfl, rfl⟩
        exact ⟨rfl, rfl, Or.inr rfl, Or.inr rfl, by simp⟩
      · rintro ⟨rfl, rfl, hk, hj, hv⟩
        have hk' : k = 0 := by omega
        have hj' : j = 0 := by omega
        exact ⟨rfl, rfl, hk', hj'⟩
    · simp only [h1, if_false, Finset.notMem_empty, false_iff]
      rintro ⟨rfl, rfl, hk, hj, hv⟩
      have hk' : k = 0 := by omega
      have hj' : j = 0 := by omega
      subst hk' hj'
      simp at hv
      exact h1 hv
  · simp only [h0, if_false]
    by_cases h1 : (C.bas r b).v ≤ n ∧ C.L ∣ (n - (C.bas r b).v)
    · simp only [h1, and_self, if_true]
      by_cases h2 : (C.reg r).kind = 1
      · simp only [h2, if_true, Finset.mem_singleton, Prod.mk.injEq]
        constructor
        · rintro ⟨rfl, rfl, rfl, rfl⟩
          refine ⟨rfl, rfl, Or.inl (by omega), Or.inr rfl, ?_⟩
          rw [add_zero]
          exact (val_iff hL).mpr ⟨h1.1, h1.2, rfl⟩
        · rintro ⟨rfl, rfl, hk, hj, hv⟩
          have hj' : j = 0 := by omega
          subst hj'
          rw [add_zero] at hv
          exact ⟨rfl, rfl, ((val_iff hL).mp hv).2.2, rfl⟩
      · simp only [h2, if_false]
        rw [Finset.mem_map]
        constructor
        · rintro ⟨⟨p1, p2⟩, hp, he⟩
          rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
          simp only [Function.Embedding.coeFn_mk, Prod.mk.injEq] at he
          obtain ⟨rfl, rfl, rfl, rfl⟩ := he
          refine ⟨rfl, rfl, Or.inl (by omega), Or.inl (by omega), ?_⟩
          exact (val_iff hL).mpr ⟨h1.1, h1.2, hp⟩
        · rintro ⟨rfl, rfl, -, -, hv⟩
          exact ⟨(k, j), Finset.HasAntidiagonal.mem_antidiagonal.mpr ((val_iff hL).mp hv).2.2, rfl⟩
    · simp only [h1, if_false, Finset.notMem_empty, false_iff]
      rintro ⟨rfl, rfl, -, -, hv⟩
      have := (val_iff hL).mp hv
      exact h1 ⟨this.1, this.2.1⟩

theorem mem_Sph (hL : 0 < C.L) {n r b k j : ℕ} :
    (r, b, k, j) ∈ C.Sph n ↔ C.Valid r b k j ∧ C.val r b k j = n := by
  unfold Sph Valid
  simp only [Finset.mem_biUnion, Finset.mem_range]
  constructor
  · rintro ⟨r', hr', b', hb', h⟩
    obtain ⟨rfl, rfl, hk, hj, hv⟩ := (mem_piece hL).mp h
    exact ⟨⟨hr', hb', hk, hj⟩, hv⟩
  · rintro ⟨⟨hr, hb, hk, hj⟩, hv⟩
    exact ⟨r, hr, b, hb, (mem_piece hL).mpr ⟨rfl, rfl, hk, hj, hv⟩⟩

theorem piece_fst (hL : 0 < C.L) {r b n : ℕ} {c : ℕ × ℕ × ℕ × ℕ} (h : c ∈ C.piece r b n) :
    c.1 = r ∧ c.2.1 = b := by
  obtain ⟨r', b', k, j⟩ := c
  have := (mem_piece hL).mp h
  exact ⟨this.1, this.2.1⟩

theorem card_piece (r b n : ℕ) : (C.piece r b n).card = C.pcard r b n := by
  unfold piece pcard
  split_ifs <;> simp

theorem lsum_range (f : ℕ → ℕ) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, Finset.sum_range_succ, ih]; simp

theorem card_Sph (hL : 0 < C.L) (n : ℕ) : (C.Sph n).card = C.A n := by
  unfold Sph A
  rw [Finset.card_biUnion, lsum_range]
  · apply Finset.sum_congr rfl
    intro r _
    rw [Finset.card_biUnion, lsum_range]
    · apply Finset.sum_congr rfl
      intro b _
      exact card_piece r b n
    · intro b1 _ b2 _ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro c h1 h2
      exact hne ((piece_fst hL h1).2.symm.trans (piece_fst hL h2).2)
  · intro r1 _ r2 _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro c h1 h2
    simp only [Finset.mem_biUnion] at h1 h2
    obtain ⟨b1, -, h1⟩ := h1
    obtain ⟨b2, -, h2⟩ := h2
    exact hne ((piece_fst hL h1).1.symm.trans (piece_fst hL h2).1)

theorem ball_mono (n : ℕ) : ball C.adj C.x0 n ⊆ ball C.adj C.x0 (n + 1) := by
  intro x hx
  simp only [ball, Finset.mem_union]
  exact Or.inl hx

theorem sphere_eq (hc : C.check = true) (n : ℕ) :
    ball C.adj C.x0 (n + 1) \ ball C.adj C.x0 n =
      (C.Sph (n + 1)).image (fun c => C.dec c.1 c.2.1 c.2.2.1 c.2.2.2) := by
  have F := facts C hc
  ext x
  rw [Finset.mem_sdiff, Finset.mem_image, ball_iff hc, ball_iff hc]
  constructor
  · rintro ⟨⟨r, b, k, j, hv, hle, rfl⟩, hn⟩
    refine ⟨(r, b, k, j), (mem_Sph F.Lpos).mpr ⟨hv, ?_⟩, rfl⟩
    by_contra hne
    exact hn ⟨r, b, k, j, hv, by omega, rfl⟩
  · rintro ⟨⟨r, b, k, j⟩, hc', rfl⟩
    obtain ⟨hv, hval⟩ := (mem_Sph F.Lpos).mp hc'
    refine ⟨⟨r, b, k, j, hv, hval.le, rfl⟩, ?_⟩
    rintro ⟨r', b', k', j', hv', hle, hd⟩
    obtain ⟨rfl, rfl, rfl, rfl⟩ := dec_inj hc hv' hv hd
    omega

theorem card_step (hc : C.check = true) (n : ℕ) :
    ((ball C.adj C.x0 (n + 1)).card : ℤ) - (ball C.adj C.x0 n).card = C.A (n + 1) := by
  have F := facts C hc
  have h1 := Finset.card_sdiff_add_card_eq_card (ball_mono (C := C) n)
  have h2 : (ball C.adj C.x0 (n + 1) \ ball C.adj C.x0 n).card = C.A (n + 1) := by
    rw [sphere_eq hc, Finset.card_image_of_injOn, card_Sph F.Lpos]
    rintro ⟨r, b, k, j⟩ h1 ⟨r', b', k', j'⟩ h2 hd
    obtain ⟨hv, -⟩ := (mem_Sph F.Lpos).mp h1
    obtain ⟨hv', -⟩ := (mem_Sph F.Lpos).mp h2
    obtain ⟨rfl, rfl, rfl, rfl⟩ := dec_inj hc hv hv' hd
    rfl
  omega

theorem pcard_rec (hL : 0 < C.L) {r b n : ℕ} (hv : (C.bas r b).v < n) :
    C.pcard r b (n + 2 * C.L) + C.pcard r b n = 2 * C.pcard r b (n + C.L) := by
  unfold pcard
  set v := (C.bas r b).v
  have e2 : n + 2 * C.L - v = (n - v) + C.L * 2 := by omega
  have e1 : n + C.L - v = (n - v) + C.L * 1 := by omega
  rw [e2, e1]
  have d2 : C.L ∣ (n - v) + C.L * 2 ↔ C.L ∣ (n - v) :=
    (Nat.dvd_add_left (Dvd.intro 2 rfl))
  have d1 : C.L ∣ (n - v) + C.L * 1 ↔ C.L ∣ (n - v) :=
    (Nat.dvd_add_left (Dvd.intro 1 rfl))
  have q2 : ((n - v) + C.L * 2) / C.L = (n - v) / C.L + 2 := by
    rw [Nat.add_mul_div_left _ _ hL]
  have q1 : ((n - v) + C.L * 1) / C.L = (n - v) / C.L + 1 := by
    rw [Nat.add_mul_div_left _ _ hL]
  simp only [d2, d1, q2, q1]
  split_ifs <;> omega

theorem A_rec (hc : C.check = true) {V : ℕ}
    (hV : ∀ r < C.regs.length, ∀ b < (C.reg r).bases.length, (C.bas r b).v ≤ V) {n : ℕ}
    (hn : V < n) : C.A (n + 2 * C.L) + C.A n = 2 * C.A (n + C.L) := by
  have F := facts C hc
  unfold A
  rw [← List.sum_map_add, ← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro r hr
  rw [List.mem_range] at hr
  rw [← List.sum_map_add, ← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro b hb
  rw [List.mem_range] at hb
  exact pcard_rec F.Lpos (lt_of_le_of_lt (hV r hr b hb) hn)

end Cfg

theorem zero_of_window {g : ℕ → ℤ} {L N : ℕ} (hL0 : 0 < L) (hrec : ∀ n, N ≤ n → g (n + 2 * L) + g n = 2 * g (n + L))
    (hw : ∀ n, N ≤ n → n < N + 2 * L → g n = 0) : ∀ n, N ≤ n → g n = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases Nat.lt_or_ge n (N + 2 * L) with h | h
    · exact hw n hn h
    · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 2 * L := ⟨n - 2 * L, by omega⟩
      have h1 := hrec n' (by omega)
      rw [ih n' (by omega) (by omega), ih (n' + L) (by omega) (by omega)] at h1
      linarith

open PowerSeries in
noncomputable def polyOf : List ℤ → PowerSeries ℤ
  | [] => 0
  | c :: l => PowerSeries.C c + PowerSeries.X * polyOf l

def conv (a : ℕ → ℤ) : List ℤ → ℕ → ℤ
  | [], _ => 0
  | c :: l, 0 => c * a 0
  | c :: l, n + 1 => c * a (n + 1) + conv a l n

open PowerSeries in
theorem coeff_mul_polyOf (a : ℕ → ℤ) (l : List ℤ) (n : ℕ) :
    coeff n (mk a * polyOf l) = conv a l n := by
  induction l generalizing n with
  | nil => simp [polyOf, conv]
  | cons c l ih =>
    rw [polyOf, mul_add, mul_comm (mk a) (C c), mul_left_comm, map_add, coeff_C_mul, coeff_mk]
    cases n with
    | zero => simp [conv]
    | succ n => rw [coeff_succ_X_mul, ih]; simp [conv]

open PowerSeries in
theorem coeff_polyOf (l : List ℤ) (n : ℕ) : coeff n (polyOf l) = l.getD n 0 := by
  induction l generalizing n with
  | nil => simp [polyOf]
  | cons c l ih =>
    cases n with
    | zero => simp [polyOf]
    | succ n => rw [polyOf, map_add, coeff_C, coeff_succ_X_mul, ih]; simp

open PowerSeries in
theorem gf_of_conv (a : ℕ → ℤ) (dl pl : List ℤ) (h : ∀ n, conv a dl n = pl.getD n 0) :
    mk a * polyOf dl = polyOf pl := by
  ext n
  rw [coeff_mul_polyOf, coeff_polyOf, h]

end GalCert

namespace GalCert
namespace Cfg
variable {m : ℕ} [NeZero m] {C : Cfg m}

def vbound (C : Cfg m) (V : ℕ) : Bool :=
  (List.range C.regs.length).all (fun r =>
    (List.range (C.reg r).bases.length).all (fun b => decide ((C.bas r b).v ≤ V)))

theorem vbound_spec {V : ℕ} (h : C.vbound V = true) :
    ∀ r < C.regs.length, ∀ b < (C.reg r).bases.length, (C.bas r b).v ≤ V := by
  intro r hr b hb
  have := all_range (all_range h hr) hb
  simpa using this

theorem lin_rec (hc : C.check = true) {V : ℕ} (hV : C.vbound V = true) (cs : List (ℤ × ℕ))
    (hs : ∀ p ∈ cs, 1 ≤ p.2) (n : ℕ) (hn : V ≤ n) :
    (cs.map fun p => p.1 * (C.A (n + 2 * C.L + p.2) : ℤ)).sum +
      (cs.map fun p => p.1 * (C.A (n + p.2) : ℤ)).sum =
      2 * (cs.map fun p => p.1 * (C.A (n + C.L + p.2) : ℤ)).sum := by
  induction cs with
  | nil => simp
  | cons p cs ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 := ih (fun q hq => hs q (List.mem_cons_of_mem _ hq))
    have hp := hs p (List.mem_cons_self ..)
    have h2 := A_rec hc (vbound_spec hV) (n := n + p.2) (by omega)
    rw [show n + p.2 + 2 * C.L = n + 2 * C.L + p.2 by omega,
      show n + p.2 + C.L = n + C.L + p.2 by omega] at h2
    have h3 : (C.A (n + 2 * C.L + p.2) : ℤ) + C.A (n + p.2) = 2 * C.A (n + C.L + p.2) := by
      exact_mod_cast h2
    linear_combination h1 + p.1 * h3

theorem lin_zero (hc : C.check = true) {V : ℕ} (hV : C.vbound V = true) (cs : List (ℤ × ℕ))
    (hs : ∀ p ∈ cs, 1 ≤ p.2)
    (hw : ∀ n < V + 2 * C.L, (cs.map fun p => p.1 * (C.A (n + p.2) : ℤ)).sum = 0) :
    ∀ n, (cs.map fun p => p.1 * (C.A (n + p.2) : ℤ)).sum = 0 := by
  have F := facts C hc
  intro n
  rcases Nat.lt_or_ge n (V + 2 * C.L) with h | h
  · exact hw n h
  · refine zero_of_window (g := fun n => (cs.map fun p => p.1 * (C.A (n + p.2) : ℤ)).sum)
      (L := C.L) (N := V) F.Lpos (fun n hn => lin_rec hc hV cs hs n hn) (fun n _ h2 => hw n h2) n
      (by omega)

end Cfg
end GalCert

namespace GalCert

theorem conv_cs (a : ℕ → ℤ) (l : List ℤ) (k : ℕ) :
    conv a l (k + l.length) = ((List.range l.length).map fun i => l.getD i 0 * a (k + l.length - i)).sum := by
  induction l generalizing k with
  | nil => simp [conv]
  | cons c l ih =>
    rw [List.length_cons, show k + (l.length + 1) = (k + l.length) + 1 by omega, conv, ih,
      List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]
    simp only [List.getD_cons_zero, Nat.sub_zero, Function.comp_def, List.getD_cons_succ]
    congr 2
    apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    congr 2
    omega

def csOf (l : List ℤ) : List (ℤ × ℕ) := (List.range l.length).map fun i => (l.getD i 0, l.length - i)

theorem csOf_pos (l : List ℤ) : ∀ p ∈ csOf l, 1 ≤ p.2 := by
  intro p hp
  unfold csOf at hp
  rw [List.mem_map] at hp
  obtain ⟨i, hi, rfl⟩ := hp
  rw [List.mem_range] at hi
  simp only
  omega

namespace Cfg
variable {m : ℕ} [NeZero m] {C : Cfg m}

theorem gf_from (hc : C.check = true) {V : ℕ} (hV : C.vbound V = true) (a : ℕ → ℤ)
    (ha : ∀ n, 1 ≤ n → a n = C.A n) (dl pl : List ℤ) (M : ℕ) (hM : dl.length ≤ M)
    (hP : pl.length ≤ M)
    (hw : ∀ n < V + 2 * C.L, ((csOf dl).map fun p => p.1 * (C.A (n + p.2) : ℤ)).sum = 0)
    (hsmall : ∀ n < M, conv a dl n = pl.getD n 0) :
    PowerSeries.mk a * polyOf dl = polyOf pl := by
  apply gf_of_conv
  intro n
  rcases Nat.lt_or_ge n M with h | h
  · exact hsmall n h
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + dl.length := ⟨n - dl.length, by omega⟩
    rw [List.getD_eq_default _ _ (by omega), conv_cs]
    have hz := lin_zero hc hV (csOf dl) (csOf_pos dl) hw k
    unfold csOf at hz
    rw [List.map_map] at hz
    refine Eq.trans ?_ hz
    congr 1
    apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    simp only [Function.comp_apply]
    rw [ha _ (by omega), show k + dl.length - i = k + (dl.length - i) by omega]

end Cfg
end GalCert

namespace GalCert

def csOfS (l : List ℤ) (s : ℕ) : List (ℤ × ℕ) :=
  (List.range l.length).map fun i => (l.getD i 0, l.length - i + s)

theorem csOfS_pos (l : List ℤ) (s : ℕ) : ∀ p ∈ csOfS l s, 1 ≤ p.2 := by
  intro p hp
  unfold csOfS at hp
  rw [List.mem_map] at hp
  obtain ⟨i, hi, rfl⟩ := hp
  rw [List.mem_range] at hi
  simp only
  omega

namespace Cfg
variable {m : ℕ} [NeZero m] {C : Cfg m}

theorem gf_from2 (hc : C.check = true) {V : ℕ} (hV : C.vbound V = true) (a : ℕ → ℤ)
    (ha : ∀ n, 1 ≤ n → a n = C.A n) (dl pl : List ℤ) (s M : ℕ) (hM : dl.length + s ≤ M)
    (hP : pl.length ≤ M)
    (hw : ∀ n < V + 2 * C.L, ((csOfS dl s).map fun p => p.1 * (C.A (n + p.2) : ℤ)).sum = 0)
    (hsmall : ∀ n < M, conv a dl n = pl.getD n 0) :
    PowerSeries.mk a * polyOf dl = polyOf pl := by
  apply gf_of_conv
  intro n
  rcases Nat.lt_or_ge n M with h | h
  · exact hsmall n h
  · obtain ⟨k, rfl⟩ : ∃ k, n = (k + s) + dl.length := ⟨n - s - dl.length, by omega⟩
    rw [List.getD_eq_default _ _ (by omega), conv_cs]
    have hz := lin_zero hc hV (csOfS dl s) (csOfS_pos dl s) hw k
    unfold csOfS at hz
    rw [List.map_map] at hz
    refine Eq.trans ?_ hz
    congr 1
    apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    simp only [Function.comp_apply]
    rw [ha _ (by omega), show k + s + dl.length - i = k + (dl.length - i + s) by omega]

end Cfg
end GalCert


namespace P312549
open OMA.S_oeis_a312549

/-- A packed target code (mixed radix). -/
def tg (n : ℕ) : GalCert.Tgt := ⟨n % 13, n / 13 % 49, n / 637 % 2, n / 1274 % 2, n / 2548 % 3, n / 7644 % 2, n / 15288 % 2, n / 30576 % 3, n / 91728⟩

set_option maxRecDepth 100000 in
def regsData : List (GalCert.Region 7) := [
  ⟨0, 0, 0, 0, 0, [(1, 0, 0), (-1, 0, 0), (0, 1, 0), (0, -1, 0)], 0, 0, 0, 0, 0, 0, 0, 0,
   [⟨0, 0, 0, 0,
      [[tg 6], [tg 124], [tg 13], [tg 3]],
      [tg 0]⟩,
    ⟨0, 0, 1, 1,
      [[tg 19], [tg 0], [tg 39], [tg 16]],
      [tg 183456]⟩,
    ⟨0, 0, 2, 6,
      [[tg 32], [tg 52], [tg 10], [tg 29]],
      [tg 183508]⟩,
    ⟨0, 0, 3, 2,
      [[tg 45], [tg 71], [tg 13], [tg 65], [tg 42]],
      [tg 183469]⟩,
    ⟨0, 0, 4, 5,
      [[tg 58], [tg 84], [tg 26], [tg 78], [tg 55]],
      [tg 275268]⟩,
    ⟨0, 0, 5, 3,
      [[tg 71], [tg 39], [tg 78], [tg 42], [tg 68]],
      [tg 275223]⟩,
    ⟨0, 0, 6, 4,
      [[tg 84], [tg 52], [tg 65], [tg 55], [tg 81]],
      [tg 183521]⟩]⟩,
  ⟨1, -1, -1, 0, 0, [(1, -1, 0), (-1, 1, 0), (-1, -1, 2)], -1, -1, 2, 2, 0, 0, 0, 0,
   [⟨-1, -1, 0, 7,
      [[tg 558, tg 38778], [tg 2672, tg 5857], [tg 14, tg 3199], [tg 98, tg 3283]],
      [tg 91742, tg 94927]⟩,
    ⟨-1, -1, 1, 6,
      [[tg 571, tg 38791], [tg 1, tg 3186], [tg 40, tg 3225], [tg 111, tg 3296]],
      [tg 183496, tg 186681]⟩,
    ⟨-1, -1, 2, 2,
      [[tg 584, tg 38804], [tg 53, tg 3238], [tg 6, tg 8202], [tg 124, tg 3309]],
      [tg 91734, tg 99930]⟩,
    ⟨-1, -1, 3, 5,
      [[tg 597, tg 38817], [tg 623, tg 38843], [tg 14, tg 3199], [tg 66, tg 3251], [tg 137, tg 3322]],
      [tg 91794, tg 94979]⟩,
    ⟨-1, -1, 4, 3,
      [[tg 610, tg 38830], [tg 636, tg 38856], [tg 27, tg 3212], [tg 79, tg 3264], [tg 150, tg 3335]],
      [tg 91755, tg 94940]⟩,
    ⟨-1, -1, 5, 4,
      [[tg 623, tg 38843], [tg 40, tg 3225], [tg 79, tg 3264], [tg 137, tg 3322], [tg 163, tg 3348]],
      [tg 183535, tg 186720]⟩,
    ⟨-1, -1, 6, 3,
      [[tg 636, tg 38856], [tg 53, tg 3238], [tg 66, tg 3251], [tg 150, tg 3335], [tg 176, tg 3361]],
      [tg 91878, tg 95063]⟩]⟩,
  ⟨1, 1, -1, 0, 0, [(1, 1, 0), (-1, -1, 0), (1, -1, 2)], 1, -1, 2, 2, 0, 0, 0, 0,
   [⟨1, -1, 0, 7,
      [[tg 98, tg 38318], [tg 30700, tg 68920], [tg 15, tg 3200], [tg 8, tg 3193]],
      [tg 91743, tg 94928]⟩,
    ⟨1, -1, 1, 6,
      [[tg 111, tg 38331], [tg 2, tg 3187], [tg 41, tg 3226], [tg 21, tg 3206]],
      [tg 183497, tg 186682]⟩,
    ⟨1, -1, 2, 2,
      [[tg 124, tg 38344], [tg 54, tg 3239], [tg 3, tg 645], [tg 34, tg 3219]],
      [tg 275308, tg 313528]⟩,
    ⟨1, -1, 3, 5,
      [[tg 137, tg 38357], [tg 163, tg 38383], [tg 15, tg 3200], [tg 67, tg 3252], [tg 47, tg 3232]],
      [tg 275347, tg 313567]⟩,
    ⟨1, -1, 4, 3,
      [[tg 150, tg 38370], [tg 176, tg 38396], [tg 28, tg 3213], [tg 80, tg 3265], [tg 60, tg 3245]],
      [tg 367062, tg 405282]⟩,
    ⟨1, -1, 5, 5,
      [[tg 163, tg 38383], [tg 41, tg 3226], [tg 80, tg 3265], [tg 47, tg 3232], [tg 73, tg 3258]],
      [tg 367075, tg 405295]⟩,
    ⟨1, -1, 6, 4,
      [[tg 176, tg 38396], [tg 54, tg 3239], [tg 67, tg 3252], [tg 60, tg 3245], [tg 86, tg 3271]],
      [tg 367088, tg 405308]⟩]⟩,
  ⟨1, 7, 0, 0, 0, [(0, 1, 0), (0, -1, 0), (1, 0, 1)], 1, 0, 1, 7, 0, 0, 0, 0,
   [⟨1, 0, 0, 1,
      [[tg 0, tg 1186], [tg 28, tg 8224], [tg 16, tg 3201], [tg 94, tg 3279]],
      [tg 275184, tg 276370]⟩,
    ⟨1, 0, 1, 2,
      [[tg 13, tg 1199], [tg 3, tg 3188], [tg 42, tg 3227], [tg 107, tg 3292]],
      [tg 275197, tg 276383]⟩,
    ⟨1, 0, 2, 6,
      [[tg 26, tg 1212], [tg 55, tg 3240], [tg 4, tg 1192], [tg 120, tg 3305]],
      [tg 183511, tg 276396]⟩,
    ⟨1, 0, 3, 3,
      [[tg 39, tg 1225], [tg 65, tg 1251], [tg 16, tg 3201], [tg 68, tg 3253], [tg 133, tg 3318]],
      [tg 366951, tg 368137]⟩,
    ⟨1, 0, 4, 5,
      [[tg 52, tg 1238], [tg 78, tg 1264], [tg 29, tg 3214], [tg 81, tg 3266], [tg 146, tg 3331]],
      [tg 275262, tg 368150]⟩,
    ⟨1, 0, 5, 4,
      [[tg 65, tg 1251], [tg 42, tg 3227], [tg 81, tg 3266], [tg 133, tg 3318], [tg 159, tg 3344]],
      [tg 366977, tg 368163]⟩,
    ⟨1, 0, 6, 5,
      [[tg 78, tg 1264], [tg 55, tg 3240], [tg 68, tg 3253], [tg 146, tg 3331], [tg 172, tg 3357]],
      [tg 366990, tg 368176]⟩,
    ⟨2, 0, 0, 2,
      [[tg 3, tg 3188], [tg 34, tg 38254], [tg 107, tg 3292], [tg 185, tg 3370]],
      [tg 275187, tg 278372]⟩,
    ⟨2, 0, 1, 3,
      [[tg 16, tg 3201], [tg 94, tg 3279], [tg 133, tg 3318], [tg 198, tg 3383]],
      [tg 275200, tg 278385]⟩,
    ⟨2, 0, 2, 7,
      [[tg 29, tg 3214], [tg 146, tg 3331], [tg 9, tg 3194], [tg 211, tg 3396]],
      [tg 275213, tg 278398]⟩,
    ⟨2, 0, 3, 4,
      [[tg 42, tg 3227], [tg 68, tg 3253], [tg 107, tg 3292], [tg 159, tg 3344], [tg 224, tg 3409]],
      [tg 366954, tg 370139]⟩,
    ⟨2, 0, 4, 6,
      [[tg 55, tg 3240], [tg 81, tg 3266], [tg 120, tg 3305], [tg 172, tg 3357], [tg 237, tg 3422]],
      [tg 366967, tg 370152]⟩,
    ⟨2, 0, 5, 5,
      [[tg 68, tg 3253], [tg 133, tg 3318], [tg 172, tg 3357], [tg 224, tg 3409], [tg 250, tg 3435]],
      [tg 366980, tg 370165]⟩,
    ⟨2, 0, 6, 6,
      [[tg 81, tg 3266], [tg 146, tg 3331], [tg 159, tg 3344], [tg 237, tg 3422], [tg 263, tg 3448]],
      [tg 366993, tg 370178]⟩,
    ⟨3, 0, 0, 3,
      [[tg 94, tg 3279], [tg 125, tg 38345], [tg 198, tg 3383], [tg 276, tg 3461]],
      [tg 275278, tg 278463]⟩,
    ⟨3, 0, 1, 4,
      [[tg 107, tg 3292], [tg 185, tg 3370], [tg 224, tg 3409], [tg 289, tg 3474]],
      [tg 275291, tg 278476]⟩,
    ⟨3, 0, 2, 8,
      [[tg 120, tg 3305], [tg 237, tg 3422], [tg 100, tg 3285], [tg 302, tg 3487]],
      [tg 275304, tg 278489]⟩,
    ⟨3, 0, 3, 5,
      [[tg 133, tg 3318], [tg 159, tg 3344], [tg 198, tg 3383], [tg 250, tg 3435], [tg 315, tg 3500]],
      [tg 367045, tg 370230]⟩,
    ⟨3, 0, 4, 7,
      [[tg 146, tg 3331], [tg 172, tg 3357], [tg 211, tg 3396], [tg 263, tg 3448], [tg 328, tg 3513]],
      [tg 367058, tg 370243]⟩,
    ⟨3, 0, 5, 6,
      [[tg 159, tg 3344], [tg 224, tg 3409], [tg 263, tg 3448], [tg 315, tg 3500], [tg 341, tg 3526]],
      [tg 367071, tg 370256]⟩,
    ⟨3, 0, 6, 7,
      [[tg 172, tg 3357], [tg 237, tg 3422], [tg 250, tg 3435], [tg 328, tg 3513], [tg 354, tg 3539]],
      [tg 367084, tg 370269]⟩,
    ⟨4, 0, 0, 4,
      [[tg 185, tg 3370], [tg 216, tg 38436], [tg 289, tg 3474], [tg 367, tg 3552]],
      [tg 275369, tg 278554]⟩,
    ⟨4, 0, 1, 5,
      [[tg 198, tg 3383], [tg 276, tg 3461], [tg 315, tg 3500], [tg 380, tg 3565]],
      [tg 275382, tg 278567]⟩,
    ⟨4, 0, 2, 9,
      [[tg 211, tg 3396], [tg 328, tg 3513], [tg 191, tg 3376], [tg 393, tg 3578]],
      [tg 275395, tg 278580]⟩,
    ⟨4, 0, 3, 6,
      [[tg 224, tg 3409], [tg 250, tg 3435], [tg 289, tg 3474], [tg 341, tg 3526], [tg 406, tg 3591]],
      [tg 367136, tg 370321]⟩,
    ⟨4, 0, 4, 8,
      [[tg 237, tg 3422], [tg 263, tg 3448], [tg 302, tg 3487], [tg 354, tg 3539], [tg 419, tg 3604]],
      [tg 367149, tg 370334]⟩,
    ⟨4, 0, 5, 7,
      [[tg 250, tg 3435], [tg 315, tg 3500], [tg 354, tg 3539], [tg 406, tg 3591], [tg 432, tg 3617]],
      [tg 367162, tg 370347]⟩,
    ⟨4, 0, 6, 8,
      [[tg 263, tg 3448], [tg 328, tg 3513], [tg 341, tg 3526], [tg 419, tg 3604], [tg 445, tg 3630]],
      [tg 367175, tg 370360]⟩,
    ⟨5, 0, 0, 5,
      [[tg 276, tg 3461], [tg 307, tg 38527], [tg 380, tg 3565], [tg 458, tg 3643]],
      [tg 275460, tg 278645]⟩,
    ⟨5, 0, 1, 6,
      [[tg 289, tg 3474], [tg 367, tg 3552], [tg 406, tg 3591], [tg 471, tg 3656]],
      [tg 275473, tg 278658]⟩,
    ⟨5, 0, 2, 10,
      [[tg 302, tg 3487], [tg 419, tg 3604], [tg 282, tg 3467], [tg 484, tg 3669]],
      [tg 275486, tg 278671]⟩,
    ⟨5, 0, 3, 7,
      [[tg 315, tg 3500], [tg 341, tg 3526], [tg 380, tg 3565], [tg 432, tg 3617], [tg 497, tg 3682]],
      [tg 367227, tg 370412]⟩,
    ⟨5, 0, 4, 9,
      [[tg 328, tg 3513], [tg 354, tg 3539], [tg 393, tg 3578], [tg 445, tg 3630], [tg 510, tg 3695]],
      [tg 367240, tg 370425]⟩,
    ⟨5, 0, 5, 8,
      [[tg 341, tg 3526], [tg 406, tg 3591], [tg 445, tg 3630], [tg 497, tg 3682], [tg 523, tg 3708]],
      [tg 367253, tg 370438]⟩,
    ⟨5, 0, 6, 9,
      [[tg 354, tg 3539], [tg 419, tg 3604], [tg 432, tg 3617], [tg 510, tg 3695], [tg 536, tg 3721]],
      [tg 367266, tg 370451]⟩,
    ⟨6, 0, 0, 6,
      [[tg 367, tg 3552], [tg 398, tg 38618], [tg 471, tg 3656], [tg 549, tg 3734]],
      [tg 275551, tg 278736]⟩,
    ⟨6, 0, 1, 7,
      [[tg 380, tg 3565], [tg 458, tg 3643], [tg 497, tg 3682], [tg 562, tg 3747]],
      [tg 275564, tg 278749]⟩,
    ⟨6, 0, 2, 11,
      [[tg 393, tg 3578], [tg 510, tg 3695], [tg 373, tg 3558], [tg 575, tg 3760]],
      [tg 275577, tg 278762]⟩,
    ⟨6, 0, 3, 8,
      [[tg 406, tg 3591], [tg 432, tg 3617], [tg 471, tg 3656], [tg 523, tg 3708], [tg 588, tg 3773]],
      [tg 367318, tg 370503]⟩,
    ⟨6, 0, 4, 10,
      [[tg 419, tg 3604], [tg 445, tg 3630], [tg 484, tg 3669], [tg 536, tg 3721], [tg 601, tg 3786]],
      [tg 367331, tg 370516]⟩,
    ⟨6, 0, 5, 9,
      [[tg 432, tg 3617], [tg 497, tg 3682], [tg 536, tg 3721], [tg 588, tg 3773], [tg 614, tg 3799]],
      [tg 367344, tg 370529]⟩,
    ⟨6, 0, 6, 10,
      [[tg 445, tg 3630], [tg 510, tg 3695], [tg 523, tg 3708], [tg 601, tg 3786], [tg 627, tg 3812]],
      [tg 367357, tg 370542]⟩,
    ⟨7, 0, 0, 7,
      [[tg 458, tg 3643], [tg 489, tg 38709], [tg 562, tg 3747], [tg 2551, tg 5736]],
      [tg 275642, tg 278827]⟩,
    ⟨7, 0, 1, 8,
      [[tg 471, tg 3656], [tg 549, tg 3734], [tg 588, tg 3773], [tg 2564, tg 5749]],
      [tg 275655, tg 278840]⟩,
    ⟨7, 0, 2, 12,
      [[tg 484, tg 3669], [tg 601, tg 3786], [tg 464, tg 3649], [tg 2577, tg 5762]],
      [tg 275668, tg 278853]⟩,
    ⟨7, 0, 3, 9,
      [[tg 497, tg 3682], [tg 523, tg 3708], [tg 562, tg 3747], [tg 614, tg 3799], [tg 2590, tg 5775]],
      [tg 367409, tg 370594]⟩,
    ⟨7, 0, 4, 11,
      [[tg 510, tg 3695], [tg 536, tg 3721], [tg 575, tg 3760], [tg 627, tg 3812], [tg 2603, tg 5788]],
      [tg 367422, tg 370607]⟩,
    ⟨7, 0, 5, 10,
      [[tg 523, tg 3708], [tg 588, tg 3773], [tg 627, tg 3812], [tg 2590, tg 5775], [tg 2616, tg 5801]],
      [tg 367435, tg 370620]⟩,
    ⟨7, 0, 6, 11,
      [[tg 536, tg 3721], [tg 601, tg 3786], [tg 614, tg 3799], [tg 2603, tg 5788], [tg 2629, tg 5814]],
      [tg 367448, tg 370633]⟩]⟩,
  ⟨1, 1, 1, 0, 0, [(-1, 1, 0), (1, -1, 0), (1, 1, 2)], 1, 1, 2, 2, 0, 0, 0, 0,
   [⟨1, 1, 0, 7,
      [[tg 10, tg 3195], [tg 29, tg 7679], [tg 17, tg 3202], [tg 9, tg 38229]],
      [tg 183485, tg 191135]⟩,
    ⟨1, 1, 1, 8,
      [[tg 23, tg 3208], [tg 4, tg 3189], [tg 43, tg 3228], [tg 22, tg 38242]],
      [tg 183460, tg 186645]⟩,
    ⟨1, 1, 2, 13,
      [[tg 36, tg 3221], [tg 56, tg 3241], [tg 2558, tg 5743], [tg 35, tg 38255]],
      [tg 183512, tg 186697]⟩,
    ⟨1, 1, 3, 9,
      [[tg 49, tg 3234], [tg 75, tg 3260], [tg 17, tg 3202], [tg 69, tg 3254], [tg 48, tg 38268]],
      [tg 183473, tg 186658]⟩,
    ⟨1, 1, 4, 12,
      [[tg 62, tg 3247], [tg 88, tg 3273], [tg 30, tg 3215], [tg 82, tg 3267], [tg 61, tg 38281]],
      [tg 275272, tg 278457]⟩,
    ⟨1, 1, 5, 10,
      [[tg 75, tg 3260], [tg 43, tg 3228], [tg 82, tg 3267], [tg 48, tg 38268], [tg 74, tg 38294]],
      [tg 275227, tg 278412]⟩,
    ⟨1, 1, 6, 11,
      [[tg 88, tg 3273], [tg 56, tg 3241], [tg 69, tg 3254], [tg 61, tg 38281], [tg 87, tg 38307]],
      [tg 183525, tg 186710]⟩]⟩,
  ⟨1, -1, 1, 0, 0, [(-1, -1, 0), (1, 1, 0), (-1, 1, 2)], -1, 1, 2, 2, 0, 0, 0, 0,
   [⟨-1, 1, 0, 7,
      [[tg 557, tg 3742], [tg 32, tg 1220], [tg 18, tg 3203], [tg 10, tg 38230]],
      [tg 183488, tg 184676]⟩,
    ⟨-1, 1, 1, 8,
      [[tg 570, tg 3755], [tg 5, tg 3190], [tg 44, tg 3229], [tg 23, tg 38243]],
      [tg 183461, tg 186646]⟩,
    ⟨-1, 1, 2, 13,
      [[tg 583, tg 3768], [tg 57, tg 3242], [tg 30586, tg 68806], [tg 36, tg 38256]],
      [tg 183513, tg 186698]⟩,
    ⟨-1, 1, 3, 9,
      [[tg 596, tg 3781], [tg 622, tg 3807], [tg 18, tg 3203], [tg 70, tg 3255], [tg 49, tg 38269]],
      [tg 183474, tg 186659]⟩,
    ⟨-1, 1, 4, 12,
      [[tg 609, tg 3794], [tg 635, tg 3820], [tg 31, tg 3216], [tg 83, tg 3268], [tg 62, tg 38282]],
      [tg 275819, tg 279004]⟩,
    ⟨-1, 1, 5, 10,
      [[tg 622, tg 3807], [tg 44, tg 3229], [tg 83, tg 3268], [tg 49, tg 38269], [tg 75, tg 38295]],
      [tg 275228, tg 278413]⟩,
    ⟨-1, 1, 6, 11,
      [[tg 635, tg 3820], [tg 57, tg 3242], [tg 70, tg 3255], [tg 62, tg 38282], [tg 88, tg 38308]],
      [tg 183526, tg 186711]⟩]⟩,
  ⟨1, -7, 0, 0, 0, [(0, -1, 0), (0, 1, 0), (-1, 0, 1)], -1, 0, 1, 7, 0, 0, 0, 0,
   [⟨-1, 0, 0, 1,
      [[tg 97, tg 3282], [tg 27, tg 675], [tg 19, tg 3204], [tg 0, tg 1189]],
      [tg 0, tg 1189]⟩,
    ⟨-1, 0, 1, 2,
      [[tg 110, tg 3295], [tg 6, tg 3191], [tg 45, tg 3230], [tg 13, tg 1202]],
      [tg 183462, tg 186647]⟩,
    ⟨-1, 0, 2, 6,
      [[tg 123, tg 3308], [tg 58, tg 3243], [tg 5, tg 7655], [tg 26, tg 1215]],
      [tg 183514, tg 186699]⟩,
    ⟨-1, 0, 3, 3,
      [[tg 136, tg 3321], [tg 162, tg 3347], [tg 19, tg 3204], [tg 71, tg 3256], [tg 39, tg 1228]],
      [tg 183475, tg 186660]⟩,
    ⟨-1, 0, 4, 5,
      [[tg 149, tg 3334], [tg 175, tg 3360], [tg 32, tg 3217], [tg 84, tg 3269], [tg 52, tg 1241]],
      [tg 91812, tg 94997]⟩,
    ⟨-1, 0, 5, 3,
      [[tg 162, tg 3347], [tg 45, tg 3230], [tg 84, tg 3269], [tg 39, tg 1228], [tg 65, tg 1254]],
      [tg 91767, tg 92956]⟩,
    ⟨-1, 0, 6, 4,
      [[tg 175, tg 3360], [tg 58, tg 3243], [tg 71, tg 3256], [tg 52, tg 1241], [tg 78, tg 1267]],
      [tg 183527, tg 186712]⟩,
    ⟨-2, 0, 0, 2,
      [[tg 188, tg 3373], [tg 584, tg 3769], [tg 110, tg 3295], [tg 6, tg 3191]],
      [tg 6, tg 3191]⟩,
    ⟨-2, 0, 1, 3,
      [[tg 201, tg 3386], [tg 97, tg 3282], [tg 136, tg 3321], [tg 19, tg 3204]],
      [tg 183553, tg 186738]⟩,
    ⟨-2, 0, 2, 7,
      [[tg 214, tg 3399], [tg 149, tg 3334], [tg 557, tg 38777], [tg 32, tg 3217]],
      [tg 183605, tg 186790]⟩,
    ⟨-2, 0, 3, 4,
      [[tg 227, tg 3412], [tg 253, tg 3438], [tg 110, tg 3295], [tg 162, tg 3347], [tg 45, tg 3230]],
      [tg 183566, tg 186751]⟩,
    ⟨-2, 0, 4, 6,
      [[tg 240, tg 3425], [tg 266, tg 3451], [tg 123, tg 3308], [tg 175, tg 3360], [tg 58, tg 3243]],
      [tg 91903, tg 95088]⟩,
    ⟨-2, 0, 5, 4,
      [[tg 253, tg 3438], [tg 136, tg 3321], [tg 175, tg 3360], [tg 45, tg 3230], [tg 71, tg 3256]],
      [tg 91773, tg 94958]⟩,
    ⟨-2, 0, 6, 5,
      [[tg 266, tg 3451], [tg 149, tg 3334], [tg 162, tg 3347], [tg 58, tg 3243], [tg 84, tg 3269]],
      [tg 183618, tg 186803]⟩,
    ⟨-3, 0, 0, 3,
      [[tg 279, tg 3464], [tg 493, tg 3678], [tg 201, tg 3386], [tg 97, tg 3282]],
      [tg 97, tg 3282]⟩,
    ⟨-3, 0, 1, 4,
      [[tg 292, tg 3477], [tg 188, tg 3373], [tg 227, tg 3412], [tg 110, tg 3295]],
      [tg 183644, tg 186829]⟩,
    ⟨-3, 0, 2, 8,
      [[tg 305, tg 3490], [tg 240, tg 3425], [tg 466, tg 38686], [tg 123, tg 3308]],
      [tg 183696, tg 186881]⟩,
    ⟨-3, 0, 3, 5,
      [[tg 318, tg 3503], [tg 344, tg 3529], [tg 201, tg 3386], [tg 253, tg 3438], [tg 136, tg 3321]],
      [tg 183657, tg 186842]⟩,
    ⟨-3, 0, 4, 7,
      [[tg 331, tg 3516], [tg 357, tg 3542], [tg 214, tg 3399], [tg 266, tg 3451], [tg 149, tg 3334]],
      [tg 91994, tg 95179]⟩,
    ⟨-3, 0, 5, 5,
      [[tg 344, tg 3529], [tg 227, tg 3412], [tg 266, tg 3451], [tg 136, tg 3321], [tg 162, tg 3347]],
      [tg 91864, tg 95049]⟩,
    ⟨-3, 0, 6, 6,
      [[tg 357, tg 3542], [tg 240, tg 3425], [tg 253, tg 3438], [tg 149, tg 3334], [tg 175, tg 3360]],
      [tg 183709, tg 186894]⟩,
    ⟨-4, 0, 0, 4,
      [[tg 370, tg 3555], [tg 402, tg 3587], [tg 292, tg 3477], [tg 188, tg 3373]],
      [tg 188, tg 3373]⟩,
    ⟨-4, 0, 1, 5,
      [[tg 383, tg 3568], [tg 279, tg 3464], [tg 318, tg 3503], [tg 201, tg 3386]],
      [tg 183735, tg 186920]⟩,
    ⟨-4, 0, 2, 9,
      [[tg 396, tg 3581], [tg 331, tg 3516], [tg 375, tg 38595], [tg 214, tg 3399]],
      [tg 183787, tg 186972]⟩,
    ⟨-4, 0, 3, 6,
      [[tg 409, tg 3594], [tg 435, tg 3620], [tg 292, tg 3477], [tg 344, tg 3529], [tg 227, tg 3412]],
      [tg 183748, tg 186933]⟩,
    ⟨-4, 0, 4, 8,
      [[tg 422, tg 3607], [tg 448, tg 3633], [tg 305, tg 3490], [tg 357, tg 3542], [tg 240, tg 3425]],
      [tg 92085, tg 95270]⟩,
    ⟨-4, 0, 5, 6,
      [[tg 435, tg 3620], [tg 318, tg 3503], [tg 357, tg 3542], [tg 227, tg 3412], [tg 253, tg 3438]],
      [tg 91955, tg 95140]⟩,
    ⟨-4, 0, 6, 7,
      [[tg 448, tg 3633], [tg 331, tg 3516], [tg 344, tg 3529], [tg 240, tg 3425], [tg 266, tg 3451]],
      [tg 183800, tg 186985]⟩,
    ⟨-5, 0, 0, 5,
      [[tg 461, tg 3646], [tg 311, tg 3496], [tg 383, tg 3568], [tg 279, tg 3464]],
      [tg 279, tg 3464]⟩,
    ⟨-5, 0, 1, 6,
      [[tg 474, tg 3659], [tg 370, tg 3555], [tg 409, tg 3594], [tg 292, tg 3477]],
      [tg 183826, tg 187011]⟩,
    ⟨-5, 0, 2, 10,
      [[tg 487, tg 3672], [tg 422, tg 3607], [tg 284, tg 38504], [tg 305, tg 3490]],
      [tg 183878, tg 187063]⟩,
    ⟨-5, 0, 3, 7,
      [[tg 500, tg 3685], [tg 526, tg 3711], [tg 383, tg 3568], [tg 435, tg 3620], [tg 318, tg 3503]],
      [tg 183839, tg 187024]⟩,
    ⟨-5, 0, 4, 9,
      [[tg 513, tg 3698], [tg 539, tg 3724], [tg 396, tg 3581], [tg 448, tg 3633], [tg 331, tg 3516]],
      [tg 92176, tg 95361]⟩,
    ⟨-5, 0, 5, 7,
      [[tg 526, tg 3711], [tg 409, tg 3594], [tg 448, tg 3633], [tg 318, tg 3503], [tg 344, tg 3529]],
      [tg 92046, tg 95231]⟩,
    ⟨-5, 0, 6, 8,
      [[tg 539, tg 3724], [tg 422, tg 3607], [tg 435, tg 3620], [tg 331, tg 3516], [tg 357, tg 3542]],
      [tg 183891, tg 187076]⟩,
    ⟨-6, 0, 0, 6,
      [[tg 552, tg 3737], [tg 220, tg 3405], [tg 474, tg 3659], [tg 370, tg 3555]],
      [tg 370, tg 3555]⟩,
    ⟨-6, 0, 1, 7,
      [[tg 565, tg 3750], [tg 461, tg 3646], [tg 500, tg 3685], [tg 383, tg 3568]],
      [tg 183917, tg 187102]⟩,
    ⟨-6, 0, 2, 11,
      [[tg 578, tg 3763], [tg 513, tg 3698], [tg 193, tg 38413], [tg 396, tg 3581]],
      [tg 183969, tg 187154]⟩,
    ⟨-6, 0, 3, 8,
      [[tg 591, tg 3776], [tg 617, tg 3802], [tg 474, tg 3659], [tg 526, tg 3711], [tg 409, tg 3594]],
      [tg 183930, tg 187115]⟩,
    ⟨-6, 0, 4, 10,
      [[tg 604, tg 3789], [tg 630, tg 3815], [tg 487, tg 3672], [tg 539, tg 3724], [tg 422, tg 3607]],
      [tg 92267, tg 95452]⟩,
    ⟨-6, 0, 5, 8,
      [[tg 617, tg 3802], [tg 500, tg 3685], [tg 539, tg 3724], [tg 409, tg 3594], [tg 435, tg 3620]],
      [tg 92137, tg 95322]⟩,
    ⟨-6, 0, 6, 9,
      [[tg 630, tg 3815], [tg 513, tg 3698], [tg 526, tg 3711], [tg 422, tg 3607], [tg 448, tg 3633]],
      [tg 183982, tg 187167]⟩,
    ⟨-7, 0, 0, 7,
      [[tg 2554, tg 5739], [tg 129, tg 3314], [tg 565, tg 3750], [tg 461, tg 3646]],
      [tg 461, tg 3646]⟩,
    ⟨-7, 0, 1, 8,
      [[tg 2567, tg 5752], [tg 552, tg 3737], [tg 591, tg 3776], [tg 474, tg 3659]],
      [tg 184008, tg 187193]⟩,
    ⟨-7, 0, 2, 12,
      [[tg 2580, tg 5765], [tg 604, tg 3789], [tg 102, tg 38322], [tg 487, tg 3672]],
      [tg 184060, tg 187245]⟩,
    ⟨-7, 0, 3, 9,
      [[tg 2593, tg 5778], [tg 2619, tg 5804], [tg 565, tg 3750], [tg 617, tg 3802], [tg 500, tg 3685]],
      [tg 184021, tg 187206]⟩,
    ⟨-7, 0, 4, 11,
      [[tg 2606, tg 5791], [tg 2632, tg 5817], [tg 578, tg 3763], [tg 630, tg 3815], [tg 513, tg 3698]],
      [tg 92358, tg 95543]⟩,
    ⟨-7, 0, 5, 9,
      [[tg 2619, tg 5804], [tg 591, tg 3776], [tg 630, tg 3815], [tg 500, tg 3685], [tg 526, tg 3711]],
      [tg 92228, tg 95413]⟩,
    ⟨-7, 0, 6, 10,
      [[tg 2632, tg 5817], [tg 604, tg 3789], [tg 617, tg 3802], [tg 513, tg 3698], [tg 539, tg 3724]],
      [tg 184073, tg 187258]⟩]⟩,
  ⟨2, -1, -1, 1, -1, [(-1, -1, 1), (1, -1, 1)], -1, -1, 1, 2, 1, -1, 1, 2,
   [⟨0, -2, 0, 14,
      [[tg 2646, tg 5831, tg 48510, tg 51695], [tg 33248, tg 36433, tg 79112, tg 82297], [tg 20, tg 3205, tg 45884, tg 49069], [tg 30674, tg 33859, tg 76538, tg 79723]],
      [tg 91748, tg 94933, tg 137612, tg 140797]⟩,
    ⟨0, -2, 1, 13,
      [[tg 2659, tg 5844, tg 48523, tg 51708], [tg 7, tg 3192, tg 45871, tg 49056], [tg 46, tg 3231, tg 45910, tg 49095], [tg 30687, tg 33872, tg 76551, tg 79736]],
      [tg 183502, tg 186687, tg 229366, tg 232551]⟩,
    ⟨0, -2, 2, 8,
      [[tg 2672, tg 5857, tg 48536, tg 51721], [tg 59, tg 3244, tg 45923, tg 49108], [tg 98, tg 3283, tg 45962, tg 49147], [tg 30700, tg 33885, tg 76564, tg 79749]],
      [tg 91826, tg 95011, tg 137690, tg 140875]⟩,
    ⟨0, -2, 3, 12,
      [[tg 2685, tg 5870, tg 48549, tg 51734], [tg 2711, tg 5896, tg 48575, tg 51760], [tg 20, tg 3205, tg 45884, tg 49069], [tg 72, tg 3257, tg 45936, tg 49121], [tg 30713, tg 33898, tg 76577, tg 79762]],
      [tg 277895, tg 281080, tg 323759, tg 326944]⟩,
    ⟨0, -2, 4, 9,
      [[tg 2698, tg 5883, tg 48562, tg 51747], [tg 2724, tg 5909, tg 48588, tg 51773], [tg 33, tg 3218, tg 45897, tg 49082], [tg 85, tg 3270, tg 45949, tg 49134], [tg 30726, tg 33911, tg 76590, tg 79775]],
      [tg 91761, tg 94946, tg 137625, tg 140810]⟩,
    ⟨0, -2, 5, 11,
      [[tg 2711, tg 5896, tg 48575, tg 51760], [tg 46, tg 3231, tg 45910, tg 49095], [tg 85, tg 3270, tg 45949, tg 49134], [tg 30713, tg 33898, tg 76577, tg 79762], [tg 30739, tg 33924, tg 76603, tg 79788]],
      [tg 183541, tg 186726, tg 229405, tg 232590]⟩,
    ⟨0, -2, 6, 10,
      [[tg 2724, tg 5909, tg 48588, tg 51773], [tg 59, tg 3244, tg 45923, tg 49108], [tg 72, tg 3257, tg 45936, tg 49121], [tg 30726, tg 33911, tg 76590, tg 79775], [tg 30752, tg 33937, tg 76616, tg 79801]],
      [tg 275243, tg 278428, tg 321107, tg 324292]⟩,
    ⟨0, -1, 0, 7,
      [[tg 1, tg 3186, tg 15295, tg 18480], [tg 33, tg 3218, tg 45897, tg 49082], [tg 111, tg 3296, tg 45975, tg 49160], [tg 2, tg 644, tg 3824, tg 46508]],
      [tg 91839, tg 95024, tg 137703, tg 140888]⟩,
    ⟨0, -1, 1, 6,
      [[tg 14, tg 3199, tg 15308, tg 18493], [tg 98, tg 3283, tg 45962, tg 49147], [tg 137, tg 3322, tg 46001, tg 49186], [tg 15, tg 657, tg 3837, tg 46521]],
      [tg 183593, tg 186778, tg 229457, tg 232642]⟩,
    ⟨0, -1, 2, 1,
      [[tg 27, tg 3212, tg 15321, tg 18506], [tg 150, tg 3335, tg 46014, tg 49199], [tg 0, tg 638, tg 1276, tg 15932], [tg 28, tg 670, tg 3850, tg 46534]],
      [tg 91728, tg 92366, tg 93004, tg 107660]⟩,
    ⟨0, -1, 3, 5,
      [[tg 40, tg 3225, tg 15334, tg 18519], [tg 66, tg 3251, tg 15360, tg 18545], [tg 111, tg 3296, tg 45975, tg 49160], [tg 163, tg 3348, tg 46027, tg 49212], [tg 41, tg 683, tg 3863, tg 46547]],
      [tg 275250, tg 278435, tg 290544, tg 293729]⟩,
    ⟨0, -1, 4, 2,
      [[tg 53, tg 3238, tg 15347, tg 18532], [tg 79, tg 3264, tg 15373, tg 18558], [tg 124, tg 3309, tg 45988, tg 49173], [tg 176, tg 3361, tg 46040, tg 49225], [tg 54, tg 696, tg 3876, tg 46560]],
      [tg 91852, tg 95037, tg 137716, tg 140901]⟩,
    ⟨0, -1, 5, 4,
      [[tg 66, tg 3251, tg 15360, tg 18545], [tg 137, tg 3322, tg 46001, tg 49186], [tg 176, tg 3361, tg 46040, tg 49225], [tg 41, tg 683, tg 3863, tg 46547], [tg 67, tg 709, tg 3889, tg 46573]],
      [tg 183632, tg 186817, tg 229496, tg 232681]⟩,
    ⟨0, -1, 6, 3,
      [[tg 79, tg 3264, tg 15373, tg 18558], [tg 150, tg 3335, tg 46014, tg 49199], [tg 163, tg 3348, tg 46027, tg 49212], [tg 54, tg 696, tg 3876, tg 46560], [tg 80, tg 722, tg 3902, tg 46586]],
      [tg 275334, tg 278519, tg 321198, tg 324383]⟩]⟩,
  ⟨2, 1, -1, 7, 0, [(0, -7, 1), (1, 1, 1)], 0, -7, 1, 7, 1, 1, 1, 7,
   [⟨2, -1, 0, 8,
      [[tg 2, tg 3187, tg 15842, tg 19027], [tg 2576, tg 5761, tg 18416, tg 21601], [tg 21, tg 3206, tg 45885, tg 49070], [tg 99, tg 3284, tg 45963, tg 49148]],
      [tg 275186, tg 278371, tg 291026, tg 294211]⟩,
    ⟨2, -1, 1, 7,
      [[tg 15, tg 3200, tg 15855, tg 19040], [tg 8, tg 3193, tg 45872, tg 49057], [tg 47, tg 3232, tg 45911, tg 49096], [tg 112, tg 3297, tg 45976, tg 49161]],
      [tg 275199, tg 278384, tg 291039, tg 294224]⟩,
    ⟨2, -1, 2, 3,
      [[tg 28, tg 3213, tg 15868, tg 19053], [tg 60, tg 3245, tg 45924, tg 49109], [tg 94, tg 736, tg 3916, tg 46600], [tg 125, tg 3310, tg 45989, tg 49174]],
      [tg 275212, tg 278397, tg 291052, tg 294237]⟩,
    ⟨2, -1, 3, 6,
      [[tg 41, tg 3226, tg 15881, tg 19066], [tg 67, tg 3252, tg 15907, tg 19092], [tg 21, tg 3206, tg 45885, tg 49070], [tg 73, tg 3258, tg 45937, tg 49122], [tg 138, tg 3323, tg 46002, tg 49187]],
      [tg 366953, tg 370138, tg 382793, tg 385978]⟩,
    ⟨2, -1, 4, 4,
      [[tg 54, tg 3239, tg 15894, tg 19079], [tg 80, tg 3265, tg 15920, tg 19105], [tg 34, tg 3219, tg 45898, tg 49083], [tg 86, tg 3271, tg 45950, tg 49135], [tg 151, tg 3336, tg 46015, tg 49200]],
      [tg 366966, tg 370151, tg 382806, tg 385991]⟩,
    ⟨2, -1, 5, 6,
      [[tg 67, tg 3252, tg 15907, tg 19092], [tg 47, tg 3232, tg 45911, tg 49096], [tg 86, tg 3271, tg 45950, tg 49135], [tg 138, tg 3323, tg 46002, tg 49187], [tg 164, tg 3349, tg 46028, tg 49213]],
      [tg 366979, tg 370164, tg 382819, tg 386004]⟩,
    ⟨2, -1, 6, 5,
      [[tg 80, tg 3265, tg 15920, tg 19105], [tg 60, tg 3245, tg 45924, tg 49109], [tg 73, tg 3258, tg 45937, tg 49122], [tg 151, tg 3336, tg 46015, tg 49200], [tg 177, tg 3362, tg 46041, tg 49226]],
      [tg 366992, tg 370177, tg 382832, tg 386017]⟩,
    ⟨3, -1, 0, 9,
      [[tg 8, tg 3193, tg 45872, tg 49057], [tg 2582, tg 5767, tg 48446, tg 51631], [tg 112, tg 3297, tg 45976, tg 49161], [tg 190, tg 3375, tg 46054, tg 49239]],
      [tg 275192, tg 278377, tg 321056, tg 324241]⟩,
    ⟨3, -1, 1, 8,
      [[tg 21, tg 3206, tg 45885, tg 49070], [tg 99, tg 3284, tg 45963, tg 49148], [tg 138, tg 3323, tg 46002, tg 49187], [tg 203, tg 3388, tg 46067, tg 49252]],
      [tg 275205, tg 278390, tg 321069, tg 324254]⟩,
    ⟨3, -1, 2, 4,
      [[tg 34, tg 3219, tg 45898, tg 49083], [tg 151, tg 3336, tg 46015, tg 49200], [tg 185, tg 827, tg 4007, tg 46691], [tg 216, tg 3401, tg 46080, tg 49265]],
      [tg 275218, tg 278403, tg 321082, tg 324267]⟩,
    ⟨3, -1, 3, 7,
      [[tg 47, tg 3232, tg 45911, tg 49096], [tg 73, tg 3258, tg 45937, tg 49122], [tg 112, tg 3297, tg 45976, tg 49161], [tg 164, tg 3349, tg 46028, tg 49213], [tg 229, tg 3414, tg 46093, tg 49278]],
      [tg 366959, tg 370144, tg 412823, tg 416008]⟩,
    ⟨3, -1, 4, 5,
      [[tg 60, tg 3245, tg 45924, tg 49109], [tg 86, tg 3271, tg 45950, tg 49135], [tg 125, tg 3310, tg 45989, tg 49174], [tg 177, tg 3362, tg 46041, tg 49226], [tg 242, tg 3427, tg 46106, tg 49291]],
      [tg 366972, tg 370157, tg 412836, tg 416021]⟩,
    ⟨3, -1, 5, 7,
      [[tg 73, tg 3258, tg 45937, tg 49122], [tg 138, tg 3323, tg 46002, tg 49187], [tg 177, tg 3362, tg 46041, tg 49226], [tg 229, tg 3414, tg 46093, tg 49278], [tg 255, tg 3440, tg 46119, tg 49304]],
      [tg 366985, tg 370170, tg 412849, tg 416034]⟩,
    ⟨3, -1, 6, 6,
      [[tg 86, tg 3271, tg 45950, tg 49135], [tg 151, tg 3336, tg 46015, tg 49200], [tg 164, tg 3349, tg 46028, tg 49213], [tg 242, tg 3427, tg 46106, tg 49291], [tg 268, tg 3453, tg 46132, tg 49317]],
      [tg 366998, tg 370183, tg 412862, tg 416047]⟩,
    ⟨4, -1, 0, 10,
      [[tg 99, tg 3284, tg 45963, tg 49148], [tg 2673, tg 5858, tg 48537, tg 51722], [tg 203, tg 3388, tg 46067, tg 49252], [tg 281, tg 3466, tg 46145, tg 49330]],
      [tg 275283, tg 278468, tg 321147, tg 324332]⟩,
    ⟨4, -1, 1, 9,
      [[tg 112, tg 3297, tg 45976, tg 49161], [tg 190, tg 3375, tg 46054, tg 49239], [tg 229, tg 3414, tg 46093, tg 49278], [tg 294, tg 3479, tg 46158, tg 49343]],
      [tg 275296, tg 278481, tg 321160, tg 324345]⟩,
    ⟨4, -1, 2, 5,
      [[tg 125, tg 3310, tg 45989, tg 49174], [tg 242, tg 3427, tg 46106, tg 49291], [tg 276, tg 918, tg 4098, tg 46782], [tg 307, tg 3492, tg 46171, tg 49356]],
      [tg 275309, tg 278494, tg 321173, tg 324358]⟩,
    ⟨4, -1, 3, 8,
      [[tg 138, tg 3323, tg 46002, tg 49187], [tg 164, tg 3349, tg 46028, tg 49213], [tg 203, tg 3388, tg 46067, tg 49252], [tg 255, tg 3440, tg 46119, tg 49304], [tg 320, tg 3505, tg 46184, tg 49369]],
      [tg 367050, tg 370235, tg 412914, tg 416099]⟩,
    ⟨4, -1, 4, 6,
      [[tg 151, tg 3336, tg 46015, tg 49200], [tg 177, tg 3362, tg 46041, tg 49226], [tg 216, tg 3401, tg 46080, tg 49265], [tg 268, tg 3453, tg 46132, tg 49317], [tg 333, tg 3518, tg 46197, tg 49382]],
      [tg 367063, tg 370248, tg 412927, tg 416112]⟩,
    ⟨4, -1, 5, 8,
      [[tg 164, tg 3349, tg 46028, tg 49213], [tg 229, tg 3414, tg 46093, tg 49278], [tg 268, tg 3453, tg 46132, tg 49317], [tg 320, tg 3505, tg 46184, tg 49369], [tg 346, tg 3531, tg 46210, tg 49395]],
      [tg 367076, tg 370261, tg 412940, tg 416125]⟩,
    ⟨4, -1, 6, 7,
      [[tg 177, tg 3362, tg 46041, tg 49226], [tg 242, tg 3427, tg 46106, tg 49291], [tg 255, tg 3440, tg 46119, tg 49304], [tg 333, tg 3518, tg 46197, tg 49382], [tg 359, tg 3544, tg 46223, tg 49408]],
      [tg 367089, tg 370274, tg 412953, tg 416138]⟩,
    ⟨5, -1, 0, 11,
      [[tg 190, tg 3375, tg 46054, tg 49239], [tg 2764, tg 5949, tg 48628, tg 51813], [tg 294, tg 3479, tg 46158, tg 49343], [tg 372, tg 3557, tg 46236, tg 49421]],
      [tg 275374, tg 278559, tg 321238, tg 324423]⟩,
    ⟨5, -1, 1, 10,
      [[tg 203, tg 3388, tg 46067, tg 49252], [tg 281, tg 3466, tg 46145, tg 49330], [tg 320, tg 3505, tg 46184, tg 49369], [tg 385, tg 3570, tg 46249, tg 49434]],
      [tg 275387, tg 278572, tg 321251, tg 324436]⟩,
    ⟨5, -1, 2, 6,
      [[tg 216, tg 3401, tg 46080, tg 49265], [tg 333, tg 3518, tg 46197, tg 49382], [tg 367, tg 1009, tg 4189, tg 46873], [tg 398, tg 3583, tg 46262, tg 49447]],
      [tg 275400, tg 278585, tg 321264, tg 324449]⟩,
    ⟨5, -1, 3, 9,
      [[tg 229, tg 3414, tg 46093, tg 49278], [tg 255, tg 3440, tg 46119, tg 49304], [tg 294, tg 3479, tg 46158, tg 49343], [tg 346, tg 3531, tg 46210, tg 49395], [tg 411, tg 3596, tg 46275, tg 49460]],
      [tg 367141, tg 370326, tg 413005, tg 416190]⟩,
    ⟨5, -1, 4, 7,
      [[tg 242, tg 3427, tg 46106, tg 49291], [tg 268, tg 3453, tg 46132, tg 49317], [tg 307, tg 3492, tg 46171, tg 49356], [tg 359, tg 3544, tg 46223, tg 49408], [tg 424, tg 3609, tg 46288, tg 49473]],
      [tg 367154, tg 370339, tg 413018, tg 416203]⟩,
    ⟨5, -1, 5, 9,
      [[tg 255, tg 3440, tg 46119, tg 49304], [tg 320, tg 3505, tg 46184, tg 49369], [tg 359, tg 3544, tg 46223, tg 49408], [tg 411, tg 3596, tg 46275, tg 49460], [tg 437, tg 3622, tg 46301, tg 49486]],
      [tg 367167, tg 370352, tg 413031, tg 416216]⟩,
    ⟨5, -1, 6, 8,
      [[tg 268, tg 3453, tg 46132, tg 49317], [tg 333, tg 3518, tg 46197, tg 49382], [tg 346, tg 3531, tg 46210, tg 49395], [tg 424, tg 3609, tg 46288, tg 49473], [tg 450, tg 3635, tg 46314, tg 49499]],
      [tg 367180, tg 370365, tg 413044, tg 416229]⟩,
    ⟨6, -1, 0, 12,
      [[tg 281, tg 3466, tg 46145, tg 49330], [tg 2855, tg 6040, tg 48719, tg 51904], [tg 385, tg 3570, tg 46249, tg 49434], [tg 463, tg 3648, tg 46327, tg 49512]],
      [tg 275465, tg 278650, tg 321329, tg 324514]⟩,
    ⟨6, -1, 1, 11,
      [[tg 294, tg 3479, tg 46158, tg 49343], [tg 372, tg 3557, tg 46236, tg 49421], [tg 411, tg 3596, tg 46275, tg 49460], [tg 476, tg 3661, tg 46340, tg 49525]],
      [tg 275478, tg 278663, tg 321342, tg 324527]⟩,
    ⟨6, -1, 2, 7,
      [[tg 307, tg 3492, tg 46171, tg 49356], [tg 424, tg 3609, tg 46288, tg 49473], [tg 458, tg 1100, tg 4280, tg 46964], [tg 489, tg 3674, tg 46353, tg 49538]],
      [tg 275491, tg 278676, tg 321355, tg 324540]⟩,
    ⟨6, -1, 3, 10,
      [[tg 320, tg 3505, tg 46184, tg 49369], [tg 346, tg 3531, tg 46210, tg 49395], [tg 385, tg 3570, tg 46249, tg 49434], [tg 437, tg 3622, tg 46301, tg 49486], [tg 502, tg 3687, tg 46366, tg 49551]],
      [tg 367232, tg 370417, tg 413096, tg 416281]⟩,
    ⟨6, -1, 4, 8,
      [[tg 333, tg 3518, tg 46197, tg 49382], [tg 359, tg 3544, tg 46223, tg 49408], [tg 398, tg 3583, tg 46262, tg 49447], [tg 450, tg 3635, tg 46314, tg 49499], [tg 515, tg 3700, tg 46379, tg 49564]],
      [tg 367245, tg 370430, tg 413109, tg 416294]⟩,
    ⟨6, -1, 5, 10,
      [[tg 346, tg 3531, tg 46210, tg 49395], [tg 411, tg 3596, tg 46275, tg 49460], [tg 450, tg 3635, tg 46314, tg 49499], [tg 502, tg 3687, tg 46366, tg 49551], [tg 528, tg 3713, tg 46392, tg 49577]],
      [tg 367258, tg 370443, tg 413122, tg 416307]⟩,
    ⟨6, -1, 6, 9,
      [[tg 359, tg 3544, tg 46223, tg 49408], [tg 424, tg 3609, tg 46288, tg 49473], [tg 437, tg 3622, tg 46301, tg 49486], [tg 515, tg 3700, tg 46379, tg 49564], [tg 541, tg 3726, tg 46405, tg 49590]],
      [tg 367271, tg 370456, tg 413135, tg 416320]⟩,
    ⟨7, -1, 0, 13,
      [[tg 372, tg 3557, tg 46236, tg 49421], [tg 2946, tg 6131, tg 48810, tg 51995], [tg 476, tg 3661, tg 46340, tg 49525], [tg 554, tg 3739, tg 46418, tg 49603]],
      [tg 275556, tg 278741, tg 321420, tg 324605]⟩,
    ⟨7, -1, 1, 12,
      [[tg 385, tg 3570, tg 46249, tg 49434], [tg 463, tg 3648, tg 46327, tg 49512], [tg 502, tg 3687, tg 46366, tg 49551], [tg 567, tg 3752, tg 46431, tg 49616]],
      [tg 275569, tg 278754, tg 321433, tg 324618]⟩,
    ⟨7, -1, 2, 8,
      [[tg 398, tg 3583, tg 46262, tg 49447], [tg 515, tg 3700, tg 46379, tg 49564], [tg 549, tg 1191, tg 4371, tg 47055], [tg 580, tg 3765, tg 46444, tg 49629]],
      [tg 275582, tg 278767, tg 321446, tg 324631]⟩,
    ⟨7, -1, 3, 11,
      [[tg 411, tg 3596, tg 46275, tg 49460], [tg 437, tg 3622, tg 46301, tg 49486], [tg 476, tg 3661, tg 46340, tg 49525], [tg 528, tg 3713, tg 46392, tg 49577], [tg 593, tg 3778, tg 46457, tg 49642]],
      [tg 367323, tg 370508, tg 413187, tg 416372]⟩,
    ⟨7, -1, 4, 9,
      [[tg 424, tg 3609, tg 46288, tg 49473], [tg 450, tg 3635, tg 46314, tg 49499], [tg 489, tg 3674, tg 46353, tg 49538], [tg 541, tg 3726, tg 46405, tg 49590], [tg 606, tg 3791, tg 46470, tg 49655]],
      [tg 367336, tg 370521, tg 413200, tg 416385]⟩,
    ⟨7, -1, 5, 11,
      [[tg 437, tg 3622, tg 46301, tg 49486], [tg 502, tg 3687, tg 46366, tg 49551], [tg 541, tg 3726, tg 46405, tg 49590], [tg 593, tg 3778, tg 46457, tg 49642], [tg 619, tg 3804, tg 46483, tg 49668]],
      [tg 367349, tg 370534, tg 413213, tg 416398]⟩,
    ⟨7, -1, 6, 10,
      [[tg 450, tg 3635, tg 46314, tg 49499], [tg 515, tg 3700, tg 46379, tg 49564], [tg 528, tg 3713, tg 46392, tg 49577], [tg 606, tg 3791, tg 46470, tg 49655], [tg 632, tg 3817, tg 46496, tg 49681]],
      [tg 367362, tg 370547, tg 413226, tg 416411]⟩,
    ⟨8, -1, 0, 14,
      [[tg 463, tg 3648, tg 46327, tg 49512], [tg 3037, tg 6222, tg 48901, tg 52086], [tg 567, tg 3752, tg 46431, tg 49616], [tg 30584, tg 33769, tg 76448, tg 79633]],
      [tg 275647, tg 278832, tg 321511, tg 324696]⟩,
    ⟨8, -1, 1, 13,
      [[tg 476, tg 3661, tg 46340, tg 49525], [tg 554, tg 3739, tg 46418, tg 49603], [tg 593, tg 3778, tg 46457, tg 49642], [tg 30597, tg 33782, tg 76461, tg 79646]],
      [tg 275660, tg 278845, tg 321524, tg 324709]⟩,
    ⟨8, -1, 2, 9,
      [[tg 489, tg 3674, tg 46353, tg 49538], [tg 606, tg 3791, tg 46470, tg 49655], [tg 2551, tg 31221, tg 6373, tg 77085], [tg 30610, tg 33795, tg 76474, tg 79659]],
      [tg 275673, tg 278858, tg 321537, tg 324722]⟩,
    ⟨8, -1, 3, 12,
      [[tg 502, tg 3687, tg 46366, tg 49551], [tg 528, tg 3713, tg 46392, tg 49577], [tg 567, tg 3752, tg 46431, tg 49616], [tg 619, tg 3804, tg 46483, tg 49668], [tg 30623, tg 33808, tg 76487, tg 79672]],
      [tg 367414, tg 370599, tg 413278, tg 416463]⟩,
    ⟨8, -1, 4, 10,
      [[tg 515, tg 3700, tg 46379, tg 49564], [tg 541, tg 3726, tg 46405, tg 49590], [tg 580, tg 3765, tg 46444, tg 49629], [tg 632, tg 3817, tg 46496, tg 49681], [tg 30636, tg 33821, tg 76500, tg 79685]],
      [tg 367427, tg 370612, tg 413291, tg 416476]⟩,
    ⟨8, -1, 5, 12,
      [[tg 528, tg 3713, tg 46392, tg 49577], [tg 593, tg 3778, tg 46457, tg 49642], [tg 632, tg 3817, tg 46496, tg 49681], [tg 30623, tg 33808, tg 76487, tg 79672], [tg 30649, tg 33834, tg 76513, tg 79698]],
      [tg 367440, tg 370625, tg 413304, tg 416489]⟩,
    ⟨8, -1, 6, 11,
      [[tg 541, tg 3726, tg 46405, tg 49590], [tg 606, tg 3791, tg 46470, tg 49655], [tg 619, tg 3804, tg 46483, tg 49668], [tg 30636, tg 33821, tg 76500, tg 79685], [tg 30662, tg 33847, tg 76526, tg 79711]],
      [tg 367453, tg 370638, tg 413317, tg 416502]⟩]⟩,
  ⟨2, 7, 0, 1, 1, [(1, -1, 1), (0, 7, 1)], 1, -1, 1, 7, 0, 7, 1, 7,
   [⟨2, 1, 0, 8,
      [[tg 4, tg 1192, tg 3826, tg 47056], [tg 120, tg 3305, tg 15414, tg 18599], [tg 22, tg 3207, tg 45886, tg 49071], [tg 100, tg 3285, tg 45964, tg 49149]],
      [tg 275188, tg 276376, tg 279010, tg 322240]⟩,
    ⟨2, 1, 1, 9,
      [[tg 17, tg 1205, tg 3839, tg 47069], [tg 9, tg 3194, tg 45873, tg 49058], [tg 48, tg 3233, tg 45912, tg 49097], [tg 113, tg 3298, tg 45977, tg 49162]],
      [tg 275201, tg 276389, tg 279023, tg 322253]⟩,
    ⟨2, 1, 2, 13,
      [[tg 30, tg 1218, tg 3852, tg 47082], [tg 61, tg 3246, tg 45925, tg 49110], [tg 2552, tg 31768, tg 6374, tg 77632], [tg 126, tg 3311, tg 45990, tg 49175]],
      [tg 183517, tg 276402, tg 229381, tg 322266]⟩,
    ⟨2, 1, 3, 10,
      [[tg 43, tg 1231, tg 3865, tg 47095], [tg 69, tg 1257, tg 3891, tg 47121], [tg 22, tg 3207, tg 45886, tg 49071], [tg 74, tg 3259, tg 45938, tg 49123], [tg 139, tg 3324, tg 46003, tg 49188]],
      [tg 366955, tg 368143, tg 370777, tg 414007]⟩,
    ⟨2, 1, 4, 12,
      [[tg 56, tg 1244, tg 3878, tg 47108], [tg 82, tg 1270, tg 3904, tg 47134], [tg 35, tg 3220, tg 45899, tg 49084], [tg 87, tg 3272, tg 45951, tg 49136], [tg 152, tg 3337, tg 46016, tg 49201]],
      [tg 275266, tg 368156, tg 279088, tg 414020]⟩,
    ⟨2, 1, 5, 11,
      [[tg 69, tg 1257, tg 3891, tg 47121], [tg 48, tg 3233, tg 45912, tg 49097], [tg 87, tg 3272, tg 45951, tg 49136], [tg 139, tg 3324, tg 46003, tg 49188], [tg 165, tg 3350, tg 46029, tg 49214]],
      [tg 366981, tg 368169, tg 370803, tg 414033]⟩,
    ⟨2, 1, 6, 12,
      [[tg 82, tg 1270, tg 3904, tg 47134], [tg 61, tg 3246, tg 45925, tg 49110], [tg 74, tg 3259, tg 45938, tg 49123], [tg 152, tg 3337, tg 46016, tg 49201], [tg 178, tg 3363, tg 46042, tg 49227]],
      [tg 366994, tg 368182, tg 370816, tg 414046]⟩,
    ⟨3, 1, 0, 9,
      [[tg 9, tg 3194, tg 45873, tg 49058], [tg 211, tg 3396, tg 15505, tg 18690], [tg 113, tg 3298, tg 45977, tg 49162], [tg 191, tg 3376, tg 46055, tg 49240]],
      [tg 275193, tg 278378, tg 321057, tg 324242]⟩,
    ⟨3, 1, 1, 10,
      [[tg 22, tg 3207, tg 45886, tg 49071], [tg 100, tg 3285, tg 45964, tg 49149], [tg 139, tg 3324, tg 46003, tg 49188], [tg 204, tg 3389, tg 46068, tg 49253]],
      [tg 275206, tg 278391, tg 321070, tg 324255]⟩,
    ⟨3, 1, 2, 14,
      [[tg 35, tg 3220, tg 45899, tg 49084], [tg 152, tg 3337, tg 46016, tg 49201], [tg 30585, tg 33770, tg 76449, tg 79634], [tg 217, tg 3402, tg 46081, tg 49266]],
      [tg 275219, tg 278404, tg 321083, tg 324268]⟩,
    ⟨3, 1, 3, 11,
      [[tg 48, tg 3233, tg 45912, tg 49097], [tg 74, tg 3259, tg 45938, tg 49123], [tg 113, tg 3298, tg 45977, tg 49162], [tg 165, tg 3350, tg 46029, tg 49214], [tg 230, tg 3415, tg 46094, tg 49279]],
      [tg 366960, tg 370145, tg 412824, tg 416009]⟩,
    ⟨3, 1, 4, 13,
      [[tg 61, tg 3246, tg 45925, tg 49110], [tg 87, tg 3272, tg 45951, tg 49136], [tg 126, tg 3311, tg 45990, tg 49175], [tg 178, tg 3363, tg 46042, tg 49227], [tg 243, tg 3428, tg 46107, tg 49292]],
      [tg 366973, tg 370158, tg 412837, tg 416022]⟩,
    ⟨3, 1, 5, 12,
      [[tg 74, tg 3259, tg 45938, tg 49123], [tg 139, tg 3324, tg 46003, tg 49188], [tg 178, tg 3363, tg 46042, tg 49227], [tg 230, tg 3415, tg 46094, tg 49279], [tg 256, tg 3441, tg 46120, tg 49305]],
      [tg 366986, tg 370171, tg 412850, tg 416035]⟩,
    ⟨3, 1, 6, 13,
      [[tg 87, tg 3272, tg 45951, tg 49136], [tg 152, tg 3337, tg 46016, tg 49201], [tg 165, tg 3350, tg 46029, tg 49214], [tg 243, tg 3428, tg 46107, tg 49292], [tg 269, tg 3454, tg 46133, tg 49318]],
      [tg 366999, tg 370184, tg 412863, tg 416048]⟩,
    ⟨4, 1, 0, 10,
      [[tg 100, tg 3285, tg 45964, tg 49149], [tg 302, tg 3487, tg 15596, tg 18781], [tg 204, tg 3389, tg 46068, tg 49253], [tg 282, tg 3467, tg 46146, tg 49331]],
      [tg 275284, tg 278469, tg 321148, tg 324333]⟩,
    ⟨4, 1, 1, 11,
      [[tg 113, tg 3298, tg 45977, tg 49162], [tg 191, tg 3376, tg 46055, tg 49240], [tg 230, tg 3415, tg 46094, tg 49279], [tg 295, tg 3480, tg 46159, tg 49344]],
      [tg 275297, tg 278482, tg 321161, tg 324346]⟩,
    ⟨4, 1, 2, 15,
      [[tg 126, tg 3311, tg 45990, tg 49175], [tg 243, tg 3428, tg 46107, tg 49292], [tg 30676, tg 33861, tg 76540, tg 79725], [tg 308, tg 3493, tg 46172, tg 49357]],
      [tg 275310, tg 278495, tg 321174, tg 324359]⟩,
    ⟨4, 1, 3, 12,
      [[tg 139, tg 3324, tg 46003, tg 49188], [tg 165, tg 3350, tg 46029, tg 49214], [tg 204, tg 3389, tg 46068, tg 49253], [tg 256, tg 3441, tg 46120, tg 49305], [tg 321, tg 3506, tg 46185, tg 49370]],
      [tg 367051, tg 370236, tg 412915, tg 416100]⟩,
    ⟨4, 1, 4, 14,
      [[tg 152, tg 3337, tg 46016, tg 49201], [tg 178, tg 3363, tg 46042, tg 49227], [tg 217, tg 3402, tg 46081, tg 49266], [tg 269, tg 3454, tg 46133, tg 49318], [tg 334, tg 3519, tg 46198, tg 49383]],
      [tg 367064, tg 370249, tg 412928, tg 416113]⟩,
    ⟨4, 1, 5, 13,
      [[tg 165, tg 3350, tg 46029, tg 49214], [tg 230, tg 3415, tg 46094, tg 49279], [tg 269, tg 3454, tg 46133, tg 49318], [tg 321, tg 3506, tg 46185, tg 49370], [tg 347, tg 3532, tg 46211, tg 49396]],
      [tg 367077, tg 370262, tg 412941, tg 416126]⟩,
    ⟨4, 1, 6, 14,
      [[tg 178, tg 3363, tg 46042, tg 49227], [tg 243, tg 3428, tg 46107, tg 49292], [tg 256, tg 3441, tg 46120, tg 49305], [tg 334, tg 3519, tg 46198, tg 49383], [tg 360, tg 3545, tg 46224, tg 49409]],
      [tg 367090, tg 370275, tg 412954, tg 416139]⟩,
    ⟨5, 1, 0, 11,
      [[tg 191, tg 3376, tg 46055, tg 49240], [tg 393, tg 3578, tg 15687, tg 18872], [tg 295, tg 3480, tg 46159, tg 49344], [tg 373, tg 3558, tg 46237, tg 49422]],
      [tg 275375, tg 278560, tg 321239, tg 324424]⟩,
    ⟨5, 1, 1, 12,
      [[tg 204, tg 3389, tg 46068, tg 49253], [tg 282, tg 3467, tg 46146, tg 49331], [tg 321, tg 3506, tg 46185, tg 49370], [tg 386, tg 3571, tg 46250, tg 49435]],
      [tg 275388, tg 278573, tg 321252, tg 324437]⟩,
    ⟨5, 1, 2, 16,
      [[tg 217, tg 3402, tg 46081, tg 49266], [tg 334, tg 3519, tg 46198, tg 49383], [tg 30767, tg 33952, tg 76631, tg 79816], [tg 399, tg 3584, tg 46263, tg 49448]],
      [tg 275401, tg 278586, tg 321265, tg 324450]⟩,
    ⟨5, 1, 3, 13,
      [[tg 230, tg 3415, tg 46094, tg 49279], [tg 256, tg 3441, tg 46120, tg 49305], [tg 295, tg 3480, tg 46159, tg 49344], [tg 347, tg 3532, tg 46211, tg 49396], [tg 412, tg 3597, tg 46276, tg 49461]],
      [tg 367142, tg 370327, tg 413006, tg 416191]⟩,
    ⟨5, 1, 4, 15,
      [[tg 243, tg 3428, tg 46107, tg 49292], [tg 269, tg 3454, tg 46133, tg 49318], [tg 308, tg 3493, tg 46172, tg 49357], [tg 360, tg 3545, tg 46224, tg 49409], [tg 425, tg 3610, tg 46289, tg 49474]],
      [tg 367155, tg 370340, tg 413019, tg 416204]⟩,
    ⟨5, 1, 5, 14,
      [[tg 256, tg 3441, tg 46120, tg 49305], [tg 321, tg 3506, tg 46185, tg 49370], [tg 360, tg 3545, tg 46224, tg 49409], [tg 412, tg 3597, tg 46276, tg 49461], [tg 438, tg 3623, tg 46302, tg 49487]],
      [tg 367168, tg 370353, tg 413032, tg 416217]⟩,
    ⟨5, 1, 6, 15,
      [[tg 269, tg 3454, tg 46133, tg 49318], [tg 334, tg 3519, tg 46198, tg 49383], [tg 347, tg 3532, tg 46211, tg 49396], [tg 425, tg 3610, tg 46289, tg 49474], [tg 451, tg 3636, tg 46315, tg 49500]],
      [tg 367181, tg 370366, tg 413045, tg 416230]⟩,
    ⟨6, 1, 0, 12,
      [[tg 282, tg 3467, tg 46146, tg 49331], [tg 484, tg 3669, tg 15778, tg 18963], [tg 386, tg 3571, tg 46250, tg 49435], [tg 464, tg 3649, tg 46328, tg 49513]],
      [tg 275466, tg 278651, tg 321330, tg 324515]⟩,
    ⟨6, 1, 1, 13,
      [[tg 295, tg 3480, tg 46159, tg 49344], [tg 373, tg 3558, tg 46237, tg 49422], [tg 412, tg 3597, tg 46276, tg 49461], [tg 477, tg 3662, tg 46341, tg 49526]],
      [tg 275479, tg 278664, tg 321343, tg 324528]⟩,
    ⟨6, 1, 2, 17,
      [[tg 308, tg 3493, tg 46172, tg 49357], [tg 425, tg 3610, tg 46289, tg 49474], [tg 30858, tg 34043, tg 76722, tg 79907], [tg 490, tg 3675, tg 46354, tg 49539]],
      [tg 275492, tg 278677, tg 321356, tg 324541]⟩,
    ⟨6, 1, 3, 14,
      [[tg 321, tg 3506, tg 46185, tg 49370], [tg 347, tg 3532, tg 46211, tg 49396], [tg 386, tg 3571, tg 46250, tg 49435], [tg 438, tg 3623, tg 46302, tg 49487], [tg 503, tg 3688, tg 46367, tg 49552]],
      [tg 367233, tg 370418, tg 413097, tg 416282]⟩,
    ⟨6, 1, 4, 16,
      [[tg 334, tg 3519, tg 46198, tg 49383], [tg 360, tg 3545, tg 46224, tg 49409], [tg 399, tg 3584, tg 46263, tg 49448], [tg 451, tg 3636, tg 46315, tg 49500], [tg 516, tg 3701, tg 46380, tg 49565]],
      [tg 367246, tg 370431, tg 413110, tg 416295]⟩,
    ⟨6, 1, 5, 15,
      [[tg 347, tg 3532, tg 46211, tg 49396], [tg 412, tg 3597, tg 46276, tg 49461], [tg 451, tg 3636, tg 46315, tg 49500], [tg 503, tg 3688, tg 46367, tg 49552], [tg 529, tg 3714, tg 46393, tg 49578]],
      [tg 367259, tg 370444, tg 413123, tg 416308]⟩,
    ⟨6, 1, 6, 16,
      [[tg 360, tg 3545, tg 46224, tg 49409], [tg 425, tg 3610, tg 46289, tg 49474], [tg 438, tg 3623, tg 46302, tg 49487], [tg 516, tg 3701, tg 46380, tg 49565], [tg 542, tg 3727, tg 46406, tg 49591]],
      [tg 367272, tg 370457, tg 413136, tg 416321]⟩,
    ⟨7, 1, 0, 13,
      [[tg 373, tg 3558, tg 46237, tg 49422], [tg 575, tg 3760, tg 15869, tg 19054], [tg 477, tg 3662, tg 46341, tg 49526], [tg 555, tg 3740, tg 46419, tg 49604]],
      [tg 275557, tg 278742, tg 321421, tg 324606]⟩,
    ⟨7, 1, 1, 14,
      [[tg 386, tg 3571, tg 46250, tg 49435], [tg 464, tg 3649, tg 46328, tg 49513], [tg 503, tg 3688, tg 46367, tg 49552], [tg 568, tg 3753, tg 46432, tg 49617]],
      [tg 275570, tg 278755, tg 321434, tg 324619]⟩,
    ⟨7, 1, 2, 18,
      [[tg 399, tg 3584, tg 46263, tg 49448], [tg 516, tg 3701, tg 46380, tg 49565], [tg 30949, tg 34134, tg 76813, tg 79998], [tg 581, tg 3766, tg 46445, tg 49630]],
      [tg 275583, tg 278768, tg 321447, tg 324632]⟩,
    ⟨7, 1, 3, 15,
      [[tg 412, tg 3597, tg 46276, tg 49461], [tg 438, tg 3623, tg 46302, tg 49487], [tg 477, tg 3662, tg 46341, tg 49526], [tg 529, tg 3714, tg 46393, tg 49578], [tg 594, tg 3779, tg 46458, tg 49643]],
      [tg 367324, tg 370509, tg 413188, tg 416373]⟩,
    ⟨7, 1, 4, 17,
      [[tg 425, tg 3610, tg 46289, tg 49474], [tg 451, tg 3636, tg 46315, tg 49500], [tg 490, tg 3675, tg 46354, tg 49539], [tg 542, tg 3727, tg 46406, tg 49591], [tg 607, tg 3792, tg 46471, tg 49656]],
      [tg 367337, tg 370522, tg 413201, tg 416386]⟩,
    ⟨7, 1, 5, 16,
      [[tg 438, tg 3623, tg 46302, tg 49487], [tg 503, tg 3688, tg 46367, tg 49552], [tg 542, tg 3727, tg 46406, tg 49591], [tg 594, tg 3779, tg 46458, tg 49643], [tg 620, tg 3805, tg 46484, tg 49669]],
      [tg 367350, tg 370535, tg 413214, tg 416399]⟩,
    ⟨7, 1, 6, 17,
      [[tg 451, tg 3636, tg 46315, tg 49500], [tg 516, tg 3701, tg 46380, tg 49565], [tg 529, tg 3714, tg 46393, tg 49578], [tg 607, tg 3792, tg 46471, tg 49656], [tg 633, tg 3818, tg 46497, tg 49682]],
      [tg 367363, tg 370548, tg 413227, tg 416412]⟩,
    ⟨8, 1, 0, 14,
      [[tg 464, tg 3649, tg 46328, tg 49513], [tg 2577, tg 5762, tg 17871, tg 21056], [tg 568, tg 3753, tg 46432, tg 49617], [tg 2557, tg 5742, tg 48421, tg 51606]],
      [tg 275648, tg 278833, tg 321512, tg 324697]⟩,
    ⟨8, 1, 1, 15,
      [[tg 477, tg 3662, tg 46341, tg 49526], [tg 555, tg 3740, tg 46419, tg 49604], [tg 594, tg 3779, tg 46458, tg 49643], [tg 2570, tg 5755, tg 48434, tg 51619]],
      [tg 275661, tg 278846, tg 321525, tg 324710]⟩,
    ⟨8, 1, 2, 19,
      [[tg 490, tg 3675, tg 46354, tg 49539], [tg 607, tg 3792, tg 46471, tg 49656], [tg 31040, tg 34225, tg 76904, tg 80089], [tg 2583, tg 5768, tg 48447, tg 51632]],
      [tg 275674, tg 278859, tg 321538, tg 324723]⟩,
    ⟨8, 1, 3, 16,
      [[tg 503, tg 3688, tg 46367, tg 49552], [tg 529, tg 3714, tg 46393, tg 49578], [tg 568, tg 3753, tg 46432, tg 49617], [tg 620, tg 3805, tg 46484, tg 49669], [tg 2596, tg 5781, tg 48460, tg 51645]],
      [tg 367415, tg 370600, tg 413279, tg 416464]⟩,
    ⟨8, 1, 4, 18,
      [[tg 516, tg 3701, tg 46380, tg 49565], [tg 542, tg 3727, tg 46406, tg 49591], [tg 581, tg 3766, tg 46445, tg 49630], [tg 633, tg 3818, tg 46497, tg 49682], [tg 2609, tg 5794, tg 48473, tg 51658]],
      [tg 367428, tg 370613, tg 413292, tg 416477]⟩,
    ⟨8, 1, 5, 17,
      [[tg 529, tg 3714, tg 46393, tg 49578], [tg 594, tg 3779, tg 46458, tg 49643], [tg 633, tg 3818, tg 46497, tg 49682], [tg 2596, tg 5781, tg 48460, tg 51645], [tg 2622, tg 5807, tg 48486, tg 51671]],
      [tg 367441, tg 370626, tg 413305, tg 416490]⟩,
    ⟨8, 1, 6, 18,
      [[tg 542, tg 3727, tg 46406, tg 49591], [tg 607, tg 3792, tg 46471, tg 49656], [tg 620, tg 3805, tg 46484, tg 49669], [tg 2609, tg 5794, tg 48473, tg 51658], [tg 2635, tg 5820, tg 48499, tg 51684]],
      [tg 367454, tg 370639, tg 413318, tg 416503]⟩]⟩,
  ⟨2, 1, 1, -1, 1, [(1, 1, 1), (-1, 1, 1)], 1, 1, 1, 2, -1, 1, 1, 2,
   [⟨0, 1, 0, 7,
      [[tg 5, tg 738, tg 3827, tg 46602], [tg 26, tg 667, tg 1305, tg 16052], [tg 23, tg 3208, tg 45887, tg 49072], [tg 4, tg 3189, tg 15389, tg 18574]],
      [tg 183482, tg 184123, tg 184761, tg 199508]⟩,
    ⟨0, 1, 1, 8,
      [[tg 18, tg 751, tg 3840, tg 46615], [tg 10, tg 3195, tg 45874, tg 49059], [tg 49, tg 3234, tg 45913, tg 49098], [tg 17, tg 3202, tg 15402, tg 18587]],
      [tg 183466, tg 186651, tg 229330, tg 232515]⟩,
    ⟨0, 1, 2, 13,
      [[tg 31, tg 764, tg 3853, tg 46628], [tg 62, tg 3247, tg 45926, tg 49111], [tg 101, tg 3286, tg 45965, tg 49150], [tg 30, tg 3215, tg 15415, tg 18600]],
      [tg 183518, tg 186703, tg 229382, tg 232567]⟩,
    ⟨0, 1, 3, 9,
      [[tg 44, tg 777, tg 3866, tg 46641], [tg 70, tg 803, tg 3892, tg 46667], [tg 23, tg 3208, tg 45887, tg 49072], [tg 75, tg 3260, tg 45939, tg 49124], [tg 43, tg 3228, tg 15428, tg 18613]],
      [tg 183479, tg 186664, tg 229343, tg 232528]⟩,
    ⟨0, 1, 4, 12,
      [[tg 57, tg 790, tg 3879, tg 46654], [tg 83, tg 816, tg 3905, tg 46680], [tg 36, tg 3221, tg 45900, tg 49085], [tg 88, tg 3273, tg 45952, tg 49137], [tg 56, tg 3241, tg 15441, tg 18626]],
      [tg 275267, tg 276000, tg 279089, tg 321864]⟩,
    ⟨0, 1, 5, 10,
      [[tg 70, tg 803, tg 3892, tg 46667], [tg 49, tg 3234, tg 45913, tg 49098], [tg 88, tg 3273, tg 45952, tg 49137], [tg 43, tg 3228, tg 15428, tg 18613], [tg 69, tg 3254, tg 15454, tg 18639]],
      [tg 275233, tg 278418, tg 321097, tg 324282]⟩,
    ⟨0, 1, 6, 11,
      [[tg 83, tg 816, tg 3905, tg 46680], [tg 62, tg 3247, tg 45926, tg 49111], [tg 75, tg 3260, tg 45939, tg 49124], [tg 56, tg 3241, tg 15441, tg 18626], [tg 82, tg 3267, tg 15467, tg 18652]],
      [tg 183531, tg 186716, tg 229395, tg 232580]⟩,
    ⟨0, 2, 0, 14,
      [[tg 30586, tg 33771, tg 76450, tg 79635], [tg 36, tg 3221, tg 45900, tg 49085], [tg 114, tg 3299, tg 45978, tg 49163], [tg 2558, tg 5743, tg 48422, tg 51607]],
      [tg 183492, tg 186677, tg 229356, tg 232541]⟩,
    ⟨0, 2, 1, 15,
      [[tg 30599, tg 33784, tg 76463, tg 79648], [tg 101, tg 3286, tg 45965, tg 49150], [tg 140, tg 3325, tg 46004, tg 49189], [tg 2571, tg 5756, tg 48435, tg 51620]],
      [tg 183557, tg 186742, tg 229421, tg 232606]⟩,
    ⟨0, 2, 2, 20,
      [[tg 30612, tg 33797, tg 76476, tg 79661], [tg 153, tg 3338, tg 46017, tg 49202], [tg 33134, tg 36319, tg 78998, tg 82183], [tg 2584, tg 5769, tg 48448, tg 51633]],
      [tg 183609, tg 186794, tg 229473, tg 232658]⟩,
    ⟨0, 2, 3, 16,
      [[tg 30625, tg 33810, tg 76489, tg 79674], [tg 30651, tg 33836, tg 76515, tg 79700], [tg 114, tg 3299, tg 45978, tg 49163], [tg 166, tg 3351, tg 46030, tg 49215], [tg 2597, tg 5782, tg 48461, tg 51646]],
      [tg 183570, tg 186755, tg 229434, tg 232619]⟩,
    ⟨0, 2, 4, 19,
      [[tg 30638, tg 33823, tg 76502, tg 79687], [tg 30664, tg 33849, tg 76528, tg 79713], [tg 127, tg 3312, tg 45991, tg 49176], [tg 179, tg 3364, tg 46043, tg 49228], [tg 2610, tg 5795, tg 48474, tg 51659]],
      [tg 305848, tg 309033, tg 351712, tg 354897]⟩,
    ⟨0, 2, 5, 17,
      [[tg 30651, tg 33836, tg 76515, tg 79700], [tg 140, tg 3325, tg 46004, tg 49189], [tg 179, tg 3364, tg 46043, tg 49228], [tg 2597, tg 5782, tg 48461, tg 51646], [tg 2623, tg 5808, tg 48487, tg 51672]],
      [tg 275324, tg 278509, tg 321188, tg 324373]⟩,
    ⟨0, 2, 6, 18,
      [[tg 30664, tg 33849, tg 76528, tg 79713], [tg 153, tg 3338, tg 46017, tg 49202], [tg 166, tg 3351, tg 46030, tg 49215], [tg 2610, tg 5795, tg 48474, tg 51659], [tg 2636, tg 5821, tg 48500, tg 51685]],
      [tg 183622, tg 186807, tg 229486, tg 232671]⟩]⟩,
  ⟨2, -1, 1, -7, 0, [(0, 7, 1), (-1, -1, 1)], 0, 7, 1, 7, -1, -1, 1, 7,
   [⟨-8, 1, 0, 14,
      [[tg 31133, tg 34318, tg 76997, tg 80182], [tg 2580, tg 31796, tg 6402, tg 77660], [tg 24, tg 3209, tg 45888, tg 49073], [tg 102, tg 3287, tg 45966, tg 49151]],
      [tg 186036, tg 215252, tg 189858, tg 261116]⟩,
    ⟨-8, 1, 1, 15,
      [[tg 31146, tg 34331, tg 77010, tg 80195], [tg 11, tg 3196, tg 45875, tg 49060], [tg 50, tg 3235, tg 45914, tg 49099], [tg 115, tg 3300, tg 45979, tg 49164]],
      [tg 183467, tg 186652, tg 229331, tg 232516]⟩,
    ⟨-8, 1, 2, 19,
      [[tg 31159, tg 34344, tg 77023, tg 80208], [tg 63, tg 3248, tg 45927, tg 49112], [tg 2650, tg 5835, tg 48514, tg 51699], [tg 128, tg 3313, tg 45992, tg 49177]],
      [tg 183519, tg 186704, tg 229383, tg 232568]⟩,
    ⟨-8, 1, 3, 16,
      [[tg 31172, tg 34357, tg 77036, tg 80221], [tg 31198, tg 34383, tg 77062, tg 80247], [tg 24, tg 3209, tg 45888, tg 49073], [tg 76, tg 3261, tg 45940, tg 49125], [tg 141, tg 3326, tg 46005, tg 49190]],
      [tg 183480, tg 186665, tg 229344, tg 232529]⟩,
    ⟨-8, 1, 4, 18,
      [[tg 31185, tg 34370, tg 77049, tg 80234], [tg 31211, tg 34396, tg 77075, tg 80260], [tg 37, tg 3222, tg 45901, tg 49086], [tg 89, tg 3274, tg 45953, tg 49138], [tg 154, tg 3339, tg 46018, tg 49203]],
      [tg 91817, tg 95002, tg 137681, tg 140866]⟩,
    ⟨-8, 1, 5, 16,
      [[tg 31198, tg 34383, tg 77062, tg 80247], [tg 50, tg 3235, tg 45914, tg 49099], [tg 89, tg 3274, tg 45953, tg 49138], [tg 141, tg 3326, tg 46005, tg 49190], [tg 167, tg 3352, tg 46031, tg 49216]],
      [tg 91869, tg 95054, tg 137733, tg 140918]⟩,
    ⟨-8, 1, 6, 17,
      [[tg 31211, tg 34396, tg 77075, tg 80260], [tg 63, tg 3248, tg 45927, tg 49112], [tg 76, tg 3261, tg 45940, tg 49125], [tg 154, tg 3339, tg 46018, tg 49203], [tg 180, tg 3365, tg 46044, tg 49229]],
      [tg 183532, tg 186717, tg 229396, tg 232581]⟩,
    ⟨-7, 1, 0, 13,
      [[tg 11, tg 3196, tg 45875, tg 49060], [tg 578, tg 674, tg 4400, tg 46538], [tg 115, tg 3300, tg 45979, tg 49164], [tg 193, tg 3378, tg 46057, tg 49242]],
      [tg 184034, tg 184130, tg 187856, tg 229994]⟩,
    ⟨-7, 1, 1, 14,
      [[tg 24, tg 3209, tg 45888, tg 49073], [tg 102, tg 3287, tg 45966, tg 49151], [tg 141, tg 3326, tg 46005, tg 49190], [tg 206, tg 3391, tg 46070, tg 49255]],
      [tg 183558, tg 186743, tg 229422, tg 232607]⟩,
    ⟨-7, 1, 2, 18,
      [[tg 37, tg 3222, tg 45901, tg 49086], [tg 154, tg 3339, tg 46018, tg 49203], [tg 2741, tg 5926, tg 48605, tg 51790], [tg 219, tg 3404, tg 46083, tg 49268]],
      [tg 183610, tg 186795, tg 229474, tg 232659]⟩,
    ⟨-7, 1, 3, 15,
      [[tg 50, tg 3235, tg 45914, tg 49099], [tg 76, tg 3261, tg 45940, tg 49125], [tg 115, tg 3300, tg 45979, tg 49164], [tg 167, tg 3352, tg 46031, tg 49216], [tg 232, tg 3417, tg 46096, tg 49281]],
      [tg 183571, tg 186756, tg 229435, tg 232620]⟩,
    ⟨-7, 1, 4, 17,
      [[tg 63, tg 3248, tg 45927, tg 49112], [tg 89, tg 3274, tg 45953, tg 49138], [tg 128, tg 3313, tg 45992, tg 49177], [tg 180, tg 3365, tg 46044, tg 49229], [tg 245, tg 3430, tg 46109, tg 49294]],
      [tg 91908, tg 95093, tg 137772, tg 140957]⟩,
    ⟨-7, 1, 5, 15,
      [[tg 76, tg 3261, tg 45940, tg 49125], [tg 141, tg 3326, tg 46005, tg 49190], [tg 180, tg 3365, tg 46044, tg 49229], [tg 232, tg 3417, tg 46096, tg 49281], [tg 258, tg 3443, tg 46122, tg 49307]],
      [tg 91960, tg 95145, tg 137824, tg 141009]⟩,
    ⟨-7, 1, 6, 16,
      [[tg 89, tg 3274, tg 45953, tg 49138], [tg 154, tg 3339, tg 46018, tg 49203], [tg 167, tg 3352, tg 46031, tg 49216], [tg 245, tg 3430, tg 46109, tg 49294], [tg 271, tg 3456, tg 46135, tg 49320]],
      [tg 183623, tg 186808, tg 229487, tg 232672]⟩,
    ⟨-6, 1, 0, 12,
      [[tg 102, tg 3287, tg 45966, tg 49151], [tg 487, tg 765, tg 4309, tg 46629], [tg 206, tg 3391, tg 46070, tg 49255], [tg 284, tg 3469, tg 46148, tg 49333]],
      [tg 183943, tg 184221, tg 187765, tg 230085]⟩,
    ⟨-6, 1, 1, 13,
      [[tg 115, tg 3300, tg 45979, tg 49164], [tg 193, tg 3378, tg 46057, tg 49242], [tg 232, tg 3417, tg 46096, tg 49281], [tg 297, tg 3482, tg 46161, tg 49346]],
      [tg 183649, tg 186834, tg 229513, tg 232698]⟩,
    ⟨-6, 1, 2, 17,
      [[tg 128, tg 3313, tg 45992, tg 49177], [tg 245, tg 3430, tg 46109, tg 49294], [tg 2832, tg 6017, tg 48696, tg 51881], [tg 310, tg 3495, tg 46174, tg 49359]],
      [tg 183701, tg 186886, tg 229565, tg 232750]⟩,
    ⟨-6, 1, 3, 14,
      [[tg 141, tg 3326, tg 46005, tg 49190], [tg 167, tg 3352, tg 46031, tg 49216], [tg 206, tg 3391, tg 46070, tg 49255], [tg 258, tg 3443, tg 46122, tg 49307], [tg 323, tg 3508, tg 46187, tg 49372]],
      [tg 183662, tg 186847, tg 229526, tg 232711]⟩,
    ⟨-6, 1, 4, 16,
      [[tg 154, tg 3339, tg 46018, tg 49203], [tg 180, tg 3365, tg 46044, tg 49229], [tg 219, tg 3404, tg 46083, tg 49268], [tg 271, tg 3456, tg 46135, tg 49320], [tg 336, tg 3521, tg 46200, tg 49385]],
      [tg 91999, tg 95184, tg 137863, tg 141048]⟩,
    ⟨-6, 1, 5, 14,
      [[tg 167, tg 3352, tg 46031, tg 49216], [tg 232, tg 3417, tg 46096, tg 49281], [tg 271, tg 3456, tg 46135, tg 49320], [tg 323, tg 3508, tg 46187, tg 49372], [tg 349, tg 3534, tg 46213, tg 49398]],
      [tg 92051, tg 95236, tg 137915, tg 141100]⟩,
    ⟨-6, 1, 6, 15,
      [[tg 180, tg 3365, tg 46044, tg 49229], [tg 245, tg 3430, tg 46109, tg 49294], [tg 258, tg 3443, tg 46122, tg 49307], [tg 336, tg 3521, tg 46200, tg 49385], [tg 362, tg 3547, tg 46226, tg 49411]],
      [tg 183714, tg 186899, tg 229578, tg 232763]⟩,
    ⟨-5, 1, 0, 11,
      [[tg 193, tg 3378, tg 46057, tg 49242], [tg 396, tg 856, tg 4218, tg 46720], [tg 297, tg 3482, tg 46161, tg 49346], [tg 375, tg 3560, tg 46239, tg 49424]],
      [tg 183852, tg 184312, tg 187674, tg 230176]⟩,
    ⟨-5, 1, 1, 12,
      [[tg 206, tg 3391, tg 46070, tg 49255], [tg 284, tg 3469, tg 46148, tg 49333], [tg 323, tg 3508, tg 46187, tg 49372], [tg 388, tg 3573, tg 46252, tg 49437]],
      [tg 183740, tg 186925, tg 229604, tg 232789]⟩,
    ⟨-5, 1, 2, 16,
      [[tg 219, tg 3404, tg 46083, tg 49268], [tg 336, tg 3521, tg 46200, tg 49385], [tg 2923, tg 6108, tg 48787, tg 51972], [tg 401, tg 3586, tg 46265, tg 49450]],
      [tg 183792, tg 186977, tg 229656, tg 232841]⟩,
    ⟨-5, 1, 3, 13,
      [[tg 232, tg 3417, tg 46096, tg 49281], [tg 258, tg 3443, tg 46122, tg 49307], [tg 297, tg 3482, tg 46161, tg 49346], [tg 349, tg 3534, tg 46213, tg 49398], [tg 414, tg 3599, tg 46278, tg 49463]],
      [tg 183753, tg 186938, tg 229617, tg 232802]⟩,
    ⟨-5, 1, 4, 15,
      [[tg 245, tg 3430, tg 46109, tg 49294], [tg 271, tg 3456, tg 46135, tg 49320], [tg 310, tg 3495, tg 46174, tg 49359], [tg 362, tg 3547, tg 46226, tg 49411], [tg 427, tg 3612, tg 46291, tg 49476]],
      [tg 92090, tg 95275, tg 137954, tg 141139]⟩,
    ⟨-5, 1, 5, 13,
      [[tg 258, tg 3443, tg 46122, tg 49307], [tg 323, tg 3508, tg 46187, tg 49372], [tg 362, tg 3547, tg 46226, tg 49411], [tg 414, tg 3599, tg 46278, tg 49463], [tg 440, tg 3625, tg 46304, tg 49489]],
      [tg 92142, tg 95327, tg 138006, tg 141191]⟩,
    ⟨-5, 1, 6, 14,
      [[tg 271, tg 3456, tg 46135, tg 49320], [tg 336, tg 3521, tg 46200, tg 49385], [tg 349, tg 3534, tg 46213, tg 49398], [tg 427, tg 3612, tg 46291, tg 49476], [tg 453, tg 3638, tg 46317, tg 49502]],
      [tg 183805, tg 186990, tg 229669, tg 232854]⟩,
    ⟨-4, 1, 0, 10,
      [[tg 284, tg 3469, tg 46148, tg 49333], [tg 305, tg 947, tg 4127, tg 46811], [tg 388, tg 3573, tg 46252, tg 49437], [tg 466, tg 3651, tg 46330, tg 49515]],
      [tg 183761, tg 184403, tg 187583, tg 230267]⟩,
    ⟨-4, 1, 1, 11,
      [[tg 297, tg 3482, tg 46161, tg 49346], [tg 375, tg 3560, tg 46239, tg 49424], [tg 414, tg 3599, tg 46278, tg 49463], [tg 479, tg 3664, tg 46343, tg 49528]],
      [tg 183831, tg 187016, tg 229695, tg 232880]⟩,
    ⟨-4, 1, 2, 15,
      [[tg 310, tg 3495, tg 46174, tg 49359], [tg 427, tg 3612, tg 46291, tg 49476], [tg 3014, tg 6199, tg 48878, tg 52063], [tg 492, tg 3677, tg 46356, tg 49541]],
      [tg 183883, tg 187068, tg 229747, tg 232932]⟩,
    ⟨-4, 1, 3, 12,
      [[tg 323, tg 3508, tg 46187, tg 49372], [tg 349, tg 3534, tg 46213, tg 49398], [tg 388, tg 3573, tg 46252, tg 49437], [tg 440, tg 3625, tg 46304, tg 49489], [tg 505, tg 3690, tg 46369, tg 49554]],
      [tg 183844, tg 187029, tg 229708, tg 232893]⟩,
    ⟨-4, 1, 4, 14,
      [[tg 336, tg 3521, tg 46200, tg 49385], [tg 362, tg 3547, tg 46226, tg 49411], [tg 401, tg 3586, tg 46265, tg 49450], [tg 453, tg 3638, tg 46317, tg 49502], [tg 518, tg 3703, tg 46382, tg 49567]],
      [tg 92181, tg 95366, tg 138045, tg 141230]⟩,
    ⟨-4, 1, 5, 12,
      [[tg 349, tg 3534, tg 46213, tg 49398], [tg 414, tg 3599, tg 46278, tg 49463], [tg 453, tg 3638, tg 46317, tg 49502], [tg 505, tg 3690, tg 46369, tg 49554], [tg 531, tg 3716, tg 46395, tg 49580]],
      [tg 92233, tg 95418, tg 138097, tg 141282]⟩,
    ⟨-4, 1, 6, 13,
      [[tg 362, tg 3547, tg 46226, tg 49411], [tg 427, tg 3612, tg 46291, tg 49476], [tg 440, tg 3625, tg 46304, tg 49489], [tg 518, tg 3703, tg 46382, tg 49567], [tg 544, tg 3729, tg 46408, tg 49593]],
      [tg 183896, tg 187081, tg 229760, tg 232945]⟩,
    ⟨-3, 1, 0, 9,
      [[tg 375, tg 3560, tg 46239, tg 49424], [tg 214, tg 1038, tg 4036, tg 46902], [tg 479, tg 3664, tg 46343, tg 49528], [tg 557, tg 3742, tg 46421, tg 49606]],
      [tg 183670, tg 184494, tg 187492, tg 230358]⟩,
    ⟨-3, 1, 1, 10,
      [[tg 388, tg 3573, tg 46252, tg 49437], [tg 466, tg 3651, tg 46330, tg 49515], [tg 505, tg 3690, tg 46369, tg 49554], [tg 570, tg 3755, tg 46434, tg 49619]],
      [tg 183922, tg 187107, tg 229786, tg 232971]⟩,
    ⟨-3, 1, 2, 14,
      [[tg 401, tg 3586, tg 46265, tg 49450], [tg 518, tg 3703, tg 46382, tg 49567], [tg 3105, tg 6290, tg 48969, tg 52154], [tg 583, tg 3768, tg 46447, tg 49632]],
      [tg 183974, tg 187159, tg 229838, tg 233023]⟩,
    ⟨-3, 1, 3, 11,
      [[tg 414, tg 3599, tg 46278, tg 49463], [tg 440, tg 3625, tg 46304, tg 49489], [tg 479, tg 3664, tg 46343, tg 49528], [tg 531, tg 3716, tg 46395, tg 49580], [tg 596, tg 3781, tg 46460, tg 49645]],
      [tg 183935, tg 187120, tg 229799, tg 232984]⟩,
    ⟨-3, 1, 4, 13,
      [[tg 427, tg 3612, tg 46291, tg 49476], [tg 453, tg 3638, tg 46317, tg 49502], [tg 492, tg 3677, tg 46356, tg 49541], [tg 544, tg 3729, tg 46408, tg 49593], [tg 609, tg 3794, tg 46473, tg 49658]],
      [tg 92272, tg 95457, tg 138136, tg 141321]⟩,
    ⟨-3, 1, 5, 11,
      [[tg 440, tg 3625, tg 46304, tg 49489], [tg 505, tg 3690, tg 46369, tg 49554], [tg 544, tg 3729, tg 46408, tg 49593], [tg 596, tg 3781, tg 46460, tg 49645], [tg 622, tg 3807, tg 46486, tg 49671]],
      [tg 92324, tg 95509, tg 138188, tg 141373]⟩,
    ⟨-3, 1, 6, 12,
      [[tg 453, tg 3638, tg 46317, tg 49502], [tg 518, tg 3703, tg 46382, tg 49567], [tg 531, tg 3716, tg 46395, tg 49580], [tg 609, tg 3794, tg 46473, tg 49658], [tg 635, tg 3820, tg 46499, tg 49684]],
      [tg 183987, tg 187172, tg 229851, tg 233036]⟩,
    ⟨-2, 1, 0, 8,
      [[tg 466, tg 3651, tg 46330, tg 49515], [tg 123, tg 1129, tg 3945, tg 46993], [tg 570, tg 3755, tg 46434, tg 49619], [tg 5, tg 3190, tg 15299, tg 18484]],
      [tg 183579, tg 184585, tg 187401, tg 230449]⟩,
    ⟨-2, 1, 1, 9,
      [[tg 479, tg 3664, tg 46343, tg 49528], [tg 557, tg 3742, tg 46421, tg 49606], [tg 596, tg 3781, tg 46460, tg 49645], [tg 18, tg 3203, tg 15312, tg 18497]],
      [tg 184013, tg 187198, tg 229877, tg 233062]⟩,
    ⟨-2, 1, 2, 13,
      [[tg 492, tg 3677, tg 46356, tg 49541], [tg 609, tg 3794, tg 46473, tg 49658], [tg 2553, tg 5738, tg 17847, tg 21032], [tg 31, tg 3216, tg 15325, tg 18510]],
      [tg 184065, tg 187250, tg 229929, tg 233114]⟩,
    ⟨-2, 1, 3, 10,
      [[tg 505, tg 3690, tg 46369, tg 49554], [tg 531, tg 3716, tg 46395, tg 49580], [tg 570, tg 3755, tg 46434, tg 49619], [tg 622, tg 3807, tg 46486, tg 49671], [tg 44, tg 3229, tg 15338, tg 18523]],
      [tg 184026, tg 187211, tg 229890, tg 233075]⟩,
    ⟨-2, 1, 4, 12,
      [[tg 518, tg 3703, tg 46382, tg 49567], [tg 544, tg 3729, tg 46408, tg 49593], [tg 583, tg 3768, tg 46447, tg 49632], [tg 635, tg 3820, tg 46499, tg 49684], [tg 57, tg 3242, tg 15351, tg 18536]],
      [tg 92363, tg 95548, tg 138227, tg 141412]⟩,
    ⟨-2, 1, 5, 10,
      [[tg 531, tg 3716, tg 46395, tg 49580], [tg 596, tg 3781, tg 46460, tg 49645], [tg 635, tg 3820, tg 46499, tg 49684], [tg 44, tg 3229, tg 15338, tg 18523], [tg 70, tg 3255, tg 15364, tg 18549]],
      [tg 91772, tg 94957, tg 107066, tg 110251]⟩,
    ⟨-2, 1, 6, 11,
      [[tg 544, tg 3729, tg 46408, tg 49593], [tg 609, tg 3794, tg 46473, tg 49658], [tg 622, tg 3807, tg 46486, tg 49671], [tg 57, tg 3242, tg 15351, tg 18536], [tg 83, tg 3268, tg 15377, tg 18562]],
      [tg 184078, tg 187263, tg 229942, tg 233127]⟩]⟩,
  ⟨2, -7, 0, -1, -1, [(-1, 1, 1), (0, -7, 1)], -1, 1, 1, 7, 0, -7, 1, 7,
   [⟨-8, -1, 0, 14,
      [[tg 3106, tg 6291, tg 48970, tg 52155], [tg 30705, tg 33890, tg 76569, tg 79754], [tg 25, tg 3210, tg 45889, tg 49074], [tg 103, tg 3288, tg 45967, tg 49152]],
      [tg 91753, tg 94938, tg 137617, tg 140802]⟩,
    ⟨-8, -1, 1, 13,
      [[tg 3119, tg 6304, tg 48983, tg 52168], [tg 12, tg 3197, tg 45876, tg 49061], [tg 51, tg 3236, tg 45915, tg 49100], [tg 116, tg 3301, tg 45980, tg 49165]],
      [tg 183507, tg 186692, tg 229371, tg 232556]⟩,
    ⟨-8, -1, 2, 9,
      [[tg 3132, tg 6317, tg 48996, tg 52181], [tg 64, tg 3249, tg 45928, tg 49113], [tg 2554, tg 5739, tg 18394, tg 21579], [tg 129, tg 3314, tg 45993, tg 49178]],
      [tg 94282, tg 97467, tg 110122, tg 113307]⟩,
    ⟨-8, -1, 3, 12,
      [[tg 3145, tg 6330, tg 49009, tg 52194], [tg 3171, tg 6356, tg 49035, tg 52220], [tg 25, tg 3210, tg 45889, tg 49074], [tg 77, tg 3262, tg 45941, tg 49126], [tg 142, tg 3327, tg 46006, tg 49191]],
      [tg 91805, tg 94990, tg 137669, tg 140854]⟩,
    ⟨-8, -1, 4, 10,
      [[tg 3158, tg 6343, tg 49022, tg 52207], [tg 3184, tg 6369, tg 49048, tg 52233], [tg 38, tg 3223, tg 45902, tg 49087], [tg 90, tg 3275, tg 45954, tg 49139], [tg 155, tg 3340, tg 46019, tg 49204]],
      [tg 91766, tg 94951, tg 137630, tg 140815]⟩,
    ⟨-8, -1, 5, 11,
      [[tg 3171, tg 6356, tg 49035, tg 52220], [tg 51, tg 3236, tg 45915, tg 49100], [tg 90, tg 3275, tg 45954, tg 49139], [tg 142, tg 3327, tg 46006, tg 49191], [tg 168, tg 3353, tg 46032, tg 49217]],
      [tg 183546, tg 186731, tg 229410, tg 232595]⟩,
    ⟨-8, -1, 6, 10,
      [[tg 3184, tg 6369, tg 49048, tg 52233], [tg 64, tg 3249, tg 45928, tg 49113], [tg 77, tg 3262, tg 45941, tg 49126], [tg 155, tg 3340, tg 46019, tg 49204], [tg 181, tg 3366, tg 46045, tg 49230]],
      [tg 91883, tg 95068, tg 137747, tg 140932]⟩,
    ⟨-7, -1, 0, 13,
      [[tg 12, tg 3197, tg 45876, tg 49061], [tg 30796, tg 33981, tg 76660, tg 79845], [tg 116, tg 3301, tg 45980, tg 49165], [tg 194, tg 3379, tg 46058, tg 49243]],
      [tg 91844, tg 95029, tg 137708, tg 140893]⟩,
    ⟨-7, -1, 1, 12,
      [[tg 25, tg 3210, tg 45889, tg 49074], [tg 103, tg 3288, tg 45967, tg 49152], [tg 142, tg 3327, tg 46006, tg 49191], [tg 207, tg 3392, tg 46071, tg 49256]],
      [tg 183598, tg 186783, tg 229462, tg 232647]⟩,
    ⟨-7, -1, 2, 8,
      [[tg 38, tg 3223, tg 45902, tg 49087], [tg 155, tg 3340, tg 46019, tg 49204], [tg 552, tg 3737, tg 15300, tg 18485], [tg 220, tg 3405, tg 46084, tg 49269]],
      [tg 92280, tg 95465, tg 107028, tg 110213]⟩,
    ⟨-7, -1, 3, 11,
      [[tg 51, tg 3236, tg 45915, tg 49100], [tg 77, tg 3262, tg 45941, tg 49126], [tg 116, tg 3301, tg 45980, tg 49165], [tg 168, tg 3353, tg 46032, tg 49217], [tg 233, tg 3418, tg 46097, tg 49282]],
      [tg 91896, tg 95081, tg 137760, tg 140945]⟩,
    ⟨-7, -1, 4, 9,
      [[tg 64, tg 3249, tg 45928, tg 49113], [tg 90, tg 3275, tg 45954, tg 49139], [tg 129, tg 3314, tg 45993, tg 49178], [tg 181, tg 3366, tg 46045, tg 49230], [tg 246, tg 3431, tg 46110, tg 49295]],
      [tg 91857, tg 95042, tg 137721, tg 140906]⟩,
    ⟨-7, -1, 5, 10,
      [[tg 77, tg 3262, tg 45941, tg 49126], [tg 142, tg 3327, tg 46006, tg 49191], [tg 181, tg 3366, tg 46045, tg 49230], [tg 233, tg 3418, tg 46097, tg 49282], [tg 259, tg 3444, tg 46123, tg 49308]],
      [tg 183637, tg 186822, tg 229501, tg 232686]⟩,
    ⟨-7, -1, 6, 9,
      [[tg 90, tg 3275, tg 45954, tg 49139], [tg 155, tg 3340, tg 46019, tg 49204], [tg 168, tg 3353, tg 46032, tg 49217], [tg 246, tg 3431, tg 46110, tg 49295], [tg 272, tg 3457, tg 46136, tg 49321]],
      [tg 91974, tg 95159, tg 137838, tg 141023]⟩,
    ⟨-6, -1, 0, 12,
      [[tg 103, tg 3288, tg 45967, tg 49152], [tg 30887, tg 34072, tg 76751, tg 79936], [tg 207, tg 3392, tg 46071, tg 49256], [tg 285, tg 3470, tg 46149, tg 49334]],
      [tg 91935, tg 95120, tg 137799, tg 140984]⟩,
    ⟨-6, -1, 1, 11,
      [[tg 116, tg 3301, tg 45980, tg 49165], [tg 194, tg 3379, tg 46058, tg 49243], [tg 233, tg 3418, tg 46097, tg 49282], [tg 298, tg 3483, tg 46162, tg 49347]],
      [tg 183689, tg 186874, tg 229553, tg 232738]⟩,
    ⟨-6, -1, 2, 7,
      [[tg 129, tg 3314, tg 45993, tg 49178], [tg 246, tg 3431, tg 46110, tg 49295], [tg 461, tg 3646, tg 15391, tg 18576], [tg 311, tg 3496, tg 46175, tg 49360]],
      [tg 92189, tg 95374, tg 107119, tg 110304]⟩,
    ⟨-6, -1, 3, 10,
      [[tg 142, tg 3327, tg 46006, tg 49191], [tg 168, tg 3353, tg 46032, tg 49217], [tg 207, tg 3392, tg 46071, tg 49256], [tg 259, tg 3444, tg 46123, tg 49308], [tg 324, tg 3509, tg 46188, tg 49373]],
      [tg 91987, tg 95172, tg 137851, tg 141036]⟩,
    ⟨-6, -1, 4, 8,
      [[tg 155, tg 3340, tg 46019, tg 49204], [tg 181, tg 3366, tg 46045, tg 49230], [tg 220, tg 3405, tg 46084, tg 49269], [tg 272, tg 3457, tg 46136, tg 49321], [tg 337, tg 3522, tg 46201, tg 49386]],
      [tg 91948, tg 95133, tg 137812, tg 140997]⟩,
    ⟨-6, -1, 5, 9,
      [[tg 168, tg 3353, tg 46032, tg 49217], [tg 233, tg 3418, tg 46097, tg 49282], [tg 272, tg 3457, tg 46136, tg 49321], [tg 324, tg 3509, tg 46188, tg 49373], [tg 350, tg 3535, tg 46214, tg 49399]],
      [tg 183728, tg 186913, tg 229592, tg 232777]⟩,
    ⟨-6, -1, 6, 8,
      [[tg 181, tg 3366, tg 46045, tg 49230], [tg 246, tg 3431, tg 46110, tg 49295], [tg 259, tg 3444, tg 46123, tg 49308], [tg 337, tg 3522, tg 46201, tg 49386], [tg 363, tg 3548, tg 46227, tg 49412]],
      [tg 92065, tg 95250, tg 137929, tg 141114]⟩,
    ⟨-5, -1, 0, 11,
      [[tg 194, tg 3379, tg 46058, tg 49243], [tg 30978, tg 34163, tg 76842, tg 80027], [tg 298, tg 3483, tg 46162, tg 49347], [tg 376, tg 3561, tg 46240, tg 49425]],
      [tg 92026, tg 95211, tg 137890, tg 141075]⟩,
    ⟨-5, -1, 1, 10,
      [[tg 207, tg 3392, tg 46071, tg 49256], [tg 285, tg 3470, tg 46149, tg 49334], [tg 324, tg 3509, tg 46188, tg 49373], [tg 389, tg 3574, tg 46253, tg 49438]],
      [tg 183780, tg 186965, tg 229644, tg 232829]⟩,
    ⟨-5, -1, 2, 6,
      [[tg 220, tg 3405, tg 46084, tg 49269], [tg 337, tg 3522, tg 46201, tg 49386], [tg 370, tg 3555, tg 15482, tg 18667], [tg 402, tg 3587, tg 46266, tg 49451]],
      [tg 92098, tg 95283, tg 107210, tg 110395]⟩,
    ⟨-5, -1, 3, 9,
      [[tg 233, tg 3418, tg 46097, tg 49282], [tg 259, tg 3444, tg 46123, tg 49308], [tg 298, tg 3483, tg 46162, tg 49347], [tg 350, tg 3535, tg 46214, tg 49399], [tg 415, tg 3600, tg 46279, tg 49464]],
      [tg 92078, tg 95263, tg 137942, tg 141127]⟩,
    ⟨-5, -1, 4, 7,
      [[tg 246, tg 3431, tg 46110, tg 49295], [tg 272, tg 3457, tg 46136, tg 49321], [tg 311, tg 3496, tg 46175, tg 49360], [tg 363, tg 3548, tg 46227, tg 49412], [tg 428, tg 3613, tg 46292, tg 49477]],
      [tg 92039, tg 95224, tg 137903, tg 141088]⟩,
    ⟨-5, -1, 5, 8,
      [[tg 259, tg 3444, tg 46123, tg 49308], [tg 324, tg 3509, tg 46188, tg 49373], [tg 363, tg 3548, tg 46227, tg 49412], [tg 415, tg 3600, tg 46279, tg 49464], [tg 441, tg 3626, tg 46305, tg 49490]],
      [tg 183819, tg 187004, tg 229683, tg 232868]⟩,
    ⟨-5, -1, 6, 7,
      [[tg 272, tg 3457, tg 46136, tg 49321], [tg 337, tg 3522, tg 46201, tg 49386], [tg 350, tg 3535, tg 46214, tg 49399], [tg 428, tg 3613, tg 46292, tg 49477], [tg 454, tg 3639, tg 46318, tg 49503]],
      [tg 92156, tg 95341, tg 138020, tg 141205]⟩,
    ⟨-4, -1, 0, 10,
      [[tg 285, tg 3470, tg 46149, tg 49334], [tg 31069, tg 34254, tg 76933, tg 80118], [tg 389, tg 3574, tg 46253, tg 49438], [tg 467, tg 3652, tg 46331, tg 49516]],
      [tg 92117, tg 95302, tg 137981, tg 141166]⟩,
    ⟨-4, -1, 1, 9,
      [[tg 298, tg 3483, tg 46162, tg 49347], [tg 376, tg 3561, tg 46240, tg 49425], [tg 415, tg 3600, tg 46279, tg 49464], [tg 480, tg 3665, tg 46344, tg 49529]],
      [tg 183871, tg 187056, tg 229735, tg 232920]⟩,
    ⟨-4, -1, 2, 5,
      [[tg 311, tg 3496, tg 46175, tg 49360], [tg 428, tg 3613, tg 46292, tg 49477], [tg 279, tg 3464, tg 15573, tg 18758], [tg 493, tg 3678, tg 46357, tg 49542]],
      [tg 92007, tg 95192, tg 107301, tg 110486]⟩,
    ⟨-4, -1, 3, 8,
      [[tg 324, tg 3509, tg 46188, tg 49373], [tg 350, tg 3535, tg 46214, tg 49399], [tg 389, tg 3574, tg 46253, tg 49438], [tg 441, tg 3626, tg 46305, tg 49490], [tg 506, tg 3691, tg 46370, tg 49555]],
      [tg 92169, tg 95354, tg 138033, tg 141218]⟩,
    ⟨-4, -1, 4, 6,
      [[tg 337, tg 3522, tg 46201, tg 49386], [tg 363, tg 3548, tg 46227, tg 49412], [tg 402, tg 3587, tg 46266, tg 49451], [tg 454, tg 3639, tg 46318, tg 49503], [tg 519, tg 3704, tg 46383, tg 49568]],
      [tg 92130, tg 95315, tg 137994, tg 141179]⟩,
    ⟨-4, -1, 5, 7,
      [[tg 350, tg 3535, tg 46214, tg 49399], [tg 415, tg 3600, tg 46279, tg 49464], [tg 454, tg 3639, tg 46318, tg 49503], [tg 506, tg 3691, tg 46370, tg 49555], [tg 532, tg 3717, tg 46396, tg 49581]],
      [tg 183910, tg 187095, tg 229774, tg 232959]⟩,
    ⟨-4, -1, 6, 6,
      [[tg 363, tg 3548, tg 46227, tg 49412], [tg 428, tg 3613, tg 46292, tg 49477], [tg 441, tg 3626, tg 46305, tg 49490], [tg 519, tg 3704, tg 46383, tg 49568], [tg 545, tg 3730, tg 46409, tg 49594]],
      [tg 92247, tg 95432, tg 138111, tg 141296]⟩,
    ⟨-3, -1, 0, 9,
      [[tg 376, tg 3561, tg 46240, tg 49425], [tg 31160, tg 34345, tg 77024, tg 80209], [tg 480, tg 3665, tg 46344, tg 49529], [tg 558, tg 3743, tg 46422, tg 49607]],
      [tg 92208, tg 95393, tg 138072, tg 141257]⟩,
    ⟨-3, -1, 1, 8,
      [[tg 389, tg 3574, tg 46253, tg 49438], [tg 467, tg 3652, tg 46331, tg 49516], [tg 506, tg 3691, tg 46370, tg 49555], [tg 571, tg 3756, tg 46435, tg 49620]],
      [tg 183962, tg 187147, tg 229826, tg 233011]⟩,
    ⟨-3, -1, 2, 4,
      [[tg 402, tg 3587, tg 46266, tg 49451], [tg 519, tg 3704, tg 46383, tg 49568], [tg 188, tg 3373, tg 15664, tg 18849], [tg 584, tg 3769, tg 46448, tg 49633]],
      [tg 91916, tg 95101, tg 107392, tg 110577]⟩,
    ⟨-3, -1, 3, 7,
      [[tg 415, tg 3600, tg 46279, tg 49464], [tg 441, tg 3626, tg 46305, tg 49490], [tg 480, tg 3665, tg 46344, tg 49529], [tg 532, tg 3717, tg 46396, tg 49581], [tg 597, tg 3782, tg 46461, tg 49646]],
      [tg 92260, tg 95445, tg 138124, tg 141309]⟩,
    ⟨-3, -1, 4, 5,
      [[tg 428, tg 3613, tg 46292, tg 49477], [tg 454, tg 3639, tg 46318, tg 49503], [tg 493, tg 3678, tg 46357, tg 49542], [tg 545, tg 3730, tg 46409, tg 49594], [tg 610, tg 3795, tg 46474, tg 49659]],
      [tg 92221, tg 95406, tg 138085, tg 141270]⟩,
    ⟨-3, -1, 5, 6,
      [[tg 441, tg 3626, tg 46305, tg 49490], [tg 506, tg 3691, tg 46370, tg 49555], [tg 545, tg 3730, tg 46409, tg 49594], [tg 597, tg 3782, tg 46461, tg 49646], [tg 623, tg 3808, tg 46487, tg 49672]],
      [tg 184001, tg 187186, tg 229865, tg 233050]⟩,
    ⟨-3, -1, 6, 5,
      [[tg 454, tg 3639, tg 46318, tg 49503], [tg 519, tg 3704, tg 46383, tg 49568], [tg 532, tg 3717, tg 46396, tg 49581], [tg 610, tg 3795, tg 46474, tg 49659], [tg 636, tg 3821, tg 46500, tg 49685]],
      [tg 92338, tg 95523, tg 138202, tg 141387]⟩,
    ⟨-2, -1, 0, 8,
      [[tg 467, tg 3652, tg 46331, tg 49516], [tg 2575, tg 31251, tg 6397, tg 77115], [tg 571, tg 3756, tg 46435, tg 49620], [tg 1, tg 649, tg 3823, tg 46513]],
      [tg 92299, tg 95484, tg 138163, tg 141348]⟩,
    ⟨-2, -1, 1, 7,
      [[tg 480, tg 3665, tg 46344, tg 49529], [tg 558, tg 3743, tg 46422, tg 49607], [tg 597, tg 3782, tg 46461, tg 49646], [tg 14, tg 662, tg 3836, tg 46526]],
      [tg 184053, tg 187238, tg 229917, tg 233102]⟩,
    ⟨-2, -1, 2, 3,
      [[tg 493, tg 3678, tg 46357, tg 49542], [tg 610, tg 3795, tg 46474, tg 49659], [tg 97, tg 3282, tg 15755, tg 18940], [tg 27, tg 675, tg 3849, tg 46539]],
      [tg 91825, tg 95010, tg 107483, tg 110668]⟩,
    ⟨-2, -1, 3, 6,
      [[tg 506, tg 3691, tg 46370, tg 49555], [tg 532, tg 3717, tg 46396, tg 49581], [tg 571, tg 3756, tg 46435, tg 49620], [tg 623, tg 3808, tg 46487, tg 49672], [tg 40, tg 688, tg 3862, tg 46552]],
      [tg 92351, tg 95536, tg 138215, tg 141400]⟩,
    ⟨-2, -1, 4, 4,
      [[tg 519, tg 3704, tg 46383, tg 49568], [tg 545, tg 3730, tg 46409, tg 49594], [tg 584, tg 3769, tg 46448, tg 49633], [tg 636, tg 3821, tg 46500, tg 49685], [tg 53, tg 701, tg 3875, tg 46565]],
      [tg 92312, tg 95497, tg 138176, tg 141361]⟩,
    ⟨-2, -1, 5, 5,
      [[tg 532, tg 3717, tg 46396, tg 49581], [tg 597, tg 3782, tg 46461, tg 49646], [tg 636, tg 3821, tg 46500, tg 49685], [tg 40, tg 688, tg 3862, tg 46552], [tg 66, tg 714, tg 3888, tg 46578]],
      [tg 184092, tg 187277, tg 229956, tg 233141]⟩,
    ⟨-2, -1, 6, 4,
      [[tg 545, tg 3730, tg 46409, tg 49594], [tg 610, tg 3795, tg 46474, tg 49659], [tg 623, tg 3808, tg 46487, tg 49672], [tg 53, tg 701, tg 3875, tg 46565], [tg 79, tg 727, tg 3901, tg 46591]],
      [tg 91781, tg 92429, tg 95603, tg 138293]⟩]⟩]

/-- A packed certificate entry: side bit, test index, coefficient. -/
def cc (n : ℕ) : Bool × ℕ × ℕ := (n % 2 == 1, n / 2 % 8, n / 16)

set_option maxRecDepth 100000 in
def certsData : List (List (List (Bool × ℕ × ℕ))) := [
  [[],[cc 16,cc 20,cc 21],[cc 18,cc 20,cc 21],[cc 18,cc 21],[cc 18,cc 22,cc 21],[cc 16,cc 22,cc 21],[cc 16,cc 21],[cc 16,cc 20,cc 17],[cc 116,cc 17],[cc 118,cc 19],[cc 16,cc 22,cc 19],[cc 118,cc 17],[cc 116,cc 19]],
  [[cc 16,cc 20,cc 37],[],[cc 18,cc 21],[cc 16,cc 20,cc 33],[cc 20,cc 21],[cc 16,cc 21],[cc 16,cc 20,cc 35],[cc 18,cc 19],[cc 20,cc 19],[cc 18,cc 17],[cc 16,cc 19],[cc 112,cc 116,cc 33],[cc 16,cc 17]],
  [[cc 16,cc 20,cc 35],[cc 16,cc 21],[],[cc 18,cc 20,cc 33],[cc 18,cc 21],[cc 20,cc 21],[cc 16,cc 20,cc 37],[cc 16,cc 17],[cc 18,cc 19],[cc 114,cc 116,cc 35],[cc 18,cc 17],[cc 16,cc 19],[cc 20,cc 17]],
  [[cc 20,cc 19],[cc 16,cc 20,cc 21],[cc 16,cc 20,cc 19],[],[cc 18,cc 20,cc 17],[cc 16,cc 20,cc 17],[cc 20,cc 21],[cc 16,cc 20,cc 17],[cc 112,cc 17],[cc 114,cc 19],[cc 18,cc 20,cc 19],[cc 114,cc 17],[cc 112,cc 19]],
  [[cc 16,cc 20,cc 39],[cc 20,cc 21],[cc 16,cc 21],[cc 16,cc 20,cc 35],[],[cc 18,cc 21],[cc 16,cc 20,cc 33],[cc 16,cc 19],[cc 112,cc 116,cc 33],[cc 16,cc 17],[cc 18,cc 19],[cc 20,cc 19],[cc 18,cc 17]],
  [[cc 16,cc 20,cc 33],[cc 18,cc 21],[cc 20,cc 21],[cc 16,cc 20,cc 37],[cc 16,cc 21],[],[cc 18,cc 20,cc 33],[cc 18,cc 17],[cc 16,cc 19],[cc 20,cc 17],[cc 16,cc 17],[cc 18,cc 19],[cc 114,cc 116,cc 35]],
  [[cc 20,cc 17],[cc 18,cc 20,cc 17],[cc 16,cc 20,cc 17],[cc 20,cc 21],[cc 16,cc 20,cc 21],[cc 16,cc 20,cc 19],[],[cc 18,cc 20,cc 19],[cc 114,cc 17],[cc 112,cc 19],[cc 16,cc 20,cc 17],[cc 112,cc 17],[cc 114,cc 19]],
  [[cc 16,cc 18,cc 37],[cc 18,cc 19],[cc 16,cc 17],[cc 16,cc 18,cc 33],[cc 16,cc 21],[cc 16,cc 19],[cc 16,cc 18,cc 35],[],[cc 16,cc 19],[cc 112,cc 114,cc 35],[cc 16,cc 17],[cc 112,cc 114,cc 33],[cc 18,cc 17]],
  [[cc 16,cc 117],[cc 18,cc 21],[cc 18,cc 19],[cc 16,cc 113],[cc 32,cc 114,cc 113],[cc 18,cc 17],[cc 16,cc 115],[cc 18,cc 17],[],[cc 16,cc 19],[cc 32,cc 114,cc 115],[cc 16,cc 17],[cc 32,cc 114,cc 113]],
  [[cc 18,cc 119],[cc 16,cc 19],[cc 112,cc 34,cc 115],[cc 18,cc 115],[cc 16,cc 17],[cc 16,cc 21],[cc 18,cc 113],[cc 112,cc 34,cc 113],[cc 18,cc 17],[],[cc 16,cc 19],[cc 112,cc 34,cc 115],[cc 16,cc 17]],
  [[cc 16,cc 18,cc 39],[cc 16,cc 21],[cc 16,cc 19],[cc 16,cc 18,cc 35],[cc 18,cc 19],[cc 16,cc 17],[cc 16,cc 18,cc 33],[cc 16,cc 17],[cc 112,cc 114,cc 33],[cc 18,cc 17],[],[cc 16,cc 19],[cc 112,cc 114,cc 35]],
  [[cc 16,cc 119],[cc 32,cc 114,cc 113],[cc 18,cc 17],[cc 16,cc 115],[cc 18,cc 21],[cc 18,cc 19],[cc 16,cc 113],[cc 32,cc 114,cc 115],[cc 16,cc 17],[cc 32,cc 114,cc 113],[cc 18,cc 17],[],[cc 16,cc 19]],
  [[cc 18,cc 117],[cc 16,cc 17],[cc 16,cc 21],[cc 18,cc 113],[cc 16,cc 19],[cc 112,cc 34,cc 115],[cc 18,cc 115],[cc 16,cc 19],[cc 112,cc 34,cc 115],[cc 16,cc 17],[cc 112,cc 34,cc 113],[cc 18,cc 17],[]]]

def cfg : GalCert.Cfg 7 := ⟨adj, (0, 0, 0), 7, regsData, certsData, 0, 0⟩

theorem hc : cfg.check = true := by decide +kernel

theorem hV : cfg.vbound 20 = true := by decide +kernel

theorem hball : ∀ n, ball n = GalCert.ball cfg.adj cfg.x0 n
  | 0 => rfl
  | n + 1 => by rw [ball, GalCert.ball, hball n]; rfl

theorem ha (n : ℕ) (hn : 1 ≤ n) : a n = (cfg.A n : ℤ) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [a, hball, hball]
  exact GalCert.Cfg.card_step hc k

theorem hrec : ∀ k, (([(1, 9), (-1, 8), (-1, 2), (1, 1)] : List (ℤ × ℕ)).map fun p => p.1 * (cfg.A (k + p.2) : ℤ)).sum = 0 :=
  GalCert.Cfg.lin_zero hc hV _ (by decide) (by decide +kernel)

theorem hgfw : ∀ n < 20 + 2 * cfg.L, ((GalCert.csOfS [1, -1, 0, 0, 0, 0, 0, -1, 1] 0).map fun p => p.1 * (cfg.A (n + p.2) : ℤ)).sum = 0 := by
  decide +kernel

theorem hsmall : ∀ n < 9, GalCert.conv a [1, -1, 0, 0, 0, 0, 0, -1, 1] n = ([1, 3, 4, 6, 4, 6, 4, 3, 1] : List ℤ).getD n 0 := by
  have e : a = fun n => if n = 0 then 1 else (cfg.A n : ℤ) := by
    funext n
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; rfl
    · rw [if_neg (by omega)]; exact ha n h
  rw [e]
  decide +kernel

end P312549

open PowerSeries OMA.S_oeis_a312549 in
theorem OMA.solution : type_of% @OMA.S_oeis_a312549.main := by
  refine ⟨?_, ?_⟩
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 9 := ⟨n - 9, by omega⟩
    have h := P312549.hrec k
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at h
    rw [show k + 9 - 1 = k + 8 by omega,
      show k + 9 - 7 = k + 2 by omega,
      show k + 9 - 8 = k + 1 by omega,
      P312549.ha (k + 9) (by omega),
      P312549.ha (k + 8) (by omega),
      P312549.ha (k + 2) (by omega),
      P312549.ha (k + 1) (by omega)]
    linarith
  · have hD : (X^8 - X^7 - X + 1 : PowerSeries ℤ) = GalCert.polyOf [1, -1, 0, 0, 0, 0, 0, -1, 1] := by
      simp only [GalCert.polyOf, map_neg, map_one, map_zero, map_ofNat, map_intCast]; ring
    have hP : (X^8 + 3*X^7 + 4*X^6 + 6*X^5 + 4*X^4 + 6*X^3 + 4*X^2 + 3*X + 1 : PowerSeries ℤ) = GalCert.polyOf [1, 3, 4, 6, 4, 6, 4, 3, 1] := by
      simp only [GalCert.polyOf, map_neg, map_one, map_zero, map_ofNat, map_intCast]; ring
    rw [hD, hP]
    exact GalCert.Cfg.gf_from2 P312549.hc P312549.hV a P312549.ha _ _ 0 9 (by decide) (by decide) P312549.hgfw P312549.hsmall
