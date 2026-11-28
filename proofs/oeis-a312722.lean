import OMAStatements.S_oeis_a312722
import Mathlib

/-!
Proof of the conjectured recurrence and generating function for A312722.

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


namespace P312722
open OMA.S_oeis_a312722

def regsData : List (GalCert.Region 19) := [
  ⟨0, 0, 0, 0, 0, [(1, 0, 0), (-1, 0, 0), (0, 1, 0), (0, -1, 0)], 0, 0, 0, 0, 0, 0, 0, 0,
   [⟨0, 0, 0, 2,
      [[⟨0, 2, 0, 0, 0, 0, 0, 0, 0⟩], [⟨0, 7, 0, 0, 0, 0, 0, 0, 0⟩], [⟨4, 4, 0, 0, 0, 0, 0, 0, 0⟩], [⟨4, 14, 0, 0, 0, 0, 0, 0, 0⟩]],
      [⟨0, 2, 0, 0, 0, 0, 0, 0, 0⟩]⟩,
    ⟨0, 0, 1, 2,
      [[⟨6, 6, 0, 0, 0, 0, 0, 0, 0⟩], [⟨5, 13, 0, 0, 0, 0, 0, 0, 0⟩], [⟨0, 3, 0, 0, 0, 0, 0, 0, 0⟩], [⟨4, 5, 0, 0, 0, 0, 0, 0, 0⟩]],
      [⟨0, 3, 0, 0, 0, 0, 0, 0, 0⟩]⟩,
    ⟨0, 0, 2, 1,
      [[⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩], [⟨0, 3, 0, 0, 0, 0, 0, 0, 0⟩], [⟨0, 8, 0, 0, 0, 0, 0, 0, 0⟩], [⟨0, 12, 0, 0, 0, 0, 0, 0, 0⟩]],
      [⟨0, 12, 0, 0, 0, 0, 0, 0, 0⟩]⟩,
    ⟨0, 0, 3, 1,
      [[⟨0, 1, 0, 0, 0, 0, 0, 0, 0⟩], [⟨0, 2, 0, 0, 0, 0, 0, 0, 0⟩], [⟨0, 10, 0, 0, 0, 0, 0, 0, 0⟩], [⟨0, 12, 0, 0, 0, 0, 0, 0, 0⟩]],
      [⟨0, 12, 0, 0, 0, 0, 0, 0, 1⟩]⟩,
    ⟨0, 0, 4, 3,
      [[⟨1, 0, 0, 0, 0, 0, 0, 0, 0⟩], [⟨0, 5, 0, 0, 0, 0, 0, 0, 0⟩], [⟨0, 11, 0, 0, 0, 0, 0, 0, 0⟩], [⟨0, 14, 0, 0, 0, 0, 0, 0, 0⟩]],
      [⟨0, 11, 0, 0, 0, 0, 0, 0, 2⟩]⟩,
    ⟨0, 0, 5, 4,
      [[⟨6, 9, 0, 0, 0, 0, 0, 0, 0⟩], [⟨6, 13, 0, 0, 0, 0, 0, 0, 0⟩], [⟨1, 1, 0, 0, 0, 0, 0, 0, 0⟩], [⟨0, 4, 0, 0, 0, 0, 0, 0, 0⟩]],
      [⟨6, 9, 0, 0, 0, 0, 0, 0, 3⟩]⟩,
    ⟨0, 0, 6, 4,
      [[⟨0, 7, 0, 0, 0, 0, 0, 0, 0⟩], [⟨0, 15, 0, 0, 0, 0, 0, 0, 0⟩], [⟨0, 18, 0, 0, 0, 0, 0, 0, 0⟩], [⟨3, 1, 0, 0, 0, 0, 0, 0, 0⟩], [⟨3, 10, 0, 0, 0, 0, 0, 0, 0⟩]],
      [⟨0, 7, 0, 0, 0, 0, 0, 0, 1⟩]⟩,
    ⟨0, 0, 7, 3,
      [[⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩], [⟨0, 6, 0, 0, 0, 0, 0, 0, 0⟩], [⟨0, 8, 0, 0, 0, 0, 0, 0, 0⟩], [⟨0, 15, 0, 0, 0, 0, 0, 0, 0⟩], [⟨0, 18, 0, 0, 0, 0, 0, 0, 0⟩]],
      [⟨0, 0, 0, 0, 0, 0, 0, 0, 1⟩]⟩,
    ⟨0, 0, 8, 2,
      [[⟨0, 2, 0, 0, 0, 0, 0, 0, 0⟩], [⟨0, 7, 0, 0, 0, 0, 0, 0, 0⟩], [⟨0, 9, 0, 0, 0, 0, 0, 0, 0⟩], [⟨0, 16, 0, 0, 0, 0, 0, 0, 0⟩], [⟨0, 18, 0, 0, 0, 0, 0, 0, 0⟩]],
      [⟨0, 2, 0, 0, 0, 0, 0, 0, 2⟩]⟩,
    ⟨0, 0, 9, 2,
      [[⟨0, 8, 0, 0, 0, 0, 0, 0, 0⟩], [⟨0, 16, 0, 0, 0, 0, 0, 0, 0⟩], [⟨0, 18, 0, 0, 0, 0, 0, 0, 0⟩], [⟨3, 5, 0, 0, 0, 0, 0, 0, 0⟩], [⟨3, 11, 0, 0, 0, 0, 0, 0, 0⟩]],
      [⟨0, 16, 0, 0, 0, 0, 0, 0, 1⟩]⟩,
    ⟨0, 0, 10, 2,
      [[⟨6, 6, 0, 0, 0, 0, 0, 0, 0⟩], [⟨6, 18, 0, 0, 0, 0, 0, 0, 0⟩], [⟨0, 3, 0, 0, 0, 0, 0, 0, 0⟩], [⟨0, 11, 0, 0, 0, 0, 0, 0, 0⟩], [⟨0, 17, 0, 0, 0, 0, 0, 0, 0⟩]],
      [⟨0, 3, 0, 0, 0, 0, 0, 0, 2⟩]⟩,
    ⟨0, 0, 11, 2,
      [[⟨6, 9, 0, 0, 0, 0, 0, 0, 0⟩], [⟨6, 18, 0, 0, 0, 0, 0, 0, 0⟩], [⟨0, 4, 0, 0, 0, 0, 0, 0, 0⟩], [⟨0, 10, 0, 0, 0, 0, 0, 0, 0⟩], [⟨0, 17, 0, 0, 0, 0, 0, 0, 0⟩]],
      [⟨0, 17, 0, 0, 0, 0, 0, 0, 1⟩]⟩,
    ⟨0, 0, 12, 0,
      [[⟨0, 2, 0, 0, 0, 0, 0, 0, 0⟩], [⟨0, 3, 0, 0, 0, 0, 0, 0, 0⟩], [⟨0, 16, 0, 0, 0, 0, 0, 0, 0⟩], [⟨0, 17, 0, 0, 0, 0, 0, 0, 0⟩]],
      [⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩]⟩,
    ⟨0, 0, 13, 2,
      [[⟨1, 15, 0, 0, 0, 0, 0, 0, 0⟩], [⟨0, 16, 0, 0, 0, 0, 0, 0, 0⟩], [⟨2, 1, 0, 0, 0, 0, 0, 0, 0⟩], [⟨3, 5, 0, 0, 0, 0, 0, 0, 0⟩]],
      [⟨0, 16, 0, 0, 0, 0, 0, 0, 3⟩]⟩,
    ⟨0, 0, 14, 2,
      [[⟨1, 0, 0, 0, 0, 0, 0, 0, 0⟩], [⟨1, 15, 0, 0, 0, 0, 0, 0, 0⟩], [⟨0, 4, 0, 0, 0, 0, 0, 0, 0⟩], [⟨0, 17, 0, 0, 0, 0, 0, 0, 0⟩]],
      [⟨0, 17, 0, 0, 0, 0, 0, 0, 3⟩]⟩,
    ⟨0, 0, 15, 4,
      [[⟨0, 6, 0, 0, 0, 0, 0, 0, 0⟩], [⟨0, 7, 0, 0, 0, 0, 0, 0, 0⟩], [⟨4, 13, 0, 0, 0, 0, 0, 0, 0⟩], [⟨4, 14, 0, 0, 0, 0, 0, 0, 0⟩]],
      [⟨0, 7, 0, 0, 0, 0, 0, 0, 3⟩]⟩,
    ⟨0, 0, 16, 1,
      [[⟨0, 8, 0, 0, 0, 0, 0, 0, 0⟩], [⟨0, 9, 0, 0, 0, 0, 0, 0, 0⟩], [⟨0, 12, 0, 0, 0, 0, 0, 0, 0⟩], [⟨0, 13, 0, 0, 0, 0, 0, 0, 0⟩]],
      [⟨0, 12, 0, 0, 0, 0, 0, 0, 2⟩]⟩,
    ⟨0, 0, 17, 1,
      [[⟨0, 10, 0, 0, 0, 0, 0, 0, 0⟩], [⟨0, 11, 0, 0, 0, 0, 0, 0, 0⟩], [⟨0, 12, 0, 0, 0, 0, 0, 0, 0⟩], [⟨0, 14, 0, 0, 0, 0, 0, 0, 0⟩]],
      [⟨0, 12, 0, 0, 0, 0, 0, 0, 3⟩]⟩,
    ⟨0, 0, 18, 3,
      [[⟨0, 6, 0, 0, 0, 0, 0, 0, 0⟩], [⟨0, 7, 0, 0, 0, 0, 0, 0, 0⟩], [⟨0, 8, 0, 0, 0, 0, 0, 0, 0⟩], [⟨0, 9, 0, 0, 0, 0, 0, 0, 0⟩], [⟨3, 10, 0, 0, 0, 0, 0, 0, 0⟩], [⟨3, 11, 0, 0, 0, 0, 0, 0, 0⟩]],
      [⟨0, 8, 0, 0, 0, 0, 0, 0, 4⟩]⟩]⟩,
  ⟨1, 0, -1, 0, 0, [(1, 0, 0), (-1, 0, 0), (0, -1, 1)], 0, -1, 1, 1, 0, 0, 0, 0,
   [⟨0, -1, 0, 3,
      [[⟨1, 2, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 2, 1, 0, 1, 0, 0, 0, 0⟩], [⟨1, 7, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 7, 1, 0, 1, 0, 0, 0, 0⟩], [⟨0, 4, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 4, 1, 0, 0, 0, 0, 0, 0⟩], [⟨0, 14, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 14, 1, 0, 0, 0, 0, 0, 0⟩]],
      [⟨0, 14, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 14, 1, 0, 0, 0, 0, 0, 0⟩]⟩,
    ⟨0, -1, 1, 5,
      [[⟨12, 6, 0, 0, 0, 0, 0, 0, 0⟩, ⟨12, 6, 0, 0, 0, 1, 0, 1, 0⟩], [⟨6, 13, 0, 0, 0, 0, 0, 0, 0⟩, ⟨12, 13, 0, 0, 0, 1, 0, 0, 0⟩], [⟨1, 3, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 3, 1, 0, 1, 0, 0, 0, 0⟩], [⟨0, 5, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 5, 1, 0, 0, 0, 0, 0, 0⟩]],
      [⟨0, 5, 0, 0, 0, 0, 0, 0, 2⟩, ⟨1, 5, 1, 0, 0, 0, 0, 0, 2⟩]⟩,
    ⟨0, -1, 2, 4,
      [[⟨1, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 0, 1, 0, 1, 0, 0, 0, 0⟩], [⟨1, 3, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 3, 1, 0, 1, 0, 0, 0, 0⟩], [⟨1, 8, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 8, 1, 0, 1, 0, 0, 0, 0⟩], [⟨1, 12, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 12, 1, 0, 1, 0, 0, 0, 0⟩]],
      [⟨1, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 0, 1, 0, 1, 0, 0, 0, 0⟩]⟩,
    ⟨0, -1, 3, 5,
      [[⟨1, 1, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 1, 1, 0, 1, 0, 0, 0, 0⟩], [⟨1, 2, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 2, 1, 0, 1, 0, 0, 0, 0⟩], [⟨1, 10, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 10, 1, 0, 1, 0, 0, 0, 0⟩], [⟨1, 12, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 12, 1, 0, 1, 0, 0, 0, 0⟩]],
      [⟨1, 2, 0, 0, 0, 0, 0, 0, 1⟩, ⟨1, 2, 1, 0, 1, 0, 0, 0, 1⟩]⟩,
    ⟨0, -1, 4, 8,
      [[⟨1, 0, 0, 0, 1, 0, 0, 0, 0⟩, ⟨1, 0, 1, 0, 2, 0, 0, 0, 0⟩], [⟨1, 5, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 5, 1, 0, 1, 0, 0, 0, 0⟩], [⟨1, 11, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 11, 1, 0, 1, 0, 0, 0, 0⟩], [⟨1, 14, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 14, 1, 0, 1, 0, 0, 0, 0⟩]],
      [⟨1, 11, 0, 0, 0, 0, 0, 0, 2⟩, ⟨1, 11, 1, 0, 1, 0, 0, 0, 2⟩]⟩,
    ⟨0, -1, 5, 9,
      [[⟨12, 9, 0, 0, 0, 0, 0, 0, 0⟩, ⟨12, 9, 0, 0, 0, 1, 0, 1, 0⟩], [⟨12, 13, 0, 0, 0, 0, 0, 0, 0⟩, ⟨12, 13, 0, 0, 0, 1, 0, 1, 0⟩], [⟨1, 1, 0, 0, 1, 0, 0, 0, 0⟩, ⟨1, 1, 1, 0, 2, 0, 0, 0, 0⟩], [⟨1, 4, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 4, 1, 0, 1, 0, 0, 0, 0⟩]],
      [⟨12, 9, 0, 0, 0, 0, 0, 0, 3⟩, ⟨12, 9, 0, 0, 0, 1, 0, 1, 3⟩]⟩,
    ⟨0, -1, 6, 4,
      [[⟨1, 7, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 7, 1, 0, 1, 0, 0, 0, 0⟩], [⟨1, 15, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 15, 1, 0, 1, 0, 0, 0, 0⟩], [⟨1, 18, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 18, 1, 0, 1, 0, 0, 0, 0⟩], [⟨2, 1, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 1, 1, 0, 0, 0, 0, 0, 0⟩], [⟨2, 10, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 10, 1, 0, 0, 0, 0, 0, 0⟩]],
      [⟨1, 15, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 15, 1, 0, 1, 0, 0, 0, 0⟩]⟩,
    ⟨0, -1, 7, 4,
      [[⟨1, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 0, 1, 0, 1, 0, 0, 0, 0⟩], [⟨1, 6, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 6, 1, 0, 1, 0, 0, 0, 0⟩], [⟨1, 8, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 8, 1, 0, 1, 0, 0, 0, 0⟩], [⟨1, 15, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 15, 1, 0, 1, 0, 0, 0, 0⟩], [⟨1, 18, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 18, 1, 0, 1, 0, 0, 0, 0⟩]],
      [⟨1, 0, 0, 0, 0, 0, 0, 0, 1⟩, ⟨1, 0, 1, 0, 1, 0, 0, 0, 1⟩]⟩,
    ⟨0, -1, 8, 5,
      [[⟨1, 2, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 2, 1, 0, 1, 0, 0, 0, 0⟩], [⟨1, 7, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 7, 1, 0, 1, 0, 0, 0, 0⟩], [⟨1, 9, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 9, 1, 0, 1, 0, 0, 0, 0⟩], [⟨1, 16, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 16, 1, 0, 1, 0, 0, 0, 0⟩], [⟨1, 18, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 18, 1, 0, 1, 0, 0, 0, 0⟩]],
      [⟨1, 2, 0, 0, 0, 0, 0, 0, 2⟩, ⟨1, 2, 1, 0, 1, 0, 0, 0, 2⟩]⟩,
    ⟨0, -1, 9, 6,
      [[⟨1, 8, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 8, 1, 0, 1, 0, 0, 0, 0⟩], [⟨1, 16, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 16, 1, 0, 1, 0, 0, 0, 0⟩], [⟨1, 18, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 18, 1, 0, 1, 0, 0, 0, 0⟩], [⟨2, 5, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 5, 1, 0, 0, 0, 0, 0, 0⟩], [⟨2, 11, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 11, 1, 0, 0, 0, 0, 0, 0⟩]],
      [⟨1, 8, 0, 0, 0, 0, 0, 0, 2⟩, ⟨1, 8, 1, 0, 1, 0, 0, 0, 2⟩]⟩,
    ⟨0, -1, 10, 6,
      [[⟨12, 6, 0, 0, 0, 0, 0, 0, 0⟩, ⟨12, 6, 0, 0, 0, 1, 0, 1, 0⟩], [⟨12, 18, 0, 0, 0, 0, 0, 0, 0⟩, ⟨12, 18, 0, 0, 0, 1, 0, 1, 0⟩], [⟨1, 3, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 3, 1, 0, 1, 0, 0, 0, 0⟩], [⟨1, 11, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 11, 1, 0, 1, 0, 0, 0, 0⟩], [⟨1, 17, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 17, 1, 0, 1, 0, 0, 0, 0⟩]],
      [⟨1, 3, 0, 0, 0, 0, 0, 0, 2⟩, ⟨1, 3, 1, 0, 1, 0, 0, 0, 2⟩]⟩,
    ⟨0, -1, 11, 7,
      [[⟨12, 9, 0, 0, 0, 0, 0, 0, 0⟩, ⟨12, 9, 0, 0, 0, 1, 0, 1, 0⟩], [⟨12, 18, 0, 0, 0, 0, 0, 0, 0⟩, ⟨12, 18, 0, 0, 0, 1, 0, 1, 0⟩], [⟨1, 4, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 4, 1, 0, 1, 0, 0, 0, 0⟩], [⟨1, 10, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 10, 1, 0, 1, 0, 0, 0, 0⟩], [⟨1, 17, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 17, 1, 0, 1, 0, 0, 0, 0⟩]],
      [⟨1, 10, 0, 0, 0, 0, 0, 0, 3⟩, ⟨1, 10, 1, 0, 1, 0, 0, 0, 3⟩]⟩,
    ⟨0, -1, 12, 5,
      [[⟨1, 2, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 2, 1, 0, 1, 0, 0, 0, 0⟩], [⟨1, 3, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 3, 1, 0, 1, 0, 0, 0, 0⟩], [⟨1, 16, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 16, 1, 0, 1, 0, 0, 0, 0⟩], [⟨1, 17, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 17, 1, 0, 1, 0, 0, 0, 0⟩]],
      [⟨1, 2, 0, 0, 0, 0, 0, 0, 3⟩, ⟨1, 2, 1, 0, 1, 0, 0, 0, 3⟩]⟩,
    ⟨0, -1, 13, 7,
      [[⟨1, 15, 0, 0, 1, 0, 0, 0, 0⟩, ⟨1, 15, 1, 0, 2, 0, 0, 0, 0⟩], [⟨1, 16, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 16, 1, 0, 1, 0, 0, 0, 0⟩], [⟨7, 1, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 1, 1, 0, 1, 0, 0, 0, 0⟩], [⟨2, 5, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 5, 1, 0, 0, 0, 0, 0, 0⟩]],
      [⟨1, 16, 0, 0, 0, 0, 0, 0, 3⟩, ⟨1, 16, 1, 0, 1, 0, 0, 0, 3⟩]⟩,
    ⟨0, -1, 14, 7,
      [[⟨1, 0, 0, 0, 1, 0, 0, 0, 0⟩, ⟨1, 0, 1, 0, 2, 0, 0, 0, 0⟩], [⟨1, 15, 0, 0, 1, 0, 0, 0, 0⟩, ⟨1, 15, 1, 0, 2, 0, 0, 0, 0⟩], [⟨1, 4, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 4, 1, 0, 1, 0, 0, 0, 0⟩], [⟨1, 17, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 17, 1, 0, 1, 0, 0, 0, 0⟩]],
      [⟨1, 17, 0, 0, 0, 0, 0, 0, 3⟩, ⟨1, 17, 1, 0, 1, 0, 0, 0, 3⟩]⟩,
    ⟨0, -1, 15, 3,
      [[⟨1, 6, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 6, 1, 0, 1, 0, 0, 0, 0⟩], [⟨1, 7, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 7, 1, 0, 1, 0, 0, 0, 0⟩], [⟨0, 13, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 13, 1, 0, 0, 0, 0, 0, 0⟩], [⟨0, 14, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 14, 1, 0, 0, 0, 0, 0, 0⟩]],
      [⟨0, 13, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 13, 1, 0, 0, 0, 0, 0, 0⟩]⟩,
    ⟨0, -1, 16, 6,
      [[⟨1, 8, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 8, 1, 0, 1, 0, 0, 0, 0⟩], [⟨1, 9, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 9, 1, 0, 1, 0, 0, 0, 0⟩], [⟨1, 12, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 12, 1, 0, 1, 0, 0, 0, 0⟩], [⟨1, 13, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 13, 1, 0, 1, 0, 0, 0, 0⟩]],
      [⟨1, 8, 0, 0, 0, 0, 0, 0, 3⟩, ⟨1, 8, 1, 0, 1, 0, 0, 0, 3⟩]⟩,
    ⟨0, -1, 17, 6,
      [[⟨1, 10, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 10, 1, 0, 1, 0, 0, 0, 0⟩], [⟨1, 11, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 11, 1, 0, 1, 0, 0, 0, 0⟩], [⟨1, 12, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 12, 1, 0, 1, 0, 0, 0, 0⟩], [⟨1, 14, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 14, 1, 0, 1, 0, 0, 0, 0⟩]],
      [⟨1, 12, 0, 0, 0, 0, 0, 0, 3⟩, ⟨1, 12, 1, 0, 1, 0, 0, 0, 3⟩]⟩,
    ⟨0, -1, 18, 5,
      [[⟨1, 6, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 6, 1, 0, 1, 0, 0, 0, 0⟩], [⟨1, 7, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 7, 1, 0, 1, 0, 0, 0, 0⟩], [⟨1, 8, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 8, 1, 0, 1, 0, 0, 0, 0⟩], [⟨1, 9, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 9, 1, 0, 1, 0, 0, 0, 0⟩], [⟨2, 10, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 10, 1, 0, 0, 0, 0, 0, 0⟩], [⟨2, 11, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 11, 1, 0, 0, 0, 0, 0, 0⟩]],
      [⟨1, 6, 0, 0, 0, 0, 0, 0, 2⟩, ⟨1, 6, 1, 0, 1, 0, 0, 0, 2⟩]⟩]⟩,
  ⟨1, 1, -1, 0, 0, [(1, 1, 0), (-1, -1, 0), (1, -1, 2)], 1, -1, 2, 2, 0, 0, 0, 0,
   [⟨1, -1, 0, 5,
      [[⟨2, 2, 0, 0, 0, 0, 0, 0, 0⟩, ⟨2, 2, 1, 0, 1, 0, 0, 0, 0⟩], [⟨2, 7, 0, 0, 0, 0, 0, 0, 0⟩, ⟨2, 7, 1, 0, 1, 0, 0, 0, 0⟩], [⟨3, 4, 0, 0, 0, 0, 0, 0, 0⟩, ⟨8, 4, 1, 0, 0, 0, 0, 0, 0⟩], [⟨3, 14, 0, 0, 0, 0, 0, 0, 0⟩, ⟨8, 14, 1, 0, 0, 0, 0, 0, 0⟩]],
      [⟨3, 4, 0, 0, 0, 0, 0, 0, 0⟩, ⟨8, 4, 1, 0, 0, 0, 0, 0, 0⟩]⟩,
    ⟨1, -1, 1, 3,
      [[⟨1, 6, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 6, 0, 0, 0, 1, 0, 0, 0⟩], [⟨0, 13, 0, 0, 0, 0, 0, 0, 0⟩, ⟨2, 13, 1, 0, 0, 0, 0, 0, 0⟩], [⟨2, 3, 0, 0, 0, 0, 0, 0, 0⟩, ⟨2, 3, 1, 0, 1, 0, 0, 0, 0⟩], [⟨3, 5, 0, 0, 0, 0, 0, 0, 0⟩, ⟨8, 5, 1, 0, 0, 0, 0, 0, 0⟩]],
      [⟨0, 13, 0, 0, 0, 0, 0, 0, 2⟩, ⟨2, 13, 1, 0, 0, 0, 0, 0, 2⟩]⟩,
    ⟨1, -1, 2, 5,
      [[⟨2, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨2, 0, 1, 0, 1, 0, 0, 0, 0⟩], [⟨2, 3, 0, 0, 0, 0, 0, 0, 0⟩, ⟨2, 3, 1, 0, 1, 0, 0, 0, 0⟩], [⟨2, 8, 0, 0, 0, 0, 0, 0, 0⟩, ⟨2, 8, 1, 0, 1, 0, 0, 0, 0⟩], [⟨2, 12, 0, 0, 0, 0, 0, 0, 0⟩, ⟨2, 12, 1, 0, 1, 0, 0, 0, 0⟩]],
      [⟨2, 3, 0, 0, 0, 0, 0, 0, 1⟩, ⟨2, 3, 1, 0, 1, 0, 0, 0, 1⟩]⟩,
    ⟨1, -1, 3, 4,
      [[⟨2, 1, 0, 0, 0, 0, 0, 0, 0⟩, ⟨2, 1, 1, 0, 1, 0, 0, 0, 0⟩], [⟨2, 2, 0, 0, 0, 0, 0, 0, 0⟩, ⟨2, 2, 1, 0, 1, 0, 0, 0, 0⟩], [⟨2, 10, 0, 0, 0, 0, 0, 0, 0⟩, ⟨2, 10, 1, 0, 1, 0, 0, 0, 0⟩], [⟨2, 12, 0, 0, 0, 0, 0, 0, 0⟩, ⟨2, 12, 1, 0, 1, 0, 0, 0, 0⟩]],
      [⟨2, 1, 0, 0, 0, 0, 0, 0, 2⟩, ⟨2, 1, 1, 0, 1, 0, 0, 0, 2⟩]⟩,
    ⟨1, -1, 4, 7,
      [[⟨7, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 0, 0, 0, 0, 1, 0, 1, 0⟩], [⟨2, 5, 0, 0, 0, 0, 0, 0, 0⟩, ⟨2, 5, 1, 0, 1, 0, 0, 0, 0⟩], [⟨2, 11, 0, 0, 0, 0, 0, 0, 0⟩, ⟨2, 11, 1, 0, 1, 0, 0, 0, 0⟩], [⟨2, 14, 0, 0, 0, 0, 0, 0, 0⟩, ⟨2, 14, 1, 0, 1, 0, 0, 0, 0⟩]],
      [⟨2, 11, 0, 0, 0, 0, 0, 0, 2⟩, ⟨2, 11, 1, 0, 1, 0, 0, 0, 2⟩]⟩,
    ⟨1, -1, 5, 7,
      [[⟨1, 9, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 9, 0, 0, 0, 1, 0, 0, 0⟩], [⟨1, 13, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 13, 0, 0, 0, 1, 0, 0, 0⟩], [⟨7, 1, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 1, 0, 0, 0, 1, 0, 1, 0⟩], [⟨2, 4, 0, 0, 0, 0, 0, 0, 0⟩, ⟨2, 4, 1, 0, 1, 0, 0, 0, 0⟩]],
      [⟨1, 9, 0, 0, 0, 0, 0, 0, 3⟩, ⟨7, 9, 0, 0, 0, 1, 0, 0, 3⟩]⟩,
    ⟨1, -1, 6, 7,
      [[⟨2, 7, 0, 0, 0, 0, 0, 0, 0⟩, ⟨2, 7, 1, 0, 1, 0, 0, 0, 0⟩], [⟨2, 15, 0, 0, 0, 0, 0, 0, 0⟩, ⟨2, 15, 1, 0, 1, 0, 0, 0, 0⟩], [⟨2, 18, 0, 0, 0, 0, 0, 0, 0⟩, ⟨2, 18, 1, 0, 1, 0, 0, 0, 0⟩], [⟨8, 1, 0, 0, 0, 0, 0, 0, 0⟩, ⟨8, 1, 1, 0, 1, 0, 0, 0, 0⟩], [⟨8, 10, 0, 0, 0, 0, 0, 0, 0⟩, ⟨8, 10, 1, 0, 1, 0, 0, 0, 0⟩]],
      [⟨2, 7, 0, 0, 0, 0, 0, 0, 1⟩, ⟨2, 7, 1, 0, 1, 0, 0, 0, 1⟩]⟩,
    ⟨1, -1, 7, 6,
      [[⟨2, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨2, 0, 1, 0, 1, 0, 0, 0, 0⟩], [⟨2, 6, 0, 0, 0, 0, 0, 0, 0⟩, ⟨2, 6, 1, 0, 1, 0, 0, 0, 0⟩], [⟨2, 8, 0, 0, 0, 0, 0, 0, 0⟩, ⟨2, 8, 1, 0, 1, 0, 0, 0, 0⟩], [⟨2, 15, 0, 0, 0, 0, 0, 0, 0⟩, ⟨2, 15, 1, 0, 1, 0, 0, 0, 0⟩], [⟨2, 18, 0, 0, 0, 0, 0, 0, 0⟩, ⟨2, 18, 1, 0, 1, 0, 0, 0, 0⟩]],
      [⟨2, 0, 0, 0, 0, 0, 0, 0, 1⟩, ⟨2, 0, 1, 0, 1, 0, 0, 0, 1⟩]⟩,
    ⟨1, -1, 8, 6,
      [[⟨2, 2, 0, 0, 0, 0, 0, 0, 0⟩, ⟨2, 2, 1, 0, 1, 0, 0, 0, 0⟩], [⟨2, 7, 0, 0, 0, 0, 0, 0, 0⟩, ⟨2, 7, 1, 0, 1, 0, 0, 0, 0⟩], [⟨2, 9, 0, 0, 0, 0, 0, 0, 0⟩, ⟨2, 9, 1, 0, 1, 0, 0, 0, 0⟩], [⟨2, 16, 0, 0, 0, 0, 0, 0, 0⟩, ⟨2, 16, 1, 0, 1, 0, 0, 0, 0⟩], [⟨2, 18, 0, 0, 0, 0, 0, 0, 0⟩, ⟨2, 18, 1, 0, 1, 0, 0, 0, 0⟩]],
      [⟨2, 2, 0, 0, 0, 0, 0, 0, 2⟩, ⟨2, 2, 1, 0, 1, 0, 0, 0, 2⟩]⟩,
    ⟨1, -1, 9, 7,
      [[⟨2, 8, 0, 0, 0, 0, 0, 0, 0⟩, ⟨2, 8, 1, 0, 1, 0, 0, 0, 0⟩], [⟨2, 16, 0, 0, 0, 0, 0, 0, 0⟩, ⟨2, 16, 1, 0, 1, 0, 0, 0, 0⟩], [⟨2, 18, 0, 0, 0, 0, 0, 0, 0⟩, ⟨2, 18, 1, 0, 1, 0, 0, 0, 0⟩], [⟨8, 5, 0, 0, 0, 0, 0, 0, 0⟩, ⟨8, 5, 1, 0, 1, 0, 0, 0, 0⟩], [⟨8, 11, 0, 0, 0, 0, 0, 0, 0⟩, ⟨8, 11, 1, 0, 1, 0, 0, 0, 0⟩]],
      [⟨2, 8, 0, 0, 0, 0, 0, 0, 2⟩, ⟨2, 8, 1, 0, 1, 0, 0, 0, 2⟩]⟩,
    ⟨1, -1, 10, 5,
      [[⟨1, 6, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 6, 0, 0, 0, 1, 0, 0, 0⟩], [⟨1, 18, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 18, 0, 0, 0, 1, 0, 0, 0⟩], [⟨2, 3, 0, 0, 0, 0, 0, 0, 0⟩, ⟨2, 3, 1, 0, 1, 0, 0, 0, 0⟩], [⟨2, 11, 0, 0, 0, 0, 0, 0, 0⟩, ⟨2, 11, 1, 0, 1, 0, 0, 0, 0⟩], [⟨2, 17, 0, 0, 0, 0, 0, 0, 0⟩, ⟨2, 17, 1, 0, 1, 0, 0, 0, 0⟩]],
      [⟨1, 6, 0, 0, 0, 0, 0, 0, 4⟩, ⟨7, 6, 0, 0, 0, 1, 0, 0, 4⟩]⟩,
    ⟨1, -1, 11, 6,
      [[⟨1, 9, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 9, 0, 0, 0, 1, 0, 0, 0⟩], [⟨1, 18, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 18, 0, 0, 0, 1, 0, 0, 0⟩], [⟨2, 4, 0, 0, 0, 0, 0, 0, 0⟩, ⟨2, 4, 1, 0, 1, 0, 0, 0, 0⟩], [⟨2, 10, 0, 0, 0, 0, 0, 0, 0⟩, ⟨2, 10, 1, 0, 1, 0, 0, 0, 0⟩], [⟨2, 17, 0, 0, 0, 0, 0, 0, 0⟩, ⟨2, 17, 1, 0, 1, 0, 0, 0, 0⟩]],
      [⟨1, 18, 0, 0, 0, 0, 0, 0, 5⟩, ⟨7, 18, 0, 0, 0, 1, 0, 0, 5⟩]⟩,
    ⟨1, -1, 12, 5,
      [[⟨2, 2, 0, 0, 0, 0, 0, 0, 0⟩, ⟨2, 2, 1, 0, 1, 0, 0, 0, 0⟩], [⟨2, 3, 0, 0, 0, 0, 0, 0, 0⟩, ⟨2, 3, 1, 0, 1, 0, 0, 0, 0⟩], [⟨2, 16, 0, 0, 0, 0, 0, 0, 0⟩, ⟨2, 16, 1, 0, 1, 0, 0, 0, 0⟩], [⟨2, 17, 0, 0, 0, 0, 0, 0, 0⟩, ⟨2, 17, 1, 0, 1, 0, 0, 0, 0⟩]],
      [⟨2, 3, 0, 0, 0, 0, 0, 0, 3⟩, ⟨2, 3, 1, 0, 1, 0, 0, 0, 3⟩]⟩,
    ⟨1, -1, 13, 7,
      [[⟨7, 15, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 15, 0, 0, 0, 1, 0, 1, 0⟩], [⟨2, 16, 0, 0, 0, 0, 0, 0, 0⟩, ⟨2, 16, 1, 0, 1, 0, 0, 0, 0⟩], [⟨2, 1, 0, 0, 1, 0, 0, 0, 0⟩, ⟨2, 1, 1, 0, 2, 0, 0, 0, 0⟩], [⟨8, 5, 0, 0, 0, 0, 0, 0, 0⟩, ⟨8, 5, 1, 0, 1, 0, 0, 0, 0⟩]],
      [⟨2, 16, 0, 0, 0, 0, 0, 0, 3⟩, ⟨2, 16, 1, 0, 1, 0, 0, 0, 3⟩]⟩,
    ⟨1, -1, 14, 7,
      [[⟨7, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 0, 0, 0, 0, 1, 0, 1, 0⟩], [⟨7, 15, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 15, 0, 0, 0, 1, 0, 1, 0⟩], [⟨2, 4, 0, 0, 0, 0, 0, 0, 0⟩, ⟨2, 4, 1, 0, 1, 0, 0, 0, 0⟩], [⟨2, 17, 0, 0, 0, 0, 0, 0, 0⟩, ⟨2, 17, 1, 0, 1, 0, 0, 0, 0⟩]],
      [⟨2, 17, 0, 0, 0, 0, 0, 0, 3⟩, ⟨2, 17, 1, 0, 1, 0, 0, 0, 3⟩]⟩,
    ⟨1, -1, 15, 6,
      [[⟨2, 6, 0, 0, 0, 0, 0, 0, 0⟩, ⟨2, 6, 1, 0, 1, 0, 0, 0, 0⟩], [⟨2, 7, 0, 0, 0, 0, 0, 0, 0⟩, ⟨2, 7, 1, 0, 1, 0, 0, 0, 0⟩], [⟨3, 13, 0, 0, 0, 0, 0, 0, 0⟩, ⟨8, 13, 1, 0, 0, 0, 0, 0, 0⟩], [⟨3, 14, 0, 0, 0, 0, 0, 0, 0⟩, ⟨8, 14, 1, 0, 0, 0, 0, 0, 0⟩]],
      [⟨3, 14, 0, 0, 0, 0, 0, 0, 1⟩, ⟨8, 14, 1, 0, 0, 0, 0, 0, 1⟩]⟩,
    ⟨1, -1, 16, 6,
      [[⟨2, 8, 0, 0, 0, 0, 0, 0, 0⟩, ⟨2, 8, 1, 0, 1, 0, 0, 0, 0⟩], [⟨2, 9, 0, 0, 0, 0, 0, 0, 0⟩, ⟨2, 9, 1, 0, 1, 0, 0, 0, 0⟩], [⟨2, 12, 0, 0, 0, 0, 0, 0, 0⟩, ⟨2, 12, 1, 0, 1, 0, 0, 0, 0⟩], [⟨2, 13, 0, 0, 0, 0, 0, 0, 0⟩, ⟨2, 13, 1, 0, 1, 0, 0, 0, 0⟩]],
      [⟨2, 12, 0, 0, 0, 0, 0, 0, 2⟩, ⟨2, 12, 1, 0, 1, 0, 0, 0, 2⟩]⟩,
    ⟨1, -1, 17, 6,
      [[⟨2, 10, 0, 0, 0, 0, 0, 0, 0⟩, ⟨2, 10, 1, 0, 1, 0, 0, 0, 0⟩], [⟨2, 11, 0, 0, 0, 0, 0, 0, 0⟩, ⟨2, 11, 1, 0, 1, 0, 0, 0, 0⟩], [⟨2, 12, 0, 0, 0, 0, 0, 0, 0⟩, ⟨2, 12, 1, 0, 1, 0, 0, 0, 0⟩], [⟨2, 14, 0, 0, 0, 0, 0, 0, 0⟩, ⟨2, 14, 1, 0, 1, 0, 0, 0, 0⟩]],
      [⟨2, 10, 0, 0, 0, 0, 0, 0, 4⟩, ⟨2, 10, 1, 0, 1, 0, 0, 0, 4⟩]⟩,
    ⟨1, -1, 18, 7,
      [[⟨2, 6, 0, 0, 0, 0, 0, 0, 0⟩, ⟨2, 6, 1, 0, 1, 0, 0, 0, 0⟩], [⟨2, 7, 0, 0, 0, 0, 0, 0, 0⟩, ⟨2, 7, 1, 0, 1, 0, 0, 0, 0⟩], [⟨2, 8, 0, 0, 0, 0, 0, 0, 0⟩, ⟨2, 8, 1, 0, 1, 0, 0, 0, 0⟩], [⟨2, 9, 0, 0, 0, 0, 0, 0, 0⟩, ⟨2, 9, 1, 0, 1, 0, 0, 0, 0⟩], [⟨8, 10, 0, 0, 0, 0, 0, 0, 0⟩, ⟨8, 10, 1, 0, 1, 0, 0, 0, 0⟩], [⟨8, 11, 0, 0, 0, 0, 0, 0, 0⟩, ⟨8, 11, 1, 0, 1, 0, 0, 0, 0⟩]],
      [⟨2, 7, 0, 0, 0, 0, 0, 0, 4⟩, ⟨2, 7, 1, 0, 1, 0, 0, 0, 4⟩]⟩]⟩,
  ⟨1, 1, 0, 0, 0, [(0, 1, 0), (0, -1, 0), (1, 0, 1)], 1, 0, 1, 1, 0, 0, 0, 0,
   [⟨1, 0, 0, 7,
      [[⟨3, 2, 0, 0, 0, 0, 0, 0, 0⟩, ⟨3, 2, 1, 0, 1, 0, 0, 0, 0⟩], [⟨3, 7, 0, 0, 0, 0, 0, 0, 0⟩, ⟨3, 7, 1, 0, 1, 0, 0, 0, 0⟩], [⟨9, 4, 0, 0, 0, 0, 0, 0, 0⟩, ⟨9, 4, 1, 0, 1, 0, 0, 0, 0⟩], [⟨9, 14, 0, 0, 0, 0, 0, 0, 0⟩, ⟨9, 14, 1, 0, 1, 0, 0, 0, 0⟩]],
      [⟨3, 2, 0, 0, 0, 0, 0, 0, 0⟩, ⟨3, 2, 1, 0, 1, 0, 0, 0, 0⟩]⟩,
    ⟨1, 0, 1, 5,
      [[⟨0, 6, 0, 0, 0, 0, 0, 0, 0⟩, ⟨3, 6, 1, 0, 0, 0, 0, 0, 0⟩], [⟨4, 13, 0, 0, 0, 0, 0, 0, 0⟩, ⟨9, 13, 1, 0, 0, 0, 0, 0, 0⟩], [⟨3, 3, 0, 0, 0, 0, 0, 0, 0⟩, ⟨3, 3, 1, 0, 1, 0, 0, 0, 0⟩], [⟨9, 5, 0, 0, 0, 0, 0, 0, 0⟩, ⟨9, 5, 1, 0, 1, 0, 0, 0, 0⟩]],
      [⟨0, 6, 0, 0, 0, 0, 0, 0, 3⟩, ⟨3, 6, 1, 0, 0, 0, 0, 0, 3⟩]⟩,
    ⟨1, 0, 2, 6,
      [[⟨3, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨3, 0, 1, 0, 1, 0, 0, 0, 0⟩], [⟨3, 3, 0, 0, 0, 0, 0, 0, 0⟩, ⟨3, 3, 1, 0, 1, 0, 0, 0, 0⟩], [⟨3, 8, 0, 0, 0, 0, 0, 0, 0⟩, ⟨3, 8, 1, 0, 1, 0, 0, 0, 0⟩], [⟨3, 12, 0, 0, 0, 0, 0, 0, 0⟩, ⟨3, 12, 1, 0, 1, 0, 0, 0, 0⟩]],
      [⟨3, 3, 0, 0, 0, 0, 0, 0, 1⟩, ⟨3, 3, 1, 0, 1, 0, 0, 0, 1⟩]⟩,
    ⟨1, 0, 3, 5,
      [[⟨3, 1, 0, 0, 0, 0, 0, 0, 0⟩, ⟨3, 1, 1, 0, 1, 0, 0, 0, 0⟩], [⟨3, 2, 0, 0, 0, 0, 0, 0, 0⟩, ⟨3, 2, 1, 0, 1, 0, 0, 0, 0⟩], [⟨3, 10, 0, 0, 0, 0, 0, 0, 0⟩, ⟨3, 10, 1, 0, 1, 0, 0, 0, 0⟩], [⟨3, 12, 0, 0, 0, 0, 0, 0, 0⟩, ⟨3, 12, 1, 0, 1, 0, 0, 0, 0⟩]],
      [⟨3, 10, 0, 0, 0, 0, 0, 0, 2⟩, ⟨3, 10, 1, 0, 1, 0, 0, 0, 2⟩]⟩,
    ⟨1, 0, 4, 4,
      [[⟨2, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨8, 0, 0, 0, 0, 1, 0, 0, 0⟩], [⟨3, 5, 0, 0, 0, 0, 0, 0, 0⟩, ⟨3, 5, 1, 0, 1, 0, 0, 0, 0⟩], [⟨3, 11, 0, 0, 0, 0, 0, 0, 0⟩, ⟨3, 11, 1, 0, 1, 0, 0, 0, 0⟩], [⟨3, 14, 0, 0, 0, 0, 0, 0, 0⟩, ⟨3, 14, 1, 0, 1, 0, 0, 0, 0⟩]],
      [⟨3, 5, 0, 0, 0, 0, 0, 0, 3⟩, ⟨3, 5, 1, 0, 1, 0, 0, 0, 3⟩]⟩,
    ⟨1, 0, 5, 3,
      [[⟨0, 9, 0, 0, 0, 0, 0, 0, 0⟩, ⟨3, 9, 1, 0, 0, 0, 0, 0, 0⟩], [⟨0, 13, 0, 0, 0, 0, 0, 0, 0⟩, ⟨3, 13, 1, 0, 0, 0, 0, 0, 0⟩], [⟨2, 1, 0, 0, 0, 0, 0, 0, 0⟩, ⟨8, 1, 0, 0, 0, 1, 0, 0, 0⟩], [⟨3, 4, 0, 0, 0, 0, 0, 0, 0⟩, ⟨3, 4, 1, 0, 1, 0, 0, 0, 0⟩]],
      [⟨0, 9, 0, 0, 0, 0, 0, 0, 3⟩, ⟨3, 9, 1, 0, 0, 0, 0, 0, 3⟩]⟩,
    ⟨1, 0, 6, 9,
      [[⟨3, 7, 0, 0, 0, 0, 0, 0, 0⟩, ⟨3, 7, 1, 0, 1, 0, 0, 0, 0⟩], [⟨3, 15, 0, 0, 0, 0, 0, 0, 0⟩, ⟨3, 15, 1, 0, 1, 0, 0, 0, 0⟩], [⟨3, 18, 0, 0, 0, 0, 0, 0, 0⟩, ⟨3, 18, 1, 0, 1, 0, 0, 0, 0⟩], [⟨3, 1, 0, 0, 1, 0, 0, 0, 0⟩, ⟨3, 1, 1, 0, 2, 0, 0, 0, 0⟩], [⟨3, 10, 0, 0, 1, 0, 0, 0, 0⟩, ⟨3, 10, 1, 0, 2, 0, 0, 0, 0⟩]],
      [⟨3, 7, 0, 0, 0, 0, 0, 0, 1⟩, ⟨3, 7, 1, 0, 1, 0, 0, 0, 1⟩]⟩,
    ⟨1, 0, 7, 8,
      [[⟨3, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨3, 0, 1, 0, 1, 0, 0, 0, 0⟩], [⟨3, 6, 0, 0, 0, 0, 0, 0, 0⟩, ⟨3, 6, 1, 0, 1, 0, 0, 0, 0⟩], [⟨3, 8, 0, 0, 0, 0, 0, 0, 0⟩, ⟨3, 8, 1, 0, 1, 0, 0, 0, 0⟩], [⟨3, 15, 0, 0, 0, 0, 0, 0, 0⟩, ⟨3, 15, 1, 0, 1, 0, 0, 0, 0⟩], [⟨3, 18, 0, 0, 0, 0, 0, 0, 0⟩, ⟨3, 18, 1, 0, 1, 0, 0, 0, 0⟩]],
      [⟨3, 0, 0, 0, 0, 0, 0, 0, 1⟩, ⟨3, 0, 1, 0, 1, 0, 0, 0, 1⟩]⟩,
    ⟨1, 0, 8, 7,
      [[⟨3, 2, 0, 0, 0, 0, 0, 0, 0⟩, ⟨3, 2, 1, 0, 1, 0, 0, 0, 0⟩], [⟨3, 7, 0, 0, 0, 0, 0, 0, 0⟩, ⟨3, 7, 1, 0, 1, 0, 0, 0, 0⟩], [⟨3, 9, 0, 0, 0, 0, 0, 0, 0⟩, ⟨3, 9, 1, 0, 1, 0, 0, 0, 0⟩], [⟨3, 16, 0, 0, 0, 0, 0, 0, 0⟩, ⟨3, 16, 1, 0, 1, 0, 0, 0, 0⟩], [⟨3, 18, 0, 0, 0, 0, 0, 0, 0⟩, ⟨3, 18, 1, 0, 1, 0, 0, 0, 0⟩]],
      [⟨3, 2, 0, 0, 0, 0, 0, 0, 2⟩, ⟨3, 2, 1, 0, 1, 0, 0, 0, 2⟩]⟩,
    ⟨1, 0, 9, 7,
      [[⟨3, 8, 0, 0, 0, 0, 0, 0, 0⟩, ⟨3, 8, 1, 0, 1, 0, 0, 0, 0⟩], [⟨3, 16, 0, 0, 0, 0, 0, 0, 0⟩, ⟨3, 16, 1, 0, 1, 0, 0, 0, 0⟩], [⟨3, 18, 0, 0, 0, 0, 0, 0, 0⟩, ⟨3, 18, 1, 0, 1, 0, 0, 0, 0⟩], [⟨3, 5, 0, 0, 1, 0, 0, 0, 0⟩, ⟨3, 5, 1, 0, 2, 0, 0, 0, 0⟩], [⟨3, 11, 0, 0, 1, 0, 0, 0, 0⟩, ⟨3, 11, 1, 0, 2, 0, 0, 0, 0⟩]],
      [⟨3, 16, 0, 0, 0, 0, 0, 0, 1⟩, ⟨3, 16, 1, 0, 1, 0, 0, 0, 1⟩]⟩,
    ⟨1, 0, 10, 4,
      [[⟨0, 6, 0, 0, 0, 0, 0, 0, 0⟩, ⟨3, 6, 1, 0, 0, 0, 0, 0, 0⟩], [⟨0, 18, 0, 0, 0, 0, 0, 0, 0⟩, ⟨3, 18, 1, 0, 0, 0, 0, 0, 0⟩], [⟨3, 3, 0, 0, 0, 0, 0, 0, 0⟩, ⟨3, 3, 1, 0, 1, 0, 0, 0, 0⟩], [⟨3, 11, 0, 0, 0, 0, 0, 0, 0⟩, ⟨3, 11, 1, 0, 1, 0, 0, 0, 0⟩], [⟨3, 17, 0, 0, 0, 0, 0, 0, 0⟩, ⟨3, 17, 1, 0, 1, 0, 0, 0, 0⟩]],
      [⟨0, 18, 0, 0, 0, 0, 0, 0, 4⟩, ⟨3, 18, 1, 0, 0, 0, 0, 0, 4⟩]⟩,
    ⟨1, 0, 11, 3,
      [[⟨0, 9, 0, 0, 0, 0, 0, 0, 0⟩, ⟨3, 9, 1, 0, 0, 0, 0, 0, 0⟩], [⟨0, 18, 0, 0, 0, 0, 0, 0, 0⟩, ⟨3, 18, 1, 0, 0, 0, 0, 0, 0⟩], [⟨3, 4, 0, 0, 0, 0, 0, 0, 0⟩, ⟨3, 4, 1, 0, 1, 0, 0, 0, 0⟩], [⟨3, 10, 0, 0, 0, 0, 0, 0, 0⟩, ⟨3, 10, 1, 0, 1, 0, 0, 0, 0⟩], [⟨3, 17, 0, 0, 0, 0, 0, 0, 0⟩, ⟨3, 17, 1, 0, 1, 0, 0, 0, 0⟩]],
      [⟨0, 9, 0, 0, 0, 0, 0, 0, 4⟩, ⟨3, 9, 1, 0, 0, 0, 0, 0, 4⟩]⟩,
    ⟨1, 0, 12, 5,
      [[⟨3, 2, 0, 0, 0, 0, 0, 0, 0⟩, ⟨3, 2, 1, 0, 1, 0, 0, 0, 0⟩], [⟨3, 3, 0, 0, 0, 0, 0, 0, 0⟩, ⟨3, 3, 1, 0, 1, 0, 0, 0, 0⟩], [⟨3, 16, 0, 0, 0, 0, 0, 0, 0⟩, ⟨3, 16, 1, 0, 1, 0, 0, 0, 0⟩], [⟨3, 17, 0, 0, 0, 0, 0, 0, 0⟩, ⟨3, 17, 1, 0, 1, 0, 0, 0, 0⟩]],
      [⟨3, 17, 0, 0, 0, 0, 0, 0, 2⟩, ⟨3, 17, 1, 0, 1, 0, 0, 0, 2⟩]⟩,
    ⟨1, 0, 13, 7,
      [[⟨2, 15, 0, 0, 0, 0, 0, 0, 0⟩, ⟨8, 15, 0, 0, 0, 1, 0, 0, 0⟩], [⟨3, 16, 0, 0, 0, 0, 0, 0, 0⟩, ⟨3, 16, 1, 0, 1, 0, 0, 0, 0⟩], [⟨8, 1, 0, 0, 0, 0, 0, 0, 0⟩, ⟨8, 1, 0, 0, 0, 1, 0, 1, 0⟩], [⟨3, 5, 0, 0, 1, 0, 0, 0, 0⟩, ⟨3, 5, 1, 0, 2, 0, 0, 0, 0⟩]],
      [⟨2, 15, 0, 0, 0, 0, 0, 0, 2⟩, ⟨8, 15, 0, 0, 0, 1, 0, 0, 2⟩]⟩,
    ⟨1, 0, 14, 5,
      [[⟨2, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨8, 0, 0, 0, 0, 1, 0, 0, 0⟩], [⟨2, 15, 0, 0, 0, 0, 0, 0, 0⟩, ⟨8, 15, 0, 0, 0, 1, 0, 0, 0⟩], [⟨3, 4, 0, 0, 0, 0, 0, 0, 0⟩, ⟨3, 4, 1, 0, 1, 0, 0, 0, 0⟩], [⟨3, 17, 0, 0, 0, 0, 0, 0, 0⟩, ⟨3, 17, 1, 0, 1, 0, 0, 0, 0⟩]],
      [⟨3, 4, 0, 0, 0, 0, 0, 0, 3⟩, ⟨3, 4, 1, 0, 1, 0, 0, 0, 3⟩]⟩,
    ⟨1, 0, 15, 9,
      [[⟨3, 6, 0, 0, 0, 0, 0, 0, 0⟩, ⟨3, 6, 1, 0, 1, 0, 0, 0, 0⟩], [⟨3, 7, 0, 0, 0, 0, 0, 0, 0⟩, ⟨3, 7, 1, 0, 1, 0, 0, 0, 0⟩], [⟨9, 13, 0, 0, 0, 0, 0, 0, 0⟩, ⟨9, 13, 1, 0, 1, 0, 0, 0, 0⟩], [⟨9, 14, 0, 0, 0, 0, 0, 0, 0⟩, ⟨9, 14, 1, 0, 1, 0, 0, 0, 0⟩]],
      [⟨3, 7, 0, 0, 0, 0, 0, 0, 3⟩, ⟨3, 7, 1, 0, 1, 0, 0, 0, 3⟩]⟩,
    ⟨1, 0, 16, 6,
      [[⟨3, 8, 0, 0, 0, 0, 0, 0, 0⟩, ⟨3, 8, 1, 0, 1, 0, 0, 0, 0⟩], [⟨3, 9, 0, 0, 0, 0, 0, 0, 0⟩, ⟨3, 9, 1, 0, 1, 0, 0, 0, 0⟩], [⟨3, 12, 0, 0, 0, 0, 0, 0, 0⟩, ⟨3, 12, 1, 0, 1, 0, 0, 0, 0⟩], [⟨3, 13, 0, 0, 0, 0, 0, 0, 0⟩, ⟨3, 13, 1, 0, 1, 0, 0, 0, 0⟩]],
      [⟨3, 12, 0, 0, 0, 0, 0, 0, 2⟩, ⟨3, 12, 1, 0, 1, 0, 0, 0, 2⟩]⟩,
    ⟨1, 0, 17, 4,
      [[⟨3, 10, 0, 0, 0, 0, 0, 0, 0⟩, ⟨3, 10, 1, 0, 1, 0, 0, 0, 0⟩], [⟨3, 11, 0, 0, 0, 0, 0, 0, 0⟩, ⟨3, 11, 1, 0, 1, 0, 0, 0, 0⟩], [⟨3, 12, 0, 0, 0, 0, 0, 0, 0⟩, ⟨3, 12, 1, 0, 1, 0, 0, 0, 0⟩], [⟨3, 14, 0, 0, 0, 0, 0, 0, 0⟩, ⟨3, 14, 1, 0, 1, 0, 0, 0, 0⟩]],
      [⟨3, 11, 0, 0, 0, 0, 0, 0, 4⟩, ⟨3, 11, 1, 0, 1, 0, 0, 0, 4⟩]⟩,
    ⟨1, 0, 18, 8,
      [[⟨3, 6, 0, 0, 0, 0, 0, 0, 0⟩, ⟨3, 6, 1, 0, 1, 0, 0, 0, 0⟩], [⟨3, 7, 0, 0, 0, 0, 0, 0, 0⟩, ⟨3, 7, 1, 0, 1, 0, 0, 0, 0⟩], [⟨3, 8, 0, 0, 0, 0, 0, 0, 0⟩, ⟨3, 8, 1, 0, 1, 0, 0, 0, 0⟩], [⟨3, 9, 0, 0, 0, 0, 0, 0, 0⟩, ⟨3, 9, 1, 0, 1, 0, 0, 0, 0⟩], [⟨3, 10, 0, 0, 1, 0, 0, 0, 0⟩, ⟨3, 10, 1, 0, 2, 0, 0, 0, 0⟩], [⟨3, 11, 0, 0, 1, 0, 0, 0, 0⟩, ⟨3, 11, 1, 0, 2, 0, 0, 0, 0⟩]],
      [⟨3, 8, 0, 0, 0, 0, 0, 0, 4⟩, ⟨3, 8, 1, 0, 1, 0, 0, 0, 4⟩]⟩]⟩,
  ⟨1, 0, 1, 0, 0, [(-1, 0, 0), (1, 0, 0), (0, 1, 1)], 0, 1, 1, 1, 0, 0, 0, 0,
   [⟨0, 1, 0, 7,
      [[⟨4, 2, 0, 0, 0, 0, 0, 0, 0⟩, ⟨4, 2, 1, 0, 1, 0, 0, 0, 0⟩], [⟨4, 7, 0, 0, 0, 0, 0, 0, 0⟩, ⟨4, 7, 1, 0, 1, 0, 0, 0, 0⟩], [⟨4, 4, 0, 0, 1, 0, 0, 0, 0⟩, ⟨4, 4, 1, 0, 2, 0, 0, 0, 0⟩], [⟨4, 14, 0, 0, 1, 0, 0, 0, 0⟩, ⟨4, 14, 1, 0, 2, 0, 0, 0, 0⟩]],
      [⟨4, 2, 0, 0, 0, 0, 0, 0, 0⟩, ⟨4, 2, 1, 0, 1, 0, 0, 0, 0⟩]⟩,
    ⟨0, 1, 1, 7,
      [[⟨5, 6, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 6, 1, 0, 0, 0, 0, 0, 0⟩], [⟨10, 13, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 13, 1, 0, 1, 0, 0, 0, 0⟩], [⟨4, 3, 0, 0, 0, 0, 0, 0, 0⟩, ⟨4, 3, 1, 0, 1, 0, 0, 0, 0⟩], [⟨4, 5, 0, 0, 1, 0, 0, 0, 0⟩, ⟨4, 5, 1, 0, 2, 0, 0, 0, 0⟩]],
      [⟨5, 6, 0, 0, 0, 0, 0, 0, 3⟩, ⟨10, 6, 1, 0, 0, 0, 0, 0, 3⟩]⟩,
    ⟨0, 1, 2, 6,
      [[⟨4, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨4, 0, 1, 0, 1, 0, 0, 0, 0⟩], [⟨4, 3, 0, 0, 0, 0, 0, 0, 0⟩, ⟨4, 3, 1, 0, 1, 0, 0, 0, 0⟩], [⟨4, 8, 0, 0, 0, 0, 0, 0, 0⟩, ⟨4, 8, 1, 0, 1, 0, 0, 0, 0⟩], [⟨4, 12, 0, 0, 0, 0, 0, 0, 0⟩, ⟨4, 12, 1, 0, 1, 0, 0, 0, 0⟩]],
      [⟨4, 12, 0, 0, 0, 0, 0, 0, 0⟩, ⟨4, 12, 1, 0, 1, 0, 0, 0, 0⟩]⟩,
    ⟨0, 1, 3, 6,
      [[⟨4, 1, 0, 0, 0, 0, 0, 0, 0⟩, ⟨4, 1, 1, 0, 1, 0, 0, 0, 0⟩], [⟨4, 2, 0, 0, 0, 0, 0, 0, 0⟩, ⟨4, 2, 1, 0, 1, 0, 0, 0, 0⟩], [⟨4, 10, 0, 0, 0, 0, 0, 0, 0⟩, ⟨4, 10, 1, 0, 1, 0, 0, 0, 0⟩], [⟨4, 12, 0, 0, 0, 0, 0, 0, 0⟩, ⟨4, 12, 1, 0, 1, 0, 0, 0, 0⟩]],
      [⟨4, 10, 0, 0, 0, 0, 0, 0, 2⟩, ⟨4, 10, 1, 0, 1, 0, 0, 0, 2⟩]⟩,
    ⟨0, 1, 4, 3,
      [[⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨4, 0, 1, 0, 0, 0, 0, 0, 0⟩], [⟨4, 5, 0, 0, 0, 0, 0, 0, 0⟩, ⟨4, 5, 1, 0, 1, 0, 0, 0, 0⟩], [⟨4, 11, 0, 0, 0, 0, 0, 0, 0⟩, ⟨4, 11, 1, 0, 1, 0, 0, 0, 0⟩], [⟨4, 14, 0, 0, 0, 0, 0, 0, 0⟩, ⟨4, 14, 1, 0, 1, 0, 0, 0, 0⟩]],
      [⟨0, 0, 0, 0, 0, 0, 0, 0, 2⟩, ⟨4, 0, 1, 0, 0, 0, 0, 0, 2⟩]⟩,
    ⟨0, 1, 5, 3,
      [[⟨5, 9, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 9, 1, 0, 0, 0, 0, 0, 0⟩], [⟨5, 13, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 13, 1, 0, 0, 0, 0, 0, 0⟩], [⟨0, 1, 0, 0, 0, 0, 0, 0, 0⟩, ⟨4, 1, 1, 0, 0, 0, 0, 0, 0⟩], [⟨4, 4, 0, 0, 0, 0, 0, 0, 0⟩, ⟨4, 4, 1, 0, 1, 0, 0, 0, 0⟩]],
      [⟨0, 1, 0, 0, 0, 0, 0, 0, 3⟩, ⟨4, 1, 1, 0, 0, 0, 0, 0, 3⟩]⟩,
    ⟨0, 1, 6, 9,
      [[⟨4, 7, 0, 0, 0, 0, 0, 0, 0⟩, ⟨4, 7, 1, 0, 1, 0, 0, 0, 0⟩], [⟨4, 15, 0, 0, 0, 0, 0, 0, 0⟩, ⟨4, 15, 1, 0, 1, 0, 0, 0, 0⟩], [⟨4, 18, 0, 0, 0, 0, 0, 0, 0⟩, ⟨4, 18, 1, 0, 1, 0, 0, 0, 0⟩], [⟨9, 1, 0, 0, 0, 0, 0, 0, 0⟩, ⟨9, 1, 0, 0, 0, 1, 0, 1, 0⟩], [⟨9, 10, 0, 0, 0, 0, 0, 0, 0⟩, ⟨9, 10, 0, 0, 0, 1, 0, 1, 0⟩]],
      [⟨4, 7, 0, 0, 0, 0, 0, 0, 1⟩, ⟨4, 7, 1, 0, 1, 0, 0, 0, 1⟩]⟩,
    ⟨0, 1, 7, 8,
      [[⟨4, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨4, 0, 1, 0, 1, 0, 0, 0, 0⟩], [⟨4, 6, 0, 0, 0, 0, 0, 0, 0⟩, ⟨4, 6, 1, 0, 1, 0, 0, 0, 0⟩], [⟨4, 8, 0, 0, 0, 0, 0, 0, 0⟩, ⟨4, 8, 1, 0, 1, 0, 0, 0, 0⟩], [⟨4, 15, 0, 0, 0, 0, 0, 0, 0⟩, ⟨4, 15, 1, 0, 1, 0, 0, 0, 0⟩], [⟨4, 18, 0, 0, 0, 0, 0, 0, 0⟩, ⟨4, 18, 1, 0, 1, 0, 0, 0, 0⟩]],
      [⟨4, 0, 0, 0, 0, 0, 0, 0, 1⟩, ⟨4, 0, 1, 0, 1, 0, 0, 0, 1⟩]⟩,
    ⟨0, 1, 8, 7,
      [[⟨4, 2, 0, 0, 0, 0, 0, 0, 0⟩, ⟨4, 2, 1, 0, 1, 0, 0, 0, 0⟩], [⟨4, 7, 0, 0, 0, 0, 0, 0, 0⟩, ⟨4, 7, 1, 0, 1, 0, 0, 0, 0⟩], [⟨4, 9, 0, 0, 0, 0, 0, 0, 0⟩, ⟨4, 9, 1, 0, 1, 0, 0, 0, 0⟩], [⟨4, 16, 0, 0, 0, 0, 0, 0, 0⟩, ⟨4, 16, 1, 0, 1, 0, 0, 0, 0⟩], [⟨4, 18, 0, 0, 0, 0, 0, 0, 0⟩, ⟨4, 18, 1, 0, 1, 0, 0, 0, 0⟩]],
      [⟨4, 2, 0, 0, 0, 0, 0, 0, 2⟩, ⟨4, 2, 1, 0, 1, 0, 0, 0, 2⟩]⟩,
    ⟨0, 1, 9, 7,
      [[⟨4, 8, 0, 0, 0, 0, 0, 0, 0⟩, ⟨4, 8, 1, 0, 1, 0, 0, 0, 0⟩], [⟨4, 16, 0, 0, 0, 0, 0, 0, 0⟩, ⟨4, 16, 1, 0, 1, 0, 0, 0, 0⟩], [⟨4, 18, 0, 0, 0, 0, 0, 0, 0⟩, ⟨4, 18, 1, 0, 1, 0, 0, 0, 0⟩], [⟨9, 5, 0, 0, 0, 0, 0, 0, 0⟩, ⟨9, 5, 0, 0, 0, 1, 0, 1, 0⟩], [⟨9, 11, 0, 0, 0, 0, 0, 0, 0⟩, ⟨9, 11, 0, 0, 0, 1, 0, 1, 0⟩]],
      [⟨4, 16, 0, 0, 0, 0, 0, 0, 1⟩, ⟨4, 16, 1, 0, 1, 0, 0, 0, 1⟩]⟩,
    ⟨0, 1, 10, 5,
      [[⟨5, 6, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 6, 1, 0, 0, 0, 0, 0, 0⟩], [⟨5, 18, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 18, 1, 0, 0, 0, 0, 0, 0⟩], [⟨4, 3, 0, 0, 0, 0, 0, 0, 0⟩, ⟨4, 3, 1, 0, 1, 0, 0, 0, 0⟩], [⟨4, 11, 0, 0, 0, 0, 0, 0, 0⟩, ⟨4, 11, 1, 0, 1, 0, 0, 0, 0⟩], [⟨4, 17, 0, 0, 0, 0, 0, 0, 0⟩, ⟨4, 17, 1, 0, 1, 0, 0, 0, 0⟩]],
      [⟨4, 11, 0, 0, 0, 0, 0, 0, 3⟩, ⟨4, 11, 1, 0, 1, 0, 0, 0, 3⟩]⟩,
    ⟨0, 1, 11, 4,
      [[⟨5, 9, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 9, 1, 0, 0, 0, 0, 0, 0⟩], [⟨5, 18, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 18, 1, 0, 0, 0, 0, 0, 0⟩], [⟨4, 4, 0, 0, 0, 0, 0, 0, 0⟩, ⟨4, 4, 1, 0, 1, 0, 0, 0, 0⟩], [⟨4, 10, 0, 0, 0, 0, 0, 0, 0⟩, ⟨4, 10, 1, 0, 1, 0, 0, 0, 0⟩], [⟨4, 17, 0, 0, 0, 0, 0, 0, 0⟩, ⟨4, 17, 1, 0, 1, 0, 0, 0, 0⟩]],
      [⟨4, 4, 0, 0, 0, 0, 0, 0, 2⟩, ⟨4, 4, 1, 0, 1, 0, 0, 0, 2⟩]⟩,
    ⟨0, 1, 12, 5,
      [[⟨4, 2, 0, 0, 0, 0, 0, 0, 0⟩, ⟨4, 2, 1, 0, 1, 0, 0, 0, 0⟩], [⟨4, 3, 0, 0, 0, 0, 0, 0, 0⟩, ⟨4, 3, 1, 0, 1, 0, 0, 0, 0⟩], [⟨4, 16, 0, 0, 0, 0, 0, 0, 0⟩, ⟨4, 16, 1, 0, 1, 0, 0, 0, 0⟩], [⟨4, 17, 0, 0, 0, 0, 0, 0, 0⟩, ⟨4, 17, 1, 0, 1, 0, 0, 0, 0⟩]],
      [⟨4, 17, 0, 0, 0, 0, 0, 0, 2⟩, ⟨4, 17, 1, 0, 1, 0, 0, 0, 2⟩]⟩,
    ⟨0, 1, 13, 5,
      [[⟨0, 15, 0, 0, 0, 0, 0, 0, 0⟩, ⟨4, 15, 1, 0, 0, 0, 0, 0, 0⟩], [⟨4, 16, 0, 0, 0, 0, 0, 0, 0⟩, ⟨4, 16, 1, 0, 1, 0, 0, 0, 0⟩], [⟨3, 1, 0, 0, 0, 0, 0, 0, 0⟩, ⟨9, 1, 0, 0, 0, 1, 0, 0, 0⟩], [⟨9, 5, 0, 0, 0, 0, 0, 0, 0⟩, ⟨9, 5, 0, 0, 0, 1, 0, 1, 0⟩]],
      [⟨0, 15, 0, 0, 0, 0, 0, 0, 2⟩, ⟨4, 15, 1, 0, 0, 0, 0, 0, 2⟩]⟩,
    ⟨0, 1, 14, 3,
      [[⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨4, 0, 1, 0, 0, 0, 0, 0, 0⟩], [⟨0, 15, 0, 0, 0, 0, 0, 0, 0⟩, ⟨4, 15, 1, 0, 0, 0, 0, 0, 0⟩], [⟨4, 4, 0, 0, 0, 0, 0, 0, 0⟩, ⟨4, 4, 1, 0, 1, 0, 0, 0, 0⟩], [⟨4, 17, 0, 0, 0, 0, 0, 0, 0⟩, ⟨4, 17, 1, 0, 1, 0, 0, 0, 0⟩]],
      [⟨0, 0, 0, 0, 0, 0, 0, 0, 3⟩, ⟨4, 0, 1, 0, 0, 0, 0, 0, 3⟩]⟩,
    ⟨0, 1, 15, 9,
      [[⟨4, 6, 0, 0, 0, 0, 0, 0, 0⟩, ⟨4, 6, 1, 0, 1, 0, 0, 0, 0⟩], [⟨4, 7, 0, 0, 0, 0, 0, 0, 0⟩, ⟨4, 7, 1, 0, 1, 0, 0, 0, 0⟩], [⟨4, 13, 0, 0, 1, 0, 0, 0, 0⟩, ⟨4, 13, 1, 0, 2, 0, 0, 0, 0⟩], [⟨4, 14, 0, 0, 1, 0, 0, 0, 0⟩, ⟨4, 14, 1, 0, 2, 0, 0, 0, 0⟩]],
      [⟨4, 7, 0, 0, 0, 0, 0, 0, 3⟩, ⟨4, 7, 1, 0, 1, 0, 0, 0, 3⟩]⟩,
    ⟨0, 1, 16, 6,
      [[⟨4, 8, 0, 0, 0, 0, 0, 0, 0⟩, ⟨4, 8, 1, 0, 1, 0, 0, 0, 0⟩], [⟨4, 9, 0, 0, 0, 0, 0, 0, 0⟩, ⟨4, 9, 1, 0, 1, 0, 0, 0, 0⟩], [⟨4, 12, 0, 0, 0, 0, 0, 0, 0⟩, ⟨4, 12, 1, 0, 1, 0, 0, 0, 0⟩], [⟨4, 13, 0, 0, 0, 0, 0, 0, 0⟩, ⟨4, 13, 1, 0, 1, 0, 0, 0, 0⟩]],
      [⟨4, 12, 0, 0, 0, 0, 0, 0, 2⟩, ⟨4, 12, 1, 0, 1, 0, 0, 0, 2⟩]⟩,
    ⟨0, 1, 17, 4,
      [[⟨4, 10, 0, 0, 0, 0, 0, 0, 0⟩, ⟨4, 10, 1, 0, 1, 0, 0, 0, 0⟩], [⟨4, 11, 0, 0, 0, 0, 0, 0, 0⟩, ⟨4, 11, 1, 0, 1, 0, 0, 0, 0⟩], [⟨4, 12, 0, 0, 0, 0, 0, 0, 0⟩, ⟨4, 12, 1, 0, 1, 0, 0, 0, 0⟩], [⟨4, 14, 0, 0, 0, 0, 0, 0, 0⟩, ⟨4, 14, 1, 0, 1, 0, 0, 0, 0⟩]],
      [⟨4, 14, 0, 0, 0, 0, 0, 0, 3⟩, ⟨4, 14, 1, 0, 1, 0, 0, 0, 3⟩]⟩,
    ⟨0, 1, 18, 8,
      [[⟨4, 6, 0, 0, 0, 0, 0, 0, 0⟩, ⟨4, 6, 1, 0, 1, 0, 0, 0, 0⟩], [⟨4, 7, 0, 0, 0, 0, 0, 0, 0⟩, ⟨4, 7, 1, 0, 1, 0, 0, 0, 0⟩], [⟨4, 8, 0, 0, 0, 0, 0, 0, 0⟩, ⟨4, 8, 1, 0, 1, 0, 0, 0, 0⟩], [⟨4, 9, 0, 0, 0, 0, 0, 0, 0⟩, ⟨4, 9, 1, 0, 1, 0, 0, 0, 0⟩], [⟨9, 10, 0, 0, 0, 0, 0, 0, 0⟩, ⟨9, 10, 0, 0, 0, 1, 0, 1, 0⟩], [⟨9, 11, 0, 0, 0, 0, 0, 0, 0⟩, ⟨9, 11, 0, 0, 0, 1, 0, 1, 0⟩]],
      [⟨4, 8, 0, 0, 0, 0, 0, 0, 4⟩, ⟨4, 8, 1, 0, 1, 0, 0, 0, 4⟩]⟩]⟩,
  ⟨1, -1, 1, 0, 0, [(-1, -1, 0), (1, 1, 0), (-1, 1, 2)], -1, 1, 2, 2, 0, 0, 0, 0,
   [⟨-1, 1, 0, 7,
      [[⟨5, 2, 0, 0, 0, 0, 0, 0, 0⟩, ⟨5, 2, 1, 0, 1, 0, 0, 0, 0⟩], [⟨5, 7, 0, 0, 0, 0, 0, 0, 0⟩, ⟨5, 7, 1, 0, 1, 0, 0, 0, 0⟩], [⟨10, 4, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 4, 0, 0, 0, 1, 0, 1, 0⟩], [⟨10, 14, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 14, 0, 0, 0, 1, 0, 1, 0⟩]],
      [⟨5, 2, 0, 0, 0, 0, 0, 0, 0⟩, ⟨5, 2, 1, 0, 1, 0, 0, 0, 0⟩]⟩,
    ⟨-1, 1, 1, 7,
      [[⟨11, 6, 0, 0, 0, 0, 0, 0, 0⟩, ⟨11, 6, 1, 0, 1, 0, 0, 0, 0⟩], [⟨5, 13, 0, 0, 1, 0, 0, 0, 0⟩, ⟨5, 13, 1, 0, 2, 0, 0, 0, 0⟩], [⟨5, 3, 0, 0, 0, 0, 0, 0, 0⟩, ⟨5, 3, 1, 0, 1, 0, 0, 0, 0⟩], [⟨10, 5, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 5, 0, 0, 0, 1, 0, 1, 0⟩]],
      [⟨5, 3, 0, 0, 0, 0, 0, 0, 0⟩, ⟨5, 3, 1, 0, 1, 0, 0, 0, 0⟩]⟩,
    ⟨-1, 1, 2, 6,
      [[⟨5, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨5, 0, 1, 0, 1, 0, 0, 0, 0⟩], [⟨5, 3, 0, 0, 0, 0, 0, 0, 0⟩, ⟨5, 3, 1, 0, 1, 0, 0, 0, 0⟩], [⟨5, 8, 0, 0, 0, 0, 0, 0, 0⟩, ⟨5, 8, 1, 0, 1, 0, 0, 0, 0⟩], [⟨5, 12, 0, 0, 0, 0, 0, 0, 0⟩, ⟨5, 12, 1, 0, 1, 0, 0, 0, 0⟩]],
      [⟨5, 8, 0, 0, 0, 0, 0, 0, 0⟩, ⟨5, 8, 1, 0, 1, 0, 0, 0, 0⟩]⟩,
    ⟨-1, 1, 3, 6,
      [[⟨5, 1, 0, 0, 0, 0, 0, 0, 0⟩, ⟨5, 1, 1, 0, 1, 0, 0, 0, 0⟩], [⟨5, 2, 0, 0, 0, 0, 0, 0, 0⟩, ⟨5, 2, 1, 0, 1, 0, 0, 0, 0⟩], [⟨5, 10, 0, 0, 0, 0, 0, 0, 0⟩, ⟨5, 10, 1, 0, 1, 0, 0, 0, 0⟩], [⟨5, 12, 0, 0, 0, 0, 0, 0, 0⟩, ⟨5, 12, 1, 0, 1, 0, 0, 0, 0⟩]],
      [⟨5, 12, 0, 0, 0, 0, 0, 0, 1⟩, ⟨5, 12, 1, 0, 1, 0, 0, 0, 1⟩]⟩,
    ⟨-1, 1, 4, 6,
      [[⟨6, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨11, 0, 1, 0, 0, 0, 0, 0, 0⟩], [⟨5, 5, 0, 0, 0, 0, 0, 0, 0⟩, ⟨5, 5, 1, 0, 1, 0, 0, 0, 0⟩], [⟨5, 11, 0, 0, 0, 0, 0, 0, 0⟩, ⟨5, 11, 1, 0, 1, 0, 0, 0, 0⟩], [⟨5, 14, 0, 0, 0, 0, 0, 0, 0⟩, ⟨5, 14, 1, 0, 1, 0, 0, 0, 0⟩]],
      [⟨6, 0, 0, 0, 0, 0, 0, 0, 2⟩, ⟨11, 0, 1, 0, 0, 0, 0, 0, 2⟩]⟩,
    ⟨-1, 1, 5, 7,
      [[⟨11, 9, 0, 0, 0, 0, 0, 0, 0⟩, ⟨11, 9, 1, 0, 1, 0, 0, 0, 0⟩], [⟨11, 13, 0, 0, 0, 0, 0, 0, 0⟩, ⟨11, 13, 1, 0, 1, 0, 0, 0, 0⟩], [⟨6, 1, 0, 0, 0, 0, 0, 0, 0⟩, ⟨11, 1, 1, 0, 0, 0, 0, 0, 0⟩], [⟨5, 4, 0, 0, 0, 0, 0, 0, 0⟩, ⟨5, 4, 1, 0, 1, 0, 0, 0, 0⟩]],
      [⟨5, 4, 0, 0, 0, 0, 0, 0, 1⟩, ⟨5, 4, 1, 0, 1, 0, 0, 0, 1⟩]⟩,
    ⟨-1, 1, 6, 6,
      [[⟨5, 7, 0, 0, 0, 0, 0, 0, 0⟩, ⟨5, 7, 1, 0, 1, 0, 0, 0, 0⟩], [⟨5, 15, 0, 0, 0, 0, 0, 0, 0⟩, ⟨5, 15, 1, 0, 1, 0, 0, 0, 0⟩], [⟨5, 18, 0, 0, 0, 0, 0, 0, 0⟩, ⟨5, 18, 1, 0, 1, 0, 0, 0, 0⟩], [⟨4, 1, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 1, 0, 0, 0, 1, 0, 0, 0⟩], [⟨4, 10, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 10, 0, 0, 0, 1, 0, 0, 0⟩]],
      [⟨5, 18, 0, 0, 0, 0, 0, 0, 0⟩, ⟨5, 18, 1, 0, 1, 0, 0, 0, 0⟩]⟩,
    ⟨-1, 1, 7, 6,
      [[⟨5, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨5, 0, 1, 0, 1, 0, 0, 0, 0⟩], [⟨5, 6, 0, 0, 0, 0, 0, 0, 0⟩, ⟨5, 6, 1, 0, 1, 0, 0, 0, 0⟩], [⟨5, 8, 0, 0, 0, 0, 0, 0, 0⟩, ⟨5, 8, 1, 0, 1, 0, 0, 0, 0⟩], [⟨5, 15, 0, 0, 0, 0, 0, 0, 0⟩, ⟨5, 15, 1, 0, 1, 0, 0, 0, 0⟩], [⟨5, 18, 0, 0, 0, 0, 0, 0, 0⟩, ⟨5, 18, 1, 0, 1, 0, 0, 0, 0⟩]],
      [⟨5, 8, 0, 0, 0, 0, 0, 0, 1⟩, ⟨5, 8, 1, 0, 1, 0, 0, 0, 1⟩]⟩,
    ⟨-1, 1, 8, 5,
      [[⟨5, 2, 0, 0, 0, 0, 0, 0, 0⟩, ⟨5, 2, 1, 0, 1, 0, 0, 0, 0⟩], [⟨5, 7, 0, 0, 0, 0, 0, 0, 0⟩, ⟨5, 7, 1, 0, 1, 0, 0, 0, 0⟩], [⟨5, 9, 0, 0, 0, 0, 0, 0, 0⟩, ⟨5, 9, 1, 0, 1, 0, 0, 0, 0⟩], [⟨5, 16, 0, 0, 0, 0, 0, 0, 0⟩, ⟨5, 16, 1, 0, 1, 0, 0, 0, 0⟩], [⟨5, 18, 0, 0, 0, 0, 0, 0, 0⟩, ⟨5, 18, 1, 0, 1, 0, 0, 0, 0⟩]],
      [⟨5, 9, 0, 0, 0, 0, 0, 0, 0⟩, ⟨5, 9, 1, 0, 1, 0, 0, 0, 0⟩]⟩,
    ⟨-1, 1, 9, 4,
      [[⟨5, 8, 0, 0, 0, 0, 0, 0, 0⟩, ⟨5, 8, 1, 0, 1, 0, 0, 0, 0⟩], [⟨5, 16, 0, 0, 0, 0, 0, 0, 0⟩, ⟨5, 16, 1, 0, 1, 0, 0, 0, 0⟩], [⟨5, 18, 0, 0, 0, 0, 0, 0, 0⟩, ⟨5, 18, 1, 0, 1, 0, 0, 0, 0⟩], [⟨4, 5, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 5, 0, 0, 0, 1, 0, 0, 0⟩], [⟨4, 11, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 11, 0, 0, 0, 1, 0, 0, 0⟩]],
      [⟨4, 5, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 5, 0, 0, 0, 1, 0, 0, 0⟩]⟩,
    ⟨-1, 1, 10, 7,
      [[⟨11, 6, 0, 0, 0, 0, 0, 0, 0⟩, ⟨11, 6, 1, 0, 1, 0, 0, 0, 0⟩], [⟨11, 18, 0, 0, 0, 0, 0, 0, 0⟩, ⟨11, 18, 1, 0, 1, 0, 0, 0, 0⟩], [⟨5, 3, 0, 0, 0, 0, 0, 0, 0⟩, ⟨5, 3, 1, 0, 1, 0, 0, 0, 0⟩], [⟨5, 11, 0, 0, 0, 0, 0, 0, 0⟩, ⟨5, 11, 1, 0, 1, 0, 0, 0, 0⟩], [⟨5, 17, 0, 0, 0, 0, 0, 0, 0⟩, ⟨5, 17, 1, 0, 1, 0, 0, 0, 0⟩]],
      [⟨5, 3, 0, 0, 0, 0, 0, 0, 2⟩, ⟨5, 3, 1, 0, 1, 0, 0, 0, 2⟩]⟩,
    ⟨-1, 1, 11, 7,
      [[⟨11, 9, 0, 0, 0, 0, 0, 0, 0⟩, ⟨11, 9, 1, 0, 1, 0, 0, 0, 0⟩], [⟨11, 18, 0, 0, 0, 0, 0, 0, 0⟩, ⟨11, 18, 1, 0, 1, 0, 0, 0, 0⟩], [⟨5, 4, 0, 0, 0, 0, 0, 0, 0⟩, ⟨5, 4, 1, 0, 1, 0, 0, 0, 0⟩], [⟨5, 10, 0, 0, 0, 0, 0, 0, 0⟩, ⟨5, 10, 1, 0, 1, 0, 0, 0, 0⟩], [⟨5, 17, 0, 0, 0, 0, 0, 0, 0⟩, ⟨5, 17, 1, 0, 1, 0, 0, 0, 0⟩]],
      [⟨5, 4, 0, 0, 0, 0, 0, 0, 2⟩, ⟨5, 4, 1, 0, 1, 0, 0, 0, 2⟩]⟩,
    ⟨-1, 1, 12, 5,
      [[⟨5, 2, 0, 0, 0, 0, 0, 0, 0⟩, ⟨5, 2, 1, 0, 1, 0, 0, 0, 0⟩], [⟨5, 3, 0, 0, 0, 0, 0, 0, 0⟩, ⟨5, 3, 1, 0, 1, 0, 0, 0, 0⟩], [⟨5, 16, 0, 0, 0, 0, 0, 0, 0⟩, ⟨5, 16, 1, 0, 1, 0, 0, 0, 0⟩], [⟨5, 17, 0, 0, 0, 0, 0, 0, 0⟩, ⟨5, 17, 1, 0, 1, 0, 0, 0, 0⟩]],
      [⟨5, 16, 0, 0, 0, 0, 0, 0, 2⟩, ⟨5, 16, 1, 0, 1, 0, 0, 0, 2⟩]⟩,
    ⟨-1, 1, 13, 3,
      [[⟨6, 15, 0, 0, 0, 0, 0, 0, 0⟩, ⟨11, 15, 1, 0, 0, 0, 0, 0, 0⟩], [⟨5, 16, 0, 0, 0, 0, 0, 0, 0⟩, ⟨5, 16, 1, 0, 1, 0, 0, 0, 0⟩], [⟨0, 1, 0, 0, 0, 0, 0, 0, 0⟩, ⟨5, 1, 1, 0, 0, 0, 0, 0, 0⟩], [⟨4, 5, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 5, 0, 0, 0, 1, 0, 0, 0⟩]],
      [⟨0, 1, 0, 0, 0, 0, 0, 0, 1⟩, ⟨5, 1, 1, 0, 0, 0, 0, 0, 1⟩]⟩,
    ⟨-1, 1, 14, 5,
      [[⟨6, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨11, 0, 1, 0, 0, 0, 0, 0, 0⟩], [⟨6, 15, 0, 0, 0, 0, 0, 0, 0⟩, ⟨11, 15, 1, 0, 0, 0, 0, 0, 0⟩], [⟨5, 4, 0, 0, 0, 0, 0, 0, 0⟩, ⟨5, 4, 1, 0, 1, 0, 0, 0, 0⟩], [⟨5, 17, 0, 0, 0, 0, 0, 0, 0⟩, ⟨5, 17, 1, 0, 1, 0, 0, 0, 0⟩]],
      [⟨6, 15, 0, 0, 0, 0, 0, 0, 3⟩, ⟨11, 15, 1, 0, 0, 0, 0, 0, 3⟩]⟩,
    ⟨-1, 1, 15, 7,
      [[⟨5, 6, 0, 0, 0, 0, 0, 0, 0⟩, ⟨5, 6, 1, 0, 1, 0, 0, 0, 0⟩], [⟨5, 7, 0, 0, 0, 0, 0, 0, 0⟩, ⟨5, 7, 1, 0, 1, 0, 0, 0, 0⟩], [⟨10, 13, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 13, 0, 0, 0, 1, 0, 1, 0⟩], [⟨10, 14, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 14, 0, 0, 0, 1, 0, 1, 0⟩]],
      [⟨5, 6, 0, 0, 0, 0, 0, 0, 1⟩, ⟨5, 6, 1, 0, 1, 0, 0, 0, 1⟩]⟩,
    ⟨-1, 1, 16, 4,
      [[⟨5, 8, 0, 0, 0, 0, 0, 0, 0⟩, ⟨5, 8, 1, 0, 1, 0, 0, 0, 0⟩], [⟨5, 9, 0, 0, 0, 0, 0, 0, 0⟩, ⟨5, 9, 1, 0, 1, 0, 0, 0, 0⟩], [⟨5, 12, 0, 0, 0, 0, 0, 0, 0⟩, ⟨5, 12, 1, 0, 1, 0, 0, 0, 0⟩], [⟨5, 13, 0, 0, 0, 0, 0, 0, 0⟩, ⟨5, 13, 1, 0, 1, 0, 0, 0, 0⟩]],
      [⟨5, 13, 0, 0, 0, 0, 0, 0, 1⟩, ⟨5, 13, 1, 0, 1, 0, 0, 0, 1⟩]⟩,
    ⟨-1, 1, 17, 6,
      [[⟨5, 10, 0, 0, 0, 0, 0, 0, 0⟩, ⟨5, 10, 1, 0, 1, 0, 0, 0, 0⟩], [⟨5, 11, 0, 0, 0, 0, 0, 0, 0⟩, ⟨5, 11, 1, 0, 1, 0, 0, 0, 0⟩], [⟨5, 12, 0, 0, 0, 0, 0, 0, 0⟩, ⟨5, 12, 1, 0, 1, 0, 0, 0, 0⟩], [⟨5, 14, 0, 0, 0, 0, 0, 0, 0⟩, ⟨5, 14, 1, 0, 1, 0, 0, 0, 0⟩]],
      [⟨5, 12, 0, 0, 0, 0, 0, 0, 3⟩, ⟨5, 12, 1, 0, 1, 0, 0, 0, 3⟩]⟩,
    ⟨-1, 1, 18, 5,
      [[⟨5, 6, 0, 0, 0, 0, 0, 0, 0⟩, ⟨5, 6, 1, 0, 1, 0, 0, 0, 0⟩], [⟨5, 7, 0, 0, 0, 0, 0, 0, 0⟩, ⟨5, 7, 1, 0, 1, 0, 0, 0, 0⟩], [⟨5, 8, 0, 0, 0, 0, 0, 0, 0⟩, ⟨5, 8, 1, 0, 1, 0, 0, 0, 0⟩], [⟨5, 9, 0, 0, 0, 0, 0, 0, 0⟩, ⟨5, 9, 1, 0, 1, 0, 0, 0, 0⟩], [⟨4, 10, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 10, 0, 0, 0, 1, 0, 0, 0⟩], [⟨4, 11, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 11, 0, 0, 0, 1, 0, 0, 0⟩]],
      [⟨5, 9, 0, 0, 0, 0, 0, 0, 2⟩, ⟨5, 9, 1, 0, 1, 0, 0, 0, 2⟩]⟩]⟩,
  ⟨1, -1, 0, 0, 0, [(0, -1, 0), (0, 1, 0), (-1, 0, 1)], -1, 0, 1, 1, 0, 0, 0, 0,
   [⟨-1, 0, 0, 5,
      [[⟨6, 2, 0, 0, 0, 0, 0, 0, 0⟩, ⟨6, 2, 1, 0, 1, 0, 0, 0, 0⟩], [⟨6, 7, 0, 0, 0, 0, 0, 0, 0⟩, ⟨6, 7, 1, 0, 1, 0, 0, 0, 0⟩], [⟨5, 4, 0, 0, 0, 0, 0, 0, 0⟩, ⟨11, 4, 0, 0, 0, 1, 0, 0, 0⟩], [⟨5, 14, 0, 0, 0, 0, 0, 0, 0⟩, ⟨11, 14, 0, 0, 0, 1, 0, 0, 0⟩]],
      [⟨6, 7, 0, 0, 0, 0, 0, 0, 0⟩, ⟨6, 7, 1, 0, 1, 0, 0, 0, 0⟩]⟩,
    ⟨-1, 0, 1, 7,
      [[⟨6, 6, 0, 0, 1, 0, 0, 0, 0⟩, ⟨6, 6, 1, 0, 2, 0, 0, 0, 0⟩], [⟨11, 13, 0, 0, 0, 0, 0, 0, 0⟩, ⟨11, 13, 0, 0, 0, 1, 0, 1, 0⟩], [⟨6, 3, 0, 0, 0, 0, 0, 0, 0⟩, ⟨6, 3, 1, 0, 1, 0, 0, 0, 0⟩], [⟨5, 5, 0, 0, 0, 0, 0, 0, 0⟩, ⟨11, 5, 0, 0, 0, 1, 0, 0, 0⟩]],
      [⟨6, 3, 0, 0, 0, 0, 0, 0, 0⟩, ⟨6, 3, 1, 0, 1, 0, 0, 0, 0⟩]⟩,
    ⟨-1, 0, 2, 5,
      [[⟨6, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨6, 0, 1, 0, 1, 0, 0, 0, 0⟩], [⟨6, 3, 0, 0, 0, 0, 0, 0, 0⟩, ⟨6, 3, 1, 0, 1, 0, 0, 0, 0⟩], [⟨6, 8, 0, 0, 0, 0, 0, 0, 0⟩, ⟨6, 8, 1, 0, 1, 0, 0, 0, 0⟩], [⟨6, 12, 0, 0, 0, 0, 0, 0, 0⟩, ⟨6, 12, 1, 0, 1, 0, 0, 0, 0⟩]],
      [⟨6, 8, 0, 0, 0, 0, 0, 0, 0⟩, ⟨6, 8, 1, 0, 1, 0, 0, 0, 0⟩]⟩,
    ⟨-1, 0, 3, 6,
      [[⟨6, 1, 0, 0, 0, 0, 0, 0, 0⟩, ⟨6, 1, 1, 0, 1, 0, 0, 0, 0⟩], [⟨6, 2, 0, 0, 0, 0, 0, 0, 0⟩, ⟨6, 2, 1, 0, 1, 0, 0, 0, 0⟩], [⟨6, 10, 0, 0, 0, 0, 0, 0, 0⟩, ⟨6, 10, 1, 0, 1, 0, 0, 0, 0⟩], [⟨6, 12, 0, 0, 0, 0, 0, 0, 0⟩, ⟨6, 12, 1, 0, 1, 0, 0, 0, 0⟩]],
      [⟨6, 2, 0, 0, 0, 0, 0, 0, 1⟩, ⟨6, 2, 1, 0, 1, 0, 0, 0, 1⟩]⟩,
    ⟨-1, 0, 4, 8,
      [[⟨12, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨12, 0, 1, 0, 1, 0, 0, 0, 0⟩], [⟨6, 5, 0, 0, 0, 0, 0, 0, 0⟩, ⟨6, 5, 1, 0, 1, 0, 0, 0, 0⟩], [⟨6, 11, 0, 0, 0, 0, 0, 0, 0⟩, ⟨6, 11, 1, 0, 1, 0, 0, 0, 0⟩], [⟨6, 14, 0, 0, 0, 0, 0, 0, 0⟩, ⟨6, 14, 1, 0, 1, 0, 0, 0, 0⟩]],
      [⟨6, 11, 0, 0, 0, 0, 0, 0, 2⟩, ⟨6, 11, 1, 0, 1, 0, 0, 0, 2⟩]⟩,
    ⟨-1, 0, 5, 9,
      [[⟨6, 9, 0, 0, 1, 0, 0, 0, 0⟩, ⟨6, 9, 1, 0, 2, 0, 0, 0, 0⟩], [⟨6, 13, 0, 0, 1, 0, 0, 0, 0⟩, ⟨6, 13, 1, 0, 2, 0, 0, 0, 0⟩], [⟨12, 1, 0, 0, 0, 0, 0, 0, 0⟩, ⟨12, 1, 1, 0, 1, 0, 0, 0, 0⟩], [⟨6, 4, 0, 0, 0, 0, 0, 0, 0⟩, ⟨6, 4, 1, 0, 1, 0, 0, 0, 0⟩]],
      [⟨6, 9, 0, 0, 1, 0, 0, 0, 3⟩, ⟨6, 9, 1, 0, 2, 0, 0, 0, 3⟩]⟩,
    ⟨-1, 0, 6, 3,
      [[⟨6, 7, 0, 0, 0, 0, 0, 0, 0⟩, ⟨6, 7, 1, 0, 1, 0, 0, 0, 0⟩], [⟨6, 15, 0, 0, 0, 0, 0, 0, 0⟩, ⟨6, 15, 1, 0, 1, 0, 0, 0, 0⟩], [⟨6, 18, 0, 0, 0, 0, 0, 0, 0⟩, ⟨6, 18, 1, 0, 1, 0, 0, 0, 0⟩], [⟨0, 1, 0, 0, 0, 0, 0, 0, 0⟩, ⟨6, 1, 1, 0, 0, 0, 0, 0, 0⟩], [⟨0, 10, 0, 0, 0, 0, 0, 0, 0⟩, ⟨6, 10, 1, 0, 0, 0, 0, 0, 0⟩]],
      [⟨0, 1, 0, 0, 0, 0, 0, 0, 0⟩, ⟨6, 1, 1, 0, 0, 0, 0, 0, 0⟩]⟩,
    ⟨-1, 0, 7, 4,
      [[⟨6, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨6, 0, 1, 0, 1, 0, 0, 0, 0⟩], [⟨6, 6, 0, 0, 0, 0, 0, 0, 0⟩, ⟨6, 6, 1, 0, 1, 0, 0, 0, 0⟩], [⟨6, 8, 0, 0, 0, 0, 0, 0, 0⟩, ⟨6, 8, 1, 0, 1, 0, 0, 0, 0⟩], [⟨6, 15, 0, 0, 0, 0, 0, 0, 0⟩, ⟨6, 15, 1, 0, 1, 0, 0, 0, 0⟩], [⟨6, 18, 0, 0, 0, 0, 0, 0, 0⟩, ⟨6, 18, 1, 0, 1, 0, 0, 0, 0⟩]],
      [⟨6, 6, 0, 0, 0, 0, 0, 0, 0⟩, ⟨6, 6, 1, 0, 1, 0, 0, 0, 0⟩]⟩,
    ⟨-1, 0, 8, 4,
      [[⟨6, 2, 0, 0, 0, 0, 0, 0, 0⟩, ⟨6, 2, 1, 0, 1, 0, 0, 0, 0⟩], [⟨6, 7, 0, 0, 0, 0, 0, 0, 0⟩, ⟨6, 7, 1, 0, 1, 0, 0, 0, 0⟩], [⟨6, 9, 0, 0, 0, 0, 0, 0, 0⟩, ⟨6, 9, 1, 0, 1, 0, 0, 0, 0⟩], [⟨6, 16, 0, 0, 0, 0, 0, 0, 0⟩, ⟨6, 16, 1, 0, 1, 0, 0, 0, 0⟩], [⟨6, 18, 0, 0, 0, 0, 0, 0, 0⟩, ⟨6, 18, 1, 0, 1, 0, 0, 0, 0⟩]],
      [⟨6, 9, 0, 0, 0, 0, 0, 0, 0⟩, ⟨6, 9, 1, 0, 1, 0, 0, 0, 0⟩]⟩,
    ⟨-1, 0, 9, 3,
      [[⟨6, 8, 0, 0, 0, 0, 0, 0, 0⟩, ⟨6, 8, 1, 0, 1, 0, 0, 0, 0⟩], [⟨6, 16, 0, 0, 0, 0, 0, 0, 0⟩, ⟨6, 16, 1, 0, 1, 0, 0, 0, 0⟩], [⟨6, 18, 0, 0, 0, 0, 0, 0, 0⟩, ⟨6, 18, 1, 0, 1, 0, 0, 0, 0⟩], [⟨0, 5, 0, 0, 0, 0, 0, 0, 0⟩, ⟨6, 5, 1, 0, 0, 0, 0, 0, 0⟩], [⟨0, 11, 0, 0, 0, 0, 0, 0, 0⟩, ⟨6, 11, 1, 0, 0, 0, 0, 0, 0⟩]],
      [⟨0, 11, 0, 0, 0, 0, 0, 0, 0⟩, ⟨6, 11, 1, 0, 0, 0, 0, 0, 0⟩]⟩,
    ⟨-1, 0, 10, 7,
      [[⟨6, 6, 0, 0, 1, 0, 0, 0, 0⟩, ⟨6, 6, 1, 0, 2, 0, 0, 0, 0⟩], [⟨6, 18, 0, 0, 1, 0, 0, 0, 0⟩, ⟨6, 18, 1, 0, 2, 0, 0, 0, 0⟩], [⟨6, 3, 0, 0, 0, 0, 0, 0, 0⟩, ⟨6, 3, 1, 0, 1, 0, 0, 0, 0⟩], [⟨6, 11, 0, 0, 0, 0, 0, 0, 0⟩, ⟨6, 11, 1, 0, 1, 0, 0, 0, 0⟩], [⟨6, 17, 0, 0, 0, 0, 0, 0, 0⟩, ⟨6, 17, 1, 0, 1, 0, 0, 0, 0⟩]],
      [⟨6, 3, 0, 0, 0, 0, 0, 0, 2⟩, ⟨6, 3, 1, 0, 1, 0, 0, 0, 2⟩]⟩,
    ⟨-1, 0, 11, 7,
      [[⟨6, 9, 0, 0, 1, 0, 0, 0, 0⟩, ⟨6, 9, 1, 0, 2, 0, 0, 0, 0⟩], [⟨6, 18, 0, 0, 1, 0, 0, 0, 0⟩, ⟨6, 18, 1, 0, 2, 0, 0, 0, 0⟩], [⟨6, 4, 0, 0, 0, 0, 0, 0, 0⟩, ⟨6, 4, 1, 0, 1, 0, 0, 0, 0⟩], [⟨6, 10, 0, 0, 0, 0, 0, 0, 0⟩, ⟨6, 10, 1, 0, 1, 0, 0, 0, 0⟩], [⟨6, 17, 0, 0, 0, 0, 0, 0, 0⟩, ⟨6, 17, 1, 0, 1, 0, 0, 0, 0⟩]],
      [⟨6, 17, 0, 0, 0, 0, 0, 0, 1⟩, ⟨6, 17, 1, 0, 1, 0, 0, 0, 1⟩]⟩,
    ⟨-1, 0, 12, 5,
      [[⟨6, 2, 0, 0, 0, 0, 0, 0, 0⟩, ⟨6, 2, 1, 0, 1, 0, 0, 0, 0⟩], [⟨6, 3, 0, 0, 0, 0, 0, 0, 0⟩, ⟨6, 3, 1, 0, 1, 0, 0, 0, 0⟩], [⟨6, 16, 0, 0, 0, 0, 0, 0, 0⟩, ⟨6, 16, 1, 0, 1, 0, 0, 0, 0⟩], [⟨6, 17, 0, 0, 0, 0, 0, 0, 0⟩, ⟨6, 17, 1, 0, 1, 0, 0, 0, 0⟩]],
      [⟨6, 16, 0, 0, 0, 0, 0, 0, 2⟩, ⟨6, 16, 1, 0, 1, 0, 0, 0, 2⟩]⟩,
    ⟨-1, 0, 13, 5,
      [[⟨12, 15, 0, 0, 0, 0, 0, 0, 0⟩, ⟨12, 15, 1, 0, 1, 0, 0, 0, 0⟩], [⟨6, 16, 0, 0, 0, 0, 0, 0, 0⟩, ⟨6, 16, 1, 0, 1, 0, 0, 0, 0⟩], [⟨1, 1, 0, 0, 0, 0, 0, 0, 0⟩, ⟨12, 1, 1, 0, 0, 0, 0, 0, 0⟩], [⟨0, 5, 0, 0, 0, 0, 0, 0, 0⟩, ⟨6, 5, 1, 0, 0, 0, 0, 0, 0⟩]],
      [⟨6, 16, 0, 0, 0, 0, 0, 0, 3⟩, ⟨6, 16, 1, 0, 1, 0, 0, 0, 3⟩]⟩,
    ⟨-1, 0, 14, 7,
      [[⟨12, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨12, 0, 1, 0, 1, 0, 0, 0, 0⟩], [⟨12, 15, 0, 0, 0, 0, 0, 0, 0⟩, ⟨12, 15, 1, 0, 1, 0, 0, 0, 0⟩], [⟨6, 4, 0, 0, 0, 0, 0, 0, 0⟩, ⟨6, 4, 1, 0, 1, 0, 0, 0, 0⟩], [⟨6, 17, 0, 0, 0, 0, 0, 0, 0⟩, ⟨6, 17, 1, 0, 1, 0, 0, 0, 0⟩]],
      [⟨12, 15, 0, 0, 0, 0, 0, 0, 3⟩, ⟨12, 15, 1, 0, 1, 0, 0, 0, 3⟩]⟩,
    ⟨-1, 0, 15, 4,
      [[⟨6, 6, 0, 0, 0, 0, 0, 0, 0⟩, ⟨6, 6, 1, 0, 1, 0, 0, 0, 0⟩], [⟨6, 7, 0, 0, 0, 0, 0, 0, 0⟩, ⟨6, 7, 1, 0, 1, 0, 0, 0, 0⟩], [⟨5, 13, 0, 0, 0, 0, 0, 0, 0⟩, ⟨11, 13, 0, 0, 0, 1, 0, 0, 0⟩], [⟨5, 14, 0, 0, 0, 0, 0, 0, 0⟩, ⟨11, 14, 0, 0, 0, 1, 0, 0, 0⟩]],
      [⟨6, 6, 0, 0, 0, 0, 0, 0, 1⟩, ⟨6, 6, 1, 0, 1, 0, 0, 0, 1⟩]⟩,
    ⟨-1, 0, 16, 4,
      [[⟨6, 8, 0, 0, 0, 0, 0, 0, 0⟩, ⟨6, 8, 1, 0, 1, 0, 0, 0, 0⟩], [⟨6, 9, 0, 0, 0, 0, 0, 0, 0⟩, ⟨6, 9, 1, 0, 1, 0, 0, 0, 0⟩], [⟨6, 12, 0, 0, 0, 0, 0, 0, 0⟩, ⟨6, 12, 1, 0, 1, 0, 0, 0, 0⟩], [⟨6, 13, 0, 0, 0, 0, 0, 0, 0⟩, ⟨6, 13, 1, 0, 1, 0, 0, 0, 0⟩]],
      [⟨6, 9, 0, 0, 0, 0, 0, 0, 1⟩, ⟨6, 9, 1, 0, 1, 0, 0, 0, 1⟩]⟩,
    ⟨-1, 0, 17, 6,
      [[⟨6, 10, 0, 0, 0, 0, 0, 0, 0⟩, ⟨6, 10, 1, 0, 1, 0, 0, 0, 0⟩], [⟨6, 11, 0, 0, 0, 0, 0, 0, 0⟩, ⟨6, 11, 1, 0, 1, 0, 0, 0, 0⟩], [⟨6, 12, 0, 0, 0, 0, 0, 0, 0⟩, ⟨6, 12, 1, 0, 1, 0, 0, 0, 0⟩], [⟨6, 14, 0, 0, 0, 0, 0, 0, 0⟩, ⟨6, 14, 1, 0, 1, 0, 0, 0, 0⟩]],
      [⟨6, 12, 0, 0, 0, 0, 0, 0, 3⟩, ⟨6, 12, 1, 0, 1, 0, 0, 0, 3⟩]⟩,
    ⟨-1, 0, 18, 3,
      [[⟨6, 6, 0, 0, 0, 0, 0, 0, 0⟩, ⟨6, 6, 1, 0, 1, 0, 0, 0, 0⟩], [⟨6, 7, 0, 0, 0, 0, 0, 0, 0⟩, ⟨6, 7, 1, 0, 1, 0, 0, 0, 0⟩], [⟨6, 8, 0, 0, 0, 0, 0, 0, 0⟩, ⟨6, 8, 1, 0, 1, 0, 0, 0, 0⟩], [⟨6, 9, 0, 0, 0, 0, 0, 0, 0⟩, ⟨6, 9, 1, 0, 1, 0, 0, 0, 0⟩], [⟨0, 10, 0, 0, 0, 0, 0, 0, 0⟩, ⟨6, 10, 1, 0, 0, 0, 0, 0, 0⟩], [⟨0, 11, 0, 0, 0, 0, 0, 0, 0⟩, ⟨6, 11, 1, 0, 0, 0, 0, 0, 0⟩]],
      [⟨0, 10, 0, 0, 0, 0, 0, 0, 1⟩, ⟨6, 10, 1, 0, 0, 0, 0, 0, 1⟩]⟩]⟩,
  ⟨2, 0, -1, 1, -1, [(-1, -1, 1), (1, 0, 1)], -1, -1, 1, 1, 1, 0, 1, 1,
   [⟨1, -2, 0, 8,
      [[⟨7, 2, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 2, 1, 0, 1, 0, 0, 0, 0⟩, ⟨7, 2, 0, 0, 0, 0, 1, 1, 0⟩, ⟨7, 2, 1, 0, 1, 0, 1, 1, 0⟩], [⟨7, 7, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 7, 1, 0, 1, 0, 0, 0, 0⟩, ⟨7, 7, 0, 0, 0, 0, 1, 1, 0⟩, ⟨7, 7, 1, 0, 1, 0, 1, 1, 0⟩], [⟨2, 4, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 4, 1, 0, 0, 0, 0, 0, 0⟩, ⟨2, 4, 0, 1, 1, 0, 0, 0, 0⟩, ⟨7, 4, 1, 0, 0, 0, 1, 1, 0⟩], [⟨2, 14, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 14, 1, 0, 0, 0, 0, 0, 0⟩, ⟨2, 14, 0, 1, 1, 0, 0, 0, 0⟩, ⟨7, 14, 1, 0, 0, 0, 1, 1, 0⟩]],
      [⟨2, 4, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 4, 1, 0, 0, 0, 0, 0, 0⟩, ⟨2, 4, 0, 1, 1, 0, 0, 0, 0⟩, ⟨7, 4, 1, 0, 0, 0, 1, 1, 0⟩]⟩,
    ⟨1, -2, 1, 8,
      [[⟨1, 6, 0, 0, 1, 0, 0, 0, 0⟩, ⟨1, 6, 1, 0, 2, 0, 0, 0, 0⟩, ⟨7, 6, 0, 0, 1, 0, 1, 0, 0⟩, ⟨7, 6, 1, 0, 2, 0, 1, 0, 0⟩], [⟨1, 13, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 13, 1, 0, 1, 0, 0, 0, 0⟩, ⟨7, 13, 0, 0, 0, 0, 1, 0, 0⟩, ⟨7, 13, 1, 0, 1, 0, 1, 0, 0⟩], [⟨7, 3, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 3, 1, 0, 1, 0, 0, 0, 0⟩, ⟨7, 3, 0, 0, 0, 0, 1, 1, 0⟩, ⟨7, 3, 1, 0, 1, 0, 1, 1, 0⟩], [⟨2, 5, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 5, 1, 0, 0, 0, 0, 0, 0⟩, ⟨2, 5, 0, 1, 1, 0, 0, 0, 0⟩, ⟨7, 5, 1, 0, 0, 0, 1, 1, 0⟩]],
      [⟨1, 13, 0, 0, 0, 0, 0, 0, 2⟩, ⟨1, 13, 1, 0, 1, 0, 0, 0, 2⟩, ⟨7, 13, 0, 0, 0, 0, 1, 0, 2⟩, ⟨7, 13, 1, 0, 1, 0, 1, 0, 2⟩]⟩,
    ⟨1, -2, 2, 9,
      [[⟨7, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 0, 1, 0, 1, 0, 0, 0, 0⟩, ⟨7, 0, 0, 0, 0, 0, 1, 1, 0⟩, ⟨7, 0, 1, 0, 1, 0, 1, 1, 0⟩], [⟨7, 3, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 3, 1, 0, 1, 0, 0, 0, 0⟩, ⟨7, 3, 0, 0, 0, 0, 1, 1, 0⟩, ⟨7, 3, 1, 0, 1, 0, 1, 1, 0⟩], [⟨7, 8, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 8, 1, 0, 1, 0, 0, 0, 0⟩, ⟨7, 8, 0, 0, 0, 0, 1, 1, 0⟩, ⟨7, 8, 1, 0, 1, 0, 1, 1, 0⟩], [⟨7, 12, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 12, 1, 0, 1, 0, 0, 0, 0⟩, ⟨7, 12, 0, 0, 0, 0, 1, 1, 0⟩, ⟨7, 12, 1, 0, 1, 0, 1, 1, 0⟩]],
      [⟨7, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 0, 1, 0, 1, 0, 0, 0, 0⟩, ⟨7, 0, 0, 0, 0, 0, 1, 1, 0⟩, ⟨7, 0, 1, 0, 1, 0, 1, 1, 0⟩]⟩,
    ⟨1, -2, 3, 9,
      [[⟨7, 1, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 1, 1, 0, 1, 0, 0, 0, 0⟩, ⟨7, 1, 0, 0, 0, 0, 1, 1, 0⟩, ⟨7, 1, 1, 0, 1, 0, 1, 1, 0⟩], [⟨7, 2, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 2, 1, 0, 1, 0, 0, 0, 0⟩, ⟨7, 2, 0, 0, 0, 0, 1, 1, 0⟩, ⟨7, 2, 1, 0, 1, 0, 1, 1, 0⟩], [⟨7, 10, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 10, 1, 0, 1, 0, 0, 0, 0⟩, ⟨7, 10, 0, 0, 0, 0, 1, 1, 0⟩, ⟨7, 10, 1, 0, 1, 0, 1, 1, 0⟩], [⟨7, 12, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 12, 1, 0, 1, 0, 0, 0, 0⟩, ⟨7, 12, 0, 0, 0, 0, 1, 1, 0⟩, ⟨7, 12, 1, 0, 1, 0, 1, 1, 0⟩]],
      [⟨7, 1, 0, 0, 0, 0, 0, 0, 2⟩, ⟨7, 1, 1, 0, 1, 0, 0, 0, 2⟩, ⟨7, 1, 0, 0, 0, 0, 1, 1, 2⟩, ⟨7, 1, 1, 0, 1, 0, 1, 1, 2⟩]⟩,
    ⟨1, -2, 4, 12,
      [[⟨7, 0, 0, 0, 1, 0, 0, 0, 0⟩, ⟨7, 0, 1, 0, 2, 0, 0, 0, 0⟩, ⟨7, 0, 0, 0, 1, 0, 1, 1, 0⟩, ⟨7, 0, 1, 0, 2, 0, 1, 1, 0⟩], [⟨7, 5, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 5, 1, 0, 1, 0, 0, 0, 0⟩, ⟨7, 5, 0, 0, 0, 0, 1, 1, 0⟩, ⟨7, 5, 1, 0, 1, 0, 1, 1, 0⟩], [⟨7, 11, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 11, 1, 0, 1, 0, 0, 0, 0⟩, ⟨7, 11, 0, 0, 0, 0, 1, 1, 0⟩, ⟨7, 11, 1, 0, 1, 0, 1, 1, 0⟩], [⟨7, 14, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 14, 1, 0, 1, 0, 0, 0, 0⟩, ⟨7, 14, 0, 0, 0, 0, 1, 1, 0⟩, ⟨7, 14, 1, 0, 1, 0, 1, 1, 0⟩]],
      [⟨7, 11, 0, 0, 0, 0, 0, 0, 2⟩, ⟨7, 11, 1, 0, 1, 0, 0, 0, 2⟩, ⟨7, 11, 0, 0, 0, 0, 1, 1, 2⟩, ⟨7, 11, 1, 0, 1, 0, 1, 1, 2⟩]⟩,
    ⟨1, -2, 5, 12,
      [[⟨1, 9, 0, 0, 1, 0, 0, 0, 0⟩, ⟨1, 9, 1, 0, 2, 0, 0, 0, 0⟩, ⟨7, 9, 0, 0, 1, 0, 1, 0, 0⟩, ⟨7, 9, 1, 0, 2, 0, 1, 0, 0⟩], [⟨1, 13, 0, 0, 1, 0, 0, 0, 0⟩, ⟨1, 13, 1, 0, 2, 0, 0, 0, 0⟩, ⟨7, 13, 0, 0, 1, 0, 1, 0, 0⟩, ⟨7, 13, 1, 0, 2, 0, 1, 0, 0⟩], [⟨7, 1, 0, 0, 1, 0, 0, 0, 0⟩, ⟨7, 1, 1, 0, 2, 0, 0, 0, 0⟩, ⟨7, 1, 0, 0, 1, 0, 1, 1, 0⟩, ⟨7, 1, 1, 0, 2, 0, 1, 1, 0⟩], [⟨7, 4, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 4, 1, 0, 1, 0, 0, 0, 0⟩, ⟨7, 4, 0, 0, 0, 0, 1, 1, 0⟩, ⟨7, 4, 1, 0, 1, 0, 1, 1, 0⟩]],
      [⟨1, 9, 0, 0, 1, 0, 0, 0, 3⟩, ⟨1, 9, 1, 0, 2, 0, 0, 0, 3⟩, ⟨7, 9, 0, 0, 1, 0, 1, 0, 3⟩, ⟨7, 9, 1, 0, 2, 0, 1, 0, 3⟩]⟩,
    ⟨1, -2, 6, 9,
      [[⟨7, 7, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 7, 1, 0, 1, 0, 0, 0, 0⟩, ⟨7, 7, 0, 0, 0, 0, 1, 1, 0⟩, ⟨7, 7, 1, 0, 1, 0, 1, 1, 0⟩], [⟨7, 15, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 15, 1, 0, 1, 0, 0, 0, 0⟩, ⟨7, 15, 0, 0, 0, 0, 1, 1, 0⟩, ⟨7, 15, 1, 0, 1, 0, 1, 1, 0⟩], [⟨7, 18, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 18, 1, 0, 1, 0, 0, 0, 0⟩, ⟨7, 18, 0, 0, 0, 0, 1, 1, 0⟩, ⟨7, 18, 1, 0, 1, 0, 1, 1, 0⟩], [⟨2, 1, 0, 0, 1, 0, 0, 0, 0⟩, ⟨7, 1, 1, 0, 0, 0, 0, 1, 0⟩, ⟨2, 1, 0, 1, 2, 0, 0, 0, 0⟩, ⟨7, 1, 1, 0, 0, 0, 1, 2, 0⟩], [⟨2, 10, 0, 0, 1, 0, 0, 0, 0⟩, ⟨7, 10, 1, 0, 0, 0, 0, 1, 0⟩, ⟨2, 10, 0, 1, 2, 0, 0, 0, 0⟩, ⟨7, 10, 1, 0, 0, 0, 1, 2, 0⟩]],
      [⟨7, 15, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 15, 1, 0, 1, 0, 0, 0, 0⟩, ⟨7, 15, 0, 0, 0, 0, 1, 1, 0⟩, ⟨7, 15, 1, 0, 1, 0, 1, 1, 0⟩]⟩,
    ⟨1, -2, 7, 9,
      [[⟨7, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 0, 1, 0, 1, 0, 0, 0, 0⟩, ⟨7, 0, 0, 0, 0, 0, 1, 1, 0⟩, ⟨7, 0, 1, 0, 1, 0, 1, 1, 0⟩], [⟨7, 6, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 6, 1, 0, 1, 0, 0, 0, 0⟩, ⟨7, 6, 0, 0, 0, 0, 1, 1, 0⟩, ⟨7, 6, 1, 0, 1, 0, 1, 1, 0⟩], [⟨7, 8, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 8, 1, 0, 1, 0, 0, 0, 0⟩, ⟨7, 8, 0, 0, 0, 0, 1, 1, 0⟩, ⟨7, 8, 1, 0, 1, 0, 1, 1, 0⟩], [⟨7, 15, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 15, 1, 0, 1, 0, 0, 0, 0⟩, ⟨7, 15, 0, 0, 0, 0, 1, 1, 0⟩, ⟨7, 15, 1, 0, 1, 0, 1, 1, 0⟩], [⟨7, 18, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 18, 1, 0, 1, 0, 0, 0, 0⟩, ⟨7, 18, 0, 0, 0, 0, 1, 1, 0⟩, ⟨7, 18, 1, 0, 1, 0, 1, 1, 0⟩]],
      [⟨7, 0, 0, 0, 0, 0, 0, 0, 1⟩, ⟨7, 0, 1, 0, 1, 0, 0, 0, 1⟩, ⟨7, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨7, 0, 1, 0, 1, 0, 1, 1, 1⟩]⟩,
    ⟨1, -2, 8, 10,
      [[⟨7, 2, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 2, 1, 0, 1, 0, 0, 0, 0⟩, ⟨7, 2, 0, 0, 0, 0, 1, 1, 0⟩, ⟨7, 2, 1, 0, 1, 0, 1, 1, 0⟩], [⟨7, 7, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 7, 1, 0, 1, 0, 0, 0, 0⟩, ⟨7, 7, 0, 0, 0, 0, 1, 1, 0⟩, ⟨7, 7, 1, 0, 1, 0, 1, 1, 0⟩], [⟨7, 9, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 9, 1, 0, 1, 0, 0, 0, 0⟩, ⟨7, 9, 0, 0, 0, 0, 1, 1, 0⟩, ⟨7, 9, 1, 0, 1, 0, 1, 1, 0⟩], [⟨7, 16, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 16, 1, 0, 1, 0, 0, 0, 0⟩, ⟨7, 16, 0, 0, 0, 0, 1, 1, 0⟩, ⟨7, 16, 1, 0, 1, 0, 1, 1, 0⟩], [⟨7, 18, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 18, 1, 0, 1, 0, 0, 0, 0⟩, ⟨7, 18, 0, 0, 0, 0, 1, 1, 0⟩, ⟨7, 18, 1, 0, 1, 0, 1, 1, 0⟩]],
      [⟨7, 2, 0, 0, 0, 0, 0, 0, 2⟩, ⟨7, 2, 1, 0, 1, 0, 0, 0, 2⟩, ⟨7, 2, 0, 0, 0, 0, 1, 1, 2⟩, ⟨7, 2, 1, 0, 1, 0, 1, 1, 2⟩]⟩,
    ⟨1, -2, 9, 11,
      [[⟨7, 8, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 8, 1, 0, 1, 0, 0, 0, 0⟩, ⟨7, 8, 0, 0, 0, 0, 1, 1, 0⟩, ⟨7, 8, 1, 0, 1, 0, 1, 1, 0⟩], [⟨7, 16, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 16, 1, 0, 1, 0, 0, 0, 0⟩, ⟨7, 16, 0, 0, 0, 0, 1, 1, 0⟩, ⟨7, 16, 1, 0, 1, 0, 1, 1, 0⟩], [⟨7, 18, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 18, 1, 0, 1, 0, 0, 0, 0⟩, ⟨7, 18, 0, 0, 0, 0, 1, 1, 0⟩, ⟨7, 18, 1, 0, 1, 0, 1, 1, 0⟩], [⟨2, 5, 0, 0, 1, 0, 0, 0, 0⟩, ⟨7, 5, 1, 0, 0, 0, 0, 1, 0⟩, ⟨2, 5, 0, 1, 2, 0, 0, 0, 0⟩, ⟨7, 5, 1, 0, 0, 0, 1, 2, 0⟩], [⟨2, 11, 0, 0, 1, 0, 0, 0, 0⟩, ⟨7, 11, 1, 0, 0, 0, 0, 1, 0⟩, ⟨2, 11, 0, 1, 2, 0, 0, 0, 0⟩, ⟨7, 11, 1, 0, 0, 0, 1, 2, 0⟩]],
      [⟨7, 8, 0, 0, 0, 0, 0, 0, 2⟩, ⟨7, 8, 1, 0, 1, 0, 0, 0, 2⟩, ⟨7, 8, 0, 0, 0, 0, 1, 1, 2⟩, ⟨7, 8, 1, 0, 1, 0, 1, 1, 2⟩]⟩,
    ⟨1, -2, 10, 10,
      [[⟨1, 6, 0, 0, 1, 0, 0, 0, 0⟩, ⟨1, 6, 1, 0, 2, 0, 0, 0, 0⟩, ⟨7, 6, 0, 0, 1, 0, 1, 0, 0⟩, ⟨7, 6, 1, 0, 2, 0, 1, 0, 0⟩], [⟨1, 18, 0, 0, 1, 0, 0, 0, 0⟩, ⟨1, 18, 1, 0, 2, 0, 0, 0, 0⟩, ⟨7, 18, 0, 0, 1, 0, 1, 0, 0⟩, ⟨7, 18, 1, 0, 2, 0, 1, 0, 0⟩], [⟨7, 3, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 3, 1, 0, 1, 0, 0, 0, 0⟩, ⟨7, 3, 0, 0, 0, 0, 1, 1, 0⟩, ⟨7, 3, 1, 0, 1, 0, 1, 1, 0⟩], [⟨7, 11, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 11, 1, 0, 1, 0, 0, 0, 0⟩, ⟨7, 11, 0, 0, 0, 0, 1, 1, 0⟩, ⟨7, 11, 1, 0, 1, 0, 1, 1, 0⟩], [⟨7, 17, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 17, 1, 0, 1, 0, 0, 0, 0⟩, ⟨7, 17, 0, 0, 0, 0, 1, 1, 0⟩, ⟨7, 17, 1, 0, 1, 0, 1, 1, 0⟩]],
      [⟨1, 6, 0, 0, 1, 0, 0, 0, 4⟩, ⟨1, 6, 1, 0, 2, 0, 0, 0, 4⟩, ⟨7, 6, 0, 0, 1, 0, 1, 0, 4⟩, ⟨7, 6, 1, 0, 2, 0, 1, 0, 4⟩]⟩,
    ⟨1, -2, 11, 11,
      [[⟨1, 9, 0, 0, 1, 0, 0, 0, 0⟩, ⟨1, 9, 1, 0, 2, 0, 0, 0, 0⟩, ⟨7, 9, 0, 0, 1, 0, 1, 0, 0⟩, ⟨7, 9, 1, 0, 2, 0, 1, 0, 0⟩], [⟨1, 18, 0, 0, 1, 0, 0, 0, 0⟩, ⟨1, 18, 1, 0, 2, 0, 0, 0, 0⟩, ⟨7, 18, 0, 0, 1, 0, 1, 0, 0⟩, ⟨7, 18, 1, 0, 2, 0, 1, 0, 0⟩], [⟨7, 4, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 4, 1, 0, 1, 0, 0, 0, 0⟩, ⟨7, 4, 0, 0, 0, 0, 1, 1, 0⟩, ⟨7, 4, 1, 0, 1, 0, 1, 1, 0⟩], [⟨7, 10, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 10, 1, 0, 1, 0, 0, 0, 0⟩, ⟨7, 10, 0, 0, 0, 0, 1, 1, 0⟩, ⟨7, 10, 1, 0, 1, 0, 1, 1, 0⟩], [⟨7, 17, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 17, 1, 0, 1, 0, 0, 0, 0⟩, ⟨7, 17, 0, 0, 0, 0, 1, 1, 0⟩, ⟨7, 17, 1, 0, 1, 0, 1, 1, 0⟩]],
      [⟨1, 18, 0, 0, 1, 0, 0, 0, 5⟩, ⟨1, 18, 1, 0, 2, 0, 0, 0, 5⟩, ⟨7, 18, 0, 0, 1, 0, 1, 0, 5⟩, ⟨7, 18, 1, 0, 2, 0, 1, 0, 5⟩]⟩,
    ⟨1, -2, 12, 10,
      [[⟨7, 2, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 2, 1, 0, 1, 0, 0, 0, 0⟩, ⟨7, 2, 0, 0, 0, 0, 1, 1, 0⟩, ⟨7, 2, 1, 0, 1, 0, 1, 1, 0⟩], [⟨7, 3, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 3, 1, 0, 1, 0, 0, 0, 0⟩, ⟨7, 3, 0, 0, 0, 0, 1, 1, 0⟩, ⟨7, 3, 1, 0, 1, 0, 1, 1, 0⟩], [⟨7, 16, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 16, 1, 0, 1, 0, 0, 0, 0⟩, ⟨7, 16, 0, 0, 0, 0, 1, 1, 0⟩, ⟨7, 16, 1, 0, 1, 0, 1, 1, 0⟩], [⟨7, 17, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 17, 1, 0, 1, 0, 0, 0, 0⟩, ⟨7, 17, 0, 0, 0, 0, 1, 1, 0⟩, ⟨7, 17, 1, 0, 1, 0, 1, 1, 0⟩]],
      [⟨7, 2, 0, 0, 0, 0, 0, 0, 3⟩, ⟨7, 2, 1, 0, 1, 0, 0, 0, 3⟩, ⟨7, 2, 0, 0, 0, 0, 1, 1, 3⟩, ⟨7, 2, 1, 0, 1, 0, 1, 1, 3⟩]⟩,
    ⟨1, -2, 13, 12,
      [[⟨7, 15, 0, 0, 1, 0, 0, 0, 0⟩, ⟨7, 15, 1, 0, 2, 0, 0, 0, 0⟩, ⟨7, 15, 0, 0, 1, 0, 1, 1, 0⟩, ⟨7, 15, 1, 0, 2, 0, 1, 1, 0⟩], [⟨7, 16, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 16, 1, 0, 1, 0, 0, 0, 0⟩, ⟨7, 16, 0, 0, 0, 0, 1, 1, 0⟩, ⟨7, 16, 1, 0, 1, 0, 1, 1, 0⟩], [⟨7, 1, 0, 0, 0, 0, 0, 1, 0⟩, ⟨7, 1, 1, 0, 1, 0, 0, 1, 0⟩, ⟨7, 1, 0, 0, 0, 0, 1, 2, 0⟩, ⟨7, 1, 1, 0, 1, 0, 1, 2, 0⟩], [⟨2, 5, 0, 0, 1, 0, 0, 0, 0⟩, ⟨7, 5, 1, 0, 0, 0, 0, 1, 0⟩, ⟨2, 5, 0, 1, 2, 0, 0, 0, 0⟩, ⟨7, 5, 1, 0, 0, 0, 1, 2, 0⟩]],
      [⟨7, 16, 0, 0, 0, 0, 0, 0, 3⟩, ⟨7, 16, 1, 0, 1, 0, 0, 0, 3⟩, ⟨7, 16, 0, 0, 0, 0, 1, 1, 3⟩, ⟨7, 16, 1, 0, 1, 0, 1, 1, 3⟩]⟩,
    ⟨1, -2, 14, 12,
      [[⟨7, 0, 0, 0, 1, 0, 0, 0, 0⟩, ⟨7, 0, 1, 0, 2, 0, 0, 0, 0⟩, ⟨7, 0, 0, 0, 1, 0, 1, 1, 0⟩, ⟨7, 0, 1, 0, 2, 0, 1, 1, 0⟩], [⟨7, 15, 0, 0, 1, 0, 0, 0, 0⟩, ⟨7, 15, 1, 0, 2, 0, 0, 0, 0⟩, ⟨7, 15, 0, 0, 1, 0, 1, 1, 0⟩, ⟨7, 15, 1, 0, 2, 0, 1, 1, 0⟩], [⟨7, 4, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 4, 1, 0, 1, 0, 0, 0, 0⟩, ⟨7, 4, 0, 0, 0, 0, 1, 1, 0⟩, ⟨7, 4, 1, 0, 1, 0, 1, 1, 0⟩], [⟨7, 17, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 17, 1, 0, 1, 0, 0, 0, 0⟩, ⟨7, 17, 0, 0, 0, 0, 1, 1, 0⟩, ⟨7, 17, 1, 0, 1, 0, 1, 1, 0⟩]],
      [⟨7, 17, 0, 0, 0, 0, 0, 0, 3⟩, ⟨7, 17, 1, 0, 1, 0, 0, 0, 3⟩, ⟨7, 17, 0, 0, 0, 0, 1, 1, 3⟩, ⟨7, 17, 1, 0, 1, 0, 1, 1, 3⟩]⟩,
    ⟨1, -2, 15, 8,
      [[⟨7, 6, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 6, 1, 0, 1, 0, 0, 0, 0⟩, ⟨7, 6, 0, 0, 0, 0, 1, 1, 0⟩, ⟨7, 6, 1, 0, 1, 0, 1, 1, 0⟩], [⟨7, 7, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 7, 1, 0, 1, 0, 0, 0, 0⟩, ⟨7, 7, 0, 0, 0, 0, 1, 1, 0⟩, ⟨7, 7, 1, 0, 1, 0, 1, 1, 0⟩], [⟨2, 13, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 13, 1, 0, 0, 0, 0, 0, 0⟩, ⟨2, 13, 0, 1, 1, 0, 0, 0, 0⟩, ⟨7, 13, 1, 0, 0, 0, 1, 1, 0⟩], [⟨2, 14, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 14, 1, 0, 0, 0, 0, 0, 0⟩, ⟨2, 14, 0, 1, 1, 0, 0, 0, 0⟩, ⟨7, 14, 1, 0, 0, 0, 1, 1, 0⟩]],
      [⟨2, 13, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 13, 1, 0, 0, 0, 0, 0, 0⟩, ⟨2, 13, 0, 1, 1, 0, 0, 0, 0⟩, ⟨7, 13, 1, 0, 0, 0, 1, 1, 0⟩]⟩,
    ⟨1, -2, 16, 11,
      [[⟨7, 8, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 8, 1, 0, 1, 0, 0, 0, 0⟩, ⟨7, 8, 0, 0, 0, 0, 1, 1, 0⟩, ⟨7, 8, 1, 0, 1, 0, 1, 1, 0⟩], [⟨7, 9, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 9, 1, 0, 1, 0, 0, 0, 0⟩, ⟨7, 9, 0, 0, 0, 0, 1, 1, 0⟩, ⟨7, 9, 1, 0, 1, 0, 1, 1, 0⟩], [⟨7, 12, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 12, 1, 0, 1, 0, 0, 0, 0⟩, ⟨7, 12, 0, 0, 0, 0, 1, 1, 0⟩, ⟨7, 12, 1, 0, 1, 0, 1, 1, 0⟩], [⟨7, 13, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 13, 1, 0, 1, 0, 0, 0, 0⟩, ⟨7, 13, 0, 0, 0, 0, 1, 1, 0⟩, ⟨7, 13, 1, 0, 1, 0, 1, 1, 0⟩]],
      [⟨7, 8, 0, 0, 0, 0, 0, 0, 3⟩, ⟨7, 8, 1, 0, 1, 0, 0, 0, 3⟩, ⟨7, 8, 0, 0, 0, 0, 1, 1, 3⟩, ⟨7, 8, 1, 0, 1, 0, 1, 1, 3⟩]⟩,
    ⟨1, -2, 17, 11,
      [[⟨7, 10, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 10, 1, 0, 1, 0, 0, 0, 0⟩, ⟨7, 10, 0, 0, 0, 0, 1, 1, 0⟩, ⟨7, 10, 1, 0, 1, 0, 1, 1, 0⟩], [⟨7, 11, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 11, 1, 0, 1, 0, 0, 0, 0⟩, ⟨7, 11, 0, 0, 0, 0, 1, 1, 0⟩, ⟨7, 11, 1, 0, 1, 0, 1, 1, 0⟩], [⟨7, 12, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 12, 1, 0, 1, 0, 0, 0, 0⟩, ⟨7, 12, 0, 0, 0, 0, 1, 1, 0⟩, ⟨7, 12, 1, 0, 1, 0, 1, 1, 0⟩], [⟨7, 14, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 14, 1, 0, 1, 0, 0, 0, 0⟩, ⟨7, 14, 0, 0, 0, 0, 1, 1, 0⟩, ⟨7, 14, 1, 0, 1, 0, 1, 1, 0⟩]],
      [⟨7, 10, 0, 0, 0, 0, 0, 0, 4⟩, ⟨7, 10, 1, 0, 1, 0, 0, 0, 4⟩, ⟨7, 10, 0, 0, 0, 0, 1, 1, 4⟩, ⟨7, 10, 1, 0, 1, 0, 1, 1, 4⟩]⟩,
    ⟨1, -2, 18, 10,
      [[⟨7, 6, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 6, 1, 0, 1, 0, 0, 0, 0⟩, ⟨7, 6, 0, 0, 0, 0, 1, 1, 0⟩, ⟨7, 6, 1, 0, 1, 0, 1, 1, 0⟩], [⟨7, 7, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 7, 1, 0, 1, 0, 0, 0, 0⟩, ⟨7, 7, 0, 0, 0, 0, 1, 1, 0⟩, ⟨7, 7, 1, 0, 1, 0, 1, 1, 0⟩], [⟨7, 8, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 8, 1, 0, 1, 0, 0, 0, 0⟩, ⟨7, 8, 0, 0, 0, 0, 1, 1, 0⟩, ⟨7, 8, 1, 0, 1, 0, 1, 1, 0⟩], [⟨7, 9, 0, 0, 0, 0, 0, 0, 0⟩, ⟨7, 9, 1, 0, 1, 0, 0, 0, 0⟩, ⟨7, 9, 0, 0, 0, 0, 1, 1, 0⟩, ⟨7, 9, 1, 0, 1, 0, 1, 1, 0⟩], [⟨2, 10, 0, 0, 1, 0, 0, 0, 0⟩, ⟨7, 10, 1, 0, 0, 0, 0, 1, 0⟩, ⟨2, 10, 0, 1, 2, 0, 0, 0, 0⟩, ⟨7, 10, 1, 0, 0, 0, 1, 2, 0⟩], [⟨2, 11, 0, 0, 1, 0, 0, 0, 0⟩, ⟨7, 11, 1, 0, 0, 0, 0, 1, 0⟩, ⟨2, 11, 0, 1, 2, 0, 0, 0, 0⟩, ⟨7, 11, 1, 0, 0, 0, 1, 2, 0⟩]],
      [⟨7, 6, 0, 0, 0, 0, 0, 0, 2⟩, ⟨7, 6, 1, 0, 1, 0, 0, 0, 2⟩, ⟨7, 6, 0, 0, 0, 0, 1, 1, 2⟩, ⟨7, 6, 1, 0, 1, 0, 1, 1, 2⟩]⟩]⟩,
  ⟨2, 1, -1, 1, 0, [(0, -1, 1), (1, 1, 1)], 0, -1, 1, 1, 1, 1, 1, 1,
   [⟨2, -1, 0, 10,
      [[⟨8, 2, 0, 0, 0, 0, 0, 0, 0⟩, ⟨8, 2, 1, 0, 1, 0, 0, 0, 0⟩, ⟨8, 2, 0, 0, 0, 0, 1, 1, 0⟩, ⟨8, 2, 1, 0, 1, 0, 1, 1, 0⟩], [⟨8, 7, 0, 0, 0, 0, 0, 0, 0⟩, ⟨8, 7, 1, 0, 1, 0, 0, 0, 0⟩, ⟨8, 7, 0, 0, 0, 0, 1, 1, 0⟩, ⟨8, 7, 1, 0, 1, 0, 1, 1, 0⟩], [⟨3, 4, 0, 0, 1, 0, 0, 0, 0⟩, ⟨8, 4, 1, 0, 0, 0, 0, 1, 0⟩, ⟨3, 4, 0, 1, 2, 0, 0, 0, 0⟩, ⟨8, 4, 1, 0, 0, 0, 1, 2, 0⟩], [⟨3, 14, 0, 0, 1, 0, 0, 0, 0⟩, ⟨8, 14, 1, 0, 0, 0, 0, 1, 0⟩, ⟨3, 14, 0, 1, 2, 0, 0, 0, 0⟩, ⟨8, 14, 1, 0, 0, 0, 1, 2, 0⟩]],
      [⟨3, 4, 0, 0, 1, 0, 0, 0, 0⟩, ⟨8, 4, 1, 0, 0, 0, 0, 1, 0⟩, ⟨3, 4, 0, 1, 2, 0, 0, 0, 0⟩, ⟨8, 4, 1, 0, 0, 0, 1, 2, 0⟩]⟩,
    ⟨2, -1, 1, 8,
      [[⟨2, 6, 0, 0, 0, 0, 0, 0, 0⟩, ⟨2, 6, 1, 0, 1, 0, 0, 0, 0⟩, ⟨8, 6, 0, 0, 0, 0, 1, 0, 0⟩, ⟨8, 6, 1, 0, 1, 0, 1, 0, 0⟩], [⟨3, 13, 0, 0, 0, 0, 0, 0, 0⟩, ⟨8, 13, 1, 0, 0, 0, 0, 0, 0⟩, ⟨3, 13, 0, 1, 1, 0, 0, 0, 0⟩, ⟨8, 13, 1, 0, 0, 0, 1, 1, 0⟩], [⟨8, 3, 0, 0, 0, 0, 0, 0, 0⟩, ⟨8, 3, 1, 0, 1, 0, 0, 0, 0⟩, ⟨8, 3, 0, 0, 0, 0, 1, 1, 0⟩, ⟨8, 3, 1, 0, 1, 0, 1, 1, 0⟩], [⟨3, 5, 0, 0, 1, 0, 0, 0, 0⟩, ⟨8, 5, 1, 0, 0, 0, 0, 1, 0⟩, ⟨3, 5, 0, 1, 2, 0, 0, 0, 0⟩, ⟨8, 5, 1, 0, 0, 0, 1, 2, 0⟩]],
      [⟨2, 6, 0, 0, 0, 0, 0, 0, 3⟩, ⟨2, 6, 1, 0, 1, 0, 0, 0, 3⟩, ⟨8, 6, 0, 0, 0, 0, 1, 0, 3⟩, ⟨8, 6, 1, 0, 1, 0, 1, 0, 3⟩]⟩,
    ⟨2, -1, 2, 10,
      [[⟨8, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨8, 0, 1, 0, 1, 0, 0, 0, 0⟩, ⟨8, 0, 0, 0, 0, 0, 1, 1, 0⟩, ⟨8, 0, 1, 0, 1, 0, 1, 1, 0⟩], [⟨8, 3, 0, 0, 0, 0, 0, 0, 0⟩, ⟨8, 3, 1, 0, 1, 0, 0, 0, 0⟩, ⟨8, 3, 0, 0, 0, 0, 1, 1, 0⟩, ⟨8, 3, 1, 0, 1, 0, 1, 1, 0⟩], [⟨8, 8, 0, 0, 0, 0, 0, 0, 0⟩, ⟨8, 8, 1, 0, 1, 0, 0, 0, 0⟩, ⟨8, 8, 0, 0, 0, 0, 1, 1, 0⟩, ⟨8, 8, 1, 0, 1, 0, 1, 1, 0⟩], [⟨8, 12, 0, 0, 0, 0, 0, 0, 0⟩, ⟨8, 12, 1, 0, 1, 0, 0, 0, 0⟩, ⟨8, 12, 0, 0, 0, 0, 1, 1, 0⟩, ⟨8, 12, 1, 0, 1, 0, 1, 1, 0⟩]],
      [⟨8, 3, 0, 0, 0, 0, 0, 0, 1⟩, ⟨8, 3, 1, 0, 1, 0, 0, 0, 1⟩, ⟨8, 3, 0, 0, 0, 0, 1, 1, 1⟩, ⟨8, 3, 1, 0, 1, 0, 1, 1, 1⟩]⟩,
    ⟨2, -1, 3, 9,
      [[⟨8, 1, 0, 0, 0, 0, 0, 0, 0⟩, ⟨8, 1, 1, 0, 1, 0, 0, 0, 0⟩, ⟨8, 1, 0, 0, 0, 0, 1, 1, 0⟩, ⟨8, 1, 1, 0, 1, 0, 1, 1, 0⟩], [⟨8, 2, 0, 0, 0, 0, 0, 0, 0⟩, ⟨8, 2, 1, 0, 1, 0, 0, 0, 0⟩, ⟨8, 2, 0, 0, 0, 0, 1, 1, 0⟩, ⟨8, 2, 1, 0, 1, 0, 1, 1, 0⟩], [⟨8, 10, 0, 0, 0, 0, 0, 0, 0⟩, ⟨8, 10, 1, 0, 1, 0, 0, 0, 0⟩, ⟨8, 10, 0, 0, 0, 0, 1, 1, 0⟩, ⟨8, 10, 1, 0, 1, 0, 1, 1, 0⟩], [⟨8, 12, 0, 0, 0, 0, 0, 0, 0⟩, ⟨8, 12, 1, 0, 1, 0, 0, 0, 0⟩, ⟨8, 12, 0, 0, 0, 0, 1, 1, 0⟩, ⟨8, 12, 1, 0, 1, 0, 1, 1, 0⟩]],
      [⟨8, 1, 0, 0, 0, 0, 0, 0, 2⟩, ⟨8, 1, 1, 0, 1, 0, 0, 0, 2⟩, ⟨8, 1, 0, 0, 0, 0, 1, 1, 2⟩, ⟨8, 1, 1, 0, 1, 0, 1, 1, 2⟩]⟩,
    ⟨2, -1, 4, 9,
      [[⟨2, 0, 0, 0, 1, 0, 0, 0, 0⟩, ⟨2, 0, 1, 0, 2, 0, 0, 0, 0⟩, ⟨8, 0, 0, 0, 1, 0, 1, 0, 0⟩, ⟨8, 0, 1, 0, 2, 0, 1, 0, 0⟩], [⟨8, 5, 0, 0, 0, 0, 0, 0, 0⟩, ⟨8, 5, 1, 0, 1, 0, 0, 0, 0⟩, ⟨8, 5, 0, 0, 0, 0, 1, 1, 0⟩, ⟨8, 5, 1, 0, 1, 0, 1, 1, 0⟩], [⟨8, 11, 0, 0, 0, 0, 0, 0, 0⟩, ⟨8, 11, 1, 0, 1, 0, 0, 0, 0⟩, ⟨8, 11, 0, 0, 0, 0, 1, 1, 0⟩, ⟨8, 11, 1, 0, 1, 0, 1, 1, 0⟩], [⟨8, 14, 0, 0, 0, 0, 0, 0, 0⟩, ⟨8, 14, 1, 0, 1, 0, 0, 0, 0⟩, ⟨8, 14, 0, 0, 0, 0, 1, 1, 0⟩, ⟨8, 14, 1, 0, 1, 0, 1, 1, 0⟩]],
      [⟨8, 5, 0, 0, 0, 0, 0, 0, 3⟩, ⟨8, 5, 1, 0, 1, 0, 0, 0, 3⟩, ⟨8, 5, 0, 0, 0, 0, 1, 1, 3⟩, ⟨8, 5, 1, 0, 1, 0, 1, 1, 3⟩]⟩,
    ⟨2, -1, 5, 8,
      [[⟨2, 9, 0, 0, 0, 0, 0, 0, 0⟩, ⟨2, 9, 1, 0, 1, 0, 0, 0, 0⟩, ⟨8, 9, 0, 0, 0, 0, 1, 0, 0⟩, ⟨8, 9, 1, 0, 1, 0, 1, 0, 0⟩], [⟨2, 13, 0, 0, 0, 0, 0, 0, 0⟩, ⟨2, 13, 1, 0, 1, 0, 0, 0, 0⟩, ⟨8, 13, 0, 0, 0, 0, 1, 0, 0⟩, ⟨8, 13, 1, 0, 1, 0, 1, 0, 0⟩], [⟨2, 1, 0, 0, 1, 0, 0, 0, 0⟩, ⟨2, 1, 1, 0, 2, 0, 0, 0, 0⟩, ⟨8, 1, 0, 0, 1, 0, 1, 0, 0⟩, ⟨8, 1, 1, 0, 2, 0, 1, 0, 0⟩], [⟨8, 4, 0, 0, 0, 0, 0, 0, 0⟩, ⟨8, 4, 1, 0, 1, 0, 0, 0, 0⟩, ⟨8, 4, 0, 0, 0, 0, 1, 1, 0⟩, ⟨8, 4, 1, 0, 1, 0, 1, 1, 0⟩]],
      [⟨2, 9, 0, 0, 0, 0, 0, 0, 3⟩, ⟨2, 9, 1, 0, 1, 0, 0, 0, 3⟩, ⟨8, 9, 0, 0, 0, 0, 1, 0, 3⟩, ⟨8, 9, 1, 0, 1, 0, 1, 0, 3⟩]⟩,
    ⟨2, -1, 6, 12,
      [[⟨8, 7, 0, 0, 0, 0, 0, 0, 0⟩, ⟨8, 7, 1, 0, 1, 0, 0, 0, 0⟩, ⟨8, 7, 0, 0, 0, 0, 1, 1, 0⟩, ⟨8, 7, 1, 0, 1, 0, 1, 1, 0⟩], [⟨8, 15, 0, 0, 0, 0, 0, 0, 0⟩, ⟨8, 15, 1, 0, 1, 0, 0, 0, 0⟩, ⟨8, 15, 0, 0, 0, 0, 1, 1, 0⟩, ⟨8, 15, 1, 0, 1, 0, 1, 1, 0⟩], [⟨8, 18, 0, 0, 0, 0, 0, 0, 0⟩, ⟨8, 18, 1, 0, 1, 0, 0, 0, 0⟩, ⟨8, 18, 0, 0, 0, 0, 1, 1, 0⟩, ⟨8, 18, 1, 0, 1, 0, 1, 1, 0⟩], [⟨8, 1, 0, 0, 0, 0, 0, 1, 0⟩, ⟨8, 1, 1, 0, 1, 0, 0, 1, 0⟩, ⟨8, 1, 0, 0, 0, 0, 1, 2, 0⟩, ⟨8, 1, 1, 0, 1, 0, 1, 2, 0⟩], [⟨8, 10, 0, 0, 0, 0, 0, 1, 0⟩, ⟨8, 10, 1, 0, 1, 0, 0, 1, 0⟩, ⟨8, 10, 0, 0, 0, 0, 1, 2, 0⟩, ⟨8, 10, 1, 0, 1, 0, 1, 2, 0⟩]],
      [⟨8, 7, 0, 0, 0, 0, 0, 0, 1⟩, ⟨8, 7, 1, 0, 1, 0, 0, 0, 1⟩, ⟨8, 7, 0, 0, 0, 0, 1, 1, 1⟩, ⟨8, 7, 1, 0, 1, 0, 1, 1, 1⟩]⟩,
    ⟨2, -1, 7, 11,
      [[⟨8, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨8, 0, 1, 0, 1, 0, 0, 0, 0⟩, ⟨8, 0, 0, 0, 0, 0, 1, 1, 0⟩, ⟨8, 0, 1, 0, 1, 0, 1, 1, 0⟩], [⟨8, 6, 0, 0, 0, 0, 0, 0, 0⟩, ⟨8, 6, 1, 0, 1, 0, 0, 0, 0⟩, ⟨8, 6, 0, 0, 0, 0, 1, 1, 0⟩, ⟨8, 6, 1, 0, 1, 0, 1, 1, 0⟩], [⟨8, 8, 0, 0, 0, 0, 0, 0, 0⟩, ⟨8, 8, 1, 0, 1, 0, 0, 0, 0⟩, ⟨8, 8, 0, 0, 0, 0, 1, 1, 0⟩, ⟨8, 8, 1, 0, 1, 0, 1, 1, 0⟩], [⟨8, 15, 0, 0, 0, 0, 0, 0, 0⟩, ⟨8, 15, 1, 0, 1, 0, 0, 0, 0⟩, ⟨8, 15, 0, 0, 0, 0, 1, 1, 0⟩, ⟨8, 15, 1, 0, 1, 0, 1, 1, 0⟩], [⟨8, 18, 0, 0, 0, 0, 0, 0, 0⟩, ⟨8, 18, 1, 0, 1, 0, 0, 0, 0⟩, ⟨8, 18, 0, 0, 0, 0, 1, 1, 0⟩, ⟨8, 18, 1, 0, 1, 0, 1, 1, 0⟩]],
      [⟨8, 0, 0, 0, 0, 0, 0, 0, 1⟩, ⟨8, 0, 1, 0, 1, 0, 0, 0, 1⟩, ⟨8, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨8, 0, 1, 0, 1, 0, 1, 1, 1⟩]⟩,
    ⟨2, -1, 8, 11,
      [[⟨8, 2, 0, 0, 0, 0, 0, 0, 0⟩, ⟨8, 2, 1, 0, 1, 0, 0, 0, 0⟩, ⟨8, 2, 0, 0, 0, 0, 1, 1, 0⟩, ⟨8, 2, 1, 0, 1, 0, 1, 1, 0⟩], [⟨8, 7, 0, 0, 0, 0, 0, 0, 0⟩, ⟨8, 7, 1, 0, 1, 0, 0, 0, 0⟩, ⟨8, 7, 0, 0, 0, 0, 1, 1, 0⟩, ⟨8, 7, 1, 0, 1, 0, 1, 1, 0⟩], [⟨8, 9, 0, 0, 0, 0, 0, 0, 0⟩, ⟨8, 9, 1, 0, 1, 0, 0, 0, 0⟩, ⟨8, 9, 0, 0, 0, 0, 1, 1, 0⟩, ⟨8, 9, 1, 0, 1, 0, 1, 1, 0⟩], [⟨8, 16, 0, 0, 0, 0, 0, 0, 0⟩, ⟨8, 16, 1, 0, 1, 0, 0, 0, 0⟩, ⟨8, 16, 0, 0, 0, 0, 1, 1, 0⟩, ⟨8, 16, 1, 0, 1, 0, 1, 1, 0⟩], [⟨8, 18, 0, 0, 0, 0, 0, 0, 0⟩, ⟨8, 18, 1, 0, 1, 0, 0, 0, 0⟩, ⟨8, 18, 0, 0, 0, 0, 1, 1, 0⟩, ⟨8, 18, 1, 0, 1, 0, 1, 1, 0⟩]],
      [⟨8, 2, 0, 0, 0, 0, 0, 0, 2⟩, ⟨8, 2, 1, 0, 1, 0, 0, 0, 2⟩, ⟨8, 2, 0, 0, 0, 0, 1, 1, 2⟩, ⟨8, 2, 1, 0, 1, 0, 1, 1, 2⟩]⟩,
    ⟨2, -1, 9, 12,
      [[⟨8, 8, 0, 0, 0, 0, 0, 0, 0⟩, ⟨8, 8, 1, 0, 1, 0, 0, 0, 0⟩, ⟨8, 8, 0, 0, 0, 0, 1, 1, 0⟩, ⟨8, 8, 1, 0, 1, 0, 1, 1, 0⟩], [⟨8, 16, 0, 0, 0, 0, 0, 0, 0⟩, ⟨8, 16, 1, 0, 1, 0, 0, 0, 0⟩, ⟨8, 16, 0, 0, 0, 0, 1, 1, 0⟩, ⟨8, 16, 1, 0, 1, 0, 1, 1, 0⟩], [⟨8, 18, 0, 0, 0, 0, 0, 0, 0⟩, ⟨8, 18, 1, 0, 1, 0, 0, 0, 0⟩, ⟨8, 18, 0, 0, 0, 0, 1, 1, 0⟩, ⟨8, 18, 1, 0, 1, 0, 1, 1, 0⟩], [⟨8, 5, 0, 0, 0, 0, 0, 1, 0⟩, ⟨8, 5, 1, 0, 1, 0, 0, 1, 0⟩, ⟨8, 5, 0, 0, 0, 0, 1, 2, 0⟩, ⟨8, 5, 1, 0, 1, 0, 1, 2, 0⟩], [⟨8, 11, 0, 0, 0, 0, 0, 1, 0⟩, ⟨8, 11, 1, 0, 1, 0, 0, 1, 0⟩, ⟨8, 11, 0, 0, 0, 0, 1, 2, 0⟩, ⟨8, 11, 1, 0, 1, 0, 1, 2, 0⟩]],
      [⟨8, 8, 0, 0, 0, 0, 0, 0, 2⟩, ⟨8, 8, 1, 0, 1, 0, 0, 0, 2⟩, ⟨8, 8, 0, 0, 0, 0, 1, 1, 2⟩, ⟨8, 8, 1, 0, 1, 0, 1, 1, 2⟩]⟩,
    ⟨2, -1, 10, 8,
      [[⟨2, 6, 0, 0, 0, 0, 0, 0, 0⟩, ⟨2, 6, 1, 0, 1, 0, 0, 0, 0⟩, ⟨8, 6, 0, 0, 0, 0, 1, 0, 0⟩, ⟨8, 6, 1, 0, 1, 0, 1, 0, 0⟩], [⟨2, 18, 0, 0, 0, 0, 0, 0, 0⟩, ⟨2, 18, 1, 0, 1, 0, 0, 0, 0⟩, ⟨8, 18, 0, 0, 0, 0, 1, 0, 0⟩, ⟨8, 18, 1, 0, 1, 0, 1, 0, 0⟩], [⟨8, 3, 0, 0, 0, 0, 0, 0, 0⟩, ⟨8, 3, 1, 0, 1, 0, 0, 0, 0⟩, ⟨8, 3, 0, 0, 0, 0, 1, 1, 0⟩, ⟨8, 3, 1, 0, 1, 0, 1, 1, 0⟩], [⟨8, 11, 0, 0, 0, 0, 0, 0, 0⟩, ⟨8, 11, 1, 0, 1, 0, 0, 0, 0⟩, ⟨8, 11, 0, 0, 0, 0, 1, 1, 0⟩, ⟨8, 11, 1, 0, 1, 0, 1, 1, 0⟩], [⟨8, 17, 0, 0, 0, 0, 0, 0, 0⟩, ⟨8, 17, 1, 0, 1, 0, 0, 0, 0⟩, ⟨8, 17, 0, 0, 0, 0, 1, 1, 0⟩, ⟨8, 17, 1, 0, 1, 0, 1, 1, 0⟩]],
      [⟨2, 6, 0, 0, 0, 0, 0, 0, 4⟩, ⟨2, 6, 1, 0, 1, 0, 0, 0, 4⟩, ⟨8, 6, 0, 0, 0, 0, 1, 0, 4⟩, ⟨8, 6, 1, 0, 1, 0, 1, 0, 4⟩]⟩,
    ⟨2, -1, 11, 8,
      [[⟨2, 9, 0, 0, 0, 0, 0, 0, 0⟩, ⟨2, 9, 1, 0, 1, 0, 0, 0, 0⟩, ⟨8, 9, 0, 0, 0, 0, 1, 0, 0⟩, ⟨8, 9, 1, 0, 1, 0, 1, 0, 0⟩], [⟨2, 18, 0, 0, 0, 0, 0, 0, 0⟩, ⟨2, 18, 1, 0, 1, 0, 0, 0, 0⟩, ⟨8, 18, 0, 0, 0, 0, 1, 0, 0⟩, ⟨8, 18, 1, 0, 1, 0, 1, 0, 0⟩], [⟨8, 4, 0, 0, 0, 0, 0, 0, 0⟩, ⟨8, 4, 1, 0, 1, 0, 0, 0, 0⟩, ⟨8, 4, 0, 0, 0, 0, 1, 1, 0⟩, ⟨8, 4, 1, 0, 1, 0, 1, 1, 0⟩], [⟨8, 10, 0, 0, 0, 0, 0, 0, 0⟩, ⟨8, 10, 1, 0, 1, 0, 0, 0, 0⟩, ⟨8, 10, 0, 0, 0, 0, 1, 1, 0⟩, ⟨8, 10, 1, 0, 1, 0, 1, 1, 0⟩], [⟨8, 17, 0, 0, 0, 0, 0, 0, 0⟩, ⟨8, 17, 1, 0, 1, 0, 0, 0, 0⟩, ⟨8, 17, 0, 0, 0, 0, 1, 1, 0⟩, ⟨8, 17, 1, 0, 1, 0, 1, 1, 0⟩]],
      [⟨2, 9, 0, 0, 0, 0, 0, 0, 4⟩, ⟨2, 9, 1, 0, 1, 0, 0, 0, 4⟩, ⟨8, 9, 0, 0, 0, 0, 1, 0, 4⟩, ⟨8, 9, 1, 0, 1, 0, 1, 0, 4⟩]⟩,
    ⟨2, -1, 12, 10,
      [[⟨8, 2, 0, 0, 0, 0, 0, 0, 0⟩, ⟨8, 2, 1, 0, 1, 0, 0, 0, 0⟩, ⟨8, 2, 0, 0, 0, 0, 1, 1, 0⟩, ⟨8, 2, 1, 0, 1, 0, 1, 1, 0⟩], [⟨8, 3, 0, 0, 0, 0, 0, 0, 0⟩, ⟨8, 3, 1, 0, 1, 0, 0, 0, 0⟩, ⟨8, 3, 0, 0, 0, 0, 1, 1, 0⟩, ⟨8, 3, 1, 0, 1, 0, 1, 1, 0⟩], [⟨8, 16, 0, 0, 0, 0, 0, 0, 0⟩, ⟨8, 16, 1, 0, 1, 0, 0, 0, 0⟩, ⟨8, 16, 0, 0, 0, 0, 1, 1, 0⟩, ⟨8, 16, 1, 0, 1, 0, 1, 1, 0⟩], [⟨8, 17, 0, 0, 0, 0, 0, 0, 0⟩, ⟨8, 17, 1, 0, 1, 0, 0, 0, 0⟩, ⟨8, 17, 0, 0, 0, 0, 1, 1, 0⟩, ⟨8, 17, 1, 0, 1, 0, 1, 1, 0⟩]],
      [⟨8, 3, 0, 0, 0, 0, 0, 0, 3⟩, ⟨8, 3, 1, 0, 1, 0, 0, 0, 3⟩, ⟨8, 3, 0, 0, 0, 0, 1, 1, 3⟩, ⟨8, 3, 1, 0, 1, 0, 1, 1, 3⟩]⟩,
    ⟨2, -1, 13, 12,
      [[⟨2, 15, 0, 0, 1, 0, 0, 0, 0⟩, ⟨2, 15, 1, 0, 2, 0, 0, 0, 0⟩, ⟨8, 15, 0, 0, 1, 0, 1, 0, 0⟩, ⟨8, 15, 1, 0, 2, 0, 1, 0, 0⟩], [⟨8, 16, 0, 0, 0, 0, 0, 0, 0⟩, ⟨8, 16, 1, 0, 1, 0, 0, 0, 0⟩, ⟨8, 16, 0, 0, 0, 0, 1, 1, 0⟩, ⟨8, 16, 1, 0, 1, 0, 1, 1, 0⟩], [⟨8, 1, 0, 0, 1, 0, 0, 0, 0⟩, ⟨8, 1, 1, 0, 2, 0, 0, 0, 0⟩, ⟨8, 1, 0, 0, 1, 0, 1, 1, 0⟩, ⟨8, 1, 1, 0, 2, 0, 1, 1, 0⟩], [⟨8, 5, 0, 0, 0, 0, 0, 1, 0⟩, ⟨8, 5, 1, 0, 1, 0, 0, 1, 0⟩, ⟨8, 5, 0, 0, 0, 0, 1, 2, 0⟩, ⟨8, 5, 1, 0, 1, 0, 1, 2, 0⟩]],
      [⟨2, 15, 0, 0, 1, 0, 0, 0, 2⟩, ⟨2, 15, 1, 0, 2, 0, 0, 0, 2⟩, ⟨8, 15, 0, 0, 1, 0, 1, 0, 2⟩, ⟨8, 15, 1, 0, 2, 0, 1, 0, 2⟩]⟩,
    ⟨2, -1, 14, 10,
      [[⟨2, 0, 0, 0, 1, 0, 0, 0, 0⟩, ⟨2, 0, 1, 0, 2, 0, 0, 0, 0⟩, ⟨8, 0, 0, 0, 1, 0, 1, 0, 0⟩, ⟨8, 0, 1, 0, 2, 0, 1, 0, 0⟩], [⟨2, 15, 0, 0, 1, 0, 0, 0, 0⟩, ⟨2, 15, 1, 0, 2, 0, 0, 0, 0⟩, ⟨8, 15, 0, 0, 1, 0, 1, 0, 0⟩, ⟨8, 15, 1, 0, 2, 0, 1, 0, 0⟩], [⟨8, 4, 0, 0, 0, 0, 0, 0, 0⟩, ⟨8, 4, 1, 0, 1, 0, 0, 0, 0⟩, ⟨8, 4, 0, 0, 0, 0, 1, 1, 0⟩, ⟨8, 4, 1, 0, 1, 0, 1, 1, 0⟩], [⟨8, 17, 0, 0, 0, 0, 0, 0, 0⟩, ⟨8, 17, 1, 0, 1, 0, 0, 0, 0⟩, ⟨8, 17, 0, 0, 0, 0, 1, 1, 0⟩, ⟨8, 17, 1, 0, 1, 0, 1, 1, 0⟩]],
      [⟨8, 4, 0, 0, 0, 0, 0, 0, 3⟩, ⟨8, 4, 1, 0, 1, 0, 0, 0, 3⟩, ⟨8, 4, 0, 0, 0, 0, 1, 1, 3⟩, ⟨8, 4, 1, 0, 1, 0, 1, 1, 3⟩]⟩,
    ⟨2, -1, 15, 11,
      [[⟨8, 6, 0, 0, 0, 0, 0, 0, 0⟩, ⟨8, 6, 1, 0, 1, 0, 0, 0, 0⟩, ⟨8, 6, 0, 0, 0, 0, 1, 1, 0⟩, ⟨8, 6, 1, 0, 1, 0, 1, 1, 0⟩], [⟨8, 7, 0, 0, 0, 0, 0, 0, 0⟩, ⟨8, 7, 1, 0, 1, 0, 0, 0, 0⟩, ⟨8, 7, 0, 0, 0, 0, 1, 1, 0⟩, ⟨8, 7, 1, 0, 1, 0, 1, 1, 0⟩], [⟨3, 13, 0, 0, 1, 0, 0, 0, 0⟩, ⟨8, 13, 1, 0, 0, 0, 0, 1, 0⟩, ⟨3, 13, 0, 1, 2, 0, 0, 0, 0⟩, ⟨8, 13, 1, 0, 0, 0, 1, 2, 0⟩], [⟨3, 14, 0, 0, 1, 0, 0, 0, 0⟩, ⟨8, 14, 1, 0, 0, 0, 0, 1, 0⟩, ⟨3, 14, 0, 1, 2, 0, 0, 0, 0⟩, ⟨8, 14, 1, 0, 0, 0, 1, 2, 0⟩]],
      [⟨3, 14, 0, 0, 1, 0, 0, 0, 1⟩, ⟨8, 14, 1, 0, 0, 0, 0, 1, 1⟩, ⟨3, 14, 0, 1, 2, 0, 0, 0, 1⟩, ⟨8, 14, 1, 0, 0, 0, 1, 2, 1⟩]⟩,
    ⟨2, -1, 16, 11,
      [[⟨8, 8, 0, 0, 0, 0, 0, 0, 0⟩, ⟨8, 8, 1, 0, 1, 0, 0, 0, 0⟩, ⟨8, 8, 0, 0, 0, 0, 1, 1, 0⟩, ⟨8, 8, 1, 0, 1, 0, 1, 1, 0⟩], [⟨8, 9, 0, 0, 0, 0, 0, 0, 0⟩, ⟨8, 9, 1, 0, 1, 0, 0, 0, 0⟩, ⟨8, 9, 0, 0, 0, 0, 1, 1, 0⟩, ⟨8, 9, 1, 0, 1, 0, 1, 1, 0⟩], [⟨8, 12, 0, 0, 0, 0, 0, 0, 0⟩, ⟨8, 12, 1, 0, 1, 0, 0, 0, 0⟩, ⟨8, 12, 0, 0, 0, 0, 1, 1, 0⟩, ⟨8, 12, 1, 0, 1, 0, 1, 1, 0⟩], [⟨8, 13, 0, 0, 0, 0, 0, 0, 0⟩, ⟨8, 13, 1, 0, 1, 0, 0, 0, 0⟩, ⟨8, 13, 0, 0, 0, 0, 1, 1, 0⟩, ⟨8, 13, 1, 0, 1, 0, 1, 1, 0⟩]],
      [⟨8, 12, 0, 0, 0, 0, 0, 0, 2⟩, ⟨8, 12, 1, 0, 1, 0, 0, 0, 2⟩, ⟨8, 12, 0, 0, 0, 0, 1, 1, 2⟩, ⟨8, 12, 1, 0, 1, 0, 1, 1, 2⟩]⟩,
    ⟨2, -1, 17, 9,
      [[⟨8, 10, 0, 0, 0, 0, 0, 0, 0⟩, ⟨8, 10, 1, 0, 1, 0, 0, 0, 0⟩, ⟨8, 10, 0, 0, 0, 0, 1, 1, 0⟩, ⟨8, 10, 1, 0, 1, 0, 1, 1, 0⟩], [⟨8, 11, 0, 0, 0, 0, 0, 0, 0⟩, ⟨8, 11, 1, 0, 1, 0, 0, 0, 0⟩, ⟨8, 11, 0, 0, 0, 0, 1, 1, 0⟩, ⟨8, 11, 1, 0, 1, 0, 1, 1, 0⟩], [⟨8, 12, 0, 0, 0, 0, 0, 0, 0⟩, ⟨8, 12, 1, 0, 1, 0, 0, 0, 0⟩, ⟨8, 12, 0, 0, 0, 0, 1, 1, 0⟩, ⟨8, 12, 1, 0, 1, 0, 1, 1, 0⟩], [⟨8, 14, 0, 0, 0, 0, 0, 0, 0⟩, ⟨8, 14, 1, 0, 1, 0, 0, 0, 0⟩, ⟨8, 14, 0, 0, 0, 0, 1, 1, 0⟩, ⟨8, 14, 1, 0, 1, 0, 1, 1, 0⟩]],
      [⟨8, 10, 0, 0, 0, 0, 0, 0, 4⟩, ⟨8, 10, 1, 0, 1, 0, 0, 0, 4⟩, ⟨8, 10, 0, 0, 0, 0, 1, 1, 4⟩, ⟨8, 10, 1, 0, 1, 0, 1, 1, 4⟩]⟩,
    ⟨2, -1, 18, 12,
      [[⟨8, 6, 0, 0, 0, 0, 0, 0, 0⟩, ⟨8, 6, 1, 0, 1, 0, 0, 0, 0⟩, ⟨8, 6, 0, 0, 0, 0, 1, 1, 0⟩, ⟨8, 6, 1, 0, 1, 0, 1, 1, 0⟩], [⟨8, 7, 0, 0, 0, 0, 0, 0, 0⟩, ⟨8, 7, 1, 0, 1, 0, 0, 0, 0⟩, ⟨8, 7, 0, 0, 0, 0, 1, 1, 0⟩, ⟨8, 7, 1, 0, 1, 0, 1, 1, 0⟩], [⟨8, 8, 0, 0, 0, 0, 0, 0, 0⟩, ⟨8, 8, 1, 0, 1, 0, 0, 0, 0⟩, ⟨8, 8, 0, 0, 0, 0, 1, 1, 0⟩, ⟨8, 8, 1, 0, 1, 0, 1, 1, 0⟩], [⟨8, 9, 0, 0, 0, 0, 0, 0, 0⟩, ⟨8, 9, 1, 0, 1, 0, 0, 0, 0⟩, ⟨8, 9, 0, 0, 0, 0, 1, 1, 0⟩, ⟨8, 9, 1, 0, 1, 0, 1, 1, 0⟩], [⟨8, 10, 0, 0, 0, 0, 0, 1, 0⟩, ⟨8, 10, 1, 0, 1, 0, 0, 1, 0⟩, ⟨8, 10, 0, 0, 0, 0, 1, 2, 0⟩, ⟨8, 10, 1, 0, 1, 0, 1, 2, 0⟩], [⟨8, 11, 0, 0, 0, 0, 0, 1, 0⟩, ⟨8, 11, 1, 0, 1, 0, 0, 1, 0⟩, ⟨8, 11, 0, 0, 0, 0, 1, 2, 0⟩, ⟨8, 11, 1, 0, 1, 0, 1, 2, 0⟩]],
      [⟨8, 7, 0, 0, 0, 0, 0, 0, 4⟩, ⟨8, 7, 1, 0, 1, 0, 0, 0, 4⟩, ⟨8, 7, 0, 0, 0, 0, 1, 1, 4⟩, ⟨8, 7, 1, 0, 1, 0, 1, 1, 4⟩]⟩]⟩,
  ⟨2, 1, 0, 0, 1, [(1, 0, 1), (0, 1, 1)], 1, 0, 1, 1, 0, 1, 1, 1,
   [⟨1, 1, 0, 12,
      [[⟨9, 2, 0, 0, 0, 0, 0, 0, 0⟩, ⟨9, 2, 1, 0, 1, 0, 0, 0, 0⟩, ⟨9, 2, 0, 0, 0, 0, 1, 1, 0⟩, ⟨9, 2, 1, 0, 1, 0, 1, 1, 0⟩], [⟨9, 7, 0, 0, 0, 0, 0, 0, 0⟩, ⟨9, 7, 1, 0, 1, 0, 0, 0, 0⟩, ⟨9, 7, 0, 0, 0, 0, 1, 1, 0⟩, ⟨9, 7, 1, 0, 1, 0, 1, 1, 0⟩], [⟨9, 4, 0, 0, 0, 0, 0, 1, 0⟩, ⟨9, 4, 1, 0, 1, 0, 0, 1, 0⟩, ⟨9, 4, 0, 0, 0, 0, 1, 2, 0⟩, ⟨9, 4, 1, 0, 1, 0, 1, 2, 0⟩], [⟨9, 14, 0, 0, 0, 0, 0, 1, 0⟩, ⟨9, 14, 1, 0, 1, 0, 0, 1, 0⟩, ⟨9, 14, 0, 0, 0, 0, 1, 2, 0⟩, ⟨9, 14, 1, 0, 1, 0, 1, 2, 0⟩]],
      [⟨9, 2, 0, 0, 0, 0, 0, 0, 0⟩, ⟨9, 2, 1, 0, 1, 0, 0, 0, 0⟩, ⟨9, 2, 0, 0, 0, 0, 1, 1, 0⟩, ⟨9, 2, 1, 0, 1, 0, 1, 1, 0⟩]⟩,
    ⟨1, 1, 1, 10,
      [[⟨4, 6, 0, 0, 0, 0, 0, 0, 0⟩, ⟨9, 6, 1, 0, 0, 0, 0, 0, 0⟩, ⟨4, 6, 0, 1, 1, 0, 0, 0, 0⟩, ⟨9, 6, 1, 0, 0, 0, 1, 1, 0⟩], [⟨4, 13, 0, 0, 1, 0, 0, 0, 0⟩, ⟨9, 13, 1, 0, 0, 0, 0, 1, 0⟩, ⟨4, 13, 0, 1, 2, 0, 0, 0, 0⟩, ⟨9, 13, 1, 0, 0, 0, 1, 2, 0⟩], [⟨9, 3, 0, 0, 0, 0, 0, 0, 0⟩, ⟨9, 3, 1, 0, 1, 0, 0, 0, 0⟩, ⟨9, 3, 0, 0, 0, 0, 1, 1, 0⟩, ⟨9, 3, 1, 0, 1, 0, 1, 1, 0⟩], [⟨9, 5, 0, 0, 0, 0, 0, 1, 0⟩, ⟨9, 5, 1, 0, 1, 0, 0, 1, 0⟩, ⟨9, 5, 0, 0, 0, 0, 1, 2, 0⟩, ⟨9, 5, 1, 0, 1, 0, 1, 2, 0⟩]],
      [⟨4, 6, 0, 0, 0, 0, 0, 0, 3⟩, ⟨9, 6, 1, 0, 0, 0, 0, 0, 3⟩, ⟨4, 6, 0, 1, 1, 0, 0, 0, 3⟩, ⟨9, 6, 1, 0, 0, 0, 1, 1, 3⟩]⟩,
    ⟨1, 1, 2, 11,
      [[⟨9, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨9, 0, 1, 0, 1, 0, 0, 0, 0⟩, ⟨9, 0, 0, 0, 0, 0, 1, 1, 0⟩, ⟨9, 0, 1, 0, 1, 0, 1, 1, 0⟩], [⟨9, 3, 0, 0, 0, 0, 0, 0, 0⟩, ⟨9, 3, 1, 0, 1, 0, 0, 0, 0⟩, ⟨9, 3, 0, 0, 0, 0, 1, 1, 0⟩, ⟨9, 3, 1, 0, 1, 0, 1, 1, 0⟩], [⟨9, 8, 0, 0, 0, 0, 0, 0, 0⟩, ⟨9, 8, 1, 0, 1, 0, 0, 0, 0⟩, ⟨9, 8, 0, 0, 0, 0, 1, 1, 0⟩, ⟨9, 8, 1, 0, 1, 0, 1, 1, 0⟩], [⟨9, 12, 0, 0, 0, 0, 0, 0, 0⟩, ⟨9, 12, 1, 0, 1, 0, 0, 0, 0⟩, ⟨9, 12, 0, 0, 0, 0, 1, 1, 0⟩, ⟨9, 12, 1, 0, 1, 0, 1, 1, 0⟩]],
      [⟨9, 3, 0, 0, 0, 0, 0, 0, 1⟩, ⟨9, 3, 1, 0, 1, 0, 0, 0, 1⟩, ⟨9, 3, 0, 0, 0, 0, 1, 1, 1⟩, ⟨9, 3, 1, 0, 1, 0, 1, 1, 1⟩]⟩,
    ⟨1, 1, 3, 10,
      [[⟨9, 1, 0, 0, 0, 0, 0, 0, 0⟩, ⟨9, 1, 1, 0, 1, 0, 0, 0, 0⟩, ⟨9, 1, 0, 0, 0, 0, 1, 1, 0⟩, ⟨9, 1, 1, 0, 1, 0, 1, 1, 0⟩], [⟨9, 2, 0, 0, 0, 0, 0, 0, 0⟩, ⟨9, 2, 1, 0, 1, 0, 0, 0, 0⟩, ⟨9, 2, 0, 0, 0, 0, 1, 1, 0⟩, ⟨9, 2, 1, 0, 1, 0, 1, 1, 0⟩], [⟨9, 10, 0, 0, 0, 0, 0, 0, 0⟩, ⟨9, 10, 1, 0, 1, 0, 0, 0, 0⟩, ⟨9, 10, 0, 0, 0, 0, 1, 1, 0⟩, ⟨9, 10, 1, 0, 1, 0, 1, 1, 0⟩], [⟨9, 12, 0, 0, 0, 0, 0, 0, 0⟩, ⟨9, 12, 1, 0, 1, 0, 0, 0, 0⟩, ⟨9, 12, 0, 0, 0, 0, 1, 1, 0⟩, ⟨9, 12, 1, 0, 1, 0, 1, 1, 0⟩]],
      [⟨9, 10, 0, 0, 0, 0, 0, 0, 2⟩, ⟨9, 10, 1, 0, 1, 0, 0, 0, 2⟩, ⟨9, 10, 0, 0, 0, 0, 1, 1, 2⟩, ⟨9, 10, 1, 0, 1, 0, 1, 1, 2⟩]⟩,
    ⟨1, 1, 4, 7,
      [[⟨3, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨3, 0, 1, 0, 1, 0, 0, 0, 0⟩, ⟨9, 0, 0, 0, 0, 0, 1, 0, 0⟩, ⟨9, 0, 1, 0, 1, 0, 1, 0, 0⟩], [⟨9, 5, 0, 0, 0, 0, 0, 0, 0⟩, ⟨9, 5, 1, 0, 1, 0, 0, 0, 0⟩, ⟨9, 5, 0, 0, 0, 0, 1, 1, 0⟩, ⟨9, 5, 1, 0, 1, 0, 1, 1, 0⟩], [⟨9, 11, 0, 0, 0, 0, 0, 0, 0⟩, ⟨9, 11, 1, 0, 1, 0, 0, 0, 0⟩, ⟨9, 11, 0, 0, 0, 0, 1, 1, 0⟩, ⟨9, 11, 1, 0, 1, 0, 1, 1, 0⟩], [⟨9, 14, 0, 0, 0, 0, 0, 0, 0⟩, ⟨9, 14, 1, 0, 1, 0, 0, 0, 0⟩, ⟨9, 14, 0, 0, 0, 0, 1, 1, 0⟩, ⟨9, 14, 1, 0, 1, 0, 1, 1, 0⟩]],
      [⟨9, 5, 0, 0, 0, 0, 0, 0, 3⟩, ⟨9, 5, 1, 0, 1, 0, 0, 0, 3⟩, ⟨9, 5, 0, 0, 0, 0, 1, 1, 3⟩, ⟨9, 5, 1, 0, 1, 0, 1, 1, 3⟩]⟩,
    ⟨1, 1, 5, 6,
      [[⟨4, 9, 0, 0, 0, 0, 0, 0, 0⟩, ⟨9, 9, 1, 0, 0, 0, 0, 0, 0⟩, ⟨4, 9, 0, 1, 1, 0, 0, 0, 0⟩, ⟨9, 9, 1, 0, 0, 0, 1, 1, 0⟩], [⟨4, 13, 0, 0, 0, 0, 0, 0, 0⟩, ⟨9, 13, 1, 0, 0, 0, 0, 0, 0⟩, ⟨4, 13, 0, 1, 1, 0, 0, 0, 0⟩, ⟨9, 13, 1, 0, 0, 0, 1, 1, 0⟩], [⟨3, 1, 0, 0, 0, 0, 0, 0, 0⟩, ⟨3, 1, 1, 0, 1, 0, 0, 0, 0⟩, ⟨9, 1, 0, 0, 0, 0, 1, 0, 0⟩, ⟨9, 1, 1, 0, 1, 0, 1, 0, 0⟩], [⟨9, 4, 0, 0, 0, 0, 0, 0, 0⟩, ⟨9, 4, 1, 0, 1, 0, 0, 0, 0⟩, ⟨9, 4, 0, 0, 0, 0, 1, 1, 0⟩, ⟨9, 4, 1, 0, 1, 0, 1, 1, 0⟩]],
      [⟨4, 13, 0, 0, 0, 0, 0, 0, 3⟩, ⟨9, 13, 1, 0, 0, 0, 0, 0, 3⟩, ⟨4, 13, 0, 1, 1, 0, 0, 0, 3⟩, ⟨9, 13, 1, 0, 0, 0, 1, 1, 3⟩]⟩,
    ⟨1, 1, 6, 14,
      [[⟨9, 7, 0, 0, 0, 0, 0, 0, 0⟩, ⟨9, 7, 1, 0, 1, 0, 0, 0, 0⟩, ⟨9, 7, 0, 0, 0, 0, 1, 1, 0⟩, ⟨9, 7, 1, 0, 1, 0, 1, 1, 0⟩], [⟨9, 15, 0, 0, 0, 0, 0, 0, 0⟩, ⟨9, 15, 1, 0, 1, 0, 0, 0, 0⟩, ⟨9, 15, 0, 0, 0, 0, 1, 1, 0⟩, ⟨9, 15, 1, 0, 1, 0, 1, 1, 0⟩], [⟨9, 18, 0, 0, 0, 0, 0, 0, 0⟩, ⟨9, 18, 1, 0, 1, 0, 0, 0, 0⟩, ⟨9, 18, 0, 0, 0, 0, 1, 1, 0⟩, ⟨9, 18, 1, 0, 1, 0, 1, 1, 0⟩], [⟨9, 1, 0, 0, 1, 0, 0, 0, 0⟩, ⟨9, 1, 1, 0, 2, 0, 0, 0, 0⟩, ⟨9, 1, 0, 0, 1, 0, 1, 1, 0⟩, ⟨9, 1, 1, 0, 2, 0, 1, 1, 0⟩], [⟨9, 10, 0, 0, 1, 0, 0, 0, 0⟩, ⟨9, 10, 1, 0, 2, 0, 0, 0, 0⟩, ⟨9, 10, 0, 0, 1, 0, 1, 1, 0⟩, ⟨9, 10, 1, 0, 2, 0, 1, 1, 0⟩]],
      [⟨9, 7, 0, 0, 0, 0, 0, 0, 1⟩, ⟨9, 7, 1, 0, 1, 0, 0, 0, 1⟩, ⟨9, 7, 0, 0, 0, 0, 1, 1, 1⟩, ⟨9, 7, 1, 0, 1, 0, 1, 1, 1⟩]⟩,
    ⟨1, 1, 7, 13,
      [[⟨9, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨9, 0, 1, 0, 1, 0, 0, 0, 0⟩, ⟨9, 0, 0, 0, 0, 0, 1, 1, 0⟩, ⟨9, 0, 1, 0, 1, 0, 1, 1, 0⟩], [⟨9, 6, 0, 0, 0, 0, 0, 0, 0⟩, ⟨9, 6, 1, 0, 1, 0, 0, 0, 0⟩, ⟨9, 6, 0, 0, 0, 0, 1, 1, 0⟩, ⟨9, 6, 1, 0, 1, 0, 1, 1, 0⟩], [⟨9, 8, 0, 0, 0, 0, 0, 0, 0⟩, ⟨9, 8, 1, 0, 1, 0, 0, 0, 0⟩, ⟨9, 8, 0, 0, 0, 0, 1, 1, 0⟩, ⟨9, 8, 1, 0, 1, 0, 1, 1, 0⟩], [⟨9, 15, 0, 0, 0, 0, 0, 0, 0⟩, ⟨9, 15, 1, 0, 1, 0, 0, 0, 0⟩, ⟨9, 15, 0, 0, 0, 0, 1, 1, 0⟩, ⟨9, 15, 1, 0, 1, 0, 1, 1, 0⟩], [⟨9, 18, 0, 0, 0, 0, 0, 0, 0⟩, ⟨9, 18, 1, 0, 1, 0, 0, 0, 0⟩, ⟨9, 18, 0, 0, 0, 0, 1, 1, 0⟩, ⟨9, 18, 1, 0, 1, 0, 1, 1, 0⟩]],
      [⟨9, 0, 0, 0, 0, 0, 0, 0, 1⟩, ⟨9, 0, 1, 0, 1, 0, 0, 0, 1⟩, ⟨9, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨9, 0, 1, 0, 1, 0, 1, 1, 1⟩]⟩,
    ⟨1, 1, 8, 12,
      [[⟨9, 2, 0, 0, 0, 0, 0, 0, 0⟩, ⟨9, 2, 1, 0, 1, 0, 0, 0, 0⟩, ⟨9, 2, 0, 0, 0, 0, 1, 1, 0⟩, ⟨9, 2, 1, 0, 1, 0, 1, 1, 0⟩], [⟨9, 7, 0, 0, 0, 0, 0, 0, 0⟩, ⟨9, 7, 1, 0, 1, 0, 0, 0, 0⟩, ⟨9, 7, 0, 0, 0, 0, 1, 1, 0⟩, ⟨9, 7, 1, 0, 1, 0, 1, 1, 0⟩], [⟨9, 9, 0, 0, 0, 0, 0, 0, 0⟩, ⟨9, 9, 1, 0, 1, 0, 0, 0, 0⟩, ⟨9, 9, 0, 0, 0, 0, 1, 1, 0⟩, ⟨9, 9, 1, 0, 1, 0, 1, 1, 0⟩], [⟨9, 16, 0, 0, 0, 0, 0, 0, 0⟩, ⟨9, 16, 1, 0, 1, 0, 0, 0, 0⟩, ⟨9, 16, 0, 0, 0, 0, 1, 1, 0⟩, ⟨9, 16, 1, 0, 1, 0, 1, 1, 0⟩], [⟨9, 18, 0, 0, 0, 0, 0, 0, 0⟩, ⟨9, 18, 1, 0, 1, 0, 0, 0, 0⟩, ⟨9, 18, 0, 0, 0, 0, 1, 1, 0⟩, ⟨9, 18, 1, 0, 1, 0, 1, 1, 0⟩]],
      [⟨9, 2, 0, 0, 0, 0, 0, 0, 2⟩, ⟨9, 2, 1, 0, 1, 0, 0, 0, 2⟩, ⟨9, 2, 0, 0, 0, 0, 1, 1, 2⟩, ⟨9, 2, 1, 0, 1, 0, 1, 1, 2⟩]⟩,
    ⟨1, 1, 9, 12,
      [[⟨9, 8, 0, 0, 0, 0, 0, 0, 0⟩, ⟨9, 8, 1, 0, 1, 0, 0, 0, 0⟩, ⟨9, 8, 0, 0, 0, 0, 1, 1, 0⟩, ⟨9, 8, 1, 0, 1, 0, 1, 1, 0⟩], [⟨9, 16, 0, 0, 0, 0, 0, 0, 0⟩, ⟨9, 16, 1, 0, 1, 0, 0, 0, 0⟩, ⟨9, 16, 0, 0, 0, 0, 1, 1, 0⟩, ⟨9, 16, 1, 0, 1, 0, 1, 1, 0⟩], [⟨9, 18, 0, 0, 0, 0, 0, 0, 0⟩, ⟨9, 18, 1, 0, 1, 0, 0, 0, 0⟩, ⟨9, 18, 0, 0, 0, 0, 1, 1, 0⟩, ⟨9, 18, 1, 0, 1, 0, 1, 1, 0⟩], [⟨9, 5, 0, 0, 1, 0, 0, 0, 0⟩, ⟨9, 5, 1, 0, 2, 0, 0, 0, 0⟩, ⟨9, 5, 0, 0, 1, 0, 1, 1, 0⟩, ⟨9, 5, 1, 0, 2, 0, 1, 1, 0⟩], [⟨9, 11, 0, 0, 1, 0, 0, 0, 0⟩, ⟨9, 11, 1, 0, 2, 0, 0, 0, 0⟩, ⟨9, 11, 0, 0, 1, 0, 1, 1, 0⟩, ⟨9, 11, 1, 0, 2, 0, 1, 1, 0⟩]],
      [⟨9, 16, 0, 0, 0, 0, 0, 0, 1⟩, ⟨9, 16, 1, 0, 1, 0, 0, 0, 1⟩, ⟨9, 16, 0, 0, 0, 0, 1, 1, 1⟩, ⟨9, 16, 1, 0, 1, 0, 1, 1, 1⟩]⟩,
    ⟨1, 1, 10, 9,
      [[⟨4, 6, 0, 0, 0, 0, 0, 0, 0⟩, ⟨9, 6, 1, 0, 0, 0, 0, 0, 0⟩, ⟨4, 6, 0, 1, 1, 0, 0, 0, 0⟩, ⟨9, 6, 1, 0, 0, 0, 1, 1, 0⟩], [⟨4, 18, 0, 0, 0, 0, 0, 0, 0⟩, ⟨9, 18, 1, 0, 0, 0, 0, 0, 0⟩, ⟨4, 18, 0, 1, 1, 0, 0, 0, 0⟩, ⟨9, 18, 1, 0, 0, 0, 1, 1, 0⟩], [⟨9, 3, 0, 0, 0, 0, 0, 0, 0⟩, ⟨9, 3, 1, 0, 1, 0, 0, 0, 0⟩, ⟨9, 3, 0, 0, 0, 0, 1, 1, 0⟩, ⟨9, 3, 1, 0, 1, 0, 1, 1, 0⟩], [⟨9, 11, 0, 0, 0, 0, 0, 0, 0⟩, ⟨9, 11, 1, 0, 1, 0, 0, 0, 0⟩, ⟨9, 11, 0, 0, 0, 0, 1, 1, 0⟩, ⟨9, 11, 1, 0, 1, 0, 1, 1, 0⟩], [⟨9, 17, 0, 0, 0, 0, 0, 0, 0⟩, ⟨9, 17, 1, 0, 1, 0, 0, 0, 0⟩, ⟨9, 17, 0, 0, 0, 0, 1, 1, 0⟩, ⟨9, 17, 1, 0, 1, 0, 1, 1, 0⟩]],
      [⟨4, 18, 0, 0, 0, 0, 0, 0, 4⟩, ⟨9, 18, 1, 0, 0, 0, 0, 0, 4⟩, ⟨4, 18, 0, 1, 1, 0, 0, 0, 4⟩, ⟨9, 18, 1, 0, 0, 0, 1, 1, 4⟩]⟩,
    ⟨1, 1, 11, 8,
      [[⟨4, 9, 0, 0, 0, 0, 0, 0, 0⟩, ⟨9, 9, 1, 0, 0, 0, 0, 0, 0⟩, ⟨4, 9, 0, 1, 1, 0, 0, 0, 0⟩, ⟨9, 9, 1, 0, 0, 0, 1, 1, 0⟩], [⟨4, 18, 0, 0, 0, 0, 0, 0, 0⟩, ⟨9, 18, 1, 0, 0, 0, 0, 0, 0⟩, ⟨4, 18, 0, 1, 1, 0, 0, 0, 0⟩, ⟨9, 18, 1, 0, 0, 0, 1, 1, 0⟩], [⟨9, 4, 0, 0, 0, 0, 0, 0, 0⟩, ⟨9, 4, 1, 0, 1, 0, 0, 0, 0⟩, ⟨9, 4, 0, 0, 0, 0, 1, 1, 0⟩, ⟨9, 4, 1, 0, 1, 0, 1, 1, 0⟩], [⟨9, 10, 0, 0, 0, 0, 0, 0, 0⟩, ⟨9, 10, 1, 0, 1, 0, 0, 0, 0⟩, ⟨9, 10, 0, 0, 0, 0, 1, 1, 0⟩, ⟨9, 10, 1, 0, 1, 0, 1, 1, 0⟩], [⟨9, 17, 0, 0, 0, 0, 0, 0, 0⟩, ⟨9, 17, 1, 0, 1, 0, 0, 0, 0⟩, ⟨9, 17, 0, 0, 0, 0, 1, 1, 0⟩, ⟨9, 17, 1, 0, 1, 0, 1, 1, 0⟩]],
      [⟨4, 9, 0, 0, 0, 0, 0, 0, 4⟩, ⟨9, 9, 1, 0, 0, 0, 0, 0, 4⟩, ⟨4, 9, 0, 1, 1, 0, 0, 0, 4⟩, ⟨9, 9, 1, 0, 0, 0, 1, 1, 4⟩]⟩,
    ⟨1, 1, 12, 10,
      [[⟨9, 2, 0, 0, 0, 0, 0, 0, 0⟩, ⟨9, 2, 1, 0, 1, 0, 0, 0, 0⟩, ⟨9, 2, 0, 0, 0, 0, 1, 1, 0⟩, ⟨9, 2, 1, 0, 1, 0, 1, 1, 0⟩], [⟨9, 3, 0, 0, 0, 0, 0, 0, 0⟩, ⟨9, 3, 1, 0, 1, 0, 0, 0, 0⟩, ⟨9, 3, 0, 0, 0, 0, 1, 1, 0⟩, ⟨9, 3, 1, 0, 1, 0, 1, 1, 0⟩], [⟨9, 16, 0, 0, 0, 0, 0, 0, 0⟩, ⟨9, 16, 1, 0, 1, 0, 0, 0, 0⟩, ⟨9, 16, 0, 0, 0, 0, 1, 1, 0⟩, ⟨9, 16, 1, 0, 1, 0, 1, 1, 0⟩], [⟨9, 17, 0, 0, 0, 0, 0, 0, 0⟩, ⟨9, 17, 1, 0, 1, 0, 0, 0, 0⟩, ⟨9, 17, 0, 0, 0, 0, 1, 1, 0⟩, ⟨9, 17, 1, 0, 1, 0, 1, 1, 0⟩]],
      [⟨9, 17, 0, 0, 0, 0, 0, 0, 2⟩, ⟨9, 17, 1, 0, 1, 0, 0, 0, 2⟩, ⟨9, 17, 0, 0, 0, 0, 1, 1, 2⟩, ⟨9, 17, 1, 0, 1, 0, 1, 1, 2⟩]⟩,
    ⟨1, 1, 13, 10,
      [[⟨3, 15, 0, 0, 0, 0, 0, 0, 0⟩, ⟨3, 15, 1, 0, 1, 0, 0, 0, 0⟩, ⟨9, 15, 0, 0, 0, 0, 1, 0, 0⟩, ⟨9, 15, 1, 0, 1, 0, 1, 0, 0⟩], [⟨9, 16, 0, 0, 0, 0, 0, 0, 0⟩, ⟨9, 16, 1, 0, 1, 0, 0, 0, 0⟩, ⟨9, 16, 0, 0, 0, 0, 1, 1, 0⟩, ⟨9, 16, 1, 0, 1, 0, 1, 1, 0⟩], [⟨3, 1, 0, 0, 1, 0, 0, 0, 0⟩, ⟨3, 1, 1, 0, 2, 0, 0, 0, 0⟩, ⟨9, 1, 0, 0, 1, 0, 1, 0, 0⟩, ⟨9, 1, 1, 0, 2, 0, 1, 0, 0⟩], [⟨9, 5, 0, 0, 1, 0, 0, 0, 0⟩, ⟨9, 5, 1, 0, 2, 0, 0, 0, 0⟩, ⟨9, 5, 0, 0, 1, 0, 1, 1, 0⟩, ⟨9, 5, 1, 0, 2, 0, 1, 1, 0⟩]],
      [⟨3, 15, 0, 0, 0, 0, 0, 0, 2⟩, ⟨3, 15, 1, 0, 1, 0, 0, 0, 2⟩, ⟨9, 15, 0, 0, 0, 0, 1, 0, 2⟩, ⟨9, 15, 1, 0, 1, 0, 1, 0, 2⟩]⟩,
    ⟨1, 1, 14, 8,
      [[⟨3, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨3, 0, 1, 0, 1, 0, 0, 0, 0⟩, ⟨9, 0, 0, 0, 0, 0, 1, 0, 0⟩, ⟨9, 0, 1, 0, 1, 0, 1, 0, 0⟩], [⟨3, 15, 0, 0, 0, 0, 0, 0, 0⟩, ⟨3, 15, 1, 0, 1, 0, 0, 0, 0⟩, ⟨9, 15, 0, 0, 0, 0, 1, 0, 0⟩, ⟨9, 15, 1, 0, 1, 0, 1, 0, 0⟩], [⟨9, 4, 0, 0, 0, 0, 0, 0, 0⟩, ⟨9, 4, 1, 0, 1, 0, 0, 0, 0⟩, ⟨9, 4, 0, 0, 0, 0, 1, 1, 0⟩, ⟨9, 4, 1, 0, 1, 0, 1, 1, 0⟩], [⟨9, 17, 0, 0, 0, 0, 0, 0, 0⟩, ⟨9, 17, 1, 0, 1, 0, 0, 0, 0⟩, ⟨9, 17, 0, 0, 0, 0, 1, 1, 0⟩, ⟨9, 17, 1, 0, 1, 0, 1, 1, 0⟩]],
      [⟨3, 0, 0, 0, 0, 0, 0, 0, 3⟩, ⟨3, 0, 1, 0, 1, 0, 0, 0, 3⟩, ⟨9, 0, 0, 0, 0, 0, 1, 0, 3⟩, ⟨9, 0, 1, 0, 1, 0, 1, 0, 3⟩]⟩,
    ⟨1, 1, 15, 14,
      [[⟨9, 6, 0, 0, 0, 0, 0, 0, 0⟩, ⟨9, 6, 1, 0, 1, 0, 0, 0, 0⟩, ⟨9, 6, 0, 0, 0, 0, 1, 1, 0⟩, ⟨9, 6, 1, 0, 1, 0, 1, 1, 0⟩], [⟨9, 7, 0, 0, 0, 0, 0, 0, 0⟩, ⟨9, 7, 1, 0, 1, 0, 0, 0, 0⟩, ⟨9, 7, 0, 0, 0, 0, 1, 1, 0⟩, ⟨9, 7, 1, 0, 1, 0, 1, 1, 0⟩], [⟨9, 13, 0, 0, 0, 0, 0, 1, 0⟩, ⟨9, 13, 1, 0, 1, 0, 0, 1, 0⟩, ⟨9, 13, 0, 0, 0, 0, 1, 2, 0⟩, ⟨9, 13, 1, 0, 1, 0, 1, 2, 0⟩], [⟨9, 14, 0, 0, 0, 0, 0, 1, 0⟩, ⟨9, 14, 1, 0, 1, 0, 0, 1, 0⟩, ⟨9, 14, 0, 0, 0, 0, 1, 2, 0⟩, ⟨9, 14, 1, 0, 1, 0, 1, 2, 0⟩]],
      [⟨9, 7, 0, 0, 0, 0, 0, 0, 3⟩, ⟨9, 7, 1, 0, 1, 0, 0, 0, 3⟩, ⟨9, 7, 0, 0, 0, 0, 1, 1, 3⟩, ⟨9, 7, 1, 0, 1, 0, 1, 1, 3⟩]⟩,
    ⟨1, 1, 16, 11,
      [[⟨9, 8, 0, 0, 0, 0, 0, 0, 0⟩, ⟨9, 8, 1, 0, 1, 0, 0, 0, 0⟩, ⟨9, 8, 0, 0, 0, 0, 1, 1, 0⟩, ⟨9, 8, 1, 0, 1, 0, 1, 1, 0⟩], [⟨9, 9, 0, 0, 0, 0, 0, 0, 0⟩, ⟨9, 9, 1, 0, 1, 0, 0, 0, 0⟩, ⟨9, 9, 0, 0, 0, 0, 1, 1, 0⟩, ⟨9, 9, 1, 0, 1, 0, 1, 1, 0⟩], [⟨9, 12, 0, 0, 0, 0, 0, 0, 0⟩, ⟨9, 12, 1, 0, 1, 0, 0, 0, 0⟩, ⟨9, 12, 0, 0, 0, 0, 1, 1, 0⟩, ⟨9, 12, 1, 0, 1, 0, 1, 1, 0⟩], [⟨9, 13, 0, 0, 0, 0, 0, 0, 0⟩, ⟨9, 13, 1, 0, 1, 0, 0, 0, 0⟩, ⟨9, 13, 0, 0, 0, 0, 1, 1, 0⟩, ⟨9, 13, 1, 0, 1, 0, 1, 1, 0⟩]],
      [⟨9, 12, 0, 0, 0, 0, 0, 0, 2⟩, ⟨9, 12, 1, 0, 1, 0, 0, 0, 2⟩, ⟨9, 12, 0, 0, 0, 0, 1, 1, 2⟩, ⟨9, 12, 1, 0, 1, 0, 1, 1, 2⟩]⟩,
    ⟨1, 1, 17, 9,
      [[⟨9, 10, 0, 0, 0, 0, 0, 0, 0⟩, ⟨9, 10, 1, 0, 1, 0, 0, 0, 0⟩, ⟨9, 10, 0, 0, 0, 0, 1, 1, 0⟩, ⟨9, 10, 1, 0, 1, 0, 1, 1, 0⟩], [⟨9, 11, 0, 0, 0, 0, 0, 0, 0⟩, ⟨9, 11, 1, 0, 1, 0, 0, 0, 0⟩, ⟨9, 11, 0, 0, 0, 0, 1, 1, 0⟩, ⟨9, 11, 1, 0, 1, 0, 1, 1, 0⟩], [⟨9, 12, 0, 0, 0, 0, 0, 0, 0⟩, ⟨9, 12, 1, 0, 1, 0, 0, 0, 0⟩, ⟨9, 12, 0, 0, 0, 0, 1, 1, 0⟩, ⟨9, 12, 1, 0, 1, 0, 1, 1, 0⟩], [⟨9, 14, 0, 0, 0, 0, 0, 0, 0⟩, ⟨9, 14, 1, 0, 1, 0, 0, 0, 0⟩, ⟨9, 14, 0, 0, 0, 0, 1, 1, 0⟩, ⟨9, 14, 1, 0, 1, 0, 1, 1, 0⟩]],
      [⟨9, 11, 0, 0, 0, 0, 0, 0, 4⟩, ⟨9, 11, 1, 0, 1, 0, 0, 0, 4⟩, ⟨9, 11, 0, 0, 0, 0, 1, 1, 4⟩, ⟨9, 11, 1, 0, 1, 0, 1, 1, 4⟩]⟩,
    ⟨1, 1, 18, 13,
      [[⟨9, 6, 0, 0, 0, 0, 0, 0, 0⟩, ⟨9, 6, 1, 0, 1, 0, 0, 0, 0⟩, ⟨9, 6, 0, 0, 0, 0, 1, 1, 0⟩, ⟨9, 6, 1, 0, 1, 0, 1, 1, 0⟩], [⟨9, 7, 0, 0, 0, 0, 0, 0, 0⟩, ⟨9, 7, 1, 0, 1, 0, 0, 0, 0⟩, ⟨9, 7, 0, 0, 0, 0, 1, 1, 0⟩, ⟨9, 7, 1, 0, 1, 0, 1, 1, 0⟩], [⟨9, 8, 0, 0, 0, 0, 0, 0, 0⟩, ⟨9, 8, 1, 0, 1, 0, 0, 0, 0⟩, ⟨9, 8, 0, 0, 0, 0, 1, 1, 0⟩, ⟨9, 8, 1, 0, 1, 0, 1, 1, 0⟩], [⟨9, 9, 0, 0, 0, 0, 0, 0, 0⟩, ⟨9, 9, 1, 0, 1, 0, 0, 0, 0⟩, ⟨9, 9, 0, 0, 0, 0, 1, 1, 0⟩, ⟨9, 9, 1, 0, 1, 0, 1, 1, 0⟩], [⟨9, 10, 0, 0, 1, 0, 0, 0, 0⟩, ⟨9, 10, 1, 0, 2, 0, 0, 0, 0⟩, ⟨9, 10, 0, 0, 1, 0, 1, 1, 0⟩, ⟨9, 10, 1, 0, 2, 0, 1, 1, 0⟩], [⟨9, 11, 0, 0, 1, 0, 0, 0, 0⟩, ⟨9, 11, 1, 0, 2, 0, 0, 0, 0⟩, ⟨9, 11, 0, 0, 1, 0, 1, 1, 0⟩, ⟨9, 11, 1, 0, 2, 0, 1, 1, 0⟩]],
      [⟨9, 8, 0, 0, 0, 0, 0, 0, 4⟩, ⟨9, 8, 1, 0, 1, 0, 0, 0, 4⟩, ⟨9, 8, 0, 0, 0, 0, 1, 1, 4⟩, ⟨9, 8, 1, 0, 1, 0, 1, 1, 4⟩]⟩]⟩,
  ⟨2, 0, 1, -1, 1, [(1, 1, 1), (-1, 0, 1)], 1, 1, 1, 1, -1, 0, 1, 1,
   [⟨-1, 2, 0, 12,
      [[⟨10, 2, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 2, 1, 0, 1, 0, 0, 0, 0⟩, ⟨10, 2, 0, 0, 0, 0, 1, 1, 0⟩, ⟨10, 2, 1, 0, 1, 0, 1, 1, 0⟩], [⟨10, 7, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 7, 1, 0, 1, 0, 0, 0, 0⟩, ⟨10, 7, 0, 0, 0, 0, 1, 1, 0⟩, ⟨10, 7, 1, 0, 1, 0, 1, 1, 0⟩], [⟨10, 4, 0, 0, 1, 0, 0, 0, 0⟩, ⟨10, 4, 1, 0, 2, 0, 0, 0, 0⟩, ⟨10, 4, 0, 0, 1, 0, 1, 1, 0⟩, ⟨10, 4, 1, 0, 2, 0, 1, 1, 0⟩], [⟨10, 14, 0, 0, 1, 0, 0, 0, 0⟩, ⟨10, 14, 1, 0, 2, 0, 0, 0, 0⟩, ⟨10, 14, 0, 0, 1, 0, 1, 1, 0⟩, ⟨10, 14, 1, 0, 2, 0, 1, 1, 0⟩]],
      [⟨10, 2, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 2, 1, 0, 1, 0, 0, 0, 0⟩, ⟨10, 2, 0, 0, 0, 0, 1, 1, 0⟩, ⟨10, 2, 1, 0, 1, 0, 1, 1, 0⟩]⟩,
    ⟨-1, 2, 1, 12,
      [[⟨5, 6, 0, 0, 1, 0, 0, 0, 0⟩, ⟨10, 6, 1, 0, 0, 0, 0, 1, 0⟩, ⟨5, 6, 0, 1, 2, 0, 0, 0, 0⟩, ⟨10, 6, 1, 0, 0, 0, 1, 2, 0⟩], [⟨10, 13, 0, 0, 0, 0, 0, 1, 0⟩, ⟨10, 13, 1, 0, 1, 0, 0, 1, 0⟩, ⟨10, 13, 0, 0, 0, 0, 1, 2, 0⟩, ⟨10, 13, 1, 0, 1, 0, 1, 2, 0⟩], [⟨10, 3, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 3, 1, 0, 1, 0, 0, 0, 0⟩, ⟨10, 3, 0, 0, 0, 0, 1, 1, 0⟩, ⟨10, 3, 1, 0, 1, 0, 1, 1, 0⟩], [⟨10, 5, 0, 0, 1, 0, 0, 0, 0⟩, ⟨10, 5, 1, 0, 2, 0, 0, 0, 0⟩, ⟨10, 5, 0, 0, 1, 0, 1, 1, 0⟩, ⟨10, 5, 1, 0, 2, 0, 1, 1, 0⟩]],
      [⟨5, 6, 0, 0, 1, 0, 0, 0, 3⟩, ⟨10, 6, 1, 0, 0, 0, 0, 1, 3⟩, ⟨5, 6, 0, 1, 2, 0, 0, 0, 3⟩, ⟨10, 6, 1, 0, 0, 0, 1, 2, 3⟩]⟩,
    ⟨-1, 2, 2, 11,
      [[⟨10, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 0, 1, 0, 1, 0, 0, 0, 0⟩, ⟨10, 0, 0, 0, 0, 0, 1, 1, 0⟩, ⟨10, 0, 1, 0, 1, 0, 1, 1, 0⟩], [⟨10, 3, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 3, 1, 0, 1, 0, 0, 0, 0⟩, ⟨10, 3, 0, 0, 0, 0, 1, 1, 0⟩, ⟨10, 3, 1, 0, 1, 0, 1, 1, 0⟩], [⟨10, 8, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 8, 1, 0, 1, 0, 0, 0, 0⟩, ⟨10, 8, 0, 0, 0, 0, 1, 1, 0⟩, ⟨10, 8, 1, 0, 1, 0, 1, 1, 0⟩], [⟨10, 12, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 12, 1, 0, 1, 0, 0, 0, 0⟩, ⟨10, 12, 0, 0, 0, 0, 1, 1, 0⟩, ⟨10, 12, 1, 0, 1, 0, 1, 1, 0⟩]],
      [⟨10, 8, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 8, 1, 0, 1, 0, 0, 0, 0⟩, ⟨10, 8, 0, 0, 0, 0, 1, 1, 0⟩, ⟨10, 8, 1, 0, 1, 0, 1, 1, 0⟩]⟩,
    ⟨-1, 2, 3, 11,
      [[⟨10, 1, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 1, 1, 0, 1, 0, 0, 0, 0⟩, ⟨10, 1, 0, 0, 0, 0, 1, 1, 0⟩, ⟨10, 1, 1, 0, 1, 0, 1, 1, 0⟩], [⟨10, 2, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 2, 1, 0, 1, 0, 0, 0, 0⟩, ⟨10, 2, 0, 0, 0, 0, 1, 1, 0⟩, ⟨10, 2, 1, 0, 1, 0, 1, 1, 0⟩], [⟨10, 10, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 10, 1, 0, 1, 0, 0, 0, 0⟩, ⟨10, 10, 0, 0, 0, 0, 1, 1, 0⟩, ⟨10, 10, 1, 0, 1, 0, 1, 1, 0⟩], [⟨10, 12, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 12, 1, 0, 1, 0, 0, 0, 0⟩, ⟨10, 12, 0, 0, 0, 0, 1, 1, 0⟩, ⟨10, 12, 1, 0, 1, 0, 1, 1, 0⟩]],
      [⟨10, 10, 0, 0, 0, 0, 0, 0, 2⟩, ⟨10, 10, 1, 0, 1, 0, 0, 0, 2⟩, ⟨10, 10, 0, 0, 0, 0, 1, 1, 2⟩, ⟨10, 10, 1, 0, 1, 0, 1, 1, 2⟩]⟩,
    ⟨-1, 2, 4, 8,
      [[⟨5, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨5, 0, 0, 1, 1, 0, 0, 0, 0⟩, ⟨10, 0, 1, 0, 0, 0, 1, 1, 0⟩], [⟨10, 5, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 5, 1, 0, 1, 0, 0, 0, 0⟩, ⟨10, 5, 0, 0, 0, 0, 1, 1, 0⟩, ⟨10, 5, 1, 0, 1, 0, 1, 1, 0⟩], [⟨10, 11, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 11, 1, 0, 1, 0, 0, 0, 0⟩, ⟨10, 11, 0, 0, 0, 0, 1, 1, 0⟩, ⟨10, 11, 1, 0, 1, 0, 1, 1, 0⟩], [⟨10, 14, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 14, 1, 0, 1, 0, 0, 0, 0⟩, ⟨10, 14, 0, 0, 0, 0, 1, 1, 0⟩, ⟨10, 14, 1, 0, 1, 0, 1, 1, 0⟩]],
      [⟨5, 0, 0, 0, 0, 0, 0, 0, 2⟩, ⟨10, 0, 1, 0, 0, 0, 0, 0, 2⟩, ⟨5, 0, 0, 1, 1, 0, 0, 0, 2⟩, ⟨10, 0, 1, 0, 0, 0, 1, 1, 2⟩]⟩,
    ⟨-1, 2, 5, 8,
      [[⟨5, 9, 0, 0, 1, 0, 0, 0, 0⟩, ⟨10, 9, 1, 0, 0, 0, 0, 1, 0⟩, ⟨5, 9, 0, 1, 2, 0, 0, 0, 0⟩, ⟨10, 9, 1, 0, 0, 0, 1, 2, 0⟩], [⟨5, 13, 0, 0, 1, 0, 0, 0, 0⟩, ⟨10, 13, 1, 0, 0, 0, 0, 1, 0⟩, ⟨5, 13, 0, 1, 2, 0, 0, 0, 0⟩, ⟨10, 13, 1, 0, 0, 0, 1, 2, 0⟩], [⟨5, 1, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 1, 1, 0, 0, 0, 0, 0, 0⟩, ⟨5, 1, 0, 1, 1, 0, 0, 0, 0⟩, ⟨10, 1, 1, 0, 0, 0, 1, 1, 0⟩], [⟨10, 4, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 4, 1, 0, 1, 0, 0, 0, 0⟩, ⟨10, 4, 0, 0, 0, 0, 1, 1, 0⟩, ⟨10, 4, 1, 0, 1, 0, 1, 1, 0⟩]],
      [⟨5, 1, 0, 0, 0, 0, 0, 0, 3⟩, ⟨10, 1, 1, 0, 0, 0, 0, 0, 3⟩, ⟨5, 1, 0, 1, 1, 0, 0, 0, 3⟩, ⟨10, 1, 1, 0, 0, 0, 1, 1, 3⟩]⟩,
    ⟨-1, 2, 6, 11,
      [[⟨10, 7, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 7, 1, 0, 1, 0, 0, 0, 0⟩, ⟨10, 7, 0, 0, 0, 0, 1, 1, 0⟩, ⟨10, 7, 1, 0, 1, 0, 1, 1, 0⟩], [⟨10, 15, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 15, 1, 0, 1, 0, 0, 0, 0⟩, ⟨10, 15, 0, 0, 0, 0, 1, 1, 0⟩, ⟨10, 15, 1, 0, 1, 0, 1, 1, 0⟩], [⟨10, 18, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 18, 1, 0, 1, 0, 0, 0, 0⟩, ⟨10, 18, 0, 0, 0, 0, 1, 1, 0⟩, ⟨10, 18, 1, 0, 1, 0, 1, 1, 0⟩], [⟨4, 1, 0, 0, 1, 0, 0, 0, 0⟩, ⟨4, 1, 1, 0, 2, 0, 0, 0, 0⟩, ⟨10, 1, 0, 0, 1, 0, 1, 0, 0⟩, ⟨10, 1, 1, 0, 2, 0, 1, 0, 0⟩], [⟨4, 10, 0, 0, 1, 0, 0, 0, 0⟩, ⟨4, 10, 1, 0, 2, 0, 0, 0, 0⟩, ⟨10, 10, 0, 0, 1, 0, 1, 0, 0⟩, ⟨10, 10, 1, 0, 2, 0, 1, 0, 0⟩]],
      [⟨10, 18, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 18, 1, 0, 1, 0, 0, 0, 0⟩, ⟨10, 18, 0, 0, 0, 0, 1, 1, 0⟩, ⟨10, 18, 1, 0, 1, 0, 1, 1, 0⟩]⟩,
    ⟨-1, 2, 7, 11,
      [[⟨10, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 0, 1, 0, 1, 0, 0, 0, 0⟩, ⟨10, 0, 0, 0, 0, 0, 1, 1, 0⟩, ⟨10, 0, 1, 0, 1, 0, 1, 1, 0⟩], [⟨10, 6, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 6, 1, 0, 1, 0, 0, 0, 0⟩, ⟨10, 6, 0, 0, 0, 0, 1, 1, 0⟩, ⟨10, 6, 1, 0, 1, 0, 1, 1, 0⟩], [⟨10, 8, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 8, 1, 0, 1, 0, 0, 0, 0⟩, ⟨10, 8, 0, 0, 0, 0, 1, 1, 0⟩, ⟨10, 8, 1, 0, 1, 0, 1, 1, 0⟩], [⟨10, 15, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 15, 1, 0, 1, 0, 0, 0, 0⟩, ⟨10, 15, 0, 0, 0, 0, 1, 1, 0⟩, ⟨10, 15, 1, 0, 1, 0, 1, 1, 0⟩], [⟨10, 18, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 18, 1, 0, 1, 0, 0, 0, 0⟩, ⟨10, 18, 0, 0, 0, 0, 1, 1, 0⟩, ⟨10, 18, 1, 0, 1, 0, 1, 1, 0⟩]],
      [⟨10, 8, 0, 0, 0, 0, 0, 0, 1⟩, ⟨10, 8, 1, 0, 1, 0, 0, 0, 1⟩, ⟨10, 8, 0, 0, 0, 0, 1, 1, 1⟩, ⟨10, 8, 1, 0, 1, 0, 1, 1, 1⟩]⟩,
    ⟨-1, 2, 8, 10,
      [[⟨10, 2, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 2, 1, 0, 1, 0, 0, 0, 0⟩, ⟨10, 2, 0, 0, 0, 0, 1, 1, 0⟩, ⟨10, 2, 1, 0, 1, 0, 1, 1, 0⟩], [⟨10, 7, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 7, 1, 0, 1, 0, 0, 0, 0⟩, ⟨10, 7, 0, 0, 0, 0, 1, 1, 0⟩, ⟨10, 7, 1, 0, 1, 0, 1, 1, 0⟩], [⟨10, 9, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 9, 1, 0, 1, 0, 0, 0, 0⟩, ⟨10, 9, 0, 0, 0, 0, 1, 1, 0⟩, ⟨10, 9, 1, 0, 1, 0, 1, 1, 0⟩], [⟨10, 16, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 16, 1, 0, 1, 0, 0, 0, 0⟩, ⟨10, 16, 0, 0, 0, 0, 1, 1, 0⟩, ⟨10, 16, 1, 0, 1, 0, 1, 1, 0⟩], [⟨10, 18, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 18, 1, 0, 1, 0, 0, 0, 0⟩, ⟨10, 18, 0, 0, 0, 0, 1, 1, 0⟩, ⟨10, 18, 1, 0, 1, 0, 1, 1, 0⟩]],
      [⟨10, 9, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 9, 1, 0, 1, 0, 0, 0, 0⟩, ⟨10, 9, 0, 0, 0, 0, 1, 1, 0⟩, ⟨10, 9, 1, 0, 1, 0, 1, 1, 0⟩]⟩,
    ⟨-1, 2, 9, 9,
      [[⟨10, 8, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 8, 1, 0, 1, 0, 0, 0, 0⟩, ⟨10, 8, 0, 0, 0, 0, 1, 1, 0⟩, ⟨10, 8, 1, 0, 1, 0, 1, 1, 0⟩], [⟨10, 16, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 16, 1, 0, 1, 0, 0, 0, 0⟩, ⟨10, 16, 0, 0, 0, 0, 1, 1, 0⟩, ⟨10, 16, 1, 0, 1, 0, 1, 1, 0⟩], [⟨10, 18, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 18, 1, 0, 1, 0, 0, 0, 0⟩, ⟨10, 18, 0, 0, 0, 0, 1, 1, 0⟩, ⟨10, 18, 1, 0, 1, 0, 1, 1, 0⟩], [⟨4, 5, 0, 0, 1, 0, 0, 0, 0⟩, ⟨4, 5, 1, 0, 2, 0, 0, 0, 0⟩, ⟨10, 5, 0, 0, 1, 0, 1, 0, 0⟩, ⟨10, 5, 1, 0, 2, 0, 1, 0, 0⟩], [⟨4, 11, 0, 0, 1, 0, 0, 0, 0⟩, ⟨4, 11, 1, 0, 2, 0, 0, 0, 0⟩, ⟨10, 11, 0, 0, 1, 0, 1, 0, 0⟩, ⟨10, 11, 1, 0, 2, 0, 1, 0, 0⟩]],
      [⟨4, 5, 0, 0, 1, 0, 0, 0, 0⟩, ⟨4, 5, 1, 0, 2, 0, 0, 0, 0⟩, ⟨10, 5, 0, 0, 1, 0, 1, 0, 0⟩, ⟨10, 5, 1, 0, 2, 0, 1, 0, 0⟩]⟩,
    ⟨-1, 2, 10, 10,
      [[⟨5, 6, 0, 0, 1, 0, 0, 0, 0⟩, ⟨10, 6, 1, 0, 0, 0, 0, 1, 0⟩, ⟨5, 6, 0, 1, 2, 0, 0, 0, 0⟩, ⟨10, 6, 1, 0, 0, 0, 1, 2, 0⟩], [⟨5, 18, 0, 0, 1, 0, 0, 0, 0⟩, ⟨10, 18, 1, 0, 0, 0, 0, 1, 0⟩, ⟨5, 18, 0, 1, 2, 0, 0, 0, 0⟩, ⟨10, 18, 1, 0, 0, 0, 1, 2, 0⟩], [⟨10, 3, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 3, 1, 0, 1, 0, 0, 0, 0⟩, ⟨10, 3, 0, 0, 0, 0, 1, 1, 0⟩, ⟨10, 3, 1, 0, 1, 0, 1, 1, 0⟩], [⟨10, 11, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 11, 1, 0, 1, 0, 0, 0, 0⟩, ⟨10, 11, 0, 0, 0, 0, 1, 1, 0⟩, ⟨10, 11, 1, 0, 1, 0, 1, 1, 0⟩], [⟨10, 17, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 17, 1, 0, 1, 0, 0, 0, 0⟩, ⟨10, 17, 0, 0, 0, 0, 1, 1, 0⟩, ⟨10, 17, 1, 0, 1, 0, 1, 1, 0⟩]],
      [⟨10, 11, 0, 0, 0, 0, 0, 0, 3⟩, ⟨10, 11, 1, 0, 1, 0, 0, 0, 3⟩, ⟨10, 11, 0, 0, 0, 0, 1, 1, 3⟩, ⟨10, 11, 1, 0, 1, 0, 1, 1, 3⟩]⟩,
    ⟨-1, 2, 11, 9,
      [[⟨5, 9, 0, 0, 1, 0, 0, 0, 0⟩, ⟨10, 9, 1, 0, 0, 0, 0, 1, 0⟩, ⟨5, 9, 0, 1, 2, 0, 0, 0, 0⟩, ⟨10, 9, 1, 0, 0, 0, 1, 2, 0⟩], [⟨5, 18, 0, 0, 1, 0, 0, 0, 0⟩, ⟨10, 18, 1, 0, 0, 0, 0, 1, 0⟩, ⟨5, 18, 0, 1, 2, 0, 0, 0, 0⟩, ⟨10, 18, 1, 0, 0, 0, 1, 2, 0⟩], [⟨10, 4, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 4, 1, 0, 1, 0, 0, 0, 0⟩, ⟨10, 4, 0, 0, 0, 0, 1, 1, 0⟩, ⟨10, 4, 1, 0, 1, 0, 1, 1, 0⟩], [⟨10, 10, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 10, 1, 0, 1, 0, 0, 0, 0⟩, ⟨10, 10, 0, 0, 0, 0, 1, 1, 0⟩, ⟨10, 10, 1, 0, 1, 0, 1, 1, 0⟩], [⟨10, 17, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 17, 1, 0, 1, 0, 0, 0, 0⟩, ⟨10, 17, 0, 0, 0, 0, 1, 1, 0⟩, ⟨10, 17, 1, 0, 1, 0, 1, 1, 0⟩]],
      [⟨10, 4, 0, 0, 0, 0, 0, 0, 2⟩, ⟨10, 4, 1, 0, 1, 0, 0, 0, 2⟩, ⟨10, 4, 0, 0, 0, 0, 1, 1, 2⟩, ⟨10, 4, 1, 0, 1, 0, 1, 1, 2⟩]⟩,
    ⟨-1, 2, 12, 10,
      [[⟨10, 2, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 2, 1, 0, 1, 0, 0, 0, 0⟩, ⟨10, 2, 0, 0, 0, 0, 1, 1, 0⟩, ⟨10, 2, 1, 0, 1, 0, 1, 1, 0⟩], [⟨10, 3, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 3, 1, 0, 1, 0, 0, 0, 0⟩, ⟨10, 3, 0, 0, 0, 0, 1, 1, 0⟩, ⟨10, 3, 1, 0, 1, 0, 1, 1, 0⟩], [⟨10, 16, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 16, 1, 0, 1, 0, 0, 0, 0⟩, ⟨10, 16, 0, 0, 0, 0, 1, 1, 0⟩, ⟨10, 16, 1, 0, 1, 0, 1, 1, 0⟩], [⟨10, 17, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 17, 1, 0, 1, 0, 0, 0, 0⟩, ⟨10, 17, 0, 0, 0, 0, 1, 1, 0⟩, ⟨10, 17, 1, 0, 1, 0, 1, 1, 0⟩]],
      [⟨10, 16, 0, 0, 0, 0, 0, 0, 2⟩, ⟨10, 16, 1, 0, 1, 0, 0, 0, 2⟩, ⟨10, 16, 0, 0, 0, 0, 1, 1, 2⟩, ⟨10, 16, 1, 0, 1, 0, 1, 1, 2⟩]⟩,
    ⟨-1, 2, 13, 8,
      [[⟨5, 15, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 15, 1, 0, 0, 0, 0, 0, 0⟩, ⟨5, 15, 0, 1, 1, 0, 0, 0, 0⟩, ⟨10, 15, 1, 0, 0, 0, 1, 1, 0⟩], [⟨10, 16, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 16, 1, 0, 1, 0, 0, 0, 0⟩, ⟨10, 16, 0, 0, 0, 0, 1, 1, 0⟩, ⟨10, 16, 1, 0, 1, 0, 1, 1, 0⟩], [⟨4, 1, 0, 0, 0, 0, 0, 0, 0⟩, ⟨4, 1, 1, 0, 1, 0, 0, 0, 0⟩, ⟨10, 1, 0, 0, 0, 0, 1, 0, 0⟩, ⟨10, 1, 1, 0, 1, 0, 1, 0, 0⟩], [⟨4, 5, 0, 0, 1, 0, 0, 0, 0⟩, ⟨4, 5, 1, 0, 2, 0, 0, 0, 0⟩, ⟨10, 5, 0, 0, 1, 0, 1, 0, 0⟩, ⟨10, 5, 1, 0, 2, 0, 1, 0, 0⟩]],
      [⟨5, 15, 0, 0, 0, 0, 0, 0, 2⟩, ⟨10, 15, 1, 0, 0, 0, 0, 0, 2⟩, ⟨5, 15, 0, 1, 1, 0, 0, 0, 2⟩, ⟨10, 15, 1, 0, 0, 0, 1, 1, 2⟩]⟩,
    ⟨-1, 2, 14, 8,
      [[⟨5, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨5, 0, 0, 1, 1, 0, 0, 0, 0⟩, ⟨10, 0, 1, 0, 0, 0, 1, 1, 0⟩], [⟨5, 15, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 15, 1, 0, 0, 0, 0, 0, 0⟩, ⟨5, 15, 0, 1, 1, 0, 0, 0, 0⟩, ⟨10, 15, 1, 0, 0, 0, 1, 1, 0⟩], [⟨10, 4, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 4, 1, 0, 1, 0, 0, 0, 0⟩, ⟨10, 4, 0, 0, 0, 0, 1, 1, 0⟩, ⟨10, 4, 1, 0, 1, 0, 1, 1, 0⟩], [⟨10, 17, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 17, 1, 0, 1, 0, 0, 0, 0⟩, ⟨10, 17, 0, 0, 0, 0, 1, 1, 0⟩, ⟨10, 17, 1, 0, 1, 0, 1, 1, 0⟩]],
      [⟨5, 0, 0, 0, 0, 0, 0, 0, 3⟩, ⟨10, 0, 1, 0, 0, 0, 0, 0, 3⟩, ⟨5, 0, 0, 1, 1, 0, 0, 0, 3⟩, ⟨10, 0, 1, 0, 0, 0, 1, 1, 3⟩]⟩,
    ⟨-1, 2, 15, 12,
      [[⟨10, 6, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 6, 1, 0, 1, 0, 0, 0, 0⟩, ⟨10, 6, 0, 0, 0, 0, 1, 1, 0⟩, ⟨10, 6, 1, 0, 1, 0, 1, 1, 0⟩], [⟨10, 7, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 7, 1, 0, 1, 0, 0, 0, 0⟩, ⟨10, 7, 0, 0, 0, 0, 1, 1, 0⟩, ⟨10, 7, 1, 0, 1, 0, 1, 1, 0⟩], [⟨10, 13, 0, 0, 1, 0, 0, 0, 0⟩, ⟨10, 13, 1, 0, 2, 0, 0, 0, 0⟩, ⟨10, 13, 0, 0, 1, 0, 1, 1, 0⟩, ⟨10, 13, 1, 0, 2, 0, 1, 1, 0⟩], [⟨10, 14, 0, 0, 1, 0, 0, 0, 0⟩, ⟨10, 14, 1, 0, 2, 0, 0, 0, 0⟩, ⟨10, 14, 0, 0, 1, 0, 1, 1, 0⟩, ⟨10, 14, 1, 0, 2, 0, 1, 1, 0⟩]],
      [⟨10, 6, 0, 0, 0, 0, 0, 0, 1⟩, ⟨10, 6, 1, 0, 1, 0, 0, 0, 1⟩, ⟨10, 6, 0, 0, 0, 0, 1, 1, 1⟩, ⟨10, 6, 1, 0, 1, 0, 1, 1, 1⟩]⟩,
    ⟨-1, 2, 16, 9,
      [[⟨10, 8, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 8, 1, 0, 1, 0, 0, 0, 0⟩, ⟨10, 8, 0, 0, 0, 0, 1, 1, 0⟩, ⟨10, 8, 1, 0, 1, 0, 1, 1, 0⟩], [⟨10, 9, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 9, 1, 0, 1, 0, 0, 0, 0⟩, ⟨10, 9, 0, 0, 0, 0, 1, 1, 0⟩, ⟨10, 9, 1, 0, 1, 0, 1, 1, 0⟩], [⟨10, 12, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 12, 1, 0, 1, 0, 0, 0, 0⟩, ⟨10, 12, 0, 0, 0, 0, 1, 1, 0⟩, ⟨10, 12, 1, 0, 1, 0, 1, 1, 0⟩], [⟨10, 13, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 13, 1, 0, 1, 0, 0, 0, 0⟩, ⟨10, 13, 0, 0, 0, 0, 1, 1, 0⟩, ⟨10, 13, 1, 0, 1, 0, 1, 1, 0⟩]],
      [⟨10, 13, 0, 0, 0, 0, 0, 0, 1⟩, ⟨10, 13, 1, 0, 1, 0, 0, 0, 1⟩, ⟨10, 13, 0, 0, 0, 0, 1, 1, 1⟩, ⟨10, 13, 1, 0, 1, 0, 1, 1, 1⟩]⟩,
    ⟨-1, 2, 17, 9,
      [[⟨10, 10, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 10, 1, 0, 1, 0, 0, 0, 0⟩, ⟨10, 10, 0, 0, 0, 0, 1, 1, 0⟩, ⟨10, 10, 1, 0, 1, 0, 1, 1, 0⟩], [⟨10, 11, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 11, 1, 0, 1, 0, 0, 0, 0⟩, ⟨10, 11, 0, 0, 0, 0, 1, 1, 0⟩, ⟨10, 11, 1, 0, 1, 0, 1, 1, 0⟩], [⟨10, 12, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 12, 1, 0, 1, 0, 0, 0, 0⟩, ⟨10, 12, 0, 0, 0, 0, 1, 1, 0⟩, ⟨10, 12, 1, 0, 1, 0, 1, 1, 0⟩], [⟨10, 14, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 14, 1, 0, 1, 0, 0, 0, 0⟩, ⟨10, 14, 0, 0, 0, 0, 1, 1, 0⟩, ⟨10, 14, 1, 0, 1, 0, 1, 1, 0⟩]],
      [⟨10, 14, 0, 0, 0, 0, 0, 0, 3⟩, ⟨10, 14, 1, 0, 1, 0, 0, 0, 3⟩, ⟨10, 14, 0, 0, 0, 0, 1, 1, 3⟩, ⟨10, 14, 1, 0, 1, 0, 1, 1, 3⟩]⟩,
    ⟨-1, 2, 18, 10,
      [[⟨10, 6, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 6, 1, 0, 1, 0, 0, 0, 0⟩, ⟨10, 6, 0, 0, 0, 0, 1, 1, 0⟩, ⟨10, 6, 1, 0, 1, 0, 1, 1, 0⟩], [⟨10, 7, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 7, 1, 0, 1, 0, 0, 0, 0⟩, ⟨10, 7, 0, 0, 0, 0, 1, 1, 0⟩, ⟨10, 7, 1, 0, 1, 0, 1, 1, 0⟩], [⟨10, 8, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 8, 1, 0, 1, 0, 0, 0, 0⟩, ⟨10, 8, 0, 0, 0, 0, 1, 1, 0⟩, ⟨10, 8, 1, 0, 1, 0, 1, 1, 0⟩], [⟨10, 9, 0, 0, 0, 0, 0, 0, 0⟩, ⟨10, 9, 1, 0, 1, 0, 0, 0, 0⟩, ⟨10, 9, 0, 0, 0, 0, 1, 1, 0⟩, ⟨10, 9, 1, 0, 1, 0, 1, 1, 0⟩], [⟨4, 10, 0, 0, 1, 0, 0, 0, 0⟩, ⟨4, 10, 1, 0, 2, 0, 0, 0, 0⟩, ⟨10, 10, 0, 0, 1, 0, 1, 0, 0⟩, ⟨10, 10, 1, 0, 2, 0, 1, 0, 0⟩], [⟨4, 11, 0, 0, 1, 0, 0, 0, 0⟩, ⟨4, 11, 1, 0, 2, 0, 0, 0, 0⟩, ⟨10, 11, 0, 0, 1, 0, 1, 0, 0⟩, ⟨10, 11, 1, 0, 2, 0, 1, 0, 0⟩]],
      [⟨10, 9, 0, 0, 0, 0, 0, 0, 2⟩, ⟨10, 9, 1, 0, 1, 0, 0, 0, 2⟩, ⟨10, 9, 0, 0, 0, 0, 1, 1, 2⟩, ⟨10, 9, 1, 0, 1, 0, 1, 1, 2⟩]⟩]⟩,
  ⟨2, -1, 1, -1, 0, [(0, 1, 1), (-1, -1, 1)], 0, 1, 1, 1, -1, -1, 1, 1,
   [⟨-2, 1, 0, 10,
      [[⟨11, 2, 0, 0, 0, 0, 0, 0, 0⟩, ⟨11, 2, 1, 0, 1, 0, 0, 0, 0⟩, ⟨11, 2, 0, 0, 0, 0, 1, 1, 0⟩, ⟨11, 2, 1, 0, 1, 0, 1, 1, 0⟩], [⟨11, 7, 0, 0, 0, 0, 0, 0, 0⟩, ⟨11, 7, 1, 0, 1, 0, 0, 0, 0⟩, ⟨11, 7, 0, 0, 0, 0, 1, 1, 0⟩, ⟨11, 7, 1, 0, 1, 0, 1, 1, 0⟩], [⟨5, 4, 0, 0, 1, 0, 0, 0, 0⟩, ⟨5, 4, 1, 0, 2, 0, 0, 0, 0⟩, ⟨11, 4, 0, 0, 1, 0, 1, 0, 0⟩, ⟨11, 4, 1, 0, 2, 0, 1, 0, 0⟩], [⟨5, 14, 0, 0, 1, 0, 0, 0, 0⟩, ⟨5, 14, 1, 0, 2, 0, 0, 0, 0⟩, ⟨11, 14, 0, 0, 1, 0, 1, 0, 0⟩, ⟨11, 14, 1, 0, 2, 0, 1, 0, 0⟩]],
      [⟨11, 7, 0, 0, 0, 0, 0, 0, 0⟩, ⟨11, 7, 1, 0, 1, 0, 0, 0, 0⟩, ⟨11, 7, 0, 0, 0, 0, 1, 1, 0⟩, ⟨11, 7, 1, 0, 1, 0, 1, 1, 0⟩]⟩,
    ⟨-2, 1, 1, 12,
      [[⟨11, 6, 0, 0, 0, 0, 0, 1, 0⟩, ⟨11, 6, 1, 0, 1, 0, 0, 1, 0⟩, ⟨11, 6, 0, 0, 0, 0, 1, 2, 0⟩, ⟨11, 6, 1, 0, 1, 0, 1, 2, 0⟩], [⟨11, 13, 0, 0, 1, 0, 0, 0, 0⟩, ⟨11, 13, 1, 0, 2, 0, 0, 0, 0⟩, ⟨11, 13, 0, 0, 1, 0, 1, 1, 0⟩, ⟨11, 13, 1, 0, 2, 0, 1, 1, 0⟩], [⟨11, 3, 0, 0, 0, 0, 0, 0, 0⟩, ⟨11, 3, 1, 0, 1, 0, 0, 0, 0⟩, ⟨11, 3, 0, 0, 0, 0, 1, 1, 0⟩, ⟨11, 3, 1, 0, 1, 0, 1, 1, 0⟩], [⟨5, 5, 0, 0, 1, 0, 0, 0, 0⟩, ⟨5, 5, 1, 0, 2, 0, 0, 0, 0⟩, ⟨11, 5, 0, 0, 1, 0, 1, 0, 0⟩, ⟨11, 5, 1, 0, 2, 0, 1, 0, 0⟩]],
      [⟨11, 3, 0, 0, 0, 0, 0, 0, 0⟩, ⟨11, 3, 1, 0, 1, 0, 0, 0, 0⟩, ⟨11, 3, 0, 0, 0, 0, 1, 1, 0⟩, ⟨11, 3, 1, 0, 1, 0, 1, 1, 0⟩]⟩,
    ⟨-2, 1, 2, 10,
      [[⟨11, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨11, 0, 1, 0, 1, 0, 0, 0, 0⟩, ⟨11, 0, 0, 0, 0, 0, 1, 1, 0⟩, ⟨11, 0, 1, 0, 1, 0, 1, 1, 0⟩], [⟨11, 3, 0, 0, 0, 0, 0, 0, 0⟩, ⟨11, 3, 1, 0, 1, 0, 0, 0, 0⟩, ⟨11, 3, 0, 0, 0, 0, 1, 1, 0⟩, ⟨11, 3, 1, 0, 1, 0, 1, 1, 0⟩], [⟨11, 8, 0, 0, 0, 0, 0, 0, 0⟩, ⟨11, 8, 1, 0, 1, 0, 0, 0, 0⟩, ⟨11, 8, 0, 0, 0, 0, 1, 1, 0⟩, ⟨11, 8, 1, 0, 1, 0, 1, 1, 0⟩], [⟨11, 12, 0, 0, 0, 0, 0, 0, 0⟩, ⟨11, 12, 1, 0, 1, 0, 0, 0, 0⟩, ⟨11, 12, 0, 0, 0, 0, 1, 1, 0⟩, ⟨11, 12, 1, 0, 1, 0, 1, 1, 0⟩]],
      [⟨11, 8, 0, 0, 0, 0, 0, 0, 0⟩, ⟨11, 8, 1, 0, 1, 0, 0, 0, 0⟩, ⟨11, 8, 0, 0, 0, 0, 1, 1, 0⟩, ⟨11, 8, 1, 0, 1, 0, 1, 1, 0⟩]⟩,
    ⟨-2, 1, 3, 11,
      [[⟨11, 1, 0, 0, 0, 0, 0, 0, 0⟩, ⟨11, 1, 1, 0, 1, 0, 0, 0, 0⟩, ⟨11, 1, 0, 0, 0, 0, 1, 1, 0⟩, ⟨11, 1, 1, 0, 1, 0, 1, 1, 0⟩], [⟨11, 2, 0, 0, 0, 0, 0, 0, 0⟩, ⟨11, 2, 1, 0, 1, 0, 0, 0, 0⟩, ⟨11, 2, 0, 0, 0, 0, 1, 1, 0⟩, ⟨11, 2, 1, 0, 1, 0, 1, 1, 0⟩], [⟨11, 10, 0, 0, 0, 0, 0, 0, 0⟩, ⟨11, 10, 1, 0, 1, 0, 0, 0, 0⟩, ⟨11, 10, 0, 0, 0, 0, 1, 1, 0⟩, ⟨11, 10, 1, 0, 1, 0, 1, 1, 0⟩], [⟨11, 12, 0, 0, 0, 0, 0, 0, 0⟩, ⟨11, 12, 1, 0, 1, 0, 0, 0, 0⟩, ⟨11, 12, 0, 0, 0, 0, 1, 1, 0⟩, ⟨11, 12, 1, 0, 1, 0, 1, 1, 0⟩]],
      [⟨11, 2, 0, 0, 0, 0, 0, 0, 1⟩, ⟨11, 2, 1, 0, 1, 0, 0, 0, 1⟩, ⟨11, 2, 0, 0, 0, 0, 1, 1, 1⟩, ⟨11, 2, 1, 0, 1, 0, 1, 1, 1⟩]⟩,
    ⟨-2, 1, 4, 11,
      [[⟨6, 0, 0, 0, 1, 0, 0, 0, 0⟩, ⟨11, 0, 1, 0, 0, 0, 0, 1, 0⟩, ⟨6, 0, 0, 1, 2, 0, 0, 0, 0⟩, ⟨11, 0, 1, 0, 0, 0, 1, 2, 0⟩], [⟨11, 5, 0, 0, 0, 0, 0, 0, 0⟩, ⟨11, 5, 1, 0, 1, 0, 0, 0, 0⟩, ⟨11, 5, 0, 0, 0, 0, 1, 1, 0⟩, ⟨11, 5, 1, 0, 1, 0, 1, 1, 0⟩], [⟨11, 11, 0, 0, 0, 0, 0, 0, 0⟩, ⟨11, 11, 1, 0, 1, 0, 0, 0, 0⟩, ⟨11, 11, 0, 0, 0, 0, 1, 1, 0⟩, ⟨11, 11, 1, 0, 1, 0, 1, 1, 0⟩], [⟨11, 14, 0, 0, 0, 0, 0, 0, 0⟩, ⟨11, 14, 1, 0, 1, 0, 0, 0, 0⟩, ⟨11, 14, 0, 0, 0, 0, 1, 1, 0⟩, ⟨11, 14, 1, 0, 1, 0, 1, 1, 0⟩]],
      [⟨6, 0, 0, 0, 1, 0, 0, 0, 2⟩, ⟨11, 0, 1, 0, 0, 0, 0, 1, 2⟩, ⟨6, 0, 0, 1, 2, 0, 0, 0, 2⟩, ⟨11, 0, 1, 0, 0, 0, 1, 2, 2⟩]⟩,
    ⟨-2, 1, 5, 12,
      [[⟨11, 9, 0, 0, 0, 0, 0, 1, 0⟩, ⟨11, 9, 1, 0, 1, 0, 0, 1, 0⟩, ⟨11, 9, 0, 0, 0, 0, 1, 2, 0⟩, ⟨11, 9, 1, 0, 1, 0, 1, 2, 0⟩], [⟨11, 13, 0, 0, 0, 0, 0, 1, 0⟩, ⟨11, 13, 1, 0, 1, 0, 0, 1, 0⟩, ⟨11, 13, 0, 0, 0, 0, 1, 2, 0⟩, ⟨11, 13, 1, 0, 1, 0, 1, 2, 0⟩], [⟨6, 1, 0, 0, 1, 0, 0, 0, 0⟩, ⟨11, 1, 1, 0, 0, 0, 0, 1, 0⟩, ⟨6, 1, 0, 1, 2, 0, 0, 0, 0⟩, ⟨11, 1, 1, 0, 0, 0, 1, 2, 0⟩], [⟨11, 4, 0, 0, 0, 0, 0, 0, 0⟩, ⟨11, 4, 1, 0, 1, 0, 0, 0, 0⟩, ⟨11, 4, 0, 0, 0, 0, 1, 1, 0⟩, ⟨11, 4, 1, 0, 1, 0, 1, 1, 0⟩]],
      [⟨11, 4, 0, 0, 0, 0, 0, 0, 1⟩, ⟨11, 4, 1, 0, 1, 0, 0, 0, 1⟩, ⟨11, 4, 0, 0, 0, 0, 1, 1, 1⟩, ⟨11, 4, 1, 0, 1, 0, 1, 1, 1⟩]⟩,
    ⟨-2, 1, 6, 8,
      [[⟨11, 7, 0, 0, 0, 0, 0, 0, 0⟩, ⟨11, 7, 1, 0, 1, 0, 0, 0, 0⟩, ⟨11, 7, 0, 0, 0, 0, 1, 1, 0⟩, ⟨11, 7, 1, 0, 1, 0, 1, 1, 0⟩], [⟨11, 15, 0, 0, 0, 0, 0, 0, 0⟩, ⟨11, 15, 1, 0, 1, 0, 0, 0, 0⟩, ⟨11, 15, 0, 0, 0, 0, 1, 1, 0⟩, ⟨11, 15, 1, 0, 1, 0, 1, 1, 0⟩], [⟨11, 18, 0, 0, 0, 0, 0, 0, 0⟩, ⟨11, 18, 1, 0, 1, 0, 0, 0, 0⟩, ⟨11, 18, 0, 0, 0, 0, 1, 1, 0⟩, ⟨11, 18, 1, 0, 1, 0, 1, 1, 0⟩], [⟨5, 1, 0, 0, 0, 0, 0, 0, 0⟩, ⟨5, 1, 1, 0, 1, 0, 0, 0, 0⟩, ⟨11, 1, 0, 0, 0, 0, 1, 0, 0⟩, ⟨11, 1, 1, 0, 1, 0, 1, 0, 0⟩], [⟨5, 10, 0, 0, 0, 0, 0, 0, 0⟩, ⟨5, 10, 1, 0, 1, 0, 0, 0, 0⟩, ⟨11, 10, 0, 0, 0, 0, 1, 0, 0⟩, ⟨11, 10, 1, 0, 1, 0, 1, 0, 0⟩]],
      [⟨5, 1, 0, 0, 0, 0, 0, 0, 0⟩, ⟨5, 1, 1, 0, 1, 0, 0, 0, 0⟩, ⟨11, 1, 0, 0, 0, 0, 1, 0, 0⟩, ⟨11, 1, 1, 0, 1, 0, 1, 0, 0⟩]⟩,
    ⟨-2, 1, 7, 9,
      [[⟨11, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨11, 0, 1, 0, 1, 0, 0, 0, 0⟩, ⟨11, 0, 0, 0, 0, 0, 1, 1, 0⟩, ⟨11, 0, 1, 0, 1, 0, 1, 1, 0⟩], [⟨11, 6, 0, 0, 0, 0, 0, 0, 0⟩, ⟨11, 6, 1, 0, 1, 0, 0, 0, 0⟩, ⟨11, 6, 0, 0, 0, 0, 1, 1, 0⟩, ⟨11, 6, 1, 0, 1, 0, 1, 1, 0⟩], [⟨11, 8, 0, 0, 0, 0, 0, 0, 0⟩, ⟨11, 8, 1, 0, 1, 0, 0, 0, 0⟩, ⟨11, 8, 0, 0, 0, 0, 1, 1, 0⟩, ⟨11, 8, 1, 0, 1, 0, 1, 1, 0⟩], [⟨11, 15, 0, 0, 0, 0, 0, 0, 0⟩, ⟨11, 15, 1, 0, 1, 0, 0, 0, 0⟩, ⟨11, 15, 0, 0, 0, 0, 1, 1, 0⟩, ⟨11, 15, 1, 0, 1, 0, 1, 1, 0⟩], [⟨11, 18, 0, 0, 0, 0, 0, 0, 0⟩, ⟨11, 18, 1, 0, 1, 0, 0, 0, 0⟩, ⟨11, 18, 0, 0, 0, 0, 1, 1, 0⟩, ⟨11, 18, 1, 0, 1, 0, 1, 1, 0⟩]],
      [⟨11, 6, 0, 0, 0, 0, 0, 0, 0⟩, ⟨11, 6, 1, 0, 1, 0, 0, 0, 0⟩, ⟨11, 6, 0, 0, 0, 0, 1, 1, 0⟩, ⟨11, 6, 1, 0, 1, 0, 1, 1, 0⟩]⟩,
    ⟨-2, 1, 8, 9,
      [[⟨11, 2, 0, 0, 0, 0, 0, 0, 0⟩, ⟨11, 2, 1, 0, 1, 0, 0, 0, 0⟩, ⟨11, 2, 0, 0, 0, 0, 1, 1, 0⟩, ⟨11, 2, 1, 0, 1, 0, 1, 1, 0⟩], [⟨11, 7, 0, 0, 0, 0, 0, 0, 0⟩, ⟨11, 7, 1, 0, 1, 0, 0, 0, 0⟩, ⟨11, 7, 0, 0, 0, 0, 1, 1, 0⟩, ⟨11, 7, 1, 0, 1, 0, 1, 1, 0⟩], [⟨11, 9, 0, 0, 0, 0, 0, 0, 0⟩, ⟨11, 9, 1, 0, 1, 0, 0, 0, 0⟩, ⟨11, 9, 0, 0, 0, 0, 1, 1, 0⟩, ⟨11, 9, 1, 0, 1, 0, 1, 1, 0⟩], [⟨11, 16, 0, 0, 0, 0, 0, 0, 0⟩, ⟨11, 16, 1, 0, 1, 0, 0, 0, 0⟩, ⟨11, 16, 0, 0, 0, 0, 1, 1, 0⟩, ⟨11, 16, 1, 0, 1, 0, 1, 1, 0⟩], [⟨11, 18, 0, 0, 0, 0, 0, 0, 0⟩, ⟨11, 18, 1, 0, 1, 0, 0, 0, 0⟩, ⟨11, 18, 0, 0, 0, 0, 1, 1, 0⟩, ⟨11, 18, 1, 0, 1, 0, 1, 1, 0⟩]],
      [⟨11, 9, 0, 0, 0, 0, 0, 0, 0⟩, ⟨11, 9, 1, 0, 1, 0, 0, 0, 0⟩, ⟨11, 9, 0, 0, 0, 0, 1, 1, 0⟩, ⟨11, 9, 1, 0, 1, 0, 1, 1, 0⟩]⟩,
    ⟨-2, 1, 9, 8,
      [[⟨11, 8, 0, 0, 0, 0, 0, 0, 0⟩, ⟨11, 8, 1, 0, 1, 0, 0, 0, 0⟩, ⟨11, 8, 0, 0, 0, 0, 1, 1, 0⟩, ⟨11, 8, 1, 0, 1, 0, 1, 1, 0⟩], [⟨11, 16, 0, 0, 0, 0, 0, 0, 0⟩, ⟨11, 16, 1, 0, 1, 0, 0, 0, 0⟩, ⟨11, 16, 0, 0, 0, 0, 1, 1, 0⟩, ⟨11, 16, 1, 0, 1, 0, 1, 1, 0⟩], [⟨11, 18, 0, 0, 0, 0, 0, 0, 0⟩, ⟨11, 18, 1, 0, 1, 0, 0, 0, 0⟩, ⟨11, 18, 0, 0, 0, 0, 1, 1, 0⟩, ⟨11, 18, 1, 0, 1, 0, 1, 1, 0⟩], [⟨5, 5, 0, 0, 0, 0, 0, 0, 0⟩, ⟨5, 5, 1, 0, 1, 0, 0, 0, 0⟩, ⟨11, 5, 0, 0, 0, 0, 1, 0, 0⟩, ⟨11, 5, 1, 0, 1, 0, 1, 0, 0⟩], [⟨5, 11, 0, 0, 0, 0, 0, 0, 0⟩, ⟨5, 11, 1, 0, 1, 0, 0, 0, 0⟩, ⟨11, 11, 0, 0, 0, 0, 1, 0, 0⟩, ⟨11, 11, 1, 0, 1, 0, 1, 0, 0⟩]],
      [⟨5, 5, 0, 0, 0, 0, 0, 0, 0⟩, ⟨5, 5, 1, 0, 1, 0, 0, 0, 0⟩, ⟨11, 5, 0, 0, 0, 0, 1, 0, 0⟩, ⟨11, 5, 1, 0, 1, 0, 1, 0, 0⟩]⟩,
    ⟨-2, 1, 10, 12,
      [[⟨11, 6, 0, 0, 0, 0, 0, 1, 0⟩, ⟨11, 6, 1, 0, 1, 0, 0, 1, 0⟩, ⟨11, 6, 0, 0, 0, 0, 1, 2, 0⟩, ⟨11, 6, 1, 0, 1, 0, 1, 2, 0⟩], [⟨11, 18, 0, 0, 0, 0, 0, 1, 0⟩, ⟨11, 18, 1, 0, 1, 0, 0, 1, 0⟩, ⟨11, 18, 0, 0, 0, 0, 1, 2, 0⟩, ⟨11, 18, 1, 0, 1, 0, 1, 2, 0⟩], [⟨11, 3, 0, 0, 0, 0, 0, 0, 0⟩, ⟨11, 3, 1, 0, 1, 0, 0, 0, 0⟩, ⟨11, 3, 0, 0, 0, 0, 1, 1, 0⟩, ⟨11, 3, 1, 0, 1, 0, 1, 1, 0⟩], [⟨11, 11, 0, 0, 0, 0, 0, 0, 0⟩, ⟨11, 11, 1, 0, 1, 0, 0, 0, 0⟩, ⟨11, 11, 0, 0, 0, 0, 1, 1, 0⟩, ⟨11, 11, 1, 0, 1, 0, 1, 1, 0⟩], [⟨11, 17, 0, 0, 0, 0, 0, 0, 0⟩, ⟨11, 17, 1, 0, 1, 0, 0, 0, 0⟩, ⟨11, 17, 0, 0, 0, 0, 1, 1, 0⟩, ⟨11, 17, 1, 0, 1, 0, 1, 1, 0⟩]],
      [⟨11, 3, 0, 0, 0, 0, 0, 0, 2⟩, ⟨11, 3, 1, 0, 1, 0, 0, 0, 2⟩, ⟨11, 3, 0, 0, 0, 0, 1, 1, 2⟩, ⟨11, 3, 1, 0, 1, 0, 1, 1, 2⟩]⟩,
    ⟨-2, 1, 11, 12,
      [[⟨11, 9, 0, 0, 0, 0, 0, 1, 0⟩, ⟨11, 9, 1, 0, 1, 0, 0, 1, 0⟩, ⟨11, 9, 0, 0, 0, 0, 1, 2, 0⟩, ⟨11, 9, 1, 0, 1, 0, 1, 2, 0⟩], [⟨11, 18, 0, 0, 0, 0, 0, 1, 0⟩, ⟨11, 18, 1, 0, 1, 0, 0, 1, 0⟩, ⟨11, 18, 0, 0, 0, 0, 1, 2, 0⟩, ⟨11, 18, 1, 0, 1, 0, 1, 2, 0⟩], [⟨11, 4, 0, 0, 0, 0, 0, 0, 0⟩, ⟨11, 4, 1, 0, 1, 0, 0, 0, 0⟩, ⟨11, 4, 0, 0, 0, 0, 1, 1, 0⟩, ⟨11, 4, 1, 0, 1, 0, 1, 1, 0⟩], [⟨11, 10, 0, 0, 0, 0, 0, 0, 0⟩, ⟨11, 10, 1, 0, 1, 0, 0, 0, 0⟩, ⟨11, 10, 0, 0, 0, 0, 1, 1, 0⟩, ⟨11, 10, 1, 0, 1, 0, 1, 1, 0⟩], [⟨11, 17, 0, 0, 0, 0, 0, 0, 0⟩, ⟨11, 17, 1, 0, 1, 0, 0, 0, 0⟩, ⟨11, 17, 0, 0, 0, 0, 1, 1, 0⟩, ⟨11, 17, 1, 0, 1, 0, 1, 1, 0⟩]],
      [⟨11, 4, 0, 0, 0, 0, 0, 0, 2⟩, ⟨11, 4, 1, 0, 1, 0, 0, 0, 2⟩, ⟨11, 4, 0, 0, 0, 0, 1, 1, 2⟩, ⟨11, 4, 1, 0, 1, 0, 1, 1, 2⟩]⟩,
    ⟨-2, 1, 12, 10,
      [[⟨11, 2, 0, 0, 0, 0, 0, 0, 0⟩, ⟨11, 2, 1, 0, 1, 0, 0, 0, 0⟩, ⟨11, 2, 0, 0, 0, 0, 1, 1, 0⟩, ⟨11, 2, 1, 0, 1, 0, 1, 1, 0⟩], [⟨11, 3, 0, 0, 0, 0, 0, 0, 0⟩, ⟨11, 3, 1, 0, 1, 0, 0, 0, 0⟩, ⟨11, 3, 0, 0, 0, 0, 1, 1, 0⟩, ⟨11, 3, 1, 0, 1, 0, 1, 1, 0⟩], [⟨11, 16, 0, 0, 0, 0, 0, 0, 0⟩, ⟨11, 16, 1, 0, 1, 0, 0, 0, 0⟩, ⟨11, 16, 0, 0, 0, 0, 1, 1, 0⟩, ⟨11, 16, 1, 0, 1, 0, 1, 1, 0⟩], [⟨11, 17, 0, 0, 0, 0, 0, 0, 0⟩, ⟨11, 17, 1, 0, 1, 0, 0, 0, 0⟩, ⟨11, 17, 0, 0, 0, 0, 1, 1, 0⟩, ⟨11, 17, 1, 0, 1, 0, 1, 1, 0⟩]],
      [⟨11, 16, 0, 0, 0, 0, 0, 0, 2⟩, ⟨11, 16, 1, 0, 1, 0, 0, 0, 2⟩, ⟨11, 16, 0, 0, 0, 0, 1, 1, 2⟩, ⟨11, 16, 1, 0, 1, 0, 1, 1, 2⟩]⟩,
    ⟨-2, 1, 13, 8,
      [[⟨6, 15, 0, 0, 1, 0, 0, 0, 0⟩, ⟨11, 15, 1, 0, 0, 0, 0, 1, 0⟩, ⟨6, 15, 0, 1, 2, 0, 0, 0, 0⟩, ⟨11, 15, 1, 0, 0, 0, 1, 2, 0⟩], [⟨11, 16, 0, 0, 0, 0, 0, 0, 0⟩, ⟨11, 16, 1, 0, 1, 0, 0, 0, 0⟩, ⟨11, 16, 0, 0, 0, 0, 1, 1, 0⟩, ⟨11, 16, 1, 0, 1, 0, 1, 1, 0⟩], [⟨6, 1, 0, 0, 0, 0, 0, 0, 0⟩, ⟨11, 1, 1, 0, 0, 0, 0, 0, 0⟩, ⟨6, 1, 0, 1, 1, 0, 0, 0, 0⟩, ⟨11, 1, 1, 0, 0, 0, 1, 1, 0⟩], [⟨5, 5, 0, 0, 0, 0, 0, 0, 0⟩, ⟨5, 5, 1, 0, 1, 0, 0, 0, 0⟩, ⟨11, 5, 0, 0, 0, 0, 1, 0, 0⟩, ⟨11, 5, 1, 0, 1, 0, 1, 0, 0⟩]],
      [⟨6, 1, 0, 0, 0, 0, 0, 0, 1⟩, ⟨11, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨6, 1, 0, 1, 1, 0, 0, 0, 1⟩, ⟨11, 1, 1, 0, 0, 0, 1, 1, 1⟩]⟩,
    ⟨-2, 1, 14, 10,
      [[⟨6, 0, 0, 0, 1, 0, 0, 0, 0⟩, ⟨11, 0, 1, 0, 0, 0, 0, 1, 0⟩, ⟨6, 0, 0, 1, 2, 0, 0, 0, 0⟩, ⟨11, 0, 1, 0, 0, 0, 1, 2, 0⟩], [⟨6, 15, 0, 0, 1, 0, 0, 0, 0⟩, ⟨11, 15, 1, 0, 0, 0, 0, 1, 0⟩, ⟨6, 15, 0, 1, 2, 0, 0, 0, 0⟩, ⟨11, 15, 1, 0, 0, 0, 1, 2, 0⟩], [⟨11, 4, 0, 0, 0, 0, 0, 0, 0⟩, ⟨11, 4, 1, 0, 1, 0, 0, 0, 0⟩, ⟨11, 4, 0, 0, 0, 0, 1, 1, 0⟩, ⟨11, 4, 1, 0, 1, 0, 1, 1, 0⟩], [⟨11, 17, 0, 0, 0, 0, 0, 0, 0⟩, ⟨11, 17, 1, 0, 1, 0, 0, 0, 0⟩, ⟨11, 17, 0, 0, 0, 0, 1, 1, 0⟩, ⟨11, 17, 1, 0, 1, 0, 1, 1, 0⟩]],
      [⟨6, 15, 0, 0, 1, 0, 0, 0, 3⟩, ⟨11, 15, 1, 0, 0, 0, 0, 1, 3⟩, ⟨6, 15, 0, 1, 2, 0, 0, 0, 3⟩, ⟨11, 15, 1, 0, 0, 0, 1, 2, 3⟩]⟩,
    ⟨-2, 1, 15, 9,
      [[⟨11, 6, 0, 0, 0, 0, 0, 0, 0⟩, ⟨11, 6, 1, 0, 1, 0, 0, 0, 0⟩, ⟨11, 6, 0, 0, 0, 0, 1, 1, 0⟩, ⟨11, 6, 1, 0, 1, 0, 1, 1, 0⟩], [⟨11, 7, 0, 0, 0, 0, 0, 0, 0⟩, ⟨11, 7, 1, 0, 1, 0, 0, 0, 0⟩, ⟨11, 7, 0, 0, 0, 0, 1, 1, 0⟩, ⟨11, 7, 1, 0, 1, 0, 1, 1, 0⟩], [⟨5, 13, 0, 0, 1, 0, 0, 0, 0⟩, ⟨5, 13, 1, 0, 2, 0, 0, 0, 0⟩, ⟨11, 13, 0, 0, 1, 0, 1, 0, 0⟩, ⟨11, 13, 1, 0, 2, 0, 1, 0, 0⟩], [⟨5, 14, 0, 0, 1, 0, 0, 0, 0⟩, ⟨5, 14, 1, 0, 2, 0, 0, 0, 0⟩, ⟨11, 14, 0, 0, 1, 0, 1, 0, 0⟩, ⟨11, 14, 1, 0, 2, 0, 1, 0, 0⟩]],
      [⟨11, 6, 0, 0, 0, 0, 0, 0, 1⟩, ⟨11, 6, 1, 0, 1, 0, 0, 0, 1⟩, ⟨11, 6, 0, 0, 0, 0, 1, 1, 1⟩, ⟨11, 6, 1, 0, 1, 0, 1, 1, 1⟩]⟩,
    ⟨-2, 1, 16, 9,
      [[⟨11, 8, 0, 0, 0, 0, 0, 0, 0⟩, ⟨11, 8, 1, 0, 1, 0, 0, 0, 0⟩, ⟨11, 8, 0, 0, 0, 0, 1, 1, 0⟩, ⟨11, 8, 1, 0, 1, 0, 1, 1, 0⟩], [⟨11, 9, 0, 0, 0, 0, 0, 0, 0⟩, ⟨11, 9, 1, 0, 1, 0, 0, 0, 0⟩, ⟨11, 9, 0, 0, 0, 0, 1, 1, 0⟩, ⟨11, 9, 1, 0, 1, 0, 1, 1, 0⟩], [⟨11, 12, 0, 0, 0, 0, 0, 0, 0⟩, ⟨11, 12, 1, 0, 1, 0, 0, 0, 0⟩, ⟨11, 12, 0, 0, 0, 0, 1, 1, 0⟩, ⟨11, 12, 1, 0, 1, 0, 1, 1, 0⟩], [⟨11, 13, 0, 0, 0, 0, 0, 0, 0⟩, ⟨11, 13, 1, 0, 1, 0, 0, 0, 0⟩, ⟨11, 13, 0, 0, 0, 0, 1, 1, 0⟩, ⟨11, 13, 1, 0, 1, 0, 1, 1, 0⟩]],
      [⟨11, 9, 0, 0, 0, 0, 0, 0, 1⟩, ⟨11, 9, 1, 0, 1, 0, 0, 0, 1⟩, ⟨11, 9, 0, 0, 0, 0, 1, 1, 1⟩, ⟨11, 9, 1, 0, 1, 0, 1, 1, 1⟩]⟩,
    ⟨-2, 1, 17, 11,
      [[⟨11, 10, 0, 0, 0, 0, 0, 0, 0⟩, ⟨11, 10, 1, 0, 1, 0, 0, 0, 0⟩, ⟨11, 10, 0, 0, 0, 0, 1, 1, 0⟩, ⟨11, 10, 1, 0, 1, 0, 1, 1, 0⟩], [⟨11, 11, 0, 0, 0, 0, 0, 0, 0⟩, ⟨11, 11, 1, 0, 1, 0, 0, 0, 0⟩, ⟨11, 11, 0, 0, 0, 0, 1, 1, 0⟩, ⟨11, 11, 1, 0, 1, 0, 1, 1, 0⟩], [⟨11, 12, 0, 0, 0, 0, 0, 0, 0⟩, ⟨11, 12, 1, 0, 1, 0, 0, 0, 0⟩, ⟨11, 12, 0, 0, 0, 0, 1, 1, 0⟩, ⟨11, 12, 1, 0, 1, 0, 1, 1, 0⟩], [⟨11, 14, 0, 0, 0, 0, 0, 0, 0⟩, ⟨11, 14, 1, 0, 1, 0, 0, 0, 0⟩, ⟨11, 14, 0, 0, 0, 0, 1, 1, 0⟩, ⟨11, 14, 1, 0, 1, 0, 1, 1, 0⟩]],
      [⟨11, 12, 0, 0, 0, 0, 0, 0, 3⟩, ⟨11, 12, 1, 0, 1, 0, 0, 0, 3⟩, ⟨11, 12, 0, 0, 0, 0, 1, 1, 3⟩, ⟨11, 12, 1, 0, 1, 0, 1, 1, 3⟩]⟩,
    ⟨-2, 1, 18, 8,
      [[⟨11, 6, 0, 0, 0, 0, 0, 0, 0⟩, ⟨11, 6, 1, 0, 1, 0, 0, 0, 0⟩, ⟨11, 6, 0, 0, 0, 0, 1, 1, 0⟩, ⟨11, 6, 1, 0, 1, 0, 1, 1, 0⟩], [⟨11, 7, 0, 0, 0, 0, 0, 0, 0⟩, ⟨11, 7, 1, 0, 1, 0, 0, 0, 0⟩, ⟨11, 7, 0, 0, 0, 0, 1, 1, 0⟩, ⟨11, 7, 1, 0, 1, 0, 1, 1, 0⟩], [⟨11, 8, 0, 0, 0, 0, 0, 0, 0⟩, ⟨11, 8, 1, 0, 1, 0, 0, 0, 0⟩, ⟨11, 8, 0, 0, 0, 0, 1, 1, 0⟩, ⟨11, 8, 1, 0, 1, 0, 1, 1, 0⟩], [⟨11, 9, 0, 0, 0, 0, 0, 0, 0⟩, ⟨11, 9, 1, 0, 1, 0, 0, 0, 0⟩, ⟨11, 9, 0, 0, 0, 0, 1, 1, 0⟩, ⟨11, 9, 1, 0, 1, 0, 1, 1, 0⟩], [⟨5, 10, 0, 0, 0, 0, 0, 0, 0⟩, ⟨5, 10, 1, 0, 1, 0, 0, 0, 0⟩, ⟨11, 10, 0, 0, 0, 0, 1, 0, 0⟩, ⟨11, 10, 1, 0, 1, 0, 1, 0, 0⟩], [⟨5, 11, 0, 0, 0, 0, 0, 0, 0⟩, ⟨5, 11, 1, 0, 1, 0, 0, 0, 0⟩, ⟨11, 11, 0, 0, 0, 0, 1, 0, 0⟩, ⟨11, 11, 1, 0, 1, 0, 1, 0, 0⟩]],
      [⟨5, 10, 0, 0, 0, 0, 0, 0, 1⟩, ⟨5, 10, 1, 0, 1, 0, 0, 0, 1⟩, ⟨11, 10, 0, 0, 0, 0, 1, 0, 1⟩, ⟨11, 10, 1, 0, 1, 0, 1, 0, 1⟩]⟩]⟩,
  ⟨2, -1, 0, 0, -1, [(-1, 0, 1), (0, -1, 1)], -1, 0, 1, 1, 0, -1, 1, 1,
   [⟨-1, -1, 0, 8,
      [[⟨12, 2, 0, 0, 0, 0, 0, 0, 0⟩, ⟨12, 2, 1, 0, 1, 0, 0, 0, 0⟩, ⟨12, 2, 0, 0, 0, 0, 1, 1, 0⟩, ⟨12, 2, 1, 0, 1, 0, 1, 1, 0⟩], [⟨12, 7, 0, 0, 0, 0, 0, 0, 0⟩, ⟨12, 7, 1, 0, 1, 0, 0, 0, 0⟩, ⟨12, 7, 0, 0, 0, 0, 1, 1, 0⟩, ⟨12, 7, 1, 0, 1, 0, 1, 1, 0⟩], [⟨6, 4, 0, 0, 0, 0, 0, 0, 0⟩, ⟨6, 4, 1, 0, 1, 0, 0, 0, 0⟩, ⟨12, 4, 0, 0, 0, 0, 1, 0, 0⟩, ⟨12, 4, 1, 0, 1, 0, 1, 0, 0⟩], [⟨6, 14, 0, 0, 0, 0, 0, 0, 0⟩, ⟨6, 14, 1, 0, 1, 0, 0, 0, 0⟩, ⟨12, 14, 0, 0, 0, 0, 1, 0, 0⟩, ⟨12, 14, 1, 0, 1, 0, 1, 0, 0⟩]],
      [⟨12, 7, 0, 0, 0, 0, 0, 0, 0⟩, ⟨12, 7, 1, 0, 1, 0, 0, 0, 0⟩, ⟨12, 7, 0, 0, 0, 0, 1, 1, 0⟩, ⟨12, 7, 1, 0, 1, 0, 1, 1, 0⟩]⟩,
    ⟨-1, -1, 1, 10,
      [[⟨12, 6, 0, 0, 1, 0, 0, 0, 0⟩, ⟨12, 6, 1, 0, 2, 0, 0, 0, 0⟩, ⟨12, 6, 0, 0, 1, 0, 1, 1, 0⟩, ⟨12, 6, 1, 0, 2, 0, 1, 1, 0⟩], [⟨6, 13, 0, 0, 1, 0, 0, 0, 0⟩, ⟨6, 13, 1, 0, 2, 0, 0, 0, 0⟩, ⟨12, 13, 0, 0, 1, 0, 1, 0, 0⟩, ⟨12, 13, 1, 0, 2, 0, 1, 0, 0⟩], [⟨12, 3, 0, 0, 0, 0, 0, 0, 0⟩, ⟨12, 3, 1, 0, 1, 0, 0, 0, 0⟩, ⟨12, 3, 0, 0, 0, 0, 1, 1, 0⟩, ⟨12, 3, 1, 0, 1, 0, 1, 1, 0⟩], [⟨6, 5, 0, 0, 0, 0, 0, 0, 0⟩, ⟨6, 5, 1, 0, 1, 0, 0, 0, 0⟩, ⟨12, 5, 0, 0, 0, 0, 1, 0, 0⟩, ⟨12, 5, 1, 0, 1, 0, 1, 0, 0⟩]],
      [⟨6, 5, 0, 0, 0, 0, 0, 0, 2⟩, ⟨6, 5, 1, 0, 1, 0, 0, 0, 2⟩, ⟨12, 5, 0, 0, 0, 0, 1, 0, 2⟩, ⟨12, 5, 1, 0, 1, 0, 1, 0, 2⟩]⟩,
    ⟨-1, -1, 2, 9,
      [[⟨12, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨12, 0, 1, 0, 1, 0, 0, 0, 0⟩, ⟨12, 0, 0, 0, 0, 0, 1, 1, 0⟩, ⟨12, 0, 1, 0, 1, 0, 1, 1, 0⟩], [⟨12, 3, 0, 0, 0, 0, 0, 0, 0⟩, ⟨12, 3, 1, 0, 1, 0, 0, 0, 0⟩, ⟨12, 3, 0, 0, 0, 0, 1, 1, 0⟩, ⟨12, 3, 1, 0, 1, 0, 1, 1, 0⟩], [⟨12, 8, 0, 0, 0, 0, 0, 0, 0⟩, ⟨12, 8, 1, 0, 1, 0, 0, 0, 0⟩, ⟨12, 8, 0, 0, 0, 0, 1, 1, 0⟩, ⟨12, 8, 1, 0, 1, 0, 1, 1, 0⟩], [⟨12, 12, 0, 0, 0, 0, 0, 0, 0⟩, ⟨12, 12, 1, 0, 1, 0, 0, 0, 0⟩, ⟨12, 12, 0, 0, 0, 0, 1, 1, 0⟩, ⟨12, 12, 1, 0, 1, 0, 1, 1, 0⟩]],
      [⟨12, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨12, 0, 1, 0, 1, 0, 0, 0, 0⟩, ⟨12, 0, 0, 0, 0, 0, 1, 1, 0⟩, ⟨12, 0, 1, 0, 1, 0, 1, 1, 0⟩]⟩,
    ⟨-1, -1, 3, 10,
      [[⟨12, 1, 0, 0, 0, 0, 0, 0, 0⟩, ⟨12, 1, 1, 0, 1, 0, 0, 0, 0⟩, ⟨12, 1, 0, 0, 0, 0, 1, 1, 0⟩, ⟨12, 1, 1, 0, 1, 0, 1, 1, 0⟩], [⟨12, 2, 0, 0, 0, 0, 0, 0, 0⟩, ⟨12, 2, 1, 0, 1, 0, 0, 0, 0⟩, ⟨12, 2, 0, 0, 0, 0, 1, 1, 0⟩, ⟨12, 2, 1, 0, 1, 0, 1, 1, 0⟩], [⟨12, 10, 0, 0, 0, 0, 0, 0, 0⟩, ⟨12, 10, 1, 0, 1, 0, 0, 0, 0⟩, ⟨12, 10, 0, 0, 0, 0, 1, 1, 0⟩, ⟨12, 10, 1, 0, 1, 0, 1, 1, 0⟩], [⟨12, 12, 0, 0, 0, 0, 0, 0, 0⟩, ⟨12, 12, 1, 0, 1, 0, 0, 0, 0⟩, ⟨12, 12, 0, 0, 0, 0, 1, 1, 0⟩, ⟨12, 12, 1, 0, 1, 0, 1, 1, 0⟩]],
      [⟨12, 2, 0, 0, 0, 0, 0, 0, 1⟩, ⟨12, 2, 1, 0, 1, 0, 0, 0, 1⟩, ⟨12, 2, 0, 0, 0, 0, 1, 1, 1⟩, ⟨12, 2, 1, 0, 1, 0, 1, 1, 1⟩]⟩,
    ⟨-1, -1, 4, 13,
      [[⟨12, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨12, 0, 1, 0, 1, 0, 0, 1, 0⟩, ⟨12, 0, 0, 0, 0, 0, 1, 2, 0⟩, ⟨12, 0, 1, 0, 1, 0, 1, 2, 0⟩], [⟨12, 5, 0, 0, 0, 0, 0, 0, 0⟩, ⟨12, 5, 1, 0, 1, 0, 0, 0, 0⟩, ⟨12, 5, 0, 0, 0, 0, 1, 1, 0⟩, ⟨12, 5, 1, 0, 1, 0, 1, 1, 0⟩], [⟨12, 11, 0, 0, 0, 0, 0, 0, 0⟩, ⟨12, 11, 1, 0, 1, 0, 0, 0, 0⟩, ⟨12, 11, 0, 0, 0, 0, 1, 1, 0⟩, ⟨12, 11, 1, 0, 1, 0, 1, 1, 0⟩], [⟨12, 14, 0, 0, 0, 0, 0, 0, 0⟩, ⟨12, 14, 1, 0, 1, 0, 0, 0, 0⟩, ⟨12, 14, 0, 0, 0, 0, 1, 1, 0⟩, ⟨12, 14, 1, 0, 1, 0, 1, 1, 0⟩]],
      [⟨12, 11, 0, 0, 0, 0, 0, 0, 2⟩, ⟨12, 11, 1, 0, 1, 0, 0, 0, 2⟩, ⟨12, 11, 0, 0, 0, 0, 1, 1, 2⟩, ⟨12, 11, 1, 0, 1, 0, 1, 1, 2⟩]⟩,
    ⟨-1, -1, 5, 14,
      [[⟨12, 9, 0, 0, 1, 0, 0, 0, 0⟩, ⟨12, 9, 1, 0, 2, 0, 0, 0, 0⟩, ⟨12, 9, 0, 0, 1, 0, 1, 1, 0⟩, ⟨12, 9, 1, 0, 2, 0, 1, 1, 0⟩], [⟨12, 13, 0, 0, 1, 0, 0, 0, 0⟩, ⟨12, 13, 1, 0, 2, 0, 0, 0, 0⟩, ⟨12, 13, 0, 0, 1, 0, 1, 1, 0⟩, ⟨12, 13, 1, 0, 2, 0, 1, 1, 0⟩], [⟨12, 1, 0, 0, 0, 0, 0, 1, 0⟩, ⟨12, 1, 1, 0, 1, 0, 0, 1, 0⟩, ⟨12, 1, 0, 0, 0, 0, 1, 2, 0⟩, ⟨12, 1, 1, 0, 1, 0, 1, 2, 0⟩], [⟨12, 4, 0, 0, 0, 0, 0, 0, 0⟩, ⟨12, 4, 1, 0, 1, 0, 0, 0, 0⟩, ⟨12, 4, 0, 0, 0, 0, 1, 1, 0⟩, ⟨12, 4, 1, 0, 1, 0, 1, 1, 0⟩]],
      [⟨12, 9, 0, 0, 1, 0, 0, 0, 3⟩, ⟨12, 9, 1, 0, 2, 0, 0, 0, 3⟩, ⟨12, 9, 0, 0, 1, 0, 1, 1, 3⟩, ⟨12, 9, 1, 0, 2, 0, 1, 1, 3⟩]⟩,
    ⟨-1, -1, 6, 6,
      [[⟨12, 7, 0, 0, 0, 0, 0, 0, 0⟩, ⟨12, 7, 1, 0, 1, 0, 0, 0, 0⟩, ⟨12, 7, 0, 0, 0, 0, 1, 1, 0⟩, ⟨12, 7, 1, 0, 1, 0, 1, 1, 0⟩], [⟨12, 15, 0, 0, 0, 0, 0, 0, 0⟩, ⟨12, 15, 1, 0, 1, 0, 0, 0, 0⟩, ⟨12, 15, 0, 0, 0, 0, 1, 1, 0⟩, ⟨12, 15, 1, 0, 1, 0, 1, 1, 0⟩], [⟨12, 18, 0, 0, 0, 0, 0, 0, 0⟩, ⟨12, 18, 1, 0, 1, 0, 0, 0, 0⟩, ⟨12, 18, 0, 0, 0, 0, 1, 1, 0⟩, ⟨12, 18, 1, 0, 1, 0, 1, 1, 0⟩], [⟨1, 1, 0, 0, 0, 0, 0, 0, 0⟩, ⟨12, 1, 1, 0, 0, 0, 0, 0, 0⟩, ⟨1, 1, 0, 1, 1, 0, 0, 0, 0⟩, ⟨12, 1, 1, 0, 0, 0, 1, 1, 0⟩], [⟨1, 10, 0, 0, 0, 0, 0, 0, 0⟩, ⟨12, 10, 1, 0, 0, 0, 0, 0, 0⟩, ⟨1, 10, 0, 1, 1, 0, 0, 0, 0⟩, ⟨12, 10, 1, 0, 0, 0, 1, 1, 0⟩]],
      [⟨1, 1, 0, 0, 0, 0, 0, 0, 0⟩, ⟨12, 1, 1, 0, 0, 0, 0, 0, 0⟩, ⟨1, 1, 0, 1, 1, 0, 0, 0, 0⟩, ⟨12, 1, 1, 0, 0, 0, 1, 1, 0⟩]⟩,
    ⟨-1, -1, 7, 7,
      [[⟨12, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨12, 0, 1, 0, 1, 0, 0, 0, 0⟩, ⟨12, 0, 0, 0, 0, 0, 1, 1, 0⟩, ⟨12, 0, 1, 0, 1, 0, 1, 1, 0⟩], [⟨12, 6, 0, 0, 0, 0, 0, 0, 0⟩, ⟨12, 6, 1, 0, 1, 0, 0, 0, 0⟩, ⟨12, 6, 0, 0, 0, 0, 1, 1, 0⟩, ⟨12, 6, 1, 0, 1, 0, 1, 1, 0⟩], [⟨12, 8, 0, 0, 0, 0, 0, 0, 0⟩, ⟨12, 8, 1, 0, 1, 0, 0, 0, 0⟩, ⟨12, 8, 0, 0, 0, 0, 1, 1, 0⟩, ⟨12, 8, 1, 0, 1, 0, 1, 1, 0⟩], [⟨12, 15, 0, 0, 0, 0, 0, 0, 0⟩, ⟨12, 15, 1, 0, 1, 0, 0, 0, 0⟩, ⟨12, 15, 0, 0, 0, 0, 1, 1, 0⟩, ⟨12, 15, 1, 0, 1, 0, 1, 1, 0⟩], [⟨12, 18, 0, 0, 0, 0, 0, 0, 0⟩, ⟨12, 18, 1, 0, 1, 0, 0, 0, 0⟩, ⟨12, 18, 0, 0, 0, 0, 1, 1, 0⟩, ⟨12, 18, 1, 0, 1, 0, 1, 1, 0⟩]],
      [⟨12, 6, 0, 0, 0, 0, 0, 0, 0⟩, ⟨12, 6, 1, 0, 1, 0, 0, 0, 0⟩, ⟨12, 6, 0, 0, 0, 0, 1, 1, 0⟩, ⟨12, 6, 1, 0, 1, 0, 1, 1, 0⟩]⟩,
    ⟨-1, -1, 8, 8,
      [[⟨12, 2, 0, 0, 0, 0, 0, 0, 0⟩, ⟨12, 2, 1, 0, 1, 0, 0, 0, 0⟩, ⟨12, 2, 0, 0, 0, 0, 1, 1, 0⟩, ⟨12, 2, 1, 0, 1, 0, 1, 1, 0⟩], [⟨12, 7, 0, 0, 0, 0, 0, 0, 0⟩, ⟨12, 7, 1, 0, 1, 0, 0, 0, 0⟩, ⟨12, 7, 0, 0, 0, 0, 1, 1, 0⟩, ⟨12, 7, 1, 0, 1, 0, 1, 1, 0⟩], [⟨12, 9, 0, 0, 0, 0, 0, 0, 0⟩, ⟨12, 9, 1, 0, 1, 0, 0, 0, 0⟩, ⟨12, 9, 0, 0, 0, 0, 1, 1, 0⟩, ⟨12, 9, 1, 0, 1, 0, 1, 1, 0⟩], [⟨12, 16, 0, 0, 0, 0, 0, 0, 0⟩, ⟨12, 16, 1, 0, 1, 0, 0, 0, 0⟩, ⟨12, 16, 0, 0, 0, 0, 1, 1, 0⟩, ⟨12, 16, 1, 0, 1, 0, 1, 1, 0⟩], [⟨12, 18, 0, 0, 0, 0, 0, 0, 0⟩, ⟨12, 18, 1, 0, 1, 0, 0, 0, 0⟩, ⟨12, 18, 0, 0, 0, 0, 1, 1, 0⟩, ⟨12, 18, 1, 0, 1, 0, 1, 1, 0⟩]],
      [⟨12, 7, 0, 0, 0, 0, 0, 0, 2⟩, ⟨12, 7, 1, 0, 1, 0, 0, 0, 2⟩, ⟨12, 7, 0, 0, 0, 0, 1, 1, 2⟩, ⟨12, 7, 1, 0, 1, 0, 1, 1, 2⟩]⟩,
    ⟨-1, -1, 9, 8,
      [[⟨12, 8, 0, 0, 0, 0, 0, 0, 0⟩, ⟨12, 8, 1, 0, 1, 0, 0, 0, 0⟩, ⟨12, 8, 0, 0, 0, 0, 1, 1, 0⟩, ⟨12, 8, 1, 0, 1, 0, 1, 1, 0⟩], [⟨12, 16, 0, 0, 0, 0, 0, 0, 0⟩, ⟨12, 16, 1, 0, 1, 0, 0, 0, 0⟩, ⟨12, 16, 0, 0, 0, 0, 1, 1, 0⟩, ⟨12, 16, 1, 0, 1, 0, 1, 1, 0⟩], [⟨12, 18, 0, 0, 0, 0, 0, 0, 0⟩, ⟨12, 18, 1, 0, 1, 0, 0, 0, 0⟩, ⟨12, 18, 0, 0, 0, 0, 1, 1, 0⟩, ⟨12, 18, 1, 0, 1, 0, 1, 1, 0⟩], [⟨1, 5, 0, 0, 0, 0, 0, 0, 0⟩, ⟨12, 5, 1, 0, 0, 0, 0, 0, 0⟩, ⟨1, 5, 0, 1, 1, 0, 0, 0, 0⟩, ⟨12, 5, 1, 0, 0, 0, 1, 1, 0⟩], [⟨1, 11, 0, 0, 0, 0, 0, 0, 0⟩, ⟨12, 11, 1, 0, 0, 0, 0, 0, 0⟩, ⟨1, 11, 0, 1, 1, 0, 0, 0, 0⟩, ⟨12, 11, 1, 0, 0, 0, 1, 1, 0⟩]],
      [⟨12, 18, 0, 0, 0, 0, 0, 0, 3⟩, ⟨12, 18, 1, 0, 1, 0, 0, 0, 3⟩, ⟨12, 18, 0, 0, 0, 0, 1, 1, 3⟩, ⟨12, 18, 1, 0, 1, 0, 1, 1, 3⟩]⟩,
    ⟨-1, -1, 10, 11,
      [[⟨12, 6, 0, 0, 1, 0, 0, 0, 0⟩, ⟨12, 6, 1, 0, 2, 0, 0, 0, 0⟩, ⟨12, 6, 0, 0, 1, 0, 1, 1, 0⟩, ⟨12, 6, 1, 0, 2, 0, 1, 1, 0⟩], [⟨12, 18, 0, 0, 1, 0, 0, 0, 0⟩, ⟨12, 18, 1, 0, 2, 0, 0, 0, 0⟩, ⟨12, 18, 0, 0, 1, 0, 1, 1, 0⟩, ⟨12, 18, 1, 0, 2, 0, 1, 1, 0⟩], [⟨12, 3, 0, 0, 0, 0, 0, 0, 0⟩, ⟨12, 3, 1, 0, 1, 0, 0, 0, 0⟩, ⟨12, 3, 0, 0, 0, 0, 1, 1, 0⟩, ⟨12, 3, 1, 0, 1, 0, 1, 1, 0⟩], [⟨12, 11, 0, 0, 0, 0, 0, 0, 0⟩, ⟨12, 11, 1, 0, 1, 0, 0, 0, 0⟩, ⟨12, 11, 0, 0, 0, 0, 1, 1, 0⟩, ⟨12, 11, 1, 0, 1, 0, 1, 1, 0⟩], [⟨12, 17, 0, 0, 0, 0, 0, 0, 0⟩, ⟨12, 17, 1, 0, 1, 0, 0, 0, 0⟩, ⟨12, 17, 0, 0, 0, 0, 1, 1, 0⟩, ⟨12, 17, 1, 0, 1, 0, 1, 1, 0⟩]],
      [⟨12, 3, 0, 0, 0, 0, 0, 0, 2⟩, ⟨12, 3, 1, 0, 1, 0, 0, 0, 2⟩, ⟨12, 3, 0, 0, 0, 0, 1, 1, 2⟩, ⟨12, 3, 1, 0, 1, 0, 1, 1, 2⟩]⟩,
    ⟨-1, -1, 11, 12,
      [[⟨12, 9, 0, 0, 1, 0, 0, 0, 0⟩, ⟨12, 9, 1, 0, 2, 0, 0, 0, 0⟩, ⟨12, 9, 0, 0, 1, 0, 1, 1, 0⟩, ⟨12, 9, 1, 0, 2, 0, 1, 1, 0⟩], [⟨12, 18, 0, 0, 1, 0, 0, 0, 0⟩, ⟨12, 18, 1, 0, 2, 0, 0, 0, 0⟩, ⟨12, 18, 0, 0, 1, 0, 1, 1, 0⟩, ⟨12, 18, 1, 0, 2, 0, 1, 1, 0⟩], [⟨12, 4, 0, 0, 0, 0, 0, 0, 0⟩, ⟨12, 4, 1, 0, 1, 0, 0, 0, 0⟩, ⟨12, 4, 0, 0, 0, 0, 1, 1, 0⟩, ⟨12, 4, 1, 0, 1, 0, 1, 1, 0⟩], [⟨12, 10, 0, 0, 0, 0, 0, 0, 0⟩, ⟨12, 10, 1, 0, 1, 0, 0, 0, 0⟩, ⟨12, 10, 0, 0, 0, 0, 1, 1, 0⟩, ⟨12, 10, 1, 0, 1, 0, 1, 1, 0⟩], [⟨12, 17, 0, 0, 0, 0, 0, 0, 0⟩, ⟨12, 17, 1, 0, 1, 0, 0, 0, 0⟩, ⟨12, 17, 0, 0, 0, 0, 1, 1, 0⟩, ⟨12, 17, 1, 0, 1, 0, 1, 1, 0⟩]],
      [⟨12, 10, 0, 0, 0, 0, 0, 0, 3⟩, ⟨12, 10, 1, 0, 1, 0, 0, 0, 3⟩, ⟨12, 10, 0, 0, 0, 0, 1, 1, 3⟩, ⟨12, 10, 1, 0, 1, 0, 1, 1, 3⟩]⟩,
    ⟨-1, -1, 12, 10,
      [[⟨12, 2, 0, 0, 0, 0, 0, 0, 0⟩, ⟨12, 2, 1, 0, 1, 0, 0, 0, 0⟩, ⟨12, 2, 0, 0, 0, 0, 1, 1, 0⟩, ⟨12, 2, 1, 0, 1, 0, 1, 1, 0⟩], [⟨12, 3, 0, 0, 0, 0, 0, 0, 0⟩, ⟨12, 3, 1, 0, 1, 0, 0, 0, 0⟩, ⟨12, 3, 0, 0, 0, 0, 1, 1, 0⟩, ⟨12, 3, 1, 0, 1, 0, 1, 1, 0⟩], [⟨12, 16, 0, 0, 0, 0, 0, 0, 0⟩, ⟨12, 16, 1, 0, 1, 0, 0, 0, 0⟩, ⟨12, 16, 0, 0, 0, 0, 1, 1, 0⟩, ⟨12, 16, 1, 0, 1, 0, 1, 1, 0⟩], [⟨12, 17, 0, 0, 0, 0, 0, 0, 0⟩, ⟨12, 17, 1, 0, 1, 0, 0, 0, 0⟩, ⟨12, 17, 0, 0, 0, 0, 1, 1, 0⟩, ⟨12, 17, 1, 0, 1, 0, 1, 1, 0⟩]],
      [⟨12, 2, 0, 0, 0, 0, 0, 0, 3⟩, ⟨12, 2, 1, 0, 1, 0, 0, 0, 3⟩, ⟨12, 2, 0, 0, 0, 0, 1, 1, 3⟩, ⟨12, 2, 1, 0, 1, 0, 1, 1, 3⟩]⟩,
    ⟨-1, -1, 13, 10,
      [[⟨12, 15, 0, 0, 0, 0, 0, 1, 0⟩, ⟨12, 15, 1, 0, 1, 0, 0, 1, 0⟩, ⟨12, 15, 0, 0, 0, 0, 1, 2, 0⟩, ⟨12, 15, 1, 0, 1, 0, 1, 2, 0⟩], [⟨12, 16, 0, 0, 0, 0, 0, 0, 0⟩, ⟨12, 16, 1, 0, 1, 0, 0, 0, 0⟩, ⟨12, 16, 0, 0, 0, 0, 1, 1, 0⟩, ⟨12, 16, 1, 0, 1, 0, 1, 1, 0⟩], [⟨1, 1, 0, 0, 1, 0, 0, 0, 0⟩, ⟨12, 1, 1, 0, 0, 0, 0, 1, 0⟩, ⟨1, 1, 0, 1, 2, 0, 0, 0, 0⟩, ⟨12, 1, 1, 0, 0, 0, 1, 2, 0⟩], [⟨1, 5, 0, 0, 0, 0, 0, 0, 0⟩, ⟨12, 5, 1, 0, 0, 0, 0, 0, 0⟩, ⟨1, 5, 0, 1, 1, 0, 0, 0, 0⟩, ⟨12, 5, 1, 0, 0, 0, 1, 1, 0⟩]],
      [⟨12, 16, 0, 0, 0, 0, 0, 0, 3⟩, ⟨12, 16, 1, 0, 1, 0, 0, 0, 3⟩, ⟨12, 16, 0, 0, 0, 0, 1, 1, 3⟩, ⟨12, 16, 1, 0, 1, 0, 1, 1, 3⟩]⟩,
    ⟨-1, -1, 14, 12,
      [[⟨12, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨12, 0, 1, 0, 1, 0, 0, 1, 0⟩, ⟨12, 0, 0, 0, 0, 0, 1, 2, 0⟩, ⟨12, 0, 1, 0, 1, 0, 1, 2, 0⟩], [⟨12, 15, 0, 0, 0, 0, 0, 1, 0⟩, ⟨12, 15, 1, 0, 1, 0, 0, 1, 0⟩, ⟨12, 15, 0, 0, 0, 0, 1, 2, 0⟩, ⟨12, 15, 1, 0, 1, 0, 1, 2, 0⟩], [⟨12, 4, 0, 0, 0, 0, 0, 0, 0⟩, ⟨12, 4, 1, 0, 1, 0, 0, 0, 0⟩, ⟨12, 4, 0, 0, 0, 0, 1, 1, 0⟩, ⟨12, 4, 1, 0, 1, 0, 1, 1, 0⟩], [⟨12, 17, 0, 0, 0, 0, 0, 0, 0⟩, ⟨12, 17, 1, 0, 1, 0, 0, 0, 0⟩, ⟨12, 17, 0, 0, 0, 0, 1, 1, 0⟩, ⟨12, 17, 1, 0, 1, 0, 1, 1, 0⟩]],
      [⟨12, 15, 0, 0, 0, 0, 0, 1, 3⟩, ⟨12, 15, 1, 0, 1, 0, 0, 1, 3⟩, ⟨12, 15, 0, 0, 0, 0, 1, 2, 3⟩, ⟨12, 15, 1, 0, 1, 0, 1, 2, 3⟩]⟩,
    ⟨-1, -1, 15, 6,
      [[⟨12, 6, 0, 0, 0, 0, 0, 0, 0⟩, ⟨12, 6, 1, 0, 1, 0, 0, 0, 0⟩, ⟨12, 6, 0, 0, 0, 0, 1, 1, 0⟩, ⟨12, 6, 1, 0, 1, 0, 1, 1, 0⟩], [⟨12, 7, 0, 0, 0, 0, 0, 0, 0⟩, ⟨12, 7, 1, 0, 1, 0, 0, 0, 0⟩, ⟨12, 7, 0, 0, 0, 0, 1, 1, 0⟩, ⟨12, 7, 1, 0, 1, 0, 1, 1, 0⟩], [⟨6, 13, 0, 0, 0, 0, 0, 0, 0⟩, ⟨6, 13, 1, 0, 1, 0, 0, 0, 0⟩, ⟨12, 13, 0, 0, 0, 0, 1, 0, 0⟩, ⟨12, 13, 1, 0, 1, 0, 1, 0, 0⟩], [⟨6, 14, 0, 0, 0, 0, 0, 0, 0⟩, ⟨6, 14, 1, 0, 1, 0, 0, 0, 0⟩, ⟨12, 14, 0, 0, 0, 0, 1, 0, 0⟩, ⟨12, 14, 1, 0, 1, 0, 1, 0, 0⟩]],
      [⟨6, 13, 0, 0, 0, 0, 0, 0, 0⟩, ⟨6, 13, 1, 0, 1, 0, 0, 0, 0⟩, ⟨12, 13, 0, 0, 0, 0, 1, 0, 0⟩, ⟨12, 13, 1, 0, 1, 0, 1, 0, 0⟩]⟩,
    ⟨-1, -1, 16, 9,
      [[⟨12, 8, 0, 0, 0, 0, 0, 0, 0⟩, ⟨12, 8, 1, 0, 1, 0, 0, 0, 0⟩, ⟨12, 8, 0, 0, 0, 0, 1, 1, 0⟩, ⟨12, 8, 1, 0, 1, 0, 1, 1, 0⟩], [⟨12, 9, 0, 0, 0, 0, 0, 0, 0⟩, ⟨12, 9, 1, 0, 1, 0, 0, 0, 0⟩, ⟨12, 9, 0, 0, 0, 0, 1, 1, 0⟩, ⟨12, 9, 1, 0, 1, 0, 1, 1, 0⟩], [⟨12, 12, 0, 0, 0, 0, 0, 0, 0⟩, ⟨12, 12, 1, 0, 1, 0, 0, 0, 0⟩, ⟨12, 12, 0, 0, 0, 0, 1, 1, 0⟩, ⟨12, 12, 1, 0, 1, 0, 1, 1, 0⟩], [⟨12, 13, 0, 0, 0, 0, 0, 0, 0⟩, ⟨12, 13, 1, 0, 1, 0, 0, 0, 0⟩, ⟨12, 13, 0, 0, 0, 0, 1, 1, 0⟩, ⟨12, 13, 1, 0, 1, 0, 1, 1, 0⟩]],
      [⟨12, 8, 0, 0, 0, 0, 0, 0, 3⟩, ⟨12, 8, 1, 0, 1, 0, 0, 0, 3⟩, ⟨12, 8, 0, 0, 0, 0, 1, 1, 3⟩, ⟨12, 8, 1, 0, 1, 0, 1, 1, 3⟩]⟩,
    ⟨-1, -1, 17, 11,
      [[⟨12, 10, 0, 0, 0, 0, 0, 0, 0⟩, ⟨12, 10, 1, 0, 1, 0, 0, 0, 0⟩, ⟨12, 10, 0, 0, 0, 0, 1, 1, 0⟩, ⟨12, 10, 1, 0, 1, 0, 1, 1, 0⟩], [⟨12, 11, 0, 0, 0, 0, 0, 0, 0⟩, ⟨12, 11, 1, 0, 1, 0, 0, 0, 0⟩, ⟨12, 11, 0, 0, 0, 0, 1, 1, 0⟩, ⟨12, 11, 1, 0, 1, 0, 1, 1, 0⟩], [⟨12, 12, 0, 0, 0, 0, 0, 0, 0⟩, ⟨12, 12, 1, 0, 1, 0, 0, 0, 0⟩, ⟨12, 12, 0, 0, 0, 0, 1, 1, 0⟩, ⟨12, 12, 1, 0, 1, 0, 1, 1, 0⟩], [⟨12, 14, 0, 0, 0, 0, 0, 0, 0⟩, ⟨12, 14, 1, 0, 1, 0, 0, 0, 0⟩, ⟨12, 14, 0, 0, 0, 0, 1, 1, 0⟩, ⟨12, 14, 1, 0, 1, 0, 1, 1, 0⟩]],
      [⟨12, 12, 0, 0, 0, 0, 0, 0, 3⟩, ⟨12, 12, 1, 0, 1, 0, 0, 0, 3⟩, ⟨12, 12, 0, 0, 0, 0, 1, 1, 3⟩, ⟨12, 12, 1, 0, 1, 0, 1, 1, 3⟩]⟩,
    ⟨-1, -1, 18, 7,
      [[⟨12, 6, 0, 0, 0, 0, 0, 0, 0⟩, ⟨12, 6, 1, 0, 1, 0, 0, 0, 0⟩, ⟨12, 6, 0, 0, 0, 0, 1, 1, 0⟩, ⟨12, 6, 1, 0, 1, 0, 1, 1, 0⟩], [⟨12, 7, 0, 0, 0, 0, 0, 0, 0⟩, ⟨12, 7, 1, 0, 1, 0, 0, 0, 0⟩, ⟨12, 7, 0, 0, 0, 0, 1, 1, 0⟩, ⟨12, 7, 1, 0, 1, 0, 1, 1, 0⟩], [⟨12, 8, 0, 0, 0, 0, 0, 0, 0⟩, ⟨12, 8, 1, 0, 1, 0, 0, 0, 0⟩, ⟨12, 8, 0, 0, 0, 0, 1, 1, 0⟩, ⟨12, 8, 1, 0, 1, 0, 1, 1, 0⟩], [⟨12, 9, 0, 0, 0, 0, 0, 0, 0⟩, ⟨12, 9, 1, 0, 1, 0, 0, 0, 0⟩, ⟨12, 9, 0, 0, 0, 0, 1, 1, 0⟩, ⟨12, 9, 1, 0, 1, 0, 1, 1, 0⟩], [⟨1, 10, 0, 0, 0, 0, 0, 0, 0⟩, ⟨12, 10, 1, 0, 0, 0, 0, 0, 0⟩, ⟨1, 10, 0, 1, 1, 0, 0, 0, 0⟩, ⟨12, 10, 1, 0, 0, 0, 1, 1, 0⟩], [⟨1, 11, 0, 0, 0, 0, 0, 0, 0⟩, ⟨12, 11, 1, 0, 0, 0, 0, 0, 0⟩, ⟨1, 11, 0, 1, 1, 0, 0, 0, 0⟩, ⟨12, 11, 1, 0, 0, 0, 1, 1, 0⟩]],
      [⟨12, 6, 0, 0, 0, 0, 0, 0, 2⟩, ⟨12, 6, 1, 0, 1, 0, 0, 0, 2⟩, ⟨12, 6, 0, 0, 0, 0, 1, 1, 2⟩, ⟨12, 6, 1, 0, 1, 0, 1, 1, 2⟩]⟩]⟩]

def certsData : List (List (List (Bool × ℕ × ℕ))) := [
  [[], [(false, 2, 1), (true, 2, 1)], [(false, 1, 1), (false, 2, 1), (true, 2, 1)], [(false, 1, 1), (true, 2, 1)], [(false, 3, 1), (true, 2, 1)], [(false, 0, 1), (false, 3, 1), (true, 2, 1)], [(false, 0, 1), (true, 2, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 2, 1), (true, 0, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 3, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)]],
  [[(false, 2, 1), (true, 2, 1)], [], [(false, 1, 1), (false, 2, 1), (true, 0, 1)], [(false, 1, 1), (true, 2, 1)], [(false, 2, 1), (true, 2, 1)], [(false, 0, 1), (false, 2, 1), (true, 2, 1)], [(false, 0, 1), (true, 2, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (false, 2, 1), (true, 1, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 2, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)]],
  [[(false, 0, 1), (false, 2, 1), (true, 1, 2)], [(false, 0, 1), (false, 2, 1), (true, 1, 2)], [], [(false, 1, 1), (false, 2, 1), (true, 0, 2)], [(false, 0, 1), (false, 2, 1), (true, 0, 2)], [(false, 2, 1), (true, 2, 1)], [(false, 0, 1), (false, 2, 1), (true, 2, 2)], [(false, 0, 1), (true, 0, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (false, 2, 1), (true, 1, 2)], [(false, 1, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (false, 2, 1), (true, 0, 2)]],
  [[(false, 2, 1), (true, 1, 1)], [(false, 0, 1), (true, 2, 1)], [(false, 0, 1), (false, 2, 1), (true, 1, 1)], [], [(false, 1, 1), (true, 2, 1)], [(false, 0, 1), (false, 2, 1), (true, 0, 1)], [(false, 2, 1), (true, 2, 1)], [(false, 0, 1), (false, 2, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 2, 1), (true, 1, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)]],
  [[(false, 2, 1), (true, 3, 1)], [(false, 2, 1), (true, 2, 1)], [(false, 0, 1), (false, 2, 1), (true, 2, 1)], [(false, 0, 1), (true, 2, 1)], [], [(false, 1, 1), (false, 2, 1), (true, 0, 1)], [(false, 1, 1), (true, 2, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 2, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (false, 2, 1), (true, 1, 1)], [(false, 1, 1), (true, 0, 1)]],
  [[(false, 0, 1), (false, 2, 1), (true, 0, 2)], [(false, 0, 1), (false, 2, 1), (true, 0, 2)], [(false, 2, 1), (true, 2, 1)], [(false, 0, 1), (false, 2, 1), (true, 2, 2)], [(false, 0, 1), (false, 2, 1), (true, 1, 2)], [], [(false, 1, 1), (false, 2, 1), (true, 0, 2)], [(false, 1, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (false, 2, 1), (true, 0, 2)], [(false, 0, 1), (true, 0, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (false, 2, 1), (true, 1, 2)]],
  [[(false, 2, 1), (true, 0, 1)], [(false, 1, 1), (true, 2, 1)], [(false, 0, 1), (false, 2, 1), (true, 0, 1)], [(false, 2, 1), (true, 2, 1)], [(false, 0, 1), (true, 2, 1)], [(false, 0, 1), (false, 2, 1), (true, 1, 1)], [], [(false, 2, 1), (true, 1, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (false, 2, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 1, 1), (true, 1, 1)]],
  [[(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 1, 1), (true, 2, 1)], [], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 0, 1)]],
  [[(false, 0, 1), (true, 2, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 2, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 1, 1), (true, 0, 1)], [], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 1)]],
  [[(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 1)], [(false, 0, 1), (true, 2, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 0, 1)], [], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)]],
  [[(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 1, 1), (true, 2, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 0, 1)], [], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 1)]],
  [[(false, 0, 1), (true, 3, 1)], [(false, 0, 1), (true, 2, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 0, 1)], [], [(false, 0, 1), (true, 1, 1)]],
  [[(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 1)], [(false, 0, 1), (true, 2, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 0, 1)], []]]

def cfg : GalCert.Cfg 19 := ⟨adj, (0, 0, 12), 5, regsData, certsData, 0, 12⟩

theorem hc : cfg.check = true := by decide +kernel

theorem hV : cfg.vbound 14 = true := by decide +kernel

theorem hball : ∀ n, ball n = GalCert.ball cfg.adj cfg.x0 n
  | 0 => rfl
  | n + 1 => by rw [ball, GalCert.ball, hball n]; rfl

theorem ha (n : ℕ) (hn : 1 ≤ n) : a n = (cfg.A n : ℤ) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [a, hball, hball]
  exact GalCert.Cfg.card_step hc k

theorem hrec : ∀ k, (([(1, 11), (-2, 6), (1, 1)] : List (ℤ × ℕ)).map fun p => p.1 * (cfg.A (k + p.2) : ℤ)).sum = 0 :=
  GalCert.Cfg.lin_zero hc hV _ (by decide) (by decide +kernel)

theorem hgfw : ∀ n < 14 + 2 * cfg.L, ((GalCert.csOfS [1, 0, 0, 0, 0, -2, 0, 0, 0, 0, 1] 0).map fun p => p.1 * (cfg.A (n + p.2) : ℤ)).sum = 0 := by
  decide +kernel

theorem hsmall : ∀ n < 11, GalCert.conv a [1, 0, 0, 0, 0, -2, 0, 0, 0, 0, 1] n = ([1, 4, 8, 15, 18, 22, 18, 15, 8, 4, 1] : List ℤ).getD n 0 := by
  have e : a = fun n => if n = 0 then 1 else (cfg.A n : ℤ) := by
    funext n
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; rfl
    · rw [if_neg (by omega)]; exact ha n h
  rw [e]
  decide +kernel

end P312722

open PowerSeries OMA.S_oeis_a312722 in
theorem OMA.solution : type_of% @OMA.S_oeis_a312722.main := by
  refine ⟨?_, ?_⟩
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 11 := ⟨n - 11, by omega⟩
    have h := P312722.hrec k
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at h
    rw [show k + 11 - 5 = k + 6 by omega,
      show k + 11 - 10 = k + 1 by omega,
      P312722.ha (k + 11) (by omega),
      P312722.ha (k + 6) (by omega),
      P312722.ha (k + 1) (by omega)]
    linarith
  · have hD : (X^10 - 2*X^5 + 1 : PowerSeries ℤ) = GalCert.polyOf [1, 0, 0, 0, 0, -2, 0, 0, 0, 0, 1] := by
      simp only [GalCert.polyOf, map_neg, map_one, map_zero, map_ofNat, map_intCast]; ring
    have hP : (X^10 + 4*X^9 + 8*X^8 + 15*X^7 + 18*X^6 + 22*X^5 + 18*X^4 + 15*X^3 + 8*X^2 + 4*X + 1 : PowerSeries ℤ) = GalCert.polyOf [1, 4, 8, 15, 18, 22, 18, 15, 8, 4, 1] := by
      simp only [GalCert.polyOf, map_neg, map_one, map_zero, map_ofNat, map_intCast]; ring
    rw [hD, hP]
    exact GalCert.Cfg.gf_from2 P312722.hc P312722.hV a P312722.ha _ _ 0 11 (by decide) (by decide) P312722.hgfw P312722.hsmall
