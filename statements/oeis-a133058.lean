import Mathlib

/-!
# OEIS A133058: the Fly straight, dammit recurrence

a(0) = a(1) = 1; for n > 1, a(n) = a(n-1) + n + 1 if a(n-1) and n
are coprime, otherwise a(n) = a(n-1)/gcd(a(n-1),n). The comments on
this sequence carry several distinct claims; `main` is the one that
was actually proved.

Source: https://oeis.org/A133058

## The multi-part comment

Zizka, Oct 27 2015: *It is conjectured that quasi-periodic
sequences exist only for R = 0, 1, 2 or 3 in a(n) = a(n-1) + n + R
and that for R >= 4 the recurrence is not quasi-periodic. For
R = 0, 1, 2 all starting values give a quasi-periodic sequence. The
respective loop is (1, x) for R = 0, (1, x, 2x, 2) for R = 1 (this
sequence), (1, x, 2x, x) or (2x, x) for R = 2. For R = 3 only some
starting values converge to a 6-loop (4x+2, 2x+1, 3x+6, x+2, 2x+9,
3x+17).*

Other claims on the same page: Sloane observes *Remarkably, at
n = 638 the sequence settles down and becomes quasi-periodic*;
Zizka conjectures the universal form *For every choice of initial
term a(0) there exist integers r and t >= 0 such that
a(2r+4t+0) = 1, a(2r+4t+1) = 2r+4t+3, a(2r+4t+2) = 2*(2r+4t+3),
a(2r+4t+3) = 2*; and Sloane restates it as *if at some point we
find a(2k) = 1, then from that point on the sequence looks like
(1, x, 2x, 2), ... where x = 2k+3*, noting that he has not seen a
proof that this must always happen.

## What `main` states

`main` is the quasi-periodicity of THIS sequence, canonical seeds
a(0) = a(1) = 1: the loop (1, x, 2x, 2) entered at index 638, with
x = 641 + 4t. That is Sloane's 638 observation plus the Zizka loop
formula instantiated at the canonical trajectory (r = 319): for
every t, the block of indices 638+4t .. 641+4t equals
(1, 641+4t, 2*(641+4t), 2). It is the INTEGRAL target frozen as
SpecPropA133058 in the DemosMathNT spec.

It is NOT:
* the first sentence of the Zizka R-comment (quasi-periodic
  sequences exist only for R = 0, 1, 2, 3), a claim about a whole
  family of recurrences parametrised by R, which stays open;
* the universal Zizka conjecture (every starting value eventually
  reaches a loop), explicitly flagged by Sloane as unproved and
  kept out of scope by the spec.

## Encoding of quasi-periodic

Quasi-periodic does NOT mean eventually periodic: the values are
unbounded, a(639 + 4t) = 641 + 4t grows without bound. The OEIS
sense here is that each residue class mod 4 follows a closed
formula - the loop (1, x, 2x, 2) - which is exactly what the four
equations of `main` assert. The division a(n-1)/g is exact
(g always divides a(n-1)), so Nat division is faithful.
-/

namespace OMA.S_oeis_a133058

/-- One step of the recurrence: `a(n)` computed from `v = a(n-1)`
is `v + n + 1` when `gcd(v, n) = 1`, else `v / gcd(v, n)`. -/
def aStep133058 (v n : ℕ) : ℕ :=
  if Nat.gcd v n = 1 then v + n + 1 else v / Nat.gcd v n

/-- The sequence A133058: seeds `a(0) = a(1) = 1` stipulated, then
`a(n) = aStep133058 (a(n-1)) n` for `n >= 2`. -/
def a133058 : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 2 => aStep133058 (a133058 (n + 1)) (n + 2)

/-- The quasi-periodic loop from index 638: for every `t`, the
block of four terms at indices `638 + 4t .. 641 + 4t` equals
`(1, 641 + 4t, 2*(641 + 4t), 2)`. -/
theorem main : ∀ t : ℕ,
    a133058 (638 + 4 * t) = 1 ∧ a133058 (639 + 4 * t) = 641 + 4 * t ∧
    a133058 (640 + 4 * t) = 2 * (641 + 4 * t) ∧
    a133058 (641 + 4 * t) = 2 := by
  sorry

end OMA.S_oeis_a133058
