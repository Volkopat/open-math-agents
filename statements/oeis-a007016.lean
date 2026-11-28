import Mathlib

/-!
# OEIS A007016: Mathar's recurrence

Source: https://oeis.org/A007016 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (N. J. A. Sloane), offset 0: Number of permutations of length n with 1 fixed and 1 reflected point.
Number of distinct solutions to the order n checkerboard problem, including symmetrical solutions: place n
pieces on an n X n board so there is exactly one piece in each row, column and main diagonal. Compare A064280.
Data: 0, 1, 0, 0, 8, 20, 96, 656, 5568, 48912, 494080, 5383552, ... The formula section states: Conjecture
D-finite with recurrence (365968635435167109808*n^2 -5566069866485493251505*n +20525522573033552369132)*a(n)
+(-1215369044326430542311*n^2 +19103429957352794982854*n -73690801030090785944295)*a(n-1)
+(-365968635435167109808*n^4 +6663975772790994580929*n^3 -35836353442786038818589*n^2
+34878550744402035813586*n +124043542472821007763204)*a(n-2) +(483431773456096322695*n^4
-10754417727097457203127*n^3 +85154149458907095778621*n^2 -277683967994722584206067*n
+286254870342835757751852)*a(n-3) +2*(-393241909113483884738*n^4 +9142334951839265043383*n^3
-78427160779754271402777*n^2 +309283968160862567580813*n -465057422344277141977923)*a(n-4)
+2*(-745044547502580209919*n^4 +21471238686323774026196*n^3 -222067832543690193789255*n^2
+944698954932049830084232*n -1372732531859619119793978)*a(n-5) +4*(365968635435167109808*n^4
-5227374504728642916627*n^3 +19793104565012302929789*n^2 +391834816007939927082*n
-57365695502678698166146)*a(n-6) +4*(-483431773456096322695*n^4 +7592214312314395379733*n^3
-45284933032689911393913*n^2 +117535885088909103449165*n -84799883220517633629252)*a(n-7)
+8*(n-7)*(393241909113483884738*n^3 -4789400677912625536335*n^2 +17834478528905815208536*n
-23668675533486426523455)*a(n-8) +8*(n-7)*(n-8)*(745044547502580209919*n^2 -6086915962816073505121*n
+12854159797389104313178)*a(n-9)=0. - R. J. Mathar, Feb 27 2025

Formalization notes:
* `a n` counts the permutations σ of {0, ..., n-1} with exactly one i such that σ i = i (a fixed point) and
  exactly one i such that σ i = n - 1 - i (a reflected point; `Fin.rev i` = n - 1 - i), the 0-based form of
  σ(i) = i and σ(i) = n + 1 - i on {1, ..., n}. As permutation matrices these are the placements of n pieces
  on an n X n board with one piece in each row and column and exactly one on each of the two main diagonals,
  as the entry's comment says. For odd n the middle point can be fixed and reflected at once and then counts
  for both, which is what gives a(1) = 1.
* The reading reproduces the entry's data a(0..9) by brute force over all permutations, and a(0..4) = 0, 1, 0,
  0, 8 also follow from the definition by kernel evaluation.
* The site's excerpt of the conjecture stops inside the a(n-6) term; the entry's formula section gives the
  whole recurrence, through the a(n-9) term, and main states all of it. The recurrence holds on the entry's
  terms a(9..21).
* The recurrence is stated in the integers for every n ≥ 9, the first n for which a(n-9) is a term (offset 0).
-/

namespace OMA.S_oeis_a007016

/-- A007016(n): the permutations σ of {0, ..., n-1} with exactly one fixed point (σ i = i) and exactly one
reflected point (σ i = n - 1 - i, which is `Fin.rev i`). -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
    (Finset.univ.filter (fun i => σ i = i)).card = 1 ∧
      (Finset.univ.filter (fun i => σ i = Fin.rev i)).card = 1)).card

/-- Mathar's conjectured recurrence. -/
theorem main :
    ∀ n : ℕ, 9 ≤ n →
    (365968635435167109808 * (n : ℤ) ^ 2 - 5566069866485493251505 * (n : ℤ)
        + 20525522573033552369132) * (a n : ℤ) +
      (-1215369044326430542311 * (n : ℤ) ^ 2 + 19103429957352794982854 * (n : ℤ)
        - 73690801030090785944295) * (a (n - 1) : ℤ) +
      (-365968635435167109808 * (n : ℤ) ^ 4 + 6663975772790994580929 * (n : ℤ) ^ 3
        - 35836353442786038818589 * (n : ℤ) ^ 2 + 34878550744402035813586 * (n : ℤ)
        + 124043542472821007763204) * (a (n - 2) : ℤ) +
      (483431773456096322695 * (n : ℤ) ^ 4 - 10754417727097457203127 * (n : ℤ) ^ 3
        + 85154149458907095778621 * (n : ℤ) ^ 2 - 277683967994722584206067 * (n : ℤ)
        + 286254870342835757751852) * (a (n - 3) : ℤ) +
      2 * (-393241909113483884738 * (n : ℤ) ^ 4 + 9142334951839265043383 * (n : ℤ) ^ 3
        - 78427160779754271402777 * (n : ℤ) ^ 2 + 309283968160862567580813 * (n : ℤ)
        - 465057422344277141977923) * (a (n - 4) : ℤ) +
      2 * (-745044547502580209919 * (n : ℤ) ^ 4 + 21471238686323774026196 * (n : ℤ) ^ 3
        - 222067832543690193789255 * (n : ℤ) ^ 2 + 944698954932049830084232 * (n : ℤ)
        - 1372732531859619119793978) * (a (n - 5) : ℤ) +
      4 * (365968635435167109808 * (n : ℤ) ^ 4 - 5227374504728642916627 * (n : ℤ) ^ 3
        + 19793104565012302929789 * (n : ℤ) ^ 2 + 391834816007939927082 * (n : ℤ)
        - 57365695502678698166146) * (a (n - 6) : ℤ) +
      4 * (-483431773456096322695 * (n : ℤ) ^ 4 + 7592214312314395379733 * (n : ℤ) ^ 3
        - 45284933032689911393913 * (n : ℤ) ^ 2 + 117535885088909103449165 * (n : ℤ)
        - 84799883220517633629252) * (a (n - 7) : ℤ) +
      8 * ((n : ℤ) - 7) * (393241909113483884738 * (n : ℤ) ^ 3 - 4789400677912625536335 * (n : ℤ) ^ 2
        + 17834478528905815208536 * (n : ℤ) - 23668675533486426523455) * (a (n - 8) : ℤ) +
      8 * ((n : ℤ) - 7) * ((n : ℤ) - 8) * (745044547502580209919 * (n : ℤ) ^ 2
        - 6086915962816073505121 * (n : ℤ) + 12854159797389104313178) * (a (n - 9) : ℤ) = 0 := by
  sorry

end OMA.S_oeis_a007016
