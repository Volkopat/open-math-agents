import OMAReductions.R_OeisA247824_conjecture_2_R2

/-!
# The 82 residual ranks from OEIS A247824

For each slope the relative ranks in its short interval are fixed. A candidate
would force one starting prime count. All forbidden values for this slope miss
the specified common residue. The first six residues already have independent
prime-count certificates. The last two residues are the remaining global tests.
-/

namespace OMA.R_OeisA247824_conjecture_2_R2_H4_R2

private theorem no_match (count : ℕ → ℕ) {e q a delta required modulus residue : ℕ}
    (arg : (e%32)*(e/32+1322164)-20868473=q) (index : e/32=required+delta)
    (window : count q=count a+delta)
    (observed : count a % modulus = residue)
    (different : required % modulus ≠ residue) :
    count ((e%32)*(e/32+1322164)-20868473) ≠ e/32 := by
  intro equality
  rw [arg,window,index] at equality
  have forced := Nat.add_right_cancel equality
  exact different (forced ▸ observed)

private theorem cons_cases {P : ℕ → Prop} {a : ℕ} {rest : List ℕ}
    (head : P a) (tail : ∀ e ∈ rest, P e) : ∀ e ∈ a::rest, P e := by
  intro e he
  rcases List.mem_cons.mp he with eq|more
  · exact eq ▸ head
  · exact tail e more

set_option maxRecDepth 6000 in
set_option maxHeartbeats 3500000 in
private theorem exclusions (count : ℕ → ℕ)
    (r17 : count 94085731 % 6 = 0)
    (r19 : count 590237761 % 7 = 5)
    (r22 : count 10425579253 % 11 = 8)
    (r23 : count 28006150079 % 3 = 2)
    (r25 : count 204778727327 % 5 = 0)
    (r26 : count 555157672301 % 6 = 4)
    (r29 : count 11092009835083 % 9 = 7)
    (r30 : count 30110134441897 % 5 = 3)
    (w17 : ∀ t ∈ ([
    (94085731,0), (94085833,7), (94085867,9), (94086479,43),
    (94086547,49), (94086649,54), (94086683,59), (94087771,118),
    (94088587,175), (94088927,198), (94089029,206), (94089131,209),
    (94089199,214), (94089607,235), (94090151,263), (94090253,271),
    (94090559,289), (94090627,293), (94091069,317)] : List (ℕ × ℕ)),
    count t.1 = count 94085731 + t.2)
    (w19 : ∀ t ∈ ([
    (590237761,0), (590238217,23), (590238749,52), (590238863,59),
    (590239129,78), (590239319,90), (590240041,122), (590240269,131)] : List (ℕ × ℕ)),
    count t.1 = count 590237761 + t.2)
    (w22 : ∀ t ∈ ([
    (10425579253,0), (10425579473,16), (10425579539,19), (10425579781,29),
    (10425579803,31), (10425579869,34), (10425580177,49), (10425580397,60),
    (10425580441,63), (10425580859,75), (10425580969,81), (10425581123,91),
    (10425581321,102), (10425581497,106), (10425581849,120), (10425582487,147),
    (10425582509,149), (10425582641,155), (10425582949,172), (10425582971,174),
    (10425583213,181)] : List (ℕ × ℕ)),
    count t.1 = count 10425579253 + t.2)
    (w23 : ∀ t ∈ ([
    (28006150079,0)] : List (ℕ × ℕ)),
    count t.1 = count 28006150079 + t.2)
    (w25 : ∀ t ∈ ([
    (204778727327,0), (204778727627,12), (204778727677,15), (204778727977,28),
    (204778728127,34), (204778728577,51), (204778728677,56), (204778729427,83)] : List (ℕ × ℕ)),
    count t.1 = count 204778727327 + t.2)
    (w26 : ∀ t ∈ ([
    (555157672301,0), (555157672717,18), (555157673003,26), (555157673159,34),
    (555157673237,36), (555157673263,37)] : List (ℕ × ℕ)),
    count t.1 = count 555157672301 + t.2)
    (w29 : ∀ t ∈ ([
    (11092009835083,0), (11092009835779,30), (11092009837229,85), (11092009837577,98),
    (11092009838389,129), (11092009838737,140), (11092009839259,153), (11092009839433,160),
    (11092009840651,207), (11092009841347,236), (11092009842449,275), (11092009842971,290),
    (11092009843087,294), (11092009843609,311), (11092009845407,359)] : List (ℕ × ℕ)),
    count t.1 = count 11092009835083 + t.2)
    (w30 : ∀ t ∈ ([
    (30110134441897,0), (30110134442137,12), (30110134442287,16), (30110134442767,35)] : List (ℕ × ℕ)),
    count t.1 = count 30110134441897 + t.2) :
    ∀ e ∈ ([
    174075153, 174075345, 174075409, 174076561, 174076689,
    174076881, 174076945, 174078993, 174080529, 174081169,
    174081361, 174081553, 174081681, 174082449, 174083473,
    174083665, 174084241, 174084369, 174085201, 986922323,
    986923091, 986923987, 986924179, 986924627, 986924947,
    986926163, 986926547, 15152523830, 15152524150, 15152524246,
    15152524598, 15152524630, 15152524726, 15152525174, 15152525494,
    15152525558, 15152526166, 15152526326, 15152526550, 15152526838,
    15152527094, 15152527606, 15152528534, 15152528566, 15152528758,
    15152529206, 15152529238, 15152529590, 38951803543, 262101173401,
    262101173785, 262101173849, 262101174233, 262101174425, 262101175001,
    262101175129, 262101176089, 683254356346, 683254356858, 683254357210,
    683254357402, 683254357498, 683254357530, 12239439846429, 12239439847197,
    12239439848797, 12239439849181, 12239439850077, 12239439850461, 12239439851037,
    12239439851229, 12239439852573, 12239439853341, 12239439854557, 12239439855133,
    12239439855261, 12239439855837, 12239439857821, 32117456688510, 32117456688766,
    32117456688926, 32117456689438] : List ℕ),
      count ((e%32)*(e/32+1322164)-20868473) ≠ e/32 := by
  let claim : ℕ → Prop := fun e : ℕ => count ((e%32)*(e/32+1322164)-20868473) ≠ e/32
  have case0 : claim 174075153 :=
    no_match count (e:=174075153) (q:=94085731) (a:=94085731) (delta:=0) (required:=5439848)
      (modulus:=6) (residue:=0) rfl rfl
      (w17 (94085731,0) (by decide)) r17 (by decide)
  have case1 : claim 174075345 :=
    no_match count (e:=174075345) (q:=94085833) (a:=94085731) (delta:=7) (required:=5439847)
      (modulus:=6) (residue:=0) rfl rfl
      (w17 (94085833,7) (by decide)) r17 (by decide)
  have case2 : claim 174075409 :=
    no_match count (e:=174075409) (q:=94085867) (a:=94085731) (delta:=9) (required:=5439847)
      (modulus:=6) (residue:=0) rfl rfl
      (w17 (94085867,9) (by decide)) r17 (by decide)
  have case3 : claim 174076561 :=
    no_match count (e:=174076561) (q:=94086479) (a:=94085731) (delta:=43) (required:=5439849)
      (modulus:=6) (residue:=0) rfl rfl
      (w17 (94086479,43) (by decide)) r17 (by decide)
  have case4 : claim 174076689 :=
    no_match count (e:=174076689) (q:=94086547) (a:=94085731) (delta:=49) (required:=5439847)
      (modulus:=6) (residue:=0) rfl rfl
      (w17 (94086547,49) (by decide)) r17 (by decide)
  have case5 : claim 174076881 :=
    no_match count (e:=174076881) (q:=94086649) (a:=94085731) (delta:=54) (required:=5439848)
      (modulus:=6) (residue:=0) rfl rfl
      (w17 (94086649,54) (by decide)) r17 (by decide)
  have case6 : claim 174076945 :=
    no_match count (e:=174076945) (q:=94086683) (a:=94085731) (delta:=59) (required:=5439845)
      (modulus:=6) (residue:=0) rfl rfl
      (w17 (94086683,59) (by decide)) r17 (by decide)
  have case7 : claim 174078993 :=
    no_match count (e:=174078993) (q:=94087771) (a:=94085731) (delta:=118) (required:=5439850)
      (modulus:=6) (residue:=0) rfl rfl
      (w17 (94087771,118) (by decide)) r17 (by decide)
  have case8 : claim 174080529 :=
    no_match count (e:=174080529) (q:=94088587) (a:=94085731) (delta:=175) (required:=5439841)
      (modulus:=6) (residue:=0) rfl rfl
      (w17 (94088587,175) (by decide)) r17 (by decide)
  have case9 : claim 174081169 :=
    no_match count (e:=174081169) (q:=94088927) (a:=94085731) (delta:=198) (required:=5439838)
      (modulus:=6) (residue:=0) rfl rfl
      (w17 (94088927,198) (by decide)) r17 (by decide)
  have case10 : claim 174081361 :=
    no_match count (e:=174081361) (q:=94089029) (a:=94085731) (delta:=206) (required:=5439836)
      (modulus:=6) (residue:=0) rfl rfl
      (w17 (94089029,206) (by decide)) r17 (by decide)
  have case11 : claim 174081553 :=
    no_match count (e:=174081553) (q:=94089131) (a:=94085731) (delta:=209) (required:=5439839)
      (modulus:=6) (residue:=0) rfl rfl
      (w17 (94089131,209) (by decide)) r17 (by decide)
  have case12 : claim 174081681 :=
    no_match count (e:=174081681) (q:=94089199) (a:=94085731) (delta:=214) (required:=5439838)
      (modulus:=6) (residue:=0) rfl rfl
      (w17 (94089199,214) (by decide)) r17 (by decide)
  have case13 : claim 174082449 :=
    no_match count (e:=174082449) (q:=94089607) (a:=94085731) (delta:=235) (required:=5439841)
      (modulus:=6) (residue:=0) rfl rfl
      (w17 (94089607,235) (by decide)) r17 (by decide)
  have case14 : claim 174083473 :=
    no_match count (e:=174083473) (q:=94090151) (a:=94085731) (delta:=263) (required:=5439845)
      (modulus:=6) (residue:=0) rfl rfl
      (w17 (94090151,263) (by decide)) r17 (by decide)
  have case15 : claim 174083665 :=
    no_match count (e:=174083665) (q:=94090253) (a:=94085731) (delta:=271) (required:=5439843)
      (modulus:=6) (residue:=0) rfl rfl
      (w17 (94090253,271) (by decide)) r17 (by decide)
  have case16 : claim 174084241 :=
    no_match count (e:=174084241) (q:=94090559) (a:=94085731) (delta:=289) (required:=5439843)
      (modulus:=6) (residue:=0) rfl rfl
      (w17 (94090559,289) (by decide)) r17 (by decide)
  have case17 : claim 174084369 :=
    no_match count (e:=174084369) (q:=94090627) (a:=94085731) (delta:=293) (required:=5439843)
      (modulus:=6) (residue:=0) rfl rfl
      (w17 (94090627,293) (by decide)) r17 (by decide)
  have case18 : claim 174085201 :=
    no_match count (e:=174085201) (q:=94091069) (a:=94085731) (delta:=317) (required:=5439845)
      (modulus:=6) (residue:=0) rfl rfl
      (w17 (94091069,317) (by decide)) r17 (by decide)
  have case19 : claim 986922323 :=
    no_match count (e:=986922323) (q:=590237761) (a:=590237761) (delta:=0) (required:=30841322)
      (modulus:=7) (residue:=5) rfl rfl
      (w19 (590237761,0) (by decide)) r19 (by decide)
  have case20 : claim 986923091 :=
    no_match count (e:=986923091) (q:=590238217) (a:=590237761) (delta:=23) (required:=30841323)
      (modulus:=7) (residue:=5) rfl rfl
      (w19 (590238217,23) (by decide)) r19 (by decide)
  have case21 : claim 986923987 :=
    no_match count (e:=986923987) (q:=590238749) (a:=590237761) (delta:=52) (required:=30841322)
      (modulus:=7) (residue:=5) rfl rfl
      (w19 (590238749,52) (by decide)) r19 (by decide)
  have case22 : claim 986924179 :=
    no_match count (e:=986924179) (q:=590238863) (a:=590237761) (delta:=59) (required:=30841321)
      (modulus:=7) (residue:=5) rfl rfl
      (w19 (590238863,59) (by decide)) r19 (by decide)
  have case23 : claim 986924627 :=
    no_match count (e:=986924627) (q:=590239129) (a:=590237761) (delta:=78) (required:=30841316)
      (modulus:=7) (residue:=5) rfl rfl
      (w19 (590239129,78) (by decide)) r19 (by decide)
  have case24 : claim 986924947 :=
    no_match count (e:=986924947) (q:=590239319) (a:=590237761) (delta:=90) (required:=30841314)
      (modulus:=7) (residue:=5) rfl rfl
      (w19 (590239319,90) (by decide)) r19 (by decide)
  have case25 : claim 986926163 :=
    no_match count (e:=986926163) (q:=590240041) (a:=590237761) (delta:=122) (required:=30841320)
      (modulus:=7) (residue:=5) rfl rfl
      (w19 (590240041,122) (by decide)) r19 (by decide)
  have case26 : claim 986926547 :=
    no_match count (e:=986926547) (q:=590240269) (a:=590237761) (delta:=131) (required:=30841323)
      (modulus:=7) (residue:=5) rfl rfl
      (w19 (590240269,131) (by decide)) r19 (by decide)
  have case27 : claim 15152523830 :=
    no_match count (e:=15152523830) (q:=10425579253) (a:=10425579253) (delta:=0) (required:=473516369)
      (modulus:=11) (residue:=8) rfl rfl
      (w22 (10425579253,0) (by decide)) r22 (by decide)
  have case28 : claim 15152524150 :=
    no_match count (e:=15152524150) (q:=10425579473) (a:=10425579253) (delta:=16) (required:=473516363)
      (modulus:=11) (residue:=8) rfl rfl
      (w22 (10425579473,16) (by decide)) r22 (by decide)
  have case29 : claim 15152524246 :=
    no_match count (e:=15152524246) (q:=10425579539) (a:=10425579253) (delta:=19) (required:=473516363)
      (modulus:=11) (residue:=8) rfl rfl
      (w22 (10425579539,19) (by decide)) r22 (by decide)
  have case30 : claim 15152524598 :=
    no_match count (e:=15152524598) (q:=10425579781) (a:=10425579253) (delta:=29) (required:=473516364)
      (modulus:=11) (residue:=8) rfl rfl
      (w22 (10425579781,29) (by decide)) r22 (by decide)
  have case31 : claim 15152524630 :=
    no_match count (e:=15152524630) (q:=10425579803) (a:=10425579253) (delta:=31) (required:=473516363)
      (modulus:=11) (residue:=8) rfl rfl
      (w22 (10425579803,31) (by decide)) r22 (by decide)
  have case32 : claim 15152524726 :=
    no_match count (e:=15152524726) (q:=10425579869) (a:=10425579253) (delta:=34) (required:=473516363)
      (modulus:=11) (residue:=8) rfl rfl
      (w22 (10425579869,34) (by decide)) r22 (by decide)
  have case33 : claim 15152525174 :=
    no_match count (e:=15152525174) (q:=10425580177) (a:=10425579253) (delta:=49) (required:=473516362)
      (modulus:=11) (residue:=8) rfl rfl
      (w22 (10425580177,49) (by decide)) r22 (by decide)
  have case34 : claim 15152525494 :=
    no_match count (e:=15152525494) (q:=10425580397) (a:=10425579253) (delta:=60) (required:=473516361)
      (modulus:=11) (residue:=8) rfl rfl
      (w22 (10425580397,60) (by decide)) r22 (by decide)
  have case35 : claim 15152525558 :=
    no_match count (e:=15152525558) (q:=10425580441) (a:=10425579253) (delta:=63) (required:=473516360)
      (modulus:=11) (residue:=8) rfl rfl
      (w22 (10425580441,63) (by decide)) r22 (by decide)
  have case36 : claim 15152526166 :=
    no_match count (e:=15152526166) (q:=10425580859) (a:=10425579253) (delta:=75) (required:=473516367)
      (modulus:=11) (residue:=8) rfl rfl
      (w22 (10425580859,75) (by decide)) r22 (by decide)
  have case37 : claim 15152526326 :=
    no_match count (e:=15152526326) (q:=10425580969) (a:=10425579253) (delta:=81) (required:=473516366)
      (modulus:=11) (residue:=8) rfl rfl
      (w22 (10425580969,81) (by decide)) r22 (by decide)
  have case38 : claim 15152526550 :=
    no_match count (e:=15152526550) (q:=10425581123) (a:=10425579253) (delta:=91) (required:=473516363)
      (modulus:=11) (residue:=8) rfl rfl
      (w22 (10425581123,91) (by decide)) r22 (by decide)
  have case39 : claim 15152526838 :=
    no_match count (e:=15152526838) (q:=10425581321) (a:=10425579253) (delta:=102) (required:=473516361)
      (modulus:=11) (residue:=8) rfl rfl
      (w22 (10425581321,102) (by decide)) r22 (by decide)
  have case40 : claim 15152527094 :=
    no_match count (e:=15152527094) (q:=10425581497) (a:=10425579253) (delta:=106) (required:=473516365)
      (modulus:=11) (residue:=8) rfl rfl
      (w22 (10425581497,106) (by decide)) r22 (by decide)
  have case41 : claim 15152527606 :=
    no_match count (e:=15152527606) (q:=10425581849) (a:=10425579253) (delta:=120) (required:=473516367)
      (modulus:=11) (residue:=8) rfl rfl
      (w22 (10425581849,120) (by decide)) r22 (by decide)
  have case42 : claim 15152528534 :=
    no_match count (e:=15152528534) (q:=10425582487) (a:=10425579253) (delta:=147) (required:=473516369)
      (modulus:=11) (residue:=8) rfl rfl
      (w22 (10425582487,147) (by decide)) r22 (by decide)
  have case43 : claim 15152528566 :=
    no_match count (e:=15152528566) (q:=10425582509) (a:=10425579253) (delta:=149) (required:=473516368)
      (modulus:=11) (residue:=8) rfl rfl
      (w22 (10425582509,149) (by decide)) r22 (by decide)
  have case44 : claim 15152528758 :=
    no_match count (e:=15152528758) (q:=10425582641) (a:=10425579253) (delta:=155) (required:=473516368)
      (modulus:=11) (residue:=8) rfl rfl
      (w22 (10425582641,155) (by decide)) r22 (by decide)
  have case45 : claim 15152529206 :=
    no_match count (e:=15152529206) (q:=10425582949) (a:=10425579253) (delta:=172) (required:=473516365)
      (modulus:=11) (residue:=8) rfl rfl
      (w22 (10425582949,172) (by decide)) r22 (by decide)
  have case46 : claim 15152529238 :=
    no_match count (e:=15152529238) (q:=10425582971) (a:=10425579253) (delta:=174) (required:=473516364)
      (modulus:=11) (residue:=8) rfl rfl
      (w22 (10425582971,174) (by decide)) r22 (by decide)
  have case47 : claim 15152529590 :=
    no_match count (e:=15152529590) (q:=10425583213) (a:=10425579253) (delta:=181) (required:=473516368)
      (modulus:=11) (residue:=8) rfl rfl
      (w22 (10425583213,181) (by decide)) r22 (by decide)
  have case48 : claim 38951803543 :=
    no_match count (e:=38951803543) (q:=28006150079) (a:=28006150079) (delta:=0) (required:=1217243860)
      (modulus:=3) (residue:=2) rfl rfl
      (w23 (28006150079,0) (by decide)) r23 (by decide)
  have case49 : claim 262101173401 :=
    no_match count (e:=262101173401) (q:=204778727327) (a:=204778727327) (delta:=0) (required:=8190661668)
      (modulus:=5) (residue:=0) rfl rfl
      (w25 (204778727327,0) (by decide)) r25 (by decide)
  have case50 : claim 262101173785 :=
    no_match count (e:=262101173785) (q:=204778727627) (a:=204778727327) (delta:=12) (required:=8190661668)
      (modulus:=5) (residue:=0) rfl rfl
      (w25 (204778727627,12) (by decide)) r25 (by decide)
  have case51 : claim 262101173849 :=
    no_match count (e:=262101173849) (q:=204778727677) (a:=204778727327) (delta:=15) (required:=8190661667)
      (modulus:=5) (residue:=0) rfl rfl
      (w25 (204778727677,15) (by decide)) r25 (by decide)
  have case52 : claim 262101174233 :=
    no_match count (e:=262101174233) (q:=204778727977) (a:=204778727327) (delta:=28) (required:=8190661666)
      (modulus:=5) (residue:=0) rfl rfl
      (w25 (204778727977,28) (by decide)) r25 (by decide)
  have case53 : claim 262101174425 :=
    no_match count (e:=262101174425) (q:=204778728127) (a:=204778727327) (delta:=34) (required:=8190661666)
      (modulus:=5) (residue:=0) rfl rfl
      (w25 (204778728127,34) (by decide)) r25 (by decide)
  have case54 : claim 262101175001 :=
    no_match count (e:=262101175001) (q:=204778728577) (a:=204778727327) (delta:=51) (required:=8190661667)
      (modulus:=5) (residue:=0) rfl rfl
      (w25 (204778728577,51) (by decide)) r25 (by decide)
  have case55 : claim 262101175129 :=
    no_match count (e:=262101175129) (q:=204778728677) (a:=204778727327) (delta:=56) (required:=8190661666)
      (modulus:=5) (residue:=0) rfl rfl
      (w25 (204778728677,56) (by decide)) r25 (by decide)
  have case56 : claim 262101176089 :=
    no_match count (e:=262101176089) (q:=204778729427) (a:=204778727327) (delta:=83) (required:=8190661669)
      (modulus:=5) (residue:=0) rfl rfl
      (w25 (204778729427,83) (by decide)) r25 (by decide)
  have case57 : claim 683254356346 :=
    no_match count (e:=683254356346) (q:=555157672301) (a:=555157672301) (delta:=0) (required:=21351698635)
      (modulus:=6) (residue:=4) rfl rfl
      (w26 (555157672301,0) (by decide)) r26 (by decide)
  have case58 : claim 683254356858 :=
    no_match count (e:=683254356858) (q:=555157672717) (a:=555157672301) (delta:=18) (required:=21351698633)
      (modulus:=6) (residue:=4) rfl rfl
      (w26 (555157672717,18) (by decide)) r26 (by decide)
  have case59 : claim 683254357210 :=
    no_match count (e:=683254357210) (q:=555157673003) (a:=555157672301) (delta:=26) (required:=21351698636)
      (modulus:=6) (residue:=4) rfl rfl
      (w26 (555157673003,26) (by decide)) r26 (by decide)
  have case60 : claim 683254357402 :=
    no_match count (e:=683254357402) (q:=555157673159) (a:=555157672301) (delta:=34) (required:=21351698634)
      (modulus:=6) (residue:=4) rfl rfl
      (w26 (555157673159,34) (by decide)) r26 (by decide)
  have case61 : claim 683254357498 :=
    no_match count (e:=683254357498) (q:=555157673237) (a:=555157672301) (delta:=36) (required:=21351698635)
      (modulus:=6) (residue:=4) rfl rfl
      (w26 (555157673237,36) (by decide)) r26 (by decide)
  have case62 : claim 683254357530 :=
    no_match count (e:=683254357530) (q:=555157673263) (a:=555157672301) (delta:=37) (required:=21351698635)
      (modulus:=6) (residue:=4) rfl rfl
      (w26 (555157673263,37) (by decide)) r26 (by decide)
  have case63 : claim 12239439846429 :=
    no_match count (e:=12239439846429) (q:=11092009835083) (a:=11092009835083) (delta:=0) (required:=382482495200)
      (modulus:=9) (residue:=7) rfl rfl
      (w29 (11092009835083,0) (by decide)) r29 (by decide)
  have case64 : claim 12239439847197 :=
    no_match count (e:=12239439847197) (q:=11092009835779) (a:=11092009835083) (delta:=30) (required:=382482495194)
      (modulus:=9) (residue:=7) rfl rfl
      (w29 (11092009835779,30) (by decide)) r29 (by decide)
  have case65 : claim 12239439848797 :=
    no_match count (e:=12239439848797) (q:=11092009837229) (a:=11092009835083) (delta:=85) (required:=382482495189)
      (modulus:=9) (residue:=7) rfl rfl
      (w29 (11092009837229,85) (by decide)) r29 (by decide)
  have case66 : claim 12239439849181 :=
    no_match count (e:=12239439849181) (q:=11092009837577) (a:=11092009835083) (delta:=98) (required:=382482495188)
      (modulus:=9) (residue:=7) rfl rfl
      (w29 (11092009837577,98) (by decide)) r29 (by decide)
  have case67 : claim 12239439850077 :=
    no_match count (e:=12239439850077) (q:=11092009838389) (a:=11092009835083) (delta:=129) (required:=382482495185)
      (modulus:=9) (residue:=7) rfl rfl
      (w29 (11092009838389,129) (by decide)) r29 (by decide)
  have case68 : claim 12239439850461 :=
    no_match count (e:=12239439850461) (q:=11092009838737) (a:=11092009835083) (delta:=140) (required:=382482495186)
      (modulus:=9) (residue:=7) rfl rfl
      (w29 (11092009838737,140) (by decide)) r29 (by decide)
  have case69 : claim 12239439851037 :=
    no_match count (e:=12239439851037) (q:=11092009839259) (a:=11092009835083) (delta:=153) (required:=382482495191)
      (modulus:=9) (residue:=7) rfl rfl
      (w29 (11092009839259,153) (by decide)) r29 (by decide)
  have case70 : claim 12239439851229 :=
    no_match count (e:=12239439851229) (q:=11092009839433) (a:=11092009835083) (delta:=160) (required:=382482495190)
      (modulus:=9) (residue:=7) rfl rfl
      (w29 (11092009839433,160) (by decide)) r29 (by decide)
  have case71 : claim 12239439852573 :=
    no_match count (e:=12239439852573) (q:=11092009840651) (a:=11092009835083) (delta:=207) (required:=382482495185)
      (modulus:=9) (residue:=7) rfl rfl
      (w29 (11092009840651,207) (by decide)) r29 (by decide)
  have case72 : claim 12239439853341 :=
    no_match count (e:=12239439853341) (q:=11092009841347) (a:=11092009835083) (delta:=236) (required:=382482495180)
      (modulus:=9) (residue:=7) rfl rfl
      (w29 (11092009841347,236) (by decide)) r29 (by decide)
  have case73 : claim 12239439854557 :=
    no_match count (e:=12239439854557) (q:=11092009842449) (a:=11092009835083) (delta:=275) (required:=382482495179)
      (modulus:=9) (residue:=7) rfl rfl
      (w29 (11092009842449,275) (by decide)) r29 (by decide)
  have case74 : claim 12239439855133 :=
    no_match count (e:=12239439855133) (q:=11092009842971) (a:=11092009835083) (delta:=290) (required:=382482495182)
      (modulus:=9) (residue:=7) rfl rfl
      (w29 (11092009842971,290) (by decide)) r29 (by decide)
  have case75 : claim 12239439855261 :=
    no_match count (e:=12239439855261) (q:=11092009843087) (a:=11092009835083) (delta:=294) (required:=382482495182)
      (modulus:=9) (residue:=7) rfl rfl
      (w29 (11092009843087,294) (by decide)) r29 (by decide)
  have case76 : claim 12239439855837 :=
    no_match count (e:=12239439855837) (q:=11092009843609) (a:=11092009835083) (delta:=311) (required:=382482495183)
      (modulus:=9) (residue:=7) rfl rfl
      (w29 (11092009843609,311) (by decide)) r29 (by decide)
  have case77 : claim 12239439857821 :=
    no_match count (e:=12239439857821) (q:=11092009845407) (a:=11092009835083) (delta:=359) (required:=382482495197)
      (modulus:=9) (residue:=7) rfl rfl
      (w29 (11092009845407,359) (by decide)) r29 (by decide)
  have case78 : claim 32117456688510 :=
    no_match count (e:=32117456688510) (q:=30110134441897) (a:=30110134441897) (delta:=0) (required:=1003670521515)
      (modulus:=5) (residue:=3) rfl rfl
      (w30 (30110134441897,0) (by decide)) r30 (by decide)
  have case79 : claim 32117456688766 :=
    no_match count (e:=32117456688766) (q:=30110134442137) (a:=30110134441897) (delta:=12) (required:=1003670521511)
      (modulus:=5) (residue:=3) rfl rfl
      (w30 (30110134442137,12) (by decide)) r30 (by decide)
  have case80 : claim 32117456688926 :=
    no_match count (e:=32117456688926) (q:=30110134442287) (a:=30110134441897) (delta:=16) (required:=1003670521512)
      (modulus:=5) (residue:=3) rfl rfl
      (w30 (30110134442287,16) (by decide)) r30 (by decide)
  have case81 : claim 32117456689438 :=
    no_match count (e:=32117456689438) (q:=30110134442767) (a:=30110134441897) (delta:=35) (required:=1003670521509)
      (modulus:=5) (residue:=3) rfl rfl
      (w30 (30110134442767,35) (by decide)) r30 (by decide)
  exact cons_cases (P:=claim) case0 (
      cons_cases (P:=claim) case1 (
      cons_cases (P:=claim) case2 (
      cons_cases (P:=claim) case3 (
      cons_cases (P:=claim) case4 (
      cons_cases (P:=claim) case5 (
      cons_cases (P:=claim) case6 (
      cons_cases (P:=claim) case7 (
      cons_cases (P:=claim) case8 (
      cons_cases (P:=claim) case9 (
      cons_cases (P:=claim) case10 (
      cons_cases (P:=claim) case11 (
      cons_cases (P:=claim) case12 (
      cons_cases (P:=claim) case13 (
      cons_cases (P:=claim) case14 (
      cons_cases (P:=claim) case15 (
      cons_cases (P:=claim) case16 (
      cons_cases (P:=claim) case17 (
      cons_cases (P:=claim) case18 (
      cons_cases (P:=claim) case19 (
      cons_cases (P:=claim) case20 (
      cons_cases (P:=claim) case21 (
      cons_cases (P:=claim) case22 (
      cons_cases (P:=claim) case23 (
      cons_cases (P:=claim) case24 (
      cons_cases (P:=claim) case25 (
      cons_cases (P:=claim) case26 (
      cons_cases (P:=claim) case27 (
      cons_cases (P:=claim) case28 (
      cons_cases (P:=claim) case29 (
      cons_cases (P:=claim) case30 (
      cons_cases (P:=claim) case31 (
      cons_cases (P:=claim) case32 (
      cons_cases (P:=claim) case33 (
      cons_cases (P:=claim) case34 (
      cons_cases (P:=claim) case35 (
      cons_cases (P:=claim) case36 (
      cons_cases (P:=claim) case37 (
      cons_cases (P:=claim) case38 (
      cons_cases (P:=claim) case39 (
      cons_cases (P:=claim) case40 (
      cons_cases (P:=claim) case41 (
      cons_cases (P:=claim) case42 (
      cons_cases (P:=claim) case43 (
      cons_cases (P:=claim) case44 (
      cons_cases (P:=claim) case45 (
      cons_cases (P:=claim) case46 (
      cons_cases (P:=claim) case47 (
      cons_cases (P:=claim) case48 (
      cons_cases (P:=claim) case49 (
      cons_cases (P:=claim) case50 (
      cons_cases (P:=claim) case51 (
      cons_cases (P:=claim) case52 (
      cons_cases (P:=claim) case53 (
      cons_cases (P:=claim) case54 (
      cons_cases (P:=claim) case55 (
      cons_cases (P:=claim) case56 (
      cons_cases (P:=claim) case57 (
      cons_cases (P:=claim) case58 (
      cons_cases (P:=claim) case59 (
      cons_cases (P:=claim) case60 (
      cons_cases (P:=claim) case61 (
      cons_cases (P:=claim) case62 (
      cons_cases (P:=claim) case63 (
      cons_cases (P:=claim) case64 (
      cons_cases (P:=claim) case65 (
      cons_cases (P:=claim) case66 (
      cons_cases (P:=claim) case67 (
      cons_cases (P:=claim) case68 (
      cons_cases (P:=claim) case69 (
      cons_cases (P:=claim) case70 (
      cons_cases (P:=claim) case71 (
      cons_cases (P:=claim) case72 (
      cons_cases (P:=claim) case73 (
      cons_cases (P:=claim) case74 (
      cons_cases (P:=claim) case75 (
      cons_cases (P:=claim) case76 (
      cons_cases (P:=claim) case77 (
      cons_cases (P:=claim) case78 (
      cons_cases (P:=claim) case79 (
      cons_cases (P:=claim) case80 (
      cons_cases (P:=claim) case81 (
      (by simp : ∀ e ∈ ([] : List ℕ), claim e)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- The six smaller endpoint residues, with slopes 17, 19, 22, 23, 25 and 26. -/
def H1 : Prop :=
  (Nat.primeCounting 94085731 % 6 = 0) ∧
  (Nat.primeCounting 590237761 % 7 = 5) ∧
  (Nat.primeCounting 10425579253 % 11 = 8) ∧
  (Nat.primeCounting 28006150079 % 3 = 2) ∧
  (Nat.primeCounting 204778727327 % 5 = 0) ∧
  (Nat.primeCounting 555157672301 % 6 = 4)

/-- Only remainders modulo 9 and 5 are needed at the two largest endpoints. -/
def H2 : Prop :=
  (Nat.primeCounting 11092009835083 % 9 = 7) ∧
  (Nat.primeCounting 30110134441897 % 5 = 3)

/-- Local prime-count differences for slopes 17, 19, 22 and 23. -/
def H3 : Prop :=
  (∀ t ∈ ([
    (94085731,0), (94085833,7), (94085867,9), (94086479,43),
    (94086547,49), (94086649,54), (94086683,59), (94087771,118),
    (94088587,175), (94088927,198), (94089029,206), (94089131,209),
    (94089199,214), (94089607,235), (94090151,263), (94090253,271),
    (94090559,289), (94090627,293), (94091069,317)] : List (ℕ × ℕ)),
    Nat.primeCounting t.1 = Nat.primeCounting 94085731 + t.2) ∧
  (∀ t ∈ ([
    (590237761,0), (590238217,23), (590238749,52), (590238863,59),
    (590239129,78), (590239319,90), (590240041,122), (590240269,131)] : List (ℕ × ℕ)),
    Nat.primeCounting t.1 = Nat.primeCounting 590237761 + t.2) ∧
  (∀ t ∈ ([
    (10425579253,0), (10425579473,16), (10425579539,19), (10425579781,29),
    (10425579803,31), (10425579869,34), (10425580177,49), (10425580397,60),
    (10425580441,63), (10425580859,75), (10425580969,81), (10425581123,91),
    (10425581321,102), (10425581497,106), (10425581849,120), (10425582487,147),
    (10425582509,149), (10425582641,155), (10425582949,172), (10425582971,174),
    (10425583213,181)] : List (ℕ × ℕ)),
    Nat.primeCounting t.1 = Nat.primeCounting 10425579253 + t.2) ∧
  (∀ t ∈ ([
    (28006150079,0)] : List (ℕ × ℕ)),
    Nat.primeCounting t.1 = Nat.primeCounting 28006150079 + t.2)

/-- Local prime-count differences for slopes 25, 26, 29 and 30. -/
def H4 : Prop :=
  (∀ t ∈ ([
    (204778727327,0), (204778727627,12), (204778727677,15), (204778727977,28),
    (204778728127,34), (204778728577,51), (204778728677,56), (204778729427,83)] : List (ℕ × ℕ)),
    Nat.primeCounting t.1 = Nat.primeCounting 204778727327 + t.2) ∧
  (∀ t ∈ ([
    (555157672301,0), (555157672717,18), (555157673003,26), (555157673159,34),
    (555157673237,36), (555157673263,37)] : List (ℕ × ℕ)),
    Nat.primeCounting t.1 = Nat.primeCounting 555157672301 + t.2) ∧
  (∀ t ∈ ([
    (11092009835083,0), (11092009835779,30), (11092009837229,85), (11092009837577,98),
    (11092009838389,129), (11092009838737,140), (11092009839259,153), (11092009839433,160),
    (11092009840651,207), (11092009841347,236), (11092009842449,275), (11092009842971,290),
    (11092009843087,294), (11092009843609,311), (11092009845407,359)] : List (ℕ × ℕ)),
    Nat.primeCounting t.1 = Nat.primeCounting 11092009835083 + t.2) ∧
  (∀ t ∈ ([
    (30110134441897,0), (30110134442137,12), (30110134442287,16), (30110134442767,35)] : List (ℕ × ℕ)),
    Nat.primeCounting t.1 = Nat.primeCounting 30110134441897 + t.2)

theorem main : H1 → H2 → H3 → H4 → OMA.R_OeisA247824_conjecture_2_R2.H4 := by
  rintro ⟨r17,r19,r22,r23,r25,r26⟩ ⟨r29,r30⟩
    ⟨w17,w19,w22,w23⟩ ⟨w25,w26,w29,w30⟩ k m hlo hhi member
  have slope : (32*m+k)%32=k := by omega
  have index : (32*m+k)/32=m := by omega
  have miss := exclusions Nat.primeCounting r17 r19 r22 r23 r25 r26 r29 r30
    w17 w19 w22 w23 w25 w26 w29 w30 (32*m+k) member
  simpa only [slope,index] using miss

end OMA.R_OeisA247824_conjecture_2_R2_H4_R2
