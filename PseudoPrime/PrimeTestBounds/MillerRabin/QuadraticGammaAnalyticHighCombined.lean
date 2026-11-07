/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaAnalyticHigh

/-! # Coverage through 119 further analytic cells -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, 119 certified analytic cells extend the `3/10`
witness bound for odd composites through logarithmic scale 550. Adjacent
closed endpoints connect each cell to the previous coverage. -/
theorem exists_reject_03_analytic550 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ (550 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  by_cases hprev : Real.log n ≤ (9699 / 50 : ℝ)
  · exact exists_reject_03_analytic19398 hn ho hc hGRH hL hprev
  by_cases h0 : Real.log n ≤ (19569 / 100 : ℝ)
  · exact gammaAnalyticHigh0_witness hn ho hc hGRH hL (le_of_not_ge hprev) h0
  by_cases h1 : Real.log n ≤ (9871 / 50 : ℝ)
  · exact gammaAnalyticHigh1_witness hn ho hc hGRH hL (le_of_not_ge h0) h1
  by_cases h2 : Real.log n ≤ (19917 / 100 : ℝ)
  · exact gammaAnalyticHigh2_witness hn ho hc hGRH hL (le_of_not_ge h1) h2
  by_cases h3 : Real.log n ≤ (20093 / 100 : ℝ)
  · exact gammaAnalyticHigh3_witness hn ho hc hGRH hL (le_of_not_ge h2) h3
  by_cases h4 : Real.log n ≤ (20271 / 100 : ℝ)
  · exact gammaAnalyticHigh4_witness hn ho hc hGRH hL (le_of_not_ge h3) h4
  by_cases h5 : Real.log n ≤ (20451 / 100 : ℝ)
  · exact gammaAnalyticHigh5_witness hn ho hc hGRH hL (le_of_not_ge h4) h5
  by_cases h6 : Real.log n ≤ (20633 / 100 : ℝ)
  · exact gammaAnalyticHigh6_witness hn ho hc hGRH hL (le_of_not_ge h5) h6
  by_cases h7 : Real.log n ≤ (20817 / 100 : ℝ)
  · exact gammaAnalyticHigh7_witness hn ho hc hGRH hL (le_of_not_ge h6) h7
  by_cases h8 : Real.log n ≤ (21003 / 100 : ℝ)
  · exact gammaAnalyticHigh8_witness hn ho hc hGRH hL (le_of_not_ge h7) h8
  by_cases h9 : Real.log n ≤ (21191 / 100 : ℝ)
  · exact gammaAnalyticHigh9_witness hn ho hc hGRH hL (le_of_not_ge h8) h9
  by_cases h10 : Real.log n ≤ (1069 / 5 : ℝ)
  · exact gammaAnalyticHigh10_witness hn ho hc hGRH hL (le_of_not_ge h9) h10
  by_cases h11 : Real.log n ≤ (5393 / 25 : ℝ)
  · exact gammaAnalyticHigh11_witness hn ho hc hGRH hL (le_of_not_ge h10) h11
  by_cases h12 : Real.log n ≤ (10883 / 50 : ℝ)
  · exact gammaAnalyticHigh12_witness hn ho hc hGRH hL (le_of_not_ge h11) h12
  by_cases h13 : Real.log n ≤ (10981 / 50 : ℝ)
  · exact gammaAnalyticHigh13_witness hn ho hc hGRH hL (le_of_not_ge h12) h13
  by_cases h14 : Real.log n ≤ (22159 / 100 : ℝ)
  · exact gammaAnalyticHigh14_witness hn ho hc hGRH hL (le_of_not_ge h13) h14
  by_cases h15 : Real.log n ≤ (11179 / 50 : ℝ)
  · exact gammaAnalyticHigh15_witness hn ho hc hGRH hL (le_of_not_ge h14) h15
  by_cases h16 : Real.log n ≤ (1128 / 5 : ℝ)
  · exact gammaAnalyticHigh16_witness hn ho hc hGRH hL (le_of_not_ge h15) h16
  by_cases h17 : Real.log n ≤ (22763 / 100 : ℝ)
  · exact gammaAnalyticHigh17_witness hn ho hc hGRH hL (le_of_not_ge h16) h17
  by_cases h18 : Real.log n ≤ (5742 / 25 : ℝ)
  · exact gammaAnalyticHigh18_witness hn ho hc hGRH hL (le_of_not_ge h17) h18
  by_cases h19 : Real.log n ≤ (927 / 4 : ℝ)
  · exact gammaAnalyticHigh19_witness hn ho hc hGRH hL (le_of_not_ge h18) h19
  by_cases h20 : Real.log n ≤ (4677 / 20 : ℝ)
  · exact gammaAnalyticHigh20_witness hn ho hc hGRH hL (le_of_not_ge h19) h20
  by_cases h21 : Real.log n ≤ (5899 / 25 : ℝ)
  · exact gammaAnalyticHigh21_witness hn ho hc hGRH hL (le_of_not_ge h20) h21
  by_cases h22 : Real.log n ≤ (2381 / 10 : ℝ)
  · exact gammaAnalyticHigh22_witness hn ho hc hGRH hL (le_of_not_ge h21) h22
  by_cases h23 : Real.log n ≤ (961 / 4 : ℝ)
  · exact gammaAnalyticHigh23_witness hn ho hc hGRH hL (le_of_not_ge h22) h23
  by_cases h24 : Real.log n ≤ (24243 / 100 : ℝ)
  · exact gammaAnalyticHigh24_witness hn ho hc hGRH hL (le_of_not_ge h23) h24
  by_cases h25 : Real.log n ≤ (12231 / 50 : ℝ)
  · exact gammaAnalyticHigh25_witness hn ho hc hGRH hL (le_of_not_ge h24) h25
  by_cases h26 : Real.log n ≤ (24683 / 100 : ℝ)
  · exact gammaAnalyticHigh26_witness hn ho hc hGRH hL (le_of_not_ge h25) h26
  by_cases h27 : Real.log n ≤ (12453 / 50 : ℝ)
  · exact gammaAnalyticHigh27_witness hn ho hc hGRH hL (le_of_not_ge h26) h27
  by_cases h28 : Real.log n ≤ (6283 / 25 : ℝ)
  · exact gammaAnalyticHigh28_witness hn ho hc hGRH hL (le_of_not_ge h27) h28
  by_cases h29 : Real.log n ≤ (25359 / 100 : ℝ)
  · exact gammaAnalyticHigh29_witness hn ho hc hGRH hL (le_of_not_ge h28) h29
  by_cases h30 : Real.log n ≤ (25589 / 100 : ℝ)
  · exact gammaAnalyticHigh30_witness hn ho hc hGRH hL (le_of_not_ge h29) h30
  by_cases h31 : Real.log n ≤ (25821 / 100 : ℝ)
  · exact gammaAnalyticHigh31_witness hn ho hc hGRH hL (le_of_not_ge h30) h31
  by_cases h32 : Real.log n ≤ (5211 / 20 : ℝ)
  · exact gammaAnalyticHigh32_witness hn ho hc hGRH hL (le_of_not_ge h31) h32
  by_cases h33 : Real.log n ≤ (2629 / 10 : ℝ)
  · exact gammaAnalyticHigh33_witness hn ho hc hGRH hL (le_of_not_ge h32) h33
  by_cases h34 : Real.log n ≤ (26527 / 100 : ℝ)
  · exact gammaAnalyticHigh34_witness hn ho hc hGRH hL (le_of_not_ge h33) h34
  by_cases h35 : Real.log n ≤ (26767 / 100 : ℝ)
  · exact gammaAnalyticHigh35_witness hn ho hc hGRH hL (le_of_not_ge h34) h35
  by_cases h36 : Real.log n ≤ (27009 / 100 : ℝ)
  · exact gammaAnalyticHigh36_witness hn ho hc hGRH hL (le_of_not_ge h35) h36
  by_cases h37 : Real.log n ≤ (27253 / 100 : ℝ)
  · exact gammaAnalyticHigh37_witness hn ho hc hGRH hL (le_of_not_ge h36) h37
  by_cases h38 : Real.log n ≤ (27499 / 100 : ℝ)
  · exact gammaAnalyticHigh38_witness hn ho hc hGRH hL (le_of_not_ge h37) h38
  by_cases h39 : Real.log n ≤ (27747 / 100 : ℝ)
  · exact gammaAnalyticHigh39_witness hn ho hc hGRH hL (le_of_not_ge h38) h39
  by_cases h40 : Real.log n ≤ (27997 / 100 : ℝ)
  · exact gammaAnalyticHigh40_witness hn ho hc hGRH hL (le_of_not_ge h39) h40
  by_cases h41 : Real.log n ≤ (28249 / 100 : ℝ)
  · exact gammaAnalyticHigh41_witness hn ho hc hGRH hL (le_of_not_ge h40) h41
  by_cases h42 : Real.log n ≤ (7126 / 25 : ℝ)
  · exact gammaAnalyticHigh42_witness hn ho hc hGRH hL (le_of_not_ge h41) h42
  by_cases h43 : Real.log n ≤ (28761 / 100 : ℝ)
  · exact gammaAnalyticHigh43_witness hn ho hc hGRH hL (le_of_not_ge h42) h43
  by_cases h44 : Real.log n ≤ (1451 / 5 : ℝ)
  · exact gammaAnalyticHigh44_witness hn ho hc hGRH hL (le_of_not_ge h43) h44
  by_cases h45 : Real.log n ≤ (29281 / 100 : ℝ)
  · exact gammaAnalyticHigh45_witness hn ho hc hGRH hL (le_of_not_ge h44) h45
  by_cases h46 : Real.log n ≤ (7386 / 25 : ℝ)
  · exact gammaAnalyticHigh46_witness hn ho hc hGRH hL (le_of_not_ge h45) h46
  by_cases h47 : Real.log n ≤ (2981 / 10 : ℝ)
  · exact gammaAnalyticHigh47_witness hn ho hc hGRH hL (le_of_not_ge h46) h47
  by_cases h48 : Real.log n ≤ (15039 / 50 : ℝ)
  · exact gammaAnalyticHigh48_witness hn ho hc hGRH hL (le_of_not_ge h47) h48
  by_cases h49 : Real.log n ≤ (7587 / 25 : ℝ)
  · exact gammaAnalyticHigh49_witness hn ho hc hGRH hL (le_of_not_ge h48) h49
  by_cases h50 : Real.log n ≤ (1531 / 5 : ℝ)
  · exact gammaAnalyticHigh50_witness hn ho hc hGRH hL (le_of_not_ge h49) h50
  by_cases h51 : Real.log n ≤ (15447 / 50 : ℝ)
  · exact gammaAnalyticHigh51_witness hn ho hc hGRH hL (le_of_not_ge h50) h51
  by_cases h52 : Real.log n ≤ (31171 / 100 : ℝ)
  · exact gammaAnalyticHigh52_witness hn ho hc hGRH hL (le_of_not_ge h51) h52
  by_cases h53 : Real.log n ≤ (31449 / 100 : ℝ)
  · exact gammaAnalyticHigh53_witness hn ho hc hGRH hL (le_of_not_ge h52) h53
  by_cases h54 : Real.log n ≤ (3173 / 10 : ℝ)
  · exact gammaAnalyticHigh54_witness hn ho hc hGRH hL (le_of_not_ge h53) h54
  by_cases h55 : Real.log n ≤ (32013 / 100 : ℝ)
  · exact gammaAnalyticHigh55_witness hn ho hc hGRH hL (le_of_not_ge h54) h55
  by_cases h56 : Real.log n ≤ (16149 / 50 : ℝ)
  · exact gammaAnalyticHigh56_witness hn ho hc hGRH hL (le_of_not_ge h55) h56
  by_cases h57 : Real.log n ≤ (6517 / 20 : ℝ)
  · exact gammaAnalyticHigh57_witness hn ho hc hGRH hL (le_of_not_ge h56) h57
  by_cases h58 : Real.log n ≤ (1315 / 4 : ℝ)
  · exact gammaAnalyticHigh58_witness hn ho hc hGRH hL (le_of_not_ge h57) h58
  by_cases h59 : Real.log n ≤ (33167 / 100 : ℝ)
  · exact gammaAnalyticHigh59_witness hn ho hc hGRH hL (le_of_not_ge h58) h59
  by_cases h60 : Real.log n ≤ (16731 / 50 : ℝ)
  · exact gammaAnalyticHigh60_witness hn ho hc hGRH hL (le_of_not_ge h59) h60
  by_cases h61 : Real.log n ≤ (33759 / 100 : ℝ)
  · exact gammaAnalyticHigh61_witness hn ho hc hGRH hL (le_of_not_ge h60) h61
  by_cases h62 : Real.log n ≤ (34059 / 100 : ℝ)
  · exact gammaAnalyticHigh62_witness hn ho hc hGRH hL (le_of_not_ge h61) h62
  by_cases h63 : Real.log n ≤ (34361 / 100 : ℝ)
  · exact gammaAnalyticHigh63_witness hn ho hc hGRH hL (le_of_not_ge h62) h63
  by_cases h64 : Real.log n ≤ (6933 / 20 : ℝ)
  · exact gammaAnalyticHigh64_witness hn ho hc hGRH hL (le_of_not_ge h63) h64
  by_cases h65 : Real.log n ≤ (34971 / 100 : ℝ)
  · exact gammaAnalyticHigh65_witness hn ho hc hGRH hL (le_of_not_ge h64) h65
  by_cases h66 : Real.log n ≤ (1764 / 5 : ℝ)
  · exact gammaAnalyticHigh66_witness hn ho hc hGRH hL (le_of_not_ge h65) h66
  by_cases h67 : Real.log n ≤ (8898 / 25 : ℝ)
  · exact gammaAnalyticHigh67_witness hn ho hc hGRH hL (le_of_not_ge h66) h67
  by_cases h68 : Real.log n ≤ (17953 / 50 : ℝ)
  · exact gammaAnalyticHigh68_witness hn ho hc hGRH hL (le_of_not_ge h67) h68
  by_cases h69 : Real.log n ≤ (36223 / 100 : ℝ)
  · exact gammaAnalyticHigh69_witness hn ho hc hGRH hL (le_of_not_ge h68) h69
  by_cases h70 : Real.log n ≤ (18271 / 50 : ℝ)
  · exact gammaAnalyticHigh70_witness hn ho hc hGRH hL (le_of_not_ge h69) h70
  by_cases h71 : Real.log n ≤ (36863 / 100 : ℝ)
  · exact gammaAnalyticHigh71_witness hn ho hc hGRH hL (le_of_not_ge h70) h71
  by_cases h72 : Real.log n ≤ (37187 / 100 : ℝ)
  · exact gammaAnalyticHigh72_witness hn ho hc hGRH hL (le_of_not_ge h71) h72
  by_cases h73 : Real.log n ≤ (37513 / 100 : ℝ)
  · exact gammaAnalyticHigh73_witness hn ho hc hGRH hL (le_of_not_ge h72) h73
  by_cases h74 : Real.log n ≤ (18921 / 50 : ℝ)
  · exact gammaAnalyticHigh74_witness hn ho hc hGRH hL (le_of_not_ge h73) h74
  by_cases h75 : Real.log n ≤ (38173 / 100 : ℝ)
  · exact gammaAnalyticHigh75_witness hn ho hc hGRH hL (le_of_not_ge h74) h75
  by_cases h76 : Real.log n ≤ (38507 / 100 : ℝ)
  · exact gammaAnalyticHigh76_witness hn ho hc hGRH hL (le_of_not_ge h75) h76
  by_cases h77 : Real.log n ≤ (9711 / 25 : ℝ)
  · exact gammaAnalyticHigh77_witness hn ho hc hGRH hL (le_of_not_ge h76) h77
  by_cases h78 : Real.log n ≤ (39183 / 100 : ℝ)
  · exact gammaAnalyticHigh78_witness hn ho hc hGRH hL (le_of_not_ge h77) h78
  by_cases h79 : Real.log n ≤ (1581 / 4 : ℝ)
  · exact gammaAnalyticHigh79_witness hn ho hc hGRH hL (le_of_not_ge h78) h79
  by_cases h80 : Real.log n ≤ (39869 / 100 : ℝ)
  · exact gammaAnalyticHigh80_witness hn ho hc hGRH hL (le_of_not_ge h79) h80
  by_cases h81 : Real.log n ≤ (40217 / 100 : ℝ)
  · exact gammaAnalyticHigh81_witness hn ho hc hGRH hL (le_of_not_ge h80) h81
  by_cases h82 : Real.log n ≤ (40567 / 100 : ℝ)
  · exact gammaAnalyticHigh82_witness hn ho hc hGRH hL (le_of_not_ge h81) h82
  by_cases h83 : Real.log n ≤ (2046 / 5 : ℝ)
  · exact gammaAnalyticHigh83_witness hn ho hc hGRH hL (le_of_not_ge h82) h83
  by_cases h84 : Real.log n ≤ (1651 / 4 : ℝ)
  · exact gammaAnalyticHigh84_witness hn ho hc hGRH hL (le_of_not_ge h83) h84
  by_cases h85 : Real.log n ≤ (41633 / 100 : ℝ)
  · exact gammaAnalyticHigh85_witness hn ho hc hGRH hL (le_of_not_ge h84) h85
  by_cases h86 : Real.log n ≤ (20997 / 50 : ℝ)
  · exact gammaAnalyticHigh86_witness hn ho hc hGRH hL (le_of_not_ge h85) h86
  by_cases h87 : Real.log n ≤ (21179 / 50 : ℝ)
  · exact gammaAnalyticHigh87_witness hn ho hc hGRH hL (le_of_not_ge h86) h87
  by_cases h88 : Real.log n ≤ (1709 / 4 : ℝ)
  · exact gammaAnalyticHigh88_witness hn ho hc hGRH hL (le_of_not_ge h87) h88
  by_cases h89 : Real.log n ≤ (21547 / 50 : ℝ)
  · exact gammaAnalyticHigh89_witness hn ho hc hGRH hL (le_of_not_ge h88) h89
  by_cases h90 : Real.log n ≤ (21733 / 50 : ℝ)
  · exact gammaAnalyticHigh90_witness hn ho hc hGRH hL (le_of_not_ge h89) h90
  by_cases h91 : Real.log n ≤ (43841 / 100 : ℝ)
  · exact gammaAnalyticHigh91_witness hn ho hc hGRH hL (le_of_not_ge h90) h91
  by_cases h92 : Real.log n ≤ (44219 / 100 : ℝ)
  · exact gammaAnalyticHigh92_witness hn ho hc hGRH hL (le_of_not_ge h91) h92
  by_cases h93 : Real.log n ≤ (446 : ℝ)
  · exact gammaAnalyticHigh93_witness hn ho hc hGRH hL (le_of_not_ge h92) h93
  by_cases h94 : Real.log n ≤ (11246 / 25 : ℝ)
  · exact gammaAnalyticHigh94_witness hn ho hc hGRH hL (le_of_not_ge h93) h94
  by_cases h95 : Real.log n ≤ (45371 / 100 : ℝ)
  · exact gammaAnalyticHigh95_witness hn ho hc hGRH hL (le_of_not_ge h94) h95
  by_cases h96 : Real.log n ≤ (45761 / 100 : ℝ)
  · exact gammaAnalyticHigh96_witness hn ho hc hGRH hL (le_of_not_ge h95) h96
  by_cases h97 : Real.log n ≤ (23077 / 50 : ℝ)
  · exact gammaAnalyticHigh97_witness hn ho hc hGRH hL (le_of_not_ge h96) h97
  by_cases h98 : Real.log n ≤ (931 / 2 : ℝ)
  · exact gammaAnalyticHigh98_witness hn ho hc hGRH hL (le_of_not_ge h97) h98
  by_cases h99 : Real.log n ≤ (46949 / 100 : ℝ)
  · exact gammaAnalyticHigh99_witness hn ho hc hGRH hL (le_of_not_ge h98) h99
  by_cases h100 : Real.log n ≤ (47351 / 100 : ℝ)
  · exact gammaAnalyticHigh100_witness hn ho hc hGRH hL (le_of_not_ge h99) h100
  by_cases h101 : Real.log n ≤ (11939 / 25 : ℝ)
  · exact gammaAnalyticHigh101_witness hn ho hc hGRH hL (le_of_not_ge h100) h101
  by_cases h102 : Real.log n ≤ (12041 / 25 : ℝ)
  · exact gammaAnalyticHigh102_witness hn ho hc hGRH hL (le_of_not_ge h101) h102
  by_cases h103 : Real.log n ≤ (1943 / 4 : ℝ)
  · exact gammaAnalyticHigh103_witness hn ho hc hGRH hL (le_of_not_ge h102) h103
  by_cases h104 : Real.log n ≤ (48989 / 100 : ℝ)
  · exact gammaAnalyticHigh104_witness hn ho hc hGRH hL (le_of_not_ge h103) h104
  by_cases h105 : Real.log n ≤ (24703 / 50 : ℝ)
  · exact gammaAnalyticHigh105_witness hn ho hc hGRH hL (le_of_not_ge h104) h105
  by_cases h106 : Real.log n ≤ (49827 / 100 : ℝ)
  · exact gammaAnalyticHigh106_witness hn ho hc hGRH hL (le_of_not_ge h105) h106
  by_cases h107 : Real.log n ≤ (50251 / 100 : ℝ)
  · exact gammaAnalyticHigh107_witness hn ho hc hGRH hL (le_of_not_ge h106) h107
  by_cases h108 : Real.log n ≤ (25339 / 50 : ℝ)
  · exact gammaAnalyticHigh108_witness hn ho hc hGRH hL (le_of_not_ge h107) h108
  by_cases h109 : Real.log n ≤ (12777 / 25 : ℝ)
  · exact gammaAnalyticHigh109_witness hn ho hc hGRH hL (le_of_not_ge h108) h109
  by_cases h110 : Real.log n ≤ (25771 / 50 : ℝ)
  · exact gammaAnalyticHigh110_witness hn ho hc hGRH hL (le_of_not_ge h109) h110
  by_cases h111 : Real.log n ≤ (51979 / 100 : ℝ)
  · exact gammaAnalyticHigh111_witness hn ho hc hGRH hL (le_of_not_ge h110) h111
  by_cases h112 : Real.log n ≤ (2621 / 5 : ℝ)
  · exact gammaAnalyticHigh112_witness hn ho hc hGRH hL (le_of_not_ge h111) h112
  by_cases h113 : Real.log n ≤ (13216 / 25 : ℝ)
  · exact gammaAnalyticHigh113_witness hn ho hc hGRH hL (le_of_not_ge h112) h113
  by_cases h114 : Real.log n ≤ (13328 / 25 : ℝ)
  · exact gammaAnalyticHigh114_witness hn ho hc hGRH hL (le_of_not_ge h113) h114
  by_cases h115 : Real.log n ≤ (53763 / 100 : ℝ)
  · exact gammaAnalyticHigh115_witness hn ho hc hGRH hL (le_of_not_ge h114) h115
  by_cases h116 : Real.log n ≤ (27109 / 50 : ℝ)
  · exact gammaAnalyticHigh116_witness hn ho hc hGRH hL (le_of_not_ge h115) h116
  by_cases h117 : Real.log n ≤ (13669 / 25 : ℝ)
  · exact gammaAnalyticHigh117_witness hn ho hc hGRH hL (le_of_not_ge h116) h117
  exact gammaAnalyticHigh118_witness hn ho hc hGRH hL (le_of_not_ge h117) hU

end PseudoPrime.PrimeTestBounds.MillerRabin
