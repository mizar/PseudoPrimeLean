/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis32768

/-! # Direct theta estimate up to 1033341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell1001341184 :
    ThetaLowerSegment 1001341184 1001406720 (100130293146287 / 100000) (2002736717987 / 2000) := by
  exact
    packedTile32768 1001341184 1001406720 13 3157 31643 30 _ _ (2072459 / 100000) (1036231 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1001406720 :
    ThetaLowerSegment 1001406720 1001472256 (2002736717987 / 2000) (50071690373489 / 50000) := by
  exact
    packedTile32768 1001406720 1001472256 13 3158 31645 30 _ _ (1036233 / 50000) (2072469 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1001472256 :
    ThetaLowerSegment 1001472256 1001537792 (50071690373489 / 50000) (10015003545457 / 10000) := by
  exact
    packedTile32768 1001472256 1001537792 13 3211 31646 30 _ _ (259059 / 12500) (82899 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1001537792 :
    ThetaLowerSegment 1001537792 1001603328 (10015003545457 / 10000)
      (100156561690941 / 100000) := by
  exact
    packedTile32768 1001537792 1001603328 13 3149 31647 30 _ _ (2072479 / 100000) (1036241 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1001603328 :
    ThetaLowerSegment 1001603328 1001668864 (100156561690941 / 100000)
      (100163172918091 / 100000) := by
  exact
    packedTile32768 1001603328 1001668864 13 3190 31648 30 _ _ (414497 / 20000) (259061 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1001668864 :
    ThetaLowerSegment 1001668864 1001734400 (100163172918091 / 100000)
      (100169721992811 / 100000) := by
  exact
    packedTile32768 1001668864 1001734400 13 3160 31649 30 _ _ (518123 / 25000) (414499 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1001734400 :
    ThetaLowerSegment 1001734400 1001799936 (100169721992811 / 100000)
      (100176231709029 / 100000) := by
  exact
    packedTile32768 1001734400 1001799936 13 3141 31650 30 _ _ (1036249 / 50000) (2072501 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1001799936 :
    ThetaLowerSegment 1001799936 1001865472 (100176231709029 / 100000)
      (100182706214649 / 100000) := by
  exact
    packedTile32768 1001799936 1001865472 13 3124 31651 30 _ _ (414501 / 20000) (518127 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1001865472 :
    ThetaLowerSegment 1001865472 1001931008 (100182706214649 / 100000)
      (10018923669681 / 10000) := by
  exact
    packedTile32768 1001865472 1001931008 13 3151 31652 30 _ _ (2072511 / 100000) (1036257 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1001931008 :
    ThetaLowerSegment 1001931008 1001996544 (10018923669681 / 10000) (50097915724543 / 50000) := by
  exact
    packedTile32768 1001931008 1001996544 13 3182 31653 30 _ _ (1036259 / 50000) (2072521 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1001996544 :
    ThetaLowerSegment 1001996544 1002062080 (50097915724543 / 50000) (50101115703143 / 50000) := by
  exact
    packedTile32768 1001996544 1002062080 13 3088 31654 30 _ _ (82901 / 4000) (129533 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1002062080 :
    ThetaLowerSegment 1002062080 1002127616 (50101115703143 / 50000) (50104431752743 / 50000) := by
  exact
    packedTile32768 1002062080 1002127616 13 3200 31655 30 _ _ (2072531 / 100000) (1036267 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1002127616 :
    ThetaLowerSegment 1002127616 1002193152 (50104431752743 / 50000) (25053850590719 / 25000) := by
  exact
    packedTile32768 1002127616 1002193152 13 3155 31656 30 _ _ (1036269 / 50000) (2072541 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1002193152 :
    ThetaLowerSegment 1002193152 1002258688 (25053850590719 / 25000) (25055494118111 / 25000) := by
  exact
    packedTile32768 1002193152 1002258688 13 3172 31657 30 _ _ (64767 / 3125) (2072547 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1002258688 :
    ThetaLowerSegment 1002258688 1002324224 (25055494118111 / 25000) (25057114852993 / 25000) := by
  exact
    packedTile32768 1002258688 1002324224 13 3128 31658 30 _ _ (2072551 / 100000) (1036277 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1002324224 :
    ThetaLowerSegment 1002324224 1002389760 (25057114852993 / 25000)
      (100234969313509 / 100000) := by
  exact
    packedTile32768 1002324224 1002389760 13 3141 31659 30 _ _ (2072557 / 100000) (25907 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1002389760 :
    ThetaLowerSegment 1002389760 1002455296 (100234969313509 / 100000)
      (100241421205241 / 100000) := by
  exact
    packedTile32768 1002389760 1002455296 13 3113 31660 30 _ _ (518141 / 25000) (2072567 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1002455296 :
    ThetaLowerSegment 1002455296 1002520832 (100241421205241 / 100000)
      (100248090735501 / 100000) := by
  exact
    packedTile32768 1002455296 1002520832 13 3218 31661 30 _ _ (207257 / 10000) (2072573 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1002520832 :
    ThetaLowerSegment 1002520832 1002586368 (100248090735501 / 100000)
      (20050920554487 / 20000) := by
  exact
    packedTile32768 1002520832 1002586368 13 3142 31662 30 _ _ (2072577 / 100000) (103629 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1002586368 :
    ThetaLowerSegment 1002586368 1002651904 (20050920554487 / 20000)
      (100261031924901 / 100000) := by
  exact
    packedTile32768 1002586368 1002651904 13 3102 31663 30 _ _ (2072583 / 100000) (1036293 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1002651904 :
    ThetaLowerSegment 1002651904 1002717440 (100261031924901 / 100000)
      (100267662140311 / 100000) := by
  exact
    packedTile32768 1002651904 1002717440 13 3199 31664 30 _ _ (207259 / 10000) (2072593 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1002717440 :
    ThetaLowerSegment 1002717440 1002782976 (100267662140311 / 100000)
      (20054860547579 / 20000) := by
  exact
    packedTile32768 1002717440 1002782976 13 3204 31665 30 _ _ (518149 / 25000) (2072599 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1002782976 :
    ThetaLowerSegment 1002782976 1002848512 (20054860547579 / 20000)
      (100280702935959 / 100000) := by
  exact
    packedTile32768 1002782976 1002848512 13 3088 31666 30 _ _ (2072603 / 100000) (1036303 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1002848512 :
    ThetaLowerSegment 1002848512 1002914048 (100280702935959 / 100000)
      (100287353941449 / 100000) := by
  exact
    packedTile32768 1002848512 1002914048 13 3209 31667 30 _ _ (207261 / 10000) (2072613 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1002914048 :
    ThetaLowerSegment 1002914048 1002979584 (100287353941449 / 100000)
      (100294023619737 / 100000) := by
  exact
    packedTile32768 1002914048 1002979584 13 3218 31668 30 _ _ (259077 / 12500) (2072619 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1002979584 :
    ThetaLowerSegment 1002979584 1003045120 (100294023619737 / 100000)
      (100300552382187 / 100000) := by
  exact
    packedTile32768 1002979584 1003045120 13 3150 31669 30 _ _ (2072623 / 100000) (1036313 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1003045120 :
    ThetaLowerSegment 1003045120 1003110656 (100300552382187 / 100000)
      (12538396285823 / 12500) := by
  exact
    packedTile32768 1003045120 1003110656 13 3193 31670 30 _ _ (2072629 / 100000) (259079 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1003110656 :
    ThetaLowerSegment 1003110656 1003176192 (12538396285823 / 12500) (6269604638647 / 6250) := by
  exact
    packedTile32768 1003110656 1003176192 13 3138 31671 30 _ _ (518159 / 25000) (2072639 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1003176192 :
    ThetaLowerSegment 1003176192 1003241728 (6269604638647 / 6250) (50160056958523 / 50000) := by
  exact
    packedTile32768 1003176192 1003241728 13 3107 31672 30 _ _ (1036321 / 50000) (414529 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1003241728 :
    ThetaLowerSegment 1003241728 1003307264 (50160056958523 / 50000) (50163319308049 / 50000) := by
  exact
    packedTile32768 1003241728 1003307264 13 3148 31673 30 _ _ (2072649 / 100000) (518163 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1003307264 :
    ThetaLowerSegment 1003307264 1003372800 (50163319308049 / 50000) (50166623120119 / 50000) := by
  exact
    packedTile32768 1003307264 1003372800 13 3188 31675 30 _ _ (414531 / 20000) (1036329 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1003372800 :
    ThetaLowerSegment 1003372800 1003438336 (50166623120119 / 50000) (12542480440423 / 12500) := by
  exact
    packedTile32768 1003372800 1003438336 13 3183 31676 30 _ _ (1036331 / 50000) (414533 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1003438336 :
    ThetaLowerSegment 1003438336 1003503872 (12542480440423 / 12500) (25086577043719 / 25000) := by
  exact
    packedTile32768 1003438336 1003503872 13 3119 31677 30 _ _ (518167 / 25000) (2072671 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1003503872 :
    ThetaLowerSegment 1003503872 1003569408 (25086577043719 / 25000) (50176397823813 / 50000) := by
  exact
    packedTile32768 1003503872 1003569408 13 3130 31678 30 _ _ (82907 / 4000) (1036339 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1003569408 :
    ThetaLowerSegment 1003569408 1003634944 (50176397823813 / 50000)
      (100359380555163 / 100000) := by
  exact
    packedTile32768 1003569408 1003634944 13 3177 31679 30 _ _ (2072681 / 100000) (518171 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1003634944 :
    ThetaLowerSegment 1003634944 1003700480 (100359380555163 / 100000)
      (100366013156763 / 100000) := by
  exact
    packedTile32768 1003634944 1003700480 13 3200 31680 30 _ _ (129543 / 6250) (2072691 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1003700480 :
    ThetaLowerSegment 1003700480 1003766016 (100366013156763 / 100000)
      (20074534544517 / 20000) := by
  exact
    packedTile32768 1003700480 1003766016 13 3213 31681 30 _ _ (1036347 / 50000) (2072697 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1003766016 :
    ThetaLowerSegment 1003766016 1003831552 (20074534544517 / 20000)
      (100379276347971 / 100000) := by
  exact
    packedTile32768 1003766016 1003831552 13 3186 31682 30 _ _ (2072701 / 100000) (64772 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1003831552 :
    ThetaLowerSegment 1003831552 1003897088 (100379276347971 / 100000)
      (20077168537383 / 20000) := by
  exact
    packedTile32768 1003831552 1003897088 13 3168 31683 30 _ _ (518177 / 25000) (2072711 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1003897088 :
    ThetaLowerSegment 1003897088 1003962624 (20077168537383 / 20000)
      (100392313700023 / 100000) := by
  exact
    packedTile32768 1003897088 1003962624 13 3122 31684 30 _ _ (1036357 / 50000) (2072717 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1003962624 :
    ThetaLowerSegment 1003962624 1004028160 (100392313700023 / 100000)
      (50199434858273 / 50000) := by
  exact
    packedTile32768 1003962624 1004028160 13 3163 31685 30 _ _ (2072721 / 100000) (518181 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1004028160 :
    ThetaLowerSegment 1004028160 1004093696 (50199434858273 / 50000)
      (100405272370249 / 100000) := by
  exact
    packedTile32768 1004028160 1004093696 13 3089 31686 30 _ _ (2072727 / 100000) (207273 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1004093696 :
    ThetaLowerSegment 1004093696 1004159232 (100405272370249 / 100000)
      (100411938282793 / 100000) := by
  exact
    packedTile32768 1004093696 1004159232 13 3216 31687 30 _ _ (1036367 / 50000) (2072737 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1004159232 :
    ThetaLowerSegment 1004159232 1004224768 (100411938282793 / 100000)
      (100418421813513 / 100000) := by
  exact
    packedTile32768 1004159232 1004224768 13 3128 31688 30 _ _ (103637 / 5000) (2072743 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1004224768 :
    ThetaLowerSegment 1004224768 1004290304 (100418421813513 / 100000)
      (100425100204347 / 100000) := by
  exact
    packedTile32768 1004224768 1004290304 13 3222 31689 30 _ _ (2072747 / 100000) (8291 / 400)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1004290304 :
    ThetaLowerSegment 1004290304 1004355840 (100425100204347 / 100000)
      (100431645958321 / 100000) := by
  exact
    packedTile32768 1004290304 1004355840 13 3158 31690 30 _ _ (2072753 / 100000) (518189 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1004355840 :
    ThetaLowerSegment 1004355840 1004421376 (100431645958321 / 100000)
      (100438079805361 / 100000) := by
  exact
    packedTile32768 1004355840 1004421376 13 3104 31691 30 _ _ (51819 / 2500) (2072763 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1004421376 :
    ThetaLowerSegment 1004421376 1004486912 (100438079805361 / 100000)
      (100444766548477 / 100000) := by
  exact
    packedTile32768 1004421376 1004486912 13 3226 31692 30 _ _ (1036383 / 50000) (2072769 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1004486912 :
    ThetaLowerSegment 1004486912 1004552448 (100444766548477 / 100000)
      (100451299928973 / 100000) := by
  exact
    packedTile32768 1004486912 1004552448 13 3152 31693 30 _ _ (2072773 / 100000) (259097 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1004552448 :
    ThetaLowerSegment 1004552448 1004617984 (100451299928973 / 100000)
      (20091594026359 / 20000) := by
  exact
    packedTile32768 1004552448 1004617984 13 3218 31694 30 _ _ (2072779 / 100000) (1036391 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1004617984 :
    ThetaLowerSegment 1004617984 1004683520 (20091594026359 / 20000)
      (100464501480481 / 100000) := by
  exact
    packedTile32768 1004617984 1004683520 13 3151 31695 30 _ _ (1036393 / 50000) (2072789 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1004683520 :
    ThetaLowerSegment 1004683520 1004749056 (100464501480481 / 100000)
      (100471111614169 / 100000) := by
  exact
    packedTile32768 1004683520 1004749056 13 3189 31696 30 _ _ (259099 / 12500) (414559 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1004749056 :
    ThetaLowerSegment 1004749056 1004814592 (100471111614169 / 100000)
      (100477698969391 / 100000) := by
  exact
    packedTile32768 1004749056 1004814592 13 3178 31697 30 _ _ (2072799 / 100000) (1036401 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1004814592 :
    ThetaLowerSegment 1004814592 1004880128 (100477698969391 / 100000)
      (100484207577091 / 100000) := by
  exact
    packedTile32768 1004814592 1004880128 13 3140 31698 30 _ _ (414561 / 20000) (259101 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1004880128 :
    ThetaLowerSegment 1004880128 1004945664 (100484207577091 / 100000)
      (100490716206771 / 100000) := by
  exact
    packedTile32768 1004880128 1004945664 13 3140 31699 30 _ _ (518203 / 25000) (414563 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1004945664 :
    ThetaLowerSegment 1004945664 1005011200 (100490716206771 / 100000)
      (100497237292199 / 100000) := by
  exact
    packedTile32768 1004945664 1005011200 13 3146 31700 30 _ _ (1036409 / 50000) (2072821 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1005011200 :
    ThetaLowerSegment 1005011200 1005076736 (100497237292199 / 100000)
      (50251896818837 / 50000) := by
  exact
    packedTile32768 1005011200 1005076736 13 3163 31701 30 _ _ (82913 / 4000) (518207 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1005076736 :
    ThetaLowerSegment 1005076736 1005142272 (50251896818837 / 50000)
      (100510271234549 / 100000) := by
  exact
    packedTile32768 1005076736 1005142272 13 3125 31702 30 _ _ (2072831 / 100000) (1036417 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1005142272 :
    ThetaLowerSegment 1005142272 1005207808 (100510271234549 / 100000)
      (100516802747087 / 100000) := by
  exact
    packedTile32768 1005142272 1005207808 13 3151 31703 30 _ _ (1036419 / 50000) (2072841 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1005207808 :
    ThetaLowerSegment 1005207808 1005273344 (100516802747087 / 100000)
      (50261779074471 / 50000) := by
  exact
    packedTile32768 1005207808 1005273344 13 3259 31705 30 _ _ (414569 / 20000) (129553 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1005273344 :
    ThetaLowerSegment 1005273344 1005338880 (50261779074471 / 50000) (50265116364581 / 50000) := by
  exact
    packedTile32768 1005273344 1005338880 13 3220 31706 30 _ _ (2072851 / 100000) (1036427 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1005338880 :
    ThetaLowerSegment 1005338880 1005404416 (50265116364581 / 50000) (12567109011667 / 12500) := by
  exact
    packedTile32768 1005338880 1005404416 13 3203 31707 30 _ _ (1036429 / 50000) (2072861 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1005404416 :
    ThetaLowerSegment 1005404416 1005469952 (12567109011667 / 12500) (12567927792947 / 12500) := by
  exact
    packedTile32768 1005404416 1005469952 13 3160 31708 30 _ _ (64777 / 3125) (2072867 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1005469952 :
    ThetaLowerSegment 1005469952 1005535488 (12567927792947 / 12500) (25137478643887 / 25000) := by
  exact
    packedTile32768 1005469952 1005535488 13 3132 31709 30 _ _ (2072871 / 100000) (1036437 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1005535488 :
    ThetaLowerSegment 1005535488 1005601024 (25137478643887 / 25000)
      (100556587166611 / 100000) := by
  exact
    packedTile32768 1005535488 1005601024 13 3219 31710 30 _ _ (2072877 / 100000) (25911 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1005601024 :
    ThetaLowerSegment 1005601024 1005666560 (100556587166611 / 100000)
      (100563147844471 / 100000) := by
  exact
    packedTile32768 1005601024 1005666560 13 3165 31711 30 _ _ (518221 / 25000) (2072887 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1005666560 :
    ThetaLowerSegment 1005666560 1005732096 (100563147844471 / 100000)
      (100569708541321 / 100000) := by
  exact
    packedTile32768 1005666560 1005732096 13 3165 31712 30 _ _ (207289 / 10000) (2072893 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1005732096 :
    ThetaLowerSegment 1005732096 1005797632 (100569708541321 / 100000)
      (50288155359133 / 50000) := by
  exact
    packedTile32768 1005732096 1005797632 13 3185 31713 30 _ _ (2072897 / 100000) (20729 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1005797632 :
    ThetaLowerSegment 1005797632 1005863168 (50288155359133 / 50000) (25145722528097 / 25000) := by
  exact
    packedTile32768 1005797632 1005863168 13 3174 31714 30 _ _ (2072903 / 100000) (1036453 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1005863168 :
    ThetaLowerSegment 1005863168 1005928704 (25145722528097 / 25000) (50294686050979 / 50000) := by
  exact
    packedTile32768 1005863168 1005928704 13 3127 31715 30 _ _ (207291 / 10000) (2072913 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1005928704 :
    ThetaLowerSegment 1005928704 1005994240 (50294686050979 / 50000) (50298001680121 / 50000) := by
  exact
    packedTile32768 1005928704 1005994240 13 3199 31716 30 _ _ (518229 / 25000) (2072919 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1005994240 :
    ThetaLowerSegment 1005994240 1006059776 (50298001680121 / 50000) (25150608391847 / 25000) := by
  exact
    packedTile32768 1005994240 1006059776 13 3102 31717 30 _ _ (2072923 / 100000) (1036463 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1006059776 :
    ThetaLowerSegment 1006059776 1006125312 (25150608391847 / 25000) (12576111601769 / 12500) := by
  exact
    packedTile32768 1006059776 1006125312 13 3116 31718 30 _ _ (2072929 / 100000) (518233 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1006125312 :
    ThetaLowerSegment 1006125312 1006190848 (12576111601769 / 12500) (12576928338553 / 12500) := by
  exact
    packedTile32768 1006125312 1006190848 13 3152 31719 30 _ _ (259117 / 12500) (2072939 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1006190848 :
    ThetaLowerSegment 1006190848 1006256384 (12576928338553 / 12500) (5031098652963 / 5000) := by
  exact
    packedTile32768 1006190848 1006256384 13 3158 31720 30 _ _ (1036471 / 50000) (414589 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1006256384 :
    ThetaLowerSegment 1006256384 1006321920 (5031098652963 / 5000) (50314263861999 / 50000) := by
  exact
    packedTile32768 1006256384 1006321920 13 3162 31721 30 _ _ (2072949 / 100000) (259119 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1006321920 :
    ThetaLowerSegment 1006321920 1006387456 (50314263861999 / 50000) (25158754018287 / 25000) := by
  exact
    packedTile32768 1006321920 1006387456 13 3130 31722 30 _ _ (414591 / 20000) (1036479 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1006387456 :
    ThetaLowerSegment 1006387456 1006452992 (25158754018287 / 25000) (25160391658267 / 25000) := by
  exact
    packedTile32768 1006387456 1006452992 13 3160 31723 30 _ _ (1036481 / 50000) (414593 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1006452992 :
    ThetaLowerSegment 1006452992 1006518528 (25160391658267 / 25000) (5032403165739 / 5000) := by
  exact
    packedTile32768 1006452992 1006518528 13 3134 31724 30 _ _ (259121 / 12500) (2072971 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1006518528 :
    ThetaLowerSegment 1006518528 1006584064 (5032403165739 / 5000) (10065452685083 / 10000) := by
  exact
    packedTile32768 1006518528 1006584064 13 3118 31725 30 _ _ (82919 / 4000) (1036489 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1006584064 :
    ThetaLowerSegment 1006584064 1006649600 (10065452685083 / 10000)
      (100661079543771 / 100000) := by
  exact
    packedTile32768 1006584064 1006649600 13 3161 31726 30 _ _ (2072981 / 100000) (259123 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1006649600 :
    ThetaLowerSegment 1006649600 1006715136 (100661079543771 / 100000)
      (100667530682427 / 100000) := by
  exact
    packedTile32768 1006649600 1006715136 13 3112 31727 30 _ _ (518247 / 25000) (2072991 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1006715136 :
    ThetaLowerSegment 1006715136 1006780672 (100667530682427 / 100000)
      (20134817097891 / 20000) := by
  exact
    packedTile32768 1006715136 1006780672 13 3162 31728 30 _ _ (1036497 / 50000) (2072997 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1006780672 :
    ThetaLowerSegment 1006780672 1006846208 (20134817097891 / 20000) (12585081853703 / 12500) := by
  exact
    packedTile32768 1006780672 1006846208 13 3169 31729 30 _ _ (2073001 / 100000) (518251 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1006846208 :
    ThetaLowerSegment 1006846208 1006911744 (12585081853703 / 12500)
      (100687199312723 / 100000) := by
  exact
    packedTile32768 1006846208 1006911744 13 3157 31730 30 _ _ (2073007 / 100000) (207301 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1006911744 :
    ThetaLowerSegment 1006911744 1006977280 (100687199312723 / 100000)
      (20138776127369 / 20000) := by
  exact
    packedTile32768 1006911744 1006977280 13 3223 31731 30 _ _ (1036507 / 50000) (2073017 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1006977280 :
    ThetaLowerSegment 1006977280 1007042816 (20138776127369 / 20000) (20140099957941 / 20000) := by
  exact
    packedTile32768 1006977280 1007042816 13 3193 31732 30 _ _ (103651 / 5000) (2073023 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1007042816 :
    ThetaLowerSegment 1007042816 1007108352 (20140099957941 / 20000) (50353578139701 / 50000) := by
  exact
    packedTile32768 1007042816 1007108352 13 3211 31733 30 _ _ (2073027 / 100000) (207303 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1007108352 :
    ThetaLowerSegment 1007108352 1007173888 (50353578139701 / 50000)
      (100713675968187 / 100000) := by
  exact
    packedTile32768 1007108352 1007173888 13 3145 31734 30 _ _ (2073033 / 100000) (518259 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1007173888 :
    ThetaLowerSegment 1007173888 1007239424 (100713675968187 / 100000)
      (100720264089307 / 100000) := by
  exact
    packedTile32768 1007173888 1007239424 13 3178 31736 30 _ _ (25913 / 1250) (2073043 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1007239424 :
    ThetaLowerSegment 1007239424 1007304960 (100720264089307 / 100000)
      (100726991123577 / 100000) := by
  exact
    packedTile32768 1007239424 1007304960 13 3245 31737 30 _ _ (1036523 / 50000) (2073049 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1007304960 :
    ThetaLowerSegment 1007304960 1007370496 (100726991123577 / 100000)
      (100733620747071 / 100000) := by
  exact
    packedTile32768 1007304960 1007370496 13 3198 31738 30 _ _ (2073053 / 100000) (64783 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1007370496 :
    ThetaLowerSegment 1007370496 1007436032 (100733620747071 / 100000)
      (100740221366927 / 100000) := by
  exact
    packedTile32768 1007370496 1007436032 13 3184 31739 30 _ _ (2073059 / 100000) (1036531 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1007436032 :
    ThetaLowerSegment 1007436032 1007501568 (100740221366927 / 100000)
      (100746620921669 / 100000) := by
  exact
    packedTile32768 1007436032 1007501568 13 3087 31740 30 _ _ (1036533 / 50000) (2073069 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1007501568 :
    ThetaLowerSegment 1007501568 1007567104 (100746620921669 / 100000)
      (100753227802133 / 100000) := by
  exact
    packedTile32768 1007501568 1007567104 13 3187 31741 30 _ _ (129567 / 6250) (82923 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1007567104 :
    ThetaLowerSegment 1007567104 1007632640 (100753227802133 / 100000)
      (20151988086387 / 20000) := by
  exact
    packedTile32768 1007567104 1007632640 13 3238 31742 30 _ _ (2073079 / 100000) (1036541 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1007632640 :
    ThetaLowerSegment 1007632640 1007698176 (20151988086387 / 20000) (20153277545257 / 20000) := by
  exact
    packedTile32768 1007632640 1007698176 13 3110 31743 30 _ _ (414617 / 20000) (64784 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1007698176 :
    ThetaLowerSegment 1007698176 1007763712 (20153277545257 / 20000)
      (100772967720293 / 100000) := by
  exact
    packedTile32768 1007698176 1007763712 13 3174 31744 30 _ _ (518273 / 25000) (414619 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1007763712 :
    ThetaLowerSegment 1007763712 1007829248 (100772967720293 / 100000)
      (100779442005347 / 100000) := by
  exact
    packedTile32768 1007763712 1007829248 13 3123 31745 30 _ _ (1036549 / 50000) (2073101 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1007829248 :
    ThetaLowerSegment 1007829248 1007894784 (100779442005347 / 100000)
      (100785910092947 / 100000) := by
  exact
    packedTile32768 1007829248 1007894784 13 3120 31746 30 _ _ (414621 / 20000) (518277 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1007894784 :
    ThetaLowerSegment 1007894784 1007960320 (100785910092947 / 100000)
      (100792461123707 / 100000) := by
  exact
    packedTile32768 1007894784 1007960320 13 3160 31747 30 _ _ (2073111 / 100000) (1036557 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1007960320 :
    ThetaLowerSegment 1007960320 1008025856 (100792461123707 / 100000)
      (20159769680053 / 20000) := by
  exact
    packedTile32768 1007960320 1008025856 13 3081 31748 30 _ _ (1036559 / 50000) (2073121 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1008025856 :
    ThetaLowerSegment 1008025856 1008091392 (20159769680053 / 20000)
      (100805490689561 / 100000) := by
  exact
    packedTile32768 1008025856 1008091392 13 3204 31749 30 _ _ (518281 / 25000) (2073127 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1008091392 :
    ThetaLowerSegment 1008091392 1008156928 (100805490689561 / 100000)
      (100812045929783 / 100000) := by
  exact
    packedTile32768 1008091392 1008156928 13 3162 31750 30 _ _ (2073131 / 100000) (1036567 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1008156928 :
    ThetaLowerSegment 1008156928 1008222464 (100812045929783 / 100000)
      (50409367971441 / 50000) := by
  exact
    packedTile32768 1008156928 1008222464 13 3227 31751 30 _ _ (2073137 / 100000) (103657 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1008222464 :
    ThetaLowerSegment 1008222464 1008288000 (50409367971441 / 50000) (50412633173241 / 50000) := by
  exact
    packedTile32768 1008222464 1008288000 13 3150 31752 30 _ _ (259143 / 12500) (2073147 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1008288000 :
    ThetaLowerSegment 1008288000 1008353536 (50412633173241 / 50000) (50415881799291 / 50000) := by
  exact
    packedTile32768 1008288000 1008353536 13 3134 31753 30 _ _ (41463 / 2000) (2073153 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1008353536 :
    ThetaLowerSegment 1008353536 1008419072 (50415881799291 / 50000)
      (100838399774139 / 100000) := by
  exact
    packedTile32768 1008353536 1008419072 13 3201 31754 30 _ _ (2073157 / 100000) (51829 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1008419072 :
    ThetaLowerSegment 1008419072 1008484608 (100838399774139 / 100000)
      (100844868042699 / 100000) := by
  exact
    packedTile32768 1008419072 1008484608 13 3120 31755 30 _ _ (2073163 / 100000) (1036583 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1008484608 :
    ThetaLowerSegment 1008484608 1008550144 (100844868042699 / 100000)
      (100851462796469 / 100000) := by
  exact
    packedTile32768 1008484608 1008550144 13 3181 31756 30 _ _ (207317 / 10000) (2073173 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1008550144 :
    ThetaLowerSegment 1008550144 1008615680 (100851462796469 / 100000)
      (100857997447221 / 100000) := by
  exact
    packedTile32768 1008550144 1008615680 13 3152 31757 30 _ _ (259147 / 12500) (2073179 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1008615680 :
    ThetaLowerSegment 1008615680 1008681216 (100857997447221 / 100000)
      (50432206974303 / 50000) := by
  exact
    packedTile32768 1008615680 1008681216 13 3095 31758 30 _ _ (2073183 / 100000) (1036593 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1008681216 :
    ThetaLowerSegment 1008681216 1008746752 (50432206974303 / 50000)
      (100870838761317 / 100000) := by
  exact
    packedTile32768 1008681216 1008746752 13 3099 31759 30 _ _ (2073189 / 100000) (259149 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1008746752 :
    ThetaLowerSegment 1008746752 1008812288 (100870838761317 / 100000)
      (100877431524597 / 100000) := by
  exact
    packedTile32768 1008746752 1008812288 13 3180 31760 30 _ _ (518299 / 25000) (2073199 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1008812288 :
    ThetaLowerSegment 1008812288 1008877824 (100877431524597 / 100000)
      (100883953818089 / 100000) := by
  exact
    packedTile32768 1008812288 1008877824 13 3146 31761 30 _ _ (1036601 / 50000) (414641 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1008877824 :
    ThetaLowerSegment 1008877824 1008943360 (100883953818089 / 100000)
      (100890422230169 / 100000) := by
  exact
    packedTile32768 1008877824 1008943360 13 3120 31762 30 _ _ (2073209 / 100000) (518303 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1008943360 :
    ThetaLowerSegment 1008943360 1009008896 (100890422230169 / 100000) (3153032562677 / 3125) := by
  exact
    packedTile32768 1008943360 1009008896 13 3193 31763 30 _ _ (414643 / 20000) (1036609 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1009008896 :
    ThetaLowerSegment 1009008896 1009074432 (3153032562677 / 3125) (5045181535259 / 5000) := by
  exact
    packedTile32768 1009008896 1009074432 13 3178 31764 30 _ _ (1036611 / 50000) (82929 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1009074432 :
    ThetaLowerSegment 1009074432 1009139968 (5045181535259 / 5000) (6306887288641 / 6250) := by
  exact
    packedTile32768 1009074432 1009139968 13 3167 31765 30 _ _ (518307 / 25000) (2073231 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1009139968 :
    ThetaLowerSegment 1009139968 1009205504 (6306887288641 / 6250) (50458388533073 / 50000) := by
  exact
    packedTile32768 1009139968 1009205504 13 3174 31766 30 _ _ (414647 / 20000) (1036619 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1009205504 :
    ThetaLowerSegment 1009205504 1009271040 (50458388533073 / 50000)
      (100923260090753 / 100000) := by
  exact
    packedTile32768 1009205504 1009271040 13 3127 31767 30 _ _ (2073241 / 100000) (518311 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1009271040 :
    ThetaLowerSegment 1009271040 1009336576 (100923260090753 / 100000)
      (100929745210497 / 100000) := by
  exact
    packedTile32768 1009271040 1009336576 13 3128 31769 30 _ _ (64789 / 3125) (2073251 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1009336576 :
    ThetaLowerSegment 1009336576 1009402112 (100929745210497 / 100000)
      (20187253948167 / 20000) := by
  exact
    packedTile32768 1009336576 1009402112 13 3147 31770 30 _ _ (1036627 / 50000) (2073257 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1009402112 :
    ThetaLowerSegment 1009402112 1009467648 (20187253948167 / 20000) (50471455197909 / 50000) := by
  exact
    packedTile32768 1009402112 1009467648 13 3203 31771 30 _ _ (2073261 / 100000) (129579 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1009467648 :
    ThetaLowerSegment 1009467648 1009533184 (50471455197909 / 50000) (2523739968879 / 2500) := by
  exact
    packedTile32768 1009467648 1009533184 13 3226 31772 30 _ _ (2073267 / 100000) (207327 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1009533184 :
    ThetaLowerSegment 1009533184 1009598720 (2523739968879 / 2500) (6309757838857 / 6250) := by
  exact
    packedTile32768 1009533184 1009598720 13 3148 31773 30 _ _ (1036637 / 50000) (2073277 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1009598720 :
    ThetaLowerSegment 1009598720 1009664256 (6309757838857 / 6250) (6310173142757 / 6250) := by
  exact
    packedTile32768 1009598720 1009664256 13 3205 31774 30 _ _ (12958 / 625) (2073283 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1009664256 :
    ThetaLowerSegment 1009664256 1009729792 (6310173142757 / 6250) (100969315651171 / 100000) := by
  exact
    packedTile32768 1009664256 1009729792 13 3157 31775 30 _ _ (2073287 / 100000) (207329 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1009729792 :
    ThetaLowerSegment 1009729792 1009795328 (100969315651171 / 100000)
      (100975846524121 / 100000) := by
  exact
    packedTile32768 1009729792 1009795328 13 3150 31776 30 _ _ (2073293 / 100000) (129581 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1009795328 :
    ThetaLowerSegment 1009795328 1009860864 (100975846524121 / 100000)
      (100982284120621 / 100000) := by
  exact
    packedTile32768 1009795328 1009860864 13 3105 31777 30 _ _ (20733 / 1000) (2073303 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1009860864 :
    ThetaLowerSegment 1009860864 1009926400 (100982284120621 / 100000)
      (100989011998591 / 100000) := by
  exact
    packedTile32768 1009860864 1009926400 13 3245 31778 30 _ _ (1036653 / 50000) (2073309 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1009926400 :
    ThetaLowerSegment 1009926400 1009991936 (100989011998591 / 100000)
      (25248893508559 / 25000) := by
  exact
    packedTile32768 1009926400 1009991936 13 3165 31779 30 _ _ (2073313 / 100000) (518329 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1009991936 :
    ThetaLowerSegment 1009991936 1010057472 (25248893508559 / 25000) (631263752261 / 625) := by
  exact
    packedTile32768 1009991936 1010057472 13 3196 31780 30 _ _ (2073319 / 100000) (1036661 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1010057472 :
    ThetaLowerSegment 1010057472 1010123008 (631263752261 / 625) (10100861730573 / 10000) := by
  exact
    packedTile32768 1010057472 1010123008 13 3095 31781 30 _ _ (1036663 / 50000) (2073329 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1010123008 :
    ThetaLowerSegment 1010123008 1010188544 (10100861730573 / 10000) (10101512756821 / 10000) := by
  exact
    packedTile32768 1010123008 1010188544 13 3140 31782 30 _ _ (518333 / 25000) (414667 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1010188544 :
    ThetaLowerSegment 1010188544 1010254080 (10101512756821 / 10000) (50510835513047 / 50000) := by
  exact
    packedTile32768 1010188544 1010254080 13 3156 31783 30 _ _ (2073339 / 100000) (1036671 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1010254080 :
    ThetaLowerSegment 1010254080 1010319616 (50510835513047 / 50000) (50514123838217 / 50000) := by
  exact
    packedTile32768 1010254080 1010319616 13 3172 31784 30 _ _ (414669 / 20000) (518337 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1010319616 :
    ThetaLowerSegment 1010319616 1010385152 (50514123838217 / 50000) (50517380037533 / 50000) := by
  exact
    packedTile32768 1010319616 1010385152 13 3141 31785 30 _ _ (259169 / 12500) (414671 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1010385152 :
    ThetaLowerSegment 1010385152 1010450688 (50517380037533 / 50000) (50520676676753 / 50000) := by
  exact
    packedTile32768 1010385152 1010450688 13 3180 31786 30 _ _ (1036679 / 50000) (2073361 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1010450688 :
    ThetaLowerSegment 1010450688 1010516224 (50520676676753 / 50000) (12631002143577 / 12500) := by
  exact
    packedTile32768 1010450688 1010516224 13 3214 31787 30 _ _ (414673 / 20000) (259171 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1010516224 :
    ThetaLowerSegment 1010516224 1010581760 (12631002143577 / 12500) (50527253399923 / 50000) := by
  exact
    packedTile32768 1010516224 1010581760 13 3130 31788 30 _ _ (2073371 / 100000) (1036687 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1010581760 :
    ThetaLowerSegment 1010581760 1010647296 (50527253399923 / 50000) (25265278663883 / 25000) := by
  exact
    packedTile32768 1010581760 1010647296 13 3187 31789 30 _ _ (1036689 / 50000) (2073381 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1010647296 :
    ThetaLowerSegment 1010647296 1010712832 (25265278663883 / 25000) (5053380424711 / 5000) := by
  exact
    packedTile32768 1010647296 1010712832 13 3132 31790 30 _ _ (259173 / 12500) (2073387 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1010712832 :
    ThetaLowerSegment 1010712832 1010778368 (5053380424711 / 5000) (10107405674023 / 10000) := by
  exact
    packedTile32768 1010712832 1010778368 13 3110 31791 30 _ _ (2073391 / 100000) (1036697 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1010778368 :
    ThetaLowerSegment 1010778368 1010843904 (10107405674023 / 10000) (12635084896281 / 12500) := by
  exact
    packedTile32768 1010778368 1010843904 13 3194 31792 30 _ _ (2073397 / 100000) (10367 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1010843904 :
    ThetaLowerSegment 1010843904 1010909440 (12635084896281 / 12500) (3158976102303 / 3125) := by
  exact
    packedTile32768 1010843904 1010909440 13 3162 31793 30 _ _ (518351 / 25000) (2073407 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1010909440 :
    ThetaLowerSegment 1010909440 1010974976 (3158976102303 / 3125) (50546894661353 / 50000) := by
  exact
    packedTile32768 1010909440 1010974976 13 3161 31794 30 _ _ (207341 / 10000) (2073413 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1010974976 :
    ThetaLowerSegment 1010974976 1011040512 (50546894661353 / 50000)
      (101100409743187 / 100000) := by
  exact
    packedTile32768 1010974976 1011040512 13 3193 31795 30 _ _ (2073417 / 100000) (103671 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1011040512 :
    ThetaLowerSegment 1011040512 1011106048 (101100409743187 / 100000) (6319184462047 / 6250) := by
  exact
    packedTile32768 1011040512 1011106048 13 3155 31796 30 _ _ (2073423 / 100000) (1036713 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1011106048 :
    ThetaLowerSegment 1011106048 1011171584 (6319184462047 / 6250) (25278360307163 / 25000) := by
  exact
    packedTile32768 1011106048 1011171584 13 3130 31797 30 _ _ (207343 / 10000) (2073433 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1011171584 :
    ThetaLowerSegment 1011171584 1011237120 (25278360307163 / 25000) (12640005640289 / 12500) := by
  exact
    packedTile32768 1011171584 1011237120 13 3185 31798 30 _ _ (518359 / 25000) (2073439 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1011237120 :
    ThetaLowerSegment 1011237120 1011302656 (12640005640289 / 12500)
      (101126690507127 / 100000) := by
  exact
    packedTile32768 1011237120 1011302656 13 3205 31799 30 _ _ (2073443 / 100000) (1036723 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1011302656 :
    ThetaLowerSegment 1011302656 1011368192 (101126690507127 / 100000)
      (50566570503483 / 50000) := by
  exact
    packedTile32768 1011302656 1011368192 13 3111 31800 30 _ _ (2073449 / 100000) (518363 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1011368192 :
    ThetaLowerSegment 1011368192 1011433728 (50566570503483 / 50000)
      (101139757401871 / 100000) := by
  exact
    packedTile32768 1011368192 1011433728 13 3191 31802 30 _ _ (414691 / 20000) (1036729 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1011433728 :
    ThetaLowerSegment 1011433728 1011499264 (101139757401871 / 100000)
      (101146274292937 / 100000) := by
  exact
    packedTile32768 1011433728 1011499264 13 3143 31803 30 _ _ (1036731 / 50000) (414693 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1011499264 :
    ThetaLowerSegment 1011499264 1011564800 (101146274292937 / 100000)
      (101152768394713 / 100000) := by
  exact
    packedTile32768 1011499264 1011564800 13 3132 31804 30 _ _ (518367 / 25000) (2073471 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1011564800 :
    ThetaLowerSegment 1011564800 1011630336 (101152768394713 / 100000)
      (50579642663319 / 50000) := by
  exact
    packedTile32768 1011564800 1011630336 13 3143 31805 30 _ _ (82939 / 4000) (1036739 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1011630336 :
    ThetaLowerSegment 1011630336 1011695872 (50579642663319 / 50000) (10116586240837 / 10000) := by
  exact
    packedTile32768 1011630336 1011695872 13 3172 31806 30 _ _ (2073481 / 100000) (518371 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1011695872 :
    ThetaLowerSegment 1011695872 1011761408 (10116586240837 / 10000) (50586206278481 / 50000) := by
  exact
    packedTile32768 1011695872 1011761408 13 3159 31807 30 _ _ (129593 / 6250) (2073491 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1011761408 :
    ThetaLowerSegment 1011761408 1011826944 (50586206278481 / 50000) (25294753122091 / 25000) := by
  exact
    packedTile32768 1011761408 1011826944 13 3183 31808 30 _ _ (1036747 / 50000) (2073497 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1011826944 :
    ThetaLowerSegment 1011826944 1011892480 (25294753122091 / 25000) (3162051749549 / 3125) := by
  exact
    packedTile32768 1011826944 1011892480 13 3204 31809 30 _ _ (2073501 / 100000) (64797 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1011892480 :
    ThetaLowerSegment 1011892480 1011958016 (3162051749549 / 3125) (101192326457587 / 100000) := by
  exact
    packedTile32768 1011892480 1011958016 13 3217 31810 30 _ _ (2073507 / 100000) (207351 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1011958016 :
    ThetaLowerSegment 1011958016 1012023552 (101192326457587 / 100000)
      (101198920232107 / 100000) := by
  exact
    packedTile32768 1011958016 1012023552 13 3180 31811 30 _ _ (1036757 / 50000) (2073517 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1012023552 :
    ThetaLowerSegment 1012023552 1012089088 (101198920232107 / 100000)
      (101205455967147 / 100000) := by
  exact
    packedTile32768 1012023552 1012089088 13 3152 31812 30 _ _ (25919 / 1250) (2073523 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1012089088 :
    ThetaLowerSegment 1012089088 1012154624 (101205455967147 / 100000)
      (101212041488899 / 100000) := by
  exact
    packedTile32768 1012089088 1012154624 13 3176 31813 30 _ _ (2073527 / 100000) (207353 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1012154624 :
    ThetaLowerSegment 1012154624 1012220160 (101212041488899 / 100000)
      (10121864983857 / 10000) := by
  exact
    packedTile32768 1012154624 1012220160 13 3187 31814 30 _ _ (2073533 / 100000) (64798 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1012220160 :
    ThetaLowerSegment 1012220160 1012285696 (10121864983857 / 10000) (10122509647443 / 10000) := by
  exact
    packedTile32768 1012220160 1012285696 13 3109 31815 30 _ _ (103677 / 5000) (2073543 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1012285696 :
    ThetaLowerSegment 1012285696 1012351232 (10122509647443 / 10000) (25307924142837 / 25000) := by
  exact
    packedTile32768 1012285696 1012351232 13 3183 31816 30 _ _ (1036773 / 50000) (2073549 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1012351232 :
    ThetaLowerSegment 1012351232 1012416768 (25307924142837 / 25000)
      (101238139100519 / 100000) := by
  exact
    packedTile32768 1012351232 1012416768 13 3107 31817 30 _ _ (2073553 / 100000) (518389 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1012416768 :
    ThetaLowerSegment 1012416768 1012482304 (101238139100519 / 100000)
      (12655590331293 / 12500) := by
  exact
    packedTile32768 1012416768 1012482304 13 3175 31818 30 _ _ (2073559 / 100000) (1036781 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1012482304 :
    ThetaLowerSegment 1012482304 1012547840 (12655590331293 / 12500) (25312836405037 / 25000) := by
  exact
    packedTile32768 1012482304 1012547840 13 3194 31819 30 _ _ (1036783 / 50000) (2073569 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1012547840 :
    ThetaLowerSegment 1012547840 1012613376 (25312836405037 / 25000) (25314469342987 / 25000) := by
  exact
    packedTile32768 1012547840 1012613376 13 3150 31820 30 _ _ (518393 / 25000) (82943 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1012613376 :
    ThetaLowerSegment 1012613376 1012678912 (25314469342987 / 25000)
      (101264440249483 / 100000) := by
  exact
    packedTile32768 1012613376 1012678912 13 3165 31821 30 _ _ (2073579 / 100000) (1036791 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1012678912 :
    ThetaLowerSegment 1012678912 1012744448 (101264440249483 / 100000)
      (25317732124237 / 25000) := by
  exact
    packedTile32768 1012678912 1012744448 13 3129 31822 30 _ _ (414717 / 20000) (518397 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1012744448 :
    ThetaLowerSegment 1012744448 1012809984 (25317732124237 / 25000) (20255503259111 / 20000) := by
  exact
    packedTile32768 1012744448 1012809984 13 3177 31823 30 _ _ (2073591 / 100000) (1036797 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1012809984 :
    ThetaLowerSegment 1012809984 1012875520 (20255503259111 / 20000) (20256811699449 / 20000) := by
  exact
    packedTile32768 1012809984 1012875520 13 3155 31824 30 _ _ (1036799 / 50000) (2073601 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1012875520 :
    ThetaLowerSegment 1012875520 1012941056 (20256811699449 / 20000)
      (101290625601113 / 100000) := by
  exact
    packedTile32768 1012875520 1012941056 13 3167 31825 30 _ _ (518401 / 25000) (2073607 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1012941056 :
    ThetaLowerSegment 1012941056 1013006592 (101290625601113 / 100000) (6331075323051 / 6250) := by
  exact
    packedTile32768 1012941056 1013006592 13 3173 31826 30 _ _ (2073611 / 100000) (1036807 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1013006592 :
    ThetaLowerSegment 1013006592 1013072128 (6331075323051 / 6250) (101303635455133 / 100000) := by
  exact
    packedTile32768 1013006592 1013072128 13 3101 31827 30 _ _ (2073617 / 100000) (103681 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1013072128 :
    ThetaLowerSegment 1013072128 1013137664 (101303635455133 / 100000)
      (101310148708117 / 100000) := by
  exact
    packedTile32768 1013072128 1013137664 13 3141 31828 30 _ _ (259203 / 12500) (2073627 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1013137664 :
    ThetaLowerSegment 1013137664 1013203200 (101310148708117 / 100000)
      (101316697231657 / 100000) := by
  exact
    packedTile32768 1013137664 1013203200 13 3158 31829 30 _ _ (207363 / 10000) (2073633 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1013203200 :
    ThetaLowerSegment 1013203200 1013268736 (101316697231657 / 100000)
      (20264655791099 / 20000) := by
  exact
    packedTile32768 1013203200 1013268736 13 3174 31830 30 _ _ (2073637 / 100000) (51841 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1013268736 :
    ThetaLowerSegment 1013268736 1013334272 (20264655791099 / 20000)
      (101329885582093 / 100000) := by
  exact
    packedTile32768 1013268736 1013334272 13 3186 31831 30 _ _ (2073643 / 100000) (1036823 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1013334272 :
    ThetaLowerSegment 1013334272 1013399808 (101329885582093 / 100000)
      (101336320118043 / 100000) := by
  exact
    packedTile32768 1013334272 1013399808 13 3103 31832 30 _ _ (41473 / 2000) (2073653 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1013399808 :
    ThetaLowerSegment 1013399808 1013465344 (101336320118043 / 100000)
      (101342796145731 / 100000) := by
  exact
    packedTile32768 1013399808 1013465344 13 3123 31833 30 _ _ (259207 / 12500) (2073659 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1013465344 :
    ThetaLowerSegment 1013465344 1013530880 (101342796145731 / 100000)
      (50674692086541 / 50000) := by
  exact
    packedTile32768 1013465344 1013530880 13 3177 31834 30 _ _ (2073663 / 100000) (1036833 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1013530880 :
    ThetaLowerSegment 1013530880 1013596416 (50674692086541 / 50000) (50677951894209 / 50000) := by
  exact
    packedTile32768 1013530880 1013596416 13 3144 31835 30 _ _ (2073669 / 100000) (259209 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1013596416 :
    ThetaLowerSegment 1013596416 1013661952 (50677951894209 / 50000) (50681192012959 / 50000) := by
  exact
    packedTile32768 1013596416 1013661952 13 3125 31837 30 _ _ (518419 / 25000) (2073679 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1013661952 :
    ThetaLowerSegment 1013661952 1013727488 (50681192012959 / 50000) (50684404146377 / 50000) := by
  exact
    packedTile32768 1013661952 1013727488 13 3098 31838 30 _ _ (1036841 / 50000) (414737 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1013727488 :
    ThetaLowerSegment 1013727488 1013793024 (50684404146377 / 50000) (50687674352353 / 50000) := by
  exact
    packedTile32768 1013727488 1013793024 13 3154 31839 30 _ _ (259211 / 12500) (2073691 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1013793024 :
    ThetaLowerSegment 1013793024 1013858560 (50687674352353 / 50000)
      (101382065402811 / 100000) := by
  exact
    packedTile32768 1013793024 1013858560 13 3239 31840 30 _ _ (414739 / 20000) (1036849 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1013858560 :
    ThetaLowerSegment 1013858560 1013924096 (101382065402811 / 100000)
      (101388547792137 / 100000) := by
  exact
    packedTile32768 1013858560 1013924096 13 3126 31841 30 _ _ (2073701 / 100000) (259213 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1013924096 :
    ThetaLowerSegment 1013924096 1013989632 (101388547792137 / 100000)
      (101395187805153 / 100000) := by
  exact
    packedTile32768 1013924096 1013989632 13 3202 31842 30 _ _ (518427 / 25000) (2073711 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1013989632 :
    ThetaLowerSegment 1013989632 1014055168 (101395187805153 / 100000)
      (101401805026527 / 100000) := by
  exact
    packedTile32768 1013989632 1014055168 13 3191 31843 30 _ _ (1036857 / 50000) (2073717 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1014055168 :
    ThetaLowerSegment 1014055168 1014120704 (101401805026527 / 100000)
      (101408403606749 / 100000) := by
  exact
    packedTile32768 1014055168 1014120704 13 3182 31844 30 _ _ (2073721 / 100000) (518431 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1014120704 :
    ThetaLowerSegment 1014120704 1014186240 (101408403606749 / 100000)
      (20282990487323 / 20000) := by
  exact
    packedTile32768 1014120704 1014186240 13 3158 31845 30 _ _ (2073727 / 100000) (207373 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1014186240 :
    ThetaLowerSegment 1014186240 1014251776 (20282990487323 / 20000)
      (101421451518971 / 100000) := by
  exact
    packedTile32768 1014186240 1014251776 13 3134 31846 30 _ _ (1036867 / 50000) (2073737 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1014251776 :
    ThetaLowerSegment 1014251776 1014317312 (101421451518971 / 100000)
      (101428002463631 / 100000) := by
  exact
    packedTile32768 1014251776 1014317312 13 3159 31847 30 _ _ (103687 / 5000) (2073743 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1014317312 :
    ThetaLowerSegment 1014317312 1014382848 (101428002463631 / 100000)
      (101434596979091 / 100000) := by
  exact
    packedTile32768 1014317312 1014382848 13 3180 31848 30 _ _ (2073747 / 100000) (1659 / 80)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1014382848 :
    ThetaLowerSegment 1014382848 1014448384 (101434596979091 / 100000)
      (101441079530969 / 100000) := by
  exact
    packedTile32768 1014382848 1014448384 13 3126 31849 30 _ _ (2073753 / 100000) (518439 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1014448384 :
    ThetaLowerSegment 1014448384 1014513920 (101441079530969 / 100000)
      (101447746669369 / 100000) := by
  exact
    packedTile32768 1014448384 1014513920 13 3215 31850 30 _ _ (12961 / 625) (2073763 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1014513920 :
    ThetaLowerSegment 1014513920 1014579456 (101447746669369 / 100000)
      (20290885253931 / 20000) := by
  exact
    packedTile32768 1014513920 1014579456 13 3221 31851 30 _ _ (1036883 / 50000) (2073769 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1014579456 :
    ThetaLowerSegment 1014579456 1014644992 (20290885253931 / 20000) (12682617498831 / 12500) := by
  exact
    packedTile32768 1014579456 1014644992 13 3141 31852 30 _ _ (2073773 / 100000) (129611 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1014644992 :
    ThetaLowerSegment 1014644992 1014710528 (12682617498831 / 12500)
      (101467470320719 / 100000) := by
  exact
    packedTile32768 1014644992 1014710528 13 3149 31853 30 _ _ (2073779 / 100000) (1036891 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1014710528 :
    ThetaLowerSegment 1014710528 1014776064 (101467470320719 / 100000)
      (101474131318139 / 100000) := by
  exact
    packedTile32768 1014710528 1014776064 13 3212 31854 30 _ _ (414757 / 20000) (518447 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1014776064 :
    ThetaLowerSegment 1014776064 1014841600 (101474131318139 / 100000)
      (101480682427067 / 100000) := by
  exact
    packedTile32768 1014776064 1014841600 13 3159 31855 30 _ _ (64806 / 3125) (414759 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1014841600 :
    ThetaLowerSegment 1014841600 1014907136 (101480682427067 / 100000)
      (101487316506869 / 100000) := by
  exact
    packedTile32768 1014841600 1014907136 13 3199 31856 30 _ _ (1036899 / 50000) (2073801 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1014907136 :
    ThetaLowerSegment 1014907136 1014972672 (101487316506869 / 100000)
      (25373477283241 / 25000) := by
  exact
    packedTile32768 1014907136 1014972672 13 3179 31857 30 _ _ (414761 / 20000) (129613 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1014972672 :
    ThetaLowerSegment 1014972672 1015038208 (25373477283241 / 25000)
      (101500373201851 / 100000) := by
  exact
    packedTile32768 1014972672 1015038208 13 3117 31858 30 _ _ (2073811 / 100000) (1036907 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1015038208 :
    ThetaLowerSegment 1015038208 1015103744 (101500373201851 / 100000) (4060279796109 / 4000) := by
  exact
    packedTile32768 1015038208 1015103744 13 3193 31859 30 _ _ (1036909 / 50000) (2073821 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1015103744 :
    ThetaLowerSegment 1015103744 1015169280 (4060279796109 / 4000) (20302707563489 / 20000) := by
  exact
    packedTile32768 1015103744 1015169280 13 3155 31860 30 _ _ (64807 / 3125) (2073827 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1015169280 :
    ThetaLowerSegment 1015169280 1015234816 (20302707563489 / 20000)
      (101520157485997 / 100000) := by
  exact
    packedTile32768 1015169280 1015234816 13 3192 31861 30 _ _ (2073831 / 100000) (1036917 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1015234816 :
    ThetaLowerSegment 1015234816 1015300352 (101520157485997 / 100000)
      (20305343821253 / 20000) := by
  exact
    packedTile32768 1015234816 1015300352 13 3164 31862 30 _ _ (2073837 / 100000) (25923 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1015300352 :
    ThetaLowerSegment 1015300352 1015365888 (20305343821253 / 20000) (4061331312901 / 4000) := by
  exact
    packedTile32768 1015300352 1015365888 13 3165 31863 30 _ _ (518461 / 25000) (2073847 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1015365888 :
    ThetaLowerSegment 1015365888 1015431424 (4061331312901 / 4000) (4061594194127 / 4000) := by
  exact
    packedTile32768 1015365888 1015431424 13 3169 31864 30 _ _ (41477 / 2000) (2073853 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1015431424 :
    ThetaLowerSegment 1015431424 1015496960 (4061594194127 / 4000) (4061857573839 / 4000) := by
  exact
    packedTile32768 1015431424 1015496960 13 3175 31865 30 _ _ (64808 / 3125) (2073859 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1015496960 :
    ThetaLowerSegment 1015496960 1015562496 (4061857573839 / 4000) (101552988605329 / 100000) := by
  exact
    packedTile32768 1015496960 1015562496 13 3158 31866 30 _ _ (2073863 / 100000) (1036933 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1015562496 :
    ThetaLowerSegment 1015562496 1015628032 (101552988605329 / 100000)
      (101559542031369 / 100000) := by
  exact
    packedTile32768 1015562496 1015628032 13 3160 31867 30 _ _ (2073869 / 100000) (129617 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1015628032 :
    ThetaLowerSegment 1015628032 1015693568 (101559542031369 / 100000)
      (101566209542709 / 100000) := by
  exact
    packedTile32768 1015628032 1015693568 13 3215 31868 30 _ _ (518469 / 25000) (2073879 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1015693568 :
    ThetaLowerSegment 1015693568 1015759104 (101566209542709 / 100000)
      (101572595025387 / 100000) := by
  exact
    packedTile32768 1015693568 1015759104 13 3079 31869 30 _ _ (1036941 / 50000) (414777 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1015759104 :
    ThetaLowerSegment 1015759104 1015824640 (101572595025387 / 100000)
      (101579198287963 / 100000) := by
  exact
    packedTile32768 1015759104 1015824640 13 3184 31870 30 _ _ (2073889 / 100000) (518473 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1015824640 :
    ThetaLowerSegment 1015824640 1015890176 (101579198287963 / 100000)
      (50792918412929 / 50000) := by
  exact
    packedTile32768 1015824640 1015890176 13 3201 31872 30 _ _ (414779 / 20000) (1036949 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1015890176 :
    ThetaLowerSegment 1015890176 1015955712 (50792918412929 / 50000) (12699041795103 / 12500) := by
  exact
    packedTile32768 1015890176 1015955712 13 3133 31873 30 _ _ (1036951 / 50000) (414781 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1015955712 :
    ThetaLowerSegment 1015955712 1016021248 (12699041795103 / 12500) (12699859951809 / 12500) := by
  exact
    packedTile32768 1015955712 1016021248 13 3156 31874 30 _ _ (518477 / 25000) (2073911 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1016021248 :
    ThetaLowerSegment 1016021248 1016086784 (12699859951809 / 12500) (50802706223361 / 50000) := by
  exact
    packedTile32768 1016021248 1016086784 13 3150 31875 30 _ _ (414783 / 20000) (1036959 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1016086784 :
    ThetaLowerSegment 1016086784 1016152320 (50802706223361 / 50000) (25403025728967 / 25000) := by
  exact
    packedTile32768 1016086784 1016152320 13 3226 31876 30 _ _ (2073921 / 100000) (518481 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1016152320 :
    ThetaLowerSegment 1016152320 1016217856 (25403025728967 / 25000)
      (101618633711991 / 100000) := by
  exact
    packedTile32768 1016152320 1016217856 13 3149 31877 30 _ _ (2073927 / 100000) (207393 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1016217856 :
    ThetaLowerSegment 1016217856 1016283392 (101618633711991 / 100000)
      (20325008848397 / 20000) := by
  exact
    packedTile32768 1016217856 1016283392 13 3091 31878 30 _ _ (1036967 / 50000) (2073937 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1016283392 :
    ThetaLowerSegment 1016283392 1016348928 (20325008848397 / 20000) (20326322896781 / 20000) := by
  exact
    packedTile32768 1016283392 1016348928 13 3168 31879 30 _ _ (103697 / 5000) (2073943 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1016348928 :
    ThetaLowerSegment 1016348928 1016414464 (20326322896781 / 20000)
      (101638172304319 / 100000) := by
  exact
    packedTile32768 1016348928 1016414464 13 3162 31880 30 _ _ (2073947 / 100000) (41479 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1016414464 :
    ThetaLowerSegment 1016414464 1016480000 (101638172304319 / 100000)
      (101644759179047 / 100000) := by
  exact
    packedTile32768 1016414464 1016480000 13 3176 31881 30 _ _ (2073953 / 100000) (518489 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1016480000 :
    ThetaLowerSegment 1016480000 1016545536 (101644759179047 / 100000)
      (101651300448887 / 100000) := by
  exact
    packedTile32768 1016480000 1016545536 13 3154 31882 30 _ _ (51849 / 2500) (2073963 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1016545536 :
    ThetaLowerSegment 1016545536 1016611072 (101651300448887 / 100000)
      (101657876995073 / 100000) := by
  exact
    packedTile32768 1016545536 1016611072 13 3171 31883 30 _ _ (1036983 / 50000) (2073969 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1016611072 :
    ThetaLowerSegment 1016611072 1016676608 (101657876995073 / 100000)
      (101664360234671 / 100000) := by
  exact
    packedTile32768 1016611072 1016676608 13 3126 31884 30 _ _ (2073973 / 100000) (259247 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1016676608 :
    ThetaLowerSegment 1016676608 1016742144 (101664360234671 / 100000) (40668358137 / 40) := by
  exact
    packedTile32768 1016676608 1016742144 13 3151 31885 30 _ _ (2073979 / 100000) (1036991 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1016742144 :
    ThetaLowerSegment 1016742144 1016807680 (40668358137 / 40) (2541937680167 / 2500) := by
  exact
    packedTile32768 1016742144 1016807680 13 3188 31886 30 _ _ (414797 / 20000) (518497 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1016807680 :
    ThetaLowerSegment 1016807680 1016873216 (2541937680167 / 2500) (12710512294157 / 12500) := by
  exact
    packedTile32768 1016807680 1016873216 13 3178 31887 30 _ _ (259249 / 12500) (414799 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1016873216 :
    ThetaLowerSegment 1016873216 1016938752 (12710512294157 / 12500) (25422659935737 / 25000) := by
  exact
    packedTile32768 1016873216 1016938752 13 3154 31888 30 _ _ (1036999 / 50000) (2074001 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1016938752 :
    ThetaLowerSegment 1016938752 1017004288 (25422659935737 / 25000)
      (101697203968773 / 100000) := by
  exact
    packedTile32768 1016938752 1017004288 13 3165 31889 30 _ _ (414801 / 20000) (259251 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1017004288 :
    ThetaLowerSegment 1017004288 1017069824 (101697203968773 / 100000) (4068147990849 / 4000) := by
  exact
    packedTile32768 1017004288 1017069824 13 3132 31890 30 _ _ (2074011 / 100000) (1037007 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1017069824 :
    ThetaLowerSegment 1017069824 1017135360 (4068147990849 / 4000) (101710259890159 / 100000) := by
  exact
    packedTile32768 1017069824 1017135360 13 3163 31891 30 _ _ (1037009 / 50000) (2074021 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1017135360 :
    ThetaLowerSegment 1017135360 1017200896 (101710259890159 / 100000)
      (101716886396839 / 100000) := by
  exact
    packedTile32768 1017135360 1017200896 13 3195 31892 30 _ _ (259253 / 12500) (2074027 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1017200896 :
    ThetaLowerSegment 1017200896 1017266432 (101716886396839 / 100000) (1017233801879 / 1000) := by
  exact
    packedTile32768 1017200896 1017266432 13 3131 31893 30 _ _ (2074031 / 100000) (1037017 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1017266432 :
    ThetaLowerSegment 1017266432 1017331968 (1017233801879 / 1000) (10172987192371 / 10000) := by
  exact
    packedTile32768 1017266432 1017331968 13 3130 31894 30 _ _ (2074037 / 100000) (51851 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1017331968 :
    ThetaLowerSegment 1017331968 1017397504 (10172987192371 / 10000) (12717058941067 / 12500) := by
  exact
    packedTile32768 1017331968 1017397504 13 3182 31895 30 _ _ (2074043 / 100000) (1037023 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1017397504 :
    ThetaLowerSegment 1017397504 1017463040 (12717058941067 / 12500) (50871490985743 / 50000) := by
  exact
    packedTile32768 1017397504 1017463040 13 3139 31896 30 _ _ (41481 / 2000) (2074053 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1017463040 :
    ThetaLowerSegment 1017463040 1017528576 (50871490985743 / 50000) (50874786660727 / 50000) := by
  exact
    packedTile32768 1017463040 1017528576 13 3178 31897 30 _ _ (259257 / 12500) (2074059 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1017528576 :
    ThetaLowerSegment 1017528576 1017594112 (50874786660727 / 50000)
      (101756150175227 / 100000) := by
  exact
    packedTile32768 1017528576 1017594112 13 3171 31898 30 _ _ (2074063 / 100000) (1037033 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1017594112 :
    ThetaLowerSegment 1017594112 1017659648 (101756150175227 / 100000)
      (25440703539731 / 25000) := by
  exact
    packedTile32768 1017594112 1017659648 13 3213 31899 30 _ _ (2074069 / 100000) (259259 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1017659648 :
    ThetaLowerSegment 1017659648 1017725184 (25440703539731 / 25000) (25442353467189 / 25000) := by
  exact
    packedTile32768 1017659648 1017725184 13 3182 31900 30 _ _ (518519 / 25000) (2074079 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1017725184 :
    ThetaLowerSegment 1017725184 1017790720 (25442353467189 / 25000) (25444010658707 / 25000) := by
  exact
    packedTile32768 1017725184 1017790720 13 3196 31901 30 _ _ (1037041 / 50000) (414817 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1017790720 :
    ThetaLowerSegment 1017790720 1017856256 (25444010658707 / 25000) (3180705889366 / 3125) := by
  exact
    packedTile32768 1017790720 1017856256 13 3156 31902 30 _ _ (2074089 / 100000) (518523 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1017856256 :
    ThetaLowerSegment 1017856256 1017921792 (3180705889366 / 3125) (101789099043917 / 100000) := by
  exact
    packedTile32768 1017856256 1017921792 13 3139 31903 30 _ _ (414819 / 20000) (1037049 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1017921792 :
    ThetaLowerSegment 1017921792 1017987328 (101789099043917 / 100000)
      (50897827638589 / 50000) := by
  exact
    packedTile32768 1017921792 1017987328 13 3161 31904 30 _ _ (2074101 / 100000) (259263 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1017987328 :
    ThetaLowerSegment 1017987328 1018052864 (50897827638589 / 50000) (50901055987691 / 50000) := by
  exact
    packedTile32768 1017987328 1018052864 13 3113 31905 30 _ _ (518527 / 25000) (2074111 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1018052864 :
    ThetaLowerSegment 1018052864 1018118400 (50901055987691 / 50000) (2036173406477 / 2000) := by
  exact
    packedTile32768 1018052864 1018118400 13 3162 31906 30 _ _ (1037057 / 50000) (2074117 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1018118400 :
    ThetaLowerSegment 1018118400 1018183936 (2036173406477 / 2000) (101815409142979 / 100000) := by
  exact
    packedTile32768 1018118400 1018183936 13 3249 31907 30 _ _ (2074121 / 100000) (518531 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1018183936 :
    ThetaLowerSegment 1018183936 1018249472 (101815409142979 / 100000) (4072877539791 / 4000) := by
  exact
    packedTile32768 1018183936 1018249472 13 3148 31908 30 _ _ (2074127 / 100000) (207413 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1018249472 :
    ThetaLowerSegment 1018249472 1018315008 (4072877539791 / 4000) (20365690255107 / 20000) := by
  exact
    packedTile32768 1018249472 1018315008 13 3140 31910 30 _ _ (1037067 / 50000) (2074137 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1018315008 :
    ThetaLowerSegment 1018315008 1018380544 (20365690255107 / 20000) (20366992400199 / 20000) := by
  exact
    packedTile32768 1018315008 1018380544 13 3139 31911 30 _ _ (103707 / 5000) (2074143 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1018380544 :
    ThetaLowerSegment 1018380544 1018446080 (20366992400199 / 20000)
      (101841528747231 / 100000) := by
  exact
    packedTile32768 1018380544 1018446080 13 3166 31912 30 _ _ (1037073 / 50000) (2074149 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1018446080 :
    ThetaLowerSegment 1018446080 1018511616 (101841528747231 / 100000)
      (101847983511367 / 100000) := by
  exact
    packedTile32768 1018446080 1018511616 13 3112 31913 30 _ _ (2074153 / 100000) (518539 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1018511616 :
    ThetaLowerSegment 1018511616 1018577152 (101847983511367 / 100000)
      (12731814898297 / 12500) := by
  exact
    packedTile32768 1018511616 1018577152 13 3151 31914 30 _ _ (2074159 / 100000) (1037081 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1018577152 :
    ThetaLowerSegment 1018577152 1018642688 (12731814898297 / 12500) (25465279795647 / 25000) := by
  exact
    packedTile32768 1018577152 1018642688 13 3182 31915 30 _ _ (1037083 / 50000) (2074169 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1018642688 :
    ThetaLowerSegment 1018642688 1018708224 (25465279795647 / 25000) (6366726875531 / 6250) := by
  exact
    packedTile32768 1018642688 1018708224 13 3139 31916 30 _ _ (518543 / 25000) (82967 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1018708224 :
    ThetaLowerSegment 1018708224 1018773760 (6366726875531 / 6250) (50937061094383 / 50000) := by
  exact
    packedTile32768 1018708224 1018773760 13 3130 31917 30 _ _ (2074179 / 100000) (1037091 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1018773760 :
    ThetaLowerSegment 1018773760 1018839296 (50937061094383 / 50000) (12735076798477 / 12500) := by
  exact
    packedTile32768 1018773760 1018839296 13 3130 31918 30 _ _ (414837 / 20000) (518547 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1018839296 :
    ThetaLowerSegment 1018839296 1018904832 (12735076798477 / 12500) (20377462390111 / 20000) := by
  exact
    packedTile32768 1018839296 1018904832 13 3229 31919 30 _ _ (2074191 / 100000) (1037097 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1018904832 :
    ThetaLowerSegment 1018904832 1018970368 (20377462390111 / 20000)
      (101893791745107 / 100000) := by
  exact
    packedTile32768 1018904832 1018970368 13 3124 31920 30 _ _ (1037099 / 50000) (2074201 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1018970368 :
    ThetaLowerSegment 1018970368 1019035904 (101893791745107 / 100000)
      (20380065927223 / 20000) := by
  exact
    packedTile32768 1018970368 1019035904 13 3152 31921 30 _ _ (518551 / 25000) (2074207 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1019035904 :
    ThetaLowerSegment 1019035904 1019101440 (20380065927223 / 20000)
      (101906813619701 / 100000) := by
  exact
    packedTile32768 1019035904 1019101440 13 3126 31922 30 _ _ (2074211 / 100000) (1037107 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1019101440 :
    ThetaLowerSegment 1019101440 1019166976 (101906813619701 / 100000)
      (50956693406687 / 50000) := by
  exact
    packedTile32768 1019101440 1019166976 13 3169 31923 30 _ _ (2074217 / 100000) (103711 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1019166976 :
    ThetaLowerSegment 1019166976 1019232512 (50956693406687 / 50000) (50959957198151 / 50000) := by
  exact
    packedTile32768 1019166976 1019232512 13 3147 31924 30 _ _ (129639 / 6250) (2074227 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1019232512 :
    ThetaLowerSegment 1019232512 1019298048 (50959957198151 / 50000) (50963249001161 / 50000) := by
  exact
    packedTile32768 1019232512 1019298048 13 3174 31925 30 _ _ (207423 / 10000) (2074233 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1019298048 :
    ThetaLowerSegment 1019298048 1019363584 (50963249001161 / 50000)
      (101933054665479 / 100000) := by
  exact
    packedTile32768 1019298048 1019363584 13 3161 31926 30 _ _ (2074237 / 100000) (12964 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1019363584 :
    ThetaLowerSegment 1019363584 1019429120 (101933054665479 / 100000)
      (10193952008091 / 10000) := by
  exact
    packedTile32768 1019363584 1019429120 13 3117 31927 30 _ _ (2074243 / 100000) (1037123 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1019429120 :
    ThetaLowerSegment 1019429120 1019494656 (10193952008091 / 10000) (3185813408571 / 3125) := by
  exact
    packedTile32768 1019429120 1019494656 13 3138 31928 30 _ _ (2074249 / 100000) (518563 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1019494656 :
    ThetaLowerSegment 1019494656 1019560192 (3185813408571 / 3125) (3186016037454 / 3125) := by
  exact
    packedTile32768 1019494656 1019560192 13 3126 31929 30 _ _ (129641 / 6250) (2074259 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1019560192 :
    ThetaLowerSegment 1019560192 1019625728 (3186016037454 / 3125) (25489792894887 / 25000) := by
  exact
    packedTile32768 1019560192 1019625728 13 3210 31930 30 _ _ (1037131 / 50000) (414853 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1019625728 :
    ThetaLowerSegment 1019625728 1019691264 (25489792894887 / 25000) (6372859447551 / 6250) := by
  exact
    packedTile32768 1019625728 1019691264 13 3172 31931 30 _ _ (2074269 / 100000) (64821 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1019691264 :
    ThetaLowerSegment 1019691264 1019756800 (6372859447551 / 6250) (101972366023791 / 100000) := by
  exact
    packedTile32768 1019691264 1019756800 13 3189 31932 30 _ _ (82971 / 4000) (1037139 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1019756800 :
    ThetaLowerSegment 1019756800 1019822336 (101972366023791 / 100000)
      (101978958091987 / 100000) := by
  exact
    packedTile32768 1019756800 1019822336 13 3178 31933 30 _ _ (1037141 / 50000) (414857 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1019822336 :
    ThetaLowerSegment 1019822336 1019887872 (101978958091987 / 100000)
      (101985450613427 / 100000) := by
  exact
    packedTile32768 1019822336 1019887872 13 3130 31934 30 _ _ (129643 / 6250) (2074291 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1019887872 :
    ThetaLowerSegment 1019887872 1019953408 (101985450613427 / 100000)
      (101991972193763 / 100000) := by
  exact
    packedTile32768 1019887872 1019953408 13 3144 31935 30 _ _ (1037147 / 50000) (2074297 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1019953408 :
    ThetaLowerSegment 1019953408 1020018944 (101991972193763 / 100000)
      (101998585065351 / 100000) := by
  exact
    packedTile32768 1019953408 1020018944 13 3188 31936 30 _ _ (2074301 / 100000) (64822 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1020018944 :
    ThetaLowerSegment 1020018944 1020084480 (101998585065351 / 100000)
      (102005222847751 / 100000) := by
  exact
    packedTile32768 1020018944 1020084480 13 3200 31937 30 _ _ (2074307 / 100000) (207431 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1020084480 :
    ThetaLowerSegment 1020084480 1020150016 (102005222847751 / 100000)
      (102011858578237 / 100000) := by
  exact
    packedTile32768 1020084480 1020150016 13 3199 31938 30 _ _ (1037157 / 50000) (2074317 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1020150016 :
    ThetaLowerSegment 1020150016 1020215552 (102011858578237 / 100000)
      (102018463213117 / 100000) := by
  exact
    packedTile32768 1020150016 1020215552 13 3184 31939 30 _ _ (25929 / 1250) (2074323 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1020215552 :
    ThetaLowerSegment 1020215552 1020281088 (102018463213117 / 100000)
      (102024945481867 / 100000) := by
  exact
    packedTile32768 1020215552 1020281088 13 3125 31940 30 _ _ (1037163 / 50000) (2074329 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1020281088 :
    ThetaLowerSegment 1020281088 1020346624 (102024945481867 / 100000)
      (102031541860807 / 100000) := by
  exact
    packedTile32768 1020281088 1020346624 13 3180 31941 30 _ _ (2074333 / 100000) (64823 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1020346624 :
    ThetaLowerSegment 1020346624 1020412160 (102031541860807 / 100000) (4081524036829 / 4000) := by
  exact
    packedTile32768 1020346624 1020412160 13 3162 31942 30 _ _ (2074339 / 100000) (1037171 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1020412160 :
    ThetaLowerSegment 1020412160 1020477696 (4081524036829 / 4000) (102044695266659 / 100000) := by
  exact
    packedTile32768 1020412160 1020477696 13 3179 31943 30 _ _ (1037173 / 50000) (2074349 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1020477696 :
    ThetaLowerSegment 1020477696 1020543232 (102044695266659 / 100000)
      (102051289631667 / 100000) := by
  exact
    packedTile32768 1020477696 1020543232 13 3179 31944 30 _ _ (129647 / 6250) (414871 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1020543232 :
    ThetaLowerSegment 1020543232 1020608768 (102051289631667 / 100000)
      (20411557304811 / 20000) := by
  exact
    packedTile32768 1020543232 1020608768 13 3132 31945 30 _ _ (2074359 / 100000) (1037181 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1020608768 :
    ThetaLowerSegment 1020608768 1020674304 (20411557304811 / 20000) (637902614181 / 625) := by
  exact
    packedTile32768 1020608768 1020674304 13 3197 31946 30 _ _ (414873 / 20000) (64824 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1020674304 :
    ThetaLowerSegment 1020674304 1020739840 (637902614181 / 625) (102070946314497 / 100000) := by
  exact
    packedTile32768 1020674304 1020739840 13 3147 31947 30 _ _ (2074371 / 100000) (1037187 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1020739840 :
    ThetaLowerSegment 1020739840 1020805376 (102070946314497 / 100000)
      (102077470233307 / 100000) := by
  exact
    packedTile32768 1020739840 1020805376 13 3145 31949 30 _ _ (1037189 / 50000) (2074381 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1020805376 :
    ThetaLowerSegment 1020805376 1020870912 (102077470233307 / 100000)
      (102084031509899 / 100000) := by
  exact
    packedTile32768 1020805376 1020870912 13 3163 31950 30 _ _ (129649 / 6250) (2074387 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1020870912 :
    ThetaLowerSegment 1020870912 1020936448 (102084031509899 / 100000)
      (51045240395759 / 50000) := by
  exact
    packedTile32768 1020870912 1020936448 13 3109 31951 30 _ _ (2074391 / 100000) (1037197 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1020936448 :
    ThetaLowerSegment 1020936448 1021001984 (51045240395759 / 50000) (51048546984577 / 50000) := by
  exact
    packedTile32768 1020936448 1021001984 13 3188 31952 30 _ _ (2074397 / 100000) (2593 / 125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1021001984 :
    ThetaLowerSegment 1021001984 1021067520 (51048546984577 / 50000) (51051779943211 / 50000) := by
  exact
    packedTile32768 1021001984 1021067520 13 3117 31953 30 _ _ (518601 / 25000) (2074407 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1021067520 :
    ThetaLowerSegment 1021067520 1021133056 (51051779943211 / 50000) (12763761525439 / 12500) := by
  exact
    packedTile32768 1021067520 1021133056 13 3149 31954 30 _ _ (207441 / 10000) (2074413 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1021133056 :
    ThetaLowerSegment 1021133056 1021198592 (12763761525439 / 12500) (12764589217423 / 12500) := by
  exact
    packedTile32768 1021133056 1021198592 13 3192 31955 30 _ _ (129651 / 6250) (2074419 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1021198592 :
    ThetaLowerSegment 1021198592 1021264128 (12764589217423 / 12500)
      (102123320776639 / 100000) := by
  exact
    packedTile32768 1021198592 1021264128 13 3185 31956 30 _ _ (2074423 / 100000) (1037213 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1021264128 :
    ThetaLowerSegment 1021264128 1021329664 (102123320776639 / 100000)
      (51064862269481 / 50000) := by
  exact
    packedTile32768 1021264128 1021329664 13 3087 31957 30 _ _ (2074429 / 100000) (64826 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1021329664 :
    ThetaLowerSegment 1021329664 1021395200 (51064862269481 / 50000) (10213636895747 / 10000) := by
  exact
    packedTile32768 1021329664 1021395200 13 3203 31958 30 _ _ (518609 / 25000) (2074439 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1021395200 :
    ThetaLowerSegment 1021395200 1021460736 (10213636895747 / 10000) (51071476618189 / 50000) := by
  exact
    packedTile32768 1021395200 1021460736 13 3174 31959 30 _ _ (1037221 / 50000) (414889 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1021460736 :
    ThetaLowerSegment 1021460736 1021526272 (51071476618189 / 50000) (51074697198709 / 50000) := by
  exact
    packedTile32768 1021460736 1021526272 13 3105 31960 30 _ _ (129653 / 6250) (2074451 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1021526272 :
    ThetaLowerSegment 1021526272 1021591808 (51074697198709 / 50000) (51077941646329 / 50000) := by
  exact
    packedTile32768 1021526272 1021591808 13 3128 31961 30 _ _ (414891 / 20000) (1037229 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1021591808 :
    ThetaLowerSegment 1021591808 1021657344 (51077941646329 / 50000) (25540623131351 / 25000) := by
  exact
    packedTile32768 1021591808 1021657344 13 3186 31962 30 _ _ (2074461 / 100000) (64827 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1021657344 :
    ThetaLowerSegment 1021657344 1021722880 (25540623131351 / 25000) (25542265072773 / 25000) := by
  exact
    packedTile32768 1021657344 1021722880 13 3166 31963 30 _ _ (518617 / 25000) (2074471 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1021722880 :
    ThetaLowerSegment 1021722880 1021788416 (25542265072773 / 25000) (12771956621183 / 12500) := by
  exact
    packedTile32768 1021722880 1021788416 13 3178 31964 30 _ _ (1037237 / 50000) (2074477 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1021788416 :
    ThetaLowerSegment 1021788416 1021853952 (12771956621183 / 12500)
      (102182156467399 / 100000) := by
  exact
    packedTile32768 1021788416 1021853952 13 3135 31965 30 _ _ (2074481 / 100000) (518621 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1021853952 :
    ThetaLowerSegment 1021853952 1021919488 (102182156467399 / 100000)
      (51094386003221 / 50000) := by
  exact
    packedTile32768 1021853952 1021919488 13 3189 31966 30 _ _ (2074487 / 100000) (207449 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1021919488 :
    ThetaLowerSegment 1021919488 1021985024 (51094386003221 / 50000) (25548820441369 / 25000) := by
  exact
    packedTile32768 1021919488 1021985024 13 3138 31967 30 _ _ (2074493 / 100000) (64828 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1021985024 :
    ThetaLowerSegment 1021985024 1022050560 (25548820441369 / 25000) (6387615213061 / 6250) := by
  exact
    packedTile32768 1021985024 1022050560 13 3163 31968 30 _ _ (4149 / 200) (2074503 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1022050560 :
    ThetaLowerSegment 1022050560 1022116096 (6387615213061 / 6250) (51104179716161 / 50000) := by
  exact
    packedTile32768 1022050560 1022116096 13 3141 31969 30 _ _ (1037253 / 50000) (2074509 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1022116096 :
    ThetaLowerSegment 1022116096 1022181632 (51104179716161 / 50000) (51107436701571 / 50000) := by
  exact
    packedTile32768 1022116096 1022181632 13 3140 31970 30 _ _ (2074513 / 100000) (518629 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1022181632 :
    ThetaLowerSegment 1022181632 1022247168 (51107436701571 / 50000)
      (102221302337523 / 100000) := by
  exact
    packedTile32768 1022181632 1022247168 13 3099 31971 30 _ _ (2074519 / 100000) (1037261 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1022247168 :
    ThetaLowerSegment 1022247168 1022312704 (102221302337523 / 100000)
      (102227837091273 / 100000) := by
  exact
    packedTile32768 1022247168 1022312704 13 3150 31972 30 _ _ (82981 / 4000) (64829 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1022312704 :
    ThetaLowerSegment 1022312704 1022378240 (102227837091273 / 100000)
      (102234432028501 / 100000) := by
  exact
    packedTile32768 1022312704 1022378240 13 3179 31973 30 _ _ (518633 / 25000) (414907 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1022378240 :
    ThetaLowerSegment 1022378240 1022443776 (102234432028501 / 100000)
      (102241091295481 / 100000) := by
  exact
    packedTile32768 1022378240 1022443776 13 3210 31974 30 _ _ (1037269 / 50000) (2074541 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1022443776 :
    ThetaLowerSegment 1022443776 1022509312 (102241091295481 / 100000)
      (51123812018843 / 50000) := by
  exact
    packedTile32768 1022443776 1022509312 13 3149 31975 30 _ _ (414909 / 20000) (518637 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1022509312 :
    ThetaLowerSegment 1022509312 1022574848 (51123812018843 / 50000) (25563533494681 / 25000) := by
  exact
    packedTile32768 1022509312 1022574848 13 3138 31976 30 _ _ (2074551 / 100000) (1037277 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1022574848 :
    ThetaLowerSegment 1022574848 1022640384 (25563533494681 / 25000) (51130309521953 / 50000) := by
  exact
    packedTile32768 1022574848 1022640384 13 3126 31977 30 _ _ (2074557 / 100000) (12966 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1022640384 :
    ThetaLowerSegment 1022640384 1022705920 (51130309521953 / 50000) (10226718711353 / 10000) := by
  exact
    packedTile32768 1022640384 1022705920 13 3166 31978 30 _ _ (518641 / 25000) (2074567 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1022705920 :
    ThetaLowerSegment 1022705920 1022771456 (10226718711353 / 10000) (10227373030731 / 10000) := by
  exact
    packedTile32768 1022705920 1022771456 13 3154 31979 30 _ _ (207457 / 10000) (2074573 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1022771456 :
    ThetaLowerSegment 1022771456 1022836992 (10227373030731 / 10000) (10228028597063 / 10000) := by
  exact
    packedTile32768 1022771456 1022836992 13 3160 31980 30 _ _ (2074577 / 100000) (103729 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1022836992 :
    ThetaLowerSegment 1022836992 1022902528 (10228028597063 / 10000) (51143445721451 / 50000) := by
  exact
    packedTile32768 1022836992 1022902528 13 3184 31981 30 _ _ (2074583 / 100000) (1037293 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1022902528 :
    ThetaLowerSegment 1022902528 1022968064 (51143445721451 / 50000) (25573387200553 / 25000) := by
  exact
    packedTile32768 1022902528 1022968064 13 3209 31982 30 _ _ (207459 / 10000) (2074593 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1022968064 :
    ThetaLowerSegment 1022968064 1023033600 (25573387200553 / 25000) (12787512287723 / 12500) := by
  exact
    packedTile32768 1022968064 1023033600 13 3157 31983 30 _ _ (518649 / 25000) (2074599 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1023033600 :
    ThetaLowerSegment 1023033600 1023099136 (12787512287723 / 12500) (12788337979319 / 12500) := by
  exact
    packedTile32768 1023033600 1023099136 13 3184 31984 30 _ _ (1037301 / 50000) (414921 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1023099136 :
    ThetaLowerSegment 1023099136 1023164672 (12788337979319 / 12500) (51156619426451 / 50000) := by
  exact
    packedTile32768 1023099136 1023164672 13 3150 31985 30 _ _ (2074609 / 100000) (518653 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1023164672 :
    ThetaLowerSegment 1023164672 1023230208 (51156619426451 / 50000) (51159855825851 / 50000) := by
  exact
    packedTile32768 1023164672 1023230208 13 3120 31986 30 _ _ (414923 / 20000) (1037309 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1023230208 :
    ThetaLowerSegment 1023230208 1023295744 (51159855825851 / 50000) (12790781098203 / 12500) := by
  exact
    packedTile32768 1023230208 1023295744 13 3151 31987 30 _ _ (1037311 / 50000) (16597 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1023295744 :
    ThetaLowerSegment 1023295744 1023361280 (12790781098203 / 12500) (3197898199102 / 3125) := by
  exact
    packedTile32768 1023295744 1023361280 13 3130 31988 30 _ _ (518657 / 25000) (2074631 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1023361280 :
    ThetaLowerSegment 1023361280 1023426816 (3197898199102 / 3125) (1023392857669 / 1000) := by
  exact
    packedTile32768 1023361280 1023426816 13 3154 31990 30 _ _ (1037317 / 50000) (2074637 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1023426816 :
    ThetaLowerSegment 1023426816 1023492352 (1023392857669 / 1000) (639661769533 / 625) := by
  exact
    packedTile32768 1023426816 1023492352 13 3180 31991 30 _ _ (2074641 / 100000) (518661 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1023492352 :
    ThetaLowerSegment 1023492352 1023557888 (639661769533 / 625) (10235245975627 / 10000) := by
  exact
    packedTile32768 1023492352 1023557888 13 3170 31992 30 _ _ (2074647 / 100000) (41493 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1023557888 :
    ThetaLowerSegment 1023557888 1023623424 (10235245975627 / 10000) (51179536876611 / 50000) := by
  exact
    packedTile32768 1023557888 1023623424 13 3188 31993 30 _ _ (1037327 / 50000) (2074657 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1023623424 :
    ThetaLowerSegment 1023623424 1023688960 (51179536876611 / 50000) (51182770234221 / 50000) := by
  exact
    packedTile32768 1023623424 1023688960 13 3117 31994 30 _ _ (103733 / 5000) (2074663 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1023688960 :
    ThetaLowerSegment 1023688960 1023754496 (51182770234221 / 50000) (51186031609173 / 50000) := by
  exact
    packedTile32768 1023688960 1023754496 13 3144 31995 30 _ _ (1037333 / 50000) (2074669 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1023754496 :
    ThetaLowerSegment 1023754496 1023820032 (51186031609173 / 50000) (51189371832703 / 50000) := by
  exact
    packedTile32768 1023754496 1023820032 13 3220 31996 30 _ _ (2074673 / 100000) (518669 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1023820032 :
    ThetaLowerSegment 1023820032 1023885568 (51189371832703 / 50000) (10238512537801 / 10000) := by
  exact
    packedTile32768 1023820032 1023885568 13 3076 31997 30 _ _ (2074679 / 100000) (1037341 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1023885568 :
    ThetaLowerSegment 1023885568 1023951104 (10238512537801 / 10000) (6399483846979 / 6250) := by
  exact
    packedTile32768 1023885568 1023951104 13 3189 31998 30 _ _ (1037343 / 50000) (2074689 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1023951104 :
    ThetaLowerSegment 1023951104 1024016640 (6399483846979 / 6250) (12799769043743 / 12500) := by
  exact
    packedTile32768 1023951104 1024016640 13 3090 31999 30 _ _ (518673 / 25000) (414939 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1024016640 :
    ThetaLowerSegment 1024016640 1024082176 (12799769043743 / 12500) (51202407102611 / 50000) := by
  exact
    packedTile32768 1024016640 1024082176 13 3211 32000 30 _ _ (1037349 / 50000) (2074701 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1024082176 :
    ThetaLowerSegment 1024082176 1024147712 (51202407102611 / 50000) (51205685136511 / 50000) := by
  exact
    packedTile32768 1024082176 1024147712 13 3160 32001 30 _ _ (414941 / 20000) (518677 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1024147712 :
    ThetaLowerSegment 1024147712 1024213248 (51205685136511 / 50000) (4096713983819 / 4000) := by
  exact
    packedTile32768 1024147712 1024213248 13 3123 32002 30 _ _ (2074711 / 100000) (1037357 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1024213248 :
    ThetaLowerSegment 1024213248 1024278784 (4096713983819 / 4000) (20484874916717 / 20000) := by
  exact
    packedTile32768 1024213248 1024278784 13 3145 32003 30 _ _ (1037359 / 50000) (2074721 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1024278784 :
    ThetaLowerSegment 1024278784 1024344320 (20484874916717 / 20000) (20486179918113 / 20000) := by
  exact
    packedTile32768 1024278784 1024344320 13 3145 32004 30 _ _ (518681 / 25000) (2074727 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1024344320 :
    ThetaLowerSegment 1024344320 1024409856 (20486179918113 / 20000) (20487511479827 / 20000) := by
  exact
    packedTile32768 1024344320 1024409856 13 3209 32005 30 _ _ (207473 / 10000) (2074733 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1024409856 :
    ThetaLowerSegment 1024409856 1024475392 (20487511479827 / 20000) (51222047447711 / 50000) := by
  exact
    packedTile32768 1024409856 1024475392 13 3151 32006 30 _ _ (2074737 / 100000) (103737 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1024475392 :
    ThetaLowerSegment 1024475392 1024540928 (51222047447711 / 50000)
      (102450711250849 / 100000) := by
  exact
    packedTile32768 1024475392 1024540928 13 3189 32007 30 _ _ (2074743 / 100000) (1037373 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1024540928 :
    ThetaLowerSegment 1024540928 1024606464 (102450711250849 / 100000)
      (102457228040599 / 100000) := by
  exact
    packedTile32768 1024540928 1024606464 13 3141 32008 30 _ _ (8299 / 400) (2074753 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1024606464 :
    ThetaLowerSegment 1024606464 1024672000 (102457228040599 / 100000)
      (20492784240691 / 20000) := by
  exact
    packedTile32768 1024606464 1024672000 13 3226 32009 30 _ _ (518689 / 25000) (2074759 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1024672000 :
    ThetaLowerSegment 1024672000 1024737536 (20492784240691 / 20000)
      (102470460853279 / 100000) := by
  exact
    packedTile32768 1024672000 1024737536 13 3152 32010 30 _ _ (1037381 / 50000) (414953 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1024737536 :
    ThetaLowerSegment 1024737536 1024803072 (102470460853279 / 100000)
      (102477058618699 / 100000) := by
  exact
    packedTile32768 1024737536 1024803072 13 3180 32011 30 _ _ (2074769 / 100000) (518693 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1024803072 :
    ThetaLowerSegment 1024803072 1024868608 (102477058618699 / 100000)
      (25620911507331 / 25000) := by
  exact
    packedTile32768 1024803072 1024868608 13 3175 32012 30 _ _ (82991 / 4000) (1037389 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1024868608 :
    ThetaLowerSegment 1024868608 1024934144 (25620911507331 / 25000) (6405630125193 / 6250) := by
  exact
    packedTile32768 1024868608 1024934144 13 3102 32013 30 _ _ (1037391 / 50000) (414957 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1024934144 :
    ThetaLowerSegment 1024934144 1024999680 (6405630125193 / 6250) (25624176700293 / 25000) := by
  exact
    packedTile32768 1024934144 1024999680 13 3193 32014 30 _ _ (518697 / 25000) (2074791 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1024999680 :
    ThetaLowerSegment 1024999680 1025065216 (25624176700293 / 25000) (51251624313327 / 50000) := by
  exact
    packedTile32768 1024999680 1025065216 13 3153 32015 30 _ _ (1037397 / 50000) (2074797 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1025065216 :
    ThetaLowerSegment 1025065216 1025130752 (51251624313327 / 50000) (51254931546121 / 50000) := by
  exact
    packedTile32768 1025065216 1025130752 13 3188 32016 30 _ _ (2074801 / 100000) (518701 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1025130752 :
    ThetaLowerSegment 1025130752 1025196288 (51254931546121 / 50000) (25629099683573 / 25000) := by
  exact
    packedTile32768 1025130752 1025196288 13 3150 32017 30 _ _ (2074807 / 100000) (207481 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1025196288 :
    ThetaLowerSegment 1025196288 1025261824 (25629099683573 / 25000)
      (102522924021177 / 100000) := by
  exact
    packedTile32768 1025196288 1025261824 13 3145 32018 30 _ _ (2074813 / 100000) (64838 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1025261824 :
    ThetaLowerSegment 1025261824 1025327360 (102522924021177 / 100000)
      (102529441030797 / 100000) := by
  exact
    packedTile32768 1025261824 1025327360 13 3141 32019 30 _ _ (103741 / 5000) (2074823 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1025327360 :
    ThetaLowerSegment 1025327360 1025392896 (102529441030797 / 100000)
      (20507223564173 / 20000) := by
  exact
    packedTile32768 1025327360 1025392896 13 3218 32020 30 _ _ (1037413 / 50000) (2074829 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1025392896 :
    ThetaLowerSegment 1025392896 1025458432 (20507223564173 / 20000) (51271329884657 / 50000) := by
  exact
    packedTile32768 1025392896 1025458432 13 3153 32021 30 _ _ (2074833 / 100000) (518709 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1025458432 :
    ThetaLowerSegment 1025458432 1025523968 (51271329884657 / 50000) (20509842837143 / 20000) := by
  exact
    packedTile32768 1025458432 1025523968 13 3159 32022 30 _ _ (2074839 / 100000) (1037421 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1025523968 :
    ThetaLowerSegment 1025523968 1025589504 (20509842837143 / 20000) (20511158288873 / 20000) := by
  exact
    packedTile32768 1025523968 1025589504 13 3170 32023 30 _ _ (414969 / 20000) (64839 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1025589504 :
    ThetaLowerSegment 1025589504 1025655040 (20511158288873 / 20000)
      (102562374949761 / 100000) := by
  exact
    packedTile32768 1025589504 1025655040 13 3173 32024 30 _ _ (518713 / 25000) (414971 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1025655040 :
    ThetaLowerSegment 1025655040 1025720576 (102562374949761 / 100000)
      (102569078815959 / 100000) := by
  exact
    packedTile32768 1025655040 1025720576 13 3231 32025 30 _ _ (1037429 / 50000) (2074861 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1025720576 :
    ThetaLowerSegment 1025720576 1025786112 (102569078815959 / 100000)
      (25643903141461 / 25000) := by
  exact
    packedTile32768 1025720576 1025786112 13 3149 32026 30 _ _ (414973 / 20000) (518717 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1025786112 :
    ThetaLowerSegment 1025786112 1025851648 (25643903141461 / 25000)
      (102582030141847 / 100000) := by
  exact
    packedTile32768 1025786112 1025851648 13 3093 32027 30 _ _ (2074871 / 100000) (1037437 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1025851648 :
    ThetaLowerSegment 1025851648 1025917184 (102582030141847 / 100000)
      (102588566004397 / 100000) := by
  exact
    packedTile32768 1025851648 1025917184 13 3150 32028 30 _ _ (2074877 / 100000) (12968 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1025917184 :
    ThetaLowerSegment 1025917184 1025982720 (102588566004397 / 100000)
      (102595159985749 / 100000) := by
  exact
    packedTile32768 1025917184 1025982720 13 3178 32029 30 _ _ (518721 / 25000) (2074887 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1025982720 :
    ThetaLowerSegment 1025982720 1026048256 (102595159985749 / 100000)
      (102601677215239 / 100000) := by
  exact
    packedTile32768 1025982720 1026048256 13 3141 32030 30 _ _ (207489 / 10000) (2074893 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1026048256 :
    ThetaLowerSegment 1026048256 1026113792 (102601677215239 / 100000)
      (51304095158461 / 50000) := by
  exact
    packedTile32768 1026048256 1026113792 13 3139 32031 30 _ _ (2074897 / 100000) (20749 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1026113792 :
    ThetaLowerSegment 1026113792 1026179328 (51304095158461 / 50000) (641341987261 / 625) := by
  exact
    packedTile32768 1026113792 1026179328 13 3146 32033 30 _ _ (2074903 / 100000) (1037453 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1026179328 :
    ThetaLowerSegment 1026179328 1026244864 (641341987261 / 625) (51310693359643 / 50000) := by
  exact
    packedTile32768 1026179328 1026244864 13 3214 32034 30 _ _ (2074909 / 100000) (64841 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1026244864 :
    ThetaLowerSegment 1026244864 1026310400 (51310693359643 / 50000) (51313958239969 / 50000) := by
  exact
    packedTile32768 1026244864 1026310400 13 3147 32035 30 _ _ (518729 / 25000) (2074919 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1026310400 :
    ThetaLowerSegment 1026310400 1026375936 (51313958239969 / 50000) (51317240766573 / 50000) := by
  exact
    packedTile32768 1026310400 1026375936 13 3164 32036 30 _ _ (1037461 / 50000) (82997 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1026375936 :
    ThetaLowerSegment 1026375936 1026441472 (51317240766573 / 50000) (51320500478461 / 50000) := by
  exact
    packedTile32768 1026375936 1026441472 13 3142 32037 30 _ _ (129683 / 6250) (2074931 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1026441472 :
    ThetaLowerSegment 1026441472 1026507008 (51320500478461 / 50000) (12830951462479 / 12500) := by
  exact
    packedTile32768 1026441472 1026507008 13 3186 32038 30 _ _ (414987 / 20000) (1037469 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1026507008 :
    ThetaLowerSegment 1026507008 1026572544 (12830951462479 / 12500)
      (102654266035619 / 100000) := by
  exact
    packedTile32768 1026507008 1026572544 13 3207 32039 30 _ _ (2074941 / 100000) (64842 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1026572544 :
    ThetaLowerSegment 1026572544 1026638080 (102654266035619 / 100000)
      (102660833246039 / 100000) := by
  exact
    packedTile32768 1026572544 1026638080 13 3165 32040 30 _ _ (518737 / 25000) (2074951 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1026638080 :
    ThetaLowerSegment 1026638080 1026703616 (102660833246039 / 100000)
      (102667446124437 / 100000) := by
  exact
    packedTile32768 1026638080 1026703616 13 3187 32041 30 _ _ (1037477 / 50000) (2074957 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1026703616 :
    ThetaLowerSegment 1026703616 1026769152 (102667446124437 / 100000)
      (102673901324997 / 100000) := by
  exact
    packedTile32768 1026703616 1026769152 13 3111 32042 30 _ _ (25937 / 1250) (2074963 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1026769152 :
    ThetaLowerSegment 1026769152 1026834688 (102673901324997 / 100000)
      (12835048199609 / 12500) := by
  exact
    packedTile32768 1026769152 1026834688 13 3125 32043 30 _ _ (2074967 / 100000) (207497 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1026834688 :
    ThetaLowerSegment 1026834688 1026900224 (12835048199609 / 12500)
      (102686907237011 / 100000) := by
  exact
    packedTile32768 1026834688 1026900224 13 3143 32044 30 _ _ (2074973 / 100000) (64843 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1026900224 :
    ThetaLowerSegment 1026900224 1026965760 (102686907237011 / 100000)
      (102693430974131 / 100000) := by
  exact
    packedTile32768 1026900224 1026965760 13 3144 32045 30 _ _ (103749 / 5000) (2074983 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1026965760 :
    ThetaLowerSegment 1026965760 1027031296 (102693430974131 / 100000)
      (20539976421121 / 20000) := by
  exact
    packedTile32768 1026965760 1027031296 13 3109 32046 30 _ _ (1037493 / 50000) (2074989 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1027031296 :
    ThetaLowerSegment 1027031296 1027096832 (20539976421121 / 20000)
      (102706497180101 / 100000) := by
  exact
    packedTile32768 1027031296 1027096832 13 3188 32047 30 _ _ (129687 / 6250) (414999 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1027096832 :
    ThetaLowerSegment 1027096832 1027162368 (102706497180101 / 100000)
      (102713016826959 / 100000) := by
  exact
    packedTile32768 1027096832 1027162368 13 3142 32048 30 _ _ (2074999 / 100000) (1037501 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1027162368 :
    ThetaLowerSegment 1027162368 1027227904 (102713016826959 / 100000)
      (102719544792689 / 100000) := by
  exact
    packedTile32768 1027162368 1027227904 13 3146 32049 30 _ _ (415001 / 20000) (64844 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1027227904 :
    ThetaLowerSegment 1027227904 1027293440 (102719544792689 / 100000)
      (102726105977471 / 100000) := by
  exact
    packedTile32768 1027227904 1027293440 13 3162 32050 30 _ _ (2075011 / 100000) (1037507 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1027293440 :
    ThetaLowerSegment 1027293440 1027358976 (102726105977471 / 100000)
      (102732521933127 / 100000) := by
  exact
    packedTile32768 1027293440 1027358976 13 3092 32051 30 _ _ (1037509 / 50000) (2075021 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1027358976 :
    ThetaLowerSegment 1027358976 1027424512 (102732521933127 / 100000)
      (102738939982359 / 100000) := by
  exact
    packedTile32768 1027358976 1027424512 13 3093 32052 30 _ _ (129689 / 6250) (2075027 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1027424512 :
    ThetaLowerSegment 1027424512 1027490048 (102738939982359 / 100000)
      (102745505380443 / 100000) := by
  exact
    packedTile32768 1027424512 1027490048 13 3164 32053 30 _ _ (2075031 / 100000) (1037517 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1027490048 :
    ThetaLowerSegment 1027490048 1027555584 (102745505380443 / 100000)
      (102752120598399 / 100000) := by
  exact
    packedTile32768 1027490048 1027555584 13 3188 32054 30 _ _ (2075037 / 100000) (12969 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1027555584 :
    ThetaLowerSegment 1027555584 1027621120 (102752120598399 / 100000)
      (51379281803457 / 50000) := by
  exact
    packedTile32768 1027555584 1027621120 13 3105 32055 30 _ _ (2075043 / 100000) (1037523 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1027621120 :
    ThetaLowerSegment 1027621120 1027686656 (51379281803457 / 50000) (51382554157307 / 50000) := by
  exact
    packedTile32768 1027621120 1027686656 13 3154 32056 30 _ _ (41501 / 2000) (2075053 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1027686656 :
    ThetaLowerSegment 1027686656 1027752192 (51382554157307 / 50000) (51385871134323 / 50000) := by
  exact
    packedTile32768 1027686656 1027752192 13 3197 32057 30 _ _ (129691 / 6250) (2075059 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1027752192 :
    ThetaLowerSegment 1027752192 1027817728 (51385871134323 / 50000) (51389189158461 / 50000) := by
  exact
    packedTile32768 1027752192 1027817728 13 3198 32058 30 _ _ (1037531 / 50000) (415013 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1027817728 :
    ThetaLowerSegment 1027817728 1027883264 (51389189158461 / 50000)
      (102784896108651 / 100000) := by
  exact
    packedTile32768 1027817728 1027883264 13 3141 32059 30 _ _ (2075069 / 100000) (64846 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1027883264 :
    ThetaLowerSegment 1027883264 1027948800 (102784896108651 / 100000)
      (25697852442269 / 25000) := by
  exact
    packedTile32768 1027883264 1027948800 13 3139 32060 30 _ _ (83003 / 4000) (1037539 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1027948800 :
    ThetaLowerSegment 1027948800 1028014336 (25697852442269 / 25000) (51398934749671 / 50000) := by
  exact
    packedTile32768 1027948800 1028014336 13 3113 32061 30 _ _ (1037541 / 50000) (415017 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1028014336 :
    ThetaLowerSegment 1028014336 1028079872 (51398934749671 / 50000) (51402190562743 / 50000) := by
  exact
    packedTile32768 1028014336 1028079872 13 3138 32062 30 _ _ (129693 / 6250) (2075091 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1028079872 :
    ThetaLowerSegment 1028079872 1028145408 (51402190562743 / 50000) (25702741349687 / 25000) := by
  exact
    packedTile32768 1028079872 1028145408 13 3173 32063 30 _ _ (1037547 / 50000) (2075097 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1028145408 :
    ThetaLowerSegment 1028145408 1028210944 (25702741349687 / 25000)
      (102817549694221 / 100000) := by
  exact
    packedTile32768 1028145408 1028210944 13 3173 32064 30 _ _ (2075101 / 100000) (64847 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1028210944 :
    ThetaLowerSegment 1028210944 1028276480 (102817549694221 / 100000)
      (102824098731913 / 100000) := by
  exact
    packedTile32768 1028210944 1028276480 13 3156 32065 30 _ _ (2075107 / 100000) (207511 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1028276480 :
    ThetaLowerSegment 1028276480 1028342016 (102824098731913 / 100000)
      (102830614586733 / 100000) := by
  exact
    packedTile32768 1028276480 1028342016 13 3140 32066 30 _ _ (2075113 / 100000) (518779 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1028342016 :
    ThetaLowerSegment 1028342016 1028407552 (102830614586733 / 100000)
      (102837128388413 / 100000) := by
  exact
    packedTile32768 1028342016 1028407552 13 3139 32067 30 _ _ (25939 / 1250) (2075123 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1028407552 :
    ThetaLowerSegment 1028407552 1028473088 (102837128388413 / 100000)
      (102843874623039 / 100000) := by
  exact
    packedTile32768 1028407552 1028473088 13 3251 32068 30 _ _ (1037563 / 50000) (2075129 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1028473088 :
    ThetaLowerSegment 1028473088 1028538624 (102843874623039 / 100000)
      (102850485996777 / 100000) := by
  exact
    packedTile32768 1028473088 1028538624 13 3186 32069 30 _ _ (2075133 / 100000) (64848 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1028538624 :
    ThetaLowerSegment 1028538624 1028604160 (102850485996777 / 100000)
      (20571413667537 / 20000) := by
  exact
    packedTile32768 1028538624 1028604160 13 3172 32070 30 _ _ (2075139 / 100000) (1037571 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1028604160 :
    ThetaLowerSegment 1028604160 1028669696 (20571413667537 / 20000) (20572711048191 / 20000) := by
  exact
    packedTile32768 1028604160 1028669696 13 3126 32071 30 _ _ (415029 / 20000) (518787 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1028669696 :
    ThetaLowerSegment 1028669696 1028735232 (20572711048191 / 20000)
      (102869961235179 / 100000) := by
  exact
    packedTile32768 1028669696 1028735232 13 3087 32072 30 _ _ (129697 / 6250) (415031 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1028735232 :
    ThetaLowerSegment 1028735232 1028800768 (102869961235179 / 100000)
      (102876568538251 / 100000) := by
  exact
    packedTile32768 1028735232 1028800768 13 3184 32073 30 _ _ (1037579 / 50000) (2075161 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1028800768 :
    ThetaLowerSegment 1028800768 1028866304 (102876568538251 / 100000)
      (102883126056491 / 100000) := by
  exact
    packedTile32768 1028800768 1028866304 13 3160 32074 30 _ _ (518791 / 25000) (2075167 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1028866304 :
    ThetaLowerSegment 1028866304 1028931840 (102883126056491 / 100000)
      (51444842836011 / 50000) := by
  exact
    packedTile32768 1028866304 1028931840 13 3161 32075 30 _ _ (2075171 / 100000) (1037587 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1028931840 :
    ThetaLowerSegment 1028931840 1028997376 (51444842836011 / 50000)
      (102896237005811 / 100000) := by
  exact
    packedTile32768 1028931840 1028997376 13 3157 32076 30 _ _ (2075177 / 100000) (103759 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1028997376 :
    ThetaLowerSegment 1028997376 1029062912 (102896237005811 / 100000)
      (102902894196083 / 100000) := by
  exact
    packedTile32768 1028997376 1029062912 13 3208 32077 30 _ _ (129699 / 6250) (2075187 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1029062912 :
    ThetaLowerSegment 1029062912 1029128448 (102902894196083 / 100000)
      (102909424819013 / 100000) := by
  exact
    packedTile32768 1029062912 1029128448 13 3147 32079 30 _ _ (207519 / 10000) (2075193 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1029128448 :
    ThetaLowerSegment 1029128448 1029193984 (102909424819013 / 100000)
      (102916104874937 / 100000) := by
  exact
    packedTile32768 1029128448 1029193984 13 3219 32080 30 _ _ (518799 / 25000) (2075199 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1029193984 :
    ThetaLowerSegment 1029193984 1029259520 (102916104874937 / 100000)
      (102922774577379 / 100000) := by
  exact
    packedTile32768 1029193984 1029259520 13 3214 32081 30 _ _ (2075203 / 100000) (1037603 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1029259520 :
    ThetaLowerSegment 1029259520 1029325056 (102922774577379 / 100000)
      (10292928865843 / 10000) := by
  exact
    packedTile32768 1029259520 1029325056 13 3139 32082 30 _ _ (2075209 / 100000) (518803 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1029325056 :
    ThetaLowerSegment 1029325056 1029390592 (10292928865843 / 10000) (10293580483353 / 10000) := by
  exact
    packedTile32768 1029325056 1029390592 13 3140 32083 30 _ _ (415043 / 20000) (1037609 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1029390592 :
    ThetaLowerSegment 1029390592 1029456128 (10293580483353 / 10000) (51471172966637 / 50000) := by
  exact
    packedTile32768 1029390592 1029456128 13 3152 32084 30 _ _ (1037611 / 50000) (83009 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1029456128 :
    ThetaLowerSegment 1029456128 1029521664 (51471172966637 / 50000) (51474465315859 / 50000) := by
  exact
    packedTile32768 1029456128 1029521664 13 3173 32085 30 _ _ (518807 / 25000) (2075231 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1029521664 :
    ThetaLowerSegment 1029521664 1029587200 (51474465315859 / 50000)
      (102955544405663 / 100000) := by
  exact
    packedTile32768 1029521664 1029587200 13 3187 32086 30 _ _ (415047 / 20000) (1037619 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1029587200 :
    ThetaLowerSegment 1029587200 1029652736 (102955544405663 / 100000)
      (102962102167223 / 100000) := by
  exact
    packedTile32768 1029587200 1029652736 13 3160 32087 30 _ _ (2075241 / 100000) (518811 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1029652736 :
    ThetaLowerSegment 1029652736 1029718272 (102962102167223 / 100000) (6435532816043 / 6250) := by
  exact
    packedTile32768 1029652736 1029718272 13 3095 32088 30 _ _ (2075247 / 100000) (8301 / 400)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1029718272 :
    ThetaLowerSegment 1029718272 1029783808 (6435532816043 / 6250) (25743796655507 / 25000) := by
  exact
    packedTile32768 1029718272 1029783808 13 3210 32089 30 _ _ (1037627 / 50000) (2075257 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1029783808 :
    ThetaLowerSegment 1029783808 1029849344 (25743796655507 / 25000) (25745430922757 / 25000) := by
  exact
    packedTile32768 1029783808 1029849344 13 3150 32090 30 _ _ (103763 / 5000) (2075263 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1029849344 :
    ThetaLowerSegment 1029849344 1029914880 (25745430922757 / 25000) (12873531559733 / 12500) := by
  exact
    packedTile32768 1029849344 1029914880 13 3146 32091 30 _ _ (1037633 / 50000) (2075269 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1029914880 :
    ThetaLowerSegment 1029914880 1029980416 (12873531559733 / 12500)
      (102994770910357 / 100000) := by
  exact
    packedTile32768 1029914880 1029980416 13 3141 32092 30 _ _ (2075273 / 100000) (518819 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1029980416 :
    ThetaLowerSegment 1029980416 1030045952 (102994770910357 / 100000) (20600247911 / 20) := by
  exact
    packedTile32768 1029980416 1030045952 13 3117 32093 30 _ _ (2075279 / 100000) (1037641 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1030045952 :
    ThetaLowerSegment 1030045952 1030111488 (20600247911 / 20) (2575194521333 / 2500) := by
  exact
    packedTile32768 1030045952 1030111488 13 3152 32094 30 _ _ (415057 / 20000) (259411 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1030111488 :
    ThetaLowerSegment 1030111488 1030177024 (2575194521333 / 2500) (12876791309359 / 12500) := by
  exact
    packedTile32768 1030111488 1030177024 13 3156 32095 30 _ _ (518823 / 25000) (415059 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1030177024 :
    ThetaLowerSegment 1030177024 1030242560 (12876791309359 / 12500) (6438806044859 / 6250) := by
  exact
    packedTile32768 1030177024 1030242560 13 3164 32096 30 _ _ (1037649 / 50000) (2075301 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1030242560 :
    ThetaLowerSegment 1030242560 1030308096 (6438806044859 / 6250) (25756874046911 / 25000) := by
  exact
    packedTile32768 1030242560 1030308096 13 3180 32097 30 _ _ (415061 / 20000) (518827 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1030308096 :
    ThetaLowerSegment 1030308096 1030373632 (25756874046911 / 25000)
      (103034052095093 / 100000) := by
  exact
    packedTile32768 1030308096 1030373632 13 3159 32098 30 _ _ (2075311 / 100000) (1037657 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1030373632 :
    ThetaLowerSegment 1030373632 1030439168 (103034052095093 / 100000) (4121627392329 / 4000) := by
  exact
    packedTile32768 1030373632 1030439168 13 3196 32099 30 _ _ (2075317 / 100000) (51883 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1030439168 :
    ThetaLowerSegment 1030439168 1030504704 (4121627392329 / 4000) (103047178497021 / 100000) := by
  exact
    packedTile32768 1030439168 1030504704 13 3129 32100 30 _ _ (518831 / 25000) (2075327 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1030504704 :
    ThetaLowerSegment 1030504704 1030570240 (103047178497021 / 100000)
      (103053589191391 / 100000) := by
  exact
    packedTile32768 1030504704 1030570240 13 3089 32101 30 _ _ (207533 / 10000) (2075333 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1030570240 :
    ThetaLowerSegment 1030570240 1030635776 (103053589191391 / 100000) (824482572651 / 800) := by
  exact
    packedTile32768 1030570240 1030635776 13 3244 32102 30 _ _ (259417 / 12500) (2075339 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1030635776 :
    ThetaLowerSegment 1030635776 1030701312 (824482572651 / 800) (4122678507159 / 4000) := by
  exact
    packedTile32768 1030635776 1030701312 13 3200 32103 30 _ _ (2075343 / 100000) (1037673 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1030701312 :
    ThetaLowerSegment 1030701312 1030766848 (4122678507159 / 4000) (103073637001359 / 100000) := by
  exact
    packedTile32768 1030701312 1030766848 13 3216 32104 30 _ _ (2075349 / 100000) (259419 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1030766848 :
    ThetaLowerSegment 1030766848 1030832384 (103073637001359 / 100000)
      (25770023357691 / 25000) := by
  exact
    packedTile32768 1030766848 1030832384 13 3111 32105 30 _ _ (415071 / 20000) (1037679 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1030832384 :
    ThetaLowerSegment 1030832384 1030897920 (25770023357691 / 25000) (2577166185599 / 2500) := by
  exact
    packedTile32768 1030832384 1030897920 13 3158 32106 30 _ _ (1037681 / 50000) (415073 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1030897920 :
    ThetaLowerSegment 1030897920 1030963456 (2577166185599 / 2500) (12886652254881 / 12500) := by
  exact
    packedTile32768 1030897920 1030963456 13 3166 32107 30 _ _ (259421 / 12500) (2075371 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1030963456 :
    ThetaLowerSegment 1030963456 1031028992 (12886652254881 / 12500) (25774920188421 / 25000) := by
  exact
    packedTile32768 1030963456 1031028992 13 3114 32108 30 _ _ (1037687 / 50000) (2075377 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1031028992 :
    ThetaLowerSegment 1031028992 1031094528 (25774920188421 / 25000) (51553150609537 / 50000) := by
  exact
    packedTile32768 1031028992 1031094528 13 3190 32109 30 _ _ (2075381 / 100000) (259423 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1031094528 :
    ThetaLowerSegment 1031094528 1031160064 (51553150609537 / 50000) (51556408967127 / 50000) := by
  exact
    packedTile32768 1031094528 1031160064 13 3140 32110 30 _ _ (2075387 / 100000) (207539 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1031160064 :
    ThetaLowerSegment 1031160064 1031225600 (51556408967127 / 50000) (12889933696503 / 12500) := by
  exact
    packedTile32768 1031160064 1031225600 13 3205 32111 30 _ _ (1037697 / 50000) (2075397 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1031225600 :
    ThetaLowerSegment 1031225600 1031291136 (12889933696503 / 12500) (12890740508253 / 12500) := by
  exact
    packedTile32768 1031225600 1031291136 13 3110 32112 30 _ _ (10377 / 500) (2075403 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1031291136 :
    ThetaLowerSegment 1031291136 1031356672 (12890740508253 / 12500) (51566198628669 / 50000) := by
  exact
    packedTile32768 1031291136 1031356672 13 3119 32113 30 _ _ (1037703 / 50000) (2075409 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1031356672 :
    ThetaLowerSegment 1031356672 1031422208 (51566198628669 / 50000)
      (103138936883701 / 100000) := by
  exact
    packedTile32768 1031356672 1031422208 13 3151 32114 30 _ _ (2075413 / 100000) (259427 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1031422208 :
    ThetaLowerSegment 1031422208 1031487744 (103138936883701 / 100000)
      (25786368094533 / 25000) := by
  exact
    packedTile32768 1031422208 1031487744 13 3149 32115 30 _ _ (2075419 / 100000) (1037711 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1031487744 :
    ThetaLowerSegment 1031487744 1031553280 (25786368094533 / 25000)
      (103152103361007 / 100000) := by
  exact
    packedTile32768 1031487744 1031553280 13 3195 32116 30 _ _ (83017 / 4000) (518857 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1031553280 :
    ThetaLowerSegment 1031553280 1031618816 (103152103361007 / 100000)
      (103158703234767 / 100000) := by
  exact
    packedTile32768 1031553280 1031618816 13 3180 32117 30 _ _ (259429 / 12500) (415087 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1031618816 :
    ThetaLowerSegment 1031618816 1031684352 (103158703234767 / 100000)
      (20633029909039 / 20000) := by
  exact
    packedTile32768 1031618816 1031684352 13 3106 32118 30 _ _ (1037719 / 50000) (2075441 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1031684352 :
    ThetaLowerSegment 1031684352 1031749888 (20633029909039 / 20000) (20634333287871 / 20000) := by
  exact
    packedTile32768 1031684352 1031749888 13 3140 32119 30 _ _ (518861 / 25000) (2075447 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1031749888 :
    ThetaLowerSegment 1031749888 1031815424 (20634333287871 / 20000) (12897277848633 / 12500) := by
  exact
    packedTile32768 1031749888 1031815424 13 3159 32120 30 _ _ (2075451 / 100000) (1037727 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1031815424 :
    ThetaLowerSegment 1031815424 1031880960 (12897277848633 / 12500) (12898108031433 / 12500) := by
  exact
    packedTile32768 1031815424 1031880960 13 3200 32121 30 _ _ (2075457 / 100000) (103773 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1031880960 :
    ThetaLowerSegment 1031880960 1031946496 (12898108031433 / 12500) (3224732997561 / 3125) := by
  exact
    packedTile32768 1031880960 1031946496 13 3176 32122 30 _ _ (2075463 / 100000) (1037733 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1031946496 :
    ThetaLowerSegment 1031946496 1032012032 (3224732997561 / 3125) (51599047675241 / 50000) := by
  exact
    packedTile32768 1031946496 1032012032 13 3199 32123 30 _ _ (207547 / 10000) (2075473 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1032012032 :
    ThetaLowerSegment 1032012032 1032077568 (51599047675241 / 50000) (51602279191373 / 50000) := by
  exact
    packedTile32768 1032012032 1032077568 13 3114 32124 30 _ _ (518869 / 25000) (2075479 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1032077568 :
    ThetaLowerSegment 1032077568 1032143104 (51602279191373 / 50000) (10321107954719 / 10000) := by
  exact
    packedTile32768 1032077568 1032143104 13 3142 32125 30 _ _ (1037741 / 50000) (415097 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1032143104 :
    ThetaLowerSegment 1032143104 1032208640 (10321107954719 / 10000) (1290219697847 / 1250) := by
  exact
    packedTile32768 1032143104 1032208640 13 3130 32126 30 _ _ (2075489 / 100000) (518873 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1032208640 :
    ThetaLowerSegment 1032208640 1032274176 (1290219697847 / 1250) (2580605850393 / 2500) := by
  exact
    packedTile32768 1032208640 1032274176 13 3208 32128 30 _ _ (415099 / 20000) (1037749 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1032274176 :
    ThetaLowerSegment 1032274176 1032339712 (2580605850393 / 2500) (51615343375719 / 50000) := by
  exact
    packedTile32768 1032274176 1032339712 13 3109 32129 30 _ _ (1037751 / 50000) (415101 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1032339712 :
    ThetaLowerSegment 1032339712 1032405248 (51615343375719 / 50000) (10323724328121 / 10000) := by
  exact
    packedTile32768 1032339712 1032405248 13 3159 32130 30 _ _ (518877 / 25000) (2075511 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1032405248 :
    ThetaLowerSegment 1032405248 1032470784 (10323724328121 / 10000) (1032438537933 / 1000) := by
  exact
    packedTile32768 1032405248 1032470784 13 3185 32131 30 _ _ (1037757 / 50000) (2075517 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1032470784 :
    ThetaLowerSegment 1032470784 1032536320 (1032438537933 / 1000) (103250518291231 / 100000) := by
  exact
    packedTile32768 1032470784 1032536320 13 3211 32132 30 _ _ (2075521 / 100000) (518881 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1032536320 :
    ThetaLowerSegment 1032536320 1032601856 (103250518291231 / 100000) (645356302901 / 625) := by
  exact
    packedTile32768 1032536320 1032601856 13 3127 32133 30 _ _ (2075527 / 100000) (207553 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1032601856 :
    ThetaLowerSegment 1032601856 1032667392 (645356302901 / 625) (12907941742489 / 12500) := by
  exact
    packedTile32768 1032601856 1032667392 13 3144 32134 30 _ _ (2075533 / 100000) (129721 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1032667392 :
    ThetaLowerSegment 1032667392 1032732928 (12907941742489 / 12500) (12908766769639 / 12500) := by
  exact
    packedTile32768 1032667392 1032732928 13 3180 32135 30 _ _ (103777 / 5000) (2075543 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1032732928 :
    ThetaLowerSegment 1032732928 1032798464 (12908766769639 / 12500) (51638345403463 / 50000) := by
  exact
    packedTile32768 1032732928 1032798464 13 3159 32136 30 _ _ (1037773 / 50000) (2075549 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1032798464 :
    ThetaLowerSegment 1032798464 1032864000 (51638345403463 / 50000) (51641588453463 / 50000) := by
  exact
    packedTile32768 1032798464 1032864000 13 3125 32137 30 _ _ (64861 / 3125) (415111 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1032864000 :
    ThetaLowerSegment 1032864000 1032929536 (51641588453463 / 50000) (20657922643077 / 20000) := by
  exact
    packedTile32768 1032864000 1032929536 13 3101 32138 30 _ _ (2075559 / 100000) (1037781 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1032929536 :
    ThetaLowerSegment 1032929536 1032995072 (20657922643077 / 20000) (20659231079253 / 20000) := by
  exact
    packedTile32768 1032929536 1032995072 13 3152 32139 30 _ _ (415113 / 20000) (129723 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1032995072 :
    ThetaLowerSegment 1032995072 1033060608 (20659231079253 / 20000) (12912826043313 / 12500) := by
  exact
    packedTile32768 1032995072 1033060608 13 3109 32140 30 _ _ (2075571 / 100000) (1037787 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1033060608 :
    ThetaLowerSegment 1033060608 1033126144 (12912826043313 / 12500) (51654568019657 / 50000) := by
  exact
    packedTile32768 1033060608 1033126144 13 3145 32141 30 _ _ (1037789 / 50000) (2075581 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1033126144 :
    ThetaLowerSegment 1033126144 1033191680 (51654568019657 / 50000) (51657838102249 / 50000) := by
  exact
    packedTile32768 1033126144 1033191680 13 3151 32142 30 _ _ (64862 / 3125) (2075587 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1033191680 :
    ThetaLowerSegment 1033191680 1033257216 (51657838102249 / 50000) (25830539568017 / 25000) := by
  exact
    packedTile32768 1033191680 1033257216 13 3123 32143 30 _ _ (207559 / 10000) (2075593 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1033257216 :
    ThetaLowerSegment 1033257216 1033322752 (25830539568017 / 25000) (516643544281 / 500) := by
  exact
    packedTile32768 1033257216 1033322752 13 3156 32144 30 _ _ (2075597 / 100000) (5189 / 250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1033322752 :
    ThetaLowerSegment 1033322752 1033339136 (516643544281 / 500) (25832577805429 / 25000) := by
  exact
    packedTile32768 1033322752 1033339136 11 772 32145 30 _ _ (2075603 / 100000) (1037803 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1033339136 :
    ThetaLowerSegment 1033339136 1033341184 (25832577805429 / 25000)
      (103330508404191 / 100000) := by
  exact
    packedTile32768 1033339136 1033341184 8 95 32145 30 _ _ (415121 / 20000) (259451 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_1001341184_1033341184 :
    ThetaLowerSegment 1001341184 1033341184 (100130293146287 / 100000)
      (103330508404191 / 100000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1001341184 cell1001406720)
                    (ThetaLowerSegment.join cell1001472256 cell1001537792))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1001603328 cell1001668864)
                    (ThetaLowerSegment.join cell1001734400 cell1001799936)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1001865472 cell1001931008)
                    (ThetaLowerSegment.join cell1001996544 cell1002062080))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1002127616 cell1002193152)
                    (ThetaLowerSegment.join cell1002258688 cell1002324224))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1002389760 cell1002455296)
                    (ThetaLowerSegment.join cell1002520832 cell1002586368))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1002651904 cell1002717440)
                    (ThetaLowerSegment.join cell1002782976 cell1002848512)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1002914048 cell1002979584)
                    (ThetaLowerSegment.join cell1003045120 cell1003110656))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1003176192 cell1003241728)
                    (ThetaLowerSegment.join cell1003307264 cell1003372800)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1003438336 cell1003503872)
                    (ThetaLowerSegment.join cell1003569408 cell1003634944))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1003700480 cell1003766016)
                    (ThetaLowerSegment.join cell1003831552 cell1003897088)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1003962624 cell1004028160)
                    (ThetaLowerSegment.join cell1004093696 cell1004159232))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1004224768 cell1004290304)
                    (ThetaLowerSegment.join cell1004355840 cell1004421376))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1004486912 cell1004552448)
                    (ThetaLowerSegment.join cell1004617984 cell1004683520))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1004749056 cell1004814592)
                    (ThetaLowerSegment.join cell1004880128 cell1004945664)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1005011200 cell1005076736)
                    (ThetaLowerSegment.join cell1005142272 cell1005207808))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1005273344 cell1005338880)
                    (ThetaLowerSegment.join cell1005404416 cell1005469952))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1005535488 cell1005601024)
                    (ThetaLowerSegment.join cell1005666560 cell1005732096))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1005797632 cell1005863168)
                    (ThetaLowerSegment.join cell1005928704 cell1005994240)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1006059776 cell1006125312)
                    (ThetaLowerSegment.join cell1006190848 cell1006256384))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1006321920 cell1006387456)
                    (ThetaLowerSegment.join cell1006452992 cell1006518528))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1006584064 cell1006649600)
                    (ThetaLowerSegment.join cell1006715136 cell1006780672))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1006846208 cell1006911744)
                    (ThetaLowerSegment.join cell1006977280 cell1007042816)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1007108352 cell1007173888)
                    (ThetaLowerSegment.join cell1007239424 cell1007304960))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1007370496 cell1007436032)
                    (ThetaLowerSegment.join cell1007501568 cell1007567104)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1007632640 cell1007698176)
                    (ThetaLowerSegment.join cell1007763712 cell1007829248))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1007894784 cell1007960320)
                    (ThetaLowerSegment.join cell1008025856 cell1008091392)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1008156928 cell1008222464)
                    (ThetaLowerSegment.join cell1008288000 cell1008353536))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1008419072 cell1008484608)
                    (ThetaLowerSegment.join cell1008550144 cell1008615680))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1008681216 cell1008746752)
                    (ThetaLowerSegment.join cell1008812288 cell1008877824))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1008943360 cell1009008896)
                    (ThetaLowerSegment.join cell1009074432 cell1009139968)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1009205504 cell1009271040)
                    (ThetaLowerSegment.join cell1009336576 cell1009402112))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1009467648 cell1009533184)
                    (ThetaLowerSegment.join cell1009598720 cell1009664256)))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1009729792 cell1009795328)
                    (ThetaLowerSegment.join cell1009860864 cell1009926400))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1009991936 cell1010057472)
                    (ThetaLowerSegment.join cell1010123008 cell1010188544)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1010254080 cell1010319616)
                    (ThetaLowerSegment.join cell1010385152 cell1010450688))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1010516224 cell1010581760)
                    (ThetaLowerSegment.join cell1010647296 cell1010712832))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1010778368 cell1010843904)
                    (ThetaLowerSegment.join cell1010909440 cell1010974976))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1011040512 cell1011106048)
                    (ThetaLowerSegment.join cell1011171584 cell1011237120)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1011302656 cell1011368192)
                    (ThetaLowerSegment.join cell1011433728 cell1011499264))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1011564800 cell1011630336)
                    (ThetaLowerSegment.join cell1011695872 cell1011761408)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1011826944 cell1011892480)
                    (ThetaLowerSegment.join cell1011958016 cell1012023552))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1012089088 cell1012154624)
                    (ThetaLowerSegment.join cell1012220160 cell1012285696)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1012351232 cell1012416768)
                    (ThetaLowerSegment.join cell1012482304 cell1012547840))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1012613376 cell1012678912)
                    (ThetaLowerSegment.join cell1012744448 cell1012809984))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1012875520 cell1012941056)
                    (ThetaLowerSegment.join cell1013006592 cell1013072128))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1013137664 cell1013203200)
                    (ThetaLowerSegment.join cell1013268736 cell1013334272)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1013399808 cell1013465344)
                    (ThetaLowerSegment.join cell1013530880 cell1013596416))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1013661952 cell1013727488)
                    (ThetaLowerSegment.join cell1013793024 cell1013858560))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1013924096 cell1013989632)
                    (ThetaLowerSegment.join cell1014055168 cell1014120704))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1014186240 cell1014251776)
                    (ThetaLowerSegment.join cell1014317312 cell1014382848)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1014448384 cell1014513920)
                    (ThetaLowerSegment.join cell1014579456 cell1014644992))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1014710528 cell1014776064)
                    (ThetaLowerSegment.join cell1014841600 cell1014907136))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1014972672 cell1015038208)
                    (ThetaLowerSegment.join cell1015103744 cell1015169280))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1015234816 cell1015300352)
                    (ThetaLowerSegment.join cell1015365888 cell1015431424)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1015496960 cell1015562496)
                    (ThetaLowerSegment.join cell1015628032 cell1015693568))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1015759104 cell1015824640)
                    (ThetaLowerSegment.join cell1015890176 cell1015955712)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1016021248 cell1016086784)
                    (ThetaLowerSegment.join cell1016152320 cell1016217856))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1016283392 cell1016348928)
                    (ThetaLowerSegment.join cell1016414464 cell1016480000)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1016545536 cell1016611072)
                    (ThetaLowerSegment.join cell1016676608 cell1016742144))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1016807680 cell1016873216)
                    (ThetaLowerSegment.join cell1016938752 cell1017004288))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1017069824 cell1017135360)
                    (ThetaLowerSegment.join cell1017200896 cell1017266432))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1017331968 cell1017397504)
                    (ThetaLowerSegment.join cell1017463040 cell1017528576)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1017594112 cell1017659648)
                    (ThetaLowerSegment.join cell1017725184 cell1017790720))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1017856256 cell1017921792)
                    (ThetaLowerSegment.join cell1017987328 cell1018052864))))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1018118400 cell1018183936)
                    (ThetaLowerSegment.join cell1018249472 cell1018315008))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1018380544 cell1018446080)
                    (ThetaLowerSegment.join cell1018511616 cell1018577152)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1018642688 cell1018708224)
                    (ThetaLowerSegment.join cell1018773760 cell1018839296))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1018904832 cell1018970368)
                    (ThetaLowerSegment.join cell1019035904 cell1019101440))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1019166976 cell1019232512)
                    (ThetaLowerSegment.join cell1019298048 cell1019363584))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1019429120 cell1019494656)
                    (ThetaLowerSegment.join cell1019560192 cell1019625728)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1019691264 cell1019756800)
                    (ThetaLowerSegment.join cell1019822336 cell1019887872))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1019953408 cell1020018944)
                    (ThetaLowerSegment.join cell1020084480 cell1020150016)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1020215552 cell1020281088)
                    (ThetaLowerSegment.join cell1020346624 cell1020412160))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1020477696 cell1020543232)
                    (ThetaLowerSegment.join cell1020608768 cell1020674304)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1020739840 cell1020805376)
                    (ThetaLowerSegment.join cell1020870912 cell1020936448))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1021001984 cell1021067520)
                    (ThetaLowerSegment.join cell1021133056 cell1021198592))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1021264128 cell1021329664)
                    (ThetaLowerSegment.join cell1021395200 cell1021460736))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1021526272 cell1021591808)
                    (ThetaLowerSegment.join cell1021657344 cell1021722880)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1021788416 cell1021853952)
                    (ThetaLowerSegment.join cell1021919488 cell1021985024))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1022050560 cell1022116096)
                    (ThetaLowerSegment.join cell1022181632 cell1022247168))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1022312704 cell1022378240)
                    (ThetaLowerSegment.join cell1022443776 cell1022509312))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1022574848 cell1022640384)
                    (ThetaLowerSegment.join cell1022705920 cell1022771456)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1022836992 cell1022902528)
                    (ThetaLowerSegment.join cell1022968064 cell1023033600))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1023099136 cell1023164672)
                    (ThetaLowerSegment.join cell1023230208 cell1023295744))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1023361280 cell1023426816)
                    (ThetaLowerSegment.join cell1023492352 cell1023557888))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1023623424 cell1023688960)
                    (ThetaLowerSegment.join cell1023754496 cell1023820032)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1023885568 cell1023951104)
                    (ThetaLowerSegment.join cell1024016640 cell1024082176))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1024147712 cell1024213248)
                    (ThetaLowerSegment.join cell1024278784 cell1024344320)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1024409856 cell1024475392)
                    (ThetaLowerSegment.join cell1024540928 cell1024606464))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1024672000 cell1024737536)
                    (ThetaLowerSegment.join cell1024803072 cell1024868608)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1024934144 cell1024999680)
                    (ThetaLowerSegment.join cell1025065216 cell1025130752))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1025196288 cell1025261824)
                    (ThetaLowerSegment.join cell1025327360 cell1025392896))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1025458432 cell1025523968)
                    (ThetaLowerSegment.join cell1025589504 cell1025655040))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1025720576 cell1025786112)
                    (ThetaLowerSegment.join cell1025851648 cell1025917184)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1025982720 cell1026048256)
                    (ThetaLowerSegment.join cell1026113792 cell1026179328))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1026244864 cell1026310400)
                    (ThetaLowerSegment.join cell1026375936 cell1026441472)))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1026507008 cell1026572544)
                    (ThetaLowerSegment.join cell1026638080 cell1026703616))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1026769152 cell1026834688)
                    (ThetaLowerSegment.join cell1026900224 cell1026965760)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1027031296 cell1027096832)
                    (ThetaLowerSegment.join cell1027162368 cell1027227904))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1027293440 cell1027358976)
                    (ThetaLowerSegment.join cell1027424512 cell1027490048))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1027555584 cell1027621120)
                    (ThetaLowerSegment.join cell1027686656 cell1027752192))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1027817728 cell1027883264)
                    (ThetaLowerSegment.join cell1027948800 cell1028014336)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1028079872 cell1028145408)
                    (ThetaLowerSegment.join cell1028210944 cell1028276480))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1028342016 cell1028407552)
                    (ThetaLowerSegment.join cell1028473088 cell1028538624)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1028604160 cell1028669696)
                    (ThetaLowerSegment.join cell1028735232 cell1028800768))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1028866304 cell1028931840)
                    (ThetaLowerSegment.join cell1028997376 cell1029062912)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1029128448 cell1029193984)
                    (ThetaLowerSegment.join cell1029259520 cell1029325056))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1029390592 cell1029456128)
                    (ThetaLowerSegment.join cell1029521664 cell1029587200))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1029652736 cell1029718272)
                    (ThetaLowerSegment.join cell1029783808 cell1029849344))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1029914880 cell1029980416)
                    (ThetaLowerSegment.join cell1030045952 cell1030111488)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1030177024 cell1030242560)
                    (ThetaLowerSegment.join cell1030308096 cell1030373632))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1030439168 cell1030504704)
                    (ThetaLowerSegment.join cell1030570240 cell1030635776))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1030701312 cell1030766848)
                    (ThetaLowerSegment.join cell1030832384 cell1030897920))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1030963456 cell1031028992)
                    (ThetaLowerSegment.join cell1031094528 cell1031160064)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1031225600 cell1031291136)
                    (ThetaLowerSegment.join cell1031356672 cell1031422208))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1031487744 cell1031553280)
                    (ThetaLowerSegment.join cell1031618816 cell1031684352))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1031749888 cell1031815424)
                    (ThetaLowerSegment.join cell1031880960 cell1031946496))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1032012032 cell1032077568)
                    (ThetaLowerSegment.join cell1032143104 cell1032208640)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1032274176 cell1032339712)
                    (ThetaLowerSegment.join cell1032405248 cell1032470784))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1032536320 cell1032601856)
                    (ThetaLowerSegment.join cell1032667392 cell1032732928)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1032798464 cell1032864000)
                  (ThetaLowerSegment.join cell1032929536 cell1032995072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1033060608 cell1033126144)
                  (ThetaLowerSegment.join cell1033191680 cell1033257216)))
              (ThetaLowerSegment.join cell1033322752 cell1033339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
