/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis32768

/-! # Direct theta estimate up to 777341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell745341184 :
    ThetaLowerSegment 745341184 745406720 (465816840053 / 625) (37268647564117 / 50000) := by
  exact
    packedTile32768 745341184 745406720 13 3231 27300 29 _ _ (1021467 / 50000) (2042937 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell745406720 :
    ThetaLowerSegment 745406720 745472256 (37268647564117 / 50000) (74543932650041 / 100000) := by
  exact
    packedTile32768 745406720 745472256 13 3249 27302 29 _ _ (2042943 / 100000) (1021473 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell745472256 :
    ThetaLowerSegment 745472256 745537792 (74543932650041 / 100000) (18637615991097 / 25000) := by
  exact
    packedTile32768 745472256 745537792 13 3197 27303 29 _ _ (2042951 / 100000) (1021477 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell745537792 :
    ThetaLowerSegment 745537792 745603328 (18637615991097 / 25000) (18639235547637 / 25000) := by
  exact
    packedTile32768 745537792 745603328 13 3171 27304 29 _ _ (25537 / 1250) (2042963 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell745603328 :
    ThetaLowerSegment 745603328 745668864 (18639235547637 / 25000) (37281721458953 / 50000) := by
  exact
    packedTile32768 745603328 745668864 13 3182 27305 29 _ _ (2042969 / 100000) (510743 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell745668864 :
    ThetaLowerSegment 745668864 745734400 (37281721458953 / 50000) (9321254450989 / 12500) := by
  exact
    packedTile32768 745668864 745734400 13 3227 27306 29 _ _ (1021489 / 50000) (2042981 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell745734400 :
    ThetaLowerSegment 745734400 745799936 (9321254450989 / 12500) (74576648756831 / 100000) := by
  exact
    packedTile32768 745734400 745799936 13 3237 27308 29 _ _ (2042987 / 100000) (204299 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell745799936 :
    ThetaLowerSegment 745799936 745865472 (74576648756831 / 100000) (37291594191913 / 50000) := by
  exact
    packedTile32768 745799936 745865472 13 3201 27309 29 _ _ (408599 / 20000) (1021499 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell745865472 :
    ThetaLowerSegment 745865472 745931008 (37291594191913 / 50000) (37294851761791 / 50000) := by
  exact
    packedTile32768 745865472 745931008 13 3189 27310 29 _ _ (510751 / 25000) (2043007 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell745931008 :
    ThetaLowerSegment 745931008 745996544 (37294851761791 / 50000) (37298141012721 / 50000) := by
  exact
    packedTile32768 745931008 745996544 13 3220 27311 29 _ _ (2043013 / 100000) (255377 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell745996544 :
    ThetaLowerSegment 745996544 746062080 (37298141012721 / 50000) (18650679896941 / 25000) := by
  exact
    packedTile32768 745996544 746062080 13 3151 27312 29 _ _ (1021511 / 50000) (81721 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell746062080 :
    ThetaLowerSegment 746062080 746127616 (18650679896941 / 25000) (37304654179757 / 50000) := by
  exact
    packedTile32768 746062080 746127616 13 3225 27314 29 _ _ (204303 / 10000) (2043033 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell746127616 :
    ThetaLowerSegment 746127616 746193152 (37304654179757 / 50000) (74615872643821 / 100000) := by
  exact
    packedTile32768 746127616 746193152 13 3213 27315 29 _ _ (2043039 / 100000) (1021521 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell746193152 :
    ThetaLowerSegment 746193152 746258688 (74615872643821 / 100000) (74622522765061 / 100000) := by
  exact
    packedTile32768 746193152 746258688 13 3255 27316 29 _ _ (255381 / 12500) (2043051 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell746258688 :
    ThetaLowerSegment 746258688 746324224 (74622522765061 / 100000) (4664311559647 / 6250) := by
  exact
    packedTile32768 746258688 746324224 13 3163 27317 29 _ _ (2043057 / 100000) (102153 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell746324224 :
    ThetaLowerSegment 746324224 746389760 (4664311559647 / 6250) (37317717456857 / 50000) := by
  exact
    packedTile32768 746324224 746389760 13 3157 27318 29 _ _ (1021533 / 50000) (2043069 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell746389760 :
    ThetaLowerSegment 746389760 746455296 (37317717456857 / 50000) (933024633843 / 1250) := by
  exact
    packedTile32768 746389760 746455296 13 3199 27320 29 _ _ (1021537 / 50000) (2043077 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell746455296 :
    ThetaLowerSegment 746455296 746520832 (933024633843 / 1250) (9331065614713 / 12500) := by
  exact
    packedTile32768 746455296 746520832 13 3208 27321 29 _ _ (2043083 / 100000) (1021543 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell746520832 :
    ThetaLowerSegment 746520832 746586368 (9331065614713 / 12500) (1866376978921 / 2500) := by
  exact
    packedTile32768 746520832 746586368 13 3208 27322 29 _ _ (510773 / 25000) (408619 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell746586368 :
    ThetaLowerSegment 746586368 746651904 (1866376978921 / 2500) (18665398140707 / 25000) := by
  exact
    packedTile32768 746586368 746651904 13 3188 27323 29 _ _ (2043101 / 100000) (63847 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell746651904 :
    ThetaLowerSegment 746651904 746717440 (18665398140707 / 25000) (18667040800343 / 25000) := by
  exact
    packedTile32768 746651904 746717440 13 3216 27324 29 _ _ (2043109 / 100000) (255389 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell746717440 :
    ThetaLowerSegment 746717440 746782976 (18667040800343 / 25000) (37337312791803 / 50000) := by
  exact
    packedTile32768 746717440 746782976 13 3163 27326 29 _ _ (1021559 / 50000) (2043121 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell746782976 :
    ThetaLowerSegment 746782976 746848512 (37337312791803 / 50000) (74681141115609 / 100000) := by
  exact
    packedTile32768 746782976 746848512 13 3189 27327 29 _ _ (2043127 / 100000) (204313 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell746848512 :
    ThetaLowerSegment 746848512 746914048 (74681141115609 / 100000) (74687546346969 / 100000) := by
  exact
    packedTile32768 746848512 746914048 13 3135 27328 29 _ _ (63848 / 3125) (2043139 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell746914048 :
    ThetaLowerSegment 746914048 746979584 (74687546346969 / 100000) (37347067744797 / 50000) := by
  exact
    packedTile32768 746914048 746979584 13 3225 27329 29 _ _ (408629 / 20000) (510787 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell746979584 :
    ThetaLowerSegment 746979584 747045120 (37347067744797 / 50000) (74700712399101 / 100000) := by
  exact
    packedTile32768 746979584 747045120 13 3219 27330 29 _ _ (2043153 / 100000) (510789 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell747045120 :
    ThetaLowerSegment 747045120 747110656 (74700712399101 / 100000) (74707256646987 / 100000) := by
  exact
    packedTile32768 747045120 747110656 13 3203 27332 29 _ _ (1021581 / 50000) (408633 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell747110656 :
    ThetaLowerSegment 747110656 747176192 (74707256646987 / 100000) (74713766189793 / 100000) := by
  exact
    packedTile32768 747110656 747176192 13 3186 27333 29 _ _ (2043171 / 100000) (1021587 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell747176192 :
    ThetaLowerSegment 747176192 747241728 (74713766189793 / 100000) (74720269631733 / 100000) := by
  exact
    packedTile32768 747176192 747241728 13 3183 27334 29 _ _ (102159 / 5000) (2043183 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell747241728 :
    ThetaLowerSegment 747241728 747307264 (74720269631733 / 100000) (74726924295049 / 100000) := by
  exact
    packedTile32768 747241728 747307264 13 3257 27335 29 _ _ (510797 / 25000) (2043191 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell747307264 :
    ThetaLowerSegment 747307264 747372800 (74726924295049 / 100000) (37366691420383 / 50000) := by
  exact
    packedTile32768 747307264 747372800 13 3161 27336 29 _ _ (2043197 / 100000) (2554 / 125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell747372800 :
    ThetaLowerSegment 747372800 747438336 (37366691420383 / 50000) (37369968722807 / 50000) := by
  exact
    packedTile32768 747372800 747438336 13 3208 27338 29 _ _ (1021603 / 50000) (2043209 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell747438336 :
    ThetaLowerSegment 747438336 747503872 (37369968722807 / 50000) (37373295076827 / 50000) := by
  exact
    packedTile32768 747438336 747503872 13 3256 27339 29 _ _ (408643 / 20000) (1021609 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell747503872 :
    ThetaLowerSegment 747503872 747569408 (37373295076827 / 50000) (37376590797139 / 50000) := by
  exact
    packedTile32768 747503872 747569408 13 3226 27340 29 _ _ (255403 / 12500) (2043227 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell747569408 :
    ThetaLowerSegment 747569408 747634944 (37376590797139 / 50000) (7475969133143 / 10000) := by
  exact
    packedTile32768 747569408 747634944 13 3186 27341 29 _ _ (63851 / 3125) (408647 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell747634944 :
    ThetaLowerSegment 747634944 747700480 (7475969133143 / 10000) (9345779223639 / 12500) := by
  exact
    packedTile32768 747634944 747700480 13 3202 27342 29 _ _ (2043241 / 100000) (510811 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell747700480 :
    ThetaLowerSegment 747700480 747766016 (9345779223639 / 12500) (18693226760903 / 25000) := by
  exact
    packedTile32768 747700480 747766016 13 3266 27344 29 _ _ (8173 / 400) (2043253 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell747766016 :
    ThetaLowerSegment 747766016 747831552 (18693226760903 / 25000) (2336856393976 / 3125) := by
  exact
    packedTile32768 747766016 747831552 13 3180 27345 29 _ _ (2043259 / 100000) (1021631 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell747831552 :
    ThetaLowerSegment 747831552 747897088 (2336856393976 / 3125) (14957196376741 / 20000) := by
  exact
    packedTile32768 747831552 747897088 13 3219 27346 29 _ _ (2043267 / 100000) (204327 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell747897088 :
    ThetaLowerSegment 747897088 747962624 (14957196376741 / 20000) (74792573492081 / 100000) := by
  exact
    packedTile32768 747897088 747962624 13 3226 27347 29 _ _ (510819 / 25000) (2043279 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell747962624 :
    ThetaLowerSegment 747962624 748028160 (74792573492081 / 100000) (74799124263791 / 100000) := by
  exact
    packedTile32768 747962624 748028160 13 3206 27348 29 _ _ (408657 / 20000) (255411 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell748028160 :
    ThetaLowerSegment 748028160 748093696 (74799124263791 / 100000) (74805605592359 / 100000) := by
  exact
    packedTile32768 748028160 748093696 13 3172 27350 29 _ _ (1021647 / 50000) (2043297 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell748093696 :
    ThetaLowerSegment 748093696 748159232 (74805605592359 / 100000) (74812225890839 / 100000) := by
  exact
    packedTile32768 748093696 748159232 13 3240 27351 29 _ _ (1021651 / 50000) (408661 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell748159232 :
    ThetaLowerSegment 748159232 748224768 (74812225890839 / 100000) (14963771695669 / 20000) := by
  exact
    packedTile32768 748159232 748224768 13 3246 27352 29 _ _ (2043311 / 100000) (1021657 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell748224768 :
    ThetaLowerSegment 748224768 748290304 (14963771695669 / 20000) (14965090454397 / 20000) := by
  exact
    packedTile32768 748224768 748290304 13 3227 27353 29 _ _ (51083 / 2500) (2043323 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell748290304 :
    ThetaLowerSegment 748290304 748355840 (14965090454397 / 20000) (9353984306879 / 12500) := by
  exact
    packedTile32768 748290304 748355840 13 3143 27354 29 _ _ (2043329 / 100000) (510833 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell748355840 :
    ThetaLowerSegment 748355840 748421376 (9353984306879 / 12500) (3741925152013 / 5000) := by
  exact
    packedTile32768 748355840 748421376 13 3244 27356 29 _ _ (2043337 / 100000) (102167 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell748421376 :
    ThetaLowerSegment 748421376 748486912 (3741925152013 / 5000) (37422478985137 / 50000) := by
  exact
    packedTile32768 748421376 748486912 13 3159 27357 29 _ _ (1021673 / 50000) (2043349 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell748486912 :
    ThetaLowerSegment 748486912 748552448 (37422478985137 / 50000) (37425740179717 / 50000) := by
  exact
    packedTile32768 748486912 748552448 13 3192 27358 29 _ _ (408671 / 20000) (1021679 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell748552448 :
    ThetaLowerSegment 748552448 748617984 (37425740179717 / 50000) (37428965629791 / 50000) := by
  exact
    packedTile32768 748552448 748617984 13 3157 27359 29 _ _ (510841 / 25000) (2043367 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell748617984 :
    ThetaLowerSegment 748617984 748683520 (37428965629791 / 50000) (7486441692231 / 10000) := by
  exact
    packedTile32768 748617984 748683520 13 3174 27360 29 _ _ (510843 / 25000) (16347 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell748683520 :
    ThetaLowerSegment 748683520 748749056 (7486441692231 / 10000) (74870957784891 / 100000) := by
  exact
    packedTile32768 748683520 748749056 13 3201 27362 29 _ _ (2043381 / 100000) (255423 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell748749056 :
    ThetaLowerSegment 748749056 748814592 (74870957784891 / 100000) (74877488459331 / 100000) := by
  exact
    packedTile32768 748749056 748814592 13 3196 27363 29 _ _ (204339 / 10000) (2043393 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell748814592 :
    ThetaLowerSegment 748814592 748880128 (74877488459331 / 100000) (37441961561391 / 50000) := by
  exact
    packedTile32768 748814592 748880128 13 3149 27364 29 _ _ (2043399 / 100000) (1021701 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell748880128 :
    ThetaLowerSegment 748880128 748945664 (37441961561391 / 50000) (74890435460891 / 100000) := by
  exact
    packedTile32768 748880128 748945664 13 3187 27365 29 _ _ (2043407 / 100000) (204341 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell748945664 :
    ThetaLowerSegment 748945664 749011200 (74890435460891 / 100000) (74897031607739 / 100000) := by
  exact
    packedTile32768 748945664 749011200 13 3228 27366 29 _ _ (255427 / 12500) (2043419 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell749011200 :
    ThetaLowerSegment 749011200 749076736 (74897031607739 / 100000) (9362949641533 / 12500) := by
  exact
    packedTile32768 749011200 749076736 13 3213 27368 29 _ _ (81737 / 4000) (510857 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell749076736 :
    ThetaLowerSegment 749076736 749142272 (9362949641533 / 12500) (18727539138851 / 25000) := by
  exact
    packedTile32768 749076736 749142272 13 3210 27369 29 _ _ (1021717 / 50000) (2043437 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell749142272 :
    ThetaLowerSegment 749142272 749207808 (18727539138851 / 25000) (7491664039687 / 10000) := by
  exact
    packedTile32768 749142272 749207808 13 3173 27370 29 _ _ (1021721 / 50000) (408689 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell749207808 :
    ThetaLowerSegment 749207808 749273344 (7491664039687 / 10000) (74923275482267 / 100000) := by
  exact
    packedTile32768 749207808 749273344 13 3247 27371 29 _ _ (2043451 / 100000) (1021727 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell749273344 :
    ThetaLowerSegment 749273344 749338880 (74923275482267 / 100000) (74929873814607 / 100000) := by
  exact
    packedTile32768 749273344 749338880 13 3229 27372 29 _ _ (102173 / 5000) (2043463 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell749338880 :
    ThetaLowerSegment 749338880 749404416 (74929873814607 / 100000) (37468221783721 / 50000) := by
  exact
    packedTile32768 749338880 749404416 13 3215 27374 29 _ _ (2043469 / 100000) (127717 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell749404416 :
    ThetaLowerSegment 749404416 749469952 (37468221783721 / 50000) (7494282738959 / 10000) := by
  exact
    packedTile32768 749404416 749469952 13 3124 27375 29 _ _ (2043477 / 100000) (51087 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell749469952 :
    ThetaLowerSegment 749469952 749535488 (7494282738959 / 10000) (9368676693121 / 12500) := by
  exact
    packedTile32768 749469952 749535488 13 3223 27376 29 _ _ (1021743 / 50000) (2043489 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell749535488 :
    ThetaLowerSegment 749535488 749601024 (9368676693121 / 12500) (74955967033433 / 100000) := by
  exact
    packedTile32768 749535488 749601024 13 3207 27377 29 _ _ (408699 / 20000) (1021749 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell749601024 :
    ThetaLowerSegment 749601024 749666560 (74955967033433 / 100000) (74962590029897 / 100000) := by
  exact
    packedTile32768 749601024 749666560 13 3241 27378 29 _ _ (127719 / 6250) (2043507 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell749666560 :
    ThetaLowerSegment 749666560 749732096 (74962590029897 / 100000) (74969215095801 / 100000) := by
  exact
    packedTile32768 749666560 749732096 13 3242 27380 29 _ _ (255439 / 12500) (408703 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell749732096 :
    ThetaLowerSegment 749732096 749797632 (74969215095801 / 100000) (37487870029177 / 50000) := by
  exact
    packedTile32768 749732096 749797632 13 3193 27381 29 _ _ (2043521 / 100000) (510881 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell749797632 :
    ThetaLowerSegment 749797632 749863168 (37487870029177 / 50000) (37491143764237 / 50000) := by
  exact
    packedTile32768 749797632 749863168 13 3204 27382 29 _ _ (204353 / 10000) (2043533 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell749863168 :
    ThetaLowerSegment 749863168 749928704 (37491143764237 / 50000) (74988914725451 / 100000) := by
  exact
    packedTile32768 749863168 749928704 13 3243 27383 29 _ _ (2043539 / 100000) (1021771 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell749928704 :
    ThetaLowerSegment 749928704 749994240 (74988914725451 / 100000) (37497736233887 / 50000) := by
  exact
    packedTile32768 749928704 749994240 13 3209 27384 29 _ _ (2043547 / 100000) (40871 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell749994240 :
    ThetaLowerSegment 749994240 750059776 (37497736233887 / 50000) (37500990596817 / 50000) := by
  exact
    packedTile32768 749994240 750059776 13 3185 27386 29 _ _ (510889 / 25000) (2043559 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell750059776 :
    ThetaLowerSegment 750059776 750125312 (37500990596817 / 50000) (18752127085061 / 25000) := by
  exact
    packedTile32768 750059776 750125312 13 3194 27387 29 _ _ (408713 / 20000) (127723 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell750125312 :
    ThetaLowerSegment 750125312 750190848 (18752127085061 / 25000) (1875374866103 / 2500) := by
  exact
    packedTile32768 750125312 750190848 13 3174 27388 29 _ _ (1021787 / 50000) (2043577 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell750190848 :
    ThetaLowerSegment 750190848 750256384 (1875374866103 / 2500) (37510766031469 / 50000) := by
  exact
    packedTile32768 750190848 750256384 13 3199 27389 29 _ _ (1021791 / 50000) (408717 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell750256384 :
    ThetaLowerSegment 750256384 750321920 (37510766031469 / 50000) (9378501280801 / 12500) := by
  exact
    packedTile32768 750256384 750321920 13 3170 27390 29 _ _ (2043591 / 100000) (1021797 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell750321920 :
    ThetaLowerSegment 750321920 750387456 (9378501280801 / 12500) (9379330471501 / 12500) := by
  exact
    packedTile32768 750321920 750387456 13 3246 27392 29 _ _ (5109 / 250) (2043603 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell750387456 :
    ThetaLowerSegment 750387456 750452992 (9379330471501 / 12500) (37520593704013 / 50000) := by
  exact
    packedTile32768 750387456 750452992 13 3202 27393 29 _ _ (2043609 / 100000) (510903 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell750452992 :
    ThetaLowerSegment 750452992 750518528 (37520593704013 / 50000) (3752390640717 / 5000) := by
  exact
    packedTile32768 750452992 750518528 13 3242 27394 29 _ _ (2043617 / 100000) (102181 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell750518528 :
    ThetaLowerSegment 750518528 750584064 (3752390640717 / 5000) (37527195623217 / 50000) := by
  exact
    packedTile32768 750518528 750584064 13 3219 27395 29 _ _ (1021813 / 50000) (2043629 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell750584064 :
    ThetaLowerSegment 750584064 750649600 (37527195623217 / 50000) (9382592347093 / 12500) := by
  exact
    packedTile32768 750584064 750649600 13 3106 27396 29 _ _ (408727 / 20000) (1021819 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell750649600 :
    ThetaLowerSegment 750649600 750715136 (9382592347093 / 12500) (18766854350517 / 25000) := by
  exact
    packedTile32768 750649600 750715136 13 3268 27397 29 _ _ (2043643 / 100000) (1021823 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell750715136 :
    ThetaLowerSegment 750715136 750780672 (18766854350517 / 25000) (18768509708637 / 25000) := by
  exact
    packedTile32768 750715136 750780672 13 3240 27399 29 _ _ (510913 / 25000) (408731 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell750780672 :
    ThetaLowerSegment 750780672 750846208 (18768509708637 / 25000) (37540303580501 / 50000) := by
  exact
    packedTile32768 750780672 750846208 13 3214 27400 29 _ _ (2043661 / 100000) (127729 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell750846208 :
    ThetaLowerSegment 750846208 750911744 (37540303580501 / 50000) (37543522360751 / 50000) := by
  exact
    packedTile32768 750846208 750911744 13 3150 27401 29 _ _ (204367 / 10000) (2043673 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell750911744 :
    ThetaLowerSegment 750911744 750977280 (37543522360751 / 50000) (9386688609377 / 12500) := by
  exact
    packedTile32768 750911744 750977280 13 3163 27402 29 _ _ (1021839 / 50000) (2043681 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell750977280 :
    ThetaLowerSegment 750977280 751042816 (9386688609377 / 12500) (375500570357 / 500) := by
  exact
    packedTile32768 750977280 751042816 13 3232 27403 29 _ _ (2043687 / 100000) (204369 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell751042816 :
    ThetaLowerSegment 751042816 751108352 (375500570357 / 500) (9388341700343 / 12500) := by
  exact
    packedTile32768 751042816 751108352 13 3239 27405 29 _ _ (127731 / 6250) (2043699 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell751108352 :
    ThetaLowerSegment 751108352 751173888 (9388341700343 / 12500) (75113177404609 / 100000) := by
  exact
    packedTile32768 751108352 751173888 13 3153 27406 29 _ _ (408741 / 20000) (510927 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell751173888 :
    ThetaLowerSegment 751173888 751239424 (75113177404609 / 100000) (75119709111357 / 100000) := by
  exact
    packedTile32768 751173888 751239424 13 3196 27407 29 _ _ (2043713 / 100000) (510929 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell751239424 :
    ThetaLowerSegment 751239424 751304960 (75119709111357 / 100000) (75126381863687 / 100000) := by
  exact
    packedTile32768 751239424 751304960 13 3265 27408 29 _ _ (1021861 / 50000) (81749 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell751304960 :
    ThetaLowerSegment 751304960 751370496 (75126381863687 / 100000) (75132848228571 / 100000) := by
  exact
    packedTile32768 751304960 751370496 13 3164 27409 29 _ _ (2043731 / 100000) (1021867 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell751370496 :
    ThetaLowerSegment 751370496 751436032 (75132848228571 / 100000) (75139384105893 / 100000) := by
  exact
    packedTile32768 751370496 751436032 13 3198 27411 29 _ _ (2043739 / 100000) (1021871 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell751436032 :
    ThetaLowerSegment 751436032 751501568 (75139384105893 / 100000) (75145879137037 / 100000) := by
  exact
    packedTile32768 751436032 751501568 13 3178 27412 29 _ _ (510937 / 25000) (2043751 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell751501568 :
    ThetaLowerSegment 751501568 751567104 (75145879137037 / 100000) (75152390546839 / 100000) := by
  exact
    packedTile32768 751501568 751567104 13 3186 27413 29 _ _ (2043757 / 100000) (25547 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell751567104 :
    ThetaLowerSegment 751567104 751632640 (75152390546839 / 100000) (75158928554273 / 100000) := by
  exact
    packedTile32768 751567104 751632640 13 3199 27414 29 _ _ (1021883 / 50000) (2043769 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell751632640 :
    ThetaLowerSegment 751632640 751698176 (75158928554273 / 100000) (75165534031841 / 100000) := by
  exact
    packedTile32768 751632640 751698176 13 3232 27415 29 _ _ (1021887 / 50000) (2043777 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell751698176 :
    ThetaLowerSegment 751698176 751763712 (75165534031841 / 100000) (75172196764421 / 100000) := by
  exact
    packedTile32768 751698176 751763712 13 3260 27417 29 _ _ (2043783 / 100000) (1021893 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell751763712 :
    ThetaLowerSegment 751763712 751829248 (75172196764421 / 100000) (75178839088421 / 100000) := by
  exact
    packedTile32768 751763712 751829248 13 3250 27418 29 _ _ (127737 / 6250) (408759 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell751829248 :
    ThetaLowerSegment 751829248 751894784 (75178839088421 / 100000) (75185326109621 / 100000) := by
  exact
    packedTile32768 751829248 751894784 13 3174 27419 29 _ _ (10219 / 500) (2043803 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell751894784 :
    ThetaLowerSegment 751894784 751960320 (75185326109621 / 100000) (9398984053731 / 12500) := by
  exact
    packedTile32768 751894784 751960320 13 3203 27420 29 _ _ (2043809 / 100000) (510953 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell751960320 :
    ThetaLowerSegment 751960320 752025856 (9398984053731 / 12500) (18799614402861 / 25000) := by
  exact
    packedTile32768 751960320 752025856 13 3222 27421 29 _ _ (1021909 / 50000) (2043821 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell752025856 :
    ThetaLowerSegment 752025856 752091392 (18799614402861 / 25000) (75204950849823 / 100000) := by
  exact
    packedTile32768 752025856 752091392 13 3177 27423 29 _ _ (2043827 / 100000) (204383 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell752091392 :
    ThetaLowerSegment 752091392 752156928 (75204950849823 / 100000) (75211601488913 / 100000) := by
  exact
    packedTile32768 752091392 752156928 13 3254 27424 29 _ _ (408767 / 20000) (1021919 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell752156928 :
    ThetaLowerSegment 752156928 752222464 (75211601488913 / 100000) (3008725508081 / 4000) := by
  exact
    packedTile32768 752156928 752222464 13 3198 27425 29 _ _ (510961 / 25000) (2043847 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell752222464 :
    ThetaLowerSegment 752222464 752288000 (3008725508081 / 4000) (75224673943919 / 100000) := by
  exact
    packedTile32768 752222464 752288000 13 3198 27426 29 _ _ (2043853 / 100000) (127741 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell752288000 :
    ThetaLowerSegment 752288000 752353536 (75224673943919 / 100000) (75231353281667 / 100000) := by
  exact
    packedTile32768 752288000 752353536 13 3268 27427 29 _ _ (2043861 / 100000) (255483 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell752353536 :
    ThetaLowerSegment 752353536 752419072 (75231353281667 / 100000) (75238073526227 / 100000) := by
  exact
    packedTile32768 752353536 752419072 13 3288 27429 29 _ _ (204387 / 10000) (2043873 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell752419072 :
    ThetaLowerSegment 752419072 752484608 (75238073526227 / 100000) (75244544447141 / 100000) := by
  exact
    packedTile32768 752419072 752484608 13 3166 27430 29 _ _ (2043879 / 100000) (1021941 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell752484608 :
    ThetaLowerSegment 752484608 752550144 (75244544447141 / 100000) (75251066493749 / 100000) := by
  exact
    packedTile32768 752484608 752550144 13 3191 27431 29 _ _ (127743 / 6250) (2043891 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell752550144 :
    ThetaLowerSegment 752550144 752615680 (75251066493749 / 100000) (75257539512381 / 100000) := by
  exact
    packedTile32768 752550144 752615680 13 3167 27432 29 _ _ (255487 / 12500) (2043899 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell752615680 :
    ThetaLowerSegment 752615680 752681216 (75257539512381 / 100000) (37632090079863 / 50000) := by
  exact
    packedTile32768 752615680 752681216 13 3249 27433 29 _ _ (408781 / 20000) (510977 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell752681216 :
    ThetaLowerSegment 752681216 752746752 (37632090079863 / 50000) (7527061031317 / 10000) := by
  exact
    packedTile32768 752681216 752746752 13 3146 27435 29 _ _ (1021957 / 50000) (2043917 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell752746752 :
    ThetaLowerSegment 752746752 752812288 (7527061031317 / 10000) (9409658931871 / 12500) := by
  exact
    packedTile32768 752746752 752812288 13 3259 27436 29 _ _ (1021961 / 50000) (81757 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell752812288 :
    ThetaLowerSegment 752812288 752877824 (9409658931871 / 12500) (75283834517409 / 100000) := by
  exact
    packedTile32768 752812288 752877824 13 3211 27437 29 _ _ (2043931 / 100000) (1021967 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell752877824 :
    ThetaLowerSegment 752877824 752943360 (75283834517409 / 100000) (75290285192049 / 100000) := by
  exact
    packedTile32768 752877824 752943360 13 3156 27438 29 _ _ (102197 / 5000) (2043943 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell752943360 :
    ThetaLowerSegment 752943360 753008896 (75290285192049 / 100000) (75296764510379 / 100000) := by
  exact
    packedTile32768 752943360 753008896 13 3170 27439 29 _ _ (2043949 / 100000) (127747 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell753008896 :
    ThetaLowerSegment 753008896 753074432 (75296764510379 / 100000) (75303268381553 / 100000) := by
  exact
    packedTile32768 753008896 753074432 13 3182 27441 29 _ _ (2043957 / 100000) (51099 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell753074432 :
    ThetaLowerSegment 753074432 753139968 (75303268381553 / 100000) (75309811116719 / 100000) := by
  exact
    packedTile32768 753074432 753139968 13 3201 27442 29 _ _ (1021983 / 50000) (2043969 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell753139968 :
    ThetaLowerSegment 753139968 753205504 (75309811116719 / 100000) (18829114019861 / 25000) := by
  exact
    packedTile32768 753139968 753205504 13 3251 27443 29 _ _ (81759 / 4000) (1021989 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell753205504 :
    ThetaLowerSegment 753205504 753271040 (18829114019861 / 25000) (37661496368539 / 50000) := by
  exact
    packedTile32768 753205504 753271040 13 3198 27444 29 _ _ (2043983 / 100000) (1021993 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell753271040 :
    ThetaLowerSegment 753271040 753336576 (37661496368539 / 50000) (37664750403803 / 50000) := by
  exact
    packedTile32768 753271040 753336576 13 3184 27445 29 _ _ (255499 / 12500) (408799 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell753336576 :
    ThetaLowerSegment 753336576 753402112 (37664750403803 / 50000) (1883402777671 / 2500) := by
  exact
    packedTile32768 753336576 753402112 13 3234 27446 29 _ _ (2044001 / 100000) (511001 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell753402112 :
    ThetaLowerSegment 753402112 753467648 (1883402777671 / 2500) (15068532431137 / 20000) := by
  exact
    packedTile32768 753402112 753467648 13 3205 27448 29 _ _ (2044009 / 100000) (511003 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell753467648 :
    ThetaLowerSegment 753467648 753533184 (15068532431137 / 20000) (75349156000871 / 100000) := by
  exact
    packedTile32768 753467648 753533184 13 3177 27449 29 _ _ (1022009 / 50000) (2044021 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell753533184 :
    ThetaLowerSegment 753533184 753598720 (75349156000871 / 100000) (9419450613257 / 12500) := by
  exact
    packedTile32768 753533184 753598720 13 3155 27450 29 _ _ (2044027 / 100000) (204403 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell753598720 :
    ThetaLowerSegment 753598720 753664256 (9419450613257 / 12500) (942026669463 / 1250) := by
  exact
    packedTile32768 753598720 753664256 13 3194 27451 29 _ _ (511009 / 25000) (2044039 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell753664256 :
    ThetaLowerSegment 753664256 753729792 (942026669463 / 1250) (18842146650987 / 25000) := by
  exact
    packedTile32768 753664256 753729792 13 3157 27452 29 _ _ (511011 / 25000) (2044047 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell753729792 :
    ThetaLowerSegment 753729792 753795328 (18842146650987 / 25000) (37687590359463 / 50000) := by
  exact
    packedTile32768 753729792 753795328 13 3226 27454 29 _ _ (2044053 / 100000) (255507 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell753795328 :
    ThetaLowerSegment 753795328 753860864 (37687590359463 / 50000) (7538166448359 / 10000) := by
  exact
    packedTile32768 753795328 753860864 13 3172 27455 29 _ _ (1022031 / 50000) (408813 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell753860864 :
    ThetaLowerSegment 753860864 753926400 (7538166448359 / 10000) (7538815644991 / 10000) := by
  exact
    packedTile32768 753860864 753926400 13 3176 27456 29 _ _ (204407 / 10000) (2044073 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell753926400 :
    ThetaLowerSegment 753926400 753991936 (7538815644991 / 10000) (75394670929683 / 100000) := by
  exact
    packedTile32768 753926400 753991936 13 3187 27457 29 _ _ (2044079 / 100000) (1022041 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell753991936 :
    ThetaLowerSegment 753991936 754057472 (75394670929683 / 100000) (75401216099459 / 100000) := by
  exact
    packedTile32768 753991936 754057472 13 3202 27458 29 _ _ (255511 / 12500) (2044091 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell754057472 :
    ThetaLowerSegment 754057472 754123008 (75401216099459 / 100000) (75407757206659 / 100000) := by
  exact
    packedTile32768 754057472 754123008 13 3200 27460 29 _ _ (63878 / 3125) (2044099 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell754123008 :
    ThetaLowerSegment 754123008 754188544 (75407757206659 / 100000) (75414355577599 / 100000) := by
  exact
    packedTile32768 754123008 754188544 13 3228 27461 29 _ _ (408821 / 20000) (511027 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell754188544 :
    ThetaLowerSegment 754188544 754254080 (75414355577599 / 100000) (75420866080689 / 100000) := by
  exact
    packedTile32768 754188544 754254080 13 3185 27462 29 _ _ (1022057 / 50000) (2044117 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell754254080 :
    ThetaLowerSegment 754254080 754319616 (75420866080689 / 100000) (75427405226967 / 100000) := by
  exact
    packedTile32768 754254080 754319616 13 3199 27463 29 _ _ (1022061 / 50000) (16353 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell754319616 :
    ThetaLowerSegment 754319616 754385152 (75427405226967 / 100000) (37716978333411 / 50000) := by
  exact
    packedTile32768 754319616 754385152 13 3205 27464 29 _ _ (2044131 / 100000) (1022067 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell754385152 :
    ThetaLowerSegment 754385152 754450688 (37716978333411 / 50000) (37720301082981 / 50000) := by
  exact
    packedTile32768 754385152 754450688 13 3251 27466 29 _ _ (102207 / 5000) (2044143 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell754450688 :
    ThetaLowerSegment 754450688 754516224 (37720301082981 / 50000) (75447071897547 / 100000) := by
  exact
    packedTile32768 754450688 754516224 13 3165 27467 29 _ _ (2044149 / 100000) (255519 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell754516224 :
    ThetaLowerSegment 754516224 754581760 (75447071897547 / 100000) (15090756981827 / 20000) := by
  exact
    packedTile32768 754516224 754581760 13 3284 27468 29 _ _ (2044157 / 100000) (12776 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell754581760 :
    ThetaLowerSegment 754581760 754647296 (15090756981827 / 20000) (75460211767039 / 100000) := by
  exact
    packedTile32768 754581760 754647296 13 3144 27469 29 _ _ (1022083 / 50000) (2044169 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell754647296 :
    ThetaLowerSegment 754647296 754712832 (75460211767039 / 100000) (37733451175907 / 50000) := by
  exact
    packedTile32768 754647296 754712832 13 3273 27470 29 _ _ (81767 / 4000) (1022089 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell754712832 :
    ThetaLowerSegment 754712832 754778368 (37733451175907 / 50000) (37736730045439 / 50000) := by
  exact
    packedTile32768 754712832 754778368 13 3208 27472 29 _ _ (2044183 / 100000) (1022093 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell754778368 :
    ThetaLowerSegment 754778368 754843904 (37736730045439 / 50000) (7547992178179 / 10000) := by
  exact
    packedTile32768 754778368 754843904 13 3161 27473 29 _ _ (63881 / 3125) (408839 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell754843904 :
    ThetaLowerSegment 754843904 754909440 (7547992178179 / 10000) (75486608363261 / 100000) := by
  exact
    packedTile32768 754843904 754909440 13 3271 27474 29 _ _ (2044201 / 100000) (511051 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell754909440 :
    ThetaLowerSegment 754909440 754974976 (75486608363261 / 100000) (9436638362959 / 12500) := by
  exact
    packedTile32768 754909440 754974976 13 3179 27475 29 _ _ (2044209 / 100000) (511053 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell754974976 :
    ThetaLowerSegment 754974976 755040512 (9436638362959 / 12500) (18874921299299 / 25000) := by
  exact
    packedTile32768 754974976 755040512 13 3218 27476 29 _ _ (1022109 / 50000) (2044221 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell755040512 :
    ThetaLowerSegment 755040512 755106048 (18874921299299 / 25000) (37753078609939 / 50000) := by
  exact
    packedTile32768 755040512 755106048 13 3166 27478 29 _ _ (2044227 / 100000) (204423 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell755106048 :
    ThetaLowerSegment 755106048 755171584 (37753078609939 / 50000) (37756365739819 / 50000) := by
  exact
    packedTile32768 755106048 755171584 13 3216 27479 29 _ _ (408847 / 20000) (1022119 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell755171584 :
    ThetaLowerSegment 755171584 755237120 (37756365739819 / 50000) (7551939162659 / 10000) := by
  exact
    packedTile32768 755171584 755237120 13 3258 27480 29 _ _ (511061 / 25000) (2044247 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell755237120 :
    ThetaLowerSegment 755237120 755302656 (7551939162659 / 10000) (3776307905201 / 5000) := by
  exact
    packedTile32768 755237120 755302656 13 3310 27481 29 _ _ (2044253 / 100000) (63883 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell755302656 :
    ThetaLowerSegment 755302656 755368192 (3776307905201 / 5000) (37766356002393 / 50000) := by
  exact
    packedTile32768 755302656 755368192 13 3206 27482 29 _ _ (2044261 / 100000) (255533 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell755368192 :
    ThetaLowerSegment 755368192 755433728 (37766356002393 / 50000) (37769626834393 / 50000) := by
  exact
    packedTile32768 755368192 755433728 13 3200 27483 29 _ _ (204427 / 10000) (2044273 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell755433728 :
    ThetaLowerSegment 755433728 755499264 (37769626834393 / 50000) (15109159481173 / 20000) := by
  exact
    packedTile32768 755433728 755499264 13 3201 27485 29 _ _ (2044279 / 100000) (1022141 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell755499264 :
    ThetaLowerSegment 755499264 755564800 (15109159481173 / 20000) (75552412718597 / 100000) := by
  exact
    packedTile32768 755499264 755564800 13 3236 27486 29 _ _ (2044287 / 100000) (204429 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell755564800 :
    ThetaLowerSegment 755564800 755630336 (75552412718597 / 100000) (75559097566517 / 100000) := by
  exact
    packedTile32768 755564800 755630336 13 3270 27487 29 _ _ (255537 / 12500) (2044299 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell755630336 :
    ThetaLowerSegment 755630336 755695872 (75559097566517 / 100000) (75565655696957 / 100000) := by
  exact
    packedTile32768 755630336 755695872 13 3208 27488 29 _ _ (408861 / 20000) (511077 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell755695872 :
    ThetaLowerSegment 755695872 755761408 (75565655696957 / 100000) (75572283359703 / 100000) := by
  exact
    packedTile32768 755695872 755761408 13 3242 27489 29 _ _ (2044313 / 100000) (511079 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell755761408 :
    ThetaLowerSegment 755761408 755826944 (75572283359703 / 100000) (75578853810611 / 100000) := by
  exact
    packedTile32768 755761408 755826944 13 3214 27491 29 _ _ (1022161 / 50000) (81773 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell755826944 :
    ThetaLowerSegment 755826944 755892480 (75578853810611 / 100000) (15117105301399 / 20000) := by
  exact
    packedTile32768 755826944 755892480 13 3264 27492 29 _ _ (2044331 / 100000) (1022167 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell755892480 :
    ThetaLowerSegment 755892480 755958016 (15117105301399 / 20000) (18898018631203 / 25000) := by
  exact
    packedTile32768 755892480 755958016 13 3203 27493 29 _ _ (2044339 / 100000) (1022171 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell755958016 :
    ThetaLowerSegment 755958016 756023552 (18898018631203 / 25000) (18899651043081 / 25000) := by
  exact
    packedTile32768 755958016 756023552 13 3194 27494 29 _ _ (511087 / 25000) (2044351 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell756023552 :
    ThetaLowerSegment 756023552 756089088 (18899651043081 / 25000) (75605168602651 / 100000) := by
  exact
    packedTile32768 756023552 756089088 13 3211 27495 29 _ _ (2044357 / 100000) (51109 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell756089088 :
    ThetaLowerSegment 756089088 756154624 (75605168602651 / 100000) (4725733060621 / 6250) := by
  exact
    packedTile32768 756089088 756154624 13 3209 27497 29 _ _ (408873 / 20000) (127773 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell756154624 :
    ThetaLowerSegment 756154624 756220160 (4725733060621 / 6250) (37809138549929 / 50000) := by
  exact
    packedTile32768 756154624 756220160 13 3203 27498 29 _ _ (1022187 / 50000) (2044377 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell756220160 :
    ThetaLowerSegment 756220160 756285696 (37809138549929 / 50000) (75624845702437 / 100000) := by
  exact
    packedTile32768 756220160 756285696 13 3213 27499 29 _ _ (2044383 / 100000) (1022193 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell756285696 :
    ThetaLowerSegment 756285696 756351232 (75624845702437 / 100000) (37815713298533 / 50000) := by
  exact
    packedTile32768 756285696 756351232 13 3219 27500 29 _ _ (2044391 / 100000) (1022197 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell756351232 :
    ThetaLowerSegment 756351232 756416768 (37815713298533 / 50000) (37818991493933 / 50000) := by
  exact
    packedTile32768 756351232 756416768 13 3207 27501 29 _ _ (5111 / 250) (2044403 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell756416768 :
    ThetaLowerSegment 756416768 756482304 (37818991493933 / 50000) (15128909517033 / 20000) := by
  exact
    packedTile32768 756416768 756482304 13 3211 27503 29 _ _ (2044409 / 100000) (511103 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell756482304 :
    ThetaLowerSegment 756482304 756547840 (15128909517033 / 20000) (37825480460647 / 50000) := by
  exact
    packedTile32768 756482304 756547840 13 3137 27504 29 _ _ (2044417 / 100000) (102221 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell756547840 :
    ThetaLowerSegment 756547840 756613376 (37825480460647 / 50000) (37828833319287 / 50000) := by
  exact
    packedTile32768 756547840 756613376 13 3280 27505 29 _ _ (1022213 / 50000) (2044429 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell756613376 :
    ThetaLowerSegment 756613376 756678912 (37828833319287 / 50000) (4729011774139 / 6250) := by
  exact
    packedTile32768 756613376 756678912 13 3190 27506 29 _ _ (408887 / 20000) (1022219 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell756678912 :
    ThetaLowerSegment 756678912 756744448 (4729011774139 / 6250) (37835355079697 / 50000) := by
  exact
    packedTile32768 756678912 756744448 13 3190 27507 29 _ _ (2044443 / 100000) (1022223 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell756744448 :
    ThetaLowerSegment 756744448 756809984 (37835355079697 / 50000) (37838602691699 / 50000) := by
  exact
    packedTile32768 756744448 756809984 13 3177 27508 29 _ _ (511113 / 25000) (408891 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell756809984 :
    ThetaLowerSegment 756809984 756875520 (37838602691699 / 50000) (75683778325513 / 100000) := by
  exact
    packedTile32768 756809984 756875520 13 3215 27510 29 _ _ (2044461 / 100000) (127779 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell756875520 :
    ThetaLowerSegment 756875520 756941056 (75683778325513 / 100000) (18922579645461 / 25000) := by
  exact
    packedTile32768 756875520 756941056 13 3199 27511 29 _ _ (2044469 / 100000) (255559 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell756941056 :
    ThetaLowerSegment 756941056 757006592 (18922579645461 / 25000) (18924213183383 / 25000) := by
  exact
    packedTile32768 756941056 757006592 13 3196 27512 29 _ _ (1022239 / 50000) (2044481 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell757006592 :
    ThetaLowerSegment 757006592 757072128 (18924213183383 / 25000) (18925865128879 / 25000) := by
  exact
    packedTile32768 757006592 757072128 13 3232 27513 29 _ _ (2044487 / 100000) (204449 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell757072128 :
    ThetaLowerSegment 757072128 757137664 (18925865128879 / 25000) (18927492546899 / 25000) := by
  exact
    packedTile32768 757072128 757137664 13 3184 27514 29 _ _ (408899 / 20000) (1022249 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell757137664 :
    ThetaLowerSegment 757137664 757203200 (18927492546899 / 25000) (18929116394201 / 25000) := by
  exact
    packedTile32768 757137664 757203200 13 3177 27516 29 _ _ (255563 / 12500) (2044507 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell757203200 :
    ThetaLowerSegment 757203200 757268736 (18929116394201 / 25000) (9465381113583 / 12500) := by
  exact
    packedTile32768 757203200 757268736 13 3220 27517 29 _ _ (2044513 / 100000) (511129 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell757268736 :
    ThetaLowerSegment 757268736 757334272 (9465381113583 / 12500) (18932371265193 / 25000) := by
  exact
    packedTile32768 757268736 757334272 13 3148 27518 29 _ _ (2044521 / 100000) (511131 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell757334272 :
    ThetaLowerSegment 757334272 757399808 (18932371265193 / 25000) (37868045468601 / 50000) := by
  exact
    packedTile32768 757334272 757399808 13 3231 27519 29 _ _ (204453 / 10000) (2044533 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell757399808 :
    ThetaLowerSegment 757399808 757465344 (37868045468601 / 50000) (37871357621781 / 50000) := by
  exact
    packedTile32768 757399808 757465344 13 3240 27520 29 _ _ (2044539 / 100000) (1022271 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell757465344 :
    ThetaLowerSegment 757465344 757530880 (37871357621781 / 50000) (18937329782593 / 25000) := by
  exact
    packedTile32768 757465344 757530880 13 3230 27522 29 _ _ (2044547 / 100000) (40891 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell757530880 :
    ThetaLowerSegment 757530880 757596416 (18937329782593 / 25000) (9469479391293 / 12500) := by
  exact
    packedTile32768 757530880 757596416 13 3187 27523 29 _ _ (511139 / 25000) (2044559 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell757596416 :
    ThetaLowerSegment 757596416 757661952 (9469479391293 / 12500) (37881186824607 / 50000) := by
  exact
    packedTile32768 757596416 757661952 13 3198 27524 29 _ _ (408913 / 20000) (255571 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell757661952 :
    ThetaLowerSegment 757661952 757727488 (37881186824607 / 50000) (75768771118131 / 100000) := by
  exact
    packedTile32768 757661952 757727488 13 3129 27525 29 _ _ (2044573 / 100000) (63893 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell757727488 :
    ThetaLowerSegment 757727488 757793024 (75768771118131 / 100000) (75775309691367 / 100000) := by
  exact
    packedTile32768 757727488 757793024 13 3198 27526 29 _ _ (1022291 / 50000) (408917 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell757793024 :
    ThetaLowerSegment 757793024 757858560 (75775309691367 / 100000) (37890927213579 / 50000) := by
  exact
    packedTile32768 757793024 757858560 13 3201 27528 29 _ _ (2044591 / 100000) (1022297 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell757858560 :
    ThetaLowerSegment 757858560 757924096 (37890927213579 / 50000) (75788399188557 / 100000) := by
  exact
    packedTile32768 757858560 757924096 13 3201 27529 29 _ _ (2044599 / 100000) (1022301 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell757924096 :
    ThetaLowerSegment 757924096 757989632 (75788399188557 / 100000) (606360287889 / 800) := by
  exact
    packedTile32768 757924096 757989632 13 3246 27530 29 _ _ (63894 / 3125) (2044611 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell757989632 :
    ThetaLowerSegment 757989632 758055168 (606360287889 / 800) (75801591028227 / 100000) := by
  exact
    packedTile32768 757989632 758055168 13 3206 27531 29 _ _ (2044617 / 100000) (102231 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell758055168 :
    ThetaLowerSegment 758055168 758120704 (75801591028227 / 100000) (2368998878886 / 3125) := by
  exact
    packedTile32768 758055168 758120704 13 3117 27532 29 _ _ (16357 / 800) (511157 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell758120704 :
    ThetaLowerSegment 758120704 758186240 (2368998878886 / 3125) (7581452126559 / 10000) := by
  exact
    packedTile32768 758120704 758186240 13 3207 27533 29 _ _ (1022317 / 50000) (2044637 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell758186240 :
    ThetaLowerSegment 758186240 758251776 (7581452126559 / 10000) (758209721111 / 1000) := by
  exact
    packedTile32768 758186240 758251776 13 3155 27535 29 _ _ (1022321 / 50000) (408929 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell758251776 :
    ThetaLowerSegment 758251776 758317312 (758209721111 / 1000) (75827594735689 / 100000) := by
  exact
    packedTile32768 758251776 758317312 13 3239 27536 29 _ _ (2044651 / 100000) (1022327 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell758317312 :
    ThetaLowerSegment 758317312 758382848 (75827594735689 / 100000) (75834051771969 / 100000) := by
  exact
    packedTile32768 758317312 758382848 13 3158 27537 29 _ _ (102233 / 5000) (2044663 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell758382848 :
    ThetaLowerSegment 758382848 758448384 (75834051771969 / 100000) (75840559950213 / 100000) := by
  exact
    packedTile32768 758382848 758448384 13 3183 27538 29 _ _ (511167 / 25000) (2044671 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell758448384 :
    ThetaLowerSegment 758448384 758513920 (75840559950213 / 100000) (37923568838061 / 50000) := by
  exact
    packedTile32768 758448384 758513920 13 3217 27539 29 _ _ (2044677 / 100000) (51117 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell758513920 :
    ThetaLowerSegment 758513920 758579456 (37923568838061 / 50000) (18963438058833 / 25000) := by
  exact
    packedTile32768 758513920 758579456 13 3235 27541 29 _ _ (1022343 / 50000) (2044689 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell758579456 :
    ThetaLowerSegment 758579456 758644992 (18963438058833 / 25000) (4741266664401 / 6250) := by
  exact
    packedTile32768 758579456 758644992 13 3186 27542 29 _ _ (1022347 / 50000) (2044697 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell758644992 :
    ThetaLowerSegment 758644992 758710528 (4741266664401 / 6250) (9483345075893 / 12500) := by
  exact
    packedTile32768 758644992 758710528 13 3176 27543 29 _ _ (2044703 / 100000) (1022353 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell758710528 :
    ThetaLowerSegment 758710528 758776064 (9483345075893 / 12500) (9484146602997 / 12500) := by
  exact
    packedTile32768 758710528 758776064 13 3136 27544 29 _ _ (255589 / 12500) (408943 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell758776064 :
    ThetaLowerSegment 758776064 758841600 (9484146602997 / 12500) (9484954522987 / 12500) := by
  exact
    packedTile32768 758776064 758841600 13 3161 27545 29 _ _ (25559 / 1250) (2044723 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell758841600 :
    ThetaLowerSegment 758841600 758907136 (9484954522987 / 12500) (75886177271967 / 100000) := by
  exact
    packedTile32768 758841600 758907136 13 3199 27547 29 _ _ (2044729 / 100000) (511183 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell758907136 :
    ThetaLowerSegment 758907136 758972672 (75886177271967 / 100000) (75892802219847 / 100000) := by
  exact
    packedTile32768 758907136 758972672 13 3240 27548 29 _ _ (2044737 / 100000) (102237 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell758972672 :
    ThetaLowerSegment 758972672 759038208 (75892802219847 / 100000) (75899431286379 / 100000) := by
  exact
    packedTile32768 758972672 759038208 13 3242 27549 29 _ _ (1022373 / 50000) (2044749 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell759038208 :
    ThetaLowerSegment 759038208 759103744 (75899431286379 / 100000) (75905986770909 / 100000) := by
  exact
    packedTile32768 759038208 759103744 13 3206 27550 29 _ _ (408951 / 20000) (1022379 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell759103744 :
    ThetaLowerSegment 759103744 759169280 (75905986770909 / 100000) (75912632250659 / 100000) := by
  exact
    packedTile32768 759103744 759169280 13 3250 27551 29 _ _ (2044763 / 100000) (1022383 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell759169280 :
    ThetaLowerSegment 759169280 759234816 (75912632250659 / 100000) (75919138715163 / 100000) := by
  exact
    packedTile32768 759169280 759234816 13 3182 27553 29 _ _ (511193 / 25000) (81791 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell759234816 :
    ThetaLowerSegment 759234816 759300352 (75919138715163 / 100000) (2372675070872 / 3125) := by
  exact
    packedTile32768 759234816 759300352 13 3161 27554 29 _ _ (2044781 / 100000) (127799 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell759300352 :
    ThetaLowerSegment 759300352 759365888 (2372675070872 / 3125) (75932315310191 / 100000) := by
  exact
    packedTile32768 759300352 759365888 13 3283 27555 30 _ _ (2044789 / 100000) (255599 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell759365888 :
    ThetaLowerSegment 759365888 759431424 (75932315310191 / 100000) (75938872977377 / 100000) := by
  exact
    packedTile32768 759365888 759431424 13 3207 27556 30 _ _ (1022399 / 50000) (2044801 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell759431424 :
    ThetaLowerSegment 759431424 759496960 (75938872977377 / 100000) (75945461345531 / 100000) := by
  exact
    packedTile32768 759431424 759496960 13 3222 27557 30 _ _ (2044807 / 100000) (204481 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell759496960 :
    ThetaLowerSegment 759496960 759562496 (75945461345531 / 100000) (37976032026583 / 50000) := by
  exact
    packedTile32768 759496960 759562496 13 3229 27558 30 _ _ (408963 / 20000) (1022409 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell759562496 :
    ThetaLowerSegment 759562496 759628032 (37976032026583 / 50000) (37979275117447 / 50000) := by
  exact
    packedTile32768 759562496 759628032 13 3172 27560 30 _ _ (255603 / 12500) (2044827 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell759628032 :
    ThetaLowerSegment 759628032 759693568 (37979275117447 / 50000) (1519302201119 / 2000) := by
  exact
    packedTile32768 759628032 759693568 13 3208 27561 30 _ _ (63901 / 3125) (408967 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell759693568 :
    ThetaLowerSegment 759693568 759759104 (1519302201119 / 2000) (75971676040401 / 100000) := by
  exact
    packedTile32768 759693568 759759104 13 3211 27562 30 _ _ (2044841 / 100000) (511211 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell759759104 :
    ThetaLowerSegment 759759104 759824640 (75971676040401 / 100000) (75978178663401 / 100000) := by
  exact
    packedTile32768 759759104 759824640 13 3180 27563 30 _ _ (40897 / 2000) (2044853 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell759824640 :
    ThetaLowerSegment 759824640 759890176 (75978178663401 / 100000) (75984804003321 / 100000) := by
  exact
    packedTile32768 759824640 759890176 13 3240 27564 30 _ _ (1022429 / 50000) (2044861 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell759890176 :
    ThetaLowerSegment 759890176 759955712 (75984804003321 / 100000) (75991327129051 / 100000) := by
  exact
    packedTile32768 759890176 759955712 13 3190 27566 30 _ _ (2044867 / 100000) (204487 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell759955712 :
    ThetaLowerSegment 759955712 760021248 (75991327129051 / 100000) (75997860507871 / 100000) := by
  exact
    packedTile32768 759955712 760021248 13 3195 27567 30 _ _ (511219 / 25000) (2044879 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell760021248 :
    ThetaLowerSegment 760021248 760086784 (75997860507871 / 100000) (76004475707611 / 100000) := by
  exact
    packedTile32768 760021248 760086784 13 3235 27568 30 _ _ (511221 / 25000) (2044887 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell760086784 :
    ThetaLowerSegment 760086784 760152320 (76004475707611 / 100000) (38005504570373 / 50000) := by
  exact
    packedTile32768 760086784 760152320 13 3195 27569 30 _ _ (2044893 / 100000) (63903 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell760152320 :
    ThetaLowerSegment 760152320 760217856 (38005504570373 / 50000) (76017554868847 / 100000) := by
  exact
    packedTile32768 760152320 760217856 13 3201 27570 30 _ _ (2044901 / 100000) (255613 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell760217856 :
    ThetaLowerSegment 760217856 760283392 (76017554868847 / 100000) (76024022919177 / 100000) := by
  exact
    packedTile32768 760217856 760283392 13 3163 27572 30 _ _ (204491 / 10000) (2044913 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell760283392 :
    ThetaLowerSegment 760283392 760348928 (76024022919177 / 100000) (190076503559 / 250) := by
  exact
    packedTile32768 760283392 760348928 13 3217 27573 30 _ _ (2044919 / 100000) (1022461 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell760348928 :
    ThetaLowerSegment 760348928 760414464 (190076503559 / 250) (76037204492883 / 100000) := by
  exact
    packedTile32768 760348928 760414464 13 3229 27574 30 _ _ (2044927 / 100000) (204493 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell760414464 :
    ThetaLowerSegment 760414464 760480000 (76037204492883 / 100000) (15208740250911 / 20000) := by
  exact
    packedTile32768 760414464 760480000 13 3177 27575 30 _ _ (255617 / 12500) (2044939 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell760480000 :
    ThetaLowerSegment 760480000 760545536 (15208740250911 / 20000) (15210048197733 / 20000) := by
  exact
    packedTile32768 760480000 760545536 13 3198 27576 30 _ _ (408989 / 20000) (511237 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell760545536 :
    ThetaLowerSegment 760545536 760611072 (15210048197733 / 20000) (76056817557513 / 100000) := by
  exact
    packedTile32768 760545536 760611072 13 3216 27577 30 _ _ (2044953 / 100000) (511239 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell760611072 :
    ThetaLowerSegment 760611072 760676608 (76056817557513 / 100000) (76063480043709 / 100000) := by
  exact
    packedTile32768 760611072 760676608 13 3258 27579 30 _ _ (1022481 / 50000) (408993 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell760676608 :
    ThetaLowerSegment 760676608 760742144 (76063480043709 / 100000) (76069911474359 / 100000) := by
  exact
    packedTile32768 760676608 760742144 13 3145 27580 30 _ _ (204497 / 10000) (2044973 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell760742144 :
    ThetaLowerSegment 760742144 760807680 (76069911474359 / 100000) (76076434957369 / 100000) := by
  exact
    packedTile32768 760742144 760807680 13 3190 27581 30 _ _ (2044979 / 100000) (1022491 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell760807680 :
    ThetaLowerSegment 760807680 760873216 (76076434957369 / 100000) (76082980963957 / 100000) := by
  exact
    packedTile32768 760807680 760873216 13 3201 27582 30 _ _ (511247 / 25000) (2044991 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell760873216 :
    ThetaLowerSegment 760873216 760938752 (76082980963957 / 100000) (76089516771173 / 100000) := by
  exact
    packedTile32768 760873216 760938752 13 3196 27583 30 _ _ (511249 / 25000) (2044999 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell760938752 :
    ThetaLowerSegment 760938752 761004288 (76089516771173 / 100000) (19024037180597 / 25000) := by
  exact
    packedTile32768 760938752 761004288 13 3243 27585 30 _ _ (409001 / 20000) (127813 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell761004288 :
    ThetaLowerSegment 761004288 761069824 (19024037180597 / 25000) (19025693641127 / 25000) := by
  exact
    packedTile32768 761004288 761069824 13 3240 27586 30 _ _ (2045013 / 100000) (255627 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell761069824 :
    ThetaLowerSegment 761069824 761135360 (19025693641127 / 25000) (38054617394503 / 50000) := by
  exact
    packedTile32768 761069824 761135360 13 3159 27587 30 _ _ (1022511 / 50000) (81801 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell761135360 :
    ThetaLowerSegment 761135360 761200896 (38054617394503 / 50000) (19028933474381 / 25000) := by
  exact
    packedTile32768 761135360 761200896 13 3178 27588 30 _ _ (2045031 / 100000) (1022517 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell761200896 :
    ThetaLowerSegment 761200896 761266432 (19028933474381 / 25000) (76122320968143 / 100000) := by
  exact
    packedTile32768 761200896 761266432 13 3221 27589 30 _ _ (2045039 / 100000) (1022521 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell761266432 :
    ThetaLowerSegment 761266432 761331968 (76122320968143 / 100000) (76128793545063 / 100000) := by
  exact
    packedTile32768 761266432 761331968 13 3165 27591 30 _ _ (255631 / 12500) (2045051 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell761331968 :
    ThetaLowerSegment 761331968 761397504 (76128793545063 / 100000) (76135415439629 / 100000) := by
  exact
    packedTile32768 761331968 761397504 13 3238 27592 30 _ _ (2045057 / 100000) (102253 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell761397504 :
    ThetaLowerSegment 761397504 761463040 (76135415439629 / 100000) (38070968575957 / 50000) := by
  exact
    packedTile32768 761397504 761463040 13 3189 27593 30 _ _ (409013 / 20000) (511267 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell761463040 :
    ThetaLowerSegment 761463040 761528576 (38070968575957 / 50000) (38074289776133 / 50000) := by
  exact
    packedTile32768 761463040 761528576 13 3248 27594 30 _ _ (1022537 / 50000) (2045077 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell761528576 :
    ThetaLowerSegment 761528576 761594112 (38074289776133 / 50000) (95194127171 / 125) := by
  exact
    packedTile32768 761528576 761594112 13 3287 27595 30 _ _ (1022541 / 50000) (409017 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell761594112 :
    ThetaLowerSegment 761594112 761659648 (95194127171 / 125) (19040463552091 / 25000) := by
  exact
    packedTile32768 761594112 761659648 13 3204 27596 30 _ _ (2045091 / 100000) (1022547 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell761659648 :
    ThetaLowerSegment 761659648 761725184 (19040463552091 / 25000) (4760526314029 / 6250) := by
  exact
    packedTile32768 761659648 761725184 13 3211 27598 30 _ _ (20451 / 1000) (2045103 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell761725184 :
    ThetaLowerSegment 761725184 761790720 (4760526314029 / 6250) (9521872205089 / 12500) := by
  exact
    packedTile32768 761725184 761790720 13 3206 27599 30 _ _ (511277 / 25000) (2045111 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell761790720 :
    ThetaLowerSegment 761790720 761856256 (9521872205089 / 12500) (76181470887187 / 100000) := by
  exact
    packedTile32768 761790720 761856256 13 3175 27600 30 _ _ (2045117 / 100000) (12782 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell761856256 :
    ThetaLowerSegment 761856256 761921792 (76181470887187 / 100000) (19046994107453 / 25000) := by
  exact
    packedTile32768 761856256 761921792 13 3181 27601 30 _ _ (16361 / 800) (255641 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell761921792 :
    ThetaLowerSegment 761921792 761987328 (19046994107453 / 25000) (38097306444821 / 50000) := by
  exact
    packedTile32768 761921792 761987328 13 3245 27602 30 _ _ (1022567 / 50000) (2045137 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell761987328 :
    ThetaLowerSegment 761987328 762052864 (38097306444821 / 50000) (76201183934101 / 100000) := by
  exact
    packedTile32768 761987328 762052864 13 3213 27604 30 _ _ (2045143 / 100000) (1022573 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell762052864 :
    ThetaLowerSegment 762052864 762118400 (76201183934101 / 100000) (76207752959113 / 100000) := by
  exact
    packedTile32768 762052864 762118400 13 3212 27605 30 _ _ (2045151 / 100000) (1022577 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell762118400 :
    ThetaLowerSegment 762118400 762183936 (76207752959113 / 100000) (76214416090393 / 100000) := by
  exact
    packedTile32768 762118400 762183936 13 3258 27606 30 _ _ (51129 / 2500) (2045163 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell762183936 :
    ThetaLowerSegment 762183936 762249472 (76214416090393 / 100000) (76220925860137 / 100000) := by
  exact
    packedTile32768 762183936 762249472 13 3183 27607 30 _ _ (127823 / 6250) (2045171 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell762249472 :
    ThetaLowerSegment 762249472 762315008 (76220925860137 / 100000) (76227523601139 / 100000) := by
  exact
    packedTile32768 762249472 762315008 13 3226 27608 30 _ _ (2045177 / 100000) (102259 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell762315008 :
    ThetaLowerSegment 762315008 762380544 (76227523601139 / 100000) (76234154094151 / 100000) := by
  exact
    packedTile32768 762315008 762380544 13 3242 27610 30 _ _ (1022593 / 50000) (2045189 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell762380544 :
    ThetaLowerSegment 762380544 762446080 (76234154094151 / 100000) (76240688488981 / 100000) := by
  exact
    packedTile32768 762380544 762446080 13 3195 27611 30 _ _ (1022597 / 50000) (2045197 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell762446080 :
    ThetaLowerSegment 762446080 762511616 (76240688488981 / 100000) (15249449900041 / 20000) := by
  exact
    packedTile32768 762446080 762511616 13 3208 27612 30 _ _ (2045203 / 100000) (1022603 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell762511616 :
    ThetaLowerSegment 762511616 762577152 (15249449900041 / 20000) (2382931643197 / 3125) := by
  exact
    packedTile32768 762511616 762577152 13 3209 27613 30 _ _ (2045211 / 100000) (1022607 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell762577152 :
    ThetaLowerSegment 762577152 762642688 (2382931643197 / 3125) (19065073471121 / 25000) := by
  exact
    packedTile32768 762577152 762642688 13 3169 27614 30 _ _ (102261 / 5000) (2045223 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell762642688 :
    ThetaLowerSegment 762642688 762708224 (19065073471121 / 25000) (76266840662513 / 100000) := by
  exact
    packedTile32768 762642688 762708224 13 3201 27615 30 _ _ (2045229 / 100000) (127827 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell762708224 :
    ThetaLowerSegment 762708224 762773760 (76266840662513 / 100000) (15254699990837 / 20000) := by
  exact
    packedTile32768 762708224 762773760 13 3256 27617 30 _ _ (2045237 / 100000) (51131 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell762773760 :
    ThetaLowerSegment 762773760 762839296 (15254699990837 / 20000) (76280151094177 / 100000) := by
  exact
    packedTile32768 762773760 762839296 13 3252 27618 30 _ _ (1022623 / 50000) (2045249 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell762839296 :
    ThetaLowerSegment 762839296 762904832 (76280151094177 / 100000) (76286732721549 / 100000) := by
  exact
    packedTile32768 762839296 762904832 13 3218 27619 30 _ _ (1022627 / 50000) (2045257 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell762904832 :
    ThetaLowerSegment 762904832 762970368 (76286732721549 / 100000) (15258644059157 / 20000) := by
  exact
    packedTile32768 762904832 762970368 13 3172 27620 30 _ _ (2045263 / 100000) (1022633 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell762970368 :
    ThetaLowerSegment 762970368 763035904 (15258644059157 / 20000) (76299789706237 / 100000) := by
  exact
    packedTile32768 762970368 763035904 13 3212 27621 30 _ _ (2045271 / 100000) (1022637 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell763035904 :
    ThetaLowerSegment 763035904 763101440 (76299789706237 / 100000) (76306320285277 / 100000) := by
  exact
    packedTile32768 763035904 763101440 13 3193 27623 30 _ _ (12783 / 625) (2045283 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell763101440 :
    ThetaLowerSegment 763101440 763166976 (76306320285277 / 100000) (38156425446527 / 50000) := by
  exact
    packedTile32768 763101440 763166976 13 3193 27624 30 _ _ (2045289 / 100000) (511323 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell763166976 :
    ThetaLowerSegment 763166976 763232512 (38156425446527 / 50000) (38159612019253 / 50000) := by
  exact
    packedTile32768 763166976 763232512 13 3116 27625 30 _ _ (2045297 / 100000) (20453 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell763232512 :
    ThetaLowerSegment 763232512 763298048 (38159612019253 / 50000) (19081438675141 / 25000) := by
  exact
    packedTile32768 763232512 763298048 13 3193 27626 30 _ _ (1022653 / 50000) (2045309 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell763298048 :
    ThetaLowerSegment 763298048 763363584 (19081438675141 / 25000) (38166150875339 / 50000) := by
  exact
    packedTile32768 763298048 763363584 13 3201 27627 30 _ _ (1022657 / 50000) (2045317 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell763363584 :
    ThetaLowerSegment 763363584 763429120 (38166150875339 / 50000) (4771183804321 / 6250) := by
  exact
    packedTile32768 763363584 763429120 13 3246 27629 30 _ _ (2045323 / 100000) (1022663 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell763429120 :
    ThetaLowerSegment 763429120 763494656 (4771183804321 / 6250) (9543184207443 / 12500) := by
  exact
    packedTile32768 763429120 763494656 13 3194 27630 30 _ _ (511333 / 25000) (409067 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell763494656 :
    ThetaLowerSegment 763494656 763560192 (9543184207443 / 12500) (19087991903511 / 25000) := by
  exact
    packedTile32768 763494656 763560192 13 3175 27631 30 _ _ (102267 / 5000) (2045343 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell763560192 :
    ThetaLowerSegment 763560192 763625728 (19087991903511 / 25000) (76358477959911 / 100000) := by
  exact
    packedTile32768 763560192 763625728 13 3183 27632 30 _ _ (2045349 / 100000) (255669 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell763625728 :
    ThetaLowerSegment 763625728 763691264 (76358477959911 / 100000) (76364949469459 / 100000) := by
  exact
    packedTile32768 763625728 763691264 13 3164 27633 30 _ _ (2045357 / 100000) (25567 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell763691264 :
    ThetaLowerSegment 763691264 763756800 (76364949469459 / 100000) (76371566228469 / 100000) := by
  exact
    packedTile32768 763691264 763756800 13 3235 27634 30 _ _ (1022683 / 50000) (2045369 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell763756800 :
    ThetaLowerSegment 763756800 763822336 (76371566228469 / 100000) (76378154378123 / 100000) := by
  exact
    packedTile32768 763756800 763822336 13 3221 27636 30 _ _ (1022687 / 50000) (2045377 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell763822336 :
    ThetaLowerSegment 763822336 763887872 (76378154378123 / 100000) (76384560517679 / 100000) := by
  exact
    packedTile32768 763822336 763887872 13 3132 27637 30 _ _ (2045383 / 100000) (1022693 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell763887872 :
    ThetaLowerSegment 763887872 763953408 (76384560517679 / 100000) (76391042364927 / 100000) := by
  exact
    packedTile32768 763887872 763953408 13 3169 27638 30 _ _ (127837 / 6250) (409079 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell763953408 :
    ThetaLowerSegment 763953408 764018944 (76391042364927 / 100000) (76397581508727 / 100000) := by
  exact
    packedTile32768 763953408 764018944 13 3197 27639 30 _ _ (10227 / 500) (2045403 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell764018944 :
    ThetaLowerSegment 764018944 764084480 (76397581508727 / 100000) (76404053182803 / 100000) := by
  exact
    packedTile32768 764018944 764084480 13 3164 27640 30 _ _ (2045409 / 100000) (511353 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell764084480 :
    ThetaLowerSegment 764084480 764150016 (76404053182803 / 100000) (76410668061381 / 100000) := by
  exact
    packedTile32768 764084480 764150016 13 3234 27642 30 _ _ (2045417 / 100000) (102271 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell764150016 :
    ThetaLowerSegment 764150016 764215552 (76410668061381 / 100000) (76417076381039 / 100000) := by
  exact
    packedTile32768 764150016 764215552 13 3133 27643 30 _ _ (1022713 / 50000) (2045429 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell764215552 :
    ThetaLowerSegment 764215552 764281088 (76417076381039 / 100000) (76423679045219 / 100000) := by
  exact
    packedTile32768 764215552 764281088 13 3228 27644 30 _ _ (409087 / 20000) (1022719 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell764281088 :
    ThetaLowerSegment 764281088 764346624 (76423679045219 / 100000) (38215141890333 / 50000) := by
  exact
    packedTile32768 764281088 764346624 13 3229 27645 30 _ _ (2045443 / 100000) (1022723 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell764346624 :
    ThetaLowerSegment 764346624 764412160 (38215141890333 / 50000) (7643675149989 / 10000) := by
  exact
    packedTile32768 764346624 764412160 13 3162 27646 30 _ _ (511363 / 25000) (409091 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell764412160 :
    ThetaLowerSegment 764412160 764477696 (7643675149989 / 10000) (7644331129011 / 10000) := by
  exact
    packedTile32768 764412160 764477696 13 3207 27648 30 _ _ (102273 / 5000) (2045463 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell764477696 :
    ThetaLowerSegment 764477696 764543232 (7644331129011 / 10000) (38224916122641 / 50000) := by
  exact
    packedTile32768 764477696 764543232 13 3188 27649 30 _ _ (2045469 / 100000) (63921 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell764543232 :
    ThetaLowerSegment 764543232 764608768 (38224916122641 / 50000) (7645630413451 / 10000) := by
  exact
    packedTile32768 764543232 764608768 13 3164 27650 30 _ _ (2045477 / 100000) (51137 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell764608768 :
    ThetaLowerSegment 764608768 764674304 (7645630413451 / 10000) (38231388026107 / 50000) := by
  exact
    packedTile32768 764608768 764674304 13 3164 27651 30 _ _ (1022743 / 50000) (2045489 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell764674304 :
    ThetaLowerSegment 764674304 764739840 (38231388026107 / 50000) (38234709909987 / 50000) := by
  exact
    packedTile32768 764674304 764739840 13 3248 27652 30 _ _ (409099 / 20000) (1022749 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell764739840 :
    ThetaLowerSegment 764739840 764805376 (38234709909987 / 50000) (19118967834109 / 25000) := by
  exact
    packedTile32768 764739840 764805376 13 3154 27653 30 _ _ (2045503 / 100000) (1022753 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell764805376 :
    ThetaLowerSegment 764805376 764870912 (19118967834109 / 25000) (19120621119183 / 25000) := by
  exact
    packedTile32768 764805376 764870912 13 3233 27655 30 _ _ (255689 / 12500) (409103 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell764870912 :
    ThetaLowerSegment 764870912 764936448 (19120621119183 / 25000) (19122273899343 / 25000) := by
  exact
    packedTile32768 764870912 764936448 13 3232 27656 30 _ _ (25569 / 1250) (2045523 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell764936448 :
    ThetaLowerSegment 764936448 765001984 (19122273899343 / 25000) (76495545150309 / 100000) := by
  exact
    packedTile32768 764936448 765001984 13 3153 27657 30 _ _ (2045529 / 100000) (511383 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell765001984 :
    ThetaLowerSegment 765001984 765067520 (76495545150309 / 100000) (76502070413339 / 100000) := by
  exact
    packedTile32768 765001984 765067520 13 3190 27658 30 _ _ (2045537 / 100000) (102277 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell765067520 :
    ThetaLowerSegment 765067520 765133056 (76502070413339 / 100000) (76508579340711 / 100000) := by
  exact
    packedTile32768 765067520 765133056 13 3182 27659 30 _ _ (1022773 / 50000) (2045549 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell765133056 :
    ThetaLowerSegment 765133056 765198592 (76508579340711 / 100000) (38257563581133 / 50000) := by
  exact
    packedTile32768 765133056 765198592 13 3201 27661 30 _ _ (409111 / 20000) (1022779 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell765198592 :
    ThetaLowerSegment 765198592 765264128 (38257563581133 / 50000) (76521736376319 / 100000) := by
  exact
    packedTile32768 765198592 765264128 13 3231 27662 30 _ _ (2045563 / 100000) (1022783 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell765264128 :
    ThetaLowerSegment 765264128 765329664 (76521736376319 / 100000) (76528081740663 / 100000) := by
  exact
    packedTile32768 765264128 765329664 13 3102 27663 30 _ _ (511393 / 25000) (81823 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell765329664 :
    ThetaLowerSegment 765329664 765395200 (76528081740663 / 100000) (76534740103563 / 100000) := by
  exact
    packedTile32768 765329664 765395200 13 3255 27664 30 _ _ (102279 / 5000) (2045583 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell765395200 :
    ThetaLowerSegment 765395200 765460736 (76534740103563 / 100000) (19135291324653 / 25000) := by
  exact
    packedTile32768 765395200 765460736 13 3141 27665 30 _ _ (2045589 / 100000) (255699 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell765460736 :
    ThetaLowerSegment 765460736 765526272 (19135291324653 / 25000) (76547696889833 / 100000) := by
  exact
    packedTile32768 765460736 765526272 13 3193 27666 30 _ _ (2045597 / 100000) (2557 / 125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell765526272 :
    ThetaLowerSegment 765526272 765591808 (76547696889833 / 100000) (76554240783427 / 100000) := by
  exact
    packedTile32768 765526272 765591808 13 3199 27668 30 _ _ (1022803 / 50000) (2045609 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell765591808 :
    ThetaLowerSegment 765591808 765657344 (76554240783427 / 100000) (76560839934191 / 100000) := by
  exact
    packedTile32768 765591808 765657344 13 3226 27669 30 _ _ (1022807 / 50000) (2045617 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell765657344 :
    ThetaLowerSegment 765657344 765722880 (76560839934191 / 100000) (76567373654053 / 100000) := by
  exact
    packedTile32768 765657344 765722880 13 3194 27670 30 _ _ (2045623 / 100000) (1022813 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell765722880 :
    ThetaLowerSegment 765722880 765788416 (76567373654053 / 100000) (76573974908517 / 100000) := by
  exact
    packedTile32768 765722880 765788416 13 3227 27671 30 _ _ (63926 / 3125) (409127 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell765788416 :
    ThetaLowerSegment 765788416 765853952 (76573974908517 / 100000) (76580488226277 / 100000) := by
  exact
    packedTile32768 765788416 765853952 13 3184 27672 30 _ _ (51141 / 2500) (2045643 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell765853952 :
    ThetaLowerSegment 765853952 765919488 (76580488226277 / 100000) (38293530448257 / 50000) := by
  exact
    packedTile32768 765853952 765919488 13 3213 27674 30 _ _ (2045649 / 100000) (511413 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell765919488 :
    ThetaLowerSegment 765919488 765985024 (38293530448257 / 50000) (76593539492233 / 100000) := by
  exact
    packedTile32768 765919488 765985024 13 3167 27675 30 _ _ (2045657 / 100000) (102283 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell765985024 :
    ThetaLowerSegment 765985024 766050560 (76593539492233 / 100000) (76600118354089 / 100000) := by
  exact
    packedTile32768 765985024 766050560 13 3216 27676 30 _ _ (1022833 / 50000) (2045669 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell766050560 :
    ThetaLowerSegment 766050560 766116096 (76600118354089 / 100000) (76606658373867 / 100000) := by
  exact
    packedTile32768 766050560 766116096 13 3197 27677 30 _ _ (1022837 / 50000) (2045677 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell766116096 :
    ThetaLowerSegment 766116096 766181632 (76606658373867 / 100000) (15322647458079 / 20000) := by
  exact
    packedTile32768 766116096 766181632 13 3216 27678 30 _ _ (2045683 / 100000) (1022843 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell766181632 :
    ThetaLowerSegment 766181632 766247168 (15322647458079 / 20000) (76619820324033 / 100000) := by
  exact
    packedTile32768 766181632 766247168 13 3218 27679 30 _ _ (2045691 / 100000) (1022847 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell766247168 :
    ThetaLowerSegment 766247168 766312704 (76619820324033 / 100000) (76626348152733 / 100000) := by
  exact
    packedTile32768 766247168 766312704 13 3191 27681 30 _ _ (20457 / 1000) (2045703 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell766312704 :
    ThetaLowerSegment 766312704 766378240 (76626348152733 / 100000) (38316423685113 / 50000) := by
  exact
    packedTile32768 766312704 766378240 13 3177 27682 30 _ _ (2045709 / 100000) (127857 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell766378240 :
    ThetaLowerSegment 766378240 766443776 (38316423685113 / 50000) (19159800341807 / 25000) := by
  exact
    packedTile32768 766378240 766443776 13 3106 27683 30 _ _ (2045717 / 100000) (51143 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell766443776 :
    ThetaLowerSegment 766443776 766509312 (19159800341807 / 25000) (3832288611957 / 5000) := by
  exact
    packedTile32768 766443776 766509312 13 3212 27684 30 _ _ (1022863 / 50000) (2045729 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell766509312 :
    ThetaLowerSegment 766509312 766574848 (3832288611957 / 5000) (2395384572298 / 3125) := by
  exact
    packedTile32768 766509312 766574848 13 3194 27685 30 _ _ (1022867 / 50000) (2045737 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell766574848 :
    ThetaLowerSegment 766574848 766640384 (2395384572298 / 3125) (76658936566599 / 100000) := by
  exact
    packedTile32768 766574848 766640384 13 3241 27687 30 _ _ (2045743 / 100000) (1022873 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell766640384 :
    ThetaLowerSegment 766640384 766705920 (76658936566599 / 100000) (76665507518811 / 100000) := by
  exact
    packedTile32768 766640384 766705920 13 3212 27688 30 _ _ (2045751 / 100000) (1022877 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell766705920 :
    ThetaLowerSegment 766705920 766771456 (76665507518811 / 100000) (76672045767771 / 100000) := by
  exact
    packedTile32768 766705920 766771456 13 3196 27689 30 _ _ (12786 / 625) (2045763 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell766771456 :
    ThetaLowerSegment 766771456 766836992 (76672045767771 / 100000) (15335731947143 / 20000) := by
  exact
    packedTile32768 766771456 766836992 13 3233 27690 30 _ _ (255721 / 12500) (2045771 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell766836992 :
    ThetaLowerSegment 766836992 766902528 (15335731947143 / 20000) (76685169398129 / 100000) := by
  exact
    packedTile32768 766836992 766902528 13 3182 27691 30 _ _ (2045777 / 100000) (102289 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell766902528 :
    ThetaLowerSegment 766902528 766968064 (76685169398129 / 100000) (76691746600119 / 100000) := by
  exact
    packedTile32768 766902528 766968064 13 3215 27693 30 _ _ (1022893 / 50000) (2045789 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell766968064 :
    ThetaLowerSegment 766968064 767033600 (76691746600119 / 100000) (15339666402201 / 20000) := by
  exact
    packedTile32768 766968064 767033600 13 3219 27694 30 _ _ (1022897 / 50000) (2045797 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell767033600 :
    ThetaLowerSegment 767033600 767099136 (15339666402201 / 20000) (76704882672211 / 100000) := by
  exact
    packedTile32768 767033600 767099136 13 3202 27695 30 _ _ (2045803 / 100000) (1022903 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell767099136 :
    ThetaLowerSegment 767099136 767164672 (76704882672211 / 100000) (76711511099851 / 100000) := by
  exact
    packedTile32768 767099136 767164672 13 3240 27696 30 _ _ (2045811 / 100000) (1022907 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell767164672 :
    ThetaLowerSegment 767164672 767230208 (76711511099851 / 100000) (76718096594431 / 100000) := by
  exact
    packedTile32768 767164672 767230208 13 3219 27697 30 _ _ (102291 / 5000) (2045823 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell767230208 :
    ThetaLowerSegment 767230208 767295744 (76718096594431 / 100000) (76724753718743 / 100000) := by
  exact
    packedTile32768 767230208 767295744 13 3254 27698 30 _ _ (511457 / 25000) (2045831 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell767295744 :
    ThetaLowerSegment 767295744 767361280 (76724753718743 / 100000) (38365612350587 / 50000) := by
  exact
    packedTile32768 767295744 767361280 13 3163 27700 30 _ _ (2045837 / 100000) (25573 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell767361280 :
    ThetaLowerSegment 767361280 767426816 (38365612350587 / 50000) (76737789817779 / 100000) := by
  exact
    packedTile32768 767361280 767426816 13 3209 27701 30 _ _ (409169 / 20000) (255731 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell767426816 :
    ThetaLowerSegment 767426816 767492352 (76737789817779 / 100000) (76744309954477 / 100000) := by
  exact
    packedTile32768 767426816 767492352 13 3187 27702 30 _ _ (1022927 / 50000) (2045857 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell767492352 :
    ThetaLowerSegment 767492352 767557888 (76744309954477 / 100000) (76750901721841 / 100000) := by
  exact
    packedTile32768 767492352 767557888 13 3222 27703 30 _ _ (1022931 / 50000) (409173 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell767557888 :
    ThetaLowerSegment 767557888 767623424 (76750901721841 / 100000) (4797342705553 / 6250) := by
  exact
    packedTile32768 767557888 767623424 13 3217 27704 30 _ _ (2045871 / 100000) (1022937 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell767623424 :
    ThetaLowerSegment 767623424 767688960 (4797342705553 / 6250) (19191017754807 / 25000) := by
  exact
    packedTile32768 767623424 767688960 13 3220 27706 30 _ _ (2045879 / 100000) (1022941 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell767688960 :
    ThetaLowerSegment 767688960 767754496 (19191017754807 / 25000) (19192648327543 / 25000) := by
  exact
    packedTile32768 767688960 767754496 13 3188 27707 30 _ _ (63934 / 3125) (2045891 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell767754496 :
    ThetaLowerSegment 767754496 767820032 (19192648327543 / 25000) (7677716882313 / 10000) := by
  exact
    packedTile32768 767754496 767820032 13 3214 27708 30 _ _ (2045897 / 100000) (20459 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell767820032 :
    ThetaLowerSegment 767820032 767885568 (7677716882313 / 10000) (7678365025017 / 10000) := by
  exact
    packedTile32768 767820032 767885568 13 3168 27709 30 _ _ (409181 / 20000) (511477 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell767885568 :
    ThetaLowerSegment 767885568 767951104 (7678365025017 / 10000) (38395168148561 / 50000) := by
  exact
    packedTile32768 767885568 767951104 13 3268 27710 30 _ _ (1022957 / 50000) (2045917 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell767951104 :
    ThetaLowerSegment 767951104 768016640 (38395168148561 / 50000) (19199207001907 / 25000) := by
  exact
    packedTile32768 767951104 768016640 13 3173 27711 30 _ _ (1022961 / 50000) (81837 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell768016640 :
    ThetaLowerSegment 768016640 768082176 (19199207001907 / 25000) (15360681953531 / 20000) := by
  exact
    packedTile32768 768016640 768082176 13 3217 27713 30 _ _ (2045931 / 100000) (1022967 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell768082176 :
    ThetaLowerSegment 768082176 768147712 (15360681953531 / 20000) (9601255593479 / 12500) := by
  exact
    packedTile32768 768082176 768147712 13 3243 27714 30 _ _ (2045939 / 100000) (1022971 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell768147712 :
    ThetaLowerSegment 768147712 768213248 (9601255593479 / 12500) (4801031104239 / 6250) := by
  exact
    packedTile32768 768147712 768213248 13 3154 27715 30 _ _ (511487 / 25000) (2045951 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell768213248 :
    ThetaLowerSegment 768213248 768278784 (4801031104239 / 6250) (9602864734719 / 12500) := by
  exact
    packedTile32768 768213248 768278784 13 3138 27716 30 _ _ (511489 / 25000) (2045959 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell768278784 :
    ThetaLowerSegment 768278784 768344320 (9602864734719 / 12500) (2400921291671 / 3125) := by
  exact
    packedTile32768 768278784 768344320 13 3208 27717 30 _ _ (409193 / 20000) (127873 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell768344320 :
    ThetaLowerSegment 768344320 768409856 (2400921291671 / 3125) (19209033709417 / 25000) := by
  exact
    packedTile32768 768344320 768409856 13 3252 27719 30 _ _ (2045973 / 100000) (255747 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell768409856 :
    ThetaLowerSegment 768409856 768475392 (19209033709417 / 25000) (2401334962742 / 3125) := by
  exact
    packedTile32768 768409856 768475392 13 3218 27720 30 _ _ (1022991 / 50000) (409197 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell768475392 :
    ThetaLowerSegment 768475392 768540928 (2401334962742 / 3125) (38424697436557 / 50000) := by
  exact
    packedTile32768 768475392 768540928 13 3263 27721 30 _ _ (204599 / 10000) (2045993 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell768540928 :
    ThetaLowerSegment 768540928 768606464 (38424697436557 / 50000) (76855985035893 / 100000) := by
  exact
    packedTile32768 768540928 768606464 13 3221 27722 30 _ _ (2045999 / 100000) (1023001 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell768606464 :
    ThetaLowerSegment 768606464 768672000 (76855985035893 / 100000) (76862393129817 / 100000) := by
  exact
    packedTile32768 768606464 768672000 13 3132 27723 30 _ _ (2046007 / 100000) (204601 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell768672000 :
    ThetaLowerSegment 768672000 768737536 (76862393129817 / 100000) (76868983347353 / 100000) := by
  exact
    packedTile32768 768672000 768737536 13 3221 27724 30 _ _ (63938 / 3125) (2046019 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell768737536 :
    ThetaLowerSegment 768737536 768803072 (76868983347353 / 100000) (76875641112703 / 100000) := by
  exact
    packedTile32768 768737536 768803072 13 3254 27726 30 _ _ (81841 / 4000) (511507 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell768803072 :
    ThetaLowerSegment 768803072 768868608 (76875641112703 / 100000) (3075286227271 / 4000) := by
  exact
    packedTile32768 768803072 768868608 13 3184 27727 30 _ _ (2046033 / 100000) (511509 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell768868608 :
    ThetaLowerSegment 768868608 768934144 (3075286227271 / 4000) (76888737798889 / 100000) := by
  exact
    packedTile32768 768868608 768934144 13 3217 27728 30 _ _ (1023021 / 50000) (409209 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell768934144 :
    ThetaLowerSegment 768934144 768999680 (76888737798889 / 100000) (76895297435189 / 100000) := by
  exact
    packedTile32768 768934144 768999680 13 3206 27729 30 _ _ (40921 / 2000) (2046053 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell768999680 :
    ThetaLowerSegment 768999680 769065216 (76895297435189 / 100000) (76901898021523 / 100000) := by
  exact
    packedTile32768 768999680 769065216 13 3226 27730 30 _ _ (2046059 / 100000) (1023031 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell769065216 :
    ThetaLowerSegment 769065216 769130752 (76901898021523 / 100000) (76908465896593 / 100000) := by
  exact
    packedTile32768 769065216 769130752 13 3210 27732 30 _ _ (2046067 / 100000) (204607 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell769130752 :
    ThetaLowerSegment 769130752 769196288 (76908465896593 / 100000) (15382997348161 / 20000) := by
  exact
    packedTile32768 769130752 769196288 13 3187 27733 30 _ _ (511519 / 25000) (2046079 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell769196288 :
    ThetaLowerSegment 769196288 769261824 (15382997348161 / 20000) (76921562854781 / 100000) := by
  exact
    packedTile32768 769196288 769261824 13 3214 27734 30 _ _ (511521 / 25000) (2046087 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell769261824 :
    ThetaLowerSegment 769261824 769327360 (76921562854781 / 100000) (15385633528597 / 20000) := by
  exact
    packedTile32768 769261824 769327360 13 3228 27735 30 _ _ (2046093 / 100000) (127881 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell769327360 :
    ThetaLowerSegment 769327360 769392896 (15385633528597 / 20000) (76934702889579 / 100000) := by
  exact
    packedTile32768 769327360 769392896 13 3194 27736 30 _ _ (2046101 / 100000) (255763 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell769392896 :
    ThetaLowerSegment 769392896 769458432 (76934702889579 / 100000) (76941197242719 / 100000) := by
  exact
    packedTile32768 769392896 769458432 13 3174 27737 30 _ _ (204611 / 10000) (2046113 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell769458432 :
    ThetaLowerSegment 769458432 769523968 (76941197242719 / 100000) (76947773465971 / 100000) := by
  exact
    packedTile32768 769458432 769523968 13 3214 27739 30 _ _ (1023059 / 50000) (2046121 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell769523968 :
    ThetaLowerSegment 769523968 769589504 (76947773465971 / 100000) (38477194297281 / 50000) := by
  exact
    packedTile32768 769523968 769589504 13 3233 27740 30 _ _ (2046127 / 100000) (204613 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell769589504 :
    ThetaLowerSegment 769589504 769655040 (38477194297281 / 50000) (76960991472207 / 100000) := by
  exact
    packedTile32768 769589504 769655040 13 3227 27741 30 _ _ (409227 / 20000) (1023069 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell769655040 :
    ThetaLowerSegment 769655040 769720576 (76960991472207 / 100000) (76967588240463 / 100000) := by
  exact
    packedTile32768 769655040 769720576 13 3224 27742 30 _ _ (63942 / 3125) (2046147 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell769720576 :
    ThetaLowerSegment 769720576 769786112 (76967588240463 / 100000) (76974154342231 / 100000) := by
  exact
    packedTile32768 769720576 769786112 13 3209 27743 30 _ _ (255769 / 12500) (409231 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell769786112 :
    ThetaLowerSegment 769786112 769851648 (76974154342231 / 100000) (38490386836533 / 50000) := by
  exact
    packedTile32768 769786112 769851648 13 3235 27745 30 _ _ (2046161 / 100000) (511541 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell769851648 :
    ThetaLowerSegment 769851648 769917184 (38490386836533 / 50000) (38493668891609 / 50000) := by
  exact
    packedTile32768 769851648 769917184 13 3208 27746 30 _ _ (2046169 / 100000) (511543 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell769917184 :
    ThetaLowerSegment 769917184 769982720 (38493668891609 / 50000) (19248453484147 / 25000) := by
  exact
    packedTile32768 769917184 769982720 13 3165 27747 30 _ _ (1023089 / 50000) (2046181 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell769982720 :
    ThetaLowerSegment 769982720 770048256 (19248453484147 / 25000) (38500202350847 / 50000) := by
  exact
    packedTile32768 769982720 770048256 13 3221 27748 30 _ _ (1023093 / 50000) (2046189 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell770048256 :
    ThetaLowerSegment 770048256 770113792 (38500202350847 / 50000) (38503513094357 / 50000) := by
  exact
    packedTile32768 770048256 770113792 13 3236 27749 30 _ _ (409239 / 20000) (1023099 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell770113792 :
    ThetaLowerSegment 770113792 770179328 (38503513094357 / 50000) (77013543345269 / 100000) := by
  exact
    packedTile32768 770113792 770179328 13 3185 27750 30 _ _ (2046203 / 100000) (1023103 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell770179328 :
    ThetaLowerSegment 770179328 770244864 (77013543345269 / 100000) (15404021518673 / 20000) := by
  exact
    packedTile32768 770179328 770244864 13 3208 27752 30 _ _ (511553 / 25000) (409243 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell770244864 :
    ThetaLowerSegment 770244864 770310400 (15404021518673 / 20000) (15405317594421 / 20000) := by
  exact
    packedTile32768 770244864 770310400 13 3167 27753 30 _ _ (102311 / 5000) (2046223 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell770310400 :
    ThetaLowerSegment 770310400 770375936 (15405317594421 / 20000) (2407287223534 / 3125) := by
  exact
    packedTile32768 770310400 770375936 13 3227 27754 30 _ _ (2046229 / 100000) (255779 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell770375936 :
    ThetaLowerSegment 770375936 770441472 (2407287223534 / 3125) (385198450009 / 500) := by
  exact
    packedTile32768 770375936 770441472 13 3176 27755 30 _ _ (2046237 / 100000) (12789 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell770441472 :
    ThetaLowerSegment 770441472 770507008 (385198450009 / 500) (19261580982833 / 25000) := by
  exact
    packedTile32768 770441472 770507008 13 3242 27756 30 _ _ (1023123 / 50000) (2046249 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell770507008 :
    ThetaLowerSegment 770507008 770572544 (19261580982833 / 25000) (770528555741 / 1000) := by
  exact
    packedTile32768 770507008 770572544 13 3192 27758 30 _ _ (1023127 / 50000) (2046257 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell770572544 :
    ThetaLowerSegment 770572544 770638080 (770528555741 / 1000) (9632436706409 / 12500) := by
  exact
    packedTile32768 770572544 770638080 13 3244 27759 30 _ _ (2046263 / 100000) (1023133 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell770638080 :
    ThetaLowerSegment 770638080 770703616 (9632436706409 / 12500) (9633251122267 / 12500) := by
  exact
    packedTile32768 770638080 770703616 13 3184 27760 30 _ _ (2046271 / 100000) (1023137 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell770703616 :
    ThetaLowerSegment 770703616 770769152 (9633251122267 / 12500) (4817030085111 / 6250) := by
  exact
    packedTile32768 770703616 770769152 13 3163 27761 30 _ _ (51157 / 2500) (2046283 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell770769152 :
    ThetaLowerSegment 770769152 770834688 (4817030085111 / 6250) (4817439598497 / 6250) := by
  exact
    packedTile32768 770769152 770834688 13 3202 27762 30 _ _ (127893 / 6250) (2046291 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell770834688 :
    ThetaLowerSegment 770834688 770900224 (4817439598497 / 6250) (3083424005721 / 4000) := by
  exact
    packedTile32768 770834688 770900224 13 3209 27763 30 _ _ (2046297 / 100000) (20463 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell770900224 :
    ThetaLowerSegment 770900224 770965760 (3083424005721 / 4000) (15418445215723 / 20000) := by
  exact
    packedTile32768 770900224 770965760 13 3238 27765 30 _ _ (409261 / 20000) (511577 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell770965760 :
    ThetaLowerSegment 770965760 771031296 (15418445215723 / 20000) (77098786561299 / 100000) := by
  exact
    packedTile32768 770965760 771031296 13 3206 27766 30 _ _ (1023157 / 50000) (2046317 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell771031296 :
    ThetaLowerSegment 771031296 771096832 (77098786561299 / 100000) (77105345023309 / 100000) := by
  exact
    packedTile32768 771031296 771096832 13 3205 27767 30 _ _ (1023161 / 50000) (81853 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell771096832 :
    ThetaLowerSegment 771096832 771162368 (77105345023309 / 100000) (77111897375171 / 100000) := by
  exact
    packedTile32768 771096832 771162368 13 3202 27768 30 _ _ (2046331 / 100000) (1023167 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell771162368 :
    ThetaLowerSegment 771162368 771227904 (77111897375171 / 100000) (19279600671713 / 25000) := by
  exact
    packedTile32768 771162368 771227904 13 3179 27769 30 _ _ (2046339 / 100000) (1023171 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell771227904 :
    ThetaLowerSegment 771227904 771293440 (19279600671713 / 25000) (4820311611773 / 6250) := by
  exact
    packedTile32768 771227904 771293440 13 3217 27770 30 _ _ (511587 / 25000) (2046351 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell771293440 :
    ThetaLowerSegment 771293440 771358976 (4820311611773 / 6250) (19282908599753 / 25000) := by
  exact
    packedTile32768 771293440 771358976 13 3249 27772 30 _ _ (511589 / 25000) (2046359 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell771358976 :
    ThetaLowerSegment 771358976 771424512 (19282908599753 / 25000) (77138180720647 / 100000) := by
  exact
    packedTile32768 771358976 771424512 13 3199 27773 30 _ _ (409273 / 20000) (63949 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell771424512 :
    ThetaLowerSegment 771424512 771490048 (77138180720647 / 100000) (38572363533937 / 50000) := by
  exact
    packedTile32768 771424512 771490048 13 3199 27774 30 _ _ (2046373 / 100000) (255797 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell771490048 :
    ThetaLowerSegment 771490048 771555584 (38572363533937 / 50000) (38575598863879 / 50000) := by
  exact
    packedTile32768 771490048 771555584 13 3162 27775 30 _ _ (1023191 / 50000) (409277 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell771555584 :
    ThetaLowerSegment 771555584 771621120 (38575598863879 / 50000) (38578967221819 / 50000) := by
  exact
    packedTile32768 771555584 771621120 13 3292 27776 30 _ _ (204639 / 10000) (2046393 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell771621120 :
    ThetaLowerSegment 771621120 771686656 (38578967221819 / 50000) (19291113567713 / 25000) := by
  exact
    packedTile32768 771621120 771686656 13 3186 27778 30 _ _ (2046399 / 100000) (1023201 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell771686656 :
    ThetaLowerSegment 771686656 771752192 (19291113567713 / 25000) (15434187866927 / 20000) := by
  exact
    packedTile32768 771686656 771752192 13 3169 27779 30 _ _ (2046407 / 100000) (204641 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell771752192 :
    ThetaLowerSegment 771752192 771817728 (15434187866927 / 20000) (77177557443979 / 100000) := by
  exact
    packedTile32768 771752192 771817728 13 3234 27780 30 _ _ (127901 / 6250) (2046419 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell771817728 :
    ThetaLowerSegment 771817728 771883264 (77177557443979 / 100000) (77183915683347 / 100000) := by
  exact
    packedTile32768 771817728 771883264 13 3107 27781 30 _ _ (255803 / 12500) (2046427 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell771883264 :
    ThetaLowerSegment 771883264 771948800 (77183915683347 / 100000) (77190587054927 / 100000) := by
  exact
    packedTile32768 771883264 771948800 13 3260 27782 30 _ _ (2046433 / 100000) (511609 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell771948800 :
    ThetaLowerSegment 771948800 772014336 (77190587054927 / 100000) (30878897651 / 40) := by
  exact
    packedTile32768 771948800 772014336 13 3253 27783 30 _ _ (2046441 / 100000) (511611 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell772014336 :
    ThetaLowerSegment 772014336 772079872 (30878897651 / 40) (154407503677 / 200) := by
  exact
    packedTile32768 772014336 772079872 13 3180 27785 30 _ _ (40929 / 2000) (2046453 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell772079872 :
    ThetaLowerSegment 772079872 772145408 (154407503677 / 200) (3860517071663 / 5000) := by
  exact
    packedTile32768 772079872 772145408 13 3220 27786 30 _ _ (1023229 / 50000) (2046461 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell772145408 :
    ThetaLowerSegment 772145408 772210944 (3860517071663 / 5000) (77216875802391 / 100000) := by
  exact
    packedTile32768 772145408 772210944 13 3193 27787 30 _ _ (2046467 / 100000) (204647 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell772210944 :
    ThetaLowerSegment 772210944 772276480 (77216875802391 / 100000) (77223457265991 / 100000) := by
  exact
    packedTile32768 772210944 772276480 13 3216 27788 30 _ _ (81859 / 4000) (1023239 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell772276480 :
    ThetaLowerSegment 772276480 772342016 (77223457265991 / 100000) (77229944620271 / 100000) := by
  exact
    packedTile32768 772276480 772342016 13 3170 27789 30 _ _ (511621 / 25000) (2046487 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell772342016 :
    ThetaLowerSegment 772342016 772407552 (77229944620271 / 100000) (77236595719271 / 100000) := by
  exact
    packedTile32768 772342016 772407552 13 3250 27791 30 _ _ (511623 / 25000) (409299 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell772407552 :
    ThetaLowerSegment 772407552 772473088 (77236595719271 / 100000) (19310798921249 / 25000) := by
  exact
    packedTile32768 772407552 772473088 13 3225 27792 30 _ _ (2046501 / 100000) (255813 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell772473088 :
    ThetaLowerSegment 772473088 772538624 (19310798921249 / 25000) (77249791583503 / 100000) := by
  exact
    packedTile32768 772473088 772538624 13 3223 27793 30 _ _ (2046509 / 100000) (127907 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell772538624 :
    ThetaLowerSegment 772538624 772604160 (77249791583503 / 100000) (15451271771953 / 20000) := by
  exact
    packedTile32768 772538624 772604160 13 3209 27794 30 _ _ (1023259 / 50000) (2046521 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell772604160 :
    ThetaLowerSegment 772604160 772669696 (15451271771953 / 20000) (15452599967327 / 20000) := by
  exact
    packedTile32768 772604160 772669696 13 3245 27795 30 _ _ (1023263 / 50000) (2046529 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell772669696 :
    ThetaLowerSegment 772669696 772735232 (15452599967327 / 20000) (15453908931113 / 20000) := by
  exact
    packedTile32768 772669696 772735232 13 3198 27796 30 _ _ (409307 / 20000) (1023269 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell772735232 :
    ThetaLowerSegment 772735232 772800768 (15453908931113 / 20000) (7727616522217 / 10000) := by
  exact
    packedTile32768 772735232 772800768 13 3235 27798 30 _ _ (2046543 / 100000) (1023273 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell772800768 :
    ThetaLowerSegment 772800768 772866304 (7727616522217 / 10000) (38641329465833 / 50000) := by
  exact
    packedTile32768 772800768 772866304 13 3173 27799 30 _ _ (255819 / 12500) (409311 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell772866304 :
    ThetaLowerSegment 772866304 772931840 (38641329465833 / 50000) (38644525169273 / 50000) := by
  exact
    packedTile32768 772866304 772931840 13 3123 27800 30 _ _ (12791 / 625) (2046563 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell772931840 :
    ThetaLowerSegment 772931840 772997376 (38644525169273 / 50000) (1932390290969 / 2500) := by
  exact
    packedTile32768 772931840 772997376 13 3206 27801 30 _ _ (2046569 / 100000) (511643 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell772997376 :
    ThetaLowerSegment 772997376 773062912 (1932390290969 / 2500) (77302113613889 / 100000) := by
  exact
    packedTile32768 772997376 773062912 13 3177 27802 30 _ _ (2046577 / 100000) (102329 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell773062912 :
    ThetaLowerSegment 773062912 773128448 (77302113613889 / 100000) (77308666782261 / 100000) := by
  exact
    packedTile32768 773062912 773128448 13 3202 27804 30 _ _ (1023293 / 50000) (2046589 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell773128448 :
    ThetaLowerSegment 773128448 773193984 (77308666782261 / 100000) (15463047679119 / 20000) := by
  exact
    packedTile32768 773128448 773193984 13 3211 27805 30 _ _ (1023297 / 50000) (2046597 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell773193984 :
    ThetaLowerSegment 773193984 773259520 (15463047679119 / 20000) (15464353411833 / 20000) := by
  exact
    packedTile32768 773193984 773259520 13 3190 27806 30 _ _ (2046603 / 100000) (1023303 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell773259520 :
    ThetaLowerSegment 773259520 773325056 (15464353411833 / 20000) (77328156578707 / 100000) := by
  exact
    packedTile32768 773259520 773325056 13 3122 27807 30 _ _ (2046611 / 100000) (1023307 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell773325056 :
    ThetaLowerSegment 773325056 773390592 (77328156578707 / 100000) (77334713949187 / 100000) := by
  exact
    packedTile32768 773325056 773390592 13 3204 27808 30 _ _ (102331 / 5000) (2046623 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell773390592 :
    ThetaLowerSegment 773390592 773456128 (77334713949187 / 100000) (15468246901199 / 20000) := by
  exact
    packedTile32768 773390592 773456128 13 3186 27809 30 _ _ (511657 / 25000) (2046631 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell773456128 :
    ThetaLowerSegment 773456128 773521664 (15468246901199 / 20000) (15469571074691 / 20000) := by
  exact
    packedTile32768 773456128 773521664 13 3235 27811 30 _ _ (511659 / 25000) (2046639 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell773521664 :
    ThetaLowerSegment 773521664 773587200 (15469571074691 / 20000) (7735443533713 / 10000) := by
  exact
    packedTile32768 773521664 773587200 13 3215 27812 30 _ _ (409329 / 20000) (255831 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell773587200 :
    ThetaLowerSegment 773587200 773652736 (7735443533713 / 10000) (4835053096727 / 6250) := by
  exact
    packedTile32768 773587200 773652736 13 3134 27813 30 _ _ (2046653 / 100000) (63958 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell773652736 :
    ThetaLowerSegment 773652736 773718272 (4835053096727 / 6250) (19341854833163 / 25000) := by
  exact
    packedTile32768 773652736 773718272 13 3210 27814 30 _ _ (1023331 / 50000) (409333 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell773718272 :
    ThetaLowerSegment 773718272 773783808 (19341854833163 / 25000) (38686991501671 / 50000) := by
  exact
    packedTile32768 773718272 773783808 13 3207 27815 30 _ _ (204667 / 10000) (2046673 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell773783808 :
    ThetaLowerSegment 773783808 773849344 (38686991501671 / 50000) (38690262094713 / 50000) := by
  exact
    packedTile32768 773783808 773849344 13 3196 27816 30 _ _ (2046679 / 100000) (1023341 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell773849344 :
    ThetaLowerSegment 773849344 773914880 (38690262094713 / 50000) (38693475393303 / 50000) := by
  exact
    packedTile32768 773849344 773914880 13 3140 27818 30 _ _ (2046687 / 100000) (204669 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell773914880 :
    ThetaLowerSegment 773914880 773980416 (38693475393303 / 50000) (38696850395007 / 50000) := by
  exact
    packedTile32768 773914880 773980416 13 3298 27819 30 _ _ (255837 / 12500) (2046699 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell773980416 :
    ThetaLowerSegment 773980416 774045952 (38696850395007 / 50000) (38700133308223 / 50000) := by
  exact
    packedTile32768 773980416 774045952 13 3208 27820 30 _ _ (127919 / 6250) (2046707 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell774045952 :
    ThetaLowerSegment 774045952 774111488 (38700133308223 / 50000) (77406797677629 / 100000) := by
  exact
    packedTile32768 774045952 774111488 13 3191 27821 30 _ _ (2046713 / 100000) (511679 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell774111488 :
    ThetaLowerSegment 774111488 774177024 (77406797677629 / 100000) (19353319910759 / 25000) := by
  exact
    packedTile32768 774111488 774177024 13 3167 27822 30 _ _ (2046721 / 100000) (511681 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell774177024 :
    ThetaLowerSegment 774177024 774242560 (19353319910759 / 25000) (19354975715329 / 25000) := by
  exact
    packedTile32768 774177024 774242560 13 3236 27824 30 _ _ (204673 / 10000) (2046733 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell774242560 :
    ThetaLowerSegment 774242560 774308096 (19354975715329 / 25000) (2419575486926 / 3125) := by
  exact
    packedTile32768 774242560 774308096 13 3182 27825 30 _ _ (1023369 / 50000) (2046741 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell774308096 :
    ThetaLowerSegment 774308096 774373632 (2419575486926 / 3125) (77432987686249 / 100000) := by
  exact
    packedTile32768 774308096 774373632 13 3211 27826 30 _ _ (2046747 / 100000) (8187 / 400)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell774373632 :
    ThetaLowerSegment 774373632 774439168 (77432987686249 / 100000) (77439574143839 / 100000) := by
  exact
    packedTile32768 774373632 774439168 13 3218 27827 30 _ _ (409351 / 20000) (1023379 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell774439168 :
    ThetaLowerSegment 774439168 774504704 (77439574143839 / 100000) (77446029634341 / 100000) := by
  exact
    packedTile32768 774439168 774504704 13 3154 27828 30 _ _ (2046763 / 100000) (1023383 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell774504704 :
    ThetaLowerSegment 774504704 774570240 (77446029634341 / 100000) (77452646848217 / 100000) := by
  exact
    packedTile32768 774504704 774570240 13 3233 27829 30 _ _ (511693 / 25000) (81871 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell774570240 :
    ThetaLowerSegment 774570240 774635776 (77452646848217 / 100000) (77459137187597 / 100000) := by
  exact
    packedTile32768 774570240 774635776 13 3171 27831 30 _ _ (102339 / 5000) (2046783 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell774635776 :
    ThetaLowerSegment 774635776 774701312 (77459137187597 / 100000) (77465641883039 / 100000) := by
  exact
    packedTile32768 774635776 774701312 13 3178 27832 30 _ _ (2046789 / 100000) (255849 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell774701312 :
    ThetaLowerSegment 774701312 774766848 (77465641883039 / 100000) (38736094793321 / 50000) := by
  exact
    packedTile32768 774701312 774766848 13 3199 27833 30 _ _ (2046797 / 100000) (5117 / 250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell774766848 :
    ThetaLowerSegment 774766848 774832384 (38736094793321 / 50000) (38739435180713 / 50000) := by
  exact
    packedTile32768 774766848 774832384 13 3264 27834 30 _ _ (1023403 / 50000) (2046809 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell774832384 :
    ThetaLowerSegment 774832384 774897920 (38739435180713 / 50000) (38742710083113 / 50000) := by
  exact
    packedTile32768 774832384 774897920 13 3200 27835 30 _ _ (1023407 / 50000) (2046817 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell774897920 :
    ThetaLowerSegment 774897920 774963456 (38742710083113 / 50000) (77491922922897 / 100000) := by
  exact
    packedTile32768 774897920 774963456 13 3177 27836 30 _ _ (2046823 / 100000) (1023413 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell774963456 :
    ThetaLowerSegment 774963456 775028992 (77491922922897 / 100000) (77498546468013 / 100000) := by
  exact
    packedTile32768 774963456 775028992 13 3236 27838 30 _ _ (2046831 / 100000) (1023417 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell775028992 :
    ThetaLowerSegment 775028992 775094528 (77498546468013 / 100000) (77505225306933 / 100000) := by
  exact
    packedTile32768 775028992 775094528 13 3263 27839 30 _ _ (51171 / 2500) (2046843 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell775094528 :
    ThetaLowerSegment 775094528 775160064 (77505225306933 / 100000) (77511881656629 / 100000) := by
  exact
    packedTile32768 775094528 775160064 13 3252 27840 30 _ _ (63964 / 3125) (2046851 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell775160064 :
    ThetaLowerSegment 775160064 775225600 (77511881656629 / 100000) (9689810858021 / 12500) := by
  exact
    packedTile32768 775160064 775225600 13 3227 27841 30 _ _ (2046857 / 100000) (102343 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell775225600 :
    ThetaLowerSegment 775225600 775291136 (9689810858021 / 12500) (19381261254907 / 25000) := by
  exact
    packedTile32768 775225600 775291136 13 3204 27842 30 _ _ (409373 / 20000) (511717 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell775291136 :
    ThetaLowerSegment 775291136 775356672 (19381261254907 / 25000) (3101266993651 / 4000) := by
  exact
    packedTile32768 775291136 775356672 13 3239 27844 30 _ _ (2046873 / 100000) (511719 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell775356672 :
    ThetaLowerSegment 775356672 775422208 (3101266993651 / 4000) (77538167550979 / 100000) := by
  exact
    packedTile32768 775356672 775422208 13 3172 27845 30 _ _ (1023441 / 50000) (409377 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell775422208 :
    ThetaLowerSegment 775422208 775487744 (77538167550979 / 100000) (77544656192279 / 100000) := by
  exact
    packedTile32768 775422208 775487744 13 3170 27846 30 _ _ (204689 / 10000) (2046893 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell775487744 :
    ThetaLowerSegment 775487744 775553280 (77544656192279 / 100000) (38775559126211 / 50000) := by
  exact
    packedTile32768 775487744 775553280 13 3157 27847 30 _ _ (2046899 / 100000) (1023451 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell775553280 :
    ThetaLowerSegment 775553280 775618816 (38775559126211 / 50000) (3102305014791 / 4000) := by
  exact
    packedTile32768 775553280 775618816 13 3179 27848 30 _ _ (2046907 / 100000) (204691 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell775618816 :
    ThetaLowerSegment 775618816 775684352 (3102305014791 / 4000) (77564159125647 / 100000) := by
  exact
    packedTile32768 775618816 775684352 13 3192 27849 30 _ _ (511729 / 25000) (2046919 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell775684352 :
    ThetaLowerSegment 775684352 775749888 (77564159125647 / 100000) (77570484120807 / 100000) := by
  exact
    packedTile32768 775684352 775749888 13 3090 27851 30 _ _ (511731 / 25000) (2046927 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell775749888 :
    ThetaLowerSegment 775749888 775815424 (77570484120807 / 100000) (3103081044747 / 4000) := by
  exact
    packedTile32768 775749888 775815424 13 3196 27852 30 _ _ (2046933 / 100000) (255867 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell775815424 :
    ThetaLowerSegment 775815424 775880960 (3103081044747 / 4000) (19395872077853 / 25000) := by
  exact
    packedTile32768 775815424 775880960 13 3157 27853 30 _ _ (2046941 / 100000) (63967 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell775880960 :
    ThetaLowerSegment 775880960 775946496 (19395872077853 / 25000) (15518014669269 / 20000) := by
  exact
    packedTile32768 775880960 775946496 13 3217 27854 30 _ _ (2046949 / 100000) (255869 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell775946496 :
    ThetaLowerSegment 775946496 776012032 (15518014669269 / 20000) (77596691161559 / 100000) := by
  exact
    packedTile32768 775946496 776012032 13 3233 27855 30 _ _ (1023479 / 50000) (2046961 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell776012032 :
    ThetaLowerSegment 776012032 776077568 (77596691161559 / 100000) (77603349941957 / 100000) := by
  exact
    packedTile32768 776012032 776077568 13 3253 27856 30 _ _ (1023483 / 50000) (2046969 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell776077568 :
    ThetaLowerSegment 776077568 776143104 (77603349941957 / 100000) (19402434637733 / 25000) := by
  exact
    packedTile32768 776077568 776143104 13 3121 27858 30 _ _ (81879 / 4000) (1023489 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell776143104 :
    ThetaLowerSegment 776143104 776208640 (19402434637733 / 25000) (7761634211809 / 10000) := by
  exact
    packedTile32768 776143104 776208640 13 3226 27859 30 _ _ (2046983 / 100000) (1023493 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell776208640 :
    ThetaLowerSegment 776208640 776274176 (7761634211809 / 10000) (38811412470877 / 50000) := by
  exact
    packedTile32768 776208640 776274176 13 3167 27860 30 _ _ (127937 / 6250) (409399 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell776274176 :
    ThetaLowerSegment 776274176 776339712 (38811412470877 / 50000) (38814607837877 / 50000) := by
  exact
    packedTile32768 776274176 776339712 13 3122 27861 30 _ _ (2047 / 100) (2047003 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell776339712 :
    ThetaLowerSegment 776339712 776405248 (38814607837877 / 50000) (77635776339599 / 100000) := by
  exact
    packedTile32768 776339712 776405248 13 3205 27862 30 _ _ (2047009 / 100000) (511753 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell776405248 :
    ThetaLowerSegment 776405248 776470784 (77635776339599 / 100000) (77642359546271 / 100000) := by
  exact
    packedTile32768 776405248 776470784 13 3216 27864 30 _ _ (2047017 / 100000) (102351 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell776470784 :
    ThetaLowerSegment 776470784 776536320 (77642359546271 / 100000) (77648918214371 / 100000) := by
  exact
    packedTile32768 776470784 776536320 13 3204 27865 30 _ _ (81881 / 4000) (511757 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell776536320 :
    ThetaLowerSegment 776536320 776601856 (77648918214371 / 100000) (77655444158763 / 100000) := by
  exact
    packedTile32768 776536320 776601856 13 3188 27866 30 _ _ (1023517 / 50000) (2047037 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell776601856 :
    ThetaLowerSegment 776601856 776667392 (77655444158763 / 100000) (77661980363869 / 100000) := by
  exact
    packedTile32768 776601856 776667392 13 3193 27867 30 _ _ (1023521 / 50000) (409409 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell776667392 :
    ThetaLowerSegment 776667392 776732928 (77661980363869 / 100000) (77668526832967 / 100000) := by
  exact
    packedTile32768 776667392 776732928 13 3198 27868 30 _ _ (2047051 / 100000) (1023527 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell776732928 :
    ThetaLowerSegment 776732928 776798464 (77668526832967 / 100000) (2427342267224 / 3125) := by
  exact
    packedTile32768 776732928 776798464 13 3139 27869 30 _ _ (2047059 / 100000) (1023531 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell776798464 :
    ThetaLowerSegment 776798464 776864000 (2427342267224 / 3125) (1942040342761 / 2500) := by
  exact
    packedTile32768 776798464 776864000 13 3254 27871 30 _ _ (511767 / 25000) (2047071 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell776864000 :
    ThetaLowerSegment 776864000 776929536 (1942040342761 / 2500) (9711027708971 / 12500) := by
  exact
    packedTile32768 776864000 776929536 13 3228 27872 30 _ _ (511769 / 25000) (2047079 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell776929536 :
    ThetaLowerSegment 776929536 776995072 (9711027708971 / 12500) (38847408689819 / 50000) := by
  exact
    packedTile32768 776929536 776995072 13 3222 27873 30 _ _ (409417 / 20000) (127943 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell776995072 :
    ThetaLowerSegment 776995072 777060608 (38847408689819 / 50000) (38850675850247 / 50000) := by
  exact
    packedTile32768 776995072 777060608 13 3192 27874 30 _ _ (2047093 / 100000) (255887 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell777060608 :
    ThetaLowerSegment 777060608 777126144 (38850675850247 / 50000) (77708010920047 / 100000) := by
  exact
    packedTile32768 777060608 777126144 13 3253 27875 30 _ _ (2047101 / 100000) (63972 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell777126144 :
    ThetaLowerSegment 777126144 777191680 (77708010920047 / 100000) (77714586237367 / 100000) := by
  exact
    packedTile32768 777126144 777191680 13 3212 27876 30 _ _ (204711 / 10000) (2047113 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell777191680 :
    ThetaLowerSegment 777191680 777257216 (77714586237367 / 100000) (15544217576827 / 20000) := by
  exact
    packedTile32768 777191680 777257216 13 3176 27878 30 _ _ (1023559 / 50000) (2047121 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell777257216 :
    ThetaLowerSegment 777257216 777322752 (15544217576827 / 20000) (77727671444567 / 100000) := by
  exact
    packedTile32768 777257216 777322752 13 3216 27879 30 _ _ (2047127 / 100000) (204713 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell777322752 :
    ThetaLowerSegment 777322752 777339136 (77727671444567 / 100000) (77729329623917 / 100000) := by
  exact
    packedTile32768 777322752 777339136 11 810 27880 30 _ _ (409427 / 20000) (1023569 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell777339136 :
    ThetaLowerSegment 777339136 777341184 (77729329623917 / 100000) (77729513866247 / 100000) := by
  exact
    packedTile32768 777339136 777341184 8 90 27880 30 _ _ (2047137 / 100000) (102357 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_745341184_777341184 :
    ThetaLowerSegment 745341184 777341184 (465816840053 / 625) (77729513866247 / 100000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell745341184 cell745406720)
                    (ThetaLowerSegment.join cell745472256 cell745537792))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell745603328 cell745668864)
                    (ThetaLowerSegment.join cell745734400 cell745799936)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell745865472 cell745931008)
                    (ThetaLowerSegment.join cell745996544 cell746062080))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell746127616 cell746193152)
                    (ThetaLowerSegment.join cell746258688 cell746324224))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell746389760 cell746455296)
                    (ThetaLowerSegment.join cell746520832 cell746586368))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell746651904 cell746717440)
                    (ThetaLowerSegment.join cell746782976 cell746848512)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell746914048 cell746979584)
                    (ThetaLowerSegment.join cell747045120 cell747110656))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell747176192 cell747241728)
                    (ThetaLowerSegment.join cell747307264 cell747372800)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell747438336 cell747503872)
                    (ThetaLowerSegment.join cell747569408 cell747634944))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell747700480 cell747766016)
                    (ThetaLowerSegment.join cell747831552 cell747897088)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell747962624 cell748028160)
                    (ThetaLowerSegment.join cell748093696 cell748159232))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell748224768 cell748290304)
                    (ThetaLowerSegment.join cell748355840 cell748421376))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell748486912 cell748552448)
                    (ThetaLowerSegment.join cell748617984 cell748683520))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell748749056 cell748814592)
                    (ThetaLowerSegment.join cell748880128 cell748945664)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell749011200 cell749076736)
                    (ThetaLowerSegment.join cell749142272 cell749207808))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell749273344 cell749338880)
                    (ThetaLowerSegment.join cell749404416 cell749469952))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell749535488 cell749601024)
                    (ThetaLowerSegment.join cell749666560 cell749732096))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell749797632 cell749863168)
                    (ThetaLowerSegment.join cell749928704 cell749994240)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell750059776 cell750125312)
                    (ThetaLowerSegment.join cell750190848 cell750256384))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell750321920 cell750387456)
                    (ThetaLowerSegment.join cell750452992 cell750518528))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell750584064 cell750649600)
                    (ThetaLowerSegment.join cell750715136 cell750780672))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell750846208 cell750911744)
                    (ThetaLowerSegment.join cell750977280 cell751042816)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell751108352 cell751173888)
                    (ThetaLowerSegment.join cell751239424 cell751304960))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell751370496 cell751436032)
                    (ThetaLowerSegment.join cell751501568 cell751567104)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell751632640 cell751698176)
                    (ThetaLowerSegment.join cell751763712 cell751829248))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell751894784 cell751960320)
                    (ThetaLowerSegment.join cell752025856 cell752091392)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell752156928 cell752222464)
                    (ThetaLowerSegment.join cell752288000 cell752353536))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell752419072 cell752484608)
                    (ThetaLowerSegment.join cell752550144 cell752615680))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell752681216 cell752746752)
                    (ThetaLowerSegment.join cell752812288 cell752877824))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell752943360 cell753008896)
                    (ThetaLowerSegment.join cell753074432 cell753139968)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell753205504 cell753271040)
                    (ThetaLowerSegment.join cell753336576 cell753402112))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell753467648 cell753533184)
                    (ThetaLowerSegment.join cell753598720 cell753664256)))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell753729792 cell753795328)
                    (ThetaLowerSegment.join cell753860864 cell753926400))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell753991936 cell754057472)
                    (ThetaLowerSegment.join cell754123008 cell754188544)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell754254080 cell754319616)
                    (ThetaLowerSegment.join cell754385152 cell754450688))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell754516224 cell754581760)
                    (ThetaLowerSegment.join cell754647296 cell754712832))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell754778368 cell754843904)
                    (ThetaLowerSegment.join cell754909440 cell754974976))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell755040512 cell755106048)
                    (ThetaLowerSegment.join cell755171584 cell755237120)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell755302656 cell755368192)
                    (ThetaLowerSegment.join cell755433728 cell755499264))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell755564800 cell755630336)
                    (ThetaLowerSegment.join cell755695872 cell755761408)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell755826944 cell755892480)
                    (ThetaLowerSegment.join cell755958016 cell756023552))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell756089088 cell756154624)
                    (ThetaLowerSegment.join cell756220160 cell756285696)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell756351232 cell756416768)
                    (ThetaLowerSegment.join cell756482304 cell756547840))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell756613376 cell756678912)
                    (ThetaLowerSegment.join cell756744448 cell756809984))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell756875520 cell756941056)
                    (ThetaLowerSegment.join cell757006592 cell757072128))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell757137664 cell757203200)
                    (ThetaLowerSegment.join cell757268736 cell757334272)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell757399808 cell757465344)
                    (ThetaLowerSegment.join cell757530880 cell757596416))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell757661952 cell757727488)
                    (ThetaLowerSegment.join cell757793024 cell757858560))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell757924096 cell757989632)
                    (ThetaLowerSegment.join cell758055168 cell758120704))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell758186240 cell758251776)
                    (ThetaLowerSegment.join cell758317312 cell758382848)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell758448384 cell758513920)
                    (ThetaLowerSegment.join cell758579456 cell758644992))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell758710528 cell758776064)
                    (ThetaLowerSegment.join cell758841600 cell758907136))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell758972672 cell759038208)
                    (ThetaLowerSegment.join cell759103744 cell759169280))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell759234816 cell759300352)
                    (ThetaLowerSegment.join cell759365888 cell759431424)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell759496960 cell759562496)
                    (ThetaLowerSegment.join cell759628032 cell759693568))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell759759104 cell759824640)
                    (ThetaLowerSegment.join cell759890176 cell759955712)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell760021248 cell760086784)
                    (ThetaLowerSegment.join cell760152320 cell760217856))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell760283392 cell760348928)
                    (ThetaLowerSegment.join cell760414464 cell760480000)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell760545536 cell760611072)
                    (ThetaLowerSegment.join cell760676608 cell760742144))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell760807680 cell760873216)
                    (ThetaLowerSegment.join cell760938752 cell761004288))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell761069824 cell761135360)
                    (ThetaLowerSegment.join cell761200896 cell761266432))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell761331968 cell761397504)
                    (ThetaLowerSegment.join cell761463040 cell761528576)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell761594112 cell761659648)
                    (ThetaLowerSegment.join cell761725184 cell761790720))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell761856256 cell761921792)
                    (ThetaLowerSegment.join cell761987328 cell762052864))))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell762118400 cell762183936)
                    (ThetaLowerSegment.join cell762249472 cell762315008))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell762380544 cell762446080)
                    (ThetaLowerSegment.join cell762511616 cell762577152)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell762642688 cell762708224)
                    (ThetaLowerSegment.join cell762773760 cell762839296))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell762904832 cell762970368)
                    (ThetaLowerSegment.join cell763035904 cell763101440))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell763166976 cell763232512)
                    (ThetaLowerSegment.join cell763298048 cell763363584))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell763429120 cell763494656)
                    (ThetaLowerSegment.join cell763560192 cell763625728)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell763691264 cell763756800)
                    (ThetaLowerSegment.join cell763822336 cell763887872))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell763953408 cell764018944)
                    (ThetaLowerSegment.join cell764084480 cell764150016)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell764215552 cell764281088)
                    (ThetaLowerSegment.join cell764346624 cell764412160))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell764477696 cell764543232)
                    (ThetaLowerSegment.join cell764608768 cell764674304)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell764739840 cell764805376)
                    (ThetaLowerSegment.join cell764870912 cell764936448))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell765001984 cell765067520)
                    (ThetaLowerSegment.join cell765133056 cell765198592))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell765264128 cell765329664)
                    (ThetaLowerSegment.join cell765395200 cell765460736))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell765526272 cell765591808)
                    (ThetaLowerSegment.join cell765657344 cell765722880)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell765788416 cell765853952)
                    (ThetaLowerSegment.join cell765919488 cell765985024))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell766050560 cell766116096)
                    (ThetaLowerSegment.join cell766181632 cell766247168))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell766312704 cell766378240)
                    (ThetaLowerSegment.join cell766443776 cell766509312))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell766574848 cell766640384)
                    (ThetaLowerSegment.join cell766705920 cell766771456)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell766836992 cell766902528)
                    (ThetaLowerSegment.join cell766968064 cell767033600))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell767099136 cell767164672)
                    (ThetaLowerSegment.join cell767230208 cell767295744))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell767361280 cell767426816)
                    (ThetaLowerSegment.join cell767492352 cell767557888))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell767623424 cell767688960)
                    (ThetaLowerSegment.join cell767754496 cell767820032)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell767885568 cell767951104)
                    (ThetaLowerSegment.join cell768016640 cell768082176))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell768147712 cell768213248)
                    (ThetaLowerSegment.join cell768278784 cell768344320)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell768409856 cell768475392)
                    (ThetaLowerSegment.join cell768540928 cell768606464))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell768672000 cell768737536)
                    (ThetaLowerSegment.join cell768803072 cell768868608)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell768934144 cell768999680)
                    (ThetaLowerSegment.join cell769065216 cell769130752))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell769196288 cell769261824)
                    (ThetaLowerSegment.join cell769327360 cell769392896))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell769458432 cell769523968)
                    (ThetaLowerSegment.join cell769589504 cell769655040))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell769720576 cell769786112)
                    (ThetaLowerSegment.join cell769851648 cell769917184)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell769982720 cell770048256)
                    (ThetaLowerSegment.join cell770113792 cell770179328))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell770244864 cell770310400)
                    (ThetaLowerSegment.join cell770375936 cell770441472)))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell770507008 cell770572544)
                    (ThetaLowerSegment.join cell770638080 cell770703616))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell770769152 cell770834688)
                    (ThetaLowerSegment.join cell770900224 cell770965760)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell771031296 cell771096832)
                    (ThetaLowerSegment.join cell771162368 cell771227904))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell771293440 cell771358976)
                    (ThetaLowerSegment.join cell771424512 cell771490048))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell771555584 cell771621120)
                    (ThetaLowerSegment.join cell771686656 cell771752192))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell771817728 cell771883264)
                    (ThetaLowerSegment.join cell771948800 cell772014336)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell772079872 cell772145408)
                    (ThetaLowerSegment.join cell772210944 cell772276480))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell772342016 cell772407552)
                    (ThetaLowerSegment.join cell772473088 cell772538624)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell772604160 cell772669696)
                    (ThetaLowerSegment.join cell772735232 cell772800768))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell772866304 cell772931840)
                    (ThetaLowerSegment.join cell772997376 cell773062912)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell773128448 cell773193984)
                    (ThetaLowerSegment.join cell773259520 cell773325056))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell773390592 cell773456128)
                    (ThetaLowerSegment.join cell773521664 cell773587200))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell773652736 cell773718272)
                    (ThetaLowerSegment.join cell773783808 cell773849344))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell773914880 cell773980416)
                    (ThetaLowerSegment.join cell774045952 cell774111488)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell774177024 cell774242560)
                    (ThetaLowerSegment.join cell774308096 cell774373632))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell774439168 cell774504704)
                    (ThetaLowerSegment.join cell774570240 cell774635776))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell774701312 cell774766848)
                    (ThetaLowerSegment.join cell774832384 cell774897920))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell774963456 cell775028992)
                    (ThetaLowerSegment.join cell775094528 cell775160064)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell775225600 cell775291136)
                    (ThetaLowerSegment.join cell775356672 cell775422208))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell775487744 cell775553280)
                    (ThetaLowerSegment.join cell775618816 cell775684352))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell775749888 cell775815424)
                    (ThetaLowerSegment.join cell775880960 cell775946496))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell776012032 cell776077568)
                    (ThetaLowerSegment.join cell776143104 cell776208640)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell776274176 cell776339712)
                    (ThetaLowerSegment.join cell776405248 cell776470784))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell776536320 cell776601856)
                    (ThetaLowerSegment.join cell776667392 cell776732928)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell776798464 cell776864000)
                  (ThetaLowerSegment.join cell776929536 cell776995072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell777060608 cell777126144)
                  (ThetaLowerSegment.join cell777191680 cell777257216)))
              (ThetaLowerSegment.join cell777322752 cell777339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
