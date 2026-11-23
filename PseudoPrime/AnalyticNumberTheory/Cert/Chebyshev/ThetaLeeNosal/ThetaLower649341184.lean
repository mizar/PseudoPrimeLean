/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis32768

/-! # Direct theta estimate up to 649341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell617341184 :
    ThetaLowerSegment 617341184 617406720 (1929110684964 / 3125) (154344824883 / 250) := by
  exact
    packedTile32768 617341184 617406720 13 3156 24846 29 _ _ (506023 / 25000) (404819 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell617406720 :
    ThetaLowerSegment 617406720 617472256 (154344824883 / 250) (385902038222 / 625) := by
  exact
    packedTile32768 617406720 617472256 13 3160 24847 29 _ _ (1012051 / 50000) (404821 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell617472256 :
    ThetaLowerSegment 617472256 617537792 (385902038222 / 625) (308753611563 / 500) := by
  exact
    packedTile32768 617472256 617537792 13 3160 24848 29 _ _ (2024113 / 100000) (506029 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell617537792 :
    ThetaLowerSegment 617537792 617603328 (308753611563 / 500) (7719645890427 / 12500) := by
  exact
    packedTile32768 617537792 617603328 13 3184 24850 29 _ _ (506031 / 25000) (2024127 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell617603328 :
    ThetaLowerSegment 617603328 617668864 (7719645890427 / 12500) (7720481857769 / 12500) := by
  exact
    packedTile32768 617603328 617668864 13 3304 24851 29 _ _ (1012067 / 50000) (2024137 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell617668864 :
    ThetaLowerSegment 617668864 617734400 (7720481857769 / 12500) (61770338198587 / 100000) := by
  exact
    packedTile32768 617668864 617734400 13 3203 24852 29 _ _ (404829 / 20000) (506037 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell617734400 :
    ThetaLowerSegment 617734400 617799936 (61770338198587 / 100000) (30888449242471 / 50000) := by
  exact
    packedTile32768 617734400 617799936 13 3241 24854 29 _ _ (404831 / 20000) (1012079 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell617799936 :
    ThetaLowerSegment 617799936 617865472 (30888449242471 / 50000) (7722935893159 / 12500) := by
  exact
    packedTile32768 617799936 617865472 13 3255 24855 29 _ _ (1012083 / 50000) (2024169 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell617865472 :
    ThetaLowerSegment 617865472 617931008 (7722935893159 / 12500) (12358000594207 / 20000) := by
  exact
    packedTile32768 617865472 617931008 13 3219 24856 29 _ _ (2024177 / 100000) (101209 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell617931008 :
    ThetaLowerSegment 617931008 617996544 (12358000594207 / 20000) (30898297874047 / 50000) := by
  exact
    packedTile32768 617931008 617996544 13 3257 24858 29 _ _ (2024187 / 100000) (202419 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell617996544 :
    ThetaLowerSegment 617996544 618062080 (30898297874047 / 50000) (772538085839 / 1250) := by
  exact
    packedTile32768 617996544 618062080 13 3187 24859 29 _ _ (1012099 / 50000) (2024201 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell618062080 :
    ThetaLowerSegment 618062080 618127616 (772538085839 / 1250) (3863099319211 / 6250) := by
  exact
    packedTile32768 618062080 618127616 13 3232 24860 29 _ _ (126513 / 6250) (2024211 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell618127616 :
    ThetaLowerSegment 618127616 618193152 (3863099319211 / 6250) (7727026543993 / 12500) := by
  exact
    packedTile32768 618127616 618193152 13 3272 24862 29 _ _ (2024219 / 100000) (1012111 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell618193152 :
    ThetaLowerSegment 618193152 618258688 (7727026543993 / 12500) (15455701823321 / 25000) := by
  exact
    packedTile32768 618193152 618258688 13 3258 24863 29 _ _ (202423 / 10000) (2024233 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell618258688 :
    ThetaLowerSegment 618258688 618324224 (15455701823321 / 25000) (15457349048621 / 25000) := by
  exact
    packedTile32768 618258688 618324224 13 3255 24864 29 _ _ (25303 / 1250) (2024243 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell618324224 :
    ThetaLowerSegment 618324224 618389760 (15457349048621 / 25000) (7729495358091 / 12500) := by
  exact
    packedTile32768 618324224 618389760 13 3244 24866 29 _ _ (2024251 / 100000) (1012127 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell618389760 :
    ThetaLowerSegment 618389760 618455296 (7729495358091 / 12500) (123685091523 / 200) := by
  exact
    packedTile32768 618389760 618455296 13 3252 24867 29 _ _ (2024261 / 100000) (253033 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell618455296 :
    ThetaLowerSegment 618455296 618520832 (123685091523 / 200) (15462312031523 / 25000) := by
  exact
    packedTile32768 618455296 618520832 13 3311 24868 29 _ _ (126517 / 6250) (80971 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell618520832 :
    ThetaLowerSegment 618520832 618586368 (15462312031523 / 25000) (1546394967647 / 2500) := by
  exact
    packedTile32768 618520832 618586368 13 3236 24870 29 _ _ (2024283 / 100000) (1012143 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell618586368 :
    ThetaLowerSegment 618586368 618651904 (1546394967647 / 2500) (30931192877651 / 50000) := by
  exact
    packedTile32768 618586368 618651904 13 3254 24871 29 _ _ (2024293 / 100000) (253037 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell618651904 :
    ThetaLowerSegment 618651904 618717440 (30931192877651 / 50000) (30934458080003 / 50000) := by
  exact
    packedTile32768 618651904 618717440 13 3226 24872 29 _ _ (126519 / 6250) (2024307 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell618717440 :
    ThetaLowerSegment 618717440 618782976 (30934458080003 / 50000) (6187542635383 / 10000) := by
  exact
    packedTile32768 618717440 618782976 13 3216 24874 29 _ _ (1012157 / 50000) (2024317 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell618782976 :
    ThetaLowerSegment 618782976 618848512 (6187542635383 / 10000) (12376378004711 / 20000) := by
  exact
    packedTile32768 618782976 618848512 13 3193 24875 29 _ _ (80973 / 4000) (253041 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell618848512 :
    ThetaLowerSegment 618848512 618914048 (12376378004711 / 20000) (12377679652759 / 20000) := by
  exact
    packedTile32768 618848512 618914048 13 3215 24876 29 _ _ (126521 / 6250) (2024339 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell618914048 :
    ThetaLowerSegment 618914048 618979584 (12377679652759 / 20000) (61895003704793 / 100000) := by
  exact
    packedTile32768 618914048 618979584 13 3263 24877 29 _ _ (1012173 / 50000) (2024349 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell618979584 :
    ThetaLowerSegment 618979584 619045120 (61895003704793 / 100000) (15475361808281 / 25000) := by
  exact
    packedTile32768 618979584 619045120 13 3183 24879 29 _ _ (2024357 / 100000) (50609 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell619045120 :
    ThetaLowerSegment 619045120 619110656 (15475361808281 / 25000) (15476997496817 / 25000) := by
  exact
    packedTile32768 619045120 619110656 13 3232 24880 29 _ _ (2024367 / 100000) (202437 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell619110656 :
    ThetaLowerSegment 619110656 619176192 (15476997496817 / 25000) (30957251205647 / 50000) := by
  exact
    packedTile32768 619110656 619176192 13 3217 24881 29 _ _ (1012189 / 50000) (2024381 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell619176192 :
    ThetaLowerSegment 619176192 619241728 (30957251205647 / 50000) (30960538813383 / 50000) := by
  exact
    packedTile32768 619176192 619241728 13 3248 24883 29 _ _ (2024389 / 100000) (253049 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell619241728 :
    ThetaLowerSegment 619241728 619307264 (30960538813383 / 50000) (61927654899117 / 100000) := by
  exact
    packedTile32768 619241728 619307264 13 3249 24884 29 _ _ (2024399 / 100000) (1012201 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell619307264 :
    ThetaLowerSegment 619307264 619372800 (61927654899117 / 100000) (61934236256027 / 100000) := by
  exact
    packedTile32768 619307264 619372800 13 3251 24885 29 _ _ (202441 / 10000) (2024413 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell619372800 :
    ThetaLowerSegment 619372800 619438336 (61934236256027 / 100000) (61940884451307 / 100000) := by
  exact
    packedTile32768 619372800 619438336 13 3284 24887 29 _ _ (101221 / 5000) (2024423 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell619438336 :
    ThetaLowerSegment 619438336 619503872 (61940884451307 / 100000) (61947455754333 / 100000) := by
  exact
    packedTile32768 619438336 619503872 13 3246 24888 29 _ _ (2024431 / 100000) (1012217 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell619503872 :
    ThetaLowerSegment 619503872 619569408 (61947455754333 / 100000) (61954027089819 / 100000) := by
  exact
    packedTile32768 619503872 619569408 13 3246 24889 29 _ _ (2024441 / 100000) (506111 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell619569408 :
    ThetaLowerSegment 619569408 619634944 (61954027089819 / 100000) (61960647047859 / 100000) := by
  exact
    packedTile32768 619569408 619634944 13 3270 24891 29 _ _ (506113 / 25000) (404891 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell619634944 :
    ThetaLowerSegment 619634944 619700480 (61960647047859 / 100000) (61967287286499 / 100000) := by
  exact
    packedTile32768 619634944 619700480 13 3280 24892 29 _ _ (2024463 / 100000) (1012233 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell619700480 :
    ThetaLowerSegment 619700480 619766016 (61967287286499 / 100000) (15493474297711 / 25000) := by
  exact
    packedTile32768 619700480 619766016 13 3265 24893 29 _ _ (2024473 / 100000) (506119 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell619766016 :
    ThetaLowerSegment 619766016 619831552 (15493474297711 / 25000) (7747557824057 / 12500) := by
  exact
    packedTile32768 619766016 619831552 13 3243 24895 29 _ _ (506121 / 25000) (2024487 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell619831552 :
    ThetaLowerSegment 619831552 619897088 (7747557824057 / 12500) (30993518062237 / 50000) := by
  exact
    packedTile32768 619831552 619897088 13 3247 24896 29 _ _ (1012247 / 50000) (2024497 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell619897088 :
    ThetaLowerSegment 619897088 619962624 (30993518062237 / 50000) (1937294672227 / 3125) := by
  exact
    packedTile32768 619897088 619962624 13 3158 24897 29 _ _ (404901 / 20000) (506127 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell619962624 :
    ThetaLowerSegment 619962624 620028160 (1937294672227 / 3125) (61999914032809 / 100000) := by
  exact
    packedTile32768 619962624 620028160 13 3203 24899 29 _ _ (404903 / 20000) (1012259 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell620028160 :
    ThetaLowerSegment 620028160 620093696 (61999914032809 / 100000) (62006528159251 / 100000) := by
  exact
    packedTile32768 620028160 620093696 13 3267 24900 29 _ _ (1012263 / 50000) (2024529 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell620093696 :
    ThetaLowerSegment 620093696 620159232 (62006528159251 / 100000) (7751633173653 / 12500) := by
  exact
    packedTile32768 620093696 620159232 13 3229 24901 29 _ _ (2024537 / 100000) (101227 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell620159232 :
    ThetaLowerSegment 620159232 620224768 (7751633173653 / 12500) (31009741601607 / 50000) := by
  exact
    packedTile32768 620159232 620224768 13 3170 24902 29 _ _ (2024547 / 100000) (40491 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell620224768 :
    ThetaLowerSegment 620224768 620290304 (31009741601607 / 50000) (31013031508357 / 50000) := by
  exact
    packedTile32768 620224768 620290304 13 3250 24904 29 _ _ (1012279 / 50000) (2024561 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell620290304 :
    ThetaLowerSegment 620290304 620355840 (31013031508357 / 50000) (6203261654333 / 10000) := by
  exact
    packedTile32768 620290304 620355840 13 3237 24905 29 _ _ (253071 / 12500) (2024571 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell620355840 :
    ThetaLowerSegment 620355840 620421376 (6203261654333 / 10000) (15509813278323 / 25000) := by
  exact
    packedTile32768 620355840 620421376 13 3278 24906 29 _ _ (2024579 / 100000) (1012291 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell620421376 :
    ThetaLowerSegment 620421376 620486912 (15509813278323 / 25000) (15511465342947 / 25000) := by
  exact
    packedTile32768 620421376 620486912 13 3264 24908 29 _ _ (2024589 / 100000) (126537 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell620486912 :
    ThetaLowerSegment 620486912 620552448 (15511465342947 / 25000) (15513122984197 / 25000) := by
  exact
    packedTile32768 620486912 620552448 13 3275 24909 29 _ _ (10123 / 500) (2024603 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell620552448 :
    ThetaLowerSegment 620552448 620617984 (15513122984197 / 25000) (15514746722219 / 25000) := by
  exact
    packedTile32768 620552448 620617984 13 3208 24910 29 _ _ (2024611 / 100000) (1012307 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell620617984 :
    ThetaLowerSegment 620617984 620683520 (15514746722219 / 25000) (31032742961143 / 50000) := by
  exact
    packedTile32768 620617984 620683520 13 3210 24912 29 _ _ (2024621 / 100000) (126539 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell620683520 :
    ThetaLowerSegment 620683520 620749056 (31032742961143 / 50000) (31036030963511 / 50000) := by
  exact
    packedTile32768 620683520 620749056 13 3248 24913 29 _ _ (253079 / 12500) (404927 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell620749056 :
    ThetaLowerSegment 620749056 620814592 (31036030963511 / 50000) (31039391869231 / 50000) := by
  exact
    packedTile32768 620749056 620814592 13 3320 24914 29 _ _ (1012321 / 50000) (404929 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell620814592 :
    ThetaLowerSegment 620814592 620880128 (31039391869231 / 50000) (31042679905703 / 50000) := by
  exact
    packedTile32768 620814592 620880128 13 3248 24916 29 _ _ (2024653 / 100000) (126541 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell620880128 :
    ThetaLowerSegment 620880128 620945664 (31042679905703 / 50000) (6209185493031 / 10000) := by
  exact
    packedTile32768 620880128 620945664 13 3208 24917 29 _ _ (2024663 / 100000) (1012333 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell620945664 :
    ThetaLowerSegment 620945664 621011200 (6209185493031 / 10000) (31049140622793 / 50000) := by
  exact
    packedTile32768 620945664 621011200 13 3174 24918 29 _ _ (1012337 / 50000) (2024677 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell621011200 :
    ThetaLowerSegment 621011200 621076736 (31049140622793 / 50000) (31052447944107 / 50000) := by
  exact
    packedTile32768 621011200 621076736 13 3267 24920 29 _ _ (506171 / 25000) (2024687 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell621076736 :
    ThetaLowerSegment 621076736 621142272 (31052447944107 / 50000) (62111275702159 / 100000) := by
  exact
    packedTile32768 621076736 621142272 13 3151 24921 29 _ _ (404939 / 20000) (1012349 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell621142272 :
    ThetaLowerSegment 621142272 621207808 (62111275702159 / 100000) (62117890416661 / 100000) := by
  exact
    packedTile32768 621142272 621207808 13 3267 24922 29 _ _ (1012353 / 50000) (2024709 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell621207808 :
    ThetaLowerSegment 621207808 621273344 (62117890416661 / 100000) (62124507188549 / 100000) := by
  exact
    packedTile32768 621207808 621273344 13 3268 24924 29 _ _ (506179 / 25000) (2024719 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell621273344 :
    ThetaLowerSegment 621273344 621338880 (62124507188549 / 100000) (7766370505369 / 12500) := by
  exact
    packedTile32768 621273344 621338880 13 3189 24925 29 _ _ (2024727 / 100000) (202473 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell621338880 :
    ThetaLowerSegment 621338880 621404416 (7766370505369 / 12500) (31068812713841 / 50000) := by
  exact
    packedTile32768 621338880 621404416 13 3290 24926 29 _ _ (2024737 / 100000) (101237 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell621404416 :
    ThetaLowerSegment 621404416 621469952 (31068812713841 / 50000) (31072056360137 / 50000) := by
  exact
    packedTile32768 621404416 621469952 13 3204 24927 29 _ _ (506187 / 25000) (2024751 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell621469952 :
    ThetaLowerSegment 621469952 621535488 (31072056360137 / 50000) (31075344567129 / 50000) := by
  exact
    packedTile32768 621469952 621535488 13 3248 24929 29 _ _ (1012379 / 50000) (2024761 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell621535488 :
    ThetaLowerSegment 621535488 621601024 (31075344567129 / 50000) (31078640891061 / 50000) := by
  exact
    packedTile32768 621535488 621601024 13 3256 24930 29 _ _ (2024769 / 100000) (506193 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell621601024 :
    ThetaLowerSegment 621601024 621666560 (31078640891061 / 50000) (62163811694397 / 100000) := by
  exact
    packedTile32768 621601024 621666560 13 3225 24931 29 _ _ (2024779 / 100000) (1012391 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell621666560 :
    ThetaLowerSegment 621666560 621732096 (62163811694397 / 100000) (62170284948027 / 100000) := by
  exact
    packedTile32768 621666560 621732096 13 3197 24933 29 _ _ (202479 / 10000) (2024793 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell621732096 :
    ThetaLowerSegment 621732096 621797632 (62170284948027 / 100000) (62176910093627 / 100000) := by
  exact
    packedTile32768 621732096 621797632 13 3272 24934 29 _ _ (2531 / 125) (2024803 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell621797632 :
    ThetaLowerSegment 621797632 621863168 (62176910093627 / 100000) (15545877238169 / 25000) := by
  exact
    packedTile32768 621797632 621863168 13 3259 24935 29 _ _ (2024811 / 100000) (1012407 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell621863168 :
    ThetaLowerSegment 621863168 621928704 (15545877238169 / 25000) (31094962806797 / 50000) := by
  exact
    packedTile32768 621863168 621928704 13 3169 24937 29 _ _ (1012411 / 50000) (80993 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell621928704 :
    ThetaLowerSegment 621928704 621994240 (31094962806797 / 50000) (6219645164713 / 10000) := by
  exact
    packedTile32768 621928704 621994240 13 3223 24938 29 _ _ (63276 / 3125) (404967 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell621994240 :
    ThetaLowerSegment 621994240 622059776 (6219645164713 / 10000) (12440620651277 / 20000) := by
  exact
    packedTile32768 621994240 622059776 13 3285 24939 29 _ _ (2024843 / 100000) (1012423 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell622059776 :
    ThetaLowerSegment 622059776 622125312 (12440620651277 / 20000) (62209667829811 / 100000) := by
  exact
    packedTile32768 622059776 622125312 13 3242 24941 29 _ _ (2024853 / 100000) (253107 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell622125312 :
    ThetaLowerSegment 622125312 622190848 (62209667829811 / 100000) (62216307358867 / 100000) := by
  exact
    packedTile32768 622125312 622190848 13 3279 24942 29 _ _ (63277 / 3125) (2024867 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell622190848 :
    ThetaLowerSegment 622190848 622256384 (62216307358867 / 100000) (2488910830267 / 4000) := by
  exact
    packedTile32768 622190848 622256384 13 3192 24943 29 _ _ (1012437 / 50000) (2024877 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell622256384 :
    ThetaLowerSegment 622256384 622321920 (2488910830267 / 4000) (12445849267781 / 20000) := by
  exact
    packedTile32768 622256384 622321920 13 3198 24945 29 _ _ (404977 / 20000) (253111 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell622321920 :
    ThetaLowerSegment 622321920 622387456 (12445849267781 / 20000) (6223579687423 / 10000) := by
  exact
    packedTile32768 622321920 622387456 13 3235 24946 29 _ _ (404979 / 20000) (1012449 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell622387456 :
    ThetaLowerSegment 622387456 622452992 (6223579687423 / 10000) (31121203083707 / 50000) := by
  exact
    packedTile32768 622387456 622452992 13 3264 24947 29 _ _ (1012453 / 50000) (2024909 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell622452992 :
    ThetaLowerSegment 622452992 622518528 (31121203083707 / 50000) (31124455098803 / 50000) := by
  exact
    packedTile32768 622452992 622518528 13 3212 24949 29 _ _ (506229 / 25000) (2024919 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell622518528 :
    ThetaLowerSegment 622518528 622584064 (31124455098803 / 50000) (2490215355569 / 4000) := by
  exact
    packedTile32768 622518528 622584064 13 3197 24950 29 _ _ (2024927 / 100000) (202493 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell622584064 :
    ThetaLowerSegment 622584064 622649600 (2490215355569 / 4000) (7782742832521 / 12500) := by
  exact
    packedTile32768 622584064 622649600 13 3239 24951 29 _ _ (2024937 / 100000) (101247 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell622649600 :
    ThetaLowerSegment 622649600 622715136 (7782742832521 / 12500) (15567143591217 / 25000) := by
  exact
    packedTile32768 622649600 622715136 13 3275 24952 29 _ _ (506237 / 25000) (2024951 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell622715136 :
    ThetaLowerSegment 622715136 622780672 (15567143591217 / 25000) (31137487628553 / 50000) := by
  exact
    packedTile32768 622715136 622780672 13 3161 24954 29 _ _ (1012479 / 50000) (2024961 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell622780672 :
    ThetaLowerSegment 622780672 622846208 (31137487628553 / 50000) (31140768078333 / 50000) := by
  exact
    packedTile32768 622780672 622846208 13 3240 24955 29 _ _ (2024969 / 100000) (506243 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell622846208 :
    ThetaLowerSegment 622846208 622911744 (31140768078333 / 50000) (31144054620873 / 50000) := by
  exact
    packedTile32768 622846208 622911744 13 3246 24956 29 _ _ (101249 / 5000) (2024983 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell622911744 :
    ThetaLowerSegment 622911744 622977280 (31144054620873 / 50000) (7786816816877 / 12500) := by
  exact
    packedTile32768 622911744 622977280 13 3173 24958 29 _ _ (202499 / 10000) (2024993 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell622977280 :
    ThetaLowerSegment 622977280 623042816 (7786816816877 / 12500) (62301223113319 / 100000) := by
  exact
    packedTile32768 622977280 623042816 13 3303 24959 29 _ _ (2025001 / 100000) (506251 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell623042816 :
    ThetaLowerSegment 623042816 623108352 (62301223113319 / 100000) (62307763898849 / 100000) := by
  exact
    packedTile32768 623042816 623108352 13 3230 24960 29 _ _ (2025011 / 100000) (1012507 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell623108352 :
    ThetaLowerSegment 623108352 623173888 (62307763898849 / 100000) (62314308769953 / 100000) := by
  exact
    packedTile32768 623108352 623173888 13 3232 24962 29 _ _ (1012511 / 50000) (81001 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell623173888 :
    ThetaLowerSegment 623173888 623239424 (62314308769953 / 100000) (62320884048857 / 100000) := by
  exact
    packedTile32768 623173888 623239424 13 3247 24963 29 _ _ (253129 / 12500) (405007 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell623239424 :
    ThetaLowerSegment 623239424 623304960 (62320884048857 / 100000) (3895461907001 / 6250) := by
  exact
    packedTile32768 623239424 623304960 13 3213 24964 29 _ _ (2025043 / 100000) (1012523 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell623304960 :
    ThetaLowerSegment 623304960 623370496 (3895461907001 / 6250) (31167022418087 / 50000) := by
  exact
    packedTile32768 623304960 623370496 13 3286 24966 29 _ _ (2025053 / 100000) (63283 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell623370496 :
    ThetaLowerSegment 623370496 623436032 (31167022418087 / 50000) (31170309096959 / 50000) := by
  exact
    packedTile32768 623370496 623436032 13 3246 24967 29 _ _ (253133 / 12500) (2025067 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell623436032 :
    ThetaLowerSegment 623436032 623501568 (31170309096959 / 50000) (31173581616543 / 50000) := by
  exact
    packedTile32768 623436032 623501568 13 3232 24968 29 _ _ (1012537 / 50000) (2025077 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell623501568 :
    ThetaLowerSegment 623501568 623567104 (31173581616543 / 50000) (31176894655603 / 50000) := by
  exact
    packedTile32768 623501568 623567104 13 3272 24970 29 _ _ (405017 / 20000) (63284 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell623567104 :
    ThetaLowerSegment 623567104 623632640 (31176894655603 / 50000) (7795037245817 / 12500) := by
  exact
    packedTile32768 623567104 623632640 13 3214 24971 29 _ _ (405019 / 20000) (1012549 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell623632640 :
    ThetaLowerSegment 623632640 623698176 (7795037245817 / 12500) (15591697614093 / 25000) := by
  exact
    packedTile32768 623632640 623698176 13 3206 24972 29 _ _ (1012553 / 50000) (2025109 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell623698176 :
    ThetaLowerSegment 623698176 623763712 (15591697614093 / 25000) (7796657587749 / 12500) := by
  exact
    packedTile32768 623698176 623763712 13 3195 24973 29 _ _ (506279 / 25000) (2025119 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell623763712 :
    ThetaLowerSegment 623763712 623829248 (7796657587749 / 12500) (7797487889819 / 12500) := by
  exact
    packedTile32768 623763712 623829248 13 3280 24975 29 _ _ (2025127 / 100000) (202513 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell623829248 :
    ThetaLowerSegment 623829248 623894784 (7797487889819 / 12500) (1247725808013 / 2000) := by
  exact
    packedTile32768 623829248 623894784 13 3154 24976 29 _ _ (2025137 / 100000) (101257 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell623894784 :
    ThetaLowerSegment 623894784 623960320 (1247725808013 / 2000) (6239296326331 / 10000) := by
  exact
    packedTile32768 623894784 623960320 13 3295 24977 29 _ _ (506287 / 25000) (2025151 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell623960320 :
    ThetaLowerSegment 623960320 624025856 (6239296326331 / 10000) (31199754286983 / 50000) := by
  exact
    packedTile32768 623960320 624025856 13 3232 24979 29 _ _ (1012579 / 50000) (2025161 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell624025856 :
    ThetaLowerSegment 624025856 624091392 (31199754286983 / 50000) (12481226580353 / 20000) := by
  exact
    packedTile32768 624025856 624091392 13 3271 24980 29 _ _ (2025169 / 100000) (506293 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell624091392 :
    ThetaLowerSegment 624091392 624156928 (12481226580353 / 20000) (62412722834231 / 100000) := by
  exact
    packedTile32768 624091392 624156928 13 3254 24981 29 _ _ (2025179 / 100000) (1012591 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell624156928 :
    ThetaLowerSegment 624156928 624222464 (62412722834231 / 100000) (62419314827681 / 100000) := by
  exact
    packedTile32768 624156928 624222464 13 3255 24983 29 _ _ (202519 / 10000) (2025193 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell624222464 :
    ThetaLowerSegment 624222464 624288000 (62419314827681 / 100000) (62425951408081 / 100000) := by
  exact
    packedTile32768 624222464 624288000 13 3277 24984 29 _ _ (5063 / 250) (2025203 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell624288000 :
    ThetaLowerSegment 624288000 624353536 (62425951408081 / 100000) (62432504990877 / 100000) := by
  exact
    packedTile32768 624288000 624353536 13 3236 24985 29 _ _ (2025211 / 100000) (1012607 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell624353536 :
    ThetaLowerSegment 624353536 624419072 (62432504990877 / 100000) (62439054555591 / 100000) := by
  exact
    packedTile32768 624353536 624419072 13 3234 24987 29 _ _ (2025221 / 100000) (253153 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell624419072 :
    ThetaLowerSegment 624419072 624484608 (62439054555591 / 100000) (62445563651239 / 100000) := by
  exact
    packedTile32768 624419072 624484608 13 3214 24988 29 _ _ (126577 / 6250) (405047 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell624484608 :
    ThetaLowerSegment 624484608 624550144 (62445563651239 / 100000) (62452200369273 / 100000) := by
  exact
    packedTile32768 624484608 624550144 13 3277 24989 29 _ _ (1012621 / 50000) (405049 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell624550144 :
    ThetaLowerSegment 624550144 624615680 (62452200369273 / 100000) (15614673838911 / 25000) := by
  exact
    packedTile32768 624550144 624615680 13 3207 24991 29 _ _ (2025253 / 100000) (253157 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell624615680 :
    ThetaLowerSegment 624615680 624681216 (15614673838911 / 25000) (62465182273033 / 100000) := by
  exact
    packedTile32768 624615680 624681216 13 3203 24992 29 _ _ (2025263 / 100000) (1012633 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell624681216 :
    ThetaLowerSegment 624681216 624746752 (62465182273033 / 100000) (62471766438807 / 100000) := by
  exact
    packedTile32768 624681216 624746752 13 3251 24993 29 _ _ (1012637 / 50000) (2025277 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell624746752 :
    ThetaLowerSegment 624746752 624812288 (62471766438807 / 100000) (62478435699019 / 100000) := by
  exact
    packedTile32768 624746752 624812288 13 3293 24994 29 _ _ (506321 / 25000) (2025287 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell624812288 :
    ThetaLowerSegment 624812288 624877824 (62478435699019 / 100000) (62484961199509 / 100000) := by
  exact
    packedTile32768 624812288 624877824 13 3222 24996 29 _ _ (405059 / 20000) (1012649 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell624877824 :
    ThetaLowerSegment 624877824 624943360 (62484961199509 / 100000) (62491620402349 / 100000) := by
  exact
    packedTile32768 624877824 624943360 13 3288 24997 29 _ _ (405061 / 20000) (506327 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell624943360 :
    ThetaLowerSegment 624943360 625008896 (62491620402349 / 100000) (62498125717341 / 100000) := by
  exact
    packedTile32768 624943360 625008896 13 3212 24998 29 _ _ (506329 / 25000) (2025319 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell625008896 :
    ThetaLowerSegment 625008896 625074432 (62498125717341 / 100000) (62504649292387 / 100000) := by
  exact
    packedTile32768 625008896 625074432 13 3221 25000 29 _ _ (1012663 / 50000) (2025329 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell625074432 :
    ThetaLowerSegment 625074432 625139968 (62504649292387 / 100000) (31255572274073 / 50000) := by
  exact
    packedTile32768 625074432 625139968 13 3207 25001 29 _ _ (2025337 / 100000) (101267 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell625139968 :
    ThetaLowerSegment 625139968 625205504 (31255572274073 / 50000) (3907352869501 / 6250) := by
  exact
    packedTile32768 625139968 625205504 13 3210 25002 29 _ _ (2025347 / 100000) (40507 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell625205504 :
    ThetaLowerSegment 625205504 625271040 (3907352869501 / 6250) (3126208175703 / 5000) := by
  exact
    packedTile32768 625205504 625271040 13 3218 25004 29 _ _ (1012679 / 50000) (2025361 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell625271040 :
    ThetaLowerSegment 625271040 625336576 (3126208175703 / 5000) (15632685983673 / 25000) := by
  exact
    packedTile32768 625271040 625336576 13 3249 25005 29 _ _ (253171 / 12500) (2025371 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell625336576 :
    ThetaLowerSegment 625336576 625402112 (15632685983673 / 25000) (1954285500963 / 3125) := by
  exact
    packedTile32768 625336576 625402112 13 3156 25006 29 _ _ (2025379 / 100000) (1012691 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell625402112 :
    ThetaLowerSegment 625402112 625467648 (1954285500963 / 3125) (31271867374089 / 50000) := by
  exact
    packedTile32768 625402112 625467648 13 3258 25008 29 _ _ (2025389 / 100000) (126587 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell625467648 :
    ThetaLowerSegment 625467648 625533184 (31271867374089 / 50000) (31275167763389 / 50000) := by
  exact
    packedTile32768 625467648 625533184 13 3259 25009 29 _ _ (10127 / 500) (2025403 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell625533184 :
    ThetaLowerSegment 625533184 625598720 (31275167763389 / 50000) (15639220919327 / 25000) := by
  exact
    packedTile32768 625533184 625598720 13 3233 25010 29 _ _ (202541 / 10000) (2025413 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell625598720 :
    ThetaLowerSegment 625598720 625664256 (15639220919327 / 25000) (15640876700177 / 25000) := by
  exact
    packedTile32768 625598720 625664256 13 3270 25011 29 _ _ (101271 / 5000) (2025423 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell625664256 :
    ThetaLowerSegment 625664256 625729792 (15640876700177 / 25000) (62570075273441 / 100000) := by
  exact
    packedTile32768 625664256 625729792 13 3243 25013 29 _ _ (2025431 / 100000) (1012717 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell625729792 :
    ThetaLowerSegment 625729792 625795328 (62570075273441 / 100000) (62576633651399 / 100000) := by
  exact
    packedTile32768 625729792 625795328 13 3238 25014 29 _ _ (2025441 / 100000) (506361 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell625795328 :
    ThetaLowerSegment 625795328 625860864 (62576633651399 / 100000) (12516612082119 / 20000) := by
  exact
    packedTile32768 625795328 625860864 13 3173 25015 29 _ _ (506363 / 25000) (405091 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell625860864 :
    ThetaLowerSegment 625860864 625926400 (12516612082119 / 20000) (62589570245463 / 100000) := by
  exact
    packedTile32768 625860864 625926400 13 3214 25017 29 _ _ (1012731 / 50000) (405093 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell625926400 :
    ThetaLowerSegment 625926400 625991936 (62589570245463 / 100000) (15649035726337 / 25000) := by
  exact
    packedTile32768 625926400 625991936 13 3245 25018 29 _ _ (2025473 / 100000) (506369 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell625991936 :
    ThetaLowerSegment 625991936 626057472 (15649035726337 / 25000) (31301354760617 / 50000) := by
  exact
    packedTile32768 625991936 626057472 13 3242 25019 29 _ _ (2025483 / 100000) (1012743 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell626057472 :
    ThetaLowerSegment 626057472 626123008 (31301354760617 / 50000) (31304593525523 / 50000) := by
  exact
    packedTile32768 626057472 626123008 13 3198 25021 29 _ _ (1012747 / 50000) (2025497 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell626123008 :
    ThetaLowerSegment 626123008 626188544 (31304593525523 / 50000) (31307882944019 / 50000) := by
  exact
    packedTile32768 626123008 626188544 13 3248 25022 29 _ _ (63297 / 3125) (2025507 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell626188544 :
    ThetaLowerSegment 626188544 626254080 (31307882944019 / 50000) (62622265765673 / 100000) := by
  exact
    packedTile32768 626188544 626254080 13 3209 25023 29 _ _ (405103 / 20000) (1012759 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell626254080 :
    ThetaLowerSegment 626254080 626319616 (62622265765673 / 100000) (62628828466673 / 100000) := by
  exact
    packedTile32768 626254080 626319616 13 3240 25025 29 _ _ (81021 / 4000) (253191 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell626319616 :
    ThetaLowerSegment 626319616 626385152 (62628828466673 / 100000) (62635330437233 / 100000) := by
  exact
    packedTile32768 626319616 626385152 13 3210 25026 29 _ _ (63298 / 3125) (2025539 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell626385152 :
    ThetaLowerSegment 626385152 626450688 (62635330437233 / 100000) (62641919538371 / 100000) := by
  exact
    packedTile32768 626385152 626450688 13 3253 25027 29 _ _ (1012773 / 50000) (2025549 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell626450688 :
    ThetaLowerSegment 626450688 626516224 (62641919538371 / 100000) (7831070673861 / 12500) := by
  exact
    packedTile32768 626450688 626516224 13 3281 25028 29 _ _ (2025557 / 100000) (50639 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell626516224 :
    ThetaLowerSegment 626516224 626581760 (7831070673861 / 12500) (1253104428081 / 2000) := by
  exact
    packedTile32768 626516224 626581760 13 3286 25030 29 _ _ (2025567 / 100000) (202557 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell626581760 :
    ThetaLowerSegment 626581760 626647296 (1253104428081 / 2000) (31330904290227 / 50000) := by
  exact
    packedTile32768 626581760 626647296 13 3252 25031 29 _ _ (2025577 / 100000) (101279 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell626647296 :
    ThetaLowerSegment 626647296 626712832 (31330904290227 / 50000) (31334210049843 / 50000) := by
  exact
    packedTile32768 626647296 626712832 13 3264 25032 29 _ _ (506397 / 25000) (2025591 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell626712832 :
    ThetaLowerSegment 626712832 626778368 (31334210049843 / 50000) (15668715881731 / 25000) := by
  exact
    packedTile32768 626712832 626778368 13 3181 25034 29 _ _ (1012799 / 50000) (2025601 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell626778368 :
    ThetaLowerSegment 626778368 626843904 (15668715881731 / 25000) (12536297048549 / 20000) := by
  exact
    packedTile32768 626778368 626843904 13 3269 25035 29 _ _ (2025609 / 100000) (506403 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell626843904 :
    ThetaLowerSegment 626843904 626909440 (12536297048549 / 20000) (62688036094591 / 100000) := by
  exact
    packedTile32768 626843904 626909440 13 3234 25036 29 _ _ (2025619 / 100000) (1012811 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell626909440 :
    ThetaLowerSegment 626909440 626974976 (62688036094591 / 100000) (62694524187481 / 100000) := by
  exact
    packedTile32768 626909440 626974976 13 3203 25038 29 _ _ (202563 / 10000) (2025633 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell626974976 :
    ThetaLowerSegment 626974976 627040512 (62694524187481 / 100000) (62701073081601 / 100000) := by
  exact
    packedTile32768 626974976 627040512 13 3233 25039 29 _ _ (50641 / 2500) (2025643 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell627040512 :
    ThetaLowerSegment 627040512 627106048 (62701073081601 / 100000) (12541528858689 / 20000) := by
  exact
    packedTile32768 627040512 627106048 13 3244 25040 29 _ _ (2025651 / 100000) (1012827 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell627106048 :
    ThetaLowerSegment 627106048 627171584 (12541528858689 / 20000) (2508567487139 / 4000) := by
  exact
    packedTile32768 627106048 627171584 13 3230 25042 29 _ _ (2025661 / 100000) (63302 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell627171584 :
    ThetaLowerSegment 627171584 627237120 (2508567487139 / 4000) (12544156148167 / 20000) := by
  exact
    packedTile32768 627171584 627237120 13 3255 25043 29 _ _ (253209 / 12500) (81027 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell627237120 :
    ThetaLowerSegment 627237120 627302656 (12544156148167 / 20000) (62727372310063 / 100000) := by
  exact
    packedTile32768 627237120 627302656 13 3254 25044 29 _ _ (1012841 / 50000) (405137 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell627302656 :
    ThetaLowerSegment 627302656 627368192 (62727372310063 / 100000) (62733984168751 / 100000) := by
  exact
    packedTile32768 627302656 627368192 13 3264 25046 29 _ _ (506423 / 25000) (405139 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell627368192 :
    ThetaLowerSegment 627368192 627433728 (62733984168751 / 100000) (62740677091463 / 100000) := by
  exact
    packedTile32768 627368192 627433728 13 3304 25047 29 _ _ (2025703 / 100000) (1012853 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell627433728 :
    ThetaLowerSegment 627433728 627499264 (62740677091463 / 100000) (31373566519397 / 50000) := by
  exact
    packedTile32768 627433728 627499264 13 3187 25048 29 _ _ (2025713 / 100000) (506429 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell627499264 :
    ThetaLowerSegment 627499264 627564800 (31373566519397 / 50000) (31376912002583 / 50000) := by
  exact
    packedTile32768 627499264 627564800 13 3303 25049 29 _ _ (506431 / 25000) (2025727 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell627564800 :
    ThetaLowerSegment 627564800 627630336 (31376912002583 / 50000) (31380193691663 / 50000) := by
  exact
    packedTile32768 627564800 627630336 13 3240 25051 29 _ _ (1012867 / 50000) (2025737 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell627630336 :
    ThetaLowerSegment 627630336 627695872 (31380193691663 / 50000) (62767001440751 / 100000) := by
  exact
    packedTile32768 627630336 627695872 13 3265 25052 29 _ _ (405149 / 20000) (506437 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell627695872 :
    ThetaLowerSegment 627695872 627761408 (62767001440751 / 100000) (62773605402051 / 100000) := by
  exact
    packedTile32768 627695872 627761408 13 3260 25053 29 _ _ (405151 / 20000) (1012879 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell627761408 :
    ThetaLowerSegment 627761408 627826944 (62773605402051 / 100000) (62780164832359 / 100000) := by
  exact
    packedTile32768 627761408 627826944 13 3238 25055 29 _ _ (1012883 / 50000) (2025769 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell627826944 :
    ThetaLowerSegment 627826944 627892480 (62780164832359 / 100000) (62786704037287 / 100000) := by
  exact
    packedTile32768 627826944 627892480 13 3228 25056 29 _ _ (126611 / 6250) (2025779 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell627892480 :
    ThetaLowerSegment 627892480 627958016 (62786704037287 / 100000) (2511730136137 / 4000) := by
  exact
    packedTile32768 627892480 627958016 13 3233 25057 29 _ _ (1012893 / 50000) (2025789 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell627958016 :
    ThetaLowerSegment 627958016 628023552 (2511730136137 / 4000) (62799934481931 / 100000) := by
  exact
    packedTile32768 627958016 628023552 13 3298 25059 29 _ _ (2025797 / 100000) (10129 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell628023552 :
    ThetaLowerSegment 628023552 628089088 (62799934481931 / 100000) (6280649201919 / 10000) := by
  exact
    packedTile32768 628023552 628089088 13 3237 25060 29 _ _ (2025807 / 100000) (202581 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell628089088 :
    ThetaLowerSegment 628089088 628154624 (6280649201919 / 10000) (6281299489497 / 10000) := by
  exact
    packedTile32768 628089088 628154624 13 3210 25061 29 _ _ (1012909 / 50000) (2025821 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell628154624 :
    ThetaLowerSegment 628154624 628220160 (6281299489497 / 10000) (31409772198447 / 50000) := by
  exact
    packedTile32768 628154624 628220160 13 3233 25063 29 _ _ (506457 / 25000) (2025831 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell628220160 :
    ThetaLowerSegment 628220160 628285696 (31409772198447 / 50000) (785325693043 / 1250) := by
  exact
    packedTile32768 628220160 628285696 13 3214 25064 29 _ _ (2025839 / 100000) (1012921 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell628285696 :
    ThetaLowerSegment 628285696 628351232 (785325693043 / 1250) (1963517830432 / 3125) := by
  exact
    packedTile32768 628285696 628351232 13 3216 25065 29 _ _ (2025849 / 100000) (506463 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell628351232 :
    ThetaLowerSegment 628351232 628416768 (1963517830432 / 3125) (3927442858523 / 6250) := by
  exact
    packedTile32768 628351232 628416768 13 3216 25066 29 _ _ (2025859 / 100000) (1012931 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell628416768 :
    ThetaLowerSegment 628416768 628482304 (3927442858523 / 6250) (31422819712909 / 50000) := by
  exact
    packedTile32768 628416768 628482304 13 3235 25068 29 _ _ (202587 / 10000) (2025873 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell628482304 :
    ThetaLowerSegment 628482304 628547840 (31422819712909 / 50000) (31426071250309 / 50000) := by
  exact
    packedTile32768 628482304 628547840 13 3210 25069 29 _ _ (50647 / 2500) (2025883 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell628547840 :
    ThetaLowerSegment 628547840 628613376 (31426071250309 / 50000) (7857346908469 / 12500) := by
  exact
    packedTile32768 628547840 628613376 13 3274 25070 29 _ _ (2025891 / 100000) (1012947 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell628613376 :
    ThetaLowerSegment 628613376 628678912 (7857346908469 / 12500) (31432675671199 / 50000) := by
  exact
    packedTile32768 628613376 628678912 13 3246 25072 29 _ _ (2025901 / 100000) (126619 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell628678912 :
    ThetaLowerSegment 628678912 628744448 (31432675671199 / 50000) (6287195784143 / 10000) := by
  exact
    packedTile32768 628678912 628744448 13 3261 25073 29 _ _ (253239 / 12500) (405183 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell628744448 :
    ThetaLowerSegment 628744448 628809984 (6287195784143 / 10000) (6287860286559 / 10000) := by
  exact
    packedTile32768 628744448 628809984 13 3280 25074 29 _ _ (1012961 / 50000) (81037 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell628809984 :
    ThetaLowerSegment 628809984 628875520 (6287860286559 / 10000) (31442530768403 / 50000) := by
  exact
    packedTile32768 628809984 628875520 13 3188 25076 29 _ _ (506483 / 25000) (405187 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell628875520 :
    ThetaLowerSegment 628875520 628941056 (31442530768403 / 50000) (31445776329089 / 50000) := by
  exact
    packedTile32768 628875520 628941056 13 3204 25077 29 _ _ (2025943 / 100000) (1012973 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell628941056 :
    ThetaLowerSegment 628941056 629006592 (31445776329089 / 50000) (62898126875663 / 100000) := by
  exact
    packedTile32768 628941056 629006592 13 3245 25078 29 _ _ (2025953 / 100000) (506489 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell629006592 :
    ThetaLowerSegment 629006592 629072128 (62898126875663 / 100000) (62904794323187 / 100000) := by
  exact
    packedTile32768 629006592 629072128 13 3291 25080 29 _ _ (506491 / 25000) (2025967 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell629072128 :
    ThetaLowerSegment 629072128 629137664 (62904794323187 / 100000) (62911305803623 / 100000) := by
  exact
    packedTile32768 629072128 629137664 13 3214 25081 29 _ _ (1012987 / 50000) (2025977 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell629137664 :
    ThetaLowerSegment 629137664 629203200 (62911305803623 / 100000) (62917906462753 / 100000) := by
  exact
    packedTile32768 629137664 629203200 13 3258 25082 29 _ _ (405197 / 20000) (506497 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell629203200 :
    ThetaLowerSegment 629203200 629268736 (62917906462753 / 100000) (15731085762217 / 25000) := by
  exact
    packedTile32768 629203200 629268736 13 3177 25083 29 _ _ (405199 / 20000) (1012999 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell629268736 :
    ThetaLowerSegment 629268736 629334272 (15731085762217 / 25000) (62930957955193 / 100000) := by
  exact
    packedTile32768 629268736 629334272 13 3265 25085 29 _ _ (405201 / 20000) (253251 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell629334272 :
    ThetaLowerSegment 629334272 629399808 (62930957955193 / 100000) (12587497155749 / 20000) := by
  exact
    packedTile32768 629334272 629399808 13 3222 25086 29 _ _ (63313 / 3125) (2026019 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell629399808 :
    ThetaLowerSegment 629399808 629465344 (12587497155749 / 20000) (62944066311193 / 100000) := by
  exact
    packedTile32768 629399808 629465344 13 3248 25087 29 _ _ (1013013 / 50000) (2026029 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell629465344 :
    ThetaLowerSegment 629465344 629530880 (62944066311193 / 100000) (7868827567611 / 12500) := by
  exact
    packedTile32768 629465344 629530880 13 3235 25089 29 _ _ (2026037 / 100000) (50651 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell629530880 :
    ThetaLowerSegment 629530880 629596416 (7868827567611 / 12500) (31478614753101 / 50000) := by
  exact
    packedTile32768 629530880 629596416 13 3262 25090 29 _ _ (2026047 / 100000) (40521 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell629596416 :
    ThetaLowerSegment 629596416 629661952 (31478614753101 / 50000) (15740921130951 / 25000) := by
  exact
    packedTile32768 629596416 629661952 13 3186 25091 29 _ _ (2026057 / 100000) (101303 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell629661952 :
    ThetaLowerSegment 629661952 629727488 (15740921130951 / 25000) (1967816038674 / 3125) := by
  exact
    packedTile32768 629661952 629727488 13 3173 25093 29 _ _ (506517 / 25000) (2026071 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell629727488 :
    ThetaLowerSegment 629727488 629793024 (1967816038674 / 3125) (31488309487013 / 50000) := by
  exact
    packedTile32768 629727488 629793024 13 3211 25094 29 _ _ (1013039 / 50000) (2026081 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell629793024 :
    ThetaLowerSegment 629793024 629858560 (31488309487013 / 50000) (62983189580653 / 100000) := by
  exact
    packedTile32768 629793024 629858560 13 3243 25095 29 _ _ (2026089 / 100000) (506523 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell629858560 :
    ThetaLowerSegment 629858560 629924096 (62983189580653 / 100000) (62989794663393 / 100000) := by
  exact
    packedTile32768 629858560 629924096 13 3260 25096 29 _ _ (2026099 / 100000) (1013051 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell629924096 :
    ThetaLowerSegment 629924096 629989632 (62989794663393 / 100000) (62996310629937 / 100000) := by
  exact
    packedTile32768 629924096 629989632 13 3216 25098 29 _ _ (2026109 / 100000) (63316 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell629989632 :
    ThetaLowerSegment 629989632 630055168 (62996310629937 / 100000) (63002891467697 / 100000) := by
  exact
    packedTile32768 629989632 630055168 13 3248 25099 29 _ _ (50653 / 2500) (2026123 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell630055168 :
    ThetaLowerSegment 630055168 630120704 (63002891467697 / 100000) (63009486520847 / 100000) := by
  exact
    packedTile32768 630055168 630120704 13 3255 25100 29 _ _ (202613 / 10000) (2026133 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell630120704 :
    ThetaLowerSegment 630120704 630186240 (63009486520847 / 100000) (63016071479097 / 100000) := by
  exact
    packedTile32768 630120704 630186240 13 3250 25102 29 _ _ (2026141 / 100000) (63317 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell630186240 :
    ThetaLowerSegment 630186240 630251776 (63016071479097 / 100000) (6302264228679 / 10000) := by
  exact
    packedTile32768 630186240 630251776 13 3243 25103 29 _ _ (2026151 / 100000) (1013077 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell630251776 :
    ThetaLowerSegment 630251776 630317312 (6302264228679 / 10000) (63029265807099 / 100000) := by
  exact
    packedTile32768 630251776 630317312 13 3269 25104 29 _ _ (2026161 / 100000) (506541 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell630317312 :
    ThetaLowerSegment 630317312 630382848 (63029265807099 / 100000) (63035881258679 / 100000) := by
  exact
    packedTile32768 630317312 630382848 13 3265 25106 29 _ _ (506543 / 25000) (81047 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell630382848 :
    ThetaLowerSegment 630382848 630448384 (63035881258679 / 100000) (63042456219269 / 100000) := by
  exact
    packedTile32768 630382848 630448384 13 3245 25107 29 _ _ (1013091 / 50000) (405237 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell630448384 :
    ThetaLowerSegment 630448384 630513920 (63042456219269 / 100000) (2521956953093 / 4000) := by
  exact
    packedTile32768 630448384 630513920 13 3192 25108 29 _ _ (2026193 / 100000) (506549 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell630513920 :
    ThetaLowerSegment 630513920 630579456 (2521956953093 / 4000) (12611085587791 / 20000) := by
  exact
    packedTile32768 630513920 630579456 13 3210 25110 29 _ _ (2026203 / 100000) (1013103 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell630579456 :
    ThetaLowerSegment 630579456 630644992 (12611085587791 / 20000) (15765472383053 / 25000) := by
  exact
    packedTile32768 630579456 630644992 13 3189 25111 29 _ _ (2026213 / 100000) (253277 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell630644992 :
    ThetaLowerSegment 630644992 630710528 (15765472383053 / 25000) (15767095388477 / 25000) := by
  exact
    packedTile32768 630644992 630710528 13 3204 25112 29 _ _ (126639 / 6250) (2026227 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell630710528 :
    ThetaLowerSegment 630710528 630776064 (15767095388477 / 25000) (31537500630193 / 50000) := by
  exact
    packedTile32768 630710528 630776064 13 3267 25113 29 _ _ (1013117 / 50000) (2026237 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell630776064 :
    ThetaLowerSegment 630776064 630841600 (31537500630193 / 50000) (63081462955691 / 100000) := by
  exact
    packedTile32768 630776064 630841600 13 3189 25115 29 _ _ (405249 / 20000) (253281 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell630841600 :
    ThetaLowerSegment 630841600 630907136 (63081462955691 / 100000) (63087963181731 / 100000) := by
  exact
    packedTile32768 630841600 630907136 13 3208 25116 29 _ _ (405251 / 20000) (1013129 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell630907136 :
    ThetaLowerSegment 630907136 630972672 (63087963181731 / 100000) (63094576910691 / 100000) := by
  exact
    packedTile32768 630907136 630972672 13 3264 25117 29 _ _ (405253 / 20000) (506567 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell630972672 :
    ThetaLowerSegment 630972672 631038208 (63094576910691 / 100000) (63100961706367 / 100000) := by
  exact
    packedTile32768 630972672 631038208 13 3151 25119 29 _ _ (506569 / 25000) (2026279 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell631038208 :
    ThetaLowerSegment 631038208 631103744 (63100961706367 / 100000) (63107409348419 / 100000) := by
  exact
    packedTile32768 631038208 631103744 13 3182 25120 29 _ _ (1013143 / 50000) (2026289 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell631103744 :
    ThetaLowerSegment 631103744 631169280 (63107409348419 / 100000) (31557034893329 / 50000) := by
  exact
    packedTile32768 631103744 631169280 13 3287 25121 29 _ _ (2026297 / 100000) (20263 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell631169280 :
    ThetaLowerSegment 631169280 631234816 (31557034893329 / 50000) (63120782941749 / 100000) := by
  exact
    packedTile32768 631169280 631234816 13 3313 25123 29 _ _ (2026307 / 100000) (202631 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell631234816 :
    ThetaLowerSegment 631234816 631300352 (63120782941749 / 100000) (15781846677213 / 25000) := by
  exact
    packedTile32768 631234816 631300352 13 3259 25124 29 _ _ (2026317 / 100000) (25329 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell631300352 :
    ThetaLowerSegment 631300352 631365888 (15781846677213 / 25000) (3156696688731 / 5000) := by
  exact
    packedTile32768 631300352 631365888 13 3231 25125 29 _ _ (253291 / 12500) (2026331 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell631365888 :
    ThetaLowerSegment 631365888 631431424 (3156696688731 / 5000) (15785096408703 / 25000) := by
  exact
    packedTile32768 631365888 631431424 13 3184 25126 29 _ _ (1013169 / 50000) (2026341 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell631431424 :
    ThetaLowerSegment 631431424 631496960 (15785096408703 / 25000) (1973346968076 / 3125) := by
  exact
    packedTile32768 631431424 631496960 13 3315 25128 29 _ _ (506587 / 25000) (2026351 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell631496960 :
    ThetaLowerSegment 631496960 631562496 (1973346968076 / 3125) (31576860533463 / 50000) := by
  exact
    packedTile32768 631496960 631562496 13 3266 25129 29 _ _ (2026359 / 100000) (1013181 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell631562496 :
    ThetaLowerSegment 631562496 631628032 (31576860533463 / 50000) (63160252054213 / 100000) := by
  exact
    packedTile32768 631562496 631628032 13 3223 25130 29 _ _ (2026369 / 100000) (506593 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell631628032 :
    ThetaLowerSegment 631628032 631693568 (63160252054213 / 100000) (63166845894733 / 100000) := by
  exact
    packedTile32768 631628032 631693568 13 3254 25132 29 _ _ (101319 / 5000) (2026383 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell631693568 :
    ThetaLowerSegment 631693568 631759104 (63166845894733 / 100000) (63173322237173 / 100000) := by
  exact
    packedTile32768 631693568 631759104 13 3196 25133 29 _ _ (202639 / 10000) (2026393 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell631759104 :
    ThetaLowerSegment 631759104 631824640 (63173322237173 / 100000) (63179855350773 / 100000) := by
  exact
    packedTile32768 631759104 631824640 13 3224 25134 29 _ _ (2533 / 125) (2026403 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell631824640 :
    ThetaLowerSegment 631824640 631890176 (63179855350773 / 100000) (31593205395179 / 50000) := by
  exact
    packedTile32768 631824640 631890176 13 3235 25136 29 _ _ (2026411 / 100000) (1013207 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell631890176 :
    ThetaLowerSegment 631890176 631955712 (31593205395179 / 50000) (63193035160607 / 100000) := by
  exact
    packedTile32768 631890176 631955712 13 3269 25137 29 _ _ (2026421 / 100000) (253303 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell631955712 :
    ThetaLowerSegment 631955712 632021248 (63193035160607 / 100000) (31599785200291 / 50000) := by
  exact
    packedTile32768 631955712 632021248 13 3225 25138 29 _ _ (2026431 / 100000) (1013217 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell632021248 :
    ThetaLowerSegment 632021248 632086784 (31599785200291 / 50000) (15801521352903 / 25000) := by
  exact
    packedTile32768 632021248 632086784 13 3215 25140 29 _ _ (1013221 / 50000) (405289 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell632086784 :
    ThetaLowerSegment 632086784 632152320 (15801521352903 / 25000) (1580313187563 / 2500) := by
  exact
    packedTile32768 632086784 632152320 13 3179 25141 29 _ _ (506613 / 25000) (405291 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell632152320 :
    ThetaLowerSegment 632152320 632217856 (1580313187563 / 2500) (63219172274697 / 100000) := by
  exact
    packedTile32768 632152320 632217856 13 3279 25142 29 _ _ (2026463 / 100000) (1013233 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell632217856 :
    ThetaLowerSegment 632217856 632283392 (63219172274697 / 100000) (63225815053191 / 100000) := by
  exact
    packedTile32768 632217856 632283392 13 3278 25143 29 _ _ (2026473 / 100000) (506619 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell632283392 :
    ThetaLowerSegment 632283392 632348928 (63225815053191 / 100000) (63232352487349 / 100000) := by
  exact
    packedTile32768 632283392 632348928 13 3226 25145 29 _ _ (2026483 / 100000) (1013243 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell632348928 :
    ThetaLowerSegment 632348928 632414464 (63232352487349 / 100000) (12647775154307 / 20000) := by
  exact
    packedTile32768 632348928 632414464 13 3219 25146 29 _ _ (1013247 / 50000) (2026497 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell632414464 :
    ThetaLowerSegment 632414464 632480000 (12647775154307 / 20000) (63245316001247 / 100000) := by
  exact
    packedTile32768 632414464 632480000 13 3178 25147 29 _ _ (253313 / 12500) (2026507 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell632480000 :
    ThetaLowerSegment 632480000 632545536 (63245316001247 / 100000) (63251873800551 / 100000) := by
  exact
    packedTile32768 632480000 632545536 13 3236 25149 29 _ _ (1013257 / 50000) (2026517 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell632545536 :
    ThetaLowerSegment 632545536 632611072 (63251873800551 / 100000) (63258297884801 / 100000) := by
  exact
    packedTile32768 632545536 632611072 13 3170 25150 29 _ _ (81061 / 4000) (63329 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell632611072 :
    ThetaLowerSegment 632611072 632676608 (63258297884801 / 100000) (63264762531451 / 100000) := by
  exact
    packedTile32768 632611072 632676608 13 3190 25151 29 _ _ (405307 / 20000) (1013269 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell632676608 :
    ThetaLowerSegment 632676608 632742144 (63264762531451 / 100000) (7908921386837 / 12500) := by
  exact
    packedTile32768 632676608 632742144 13 3261 25153 29 _ _ (405309 / 20000) (506637 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell632742144 :
    ThetaLowerSegment 632742144 632807680 (7908921386837 / 12500) (15819475671171 / 25000) := by
  exact
    packedTile32768 632742144 632807680 13 3223 25154 29 _ _ (506639 / 25000) (2026559 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell632807680 :
    ThetaLowerSegment 632807680 632873216 (15819475671171 / 25000) (31642231339413 / 50000) := by
  exact
    packedTile32768 632807680 632873216 13 3237 25155 29 _ _ (1013283 / 50000) (2026569 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell632873216 :
    ThetaLowerSegment 632873216 632938752 (31642231339413 / 50000) (63290998389651 / 100000) := by
  exact
    packedTile32768 632873216 632938752 13 3225 25156 29 _ _ (2026577 / 100000) (101329 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell632938752 :
    ThetaLowerSegment 632938752 633004288 (63290998389651 / 100000) (63297475361703 / 100000) := by
  exact
    packedTile32768 632938752 633004288 13 3196 25158 29 _ _ (2026587 / 100000) (202659 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell633004288 :
    ThetaLowerSegment 633004288 633069824 (63297475361703 / 100000) (15826027103421 / 25000) := by
  exact
    packedTile32768 633004288 633069824 13 3273 25159 29 _ _ (2026597 / 100000) (10133 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell633069824 :
    ThetaLowerSegment 633069824 633135360 (15826027103421 / 25000) (15827671189161 / 25000) := by
  exact
    packedTile32768 633069824 633135360 13 3245 25160 29 _ _ (126663 / 6250) (2026611 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell633135360 :
    ThetaLowerSegment 633135360 633200896 (15827671189161 / 25000) (15829314776359 / 25000) := by
  exact
    packedTile32768 633135360 633200896 13 3244 25162 29 _ _ (1013309 / 50000) (2026621 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell633200896 :
    ThetaLowerSegment 633200896 633266432 (15829314776359 / 25000) (1978867579834 / 3125) := by
  exact
    packedTile32768 633200896 633266432 13 3209 25163 29 _ _ (506657 / 25000) (2026631 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell633266432 :
    ThetaLowerSegment 633266432 633331968 (1978867579834 / 3125) (63330245772849 / 100000) := by
  exact
    packedTile32768 633266432 633331968 13 3199 25164 29 _ _ (2026639 / 100000) (1013321 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell633331968 :
    ThetaLowerSegment 633331968 633397504 (63330245772849 / 100000) (15834188335697 / 25000) := by
  exact
    packedTile32768 633331968 633397504 13 3211 25166 29 _ _ (2026649 / 100000) (506663 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell633397504 :
    ThetaLowerSegment 633397504 633463040 (15834188335697 / 25000) (63343171771841 / 100000) := by
  exact
    packedTile32768 633397504 633463040 13 3167 25167 29 _ _ (2026659 / 100000) (1013331 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell633463040 :
    ThetaLowerSegment 633463040 633528576 (63343171771841 / 100000) (63349726022621 / 100000) := by
  exact
    packedTile32768 633463040 633528576 13 3234 25168 29 _ _ (202667 / 10000) (2026673 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell633528576 :
    ThetaLowerSegment 633528576 633594112 (63349726022621 / 100000) (63356233692101 / 100000) := by
  exact
    packedTile32768 633528576 633594112 13 3211 25169 29 _ _ (50667 / 2500) (2026683 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell633594112 :
    ThetaLowerSegment 633594112 633659648 (63356233692101 / 100000) (63362824487981 / 100000) := by
  exact
    packedTile32768 633594112 633659648 13 3252 25171 29 _ _ (202669 / 10000) (2026693 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell633659648 :
    ThetaLowerSegment 633659648 633725184 (63362824487981 / 100000) (63369447746849 / 100000) := by
  exact
    packedTile32768 633659648 633725184 13 3268 25172 29 _ _ (2026701 / 100000) (126669 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell633725184 :
    ThetaLowerSegment 633725184 633790720 (63369447746849 / 100000) (63375977809691 / 100000) := by
  exact
    packedTile32768 633725184 633790720 13 3222 25173 29 _ _ (2026711 / 100000) (1013357 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell633790720 :
    ThetaLowerSegment 633790720 633856256 (63375977809691 / 100000) (316912610459 / 500) := by
  exact
    packedTile32768 633790720 633856256 13 3229 25175 29 _ _ (2026721 / 100000) (506681 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell633856256 :
    ThetaLowerSegment 633856256 633921792 (316912610459 / 500) (3169456968589 / 5000) := by
  exact
    packedTile32768 633856256 633921792 13 3265 25176 29 _ _ (506683 / 25000) (405347 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell633921792 :
    ThetaLowerSegment 633921792 633987328 (3169456968589 / 5000) (31697833753881 / 50000) := by
  exact
    packedTile32768 633921792 633987328 13 3221 25177 29 _ _ (1013371 / 50000) (405349 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell633987328 :
    ThetaLowerSegment 633987328 634052864 (31697833753881 / 50000) (31701140399769 / 50000) := by
  exact
    packedTile32768 633987328 634052864 13 3263 25179 29 _ _ (63336 / 3125) (405351 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell634052864 :
    ThetaLowerSegment 634052864 634118400 (31701140399769 / 50000) (12681777204031 / 20000) := by
  exact
    packedTile32768 634052864 634118400 13 3259 25180 29 _ _ (2026763 / 100000) (1013383 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell634118400 :
    ThetaLowerSegment 634118400 634183936 (12681777204031 / 20000) (63415477085951 / 100000) := by
  exact
    packedTile32768 634118400 634183936 13 3252 25181 29 _ _ (2026773 / 100000) (253347 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell634183936 :
    ThetaLowerSegment 634183936 634249472 (63415477085951 / 100000) (1981938300682 / 3125) := by
  exact
    packedTile32768 634183936 634249472 13 3231 25183 29 _ _ (2026783 / 100000) (1013393 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell634249472 :
    ThetaLowerSegment 634249472 634315008 (1981938300682 / 3125) (3964278919973 / 6250) := by
  exact
    packedTile32768 634249472 634315008 13 3176 25184 29 _ _ (1013397 / 50000) (2026797 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell634315008 :
    ThetaLowerSegment 634315008 634380544 (3964278919973 / 6250) (15858762964843 / 25000) := by
  exact
    packedTile32768 634315008 634380544 13 3251 25185 29 _ _ (506701 / 25000) (2026807 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell634380544 :
    ThetaLowerSegment 634380544 634446080 (15858762964843 / 25000) (7930194741539 / 12500) := by
  exact
    packedTile32768 634380544 634446080 13 3210 25186 29 _ _ (1013407 / 50000) (2026817 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell634446080 :
    ThetaLowerSegment 634446080 634511616 (7930194741539 / 12500) (63448021477237 / 100000) := by
  exact
    packedTile32768 634446080 634511616 13 3189 25188 29 _ _ (81073 / 4000) (506707 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell634511616 :
    ThetaLowerSegment 634511616 634577152 (63448021477237 / 100000) (63454604637317 / 100000) := by
  exact
    packedTile32768 634511616 634577152 13 3248 25189 29 _ _ (405367 / 20000) (1013419 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell634577152 :
    ThetaLowerSegment 634577152 634642688 (63454604637317 / 100000) (63461272957367 / 100000) := by
  exact
    packedTile32768 634577152 634642688 13 3290 25190 29 _ _ (405369 / 20000) (63339 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell634642688 :
    ThetaLowerSegment 634642688 634708224 (63461272957367 / 100000) (63467752815999 / 100000) := by
  exact
    packedTile32768 634642688 634708224 13 3197 25192 29 _ _ (253357 / 12500) (2026859 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell634708224 :
    ThetaLowerSegment 634708224 634773760 (63467752815999 / 100000) (63474244867797 / 100000) := by
  exact
    packedTile32768 634708224 634773760 13 3203 25193 29 _ _ (1013433 / 50000) (2026869 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell634773760 :
    ThetaLowerSegment 634773760 634839296 (63474244867797 / 100000) (63480789650401 / 100000) := by
  exact
    packedTile32768 634773760 634839296 13 3229 25194 29 _ _ (506719 / 25000) (2026879 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell634839296 :
    ThetaLowerSegment 634839296 634904832 (63480789650401 / 100000) (1983979962224 / 3125) := by
  exact
    packedTile32768 634839296 634904832 13 3241 25196 29 _ _ (2026887 / 100000) (202689 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell634904832 :
    ThetaLowerSegment 634904832 634970368 (1983979962224 / 3125) (15873507834023 / 25000) := by
  exact
    packedTile32768 634904832 634970368 13 3292 25197 29 _ _ (2026897 / 100000) (20269 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell634970368 :
    ThetaLowerSegment 634970368 635035904 (15873507834023 / 25000) (63500527573027 / 100000) := by
  exact
    packedTile32768 634970368 635035904 13 3205 25198 29 _ _ (2026907 / 100000) (202691 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell635035904 :
    ThetaLowerSegment 635035904 635101440 (63500527573027 / 100000) (63507185998657 / 100000) := by
  exact
    packedTile32768 635035904 635101440 13 3285 25199 29 _ _ (1013459 / 50000) (2026921 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell635101440 :
    ThetaLowerSegment 635101440 635166976 (63507185998657 / 100000) (63513649872049 / 100000) := by
  exact
    packedTile32768 635101440 635166976 13 3189 25201 29 _ _ (126683 / 6250) (2026931 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell635166976 :
    ThetaLowerSegment 635166976 635232512 (63513649872049 / 100000) (12704030052443 / 20000) := by
  exact
    packedTile32768 635166976 635232512 13 3207 25202 29 _ _ (1013469 / 50000) (2026941 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell635232512 :
    ThetaLowerSegment 635232512 635298048 (12704030052443 / 20000) (63526689199689 / 100000) := by
  exact
    packedTile32768 635232512 635298048 13 3226 25203 29 _ _ (2026949 / 100000) (253369 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell635298048 :
    ThetaLowerSegment 635298048 635363584 (63526689199689 / 100000) (1270662658047 / 2000) := by
  exact
    packedTile32768 635298048 635363584 13 3179 25205 29 _ _ (2026959 / 100000) (1013481 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell635363584 :
    ThetaLowerSegment 635363584 635429120 (1270662658047 / 2000) (31769894734273 / 50000) := by
  exact
    packedTile32768 635363584 635429120 13 3284 25206 29 _ _ (2026969 / 100000) (506743 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell635429120 :
    ThetaLowerSegment 635429120 635494656 (31769894734273 / 50000) (31773124726903 / 50000) := by
  exact
    packedTile32768 635429120 635494656 13 3187 25207 29 _ _ (101349 / 5000) (2026983 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell635494656 :
    ThetaLowerSegment 635494656 635560192 (31773124726903 / 50000) (3972054983631 / 6250) := by
  exact
    packedTile32768 635494656 635560192 13 3271 25209 29 _ _ (202699 / 10000) (2026993 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell635560192 :
    ThetaLowerSegment 635560192 635625728 (3972054983631 / 6250) (7944932169137 / 12500) := by
  exact
    packedTile32768 635560192 635625728 13 3245 25210 29 _ _ (2027 / 100) (2027003 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell635625728 :
    ThetaLowerSegment 635625728 635691264 (7944932169137 / 12500) (12713196460301 / 20000) := by
  exact
    packedTile32768 635625728 635691264 13 3219 25211 29 _ _ (2027011 / 100000) (1013507 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell635691264 :
    ThetaLowerSegment 635691264 635756800 (12713196460301 / 20000) (3178629012743 / 5000) := by
  exact
    packedTile32768 635691264 635756800 13 3255 25212 29 _ _ (2027021 / 100000) (126689 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell635756800 :
    ThetaLowerSegment 635756800 635822336 (3178629012743 / 5000) (7947400574021 / 12500) := by
  exact
    packedTile32768 635756800 635822336 13 3268 25214 29 _ _ (2027031 / 100000) (1013517 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell635822336 :
    ThetaLowerSegment 635822336 635887872 (7947400574021 / 12500) (3179293880557 / 5000) := by
  exact
    packedTile32768 635822336 635887872 13 3292 25215 29 _ _ (2027041 / 100000) (506761 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell635887872 :
    ThetaLowerSegment 635887872 635953408 (3179293880557 / 5000) (15898105233749 / 25000) := by
  exact
    packedTile32768 635887872 635953408 13 3228 25216 29 _ _ (506763 / 25000) (405411 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell635953408 :
    ThetaLowerSegment 635953408 636018944 (15898105233749 / 25000) (31799543970957 / 50000) := by
  exact
    packedTile32768 635953408 636018944 13 3289 25218 29 _ _ (1013531 / 50000) (405413 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell636018944 :
    ThetaLowerSegment 636018944 636084480 (31799543970957 / 50000) (31802809583949 / 50000) := by
  exact
    packedTile32768 636018944 636084480 13 3222 25219 29 _ _ (63346 / 3125) (81083 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell636084480 :
    ThetaLowerSegment 636084480 636150016 (31802809583949 / 50000) (63612107860581 / 100000) := by
  exact
    packedTile32768 636084480 636150016 13 3201 25220 29 _ _ (2027083 / 100000) (1013543 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell636150016 :
    ThetaLowerSegment 636150016 636215552 (63612107860581 / 100000) (63618781050737 / 100000) := by
  exact
    packedTile32768 636150016 636215552 13 3292 25222 29 _ _ (2027093 / 100000) (253387 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell636215552 :
    ThetaLowerSegment 636215552 636281088 (63618781050737 / 100000) (31812689635501 / 50000) := by
  exact
    packedTile32768 636215552 636281088 13 3255 25223 29 _ _ (2027103 / 100000) (1013553 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell636281088 :
    ThetaLowerSegment 636281088 636346624 (31812689635501 / 50000) (31815930990787 / 50000) := by
  exact
    packedTile32768 636281088 636346624 13 3198 25224 29 _ _ (1013557 / 50000) (2027117 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell636346624 :
    ThetaLowerSegment 636346624 636412160 (31815930990787 / 50000) (31819184524807 / 50000) := by
  exact
    packedTile32768 636346624 636412160 13 3210 25225 29 _ _ (506781 / 25000) (2027127 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell636412160 :
    ThetaLowerSegment 636412160 636477696 (31819184524807 / 50000) (31822448210547 / 50000) := by
  exact
    packedTile32768 636412160 636477696 13 3220 25227 29 _ _ (1013567 / 50000) (2027137 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell636477696 :
    ThetaLowerSegment 636477696 636543232 (31822448210547 / 50000) (31825747387407 / 50000) := by
  exact
    packedTile32768 636477696 636543232 13 3255 25228 29 _ _ (253393 / 12500) (2027147 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell636543232 :
    ThetaLowerSegment 636543232 636608768 (31825747387407 / 50000) (63657935046249 / 100000) := by
  exact
    packedTile32768 636543232 636608768 13 3177 25229 29 _ _ (405431 / 20000) (1013579 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell636608768 :
    ThetaLowerSegment 636608768 636674304 (63657935046249 / 100000) (63664551712809 / 100000) := by
  exact
    packedTile32768 636608768 636674304 13 3264 25231 29 _ _ (405433 / 20000) (63349 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell636674304 :
    ThetaLowerSegment 636674304 636739840 (63664551712809 / 100000) (63671075161959 / 100000) := by
  exact
    packedTile32768 636674304 636739840 13 3218 25232 29 _ _ (81087 / 4000) (1013589 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell636739840 :
    ThetaLowerSegment 636739840 636805376 (63671075161959 / 100000) (63677659462087 / 100000) := by
  exact
    packedTile32768 636739840 636805376 13 3248 25233 29 _ _ (1013593 / 50000) (2027189 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell636805376 :
    ThetaLowerSegment 636805376 636870912 (63677659462087 / 100000) (63684270148243 / 100000) := by
  exact
    packedTile32768 636805376 636870912 13 3261 25235 29 _ _ (506799 / 25000) (2027199 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell636870912 :
    ThetaLowerSegment 636870912 636936448 (63684270148243 / 100000) (63690789642739 / 100000) := by
  exact
    packedTile32768 636870912 636936448 13 3216 25236 29 _ _ (1013603 / 50000) (2027209 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell636936448 :
    ThetaLowerSegment 636936448 637001984 (63690789642739 / 100000) (63697463241103 / 100000) := by
  exact
    packedTile32768 636936448 637001984 13 3292 25237 29 _ _ (2027217 / 100000) (101361 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell637001984 :
    ThetaLowerSegment 637001984 637067520 (63697463241103 / 100000) (63703974694227 / 100000) := by
  exact
    packedTile32768 637001984 637067520 13 3212 25238 29 _ _ (2027227 / 100000) (202723 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell637067520 :
    ThetaLowerSegment 637067520 637133056 (63703974694227 / 100000) (31855286675331 / 50000) := by
  exact
    packedTile32768 637067520 637133056 13 3255 25240 29 _ _ (2027237 / 100000) (50681 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell637133056 :
    ThetaLowerSegment 637133056 637198592 (31855286675331 / 50000) (63717070677297 / 100000) := by
  exact
    packedTile32768 637133056 637198592 13 3205 25241 29 _ _ (2027247 / 100000) (8109 / 400)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell637198592 :
    ThetaLowerSegment 637198592 637264128 (63717070677297 / 100000) (12744724149579 / 20000) := by
  exact
    packedTile32768 637198592 637264128 13 3231 25242 29 _ _ (1013629 / 50000) (2027261 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell637264128 :
    ThetaLowerSegment 637264128 637329664 (12744724149579 / 20000) (63730264105131 / 100000) := by
  exact
    packedTile32768 637264128 637329664 13 3277 25244 29 _ _ (506817 / 25000) (2027271 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell637329664 :
    ThetaLowerSegment 637329664 637395200 (63730264105131 / 100000) (63736877085967 / 100000) := by
  exact
    packedTile32768 637329664 637395200 13 3262 25245 29 _ _ (1013639 / 50000) (2027281 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell637395200 :
    ThetaLowerSegment 637395200 637460736 (63736877085967 / 100000) (63743481993529 / 100000) := by
  exact
    packedTile32768 637395200 637460736 13 3258 25246 29 _ _ (2027289 / 100000) (506823 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell637460736 :
    ThetaLowerSegment 637460736 637526272 (63743481993529 / 100000) (63750066660681 / 100000) := by
  exact
    packedTile32768 637460736 637526272 13 3248 25247 29 _ _ (2027299 / 100000) (1013651 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell637526272 :
    ThetaLowerSegment 637526272 637591808 (63750066660681 / 100000) (31878302366103 / 50000) := by
  exact
    packedTile32768 637526272 637591808 13 3225 25249 29 _ _ (2027309 / 100000) (126707 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell637591808 :
    ThetaLowerSegment 637591808 637657344 (31878302366103 / 50000) (63763126617429 / 100000) := by
  exact
    packedTile32768 637591808 637657344 13 3217 25250 29 _ _ (2027319 / 100000) (1013661 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell637657344 :
    ThetaLowerSegment 637657344 637722880 (63763126617429 / 100000) (63769620155419 / 100000) := by
  exact
    packedTile32768 637657344 637722880 13 3203 25251 29 _ _ (202733 / 10000) (2027333 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell637722880 :
    ThetaLowerSegment 637722880 637788416 (63769620155419 / 100000) (63776184682339 / 100000) := by
  exact
    packedTile32768 637722880 637788416 13 3238 25253 29 _ _ (101367 / 5000) (2027343 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell637788416 :
    ThetaLowerSegment 637788416 637853952 (63776184682339 / 100000) (63782631655339 / 100000) := by
  exact
    packedTile32768 637788416 637853952 13 3180 25254 29 _ _ (40547 / 2000) (2027353 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell637853952 :
    ThetaLowerSegment 637853952 637919488 (63782631655339 / 100000) (63789222602699 / 100000) := by
  exact
    packedTile32768 637853952 637919488 13 3251 25255 29 _ _ (12671 / 625) (2027363 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell637919488 :
    ThetaLowerSegment 637919488 637985024 (63789222602699 / 100000) (63795819667933 / 100000) := by
  exact
    packedTile32768 637919488 637985024 13 3254 25257 29 _ _ (2027371 / 100000) (1013687 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell637985024 :
    ThetaLowerSegment 637985024 638050560 (63795819667933 / 100000) (63802343779991 / 100000) := by
  exact
    packedTile32768 637985024 638050560 13 3218 25258 29 _ _ (2027381 / 100000) (253423 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell638050560 :
    ThetaLowerSegment 638050560 638116096 (63802343779991 / 100000) (31904514044059 / 50000) := by
  exact
    packedTile32768 638050560 638116096 13 3297 25259 29 _ _ (2027391 / 100000) (1013697 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell638116096 :
    ThetaLowerSegment 638116096 638181632 (31904514044059 / 50000) (31907737613239 / 50000) := by
  exact
    packedTile32768 638116096 638181632 13 3180 25260 29 _ _ (1013701 / 50000) (405481 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell638181632 :
    ThetaLowerSegment 638181632 638247168 (31907737613239 / 50000) (31910998705441 / 50000) := by
  exact
    packedTile32768 638181632 638247168 13 3217 25262 29 _ _ (506853 / 25000) (405483 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell638247168 :
    ThetaLowerSegment 638247168 638312704 (31910998705441 / 50000) (7978563939721 / 12500) := by
  exact
    packedTile32768 638247168 638312704 13 3213 25263 29 _ _ (1013711 / 50000) (81097 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell638312704 :
    ThetaLowerSegment 638312704 638378240 (7978563939721 / 12500) (7979393666267 / 12500) := by
  exact
    packedTile32768 638312704 638378240 13 3274 25264 29 _ _ (253429 / 12500) (405487 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell638378240 :
    ThetaLowerSegment 638378240 638443776 (7979393666267 / 12500) (63841781096189 / 100000) := by
  exact
    packedTile32768 638378240 638443776 13 3271 25266 29 _ _ (2027443 / 100000) (1013723 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell638443776 :
    ThetaLowerSegment 638443776 638509312 (63841781096189 / 100000) (31924139541527 / 50000) := by
  exact
    packedTile32768 638443776 638509312 13 3205 25267 29 _ _ (2027453 / 100000) (63358 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell638509312 :
    ThetaLowerSegment 638509312 638574848 (31924139541527 / 50000) (15963696809821 / 25000) := by
  exact
    packedTile32768 638509312 638574848 13 3210 25268 29 _ _ (2027463 / 100000) (1013733 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell638574848 :
    ThetaLowerSegment 638574848 638640384 (15963696809821 / 25000) (63861378554007 / 100000) := by
  exact
    packedTile32768 638574848 638640384 13 3251 25270 29 _ _ (2027473 / 100000) (506869 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell638640384 :
    ThetaLowerSegment 638640384 638705920 (63861378554007 / 100000) (12773568029103 / 20000) := by
  exact
    packedTile32768 638640384 638705920 13 3187 25271 29 _ _ (506871 / 25000) (2027487 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell638705920 :
    ThetaLowerSegment 638705920 638771456 (12773568029103 / 20000) (63874295686411 / 100000) := by
  exact
    packedTile32768 638705920 638771456 13 3184 25272 29 _ _ (1013747 / 50000) (2027497 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell638771456 :
    ThetaLowerSegment 638771456 638836992 (63874295686411 / 100000) (63880858716859 / 100000) := by
  exact
    packedTile32768 638771456 638836992 13 3237 25273 29 _ _ (126719 / 6250) (2027507 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell638836992 :
    ThetaLowerSegment 638836992 638902528 (63880858716859 / 100000) (12777475029371 / 20000) := by
  exact
    packedTile32768 638836992 638902528 13 3214 25275 29 _ _ (1013757 / 50000) (2027517 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell638902528 :
    ThetaLowerSegment 638902528 638968064 (12777475029371 / 20000) (798675444581 / 1250) := by
  exact
    packedTile32768 638902528 638968064 13 3285 25276 29 _ _ (81101 / 4000) (253441 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell638968064 :
    ThetaLowerSegment 638968064 639033600 (798675444581 / 1250) (319502537291 / 500) := by
  exact
    packedTile32768 638968064 639033600 13 3192 25277 29 _ _ (405507 / 20000) (1013769 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell639033600 :
    ThetaLowerSegment 639033600 639099136 (319502537291 / 500) (12781403581039 / 20000) := by
  exact
    packedTile32768 639033600 639099136 13 3211 25279 29 _ _ (405509 / 20000) (506887 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell639099136 :
    ThetaLowerSegment 639099136 639164672 (12781403581039 / 20000) (63913625710199 / 100000) := by
  exact
    packedTile32768 639099136 639164672 13 3259 25280 29 _ _ (506889 / 25000) (2027559 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell639164672 :
    ThetaLowerSegment 639164672 639230208 (63913625710199 / 100000) (63920265988849 / 100000) := by
  exact
    packedTile32768 639164672 639230208 13 3275 25281 29 _ _ (1013783 / 50000) (2027569 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell639230208 :
    ThetaLowerSegment 639230208 639295744 (63920265988849 / 100000) (63926792755993 / 100000) := by
  exact
    packedTile32768 639230208 639295744 13 3219 25283 29 _ _ (253447 / 12500) (2027579 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell639295744 :
    ThetaLowerSegment 639295744 639361280 (63926792755993 / 100000) (63933347941531 / 100000) := by
  exact
    packedTile32768 639295744 639361280 13 3233 25284 29 _ _ (1013793 / 50000) (2027589 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell639361280 :
    ThetaLowerSegment 639361280 639426816 (63933347941531 / 100000) (15984925100733 / 25000) := by
  exact
    packedTile32768 639361280 639426816 13 3133 25285 29 _ _ (2027597 / 100000) (5069 / 250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell639426816 :
    ThetaLowerSegment 639426816 639492352 (15984925100733 / 25000) (63946344871071 / 100000) := by
  exact
    packedTile32768 639426816 639492352 13 3277 25286 29 _ _ (2027607 / 100000) (202761 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell639492352 :
    ThetaLowerSegment 639492352 639557888 (63946344871071 / 100000) (31976439940331 / 50000) := by
  exact
    packedTile32768 639492352 639557888 13 3223 25288 29 _ _ (2027617 / 100000) (101381 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell639557888 :
    ThetaLowerSegment 639557888 639623424 (31976439940331 / 50000) (31979736861833 / 50000) := by
  exact
    packedTile32768 639557888 639623424 13 3252 25289 29 _ _ (2027627 / 100000) (202763 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell639623424 :
    ThetaLowerSegment 639623424 639688960 (31979736861833 / 50000) (6396607976827 / 10000) := by
  exact
    packedTile32768 639623424 639688960 13 3258 25290 29 _ _ (1013819 / 50000) (2027641 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell639688960 :
    ThetaLowerSegment 639688960 639754496 (6396607976827 / 10000) (31986327715367 / 50000) := by
  exact
    packedTile32768 639688960 639754496 13 3243 25292 29 _ _ (63364 / 3125) (2027651 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell639754496 :
    ThetaLowerSegment 639754496 639820032 (31986327715367 / 50000) (15994805753749 / 25000) := by
  exact
    packedTile32768 639754496 639820032 13 3239 25293 29 _ _ (1013829 / 50000) (2027661 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell639820032 :
    ThetaLowerSegment 639820032 639885568 (15994805753749 / 25000) (15996420791311 / 25000) := by
  exact
    packedTile32768 639820032 639885568 13 3186 25294 29 _ _ (506917 / 25000) (2027671 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell639885568 :
    ThetaLowerSegment 639885568 639951104 (15996420791311 / 25000) (31996078770549 / 50000) := by
  exact
    packedTile32768 639885568 639951104 13 3193 25295 29 _ _ (1013839 / 50000) (2027681 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell639951104 :
    ThetaLowerSegment 639951104 640016640 (31996078770549 / 50000) (31999367682107 / 50000) := by
  exact
    packedTile32768 639951104 640016640 13 3244 25297 29 _ _ (2027689 / 100000) (506923 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell640016640 :
    ThetaLowerSegment 640016640 640082176 (31999367682107 / 50000) (32002672831477 / 50000) := by
  exact
    packedTile32768 640016640 640082176 13 3260 25298 29 _ _ (2027699 / 100000) (1013851 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell640082176 :
    ThetaLowerSegment 640082176 640147712 (32002672831477 / 50000) (64012010742437 / 100000) := by
  exact
    packedTile32768 640082176 640147712 13 3287 25299 29 _ _ (2027709 / 100000) (63366 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell640147712 :
    ThetaLowerSegment 640147712 640213248 (64012010742437 / 100000) (12803704755173 / 20000) := by
  exact
    packedTile32768 640147712 640213248 13 3212 25301 29 _ _ (2027719 / 100000) (1013861 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell640213248 :
    ThetaLowerSegment 640213248 640278784 (12803704755173 / 20000) (2561009990251 / 4000) := by
  exact
    packedTile32768 640213248 640278784 13 3317 25302 29 _ _ (202773 / 10000) (2027733 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell640278784 :
    ThetaLowerSegment 640278784 640344320 (2561009990251 / 4000) (12806363115679 / 20000) := by
  exact
    packedTile32768 640278784 640344320 13 3238 25303 29 _ _ (101387 / 5000) (2027743 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell640344320 :
    ThetaLowerSegment 640344320 640409856 (12806363115679 / 20000) (12807660875679 / 20000) := by
  exact
    packedTile32768 640344320 640409856 13 3200 25305 29 _ _ (8111 / 400) (2027753 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell640409856 :
    ThetaLowerSegment 640409856 640475392 (12807660875679 / 20000) (12808966753119 / 20000) := by
  exact
    packedTile32768 640409856 640475392 13 3220 25306 29 _ _ (25347 / 1250) (2027763 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell640475392 :
    ThetaLowerSegment 640475392 640540928 (12808966753119 / 20000) (32025674496909 / 50000) := by
  exact
    packedTile32768 640475392 640540928 13 3213 25307 29 _ _ (2027771 / 100000) (1013887 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell640540928 :
    ThetaLowerSegment 640540928 640606464 (32025674496909 / 50000) (2001812376873 / 3125) := by
  exact
    packedTile32768 640540928 640606464 13 3278 25308 29 _ _ (2027781 / 100000) (253473 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell640606464 :
    ThetaLowerSegment 640606464 640672000 (2001812376873 / 3125) (64064560019403 / 100000) := by
  exact
    packedTile32768 640606464 640672000 13 3237 25310 29 _ _ (2027791 / 100000) (1013897 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell640672000 :
    ThetaLowerSegment 640672000 640737536 (64064560019403 / 100000) (32035547811013 / 50000) := by
  exact
    packedTile32768 640672000 640737536 13 3223 25311 29 _ _ (2027801 / 100000) (506951 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell640737536 :
    ThetaLowerSegment 640737536 640803072 (32035547811013 / 50000) (32038857200197 / 50000) := by
  exact
    packedTile32768 640737536 640803072 13 3264 25312 29 _ _ (506953 / 25000) (405563 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell640803072 :
    ThetaLowerSegment 640803072 640868608 (32038857200197 / 50000) (32042128077083 / 50000) := by
  exact
    packedTile32768 640803072 640868608 13 3226 25314 29 _ _ (1013911 / 50000) (81113 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell640868608 :
    ThetaLowerSegment 640868608 640934144 (32042128077083 / 50000) (32045368552619 / 50000) := by
  exact
    packedTile32768 640868608 640934144 13 3196 25315 29 _ _ (253479 / 12500) (405567 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell640934144 :
    ThetaLowerSegment 640934144 640999680 (32045368552619 / 50000) (16024356738999 / 25000) := by
  exact
    packedTile32768 640934144 640999680 13 3299 25316 29 _ _ (1013921 / 50000) (405569 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell640999680 :
    ThetaLowerSegment 640999680 641065216 (16024356738999 / 25000) (8012987735929 / 12500) := by
  exact
    packedTile32768 640999680 641065216 13 3193 25317 29 _ _ (506963 / 25000) (405571 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell641065216 :
    ThetaLowerSegment 641065216 641130752 (8012987735929 / 12500) (16027611957299 / 25000) := by
  exact
    packedTile32768 641065216 641130752 13 3228 25319 29 _ _ (2027863 / 100000) (1013933 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell641130752 :
    ThetaLowerSegment 641130752 641196288 (16027611957299 / 25000) (64116955273653 / 100000) := by
  exact
    packedTile32768 641130752 641196288 13 3209 25320 29 _ _ (2027873 / 100000) (506969 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell641196288 :
    ThetaLowerSegment 641196288 641261824 (64116955273653 / 100000) (64123485056913 / 100000) := by
  exact
    packedTile32768 641196288 641261824 13 3220 25321 29 _ _ (2027883 / 100000) (1013943 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell641261824 :
    ThetaLowerSegment 641261824 641327360 (64123485056913 / 100000) (16032505239013 / 25000) := by
  exact
    packedTile32768 641261824 641327360 13 3223 25323 29 _ _ (2027893 / 100000) (253487 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell641327360 :
    ThetaLowerSegment 641327360 641392896 (16032505239013 / 25000) (16034151897061 / 25000) := by
  exact
    packedTile32768 641327360 641392896 13 3248 25324 29 _ _ (63372 / 3125) (2027907 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell641392896 :
    ThetaLowerSegment 641392896 641458432 (16034151897061 / 25000) (32071663033663 / 50000) := by
  exact
    packedTile32768 641392896 641458432 13 3313 25325 29 _ _ (1013957 / 50000) (2027917 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell641458432 :
    ThetaLowerSegment 641458432 641523968 (32071663033663 / 50000) (32074962466011 / 50000) := by
  exact
    packedTile32768 641458432 641523968 13 3254 25327 29 _ _ (506981 / 25000) (2027927 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell641523968 :
    ThetaLowerSegment 641523968 641589504 (32074962466011 / 50000) (32078231495619 / 50000) := by
  exact
    packedTile32768 641523968 641589504 13 3224 25328 29 _ _ (1013967 / 50000) (2027937 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell641589504 :
    ThetaLowerSegment 641589504 641655040 (32078231495619 / 50000) (32081507639151 / 50000) := by
  exact
    packedTile32768 641589504 641655040 13 3231 25329 29 _ _ (253493 / 12500) (2027947 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell641655040 :
    ThetaLowerSegment 641655040 641720576 (32081507639151 / 50000) (32084744255331 / 50000) := by
  exact
    packedTile32768 641655040 641720576 13 3192 25330 29 _ _ (405591 / 20000) (1013979 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell641720576 :
    ThetaLowerSegment 641720576 641786112 (32084744255331 / 50000) (8022007896649 / 12500) := by
  exact
    packedTile32768 641720576 641786112 13 3242 25332 29 _ _ (405593 / 20000) (63374 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell641786112 :
    ThetaLowerSegment 641786112 641851648 (8022007896649 / 12500) (64182615560417 / 100000) := by
  exact
    packedTile32768 641786112 641851648 13 3231 25333 29 _ _ (81119 / 4000) (1013989 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell641851648 :
    ThetaLowerSegment 641851648 641917184 (64182615560417 / 100000) (64189076720627 / 100000) := by
  exact
    packedTile32768 641851648 641917184 13 3186 25334 29 _ _ (405597 / 20000) (506997 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell641917184 :
    ThetaLowerSegment 641917184 641982720 (64189076720627 / 100000) (32097780110321 / 50000) := by
  exact
    packedTile32768 641917184 641982720 13 3197 25336 29 _ _ (405599 / 20000) (1013999 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell641982720 :
    ThetaLowerSegment 641982720 642048256 (32097780110321 / 50000) (6420206606389 / 10000) := by
  exact
    packedTile32768 641982720 642048256 13 3208 25337 29 _ _ (1014003 / 50000) (2028009 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell642048256 :
    ThetaLowerSegment 642048256 642113792 (6420206606389 / 10000) (1284172533913 / 2000) := by
  exact
    packedTile32768 642048256 642113792 13 3235 25338 29 _ _ (126751 / 6250) (2028019 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell642113792 :
    ThetaLowerSegment 642113792 642179328 (1284172533913 / 2000) (32107499376671 / 50000) := by
  exact
    packedTile32768 642113792 642179328 13 3142 25339 29 _ _ (1014013 / 50000) (2028029 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell642179328 :
    ThetaLowerSegment 642179328 642244864 (32107499376671 / 50000) (32110842594017 / 50000) := by
  exact
    packedTile32768 642179328 642244864 13 3297 25341 29 _ _ (507009 / 25000) (2028039 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell642244864 :
    ThetaLowerSegment 642244864 642310400 (32110842594017 / 50000) (64228339210241 / 100000) := by
  exact
    packedTile32768 642244864 642310400 13 3281 25342 29 _ _ (2028047 / 100000) (40561 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell642310400 :
    ThetaLowerSegment 642310400 642375936 (64228339210241 / 100000) (64234897946579 / 100000) := by
  exact
    packedTile32768 642310400 642375936 13 3234 25343 29 _ _ (2028057 / 100000) (101403 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell642375936 :
    ThetaLowerSegment 642375936 642441472 (64234897946579 / 100000) (64241391817113 / 100000) := by
  exact
    packedTile32768 642375936 642441472 13 3202 25345 29 _ _ (2028067 / 100000) (202807 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell642441472 :
    ThetaLowerSegment 642441472 642507008 (64241391817113 / 100000) (64247885719667 / 100000) := by
  exact
    packedTile32768 642441472 642507008 13 3202 25346 29 _ _ (2028077 / 100000) (25351 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell642507008 :
    ThetaLowerSegment 642507008 642572544 (64247885719667 / 100000) (32127282105079 / 50000) := by
  exact
    packedTile32768 642507008 642572544 13 3293 25347 29 _ _ (2028087 / 100000) (202809 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell642572544 :
    ThetaLowerSegment 642572544 642638080 (32127282105079 / 50000) (16065277220601 / 25000) := by
  exact
    packedTile32768 642572544 642638080 13 3227 25349 29 _ _ (1014049 / 50000) (2028101 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell642638080 :
    ThetaLowerSegment 642638080 642703616 (16065277220601 / 25000) (8033448585933 / 12500) := by
  exact
    packedTile32768 642638080 642703616 13 3195 25350 29 _ _ (507027 / 25000) (2028111 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell642703616 :
    ThetaLowerSegment 642703616 642769152 (8033448585933 / 12500) (803426287531 / 1250) := by
  exact
    packedTile32768 642703616 642769152 13 3212 25351 29 _ _ (1014059 / 50000) (2028121 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell642769152 :
    ThetaLowerSegment 642769152 642834688 (803426287531 / 1250) (4017535415401 / 6250) := by
  exact
    packedTile32768 642769152 642834688 13 3187 25352 29 _ _ (63379 / 3125) (2028131 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell642834688 :
    ThetaLowerSegment 642834688 642900224 (4017535415401 / 6250) (8035901353313 / 12500) := by
  exact
    packedTile32768 642834688 642900224 13 3276 25354 29 _ _ (1014069 / 50000) (2028141 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell642900224 :
    ThetaLowerSegment 642900224 642965760 (8035901353313 / 12500) (64293743494433 / 100000) := by
  exact
    packedTile32768 642900224 642965760 13 3221 25355 29 _ _ (2028149 / 100000) (253519 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell642965760 :
    ThetaLowerSegment 642965760 643031296 (64293743494433 / 100000) (8037539594719 / 12500) := by
  exact
    packedTile32768 642965760 643031296 13 3241 25356 29 _ _ (2028159 / 100000) (1014081 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell643031296 :
    ThetaLowerSegment 643031296 643096832 (8037539594719 / 12500) (64306938729537 / 100000) := by
  exact
    packedTile32768 643031296 643096832 13 3265 25358 29 _ _ (2028169 / 100000) (507043 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell643096832 :
    ThetaLowerSegment 643096832 643162368 (64306938729537 / 100000) (12862682535381 / 20000) := by
  exact
    packedTile32768 643096832 643162368 13 3192 25359 29 _ _ (2028179 / 100000) (1014091 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell643162368 :
    ThetaLowerSegment 643162368 643227904 (12862682535381 / 20000) (1286398260453 / 2000) := by
  exact
    packedTile32768 643162368 643227904 13 3205 25360 29 _ _ (2028189 / 100000) (63381 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell643227904 :
    ThetaLowerSegment 643227904 643293440 (1286398260453 / 2000) (64326437738833 / 100000) := by
  exact
    packedTile32768 643227904 643293440 13 3217 25361 29 _ _ (2028199 / 100000) (1014101 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell643293440 :
    ThetaLowerSegment 643293440 643358976 (64326437738833 / 100000) (64333015223863 / 100000) := by
  exact
    packedTile32768 643293440 643358976 13 3243 25363 29 _ _ (202821 / 10000) (2028213 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell643358976 :
    ThetaLowerSegment 643358976 643424512 (64333015223863 / 100000) (64339481189223 / 100000) := by
  exact
    packedTile32768 643358976 643424512 13 3188 25364 29 _ _ (101411 / 5000) (2028223 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell643424512 :
    ThetaLowerSegment 643424512 643490048 (64339481189223 / 100000) (64345894452483 / 100000) := by
  exact
    packedTile32768 643424512 643490048 13 3162 25365 29 _ _ (202823 / 10000) (2028233 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell643490048 :
    ThetaLowerSegment 643490048 643555584 (64345894452483 / 100000) (64352611983363 / 100000) := by
  exact
    packedTile32768 643490048 643555584 13 3312 25367 29 _ _ (25353 / 1250) (2028243 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell643555584 :
    ThetaLowerSegment 643555584 643621120 (64352611983363 / 100000) (64359197711113 / 100000) := by
  exact
    packedTile32768 643555584 643621120 13 3247 25368 29 _ _ (8113 / 400) (2028253 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell643621120 :
    ThetaLowerSegment 643621120 643686656 (64359197711113 / 100000) (64365635411527 / 100000) := by
  exact
    packedTile32768 643621120 643686656 13 3174 25369 29 _ _ (2028261 / 100000) (253533 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell643686656 :
    ThetaLowerSegment 643686656 643752192 (64365635411527 / 100000) (64372178613773 / 100000) := by
  exact
    packedTile32768 643686656 643752192 13 3226 25370 29 _ _ (2028271 / 100000) (1014137 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell643752192 :
    ThetaLowerSegment 643752192 643817728 (64372178613773 / 100000) (64378843545139 / 100000) := by
  exact
    packedTile32768 643752192 643817728 13 3286 25372 29 _ _ (2028281 / 100000) (507071 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell643817728 :
    ThetaLowerSegment 643817728 643883264 (64378843545139 / 100000) (32192672108897 / 50000) := by
  exact
    packedTile32768 643817728 643883264 13 3205 25373 29 _ _ (2028291 / 100000) (1014147 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell643883264 :
    ThetaLowerSegment 643883264 643948800 (32192672108897 / 50000) (32195929560303 / 50000) := by
  exact
    packedTile32768 643883264 643948800 13 3212 25374 29 _ _ (2028301 / 100000) (126769 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell643948800 :
    ThetaLowerSegment 643948800 644014336 (32195929560303 / 50000) (12879685763987 / 20000) := by
  exact
    packedTile32768 643948800 644014336 13 3239 25376 29 _ _ (2028311 / 100000) (1014157 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell644014336 :
    ThetaLowerSegment 644014336 644079872 (12879685763987 / 20000) (12880973748457 / 20000) := by
  exact
    packedTile32768 644014336 644079872 13 3175 25377 29 _ _ (1014161 / 50000) (81133 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell644079872 :
    ThetaLowerSegment 644079872 644145408 (12880973748457 / 20000) (64411393886329 / 100000) := by
  exact
    packedTile32768 644079872 644145408 13 3217 25378 29 _ _ (507083 / 25000) (405667 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell644145408 :
    ThetaLowerSegment 644145408 644210944 (64411393886329 / 100000) (12883584218177 / 20000) := by
  exact
    packedTile32768 644145408 644210944 13 3218 25380 29 _ _ (1014171 / 50000) (405669 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell644210944 :
    ThetaLowerSegment 644210944 644276480 (12883584218177 / 20000) (64424436157509 / 100000) := by
  exact
    packedTile32768 644210944 644276480 13 3212 25381 29 _ _ (63386 / 3125) (405671 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell644276480 :
    ThetaLowerSegment 644276480 644342016 (64424436157509 / 100000) (64430930972633 / 100000) := by
  exact
    packedTile32768 644276480 644342016 13 3202 25382 29 _ _ (1014181 / 50000) (405673 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell644342016 :
    ThetaLowerSegment 644342016 644407552 (64430930972633 / 100000) (12887502202929 / 20000) := by
  exact
    packedTile32768 644342016 644407552 13 3244 25383 29 _ _ (2028373 / 100000) (253547 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell644407552 :
    ThetaLowerSegment 644407552 644473088 (12887502202929 / 20000) (64443985613181 / 100000) := by
  exact
    packedTile32768 644407552 644473088 13 3192 25385 29 _ _ (2028383 / 100000) (1014193 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell644473088 :
    ThetaLowerSegment 644473088 644538624 (64443985613181 / 100000) (64450500811497 / 100000) := by
  exact
    packedTile32768 644473088 644538624 13 3212 25386 29 _ _ (2028393 / 100000) (507099 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell644538624 :
    ThetaLowerSegment 644538624 644604160 (64450500811497 / 100000) (64456955189843 / 100000) := by
  exact
    packedTile32768 644538624 644604160 13 3182 25387 29 _ _ (2028403 / 100000) (1014203 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell644604160 :
    ThetaLowerSegment 644604160 644669696 (64456955189843 / 100000) (64463604327657 / 100000) := by
  exact
    packedTile32768 644604160 644669696 13 3278 25389 29 _ _ (2028413 / 100000) (63388 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell644669696 :
    ThetaLowerSegment 644669696 644735232 (64463604327657 / 100000) (64470253498251 / 100000) := by
  exact
    packedTile32768 644669696 644735232 13 3278 25390 29 _ _ (2028423 / 100000) (1014213 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell644735232 :
    ThetaLowerSegment 644735232 644800768 (64470253498251 / 100000) (64476681605597 / 100000) := by
  exact
    packedTile32768 644735232 644800768 13 3169 25391 29 _ _ (1014217 / 50000) (2028437 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell644800768 :
    ThetaLowerSegment 644800768 644866304 (64476681605597 / 100000) (64483219280609 / 100000) := by
  exact
    packedTile32768 644800768 644866304 13 3223 25392 29 _ _ (507111 / 25000) (2028447 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell644866304 :
    ThetaLowerSegment 644866304 644931840 (64483219280609 / 100000) (64489724532587 / 100000) := by
  exact
    packedTile32768 644866304 644931840 13 3207 25394 29 _ _ (1014227 / 50000) (2028457 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell644931840 :
    ThetaLowerSegment 644931840 644997376 (64489724532587 / 100000) (64496345439083 / 100000) := by
  exact
    packedTile32768 644931840 644997376 13 3264 25395 29 _ _ (126779 / 6250) (2028467 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell644997376 :
    ThetaLowerSegment 644997376 645062912 (64496345439083 / 100000) (64502871039941 / 100000) := by
  exact
    packedTile32768 644997376 645062912 13 3217 25396 29 _ _ (1014237 / 50000) (2028477 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell645062912 :
    ThetaLowerSegment 645062912 645128448 (64502871039941 / 100000) (64509431157197 / 100000) := by
  exact
    packedTile32768 645062912 645128448 13 3234 25398 29 _ _ (507121 / 25000) (2028487 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell645128448 :
    ThetaLowerSegment 645128448 645193984 (64509431157197 / 100000) (64515932480467 / 100000) := by
  exact
    packedTile32768 645128448 645193984 13 3205 25399 29 _ _ (1014247 / 50000) (2028497 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell645193984 :
    ThetaLowerSegment 645193984 645259520 (64515932480467 / 100000) (32261247347071 / 50000) := by
  exact
    packedTile32768 645193984 645259520 13 3235 25400 29 _ _ (405701 / 20000) (507127 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell645259520 :
    ThetaLowerSegment 645259520 645325056 (32261247347071 / 50000) (32264505142161 / 50000) := by
  exact
    packedTile32768 645259520 645325056 13 3212 25401 29 _ _ (405703 / 20000) (1014259 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell645325056 :
    ThetaLowerSegment 645325056 645390592 (32264505142161 / 50000) (32267848151361 / 50000) := by
  exact
    packedTile32768 645325056 645390592 13 3296 25403 29 _ _ (81141 / 4000) (126783 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell645390592 :
    ThetaLowerSegment 645390592 645456128 (32267848151361 / 50000) (64542295127077 / 100000) := by
  exact
    packedTile32768 645390592 645456128 13 3253 25404 29 _ _ (405707 / 20000) (1014269 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell645456128 :
    ThetaLowerSegment 645456128 645521664 (64542295127077 / 100000) (16137248852803 / 25000) := by
  exact
    packedTile32768 645456128 645521664 13 3303 25405 29 _ _ (405709 / 20000) (507137 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell645521664 :
    ThetaLowerSegment 645521664 645587200 (16137248852803 / 25000) (64555663271497 / 100000) := by
  exact
    packedTile32768 645521664 645587200 13 3287 25407 29 _ _ (405711 / 20000) (1014279 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell645587200 :
    ThetaLowerSegment 645587200 645652736 (64555663271497 / 100000) (64562112082811 / 100000) := by
  exact
    packedTile32768 645587200 645652736 13 3179 25408 29 _ _ (1014283 / 50000) (2028569 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell645652736 :
    ThetaLowerSegment 645652736 645718272 (64562112082811 / 100000) (64568719154843 / 100000) := by
  exact
    packedTile32768 645652736 645718272 13 3257 25409 29 _ _ (63393 / 3125) (2028579 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell645718272 :
    ThetaLowerSegment 645718272 645783808 (64568719154843 / 100000) (64575324230859 / 100000) := by
  exact
    packedTile32768 645718272 645783808 13 3256 25410 29 _ _ (1014293 / 50000) (2028589 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell645783808 :
    ThetaLowerSegment 645783808 645849344 (64575324230859 / 100000) (12916373696311 / 20000) := by
  exact
    packedTile32768 645783808 645849344 13 3226 25412 29 _ _ (507149 / 25000) (2028599 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell645849344 :
    ThetaLowerSegment 645849344 645914880 (12916373696311 / 20000) (12917688232999 / 20000) := by
  exact
    packedTile32768 645849344 645914880 13 3240 25413 29 _ _ (1014303 / 50000) (2028609 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell645914880 :
    ThetaLowerSegment 645914880 645980416 (12917688232999 / 20000) (12919010890631 / 20000) := by
  exact
    packedTile32768 645914880 645980416 13 3260 25414 29 _ _ (253577 / 12500) (2028619 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell645980416 :
    ThetaLowerSegment 645980416 646045952 (12919010890631 / 20000) (64601562285363 / 100000) := by
  exact
    packedTile32768 645980416 646045952 13 3208 25416 29 _ _ (1014313 / 50000) (2028629 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell646045952 :
    ThetaLowerSegment 646045952 646111488 (64601562285363 / 100000) (64608143183791 / 100000) := by
  exact
    packedTile32768 646045952 646111488 13 3244 25417 29 _ _ (2028637 / 100000) (12679 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell646111488 :
    ThetaLowerSegment 646111488 646177024 (64608143183791 / 100000) (4038421651861 / 6250) := by
  exact
    packedTile32768 646111488 646177024 13 3255 25418 29 _ _ (2028647 / 100000) (40573 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell646177024 :
    ThetaLowerSegment 646177024 646242560 (4038421651861 / 6250) (32310588636233 / 50000) := by
  exact
    packedTile32768 646177024 646242560 13 3170 25420 29 _ _ (2028657 / 100000) (101433 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell646242560 :
    ThetaLowerSegment 646242560 646308096 (32310588636233 / 50000) (32313830446099 / 50000) := by
  exact
    packedTile32768 646242560 646308096 13 3196 25421 29 _ _ (2028667 / 100000) (202867 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell646308096 :
    ThetaLowerSegment 646308096 646373632 (32313830446099 / 50000) (64634199318169 / 100000) := by
  exact
    packedTile32768 646308096 646373632 13 3223 25422 29 _ _ (2028677 / 100000) (50717 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell646373632 :
    ThetaLowerSegment 646373632 646439168 (64634199318169 / 100000) (32320441920917 / 50000) := by
  exact
    packedTile32768 646373632 646439168 13 3295 25423 29 _ _ (2028687 / 100000) (202869 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell646439168 :
    ThetaLowerSegment 646439168 646504704 (32320441920917 / 50000) (12929492581241 / 20000) := by
  exact
    packedTile32768 646439168 646504704 13 3243 25425 29 _ _ (2028697 / 100000) (20287 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell646504704 :
    ThetaLowerSegment 646504704 646570240 (12929492581241 / 20000) (64654044034957 / 100000) := by
  exact
    packedTile32768 646504704 646570240 13 3244 25426 29 _ _ (507177 / 25000) (2028711 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell646570240 :
    ThetaLowerSegment 646570240 646635776 (64654044034957 / 100000) (64660604908969 / 100000) := by
  exact
    packedTile32768 646570240 646635776 13 3234 25427 29 _ _ (1014359 / 50000) (2028721 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell646635776 :
    ThetaLowerSegment 646635776 646701312 (64660604908969 / 100000) (12933434380301 / 20000) := by
  exact
    packedTile32768 646635776 646701312 13 3237 25429 29 _ _ (253591 / 12500) (2028731 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell646701312 :
    ThetaLowerSegment 646701312 646766848 (12933434380301 / 20000) (64673621259607 / 100000) := by
  exact
    packedTile32768 646701312 646766848 13 3179 25430 29 _ _ (1014369 / 50000) (2028741 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell646766848 :
    ThetaLowerSegment 646766848 646832384 (64673621259607 / 100000) (64680157885663 / 100000) := by
  exact
    packedTile32768 646766848 646832384 13 3222 25431 29 _ _ (507187 / 25000) (2028751 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell646832384 :
    ThetaLowerSegment 646832384 646897920 (64680157885663 / 100000) (64686623537409 / 100000) := by
  exact
    packedTile32768 646832384 646897920 13 3187 25432 29 _ _ (1014379 / 50000) (2028761 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell646897920 :
    ThetaLowerSegment 646897920 646963456 (64686623537409 / 100000) (12938634074349 / 20000) := by
  exact
    packedTile32768 646897920 646963456 13 3227 25434 29 _ _ (63399 / 3125) (2028771 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell646963456 :
    ThetaLowerSegment 646963456 647028992 (12938634074349 / 20000) (64699719270357 / 100000) := by
  exact
    packedTile32768 646963456 647028992 13 3228 25435 29 _ _ (2028779 / 100000) (1014391 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell647028992 :
    ThetaLowerSegment 647028992 647094528 (64699719270357 / 100000) (32353179748377 / 50000) := by
  exact
    packedTile32768 647028992 647094528 13 3273 25436 29 _ _ (2028789 / 100000) (253599 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell647094528 :
    ThetaLowerSegment 647094528 647160064 (32353179748377 / 50000) (32356482633149 / 50000) := by
  exact
    packedTile32768 647094528 647160064 13 3256 25438 29 _ _ (2028799 / 100000) (1014401 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell647160064 :
    ThetaLowerSegment 647160064 647225600 (32356482633149 / 50000) (8089935732303 / 12500) := by
  exact
    packedTile32768 647160064 647225600 13 3214 25439 29 _ _ (2028809 / 100000) (507203 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell647225600 :
    ThetaLowerSegment 647225600 647291136 (8089935732303 / 12500) (12945219555909 / 20000) := by
  exact
    packedTile32768 647225600 647291136 13 3259 25440 29 _ _ (2028819 / 100000) (1014411 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell647291136 :
    ThetaLowerSegment 647291136 647356672 (12945219555909 / 20000) (64732654954873 / 100000) := by
  exact
    packedTile32768 647291136 647356672 13 3232 25441 29 _ _ (2028829 / 100000) (63401 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell647356672 :
    ThetaLowerSegment 647356672 647422208 (64732654954873 / 100000) (64739248681623 / 100000) := by
  exact
    packedTile32768 647356672 647422208 13 3250 25443 29 _ _ (2028839 / 100000) (1014421 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell647422208 :
    ThetaLowerSegment 647422208 647487744 (64739248681623 / 100000) (64745773460007 / 100000) := by
  exact
    packedTile32768 647422208 647487744 13 3216 25444 29 _ _ (2028849 / 100000) (507213 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell647487744 :
    ThetaLowerSegment 647487744 647553280 (64745773460007 / 100000) (64752259725427 / 100000) := by
  exact
    packedTile32768 647487744 647553280 13 3197 25445 29 _ _ (101443 / 5000) (2028863 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell647553280 :
    ThetaLowerSegment 647553280 647618816 (64752259725427 / 100000) (64758835293097 / 100000) := by
  exact
    packedTile32768 647553280 647618816 13 3241 25447 29 _ _ (202887 / 10000) (2028873 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell647618816 :
    ThetaLowerSegment 647618816 647684352 (64758835293097 / 100000) (64765512337177 / 100000) := by
  exact
    packedTile32768 647618816 647684352 13 3291 25448 29 _ _ (25361 / 1250) (2028883 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell647684352 :
    ThetaLowerSegment 647684352 647749888 (64765512337177 / 100000) (64772065651877 / 100000) := by
  exact
    packedTile32768 647684352 647749888 13 3230 25449 29 _ _ (202889 / 10000) (2028893 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell647749888 :
    ThetaLowerSegment 647749888 647815424 (64772065651877 / 100000) (64778604796577 / 100000) := by
  exact
    packedTile32768 647749888 647815424 13 3223 25450 29 _ _ (20289 / 1000) (2028903 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell647815424 :
    ThetaLowerSegment 647815424 647880960 (64778604796577 / 100000) (64785164262607 / 100000) := by
  exact
    packedTile32768 647815424 647880960 13 3233 25452 29 _ _ (202891 / 10000) (2028913 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell647880960 :
    ThetaLowerSegment 647880960 647946496 (64785164262607 / 100000) (64791760281527 / 100000) := by
  exact
    packedTile32768 647880960 647946496 13 3251 25453 29 _ _ (50723 / 2500) (2028923 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell647946496 :
    ThetaLowerSegment 647946496 648012032 (64791760281527 / 100000) (64798252857527 / 100000) := by
  exact
    packedTile32768 647946496 648012032 13 3200 25454 29 _ _ (202893 / 10000) (2028933 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell648012032 :
    ThetaLowerSegment 648012032 648077568 (64798252857527 / 100000) (64804816478427 / 100000) := by
  exact
    packedTile32768 648012032 648077568 13 3235 25456 29 _ _ (101447 / 5000) (2028943 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell648077568 :
    ThetaLowerSegment 648077568 648143104 (64804816478427 / 100000) (32405655575289 / 50000) := by
  exact
    packedTile32768 648077568 648143104 13 3201 25457 29 _ _ (2028951 / 100000) (1014477 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell648143104 :
    ThetaLowerSegment 648143104 648208640 (32405655575289 / 50000) (64817862665647 / 100000) := by
  exact
    packedTile32768 648143104 648208640 13 3229 25458 29 _ _ (2028961 / 100000) (507241 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell648208640 :
    ThetaLowerSegment 648208640 648274176 (64817862665647 / 100000) (518595946743 / 800) := by
  exact
    packedTile32768 648208640 648274176 13 3268 25459 29 _ _ (2028971 / 100000) (1014487 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell648274176 :
    ThetaLowerSegment 648274176 648339712 (518595946743 / 800) (16207744998783 / 25000) := by
  exact
    packedTile32768 648274176 648339712 13 3197 25461 29 _ _ (2028981 / 100000) (253623 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell648339712 :
    ThetaLowerSegment 648339712 648405248 (16207744998783 / 25000) (32418791165923 / 50000) := by
  exact
    packedTile32768 648339712 648405248 13 3254 25462 29 _ _ (2028991 / 100000) (1014497 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell648405248 :
    ThetaLowerSegment 648405248 648470784 (32418791165923 / 50000) (64844247600131 / 100000) := by
  exact
    packedTile32768 648405248 648470784 13 3285 25463 29 _ _ (2029001 / 100000) (507251 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell648470784 :
    ThetaLowerSegment 648470784 648536320 (64844247600131 / 100000) (32425350942061 / 50000) := by
  exact
    packedTile32768 648470784 648536320 13 3181 25465 29 _ _ (2029011 / 100000) (1014507 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell648536320 :
    ThetaLowerSegment 648536320 648601856 (32425350942061 / 50000) (64857310405519 / 100000) := by
  exact
    packedTile32768 648536320 648601856 13 3257 25466 29 _ _ (2029021 / 100000) (63407 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell648601856 :
    ThetaLowerSegment 648601856 648667392 (64857310405519 / 100000) (16215984812449 / 25000) := by
  exact
    packedTile32768 648601856 648667392 13 3267 25467 29 _ _ (2029031 / 100000) (1014517 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell648667392 :
    ThetaLowerSegment 648667392 648732928 (16215984812449 / 25000) (4054400743361 / 6250) := by
  exact
    packedTile32768 648667392 648732928 13 3190 25468 29 _ _ (1014521 / 50000) (405809 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell648732928 :
    ThetaLowerSegment 648732928 648798464 (4054400743361 / 6250) (16219213533469 / 25000) := by
  exact
    packedTile32768 648732928 648798464 13 3175 25470 29 _ _ (507263 / 25000) (405811 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell648798464 :
    ThetaLowerSegment 648798464 648864000 (16219213533469 / 25000) (16220844899317 / 25000) := by
  exact
    packedTile32768 648798464 648864000 13 3216 25471 29 _ _ (1014531 / 50000) (405813 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell648864000 :
    ThetaLowerSegment 648864000 648929536 (16220844899317 / 25000) (16222480838617 / 25000) := by
  exact
    packedTile32768 648864000 648929536 13 3225 25472 29 _ _ (126817 / 6250) (81163 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell648929536 :
    ThetaLowerSegment 648929536 648995072 (16222480838617 / 25000) (16224134540447 / 25000) := by
  exact
    packedTile32768 648929536 648995072 13 3260 25474 29 _ _ (1014541 / 50000) (405817 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell648995072 :
    ThetaLowerSegment 648995072 649060608 (16224134540447 / 25000) (16225780134059 / 25000) := by
  exact
    packedTile32768 648995072 649060608 13 3244 25475 29 _ _ (507273 / 25000) (405819 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell649060608 :
    ThetaLowerSegment 649060608 649126144 (16225780134059 / 25000) (16227401386557 / 25000) := by
  exact
    packedTile32768 649060608 649126144 13 3196 25476 29 _ _ (1014551 / 50000) (405821 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell649126144 :
    ThetaLowerSegment 649126144 649191680 (16227401386557 / 25000) (16229031778049 / 25000) := by
  exact
    packedTile32768 649126144 649191680 13 3214 25477 29 _ _ (253639 / 12500) (405823 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell649191680 :
    ThetaLowerSegment 649191680 649257216 (16229031778049 / 25000) (32461365952153 / 50000) := by
  exact
    packedTile32768 649191680 649257216 13 3255 25479 29 _ _ (1014561 / 50000) (16233 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell649257216 :
    ThetaLowerSegment 649257216 649322752 (32461365952153 / 50000) (32464649087729 / 50000) := by
  exact
    packedTile32768 649257216 649322752 13 3236 25480 29 _ _ (507283 / 25000) (405827 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell649322752 :
    ThetaLowerSegment 649322752 649339136 (32464649087729 / 50000) (6493092960643 / 10000) := by
  exact
    packedTile32768 649322752 649339136 11 804 25481 29 _ _ (2029143 / 100000) (1014573 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell649339136 :
    ThetaLowerSegment 649339136 649341184 (6493092960643 / 10000) (12986227721673 / 20000) := by
  exact
    packedTile32768 649339136 649341184 8 103 25482 29 _ _ (405829 / 20000) (507287 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_617341184_649341184 :
    ThetaLowerSegment 617341184 649341184 (1929110684964 / 3125) (12986227721673 / 20000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell617341184 cell617406720)
                    (ThetaLowerSegment.join cell617472256 cell617537792))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell617603328 cell617668864)
                    (ThetaLowerSegment.join cell617734400 cell617799936)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell617865472 cell617931008)
                    (ThetaLowerSegment.join cell617996544 cell618062080))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell618127616 cell618193152)
                    (ThetaLowerSegment.join cell618258688 cell618324224))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell618389760 cell618455296)
                    (ThetaLowerSegment.join cell618520832 cell618586368))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell618651904 cell618717440)
                    (ThetaLowerSegment.join cell618782976 cell618848512)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell618914048 cell618979584)
                    (ThetaLowerSegment.join cell619045120 cell619110656))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell619176192 cell619241728)
                    (ThetaLowerSegment.join cell619307264 cell619372800)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell619438336 cell619503872)
                    (ThetaLowerSegment.join cell619569408 cell619634944))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell619700480 cell619766016)
                    (ThetaLowerSegment.join cell619831552 cell619897088)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell619962624 cell620028160)
                    (ThetaLowerSegment.join cell620093696 cell620159232))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell620224768 cell620290304)
                    (ThetaLowerSegment.join cell620355840 cell620421376))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell620486912 cell620552448)
                    (ThetaLowerSegment.join cell620617984 cell620683520))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell620749056 cell620814592)
                    (ThetaLowerSegment.join cell620880128 cell620945664)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell621011200 cell621076736)
                    (ThetaLowerSegment.join cell621142272 cell621207808))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell621273344 cell621338880)
                    (ThetaLowerSegment.join cell621404416 cell621469952))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell621535488 cell621601024)
                    (ThetaLowerSegment.join cell621666560 cell621732096))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell621797632 cell621863168)
                    (ThetaLowerSegment.join cell621928704 cell621994240)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell622059776 cell622125312)
                    (ThetaLowerSegment.join cell622190848 cell622256384))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell622321920 cell622387456)
                    (ThetaLowerSegment.join cell622452992 cell622518528))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell622584064 cell622649600)
                    (ThetaLowerSegment.join cell622715136 cell622780672))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell622846208 cell622911744)
                    (ThetaLowerSegment.join cell622977280 cell623042816)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell623108352 cell623173888)
                    (ThetaLowerSegment.join cell623239424 cell623304960))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell623370496 cell623436032)
                    (ThetaLowerSegment.join cell623501568 cell623567104)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell623632640 cell623698176)
                    (ThetaLowerSegment.join cell623763712 cell623829248))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell623894784 cell623960320)
                    (ThetaLowerSegment.join cell624025856 cell624091392)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell624156928 cell624222464)
                    (ThetaLowerSegment.join cell624288000 cell624353536))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell624419072 cell624484608)
                    (ThetaLowerSegment.join cell624550144 cell624615680))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell624681216 cell624746752)
                    (ThetaLowerSegment.join cell624812288 cell624877824))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell624943360 cell625008896)
                    (ThetaLowerSegment.join cell625074432 cell625139968)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell625205504 cell625271040)
                    (ThetaLowerSegment.join cell625336576 cell625402112))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell625467648 cell625533184)
                    (ThetaLowerSegment.join cell625598720 cell625664256)))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell625729792 cell625795328)
                    (ThetaLowerSegment.join cell625860864 cell625926400))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell625991936 cell626057472)
                    (ThetaLowerSegment.join cell626123008 cell626188544)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell626254080 cell626319616)
                    (ThetaLowerSegment.join cell626385152 cell626450688))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell626516224 cell626581760)
                    (ThetaLowerSegment.join cell626647296 cell626712832))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell626778368 cell626843904)
                    (ThetaLowerSegment.join cell626909440 cell626974976))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell627040512 cell627106048)
                    (ThetaLowerSegment.join cell627171584 cell627237120)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell627302656 cell627368192)
                    (ThetaLowerSegment.join cell627433728 cell627499264))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell627564800 cell627630336)
                    (ThetaLowerSegment.join cell627695872 cell627761408)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell627826944 cell627892480)
                    (ThetaLowerSegment.join cell627958016 cell628023552))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell628089088 cell628154624)
                    (ThetaLowerSegment.join cell628220160 cell628285696)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell628351232 cell628416768)
                    (ThetaLowerSegment.join cell628482304 cell628547840))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell628613376 cell628678912)
                    (ThetaLowerSegment.join cell628744448 cell628809984))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell628875520 cell628941056)
                    (ThetaLowerSegment.join cell629006592 cell629072128))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell629137664 cell629203200)
                    (ThetaLowerSegment.join cell629268736 cell629334272)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell629399808 cell629465344)
                    (ThetaLowerSegment.join cell629530880 cell629596416))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell629661952 cell629727488)
                    (ThetaLowerSegment.join cell629793024 cell629858560))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell629924096 cell629989632)
                    (ThetaLowerSegment.join cell630055168 cell630120704))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell630186240 cell630251776)
                    (ThetaLowerSegment.join cell630317312 cell630382848)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell630448384 cell630513920)
                    (ThetaLowerSegment.join cell630579456 cell630644992))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell630710528 cell630776064)
                    (ThetaLowerSegment.join cell630841600 cell630907136))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell630972672 cell631038208)
                    (ThetaLowerSegment.join cell631103744 cell631169280))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell631234816 cell631300352)
                    (ThetaLowerSegment.join cell631365888 cell631431424)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell631496960 cell631562496)
                    (ThetaLowerSegment.join cell631628032 cell631693568))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell631759104 cell631824640)
                    (ThetaLowerSegment.join cell631890176 cell631955712)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell632021248 cell632086784)
                    (ThetaLowerSegment.join cell632152320 cell632217856))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell632283392 cell632348928)
                    (ThetaLowerSegment.join cell632414464 cell632480000)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell632545536 cell632611072)
                    (ThetaLowerSegment.join cell632676608 cell632742144))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell632807680 cell632873216)
                    (ThetaLowerSegment.join cell632938752 cell633004288))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell633069824 cell633135360)
                    (ThetaLowerSegment.join cell633200896 cell633266432))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell633331968 cell633397504)
                    (ThetaLowerSegment.join cell633463040 cell633528576)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell633594112 cell633659648)
                    (ThetaLowerSegment.join cell633725184 cell633790720))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell633856256 cell633921792)
                    (ThetaLowerSegment.join cell633987328 cell634052864))))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell634118400 cell634183936)
                    (ThetaLowerSegment.join cell634249472 cell634315008))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell634380544 cell634446080)
                    (ThetaLowerSegment.join cell634511616 cell634577152)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell634642688 cell634708224)
                    (ThetaLowerSegment.join cell634773760 cell634839296))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell634904832 cell634970368)
                    (ThetaLowerSegment.join cell635035904 cell635101440))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell635166976 cell635232512)
                    (ThetaLowerSegment.join cell635298048 cell635363584))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell635429120 cell635494656)
                    (ThetaLowerSegment.join cell635560192 cell635625728)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell635691264 cell635756800)
                    (ThetaLowerSegment.join cell635822336 cell635887872))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell635953408 cell636018944)
                    (ThetaLowerSegment.join cell636084480 cell636150016)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell636215552 cell636281088)
                    (ThetaLowerSegment.join cell636346624 cell636412160))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell636477696 cell636543232)
                    (ThetaLowerSegment.join cell636608768 cell636674304)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell636739840 cell636805376)
                    (ThetaLowerSegment.join cell636870912 cell636936448))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell637001984 cell637067520)
                    (ThetaLowerSegment.join cell637133056 cell637198592))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell637264128 cell637329664)
                    (ThetaLowerSegment.join cell637395200 cell637460736))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell637526272 cell637591808)
                    (ThetaLowerSegment.join cell637657344 cell637722880)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell637788416 cell637853952)
                    (ThetaLowerSegment.join cell637919488 cell637985024))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell638050560 cell638116096)
                    (ThetaLowerSegment.join cell638181632 cell638247168))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell638312704 cell638378240)
                    (ThetaLowerSegment.join cell638443776 cell638509312))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell638574848 cell638640384)
                    (ThetaLowerSegment.join cell638705920 cell638771456)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell638836992 cell638902528)
                    (ThetaLowerSegment.join cell638968064 cell639033600))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell639099136 cell639164672)
                    (ThetaLowerSegment.join cell639230208 cell639295744))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell639361280 cell639426816)
                    (ThetaLowerSegment.join cell639492352 cell639557888))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell639623424 cell639688960)
                    (ThetaLowerSegment.join cell639754496 cell639820032)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell639885568 cell639951104)
                    (ThetaLowerSegment.join cell640016640 cell640082176))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell640147712 cell640213248)
                    (ThetaLowerSegment.join cell640278784 cell640344320)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell640409856 cell640475392)
                    (ThetaLowerSegment.join cell640540928 cell640606464))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell640672000 cell640737536)
                    (ThetaLowerSegment.join cell640803072 cell640868608)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell640934144 cell640999680)
                    (ThetaLowerSegment.join cell641065216 cell641130752))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell641196288 cell641261824)
                    (ThetaLowerSegment.join cell641327360 cell641392896))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell641458432 cell641523968)
                    (ThetaLowerSegment.join cell641589504 cell641655040))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell641720576 cell641786112)
                    (ThetaLowerSegment.join cell641851648 cell641917184)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell641982720 cell642048256)
                    (ThetaLowerSegment.join cell642113792 cell642179328))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell642244864 cell642310400)
                    (ThetaLowerSegment.join cell642375936 cell642441472)))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell642507008 cell642572544)
                    (ThetaLowerSegment.join cell642638080 cell642703616))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell642769152 cell642834688)
                    (ThetaLowerSegment.join cell642900224 cell642965760)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell643031296 cell643096832)
                    (ThetaLowerSegment.join cell643162368 cell643227904))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell643293440 cell643358976)
                    (ThetaLowerSegment.join cell643424512 cell643490048))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell643555584 cell643621120)
                    (ThetaLowerSegment.join cell643686656 cell643752192))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell643817728 cell643883264)
                    (ThetaLowerSegment.join cell643948800 cell644014336)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell644079872 cell644145408)
                    (ThetaLowerSegment.join cell644210944 cell644276480))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell644342016 cell644407552)
                    (ThetaLowerSegment.join cell644473088 cell644538624)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell644604160 cell644669696)
                    (ThetaLowerSegment.join cell644735232 cell644800768))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell644866304 cell644931840)
                    (ThetaLowerSegment.join cell644997376 cell645062912)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell645128448 cell645193984)
                    (ThetaLowerSegment.join cell645259520 cell645325056))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell645390592 cell645456128)
                    (ThetaLowerSegment.join cell645521664 cell645587200))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell645652736 cell645718272)
                    (ThetaLowerSegment.join cell645783808 cell645849344))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell645914880 cell645980416)
                    (ThetaLowerSegment.join cell646045952 cell646111488)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell646177024 cell646242560)
                    (ThetaLowerSegment.join cell646308096 cell646373632))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell646439168 cell646504704)
                    (ThetaLowerSegment.join cell646570240 cell646635776))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell646701312 cell646766848)
                    (ThetaLowerSegment.join cell646832384 cell646897920))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell646963456 cell647028992)
                    (ThetaLowerSegment.join cell647094528 cell647160064)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell647225600 cell647291136)
                    (ThetaLowerSegment.join cell647356672 cell647422208))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell647487744 cell647553280)
                    (ThetaLowerSegment.join cell647618816 cell647684352))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell647749888 cell647815424)
                    (ThetaLowerSegment.join cell647880960 cell647946496))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell648012032 cell648077568)
                    (ThetaLowerSegment.join cell648143104 cell648208640)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell648274176 cell648339712)
                    (ThetaLowerSegment.join cell648405248 cell648470784))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell648536320 cell648601856)
                    (ThetaLowerSegment.join cell648667392 cell648732928)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell648798464 cell648864000)
                  (ThetaLowerSegment.join cell648929536 cell648995072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell649060608 cell649126144)
                  (ThetaLowerSegment.join cell649191680 cell649257216)))
              (ThetaLowerSegment.join cell649322752 cell649339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
