/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis32768

/-! # Direct theta estimate up to 425341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell393341184 :
    ThetaLowerSegment 393341184 393406720 (19665892057069 / 50000) (19669177225289 / 50000) := by
  exact
    packedTile32768 393341184 393406720 13 3320 19832 29 _ _ (1979017 / 100000) (98951 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell393406720 :
    ThetaLowerSegment 393406720 393472256 (19669177225289 / 50000) (19672474295933 / 50000) := by
  exact
    packedTile32768 393406720 393472256 13 3332 19834 29 _ _ (989517 / 50000) (1979037 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell393472256 :
    ThetaLowerSegment 393472256 393537792 (19672474295933 / 50000) (9837878770771 / 25000) := by
  exact
    packedTile32768 393472256 393537792 13 3318 19836 29 _ _ (1979051 / 100000) (989527 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell393537792 :
    ThetaLowerSegment 393537792 393603328 (9837878770771 / 25000) (19678973525417 / 50000) := by
  exact
    packedTile32768 393537792 393603328 13 3250 19837 29 _ _ (1979067 / 100000) (197907 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell393603328 :
    ThetaLowerSegment 393603328 393668864 (19678973525417 / 50000) (19682259794399 / 50000) := by
  exact
    packedTile32768 393603328 393668864 13 3321 19839 29 _ _ (494771 / 25000) (1979087 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell393668864 :
    ThetaLowerSegment 393668864 393734400 (19682259794399 / 50000) (39371100099623 / 100000) := by
  exact
    packedTile32768 393668864 393734400 13 3325 19841 29 _ _ (1979101 / 100000) (61847 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell393734400 :
    ThetaLowerSegment 393734400 393799936 (39371100099623 / 100000) (39377615352787 / 100000) := by
  exact
    packedTile32768 393734400 393799936 13 3292 19842 29 _ _ (1979117 / 100000) (24739 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell393799936 :
    ThetaLowerSegment 393799936 393865472 (39377615352787 / 100000) (7876839986321 / 20000) := by
  exact
    packedTile32768 393799936 393865472 13 3327 19844 29 _ _ (989567 / 50000) (1979137 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell393865472 :
    ThetaLowerSegment 393865472 393931008 (7876839986321 / 20000) (7878143454511 / 20000) := by
  exact
    packedTile32768 393865472 393931008 13 3293 19846 29 _ _ (39583 / 2000) (1979153 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell393931008 :
    ThetaLowerSegment 393931008 393996544 (7878143454511 / 20000) (19698652959749 / 50000) := by
  exact
    packedTile32768 393931008 393996544 13 3329 19847 29 _ _ (1979167 / 100000) (197917 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell393996544 :
    ThetaLowerSegment 393996544 394062080 (19698652959749 / 50000) (19701965124173 / 50000) := by
  exact
    packedTile32768 393996544 394062080 13 3347 19849 29 _ _ (123699 / 6250) (1979187 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell394062080 :
    ThetaLowerSegment 394062080 394127616 (19701965124173 / 50000) (19705229814573 / 50000) := by
  exact
    packedTile32768 394062080 394127616 13 3299 19850 29 _ _ (2474 / 125) (1979203 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell394127616 :
    ThetaLowerSegment 394127616 394193152 (19705229814573 / 50000) (9854270522307 / 25000) := by
  exact
    packedTile32768 394127616 394193152 13 3346 19852 29 _ _ (1979217 / 100000) (98961 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell394193152 :
    ThetaLowerSegment 394193152 394258688 (9854270522307 / 25000) (19711837458841 / 50000) := by
  exact
    packedTile32768 394193152 394258688 13 3331 19854 29 _ _ (989617 / 50000) (1979237 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell394258688 :
    ThetaLowerSegment 394258688 394324224 (19711837458841 / 50000) (9857548146983 / 25000) := by
  exact
    packedTile32768 394258688 394324224 13 3293 19855 29 _ _ (7917 / 400) (1979253 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell394324224 :
    ThetaLowerSegment 394324224 394389760 (9857548146983 / 25000) (492959645893 / 1250) := by
  exact
    packedTile32768 394324224 394389760 13 3324 19857 29 _ _ (1979267 / 100000) (197927 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell394389760 :
    ThetaLowerSegment 394389760 394455296 (492959645893 / 1250) (1972159722401 / 5000) := by
  exact
    packedTile32768 394389760 394455296 13 3245 19859 29 _ _ (494821 / 25000) (1979287 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell394455296 :
    ThetaLowerSegment 394455296 394520832 (1972159722401 / 5000) (493121453019 / 1250) := by
  exact
    packedTile32768 394455296 394520832 13 3295 19860 29 _ _ (19793 / 1000) (1979303 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell394520832 :
    ThetaLowerSegment 394520832 394586368 (493121453019 / 1250) (19728129931761 / 50000) := by
  exact
    packedTile32768 394520832 394586368 13 3306 19862 29 _ _ (1979317 / 100000) (49483 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell394586368 :
    ThetaLowerSegment 394586368 394651904 (19728129931761 / 50000) (19731364161883 / 50000) := by
  exact
    packedTile32768 394586368 394651904 13 3268 19864 29 _ _ (1979333 / 100000) (247417 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell394651904 :
    ThetaLowerSegment 394651904 394717440 (19731364161883 / 50000) (4933673109727 / 12500) := by
  exact
    packedTile32768 394651904 394717440 13 3363 19865 29 _ _ (39587 / 2000) (1979353 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell394717440 :
    ThetaLowerSegment 394717440 394782976 (4933673109727 / 12500) (19737936621421 / 50000) := by
  exact
    packedTile32768 394717440 394782976 13 3278 19867 29 _ _ (1979367 / 100000) (197937 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell394782976 :
    ThetaLowerSegment 394782976 394848512 (19737936621421 / 50000) (9870657714101 / 25000) := by
  exact
    packedTile32768 394782976 394848512 13 3414 19869 29 _ _ (1979383 / 100000) (989693 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell394848512 :
    ThetaLowerSegment 394848512 394914048 (9870657714101 / 25000) (9872312492501 / 25000) := by
  exact
    packedTile32768 394848512 394914048 13 3344 19870 29 _ _ (9897 / 500) (1979403 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell394914048 :
    ThetaLowerSegment 394914048 394979584 (9872312492501 / 25000) (9873936603329 / 25000) := by
  exact
    packedTile32768 394914048 394979584 13 3282 19872 29 _ _ (247427 / 12500) (1979419 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell394979584 :
    ThetaLowerSegment 394979584 395045120 (9873936603329 / 25000) (39502280521649 / 100000) := by
  exact
    packedTile32768 394979584 395045120 13 3301 19874 29 _ _ (1979433 / 100000) (494859 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell395045120 :
    ThetaLowerSegment 395045120 395110656 (39502280521649 / 100000) (39508933453099 / 100000) := by
  exact
    packedTile32768 395045120 395110656 13 3361 19875 29 _ _ (39589 / 2000) (1979453 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell395110656 :
    ThetaLowerSegment 395110656 395176192 (39508933453099 / 100000) (39515485485559 / 100000) := by
  exact
    packedTile32768 395110656 395176192 13 3310 19877 29 _ _ (989733 / 50000) (1979469 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell395176192 :
    ThetaLowerSegment 395176192 395241728 (39515485485559 / 100000) (39522144466371 / 100000) := by
  exact
    packedTile32768 395176192 395241728 13 3364 19879 29 _ _ (1979483 / 100000) (989743 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell395241728 :
    ThetaLowerSegment 395241728 395307264 (39522144466371 / 100000) (1235272325736 / 3125) := by
  exact
    packedTile32768 395241728 395307264 13 3319 19880 29 _ _ (1979499 / 100000) (989751 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell395307264 :
    ThetaLowerSegment 395307264 395372800 (1235272325736 / 3125) (4941901399383 / 12500) := by
  exact
    packedTile32768 395307264 395372800 13 3282 19882 29 _ _ (494879 / 25000) (1979519 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell395372800 :
    ThetaLowerSegment 395372800 395438336 (4941901399383 / 12500) (1977090448761 / 5000) := by
  exact
    packedTile32768 395372800 395438336 13 3333 19883 29 _ _ (494883 / 25000) (395907 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell395438336 :
    ThetaLowerSegment 395438336 395503872 (1977090448761 / 5000) (247176639406 / 625) := by
  exact
    packedTile32768 395438336 395503872 13 3260 19885 29 _ _ (1979549 / 100000) (61861 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell395503872 :
    ThetaLowerSegment 395503872 395569408 (247176639406 / 625) (19777408323993 / 50000) := by
  exact
    packedTile32768 395503872 395569408 13 3311 19887 29 _ _ (989783 / 50000) (1979569 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell395569408 :
    ThetaLowerSegment 395569408 395634944 (19777408323993 / 50000) (9890342760997 / 25000) := by
  exact
    packedTile32768 395569408 395634944 13 3311 19888 29 _ _ (989791 / 50000) (395917 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell395634944 :
    ThetaLowerSegment 395634944 395700480 (9890342760997 / 25000) (7913562135907 / 20000) := by
  exact
    packedTile32768 395634944 395700480 13 3253 19890 29 _ _ (1979599 / 100000) (989801 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell395700480 :
    ThetaLowerSegment 395700480 395766016 (7913562135907 / 20000) (7914884518727 / 20000) := by
  exact
    packedTile32768 395700480 395766016 13 3340 19892 29 _ _ (395923 / 20000) (989809 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell395766016 :
    ThetaLowerSegment 395766016 395831552 (7914884518727 / 20000) (39580977155187 / 100000) := by
  exact
    packedTile32768 395766016 395831552 13 3311 19893 29 _ _ (123727 / 6250) (395927 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell395831552 :
    ThetaLowerSegment 395831552 395897088 (39580977155187 / 100000) (39587539688307 / 100000) := by
  exact
    packedTile32768 395831552 395897088 13 3315 19895 29 _ _ (61864 / 3125) (1979651 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell395897088 :
    ThetaLowerSegment 395897088 395962624 (39587539688307 / 100000) (39594036948837 / 100000) := by
  exact
    packedTile32768 395897088 395962624 13 3282 19897 29 _ _ (395933 / 20000) (494917 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell395962624 :
    ThetaLowerSegment 395962624 396028160 (39594036948837 / 100000) (7920103685541 / 20000) := by
  exact
    packedTile32768 395962624 396028160 13 3274 19898 29 _ _ (989841 / 50000) (395937 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell396028160 :
    ThetaLowerSegment 396028160 396093696 (7920103685541 / 20000) (7921408306523 / 20000) := by
  exact
    packedTile32768 396028160 396093696 13 3295 19900 29 _ _ (989849 / 50000) (1979701 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell396093696 :
    ThetaLowerSegment 396093696 396159232 (7921408306523 / 20000) (7922701456361 / 20000) := by
  exact
    packedTile32768 396093696 396159232 13 3266 19902 29 _ _ (395943 / 20000) (989859 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell396159232 :
    ThetaLowerSegment 396159232 396224768 (7922701456361 / 20000) (39619913691321 / 100000) := by
  exact
    packedTile32768 396159232 396224768 13 3236 19903 29 _ _ (1979731 / 100000) (989867 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell396224768 :
    ThetaLowerSegment 396224768 396290304 (39619913691321 / 100000) (39626533968633 / 100000) := by
  exact
    packedTile32768 396224768 396290304 13 3344 19905 29 _ _ (494937 / 25000) (1979751 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell396290304 :
    ThetaLowerSegment 396290304 396355840 (39626533968633 / 100000) (39632995918329 / 100000) := by
  exact
    packedTile32768 396290304 396355840 13 3264 19907 29 _ _ (494941 / 25000) (1979767 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell396355840 :
    ThetaLowerSegment 396355840 396421376 (39632995918329 / 100000) (7927920093549 / 20000) := by
  exact
    packedTile32768 396355840 396421376 13 3336 19908 29 _ _ (1979781 / 100000) (247473 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell396421376 :
    ThetaLowerSegment 396421376 396486912 (7927920093549 / 20000) (39646090242311 / 100000) := by
  exact
    packedTile32768 396421376 396486912 13 3278 19910 29 _ _ (1979797 / 100000) (9899 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell396486912 :
    ThetaLowerSegment 396486912 396552448 (39646090242311 / 100000) (39652732518281 / 100000) := by
  exact
    packedTile32768 396486912 396552448 13 3355 19911 29 _ _ (989907 / 50000) (1979817 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell396552448 :
    ThetaLowerSegment 396552448 396617984 (39652732518281 / 100000) (39659289715241 / 100000) := by
  exact
    packedTile32768 396552448 396617984 13 3312 19913 29 _ _ (197983 / 10000) (1979833 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell396617984 :
    ThetaLowerSegment 396617984 396683520 (39659289715241 / 100000) (39665890525139 / 100000) := by
  exact
    packedTile32768 396617984 396683520 13 3334 19915 29 _ _ (1979847 / 100000) (39597 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell396683520 :
    ThetaLowerSegment 396683520 396749056 (39665890525139 / 100000) (39672384475779 / 100000) := by
  exact
    packedTile32768 396683520 396749056 13 3280 19916 29 _ _ (1979863 / 100000) (989933 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell396749056 :
    ThetaLowerSegment 396749056 396814592 (39672384475779 / 100000) (39678985395699 / 100000) := by
  exact
    packedTile32768 396749056 396814592 13 3334 19918 29 _ _ (49497 / 2500) (1979883 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell396814592 :
    ThetaLowerSegment 396814592 396880128 (39678985395699 / 100000) (39685465595307 / 100000) := by
  exact
    packedTile32768 396814592 396880128 13 3273 19920 29 _ _ (247487 / 12500) (1979899 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell396880128 :
    ThetaLowerSegment 396880128 396945664 (39685465595307 / 100000) (39692074544901 / 100000) := by
  exact
    packedTile32768 396880128 396945664 13 3338 19921 29 _ _ (1979913 / 100000) (494979 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell396945664 :
    ThetaLowerSegment 396945664 397011200 (39692074544901 / 100000) (39698616230317 / 100000) := by
  exact
    packedTile32768 396945664 397011200 13 3304 19923 29 _ _ (1979929 / 100000) (494983 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell397011200 :
    ThetaLowerSegment 397011200 397076736 (39698616230317 / 100000) (7941027238499 / 20000) := by
  exact
    packedTile32768 397011200 397076736 13 3293 19925 29 _ _ (989973 / 50000) (1979949 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell397076736 :
    ThetaLowerSegment 397076736 397142272 (7941027238499 / 20000) (7942341933931 / 20000) := by
  exact
    packedTile32768 397076736 397142272 13 3320 19926 29 _ _ (1979963 / 100000) (989983 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell397142272 :
    ThetaLowerSegment 397142272 397207808 (7942341933931 / 20000) (19859174269621 / 50000) := by
  exact
    packedTile32768 397142272 397207808 13 3353 19928 29 _ _ (1979979 / 100000) (989991 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell397207808 :
    ThetaLowerSegment 397207808 397273344 (19859174269621 / 50000) (19862440273023 / 50000) := by
  exact
    packedTile32768 397207808 397273344 13 3299 19930 29 _ _ (494999 / 25000) (1979999 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell397273344 :
    ThetaLowerSegment 397273344 397338880 (19862440273023 / 50000) (19865700362781 / 50000) := by
  exact
    packedTile32768 397273344 397338880 13 3293 19931 29 _ _ (495003 / 25000) (396003 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell397338880 :
    ThetaLowerSegment 397338880 397404416 (19865700362781 / 50000) (4967238387607 / 12500) := by
  exact
    packedTile32768 397338880 397404416 13 3286 19933 29 _ _ (1980029 / 100000) (61876 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell397404416 :
    ThetaLowerSegment 397404416 397469952 (4967238387607 / 12500) (19872246365263 / 50000) := by
  exact
    packedTile32768 397404416 397469952 13 3326 19935 29 _ _ (396009 / 20000) (123753 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell397469952 :
    ThetaLowerSegment 397469952 397535488 (19872246365263 / 50000) (4968873911341 / 12500) := by
  exact
    packedTile32768 397469952 397535488 13 3282 19936 29 _ _ (1980061 / 100000) (61877 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell397535488 :
    ThetaLowerSegment 397535488 397601024 (4968873911341 / 12500) (19878793465273 / 50000) := by
  exact
    packedTile32768 397535488 397601024 13 3331 19938 29 _ _ (990039 / 50000) (1980081 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell397601024 :
    ThetaLowerSegment 397601024 397666560 (19878793465273 / 50000) (19882044779621 / 50000) := by
  exact
    packedTile32768 397601024 397666560 13 3284 19939 29 _ _ (990047 / 50000) (1980097 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell397666560 :
    ThetaLowerSegment 397666560 397732096 (19882044779621 / 50000) (1590829154857 / 4000) := by
  exact
    packedTile32768 397666560 397732096 13 3353 19941 29 _ _ (1980111 / 100000) (990057 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell397732096 :
    ThetaLowerSegment 397732096 397797632 (1590829154857 / 4000) (39777291012303 / 100000) := by
  exact
    packedTile32768 397732096 397797632 13 3314 19943 29 _ _ (1980127 / 100000) (198013 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell397797632 :
    ThetaLowerSegment 397797632 397863168 (39777291012303 / 100000) (39783977958591 / 100000) := by
  exact
    packedTile32768 397797632 397863168 13 3377 19944 29 _ _ (123759 / 6250) (1980147 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell397863168 :
    ThetaLowerSegment 397863168 397928704 (39783977958591 / 100000) (39790575851711 / 100000) := by
  exact
    packedTile32768 397863168 397928704 13 3332 19946 29 _ _ (12376 / 625) (1980163 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell397928704 :
    ThetaLowerSegment 397928704 397994240 (39790575851711 / 100000) (39797086673687 / 100000) := by
  exact
    packedTile32768 397928704 397994240 13 3288 19948 29 _ _ (1980177 / 100000) (99009 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell397994240 :
    ThetaLowerSegment 397994240 398059776 (39797086673687 / 100000) (39803605469043 / 100000) := by
  exact
    packedTile32768 397994240 398059776 13 3292 19949 29 _ _ (1980193 / 100000) (495049 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell398059776 :
    ThetaLowerSegment 398059776 398125312 (39803605469043 / 100000) (39810253034013 / 100000) := by
  exact
    packedTile32768 398059776 398125312 13 3357 19951 29 _ _ (198021 / 10000) (1980213 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell398125312 :
    ThetaLowerSegment 398125312 398190848 (39810253034013 / 100000) (39816769957779 / 100000) := by
  exact
    packedTile32768 398125312 398190848 13 3291 19953 29 _ _ (990113 / 50000) (1980229 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell398190848 :
    ThetaLowerSegment 398190848 398256384 (39816769957779 / 100000) (7964677585977 / 20000) := by
  exact
    packedTile32768 398190848 398256384 13 3342 19954 29 _ _ (1980243 / 100000) (990123 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell398256384 :
    ThetaLowerSegment 398256384 398321920 (7964677585977 / 20000) (7965984556917 / 20000) := by
  exact
    packedTile32768 398256384 398321920 13 3300 19956 29 _ _ (1980259 / 100000) (990131 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell398321920 :
    ThetaLowerSegment 398321920 398387456 (7965984556917 / 20000) (7967303420733 / 20000) := by
  exact
    packedTile32768 398321920 398387456 13 3330 19958 29 _ _ (495069 / 25000) (1980279 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell398387456 :
    ThetaLowerSegment 398387456 398452992 (7967303420733 / 20000) (39843073850477 / 100000) := by
  exact
    packedTile32768 398387456 398452992 13 3311 19959 29 _ _ (495073 / 25000) (396059 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell398452992 :
    ThetaLowerSegment 398452992 398518528 (39843073850477 / 100000) (39849525697199 / 100000) := by
  exact
    packedTile32768 398452992 398518528 13 3258 19961 29 _ _ (1980309 / 100000) (247539 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell398518528 :
    ThetaLowerSegment 398518528 398584064 (39849525697199 / 100000) (39856048887749 / 100000) := by
  exact
    packedTile32768 398518528 398584064 13 3294 19962 29 _ _ (79213 / 4000) (247541 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell398584064 :
    ThetaLowerSegment 398584064 398649600 (39856048887749 / 100000) (39862552327593 / 100000) := by
  exact
    packedTile32768 398584064 398649600 13 3284 19964 29 _ _ (1980341 / 100000) (247543 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell398649600 :
    ThetaLowerSegment 398649600 398715136 (39862552327593 / 100000) (1594761836859 / 4000) := by
  exact
    packedTile32768 398649600 398715136 13 3279 19966 29 _ _ (990179 / 50000) (1980361 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell398715136 :
    ThetaLowerSegment 398715136 398780672 (1594761836859 / 4000) (39875517783707 / 100000) := by
  exact
    packedTile32768 398715136 398780672 13 3268 19967 29 _ _ (990187 / 50000) (1980377 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell398780672 :
    ThetaLowerSegment 398780672 398846208 (39875517783707 / 100000) (39882096642609 / 100000) := by
  exact
    packedTile32768 398780672 398846208 13 3322 19969 29 _ _ (1980391 / 100000) (990197 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell398846208 :
    ThetaLowerSegment 398846208 398911744 (39882096642609 / 100000) (19944307081023 / 50000) := by
  exact
    packedTile32768 398846208 398911744 13 3291 19971 29 _ _ (1980407 / 100000) (198041 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell398911744 :
    ThetaLowerSegment 398911744 398977280 (19944307081023 / 50000) (19947581712107 / 50000) := by
  exact
    packedTile32768 398911744 398977280 13 3307 19972 29 _ _ (247553 / 12500) (1980427 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell398977280 :
    ThetaLowerSegment 398977280 399042816 (19947581712107 / 50000) (19950887066467 / 50000) := by
  exact
    packedTile32768 398977280 399042816 13 3338 19974 29 _ _ (49511 / 2500) (1980443 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell399042816 :
    ThetaLowerSegment 399042816 399108352 (19950887066467 / 50000) (19954134024079 / 50000) := by
  exact
    packedTile32768 399042816 399108352 13 3279 19976 29 _ _ (247557 / 12500) (1980459 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell399108352 :
    ThetaLowerSegment 399108352 399173888 (19954134024079 / 50000) (39914825394261 / 100000) := by
  exact
    packedTile32768 399108352 399173888 13 3311 19977 29 _ _ (1980473 / 100000) (495119 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell399173888 :
    ThetaLowerSegment 399173888 399239424 (39914825394261 / 100000) (39921408539697 / 100000) := by
  exact
    packedTile32768 399173888 399239424 13 3324 19979 29 _ _ (1980489 / 100000) (495123 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell399239424 :
    ThetaLowerSegment 399239424 399304960 (39921408539697 / 100000) (39927872911281 / 100000) := by
  exact
    packedTile32768 399239424 399304960 13 3264 19980 29 _ _ (990253 / 50000) (1980509 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell399304960 :
    ThetaLowerSegment 399304960 399370496 (39927872911281 / 100000) (39934456166409 / 100000) := by
  exact
    packedTile32768 399304960 399370496 13 3324 19982 29 _ _ (990261 / 50000) (79221 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell399370496 :
    ThetaLowerSegment 399370496 399436032 (39934456166409 / 100000) (39941114738527 / 100000) := by
  exact
    packedTile32768 399370496 399436032 13 3362 19984 29 _ _ (1980539 / 100000) (990271 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell399436032 :
    ThetaLowerSegment 399436032 399501568 (39941114738527 / 100000) (2496722095177 / 6250) := by
  exact
    packedTile32768 399436032 399501568 13 3251 19985 29 _ _ (396111 / 20000) (990279 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell399501568 :
    ThetaLowerSegment 399501568 399567104 (2496722095177 / 6250) (19977094217841 / 50000) := by
  exact
    packedTile32768 399501568 399567104 13 3350 19987 29 _ _ (1980571 / 100000) (990287 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell399567104 :
    ThetaLowerSegment 399567104 399632640 (19977094217841 / 50000) (19980393877449 / 50000) := by
  exact
    packedTile32768 399567104 399632640 13 3332 19989 29 _ _ (495147 / 25000) (1980591 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell399632640 :
    ThetaLowerSegment 399632640 399698176 (19980393877449 / 50000) (19983687621901 / 50000) := by
  exact
    packedTile32768 399632640 399698176 13 3326 19990 29 _ _ (495151 / 25000) (1980607 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell399698176 :
    ThetaLowerSegment 399698176 399763712 (19983687621901 / 50000) (39974087568371 / 100000) := by
  exact
    packedTile32768 399698176 399763712 13 3389 19992 29 _ _ (1980621 / 100000) (123789 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell399763712 :
    ThetaLowerSegment 399763712 399829248 (39974087568371 / 100000) (7996145332719 / 20000) := by
  exact
    packedTile32768 399763712 399829248 13 3352 19994 29 _ _ (1980637 / 100000) (12379 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell399829248 :
    ThetaLowerSegment 399829248 399894784 (7996145332719 / 20000) (39987286586331 / 100000) := by
  exact
    packedTile32768 399829248 399894784 13 3312 19995 29 _ _ (1980653 / 100000) (123791 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell399894784 :
    ThetaLowerSegment 399894784 399960320 (39987286586331 / 100000) (39993818835991 / 100000) := by
  exact
    packedTile32768 399894784 399960320 13 3298 19997 29 _ _ (198067 / 10000) (1980673 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell399960320 :
    ThetaLowerSegment 399960320 400025856 (39993818835991 / 100000) (40000384810081 / 100000) := by
  exact
    packedTile32768 399960320 400025856 13 3315 19999 29 _ _ (990343 / 50000) (1980689 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell400025856 :
    ThetaLowerSegment 400025856 400091392 (40000384810081 / 100000) (40006966682827 / 100000) := by
  exact
    packedTile32768 400025856 400091392 13 3323 20000 29 _ _ (990351 / 50000) (396141 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell400091392 :
    ThetaLowerSegment 400091392 400156928 (40006966682827 / 100000) (20006732710933 / 50000) := by
  exact
    packedTile32768 400091392 400156928 13 3281 20002 29 _ _ (1980719 / 100000) (990361 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell400156928 :
    ThetaLowerSegment 400156928 400222464 (20006732710933 / 50000) (40020003828101 / 100000) := by
  exact
    packedTile32768 400156928 400222464 13 3301 20003 29 _ _ (396147 / 20000) (990369 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell400222464 :
    ThetaLowerSegment 400222464 400288000 (40020003828101 / 100000) (40026572001733 / 100000) := by
  exact
    packedTile32768 400222464 400288000 13 3316 20005 29 _ _ (123797 / 6250) (396151 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell400288000 :
    ThetaLowerSegment 400288000 400353536 (40026572001733 / 100000) (40033122401509 / 100000) := by
  exact
    packedTile32768 400288000 400353536 13 3307 20007 29 _ _ (61899 / 3125) (1980771 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell400353536 :
    ThetaLowerSegment 400353536 400419072 (40033122401509 / 100000) (40039761989477 / 100000) := by
  exact
    packedTile32768 400353536 400419072 13 3352 20008 29 _ _ (123799 / 6250) (1980787 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell400419072 :
    ThetaLowerSegment 400419072 400484608 (40039761989477 / 100000) (40046266939961 / 100000) := by
  exact
    packedTile32768 400419072 400484608 13 3284 20010 29 _ _ (1980801 / 100000) (495201 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell400484608 :
    ThetaLowerSegment 400484608 400550144 (40046266939961 / 100000) (4005271846093 / 10000) := by
  exact
    packedTile32768 400484608 400550144 13 3257 20012 29 _ _ (1980817 / 100000) (99041 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell400550144 :
    ThetaLowerSegment 400550144 400615680 (4005271846093 / 10000) (1001479894621 / 2500) := by
  exact
    packedTile32768 400550144 400615680 13 3270 20013 29 _ _ (1980833 / 100000) (495209 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell400615680 :
    ThetaLowerSegment 400615680 400681216 (1001479894621 / 2500) (2003289204597 / 5000) := by
  exact
    packedTile32768 400615680 400681216 13 3326 20015 29 _ _ (39617 / 2000) (1980853 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell400681216 :
    ThetaLowerSegment 400681216 400746752 (2003289204597 / 5000) (2003620009219 / 5000) := by
  exact
    packedTile32768 400681216 400746752 13 3340 20017 29 _ _ (990433 / 50000) (1980869 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell400746752 :
    ThetaLowerSegment 400746752 400812288 (2003620009219 / 5000) (40078978696823 / 100000) := by
  exact
    packedTile32768 400746752 400812288 13 3321 20018 29 _ _ (1980883 / 100000) (990443 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell400812288 :
    ThetaLowerSegment 400812288 400877824 (40078978696823 / 100000) (10021392286949 / 25000) := by
  exact
    packedTile32768 400812288 400877824 13 3327 20020 29 _ _ (1980899 / 100000) (990451 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell400877824 :
    ThetaLowerSegment 400877824 400943360 (10021392286949 / 25000) (40092135881021 / 100000) := by
  exact
    packedTile32768 400877824 400943360 13 3315 20021 29 _ _ (396183 / 20000) (990459 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell400943360 :
    ThetaLowerSegment 400943360 401008896 (40092135881021 / 100000) (8019721517173 / 20000) := by
  exact
    packedTile32768 400943360 401008896 13 3267 20023 29 _ _ (495233 / 25000) (396187 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell401008896 :
    ThetaLowerSegment 401008896 401074432 (8019721517173 / 20000) (40105037743073 / 100000) := by
  exact
    packedTile32768 401008896 401074432 13 3246 20025 29 _ _ (495237 / 25000) (1980951 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell401074432 :
    ThetaLowerSegment 401074432 401139968 (40105037743073 / 100000) (40111543228849 / 100000) := by
  exact
    packedTile32768 401074432 401139968 13 3284 20026 29 _ _ (495241 / 25000) (1980967 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell401139968 :
    ThetaLowerSegment 401139968 401205504 (40111543228849 / 100000) (40118001226909 / 100000) := by
  exact
    packedTile32768 401139968 401205504 13 3260 20028 29 _ _ (1980981 / 100000) (247623 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell401205504 :
    ThetaLowerSegment 401205504 401271040 (40118001226909 / 100000) (40124451353141 / 100000) := by
  exact
    packedTile32768 401205504 401271040 13 3256 20030 29 _ _ (1980997 / 100000) (1981 / 100)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell401271040 :
    ThetaLowerSegment 401271040 401336576 (40124451353141 / 100000) (20065483452449 / 50000) := by
  exact
    packedTile32768 401271040 401336576 13 3289 20031 29 _ _ (1981013 / 100000) (247627 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell401336576 :
    ThetaLowerSegment 401336576 401402112 (20065483452449 / 50000) (10034369637627 / 25000) := by
  exact
    packedTile32768 401336576 401402112 13 3287 20033 29 _ _ (198103 / 10000) (1981033 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell401402112 :
    ThetaLowerSegment 401402112 401467648 (10034369637627 / 25000) (4014410911147 / 10000) := by
  exact
    packedTile32768 401402112 401467648 13 3347 20035 29 _ _ (990523 / 50000) (1981049 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell401467648 :
    ThetaLowerSegment 401467648 401533184 (4014410911147 / 10000) (10037699789461 / 25000) := by
  exact
    packedTile32768 401467648 401533184 13 3377 20036 29 _ _ (990531 / 50000) (396213 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell401533184 :
    ThetaLowerSegment 401533184 401598720 (10037699789461 / 25000) (40157406056309 / 100000) := by
  exact
    packedTile32768 401533184 401598720 13 3335 20038 29 _ _ (1981079 / 100000) (990541 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell401598720 :
    ThetaLowerSegment 401598720 401664256 (40157406056309 / 100000) (40164003102659 / 100000) := by
  exact
    packedTile32768 401598720 401664256 13 3330 20039 29 _ _ (396219 / 20000) (990549 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell401664256 :
    ThetaLowerSegment 401664256 401729792 (40164003102659 / 100000) (40170675484507 / 100000) := by
  exact
    packedTile32768 401664256 401729792 13 3368 20041 29 _ _ (1981111 / 100000) (990557 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell401729792 :
    ThetaLowerSegment 401729792 401795328 (40170675484507 / 100000) (40177072546819 / 100000) := by
  exact
    packedTile32768 401729792 401795328 13 3229 20043 29 _ _ (247641 / 12500) (1981131 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell401795328 :
    ThetaLowerSegment 401795328 401860864 (40177072546819 / 100000) (40183642020323 / 100000) := by
  exact
    packedTile32768 401795328 401860864 13 3316 20044 29 _ _ (247643 / 12500) (1981147 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell401860864 :
    ThetaLowerSegment 401860864 401926400 (40183642020323 / 100000) (40190223433843 / 100000) := by
  exact
    packedTile32768 401860864 401926400 13 3322 20046 29 _ _ (49529 / 2500) (1981163 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell401926400 :
    ThetaLowerSegment 401926400 401991936 (40190223433843 / 100000) (40196763295819 / 100000) := by
  exact
    packedTile32768 401926400 401991936 13 3301 20048 29 _ _ (247647 / 12500) (1981179 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell401991936 :
    ThetaLowerSegment 401991936 402057472 (40196763295819 / 100000) (20101689249623 / 50000) := by
  exact
    packedTile32768 401991936 402057472 13 3339 20049 29 _ _ (1981193 / 100000) (495299 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell402057472 :
    ThetaLowerSegment 402057472 402123008 (20101689249623 / 50000) (20104970131727 / 50000) := by
  exact
    packedTile32768 402057472 402123008 13 3312 20051 29 _ _ (1981209 / 100000) (495303 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell402123008 :
    ThetaLowerSegment 402123008 402188544 (20104970131727 / 50000) (40216476324729 / 100000) := by
  exact
    packedTile32768 402123008 402188544 13 3299 20053 29 _ _ (79249 / 4000) (495307 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell402188544 :
    ThetaLowerSegment 402188544 402254080 (40216476324729 / 100000) (40223075841831 / 100000) := by
  exact
    packedTile32768 402188544 402254080 13 3331 20054 29 _ _ (990621 / 50000) (396249 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell402254080 :
    ThetaLowerSegment 402254080 402319616 (40223075841831 / 100000) (40229493136493 / 100000) := by
  exact
    packedTile32768 402254080 402319616 13 3239 20056 29 _ _ (990629 / 50000) (1981261 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell402319616 :
    ThetaLowerSegment 402319616 402385152 (40229493136493 / 100000) (40236051153433 / 100000) := by
  exact
    packedTile32768 402319616 402385152 13 3310 20057 29 _ _ (990637 / 50000) (1981277 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell402385152 :
    ThetaLowerSegment 402385152 402450688 (40236051153433 / 100000) (5030329868251 / 12500) := by
  exact
    packedTile32768 402385152 402450688 13 3325 20059 29 _ _ (1981291 / 100000) (990647 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell402450688 :
    ThetaLowerSegment 402450688 402516224 (5030329868251 / 12500) (503115607327 / 1250) := by
  exact
    packedTile32768 402450688 402516224 13 3336 20061 29 _ _ (1981307 / 100000) (198131 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell402516224 :
    ThetaLowerSegment 402516224 402581760 (503115607327 / 1250) (8051151446443 / 20000) := by
  exact
    packedTile32768 402516224 402581760 13 3285 20062 29 _ _ (1981323 / 100000) (990663 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell402581760 :
    ThetaLowerSegment 402581760 402647296 (8051151446443 / 20000) (40262325371 / 100) := by
  exact
    packedTile32768 402581760 402647296 13 3315 20064 29 _ _ (1981339 / 100000) (990671 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell402647296 :
    ThetaLowerSegment 402647296 402712832 (40262325371 / 100) (10067222400857 / 25000) := by
  exact
    packedTile32768 402647296 402712832 13 3313 20066 29 _ _ (495339 / 25000) (1981359 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell402712832 :
    ThetaLowerSegment 402712832 402778368 (10067222400857 / 25000) (5034419352533 / 12500) := by
  exact
    packedTile32768 402712832 402778368 13 3263 20067 29 _ _ (495343 / 25000) (15851 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell402778368 :
    ThetaLowerSegment 402778368 402843904 (5034419352533 / 12500) (10070479789677 / 25000) := by
  exact
    packedTile32768 402778368 402843904 13 3313 20069 29 _ _ (495347 / 25000) (1981391 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell402843904 :
    ThetaLowerSegment 402843904 402909440 (10070479789677 / 25000) (5036045087889 / 12500) := by
  exact
    packedTile32768 402843904 402909440 13 3251 20070 29 _ _ (495351 / 25000) (1981407 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell402909440 :
    ThetaLowerSegment 402909440 402974976 (5036045087889 / 12500) (40295012333409 / 100000) := by
  exact
    packedTile32768 402909440 402974976 13 3357 20072 29 _ _ (1981421 / 100000) (123839 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell402974976 :
    ThetaLowerSegment 402974976 403040512 (40295012333409 / 100000) (20150824082961 / 50000) := by
  exact
    packedTile32768 402974976 403040512 13 3349 20074 29 _ _ (1981437 / 100000) (12384 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell403040512 :
    ThetaLowerSegment 403040512 403106048 (20150824082961 / 50000) (2519261932733 / 6250) := by
  exact
    packedTile32768 403040512 403106048 13 3302 20075 29 _ _ (1981453 / 100000) (123841 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell403106048 :
    ThetaLowerSegment 403106048 403171584 (2519261932733 / 6250) (10078689378827 / 25000) := by
  exact
    packedTile32768 403106048 403171584 13 3314 20077 29 _ _ (198147 / 10000) (1981473 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell403171584 :
    ThetaLowerSegment 403171584 403237120 (10078689378827 / 25000) (4032125084493 / 10000) := by
  exact
    packedTile32768 403171584 403237120 13 3277 20079 29 _ _ (990743 / 50000) (1981489 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell403237120 :
    ThetaLowerSegment 403237120 403302656 (4032125084493 / 10000) (10081950918011 / 25000) := by
  exact
    packedTile32768 403237120 403302656 13 3307 20080 29 _ _ (990751 / 50000) (396301 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell403302656 :
    ThetaLowerSegment 403302656 403368192 (10081950918011 / 25000) (1008361638389 / 2500) := by
  exact
    packedTile32768 403302656 403368192 13 3362 20082 29 _ _ (990759 / 50000) (1981521 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell403368192 :
    ThetaLowerSegment 403368192 403433728 (1008361638389 / 2500) (8068210827887 / 20000) := by
  exact
    packedTile32768 403368192 403433728 13 3325 20084 29 _ _ (396307 / 20000) (990769 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell403433728 :
    ThetaLowerSegment 403433728 403499264 (8068210827887 / 20000) (40347676482877 / 100000) := by
  exact
    packedTile32768 403433728 403499264 13 3342 20085 29 _ _ (1981551 / 100000) (990777 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell403499264 :
    ThetaLowerSegment 403499264 403564800 (40347676482877 / 100000) (40354195838307 / 100000) := by
  exact
    packedTile32768 403499264 403564800 13 3290 20087 29 _ _ (1981567 / 100000) (198157 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell403564800 :
    ThetaLowerSegment 403564800 403630336 (40354195838307 / 100000) (40360695430547 / 100000) := by
  exact
    packedTile32768 403564800 403630336 13 3280 20088 29 _ _ (1981583 / 100000) (990793 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell403630336 :
    ThetaLowerSegment 403630336 403695872 (40360695430547 / 100000) (40367333790547 / 100000) := by
  exact
    packedTile32768 403630336 403695872 13 3350 20090 29 _ _ (2477 / 125) (1981603 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell403695872 :
    ThetaLowerSegment 403695872 403761408 (40367333790547 / 100000) (40373726483763 / 100000) := by
  exact
    packedTile32768 403695872 403761408 13 3226 20092 29 _ _ (123851 / 6250) (1981619 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell403761408 :
    ThetaLowerSegment 403761408 403826944 (40373726483763 / 100000) (40380291630579 / 100000) := by
  exact
    packedTile32768 403761408 403826944 13 3313 20093 29 _ _ (61926 / 3125) (396327 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell403826944 :
    ThetaLowerSegment 403826944 403892480 (40380291630579 / 100000) (40386942041267 / 100000) := by
  exact
    packedTile32768 403826944 403892480 13 3356 20095 29 _ _ (123853 / 6250) (1981651 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell403892480 :
    ThetaLowerSegment 403892480 403958016 (40386942041267 / 100000) (40393453789171 / 100000) := by
  exact
    packedTile32768 403892480 403958016 13 3286 20097 29 _ _ (61927 / 3125) (1981667 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell403958016 :
    ThetaLowerSegment 403958016 404023552 (40393453789171 / 100000) (40400056750263 / 100000) := by
  exact
    packedTile32768 403958016 404023552 13 3332 20098 29 _ _ (1981681 / 100000) (495421 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell404023552 :
    ThetaLowerSegment 404023552 404089088 (40400056750263 / 100000) (20203317001303 / 50000) := by
  exact
    packedTile32768 404023552 404089088 13 3319 20100 29 _ _ (1981697 / 100000) (19817 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell404089088 :
    ThetaLowerSegment 404089088 404154624 (20203317001303 / 50000) (1616527976711 / 4000) := by
  exact
    packedTile32768 404089088 404154624 13 3313 20101 29 _ _ (1981713 / 100000) (495429 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell404154624 :
    ThetaLowerSegment 404154624 404220160 (1616527976711 / 4000) (40419782721513 / 100000) := by
  exact
    packedTile32768 404154624 404220160 13 3322 20103 29 _ _ (1981729 / 100000) (495433 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell404220160 :
    ThetaLowerSegment 404220160 404285696 (40419782721513 / 100000) (323409343257 / 800) := by
  exact
    packedTile32768 404220160 404285696 13 3222 20105 29 _ _ (990873 / 50000) (1981749 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell404285696 :
    ThetaLowerSegment 404285696 404351232 (323409343257 / 800) (40432765192823 / 100000) := by
  exact
    packedTile32768 404285696 404351232 13 3329 20106 29 _ _ (990881 / 50000) (396353 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell404351232 :
    ThetaLowerSegment 404351232 404416768 (40432765192823 / 100000) (8087878451691 / 20000) := by
  exact
    packedTile32768 404351232 404416768 13 3344 20108 29 _ _ (990889 / 50000) (1981781 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell404416768 :
    ThetaLowerSegment 404416768 404482304 (8087878451691 / 20000) (40445777598723 / 100000) := by
  exact
    packedTile32768 404416768 404482304 13 3222 20110 29 _ _ (990897 / 50000) (1981797 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell404482304 :
    ThetaLowerSegment 404482304 404547840 (40445777598723 / 100000) (40452396844123 / 100000) := by
  exact
    packedTile32768 404482304 404547840 13 3340 20111 29 _ _ (198181 / 10000) (1981813 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell404547840 :
    ThetaLowerSegment 404547840 404613376 (40452396844123 / 100000) (505735992503 / 1250) := by
  exact
    packedTile32768 404547840 404613376 13 3271 20113 29 _ _ (1981827 / 100000) (198183 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell404613376 :
    ThetaLowerSegment 404613376 404678912 (505735992503 / 1250) (2023274937793 / 5000) := by
  exact
    packedTile32768 404613376 404678912 13 3340 20115 29 _ _ (1981843 / 100000) (990923 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell404678912 :
    ThetaLowerSegment 404678912 404744448 (2023274937793 / 5000) (5059002879461 / 12500) := by
  exact
    packedTile32768 404678912 404744448 13 3292 20116 29 _ _ (1981859 / 100000) (990931 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell404744448 :
    ThetaLowerSegment 404744448 404809984 (5059002879461 / 12500) (40478573132563 / 100000) := by
  exact
    packedTile32768 404744448 404809984 13 3305 20118 29 _ _ (3171 / 160) (990939 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell404809984 :
    ThetaLowerSegment 404809984 404875520 (40478573132563 / 100000) (10121273883961 / 25000) := by
  exact
    packedTile32768 404809984 404875520 13 3291 20119 29 _ _ (1981891 / 100000) (990947 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell404875520 :
    ThetaLowerSegment 404875520 404941056 (10121273883961 / 25000) (5061470582033 / 12500) := by
  exact
    packedTile32768 404875520 404941056 13 3365 20121 29 _ _ (495477 / 25000) (1981911 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell404941056 :
    ThetaLowerSegment 404941056 405006592 (5061470582033 / 12500) (10124573773961 / 25000) := by
  exact
    packedTile32768 404941056 405006592 13 3295 20123 29 _ _ (495481 / 25000) (1981927 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell405006592 :
    ThetaLowerSegment 405006592 405072128 (10124573773961 / 25000) (5063099730123 / 12500) := by
  exact
    packedTile32768 405006592 405072128 13 3281 20124 29 _ _ (99097 / 5000) (1981943 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell405072128 :
    ThetaLowerSegment 405072128 405137664 (5063099730123 / 12500) (10127863807797 / 25000) := by
  exact
    packedTile32768 405072128 405137664 13 3359 20126 29 _ _ (495489 / 25000) (1981959 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell405137664 :
    ThetaLowerSegment 405137664 405203200 (10127863807797 / 25000) (1266187552647 / 3125) := by
  exact
    packedTile32768 405137664 405203200 13 3303 20128 29 _ _ (495493 / 25000) (79279 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell405203200 :
    ThetaLowerSegment 405203200 405268736 (1266187552647 / 3125) (2532785872307 / 6250) := by
  exact
    packedTile32768 405203200 405268736 13 3316 20129 29 _ _ (495497 / 25000) (1981991 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell405268736 :
    ThetaLowerSegment 405268736 405334272 (2532785872307 / 6250) (40531104663387 / 100000) := by
  exact
    packedTile32768 405268736 405334272 13 3295 20131 29 _ _ (396401 / 20000) (247751 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell405334272 :
    ThetaLowerSegment 405334272 405399808 (40531104663387 / 100000) (2026881572927 / 5000) := by
  exact
    packedTile32768 405334272 405399808 13 3293 20132 29 _ _ (1982021 / 100000) (247753 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell405399808 :
    ThetaLowerSegment 405399808 405465344 (2026881572927 / 5000) (40544178126751 / 100000) := by
  exact
    packedTile32768 405399808 405465344 13 3303 20134 29 _ _ (1982037 / 100000) (49551 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell405465344 :
    ThetaLowerSegment 405465344 405530880 (40544178126751 / 100000) (40550738722181 / 100000) := by
  exact
    packedTile32768 405465344 405530880 13 3310 20136 29 _ _ (1982053 / 100000) (247757 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell405530880 :
    ThetaLowerSegment 405530880 405596416 (40550738722181 / 100000) (40557358832641 / 100000) := by
  exact
    packedTile32768 405530880 405596416 13 3340 20137 29 _ _ (1982069 / 100000) (247759 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell405596416 :
    ThetaLowerSegment 405596416 405661952 (40557358832641 / 100000) (40563836286421 / 100000) := by
  exact
    packedTile32768 405596416 405661952 13 3268 20139 29 _ _ (396417 / 20000) (247761 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell405661952 :
    ThetaLowerSegment 405661952 405727488 (40563836286421 / 100000) (40570452542897 / 100000) := by
  exact
    packedTile32768 405661952 405727488 13 3338 20141 29 _ _ (991051 / 50000) (396421 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell405727488 :
    ThetaLowerSegment 405727488 405793024 (40570452542897 / 100000) (8115391174411 / 20000) := by
  exact
    packedTile32768 405727488 405793024 13 3281 20142 29 _ _ (991059 / 50000) (1982121 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell405793024 :
    ThetaLowerSegment 405793024 405858560 (8115391174411 / 20000) (40583564306811 / 100000) := by
  exact
    packedTile32768 405793024 405858560 13 3334 20144 29 _ _ (991067 / 50000) (1982137 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell405858560 :
    ThetaLowerSegment 405858560 405924096 (40583564306811 / 100000) (40590367045611 / 100000) := by
  exact
    packedTile32768 405858560 405924096 13 3432 20145 29 _ _ (39643 / 2000) (1982153 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell405924096 :
    ThetaLowerSegment 405924096 405989632 (40590367045611 / 100000) (40596848728431 / 100000) := by
  exact
    packedTile32768 405924096 405989632 13 3270 20147 29 _ _ (991083 / 50000) (1982169 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell405989632 :
    ThetaLowerSegment 405989632 406055168 (40596848728431 / 100000) (40603421643943 / 100000) := by
  exact
    packedTile32768 405989632 406055168 13 3316 20149 29 _ _ (991091 / 50000) (396437 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell406055168 :
    ThetaLowerSegment 406055168 406120704 (40603421643943 / 100000) (8121988218633 / 20000) := by
  exact
    packedTile32768 406055168 406120704 13 3289 20150 29 _ _ (991099 / 50000) (1982201 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell406120704 :
    ThetaLowerSegment 406120704 406186240 (8121988218633 / 20000) (8123294894761 / 20000) := by
  exact
    packedTile32768 406120704 406186240 13 3296 20152 29 _ _ (396443 / 20000) (991109 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell406186240 :
    ThetaLowerSegment 406186240 406251776 (8123294894761 / 20000) (40623023765029 / 100000) := by
  exact
    packedTile32768 406186240 406251776 13 3304 20154 29 _ _ (1982231 / 100000) (991117 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell406251776 :
    ThetaLowerSegment 406251776 406317312 (40623023765029 / 100000) (40629723759889 / 100000) := by
  exact
    packedTile32768 406251776 406317312 13 3380 20155 29 _ _ (1982247 / 100000) (7929 / 400)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell406317312 :
    ThetaLowerSegment 406317312 406382848 (40629723759889 / 100000) (8127253838463 / 20000) := by
  exact
    packedTile32768 406317312 406382848 13 3302 20157 29 _ _ (1982263 / 100000) (991133 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell406382848 :
    ThetaLowerSegment 406382848 406448384 (8127253838463 / 20000) (20321374631183 / 50000) := by
  exact
    packedTile32768 406382848 406448384 13 3269 20158 29 _ _ (1982279 / 100000) (991141 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell406448384 :
    ThetaLowerSegment 406448384 406513920 (20321374631183 / 50000) (40649205597181 / 100000) := by
  exact
    packedTile32768 406448384 406513920 13 3257 20160 29 _ _ (396459 / 20000) (991149 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell406513920 :
    ThetaLowerSegment 406513920 406579456 (40649205597181 / 100000) (40655683789529 / 100000) := by
  exact
    packedTile32768 406513920 406579456 13 3268 20162 29 _ _ (1982311 / 100000) (991157 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell406579456 :
    ThetaLowerSegment 406579456 406644992 (40655683789529 / 100000) (10165548933431 / 25000) := by
  exact
    packedTile32768 406579456 406644992 13 3285 20163 29 _ _ (1982327 / 100000) (198233 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell406644992 :
    ThetaLowerSegment 406644992 406710528 (10165548933431 / 25000) (10167149676211 / 25000) := by
  exact
    packedTile32768 406644992 406710528 13 3230 20165 29 _ _ (247793 / 12500) (1982347 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell406710528 :
    ThetaLowerSegment 406710528 406776064 (10167149676211 / 25000) (10168792061471 / 25000) := by
  exact
    packedTile32768 406710528 406776064 13 3314 20167 29 _ _ (49559 / 2500) (1982363 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell406776064 :
    ThetaLowerSegment 406776064 406841600 (10168792061471 / 25000) (10170453292559 / 25000) := by
  exact
    packedTile32768 406776064 406841600 13 3352 20168 29 _ _ (247797 / 12500) (1982379 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell406841600 :
    ThetaLowerSegment 406841600 406907136 (10170453292559 / 25000) (10172093721939 / 25000) := by
  exact
    packedTile32768 406841600 406907136 13 3310 20170 29 _ _ (247799 / 12500) (396479 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell406907136 :
    ThetaLowerSegment 406907136 406972672 (10172093721939 / 25000) (10173750023823 / 25000) := by
  exact
    packedTile32768 406907136 406972672 13 3342 20171 29 _ _ (247801 / 12500) (1982411 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell406972672 :
    ThetaLowerSegment 406972672 407038208 (10173750023823 / 25000) (10175419224831 / 25000) := by
  exact
    packedTile32768 406972672 407038208 13 3368 20173 29 _ _ (247803 / 12500) (1982427 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell407038208 :
    ThetaLowerSegment 407038208 407103744 (10175419224831 / 25000) (10177054737831 / 25000) := by
  exact
    packedTile32768 407038208 407103744 13 3300 20175 29 _ _ (49561 / 2500) (1982443 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell407103744 :
    ThetaLowerSegment 407103744 407169280 (10177054737831 / 25000) (10178711079819 / 25000) := by
  exact
    packedTile32768 407103744 407169280 13 3342 20176 29 _ _ (247807 / 12500) (1982459 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell407169280 :
    ThetaLowerSegment 407169280 407234816 (10178711079819 / 25000) (10180363470231 / 25000) := by
  exact
    packedTile32768 407169280 407234816 13 3334 20178 29 _ _ (247809 / 12500) (79299 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell407234816 :
    ThetaLowerSegment 407234816 407300352 (10180363470231 / 25000) (20363968309977 / 50000) := by
  exact
    packedTile32768 407234816 407300352 13 3270 20180 29 _ _ (1982489 / 100000) (495623 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell407300352 :
    ThetaLowerSegment 407300352 407365888 (20363968309977 / 50000) (20367199793127 / 50000) := by
  exact
    packedTile32768 407300352 407365888 13 3260 20181 29 _ _ (396501 / 20000) (495627 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell407365888 :
    ThetaLowerSegment 407365888 407431424 (20367199793127 / 50000) (10185220607481 / 25000) := by
  exact
    packedTile32768 407365888 407431424 13 3270 20183 29 _ _ (1982521 / 100000) (495631 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell407431424 :
    ThetaLowerSegment 407431424 407496960 (10185220607481 / 25000) (10186842322747 / 25000) := by
  exact
    packedTile32768 407431424 407496960 13 3272 20184 29 _ _ (1982537 / 100000) (99127 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell407496960 :
    ThetaLowerSegment 407496960 407562496 (10186842322747 / 25000) (40753996965667 / 100000) := by
  exact
    packedTile32768 407496960 407562496 13 3343 20186 29 _ _ (1982553 / 100000) (495639 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell407562496 :
    ThetaLowerSegment 407562496 407628032 (40753996965667 / 100000) (8152112646839 / 20000) := by
  exact
    packedTile32768 407562496 407628032 13 3312 20188 29 _ _ (1982569 / 100000) (495643 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell407628032 :
    ThetaLowerSegment 407628032 407693568 (8152112646839 / 20000) (2038355783881 / 5000) := by
  exact
    packedTile32768 407628032 407693568 13 3305 20189 29 _ _ (396517 / 20000) (495647 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell407693568 :
    ThetaLowerSegment 407693568 407759104 (2038355783881 / 5000) (8154721739179 / 20000) := by
  exact
    packedTile32768 407693568 407759104 13 3275 20191 29 _ _ (1982601 / 100000) (495651 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell407759104 :
    ThetaLowerSegment 407759104 407824640 (8154721739179 / 20000) (20390074674689 / 50000) := by
  exact
    packedTile32768 407759104 407824640 13 3299 20193 29 _ _ (1982617 / 100000) (99131 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell407824640 :
    ThetaLowerSegment 407824640 407890176 (20390074674689 / 50000) (40786757465167 / 100000) := by
  exact
    packedTile32768 407824640 407890176 13 3333 20194 29 _ _ (1982633 / 100000) (495659 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell407890176 :
    ThetaLowerSegment 407890176 407955712 (40786757465167 / 100000) (40793280380377 / 100000) := by
  exact
    packedTile32768 407890176 407955712 13 3290 20196 29 _ _ (1982649 / 100000) (495663 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell407955712 :
    ThetaLowerSegment 407955712 408021248 (40793280380377 / 100000) (40799823174877 / 100000) := by
  exact
    packedTile32768 407955712 408021248 13 3300 20197 29 _ _ (396533 / 20000) (495667 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell408021248 :
    ThetaLowerSegment 408021248 408086784 (40799823174877 / 100000) (20403227621411 / 50000) := by
  exact
    packedTile32768 408021248 408086784 13 3345 20199 29 _ _ (1982681 / 100000) (495671 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell408086784 :
    ThetaLowerSegment 408086784 408152320 (20403227621411 / 50000) (20406461401849 / 50000) := by
  exact
    packedTile32768 408086784 408152320 13 3262 20201 29 _ _ (991349 / 50000) (1982701 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell408152320 :
    ThetaLowerSegment 408152320 408217856 (20406461401849 / 50000) (2040970611331 / 5000) := by
  exact
    packedTile32768 408152320 408217856 13 3273 20202 29 _ _ (991357 / 50000) (1982717 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell408217856 :
    ThetaLowerSegment 408217856 408283392 (2040970611331 / 5000) (408259076501 / 1000) := by
  exact
    packedTile32768 408217856 408283392 13 3276 20204 29 _ _ (198273 / 10000) (1982733 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell408283392 :
    ThetaLowerSegment 408283392 408348928 (408259076501 / 1000) (10208104746991 / 25000) := by
  exact
    packedTile32768 408283392 408348928 13 3284 20206 29 _ _ (991373 / 50000) (1982749 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell408348928 :
    ThetaLowerSegment 408348928 408414464 (10208104746991 / 25000) (10209762336023 / 25000) := by
  exact
    packedTile32768 408348928 408414464 13 3344 20207 29 _ _ (991381 / 50000) (396553 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell408414464 :
    ThetaLowerSegment 408414464 408480000 (10209762336023 / 25000) (816910303663 / 2000) := by
  exact
    packedTile32768 408414464 408480000 13 3261 20209 29 _ _ (991389 / 50000) (1982781 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell408480000 :
    ThetaLowerSegment 408480000 408545536 (816910303663 / 2000) (1276624904273 / 3125) := by
  exact
    packedTile32768 408480000 408545536 13 3269 20210 29 _ _ (991397 / 50000) (1982797 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell408545536 :
    ThetaLowerSegment 408545536 408611072 (1276624904273 / 3125) (5107315543407 / 12500) := by
  exact
    packedTile32768 408545536 408611072 13 3292 20212 29 _ _ (198281 / 10000) (1982813 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell408611072 :
    ThetaLowerSegment 408611072 408676608 (5107315543407 / 12500) (20432550690549 / 50000) := by
  exact
    packedTile32768 408611072 408676608 13 3317 20214 29 _ _ (991413 / 50000) (1982829 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell408676608 :
    ThetaLowerSegment 408676608 408742144 (20432550690549 / 50000) (204358531139 / 500) := by
  exact
    packedTile32768 408676608 408742144 13 3331 20215 29 _ _ (991421 / 50000) (396569 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell408742144 :
    ThetaLowerSegment 408742144 408807680 (204358531139 / 500) (1277447284708 / 3125) := by
  exact
    packedTile32768 408742144 408807680 13 3332 20217 29 _ _ (991429 / 50000) (1982861 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell408807680 :
    ThetaLowerSegment 408807680 408873216 (1277447284708 / 3125) (10221213157277 / 25000) := by
  exact
    packedTile32768 408807680 408873216 13 3298 20218 29 _ _ (991437 / 50000) (1982877 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell408873216 :
    ThetaLowerSegment 408873216 408938752 (10221213157277 / 25000) (1277858732734 / 3125) := by
  exact
    packedTile32768 408873216 408938752 13 3342 20220 29 _ _ (198289 / 10000) (1982893 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell408938752 :
    ThetaLowerSegment 408938752 409004288 (1277858732734 / 3125) (2556128918463 / 6250) := by
  exact
    packedTile32768 408938752 409004288 13 3320 20222 29 _ _ (991453 / 50000) (1982909 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell409004288 :
    ThetaLowerSegment 409004288 409069824 (2556128918463 / 6250) (511307480079 / 1250) := by
  exact
    packedTile32768 409004288 409069824 13 3296 20223 29 _ _ (991461 / 50000) (79317 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell409069824 :
    ThetaLowerSegment 409069824 409135360 (511307480079 / 1250) (204555313921 / 500) := by
  exact
    packedTile32768 409069824 409135360 13 3260 20225 29 _ _ (991469 / 50000) (1982941 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell409135360 :
    ThetaLowerSegment 409135360 409200896 (204555313921 / 500) (10229380812083 / 25000) := by
  exact
    packedTile32768 409135360 409200896 13 3258 20227 29 _ _ (991477 / 50000) (1982957 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell409200896 :
    ThetaLowerSegment 409200896 409266432 (10229380812083 / 25000) (20462042448031 / 50000) := by
  exact
    packedTile32768 409200896 409266432 13 3309 20228 29 _ _ (198297 / 10000) (1982973 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell409266432 :
    ThetaLowerSegment 409266432 409331968 (20462042448031 / 50000) (4093062478389 / 10000) := by
  exact
    packedTile32768 409266432 409331968 13 3298 20230 29 _ _ (991493 / 50000) (1982989 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell409331968 :
    ThetaLowerSegment 409331968 409397504 (4093062478389 / 10000) (20468612107273 / 50000) := by
  exact
    packedTile32768 409331968 409397504 13 3328 20231 29 _ _ (991501 / 50000) (396601 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell409397504 :
    ThetaLowerSegment 409397504 409463040 (20468612107273 / 50000) (20471800800217 / 50000) := by
  exact
    packedTile32768 409397504 409463040 13 3216 20233 29 _ _ (991509 / 50000) (1983021 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell409463040 :
    ThetaLowerSegment 409463040 409528576 (20471800800217 / 50000) (10237562678359 / 25000) := by
  exact
    packedTile32768 409463040 409528576 13 3353 20235 29 _ _ (991517 / 50000) (1983037 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell409528576 :
    ThetaLowerSegment 409528576 409594112 (10237562678359 / 25000) (1279899217123 / 3125) := by
  exact
    packedTile32768 409528576 409594112 13 3290 20236 29 _ _ (39661 / 2000) (1983053 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell409594112 :
    ThetaLowerSegment 409594112 409659648 (1279899217123 / 3125) (20481666473599 / 50000) := by
  exact
    packedTile32768 409594112 409659648 13 3307 20238 29 _ _ (991533 / 50000) (1983069 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell409659648 :
    ThetaLowerSegment 409659648 409725184 (20481666473599 / 50000) (256062240151 / 625) := by
  exact
    packedTile32768 409659648 409725184 13 3341 20240 29 _ _ (991541 / 50000) (396617 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell409725184 :
    ThetaLowerSegment 409725184 409790720 (256062240151 / 625) (10244146484419 / 25000) := by
  exact
    packedTile32768 409725184 409790720 13 3342 20241 29 _ _ (991549 / 50000) (1983101 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell409790720 :
    ThetaLowerSegment 409790720 409856256 (10244146484419 / 25000) (20491568081609 / 50000) := by
  exact
    packedTile32768 409790720 409856256 13 3303 20243 29 _ _ (991557 / 50000) (1983117 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell409856256 :
    ThetaLowerSegment 409856256 409921792 (20491568081609 / 50000) (20494838262979 / 50000) := by
  exact
    packedTile32768 409856256 409921792 13 3298 20244 29 _ _ (198313 / 10000) (1983133 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell409921792 :
    ThetaLowerSegment 409921792 409987328 (20494838262979 / 50000) (5124525878217 / 12500) := by
  exact
    packedTile32768 409921792 409987328 13 3293 20246 29 _ _ (991573 / 50000) (1983149 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell409987328 :
    ThetaLowerSegment 409987328 410052864 (5124525878217 / 12500) (820056893379 / 2000) := by
  exact
    packedTile32768 409987328 410052864 13 3347 20248 29 _ _ (991581 / 50000) (396633 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell410052864 :
    ThetaLowerSegment 410052864 410118400 (820056893379 / 2000) (20504672763217 / 50000) := by
  exact
    packedTile32768 410052864 410118400 13 3278 20249 29 _ _ (991589 / 50000) (1983181 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell410118400 :
    ThetaLowerSegment 410118400 410183936 (20504672763217 / 50000) (256348804723 / 625) := by
  exact
    packedTile32768 410118400 410183936 13 3259 20251 29 _ _ (991597 / 50000) (1983197 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell410183936 :
    ThetaLowerSegment 410183936 410249472 (256348804723 / 625) (4102245845881 / 10000) := by
  exact
    packedTile32768 410183936 410249472 13 3353 20252 29 _ _ (198321 / 10000) (1983213 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell410249472 :
    ThetaLowerSegment 410249472 410315008 (4102245845881 / 10000) (20514416273587 / 50000) := by
  exact
    packedTile32768 410249472 410315008 13 3214 20254 29 _ _ (991613 / 50000) (1983229 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell410315008 :
    ThetaLowerSegment 410315008 410380544 (20514416273587 / 50000) (4103545260897 / 10000) := by
  exact
    packedTile32768 410315008 410380544 13 3338 20256 29 _ _ (991621 / 50000) (396649 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell410380544 :
    ThetaLowerSegment 410380544 410446080 (4103545260897 / 10000) (4104203702553 / 10000) := by
  exact
    packedTile32768 410380544 410446080 13 3320 20257 29 _ _ (991629 / 50000) (1983261 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell410446080 :
    ThetaLowerSegment 410446080 410511616 (4104203702553 / 10000) (20524302814509 / 50000) := by
  exact
    packedTile32768 410446080 410511616 13 3312 20259 29 _ _ (991637 / 50000) (1983277 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell410511616 :
    ThetaLowerSegment 410511616 410577152 (20524302814509 / 50000) (20527610942229 / 50000) := by
  exact
    packedTile32768 410511616 410577152 13 3336 20261 29 _ _ (198329 / 10000) (1983293 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell410577152 :
    ThetaLowerSegment 410577152 410642688 (20527610942229 / 50000) (5132724567981 / 12500) := by
  exact
    packedTile32768 410577152 410642688 13 3315 20262 29 _ _ (991653 / 50000) (1983309 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell410642688 :
    ThetaLowerSegment 410642688 410708224 (5132724567981 / 12500) (20534175711529 / 50000) := by
  exact
    packedTile32768 410642688 410708224 13 3305 20264 29 _ _ (991661 / 50000) (79333 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell410708224 :
    ThetaLowerSegment 410708224 410773760 (20534175711529 / 50000) (2567182886783 / 6250) := by
  exact
    packedTile32768 410708224 410773760 13 3315 20265 29 _ _ (991669 / 50000) (1983341 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell410773760 :
    ThetaLowerSegment 410773760 410839296 (2567182886783 / 6250) (4108157637449 / 10000) := by
  exact
    packedTile32768 410773760 410839296 13 3353 20267 29 _ _ (991677 / 50000) (1983357 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell410839296 :
    ThetaLowerSegment 410839296 410904832 (4108157637449 / 10000) (4108814132919 / 10000) := by
  exact
    packedTile32768 410839296 410904832 13 3310 20269 29 _ _ (198337 / 10000) (1983373 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell410904832 :
    ThetaLowerSegment 410904832 410970368 (4108814132919 / 10000) (10273677080059 / 25000) := by
  exact
    packedTile32768 410904832 410970368 13 3311 20270 29 _ _ (991693 / 50000) (1983389 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell410970368 :
    ThetaLowerSegment 410970368 411035904 (10273677080059 / 25000) (1027529454439 / 2500) := by
  exact
    packedTile32768 410970368 411035904 13 3262 20272 29 _ _ (991701 / 50000) (396681 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell411035904 :
    ThetaLowerSegment 411035904 411101440 (1027529454439 / 2500) (4110779287659 / 10000) := by
  exact
    packedTile32768 411035904 411101440 13 3335 20274 29 _ _ (991709 / 50000) (1983421 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell411101440 :
    ThetaLowerSegment 411101440 411166976 (4110779287659 / 10000) (10278588023207 / 25000) := by
  exact
    packedTile32768 411101440 411166976 13 3307 20275 29 _ _ (991717 / 50000) (1983437 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell411166976 :
    ThetaLowerSegment 411166976 411232512 (10278588023207 / 25000) (1285028046079 / 3125) := by
  exact
    packedTile32768 411166976 411232512 13 3300 20277 29 _ _ (1983449 / 100000) (495863 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell411232512 :
    ThetaLowerSegment 411232512 411298048 (1285028046079 / 3125) (41127492495653 / 100000) := by
  exact
    packedTile32768 411232512 411298048 13 3325 20278 29 _ _ (396693 / 20000) (495867 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell411298048 :
    ThetaLowerSegment 411298048 411363584 (41127492495653 / 100000) (164536445487 / 400) := by
  exact
    packedTile32768 411298048 411363584 13 3337 20280 29 _ _ (1983481 / 100000) (495871 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell411363584 :
    ThetaLowerSegment 411363584 411429120 (164536445487 / 400) (4114049823209 / 10000) := by
  exact
    packedTile32768 411363584 411429120 13 3220 20282 29 _ _ (1983497 / 100000) (3967 / 200)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell411429120 :
    ThetaLowerSegment 411429120 411494656 (4114049823209 / 10000) (41147037874451 / 100000) := by
  exact
    packedTile32768 411429120 411494656 13 3297 20283 29 _ _ (1983513 / 100000) (495879 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell411494656 :
    ThetaLowerSegment 411494656 411560192 (41147037874451 / 100000) (41153631124847 / 100000) := by
  exact
    packedTile32768 411494656 411560192 13 3324 20285 29 _ _ (1983529 / 100000) (495883 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell411560192 :
    ThetaLowerSegment 411560192 411625728 (41153631124847 / 100000) (10290060570083 / 25000) := by
  exact
    packedTile32768 411560192 411625728 13 3333 20286 29 _ _ (396709 / 20000) (495887 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell411625728 :
    ThetaLowerSegment 411625728 411691264 (10290060570083 / 25000) (41166857456267 / 100000) := by
  exact
    packedTile32768 411625728 411691264 13 3335 20288 29 _ _ (1983561 / 100000) (495891 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell411691264 :
    ThetaLowerSegment 411691264 411756800 (41166857456267 / 100000) (5146663754031 / 12500) := by
  exact
    packedTile32768 411691264 411756800 13 3253 20290 29 _ _ (1983577 / 100000) (99179 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell411756800 :
    ThetaLowerSegment 411756800 411822336 (5146663754031 / 12500) (1286868760892 / 3125) := by
  exact
    packedTile32768 411756800 411822336 13 3272 20291 29 _ _ (1983593 / 100000) (495899 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell411822336 :
    ThetaLowerSegment 411822336 411887872 (1286868760892 / 3125) (20593194948821 / 50000) := by
  exact
    packedTile32768 411822336 411887872 13 3322 20293 29 _ _ (1983609 / 100000) (495903 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell411887872 :
    ThetaLowerSegment 411887872 411953408 (20593194948821 / 50000) (41192854531517 / 100000) := by
  exact
    packedTile32768 411887872 411953408 13 3259 20295 29 _ _ (15869 / 800) (495907 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell411953408 :
    ThetaLowerSegment 411953408 412018944 (41192854531517 / 100000) (20599756807177 / 50000) := by
  exact
    packedTile32768 411953408 412018944 13 3357 20296 29 _ _ (1983641 / 100000) (495911 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell412018944 :
    ThetaLowerSegment 412018944 412084480 (20599756807177 / 50000) (20603026864093 / 50000) := by
  exact
    packedTile32768 412018944 412084480 13 3297 20298 29 _ _ (247957 / 12500) (1983659 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell412084480 :
    ThetaLowerSegment 412084480 412150016 (20603026864093 / 50000) (20606283061681 / 50000) := by
  exact
    packedTile32768 412084480 412150016 13 3283 20299 29 _ _ (247959 / 12500) (79347 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell412150016 :
    ThetaLowerSegment 412150016 412215552 (20606283061681 / 50000) (20609550195817 / 50000) := by
  exact
    packedTile32768 412150016 412215552 13 3294 20301 29 _ _ (247961 / 12500) (1983691 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell412215552 :
    ThetaLowerSegment 412215552 412281088 (20609550195817 / 50000) (20612759828889 / 50000) := by
  exact
    packedTile32768 412215552 412281088 13 3236 20303 29 _ _ (247963 / 12500) (1983707 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell412281088 :
    ThetaLowerSegment 412281088 412346624 (20612759828889 / 50000) (20616092478489 / 50000) := by
  exact
    packedTile32768 412281088 412346624 13 3360 20304 29 _ _ (49593 / 2500) (1983723 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell412346624 :
    ThetaLowerSegment 412346624 412412160 (20616092478489 / 50000) (20619354732341 / 50000) := by
  exact
    packedTile32768 412346624 412412160 13 3289 20306 29 _ _ (247967 / 12500) (1983739 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell412412160 :
    ThetaLowerSegment 412412160 412477696 (20619354732341 / 50000) (20622620980009 / 50000) := by
  exact
    packedTile32768 412412160 412477696 13 3293 20307 29 _ _ (247969 / 12500) (396751 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell412477696 :
    ThetaLowerSegment 412477696 412543232 (20622620980009 / 50000) (825034736329 / 2000) := by
  exact
    packedTile32768 412477696 412543232 13 3274 20309 29 _ _ (247971 / 12500) (1983771 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell412543232 :
    ThetaLowerSegment 412543232 412608768 (825034736329 / 2000) (20629130741013 / 50000) := by
  exact
    packedTile32768 412543232 412608768 13 3289 20311 29 _ _ (247973 / 12500) (1983787 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell412608768 :
    ThetaLowerSegment 412608768 412674304 (20629130741013 / 50000) (20632424840913 / 50000) := by
  exact
    packedTile32768 412608768 412674304 13 3321 20312 29 _ _ (9919 / 500) (1983803 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell412674304 :
    ThetaLowerSegment 412674304 412739840 (20632424840913 / 50000) (5158929989407 / 12500) := by
  exact
    packedTile32768 412674304 412739840 13 3322 20314 29 _ _ (396763 / 20000) (991909 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell412739840 :
    ThetaLowerSegment 412739840 412805376 (5158929989407 / 12500) (41277968703077 / 100000) := by
  exact
    packedTile32768 412739840 412805376 13 3291 20315 29 _ _ (1983831 / 100000) (991917 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell412805376 :
    ThetaLowerSegment 412805376 412870912 (41277968703077 / 100000) (20642268610247 / 50000) := by
  exact
    packedTile32768 412805376 412870912 13 3311 20317 29 _ _ (1983847 / 100000) (39677 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell412870912 :
    ThetaLowerSegment 412870912 412936448 (20642268610247 / 50000) (41291145468147 / 100000) := by
  exact
    packedTile32768 412870912 412936448 13 3331 20319 29 _ _ (1983863 / 100000) (991933 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell412936448 :
    ThetaLowerSegment 412936448 413001984 (41291145468147 / 100000) (41297751785217 / 100000) := by
  exact
    packedTile32768 412936448 413001984 13 3330 20320 29 _ _ (1983879 / 100000) (991941 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell413001984 :
    ThetaLowerSegment 413001984 413067520 (41297751785217 / 100000) (2581519284887 / 6250) := by
  exact
    packedTile32768 413001984 413067520 13 3305 20322 29 _ _ (396779 / 20000) (991949 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell413067520 :
    ThetaLowerSegment 413067520 413133056 (2581519284887 / 6250) (5163865860661 / 12500) := by
  exact
    packedTile32768 413067520 413133056 13 3336 20324 29 _ _ (1983911 / 100000) (991957 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell413133056 :
    ThetaLowerSegment 413133056 413198592 (5163865860661 / 12500) (41317372664111 / 100000) := by
  exact
    packedTile32768 413133056 413198592 13 3249 20325 29 _ _ (1983927 / 100000) (198393 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell413198592 :
    ThetaLowerSegment 413198592 413264128 (41317372664111 / 100000) (41323866106277 / 100000) := by
  exact
    packedTile32768 413198592 413264128 13 3273 20327 29 _ _ (991971 / 50000) (396789 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell413264128 :
    ThetaLowerSegment 413264128 413329664 (41323866106277 / 100000) (41330452846837 / 100000) := by
  exact
    packedTile32768 413264128 413329664 13 3320 20328 29 _ _ (991979 / 50000) (1983961 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell413329664 :
    ThetaLowerSegment 413329664 413395200 (41330452846837 / 100000) (41337029720647 / 100000) := by
  exact
    packedTile32768 413329664 413395200 13 3315 20330 29 _ _ (991987 / 50000) (1983977 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell413395200 :
    ThetaLowerSegment 413395200 413460736 (41337029720647 / 100000) (41343570935677 / 100000) := by
  exact
    packedTile32768 413395200 413460736 13 3297 20332 29 _ _ (198399 / 10000) (1983993 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell413460736 :
    ThetaLowerSegment 413460736 413526272 (41343570935677 / 100000) (41350086411381 / 100000) := by
  exact
    packedTile32768 413460736 413526272 13 3284 20333 29 _ _ (992003 / 50000) (1984009 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell413526272 :
    ThetaLowerSegment 413526272 413591808 (41350086411381 / 100000) (41356661460289 / 100000) := by
  exact
    packedTile32768 413526272 413591808 13 3314 20335 29 _ _ (992011 / 50000) (79361 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell413591808 :
    ThetaLowerSegment 413591808 413657344 (41356661460289 / 100000) (8272656439019 / 20000) := by
  exact
    packedTile32768 413591808 413657344 13 3337 20336 29 _ _ (992019 / 50000) (1984041 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell413657344 :
    ThetaLowerSegment 413657344 413722880 (8272656439019 / 20000) (20684945537819 / 50000) := by
  exact
    packedTile32768 413657344 413722880 13 3331 20338 29 _ _ (1984053 / 100000) (248007 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell413722880 :
    ThetaLowerSegment 413722880 413788416 (20684945537819 / 50000) (827530674773 / 2000) := by
  exact
    packedTile32768 413722880 413788416 13 3348 20340 29 _ _ (1984069 / 100000) (248009 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell413788416 :
    ThetaLowerSegment 413788416 413853952 (827530674773 / 2000) (4138304947379 / 10000) := by
  exact
    packedTile32768 413788416 413853952 13 3284 20341 29 _ _ (396817 / 20000) (248011 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell413853952 :
    ThetaLowerSegment 413853952 413919488 (4138304947379 / 10000) (5173683257053 / 12500) := by
  exact
    packedTile32768 413853952 413919488 13 3234 20343 29 _ _ (1984101 / 100000) (248013 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell413919488 :
    ThetaLowerSegment 413919488 413985024 (5173683257053 / 12500) (41396047372513 / 100000) := by
  exact
    packedTile32768 413919488 413985024 13 3317 20345 29 _ _ (1984117 / 100000) (49603 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell413985024 :
    ThetaLowerSegment 413985024 414050560 (41396047372513 / 100000) (20701322307369 / 50000) := by
  exact
    packedTile32768 413985024 414050560 13 3325 20346 29 _ _ (1984133 / 100000) (248017 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell414050560 :
    ThetaLowerSegment 414050560 414116096 (20701322307369 / 50000) (20704593175347 / 50000) := by
  exact
    packedTile32768 414050560 414116096 13 3297 20348 29 _ _ (496037 / 25000) (1984151 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell414116096 :
    ThetaLowerSegment 414116096 414181632 (20704593175347 / 50000) (20707892840079 / 50000) := by
  exact
    packedTile32768 414116096 414181632 13 3326 20349 29 _ _ (496041 / 25000) (1984167 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell414181632 :
    ThetaLowerSegment 414181632 414247168 (20707892840079 / 50000) (20711202452319 / 50000) := by
  exact
    packedTile32768 414181632 414247168 13 3336 20351 29 _ _ (99209 / 5000) (1984183 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell414247168 :
    ThetaLowerSegment 414247168 414312704 (20711202452319 / 50000) (20714477367817 / 50000) := by
  exact
    packedTile32768 414247168 414312704 13 3301 20353 29 _ _ (496049 / 25000) (1984199 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell414312704 :
    ThetaLowerSegment 414312704 414378240 (20714477367817 / 50000) (20717804891341 / 50000) := by
  exact
    packedTile32768 414312704 414378240 13 3354 20354 29 _ _ (496053 / 25000) (396843 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell414378240 :
    ThetaLowerSegment 414378240 414443776 (20717804891341 / 50000) (41442100189199 / 100000) := by
  exact
    packedTile32768 414378240 414443776 13 3271 20356 29 _ _ (1984227 / 100000) (198423 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell414443776 :
    ThetaLowerSegment 414443776 414509312 (41442100189199 / 100000) (8289746305861 / 20000) := by
  exact
    packedTile32768 414443776 414509312 13 3342 20357 29 _ _ (1984243 / 100000) (992123 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell414509312 :
    ThetaLowerSegment 414509312 414574848 (8289746305861 / 20000) (10363830313361 / 25000) := by
  exact
    packedTile32768 414509312 414574848 13 3321 20359 29 _ _ (1984259 / 100000) (992131 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell414574848 :
    ThetaLowerSegment 414574848 414640384 (10363830313361 / 25000) (41461819754069 / 100000) := by
  exact
    packedTile32768 414574848 414640384 13 3275 20361 29 _ _ (79371 / 4000) (992139 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell414640384 :
    ThetaLowerSegment 414640384 414705920 (41461819754069 / 100000) (10367060726009 / 25000) := by
  exact
    packedTile32768 414640384 414705920 13 3237 20362 29 _ _ (1984291 / 100000) (992147 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell414705920 :
    ThetaLowerSegment 414705920 414771456 (10367060726009 / 25000) (10368715638047 / 25000) := by
  exact
    packedTile32768 414705920 414771456 13 3336 20364 29 _ _ (1984307 / 100000) (198431 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell414771456 :
    ThetaLowerSegment 414771456 414836992 (10368715638047 / 25000) (4148143264233 / 10000) := by
  exact
    packedTile32768 414771456 414836992 13 3311 20365 29 _ _ (992161 / 50000) (79373 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell414836992 :
    ThetaLowerSegment 414836992 414902528 (4148143264233 / 10000) (20743976588499 / 50000) := by
  exact
    packedTile32768 414836992 414902528 13 3286 20367 29 _ _ (992169 / 50000) (1984341 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell414902528 :
    ThetaLowerSegment 414902528 414968064 (20743976588499 / 50000) (10373595124901 / 25000) := by
  exact
    packedTile32768 414902528 414968064 13 3239 20369 29 _ _ (992177 / 50000) (1984357 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell414968064 :
    ThetaLowerSegment 414968064 415033600 (10373595124901 / 25000) (20750513077367 / 50000) := by
  exact
    packedTile32768 414968064 415033600 13 3349 20370 29 _ _ (198437 / 10000) (1984373 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell415033600 :
    ThetaLowerSegment 415033600 415099136 (20750513077367 / 50000) (1037687430937 / 2500) := by
  exact
    packedTile32768 415033600 415099136 13 3261 20372 29 _ _ (992193 / 50000) (1984389 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell415099136 :
    ThetaLowerSegment 415099136 415164672 (1037687430937 / 2500) (8302811136557 / 20000) := by
  exact
    packedTile32768 415099136 415164672 13 3305 20373 29 _ _ (1984401 / 100000) (496101 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell415164672 :
    ThetaLowerSegment 415164672 415230208 (8302811136557 / 20000) (41520759043411 / 100000) := by
  exact
    packedTile32768 415164672 415230208 13 3378 20375 29 _ _ (1984417 / 100000) (99221 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell415230208 :
    ThetaLowerSegment 415230208 415295744 (41520759043411 / 100000) (41527275921383 / 100000) := by
  exact
    packedTile32768 415230208 415295744 13 3284 20377 29 _ _ (1984433 / 100000) (496109 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell415295744 :
    ThetaLowerSegment 415295744 415361280 (41527275921383 / 100000) (41533804758593 / 100000) := by
  exact
    packedTile32768 415295744 415361280 13 3290 20378 29 _ _ (1984449 / 100000) (496113 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell415361280 :
    ThetaLowerSegment 415361280 415426816 (41533804758593 / 100000) (41540422946033 / 100000) := by
  exact
    packedTile32768 415361280 415426816 13 3335 20380 29 _ _ (124029 / 6250) (1984467 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell415426816 :
    ThetaLowerSegment 415426816 415492352 (41540422946033 / 100000) (41547063016113 / 100000) := by
  exact
    packedTile32768 415426816 415492352 13 3346 20382 29 _ _ (12403 / 625) (1984483 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell415492352 :
    ThetaLowerSegment 415492352 415557888 (41547063016113 / 100000) (8310717210893 / 20000) := by
  exact
    packedTile32768 415492352 415557888 13 3287 20383 29 _ _ (124031 / 6250) (1984499 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell415557888 :
    ThetaLowerSegment 415557888 415623424 (8310717210893 / 20000) (41560059532609 / 100000) := by
  exact
    packedTile32768 415557888 415623424 13 3262 20385 29 _ _ (62016 / 3125) (396903 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell415623424 :
    ThetaLowerSegment 415623424 415688960 (41560059532609 / 100000) (41566550923697 / 100000) := by
  exact
    packedTile32768 415623424 415688960 13 3271 20386 29 _ _ (124033 / 6250) (1984531 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell415688960 :
    ThetaLowerSegment 415688960 415754496 (41566550923697 / 100000) (41573024502963 / 100000) := by
  exact
    packedTile32768 415688960 415754496 13 3262 20388 29 _ _ (1984543 / 100000) (992273 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell415754496 :
    ThetaLowerSegment 415754496 415820032 (41573024502963 / 100000) (4157967872929 / 10000) := by
  exact
    packedTile32768 415754496 415820032 13 3353 20390 29 _ _ (1984559 / 100000) (992281 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell415820032 :
    ThetaLowerSegment 415820032 415885568 (4157967872929 / 10000) (8317241199293 / 20000) := by
  exact
    packedTile32768 415820032 415885568 13 3289 20391 29 _ _ (79383 / 4000) (992289 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell415885568 :
    ThetaLowerSegment 415885568 415951104 (8317241199293 / 20000) (10398173406111 / 25000) := by
  exact
    packedTile32768 415885568 415951104 13 3269 20393 29 _ _ (1984591 / 100000) (992297 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell415951104 :
    ThetaLowerSegment 415951104 416016640 (10398173406111 / 25000) (20799675988787 / 50000) := by
  exact
    packedTile32768 415951104 416016640 13 3355 20394 29 _ _ (992303 / 50000) (1984609 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell416016640 :
    ThetaLowerSegment 416016640 416082176 (20799675988787 / 50000) (10401457942101 / 25000) := by
  exact
    packedTile32768 416016640 416082176 13 3265 20396 29 _ _ (992311 / 50000) (15877 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell416082176 :
    ThetaLowerSegment 416082176 416147712 (10401457942101 / 25000) (10403087329899 / 25000) := by
  exact
    packedTile32768 416082176 416147712 13 3284 20398 29 _ _ (992319 / 50000) (1984641 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell416147712 :
    ThetaLowerSegment 416147712 416213248 (10403087329899 / 25000) (2601182407771 / 6250) := by
  exact
    packedTile32768 416147712 416213248 13 3310 20399 29 _ _ (992327 / 50000) (1984657 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell416213248 :
    ThetaLowerSegment 416213248 416278784 (2601182407771 / 6250) (20812747858701 / 50000) := by
  exact
    packedTile32768 416213248 416278784 13 3314 20401 29 _ _ (1984669 / 100000) (62021 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell416278784 :
    ThetaLowerSegment 416278784 416344320 (20812747858701 / 50000) (20816006711471 / 50000) := by
  exact
    packedTile32768 416278784 416344320 13 3284 20402 29 _ _ (396937 / 20000) (124043 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell416344320 :
    ThetaLowerSegment 416344320 416409856 (20816006711471 / 50000) (41638676064199 / 100000) := by
  exact
    packedTile32768 416344320 416409856 13 3357 20404 29 _ _ (1984701 / 100000) (62022 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell416409856 :
    ThetaLowerSegment 416409856 416475392 (41638676064199 / 100000) (41645146241619 / 100000) := by
  exact
    packedTile32768 416409856 416475392 13 3260 20406 29 _ _ (1984717 / 100000) (24809 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell416475392 :
    ThetaLowerSegment 416475392 416540928 (41645146241619 / 100000) (8330340362283 / 20000) := by
  exact
    packedTile32768 416475392 416540928 13 3303 20407 29 _ _ (496183 / 25000) (396947 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell416540928 :
    ThetaLowerSegment 416540928 416606464 (8330340362283 / 20000) (41658249495067 / 100000) := by
  exact
    packedTile32768 416540928 416606464 13 3299 20409 29 _ _ (496187 / 25000) (1984751 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell416606464 :
    ThetaLowerSegment 416606464 416672000 (41658249495067 / 100000) (41664904408759 / 100000) := by
  exact
    packedTile32768 416606464 416672000 13 3353 20410 29 _ _ (496191 / 25000) (1984767 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell416672000 :
    ThetaLowerSegment 416672000 416737536 (41664904408759 / 100000) (5208939463451 / 12500) := by
  exact
    packedTile32768 416672000 416737536 13 3331 20412 29 _ _ (1984779 / 100000) (992391 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell416737536 :
    ThetaLowerSegment 416737536 416803072 (5208939463451 / 12500) (41678075455083 / 100000) := by
  exact
    packedTile32768 416737536 416803072 13 3305 20414 29 _ _ (396959 / 20000) (992399 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell416803072 :
    ThetaLowerSegment 416803072 416868608 (41678075455083 / 100000) (5210567001861 / 12500) := by
  exact
    packedTile32768 416803072 416868608 13 3255 20415 29 _ _ (1984811 / 100000) (992407 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell416868608 :
    ThetaLowerSegment 416868608 416934144 (5210567001861 / 12500) (8338245373341 / 20000) := by
  exact
    packedTile32768 416868608 416934144 13 3371 20417 29 _ _ (1984827 / 100000) (198483 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell416934144 :
    ThetaLowerSegment 416934144 416999680 (8338245373341 / 20000) (41697679588047 / 100000) := by
  exact
    packedTile32768 416934144 416999680 13 3251 20418 29 _ _ (992421 / 50000) (396969 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell416999680 :
    ThetaLowerSegment 416999680 417065216 (41697679588047 / 100000) (41704269316607 / 100000) := by
  exact
    packedTile32768 416999680 417065216 13 3320 20420 29 _ _ (992429 / 50000) (1984861 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell417065216 :
    ThetaLowerSegment 417065216 417130752 (41704269316607 / 100000) (41710849173917 / 100000) := by
  exact
    packedTile32768 417065216 417130752 13 3315 20422 29 _ _ (992437 / 50000) (1984877 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell417130752 :
    ThetaLowerSegment 417130752 417196288 (41710849173917 / 100000) (41717405265587 / 100000) := by
  exact
    packedTile32768 417130752 417196288 13 3303 20423 29 _ _ (198489 / 10000) (1984893 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell417196288 :
    ThetaLowerSegment 417196288 417261824 (41717405265587 / 100000) (41723999119997 / 100000) := by
  exact
    packedTile32768 417196288 417261824 13 3322 20425 29 _ _ (396981 / 20000) (496227 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell417261824 :
    ThetaLowerSegment 417261824 417327360 (41723999119997 / 100000) (10432642798357 / 25000) := by
  exact
    packedTile32768 417261824 417327360 13 3311 20426 29 _ _ (1984921 / 100000) (496231 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell417327360 :
    ThetaLowerSegment 417327360 417392896 (10432642798357 / 25000) (41737159199331 / 100000) := by
  exact
    packedTile32768 417327360 417392896 13 3319 20428 29 _ _ (1984937 / 100000) (99247 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell417392896 :
    ThetaLowerSegment 417392896 417458432 (41737159199331 / 100000) (41743731375403 / 100000) := by
  exact
    packedTile32768 417392896 417458432 13 3311 20430 29 _ _ (248119 / 12500) (396991 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell417458432 :
    ThetaLowerSegment 417458432 417523968 (41743731375403 / 100000) (8350050002063 / 20000) := by
  exact
    packedTile32768 417458432 417523968 13 3284 20431 29 _ _ (248121 / 12500) (1984971 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell417523968 :
    ThetaLowerSegment 417523968 417589504 (8350050002063 / 20000) (41756826262307 / 100000) := by
  exact
    packedTile32768 417523968 417589504 13 3313 20433 29 _ _ (248123 / 12500) (1984987 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell417589504 :
    ThetaLowerSegment 417589504 417655040 (41756826262307 / 100000) (41763412488989 / 100000) := by
  exact
    packedTile32768 417589504 417655040 13 3318 20435 29 _ _ (1984999 / 100000) (992501 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell417655040 :
    ThetaLowerSegment 417655040 417720576 (41763412488989 / 100000) (10442489270861 / 25000) := by
  exact
    packedTile32768 417655040 417720576 13 3297 20436 29 _ _ (397003 / 20000) (992509 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell417720576 :
    ThetaLowerSegment 417720576 417786112 (10442489270861 / 25000) (20888263768027 / 50000) := by
  exact
    packedTile32768 417720576 417786112 13 3310 20438 29 _ _ (1985031 / 100000) (992517 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell417786112 :
    ThetaLowerSegment 417786112 417851648 (20888263768027 / 50000) (5222871374827 / 12500) := by
  exact
    packedTile32768 417786112 417851648 13 3246 20439 29 _ _ (1985047 / 100000) (39701 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell417851648 :
    ThetaLowerSegment 417851648 417917184 (5222871374827 / 12500) (10447379433273 / 25000) := by
  exact
    packedTile32768 417851648 417917184 13 3298 20441 29 _ _ (992531 / 50000) (397013 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell417917184 :
    ThetaLowerSegment 417917184 417982720 (10447379433273 / 25000) (2612246092209 / 6250) := by
  exact
    packedTile32768 417917184 417982720 13 3234 20443 29 _ _ (992539 / 50000) (1985081 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell417982720 :
    ThetaLowerSegment 417982720 418048256 (2612246092209 / 6250) (5225311035693 / 12500) := by
  exact
    packedTile32768 417982720 418048256 13 3300 20444 29 _ _ (992547 / 50000) (1985097 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell418048256 :
    ThetaLowerSegment 418048256 418113792 (5225311035693 / 12500) (10452224054349 / 25000) := by
  exact
    packedTile32768 418048256 418113792 13 3228 20446 29 _ _ (1985109 / 100000) (248139 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell418113792 :
    ThetaLowerSegment 418113792 418179328 (10452224054349 / 25000) (20907832746823 / 50000) := by
  exact
    packedTile32768 418113792 418179328 13 3410 20447 29 _ _ (15881 / 800) (248141 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell418179328 :
    ThetaLowerSegment 418179328 418244864 (20907832746823 / 50000) (10455567018153 / 25000) := by
  exact
    packedTile32768 418179328 418244864 13 3326 20449 29 _ _ (1985141 / 100000) (248143 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell418244864 :
    ThetaLowerSegment 418244864 418310400 (10455567018153 / 25000) (10457200801541 / 25000) := by
  exact
    packedTile32768 418244864 418310400 13 3292 20451 29 _ _ (496289 / 25000) (1985159 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell418310400 :
    ThetaLowerSegment 418310400 418375936 (10457200801541 / 25000) (10458821694479 / 25000) := by
  exact
    packedTile32768 418310400 418375936 13 3266 20452 29 _ _ (496293 / 25000) (79407 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell418375936 :
    ThetaLowerSegment 418375936 418441472 (10458821694479 / 25000) (10460435652323 / 25000) := by
  exact
    packedTile32768 418375936 418441472 13 3252 20454 29 _ _ (496297 / 25000) (1985191 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell418441472 :
    ThetaLowerSegment 418441472 418507008 (10460435652323 / 25000) (20924144904393 / 50000) := by
  exact
    packedTile32768 418441472 418507008 13 3298 20455 29 _ _ (1985203 / 100000) (992603 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell418507008 :
    ThetaLowerSegment 418507008 418572544 (20924144904393 / 50000) (10463731102671 / 25000) := by
  exact
    packedTile32768 418507008 418572544 13 3342 20457 29 _ _ (1985219 / 100000) (992611 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell418572544 :
    ThetaLowerSegment 418572544 418638080 (10463731102671 / 25000) (41861342675439 / 100000) := by
  exact
    packedTile32768 418572544 418638080 13 3233 20459 29 _ _ (397047 / 20000) (992619 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell418638080 :
    ThetaLowerSegment 418638080 418703616 (41861342675439 / 100000) (41867997233439 / 100000) := by
  exact
    packedTile32768 418638080 418703616 13 3352 20460 29 _ _ (7941 / 400) (1985253 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell418703616 :
    ThetaLowerSegment 418703616 418769152 (41867997233439 / 100000) (41874528758579 / 100000) := by
  exact
    packedTile32768 418703616 418769152 13 3290 20462 29 _ _ (992633 / 50000) (1985269 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell418769152 :
    ThetaLowerSegment 418769152 418834688 (41874528758579 / 100000) (41881169526869 / 100000) := by
  exact
    packedTile32768 418769152 418834688 13 3345 20463 29 _ _ (992641 / 50000) (397057 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell418834688 :
    ThetaLowerSegment 418834688 418900224 (41881169526869 / 100000) (20943825760787 / 50000) := by
  exact
    packedTile32768 418834688 418900224 13 3265 20465 29 _ _ (1985297 / 100000) (19853 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell418900224 :
    ThetaLowerSegment 418900224 418965760 (20943825760787 / 50000) (41894173274779 / 100000) := by
  exact
    packedTile32768 418900224 418965760 13 3285 20467 29 _ _ (1985313 / 100000) (496329 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell418965760 :
    ThetaLowerSegment 418965760 419031296 (41894173274779 / 100000) (41900716915867 / 100000) := by
  exact
    packedTile32768 418965760 419031296 13 3296 20468 29 _ _ (124083 / 6250) (1985331 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell419031296 :
    ThetaLowerSegment 419031296 419096832 (41900716915867 / 100000) (1676285341907 / 4000) := by
  exact
    packedTile32768 419031296 419096832 13 3232 20470 29 _ _ (62042 / 3125) (1985347 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell419096832 :
    ThetaLowerSegment 419096832 419162368 (1676285341907 / 4000) (8382739826639 / 20000) := by
  exact
    packedTile32768 419096832 419162368 13 3307 20471 29 _ _ (24817 / 1250) (1985363 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell419162368 :
    ThetaLowerSegment 419162368 419227904 (8382739826639 / 20000) (4192026873907 / 10000) := by
  exact
    packedTile32768 419162368 419227904 13 3309 20473 29 _ _ (15883 / 800) (992689 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell419227904 :
    ThetaLowerSegment 419227904 419293440 (4192026873907 / 10000) (41926786777723 / 100000) := by
  exact
    packedTile32768 419227904 419293440 13 3283 20475 29 _ _ (1985391 / 100000) (992697 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell419293440 :
    ThetaLowerSegment 419293440 419358976 (41926786777723 / 100000) (41933298912683 / 100000) := by
  exact
    packedTile32768 419293440 419358976 13 3280 20476 29 _ _ (1985407 / 100000) (198541 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell419358976 :
    ThetaLowerSegment 419358976 419424512 (41933298912683 / 100000) (41939819038531 / 100000) := by
  exact
    packedTile32768 419358976 419424512 13 3284 20478 29 _ _ (992711 / 50000) (79417 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell419424512 :
    ThetaLowerSegment 419424512 419490048 (41939819038531 / 100000) (41946372969369 / 100000) := by
  exact
    packedTile32768 419424512 419490048 13 3301 20479 29 _ _ (992719 / 50000) (1985441 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell419490048 :
    ThetaLowerSegment 419490048 419555584 (41946372969369 / 100000) (8390574669153 / 20000) := by
  exact
    packedTile32768 419490048 419555584 13 3274 20481 29 _ _ (992727 / 50000) (1985457 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell419555584 :
    ThetaLowerSegment 419555584 419621120 (8390574669153 / 20000) (41959389655023 / 100000) := by
  exact
    packedTile32768 419555584 419621120 13 3282 20483 29 _ _ (1985469 / 100000) (62046 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell419621120 :
    ThetaLowerSegment 419621120 419686656 (41959389655023 / 100000) (41966017203953 / 100000) := by
  exact
    packedTile32768 419621120 419686656 13 3338 20484 29 _ _ (397097 / 20000) (124093 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell419686656 :
    ThetaLowerSegment 419686656 419752192 (41966017203953 / 100000) (41972559426453 / 100000) := by
  exact
    packedTile32768 419686656 419752192 13 3295 20486 29 _ _ (3971 / 200) (1985503 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell419752192 :
    ThetaLowerSegment 419752192 419817728 (41972559426453 / 100000) (41979256571921 / 100000) := by
  exact
    packedTile32768 419752192 419817728 13 3373 20487 29 _ _ (496379 / 25000) (1985519 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell419817728 :
    ThetaLowerSegment 419817728 419883264 (41979256571921 / 100000) (41985727420709 / 100000) := by
  exact
    packedTile32768 419817728 419883264 13 3259 20489 29 _ _ (496383 / 25000) (397107 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell419883264 :
    ThetaLowerSegment 419883264 419948800 (41985727420709 / 100000) (41992120882049 / 100000) := by
  exact
    packedTile32768 419883264 419948800 13 3220 20491 29 _ _ (1985547 / 100000) (39711 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell419948800 :
    ThetaLowerSegment 419948800 420014336 (41992120882049 / 100000) (10499642994059 / 25000) := by
  exact
    packedTile32768 419948800 420014336 13 3249 20492 29 _ _ (1985563 / 100000) (992783 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell420014336 :
    ThetaLowerSegment 420014336 420079872 (10499642994059 / 25000) (1312659020101 / 3125) := by
  exact
    packedTile32768 420014336 420079872 13 3282 20494 29 _ _ (992789 / 50000) (1985581 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell420079872 :
    ThetaLowerSegment 420079872 420145408 (1312659020101 / 3125) (5251451166741 / 12500) := by
  exact
    packedTile32768 420079872 420145408 13 3284 20495 29 _ _ (992797 / 50000) (1985597 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell420145408 :
    ThetaLowerSegment 420145408 420210944 (5251451166741 / 12500) (21009083901879 / 50000) := by
  exact
    packedTile32768 420145408 420210944 13 3303 20497 29 _ _ (198561 / 10000) (1985613 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell420210944 :
    ThetaLowerSegment 420210944 420276480 (21009083901879 / 50000) (10506181084377 / 25000) := by
  exact
    packedTile32768 420210944 420276480 13 3302 20499 29 _ _ (3177 / 160) (496407 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell420276480 :
    ThetaLowerSegment 420276480 420342016 (10506181084377 / 25000) (4203128092409 / 10000) := by
  exact
    packedTile32768 420276480 420342016 13 3302 20500 29 _ _ (1985641 / 100000) (496411 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell420342016 :
    ThetaLowerSegment 420342016 420407552 (4203128092409 / 10000) (21018919772929 / 50000) := by
  exact
    packedTile32768 420342016 420407552 13 3303 20502 29 _ _ (248207 / 12500) (1985659 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell420407552 :
    ThetaLowerSegment 420407552 420473088 (21018919772929 / 50000) (21022183224861 / 50000) := by
  exact
    packedTile32768 420407552 420473088 13 3287 20503 29 _ _ (248209 / 12500) (79427 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell420473088 :
    ThetaLowerSegment 420473088 420538624 (21022183224861 / 50000) (21025493366757 / 50000) := by
  exact
    packedTile32768 420473088 420538624 13 3334 20505 29 _ _ (248211 / 12500) (1985691 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell420538624 :
    ThetaLowerSegment 420538624 420604160 (21025493366757 / 50000) (2102881147647 / 5000) := by
  exact
    packedTile32768 420538624 420604160 13 3342 20507 29 _ _ (1985703 / 100000) (992853 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell420604160 :
    ThetaLowerSegment 420604160 420669696 (2102881147647 / 5000) (42064169868483 / 100000) := by
  exact
    packedTile32768 420604160 420669696 13 3297 20508 29 _ _ (1985719 / 100000) (992861 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell420669696 :
    ThetaLowerSegment 420669696 420735232 (42064169868483 / 100000) (42070812148713 / 100000) := by
  exact
    packedTile32768 420669696 420735232 13 3345 20510 29 _ _ (992867 / 50000) (1985737 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell420735232 :
    ThetaLowerSegment 420735232 420800768 (42070812148713 / 100000) (42077448525213 / 100000) := by
  exact
    packedTile32768 420735232 420800768 13 3342 20511 29 _ _ (7943 / 400) (1985753 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell420800768 :
    ThetaLowerSegment 420800768 420866304 (42077448525213 / 100000) (42083882407053 / 100000) := by
  exact
    packedTile32768 420800768 420866304 13 3240 20513 29 _ _ (992883 / 50000) (1985769 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell420866304 :
    ThetaLowerSegment 420866304 420931840 (42083882407053 / 100000) (8418087891183 / 20000) := by
  exact
    packedTile32768 420866304 420931840 13 3302 20515 29 _ _ (1985781 / 100000) (248223 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell420931840 :
    ThetaLowerSegment 420931840 420997376 (8418087891183 / 20000) (42096917125729 / 100000) := by
  exact
    packedTile32768 420931840 420997376 13 3262 20516 29 _ _ (1985797 / 100000) (9929 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell420997376 :
    ThetaLowerSegment 420997376 421062912 (42096917125729 / 100000) (42103523922253 / 100000) := by
  exact
    packedTile32768 420997376 421062912 13 3327 20518 29 _ _ (496453 / 25000) (397163 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell421062912 :
    ThetaLowerSegment 421062912 421128448 (42103523922253 / 100000) (42110079140481 / 100000) := by
  exact
    packedTile32768 421062912 421128448 13 3301 20519 29 _ _ (496457 / 25000) (1985831 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell421128448 :
    ThetaLowerSegment 421128448 421193984 (42110079140481 / 100000) (5264585258557 / 12500) := by
  exact
    packedTile32768 421128448 421193984 13 3325 20521 29 _ _ (1985843 / 100000) (992923 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell421193984 :
    ThetaLowerSegment 421193984 421259520 (5264585258557 / 12500) (1684928701217 / 4000) := by
  exact
    packedTile32768 421193984 421259520 13 3291 20523 29 _ _ (1985859 / 100000) (992931 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell421259520 :
    ThetaLowerSegment 421259520 421325056 (1684928701217 / 4000) (42129675592673 / 100000) := by
  exact
    packedTile32768 421259520 421325056 13 3252 20524 29 _ _ (992937 / 50000) (1985877 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell421325056 :
    ThetaLowerSegment 421325056 421390592 (42129675592673 / 100000) (42136217114333 / 100000) := by
  exact
    packedTile32768 421325056 421390592 13 3294 20526 29 _ _ (198589 / 10000) (1985893 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell421390592 :
    ThetaLowerSegment 421390592 421456128 (42136217114333 / 100000) (8428564844719 / 20000) := by
  exact
    packedTile32768 421390592 421456128 13 3327 20527 29 _ _ (992953 / 50000) (1985909 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell421456128 :
    ThetaLowerSegment 421456128 421521664 (8428564844719 / 20000) (42149409537631 / 100000) := by
  exact
    packedTile32768 421456128 421521664 13 3316 20529 29 _ _ (1985921 / 100000) (496481 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell421521664 :
    ThetaLowerSegment 421521664 421587200 (42149409537631 / 100000) (10538995250791 / 25000) := by
  exact
    packedTile32768 421521664 421587200 13 3309 20530 29 _ _ (1985937 / 100000) (99297 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell421587200 :
    ThetaLowerSegment 421587200 421652736 (10538995250791 / 25000) (10540626213871 / 25000) := by
  exact
    packedTile32768 421587200 421652736 13 3285 20532 29 _ _ (62061 / 3125) (397191 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell421652736 :
    ThetaLowerSegment 421652736 421718272 (10540626213871 / 25000) (10542265133963 / 25000) := by
  exact
    packedTile32768 421652736 421718272 13 3301 20534 29 _ _ (124123 / 6250) (1985971 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell421718272 :
    ThetaLowerSegment 421718272 421783808 (10542265133963 / 25000) (1687027033809 / 4000) := by
  exact
    packedTile32768 421718272 421783808 13 3331 20535 29 _ _ (1985983 / 100000) (992993 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell421783808 :
    ThetaLowerSegment 421783808 421849344 (1687027033809 / 4000) (8436457844379 / 20000) := by
  exact
    packedTile32768 421783808 421849344 13 3330 20537 29 _ _ (1985999 / 100000) (993001 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell421849344 :
    ThetaLowerSegment 421849344 421914880 (8436457844379 / 20000) (8437758683549 / 20000) := by
  exact
    packedTile32768 421849344 421914880 13 3275 20538 29 _ _ (993007 / 50000) (1986017 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell421914880 :
    ThetaLowerSegment 421914880 421980416 (8437758683549 / 20000) (8439080585117 / 20000) := by
  exact
    packedTile32768 421914880 421980416 13 3328 20540 29 _ _ (198603 / 10000) (1986033 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell421980416 :
    ThetaLowerSegment 421980416 422045952 (8439080585117 / 20000) (8440405674341 / 20000) := by
  exact
    packedTile32768 421980416 422045952 13 3336 20542 29 _ _ (397209 / 20000) (62064 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell422045952 :
    ThetaLowerSegment 422045952 422111488 (8440405674341 / 20000) (42208578400883 / 100000) := by
  exact
    packedTile32768 422045952 422111488 13 3298 20543 29 _ _ (1986061 / 100000) (124129 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell422111488 :
    ThetaLowerSegment 422111488 422177024 (42208578400883 / 100000) (42215192037293 / 100000) := by
  exact
    packedTile32768 422111488 422177024 13 3330 20545 29 _ _ (1986077 / 100000) (12413 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell422177024 :
    ThetaLowerSegment 422177024 422242560 (42215192037293 / 100000) (42221624989281 / 100000) := by
  exact
    packedTile32768 422177024 422242560 13 3239 20546 29 _ _ (496523 / 25000) (397219 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell422242560 :
    ThetaLowerSegment 422242560 422308096 (42221624989281 / 100000) (42228063951417 / 100000) := by
  exact
    packedTile32768 422242560 422308096 13 3242 20548 29 _ _ (496527 / 25000) (1986111 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell422308096 :
    ThetaLowerSegment 422308096 422373632 (42228063951417 / 100000) (21117276307629 / 50000) := by
  exact
    packedTile32768 422308096 422373632 13 3267 20550 29 _ _ (1986123 / 100000) (993063 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell422373632 :
    ThetaLowerSegment 422373632 422439168 (21117276307629 / 50000) (10560261822447 / 25000) := by
  exact
    packedTile32768 422373632 422439168 13 3270 20551 29 _ _ (1986139 / 100000) (993071 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell422439168 :
    ThetaLowerSegment 422439168 422504704 (10560261822447 / 25000) (21123849459767 / 50000) := by
  exact
    packedTile32768 422439168 422504704 13 3349 20553 29 _ _ (993077 / 50000) (1986157 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell422504704 :
    ThetaLowerSegment 422504704 422570240 (21123849459767 / 50000) (21127140543457 / 50000) := by
  exact
    packedTile32768 422504704 422570240 13 3314 20554 29 _ _ (198617 / 10000) (1986173 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell422570240 :
    ThetaLowerSegment 422570240 422635776 (21127140543457 / 50000) (2641293529029 / 6250) := by
  exact
    packedTile32768 422570240 422635776 13 3230 20556 29 _ _ (397237 / 20000) (496547 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell422635776 :
    ThetaLowerSegment 422635776 422701312 (2641293529029 / 6250) (8453466472401 / 20000) := by
  exact
    packedTile32768 422635776 422701312 13 3341 20558 29 _ _ (1986201 / 100000) (496551 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell422701312 :
    ThetaLowerSegment 422701312 422766848 (8453466472401 / 20000) (42273930571557 / 100000) := by
  exact
    packedTile32768 422701312 422766848 13 3322 20559 29 _ _ (248277 / 12500) (1986219 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell422766848 :
    ThetaLowerSegment 422766848 422832384 (42273930571557 / 100000) (42280361990773 / 100000) := by
  exact
    packedTile32768 422766848 422832384 13 3238 20561 29 _ _ (248279 / 12500) (397247 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell422832384 :
    ThetaLowerSegment 422832384 422897920 (42280361990773 / 100000) (21143477172283 / 50000) := by
  exact
    packedTile32768 422832384 422897920 13 3319 20562 29 _ _ (1986247 / 100000) (1589 / 80)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell422897920 :
    ThetaLowerSegment 422897920 422963456 (21143477172283 / 50000) (4229356462783 / 10000) := by
  exact
    packedTile32768 422897920 422963456 13 3328 20564 29 _ _ (1986263 / 100000) (993133 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell422963456 :
    ThetaLowerSegment 422963456 423028992 (4229356462783 / 10000) (10575036291711 / 25000) := by
  exact
    packedTile32768 422963456 423028992 13 3313 20566 29 _ _ (993139 / 50000) (1986281 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell423028992 :
    ThetaLowerSegment 423028992 423094528 (10575036291711 / 25000) (21153364865727 / 50000) := by
  exact
    packedTile32768 423028992 423094528 13 3315 20567 29 _ _ (993147 / 50000) (1986297 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell423094528 :
    ThetaLowerSegment 423094528 423160064 (21153364865727 / 50000) (42313397770767 / 100000) := by
  exact
    packedTile32768 423094528 423160064 13 3357 20569 29 _ _ (1986309 / 100000) (248289 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell423160064 :
    ThetaLowerSegment 423160064 423225600 (42313397770767 / 100000) (21159967383171 / 50000) := by
  exact
    packedTile32768 423160064 423225600 13 3291 20570 29 _ _ (79453 / 4000) (248291 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell423225600 :
    ThetaLowerSegment 423225600 423291136 (21159967383171 / 50000) (21163210083221 / 50000) := by
  exact
    packedTile32768 423225600 423291136 13 3265 20572 29 _ _ (99317 / 5000) (1986343 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell423291136 :
    ThetaLowerSegment 423291136 423356672 (21163210083221 / 50000) (21166477638841 / 50000) := by
  exact
    packedTile32768 423291136 423356672 13 3290 20574 29 _ _ (496589 / 25000) (1986359 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell423356672 :
    ThetaLowerSegment 423356672 423422208 (21166477638841 / 50000) (42339559961257 / 100000) := by
  exact
    packedTile32768 423356672 423422208 13 3325 20575 29 _ _ (1986371 / 100000) (993187 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell423422208 :
    ThetaLowerSegment 423422208 423487744 (42339559961257 / 100000) (42346273949317 / 100000) := by
  exact
    packedTile32768 423422208 423487744 13 3380 20577 29 _ _ (1986387 / 100000) (198639 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell423487744 :
    ThetaLowerSegment 423487744 423553280 (42346273949317 / 100000) (42352783388671 / 100000) := by
  exact
    packedTile32768 423487744 423553280 13 3277 20578 29 _ _ (993201 / 50000) (397281 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell423553280 :
    ThetaLowerSegment 423553280 423618816 (42352783388671 / 100000) (21179680207679 / 50000) := by
  exact
    packedTile32768 423553280 423618816 13 3311 20580 29 _ _ (1986417 / 100000) (99321 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell423618816 :
    ThetaLowerSegment 423618816 423684352 (21179680207679 / 50000) (2647863520163 / 6250) := by
  exact
    packedTile32768 423618816 423684352 13 3250 20582 29 _ _ (1986433 / 100000) (496609 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell423684352 :
    ThetaLowerSegment 423684352 423749888 (2647863520163 / 6250) (2648270742003 / 6250) := by
  exact
    packedTile32768 423684352 423749888 13 3280 20583 29 _ _ (124153 / 6250) (1986451 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell423749888 :
    ThetaLowerSegment 423749888 423815424 (2648270742003 / 6250) (2648681319281 / 6250) := by
  exact
    packedTile32768 423749888 423815424 13 3307 20585 29 _ _ (62077 / 3125) (1986467 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell423815424 :
    ThetaLowerSegment 423815424 423880960 (2648681319281 / 6250) (42385466421591 / 100000) := by
  exact
    packedTile32768 423815424 423880960 13 3305 20586 29 _ _ (1986479 / 100000) (993241 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell423880960 :
    ThetaLowerSegment 423880960 423946496 (42385466421591 / 100000) (42392081449941 / 100000) := by
  exact
    packedTile32768 423880960 423946496 13 3330 20588 29 _ _ (397299 / 20000) (993249 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell423946496 :
    ThetaLowerSegment 423946496 424012032 (42392081449941 / 100000) (42398621040861 / 100000) := by
  exact
    packedTile32768 423946496 424012032 13 3292 20589 29 _ _ (198651 / 10000) (1986513 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell424012032 :
    ThetaLowerSegment 424012032 424077568 (42398621040861 / 100000) (42405136846141 / 100000) := by
  exact
    packedTile32768 424012032 424077568 13 3280 20591 29 _ _ (993263 / 50000) (1986529 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell424077568 :
    ThetaLowerSegment 424077568 424143104 (42405136846141 / 100000) (21205783639679 / 50000) := by
  exact
    packedTile32768 424077568 424143104 13 3237 20593 29 _ _ (1986541 / 100000) (124159 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell424143104 :
    ThetaLowerSegment 424143104 424208640 (21205783639679 / 50000) (10604571453783 / 25000) := by
  exact
    packedTile32768 424143104 424208640 13 3382 20594 29 _ _ (1986557 / 100000) (12416 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell424208640 :
    ThetaLowerSegment 424208640 424274176 (10604571453783 / 25000) (1060620491261 / 2500) := by
  exact
    packedTile32768 424208640 424274176 13 3289 20596 29 _ _ (496643 / 25000) (79463 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell424274176 :
    ThetaLowerSegment 424274176 424339712 (1060620491261 / 2500) (2651960216957 / 6250) := by
  exact
    packedTile32768 424274176 424339712 13 3294 20597 29 _ _ (496647 / 25000) (1986591 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell424339712 :
    ThetaLowerSegment 424339712 424405248 (2651960216957 / 6250) (10609479815303 / 25000) := by
  exact
    packedTile32768 424339712 424405248 13 3300 20599 29 _ _ (1986603 / 100000) (993303 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell424405248 :
    ThetaLowerSegment 424405248 424470784 (10609479815303 / 25000) (10611150561041 / 25000) := by
  exact
    packedTile32768 424405248 424470784 13 3364 20601 29 _ _ (993309 / 50000) (1986621 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell424470784 :
    ThetaLowerSegment 424470784 424536320 (10611150561041 / 25000) (21225536355551 / 50000) := by
  exact
    packedTile32768 424470784 424536320 13 3257 20602 29 _ _ (993317 / 50000) (1986637 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell424536320 :
    ThetaLowerSegment 424536320 424601856 (21225536355551 / 50000) (42457849170841 / 100000) := by
  exact
    packedTile32768 424536320 424601856 13 3411 20604 29 _ _ (1986649 / 100000) (496663 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell424601856 :
    ThetaLowerSegment 424601856 424667392 (42457849170841 / 100000) (10616108741329 / 25000) := by
  exact
    packedTile32768 424601856 424667392 13 3315 20605 29 _ _ (397333 / 20000) (496667 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell424667392 :
    ThetaLowerSegment 424667392 424732928 (10616108741329 / 25000) (10617775565849 / 25000) := by
  exact
    packedTile32768 424667392 424732928 13 3356 20607 29 _ _ (49667 / 2500) (1986683 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell424732928 :
    ThetaLowerSegment 424732928 424798464 (10617775565849 / 25000) (10619403663221 / 25000) := by
  exact
    packedTile32768 424732928 424798464 13 3278 20609 29 _ _ (248337 / 12500) (1986699 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell424798464 :
    ThetaLowerSegment 424798464 424864000 (10619403663221 / 25000) (42484176759317 / 100000) := by
  exact
    packedTile32768 424798464 424864000 13 3303 20610 29 _ _ (1986711 / 100000) (993357 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell424864000 :
    ThetaLowerSegment 424864000 424929536 (42484176759317 / 100000) (8498137849429 / 20000) := by
  exact
    packedTile32768 424864000 424929536 13 3278 20612 29 _ _ (993363 / 50000) (1986729 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell424929536 :
    ThetaLowerSegment 424929536 424995072 (8498137849429 / 20000) (8499443138923 / 20000) := by
  exact
    packedTile32768 424929536 424995072 13 3285 20613 29 _ _ (993371 / 50000) (397349 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell424995072 :
    ThetaLowerSegment 424995072 425060608 (8499443138923 / 20000) (42503728284061 / 100000) := by
  exact
    packedTile32768 424995072 425060608 13 3278 20615 29 _ _ (1986757 / 100000) (49669 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell425060608 :
    ThetaLowerSegment 425060608 425126144 (42503728284061 / 100000) (8502060105829 / 20000) := by
  exact
    packedTile32768 425060608 425126144 13 3308 20616 29 _ _ (1986773 / 100000) (248347 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell425126144 :
    ThetaLowerSegment 425126144 425191680 (8502060105829 / 20000) (42516894678517 / 100000) := by
  exact
    packedTile32768 425126144 425191680 13 3319 20618 29 _ _ (496697 / 25000) (1986791 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell425191680 :
    ThetaLowerSegment 425191680 425257216 (42516894678517 / 100000) (42523429276873 / 100000) := by
  exact
    packedTile32768 425191680 425257216 13 3289 20620 29 _ _ (496701 / 25000) (1986807 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell425257216 :
    ThetaLowerSegment 425257216 425322752 (42523429276873 / 100000) (8505992387549 / 20000) := by
  exact
    packedTile32768 425257216 425322752 13 3288 20621 29 _ _ (1986819 / 100000) (993411 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell425322752 :
    ThetaLowerSegment 425322752 425339136 (8505992387549 / 20000) (1701261658831 / 4000) := by
  exact
    packedTile32768 425322752 425339136 11 795 20623 29 _ _ (993417 / 50000) (1986837 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell425339136 :
    ThetaLowerSegment 425339136 425341184 (1701261658831 / 4000) (42531736180899 / 100000) := by
  exact
    packedTile32768 425339136 425341184 8 98 20623 29 _ _ (993419 / 50000) (1986841 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_393341184_425341184 :
    ThetaLowerSegment 393341184 425341184 (19665892057069 / 50000) (42531736180899 / 100000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell393341184 cell393406720)
                    (ThetaLowerSegment.join cell393472256 cell393537792))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell393603328 cell393668864)
                    (ThetaLowerSegment.join cell393734400 cell393799936)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell393865472 cell393931008)
                    (ThetaLowerSegment.join cell393996544 cell394062080))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell394127616 cell394193152)
                    (ThetaLowerSegment.join cell394258688 cell394324224))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell394389760 cell394455296)
                    (ThetaLowerSegment.join cell394520832 cell394586368))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell394651904 cell394717440)
                    (ThetaLowerSegment.join cell394782976 cell394848512)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell394914048 cell394979584)
                    (ThetaLowerSegment.join cell395045120 cell395110656))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell395176192 cell395241728)
                    (ThetaLowerSegment.join cell395307264 cell395372800)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell395438336 cell395503872)
                    (ThetaLowerSegment.join cell395569408 cell395634944))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell395700480 cell395766016)
                    (ThetaLowerSegment.join cell395831552 cell395897088)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell395962624 cell396028160)
                    (ThetaLowerSegment.join cell396093696 cell396159232))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell396224768 cell396290304)
                    (ThetaLowerSegment.join cell396355840 cell396421376))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell396486912 cell396552448)
                    (ThetaLowerSegment.join cell396617984 cell396683520))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell396749056 cell396814592)
                    (ThetaLowerSegment.join cell396880128 cell396945664)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell397011200 cell397076736)
                    (ThetaLowerSegment.join cell397142272 cell397207808))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell397273344 cell397338880)
                    (ThetaLowerSegment.join cell397404416 cell397469952))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell397535488 cell397601024)
                    (ThetaLowerSegment.join cell397666560 cell397732096))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell397797632 cell397863168)
                    (ThetaLowerSegment.join cell397928704 cell397994240)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell398059776 cell398125312)
                    (ThetaLowerSegment.join cell398190848 cell398256384))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell398321920 cell398387456)
                    (ThetaLowerSegment.join cell398452992 cell398518528))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell398584064 cell398649600)
                    (ThetaLowerSegment.join cell398715136 cell398780672))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell398846208 cell398911744)
                    (ThetaLowerSegment.join cell398977280 cell399042816)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell399108352 cell399173888)
                    (ThetaLowerSegment.join cell399239424 cell399304960))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell399370496 cell399436032)
                    (ThetaLowerSegment.join cell399501568 cell399567104)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell399632640 cell399698176)
                    (ThetaLowerSegment.join cell399763712 cell399829248))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell399894784 cell399960320)
                    (ThetaLowerSegment.join cell400025856 cell400091392)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell400156928 cell400222464)
                    (ThetaLowerSegment.join cell400288000 cell400353536))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell400419072 cell400484608)
                    (ThetaLowerSegment.join cell400550144 cell400615680))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell400681216 cell400746752)
                    (ThetaLowerSegment.join cell400812288 cell400877824))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell400943360 cell401008896)
                    (ThetaLowerSegment.join cell401074432 cell401139968)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell401205504 cell401271040)
                    (ThetaLowerSegment.join cell401336576 cell401402112))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell401467648 cell401533184)
                    (ThetaLowerSegment.join cell401598720 cell401664256)))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell401729792 cell401795328)
                    (ThetaLowerSegment.join cell401860864 cell401926400))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell401991936 cell402057472)
                    (ThetaLowerSegment.join cell402123008 cell402188544)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell402254080 cell402319616)
                    (ThetaLowerSegment.join cell402385152 cell402450688))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell402516224 cell402581760)
                    (ThetaLowerSegment.join cell402647296 cell402712832))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell402778368 cell402843904)
                    (ThetaLowerSegment.join cell402909440 cell402974976))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell403040512 cell403106048)
                    (ThetaLowerSegment.join cell403171584 cell403237120)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell403302656 cell403368192)
                    (ThetaLowerSegment.join cell403433728 cell403499264))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell403564800 cell403630336)
                    (ThetaLowerSegment.join cell403695872 cell403761408)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell403826944 cell403892480)
                    (ThetaLowerSegment.join cell403958016 cell404023552))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell404089088 cell404154624)
                    (ThetaLowerSegment.join cell404220160 cell404285696)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell404351232 cell404416768)
                    (ThetaLowerSegment.join cell404482304 cell404547840))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell404613376 cell404678912)
                    (ThetaLowerSegment.join cell404744448 cell404809984))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell404875520 cell404941056)
                    (ThetaLowerSegment.join cell405006592 cell405072128))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell405137664 cell405203200)
                    (ThetaLowerSegment.join cell405268736 cell405334272)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell405399808 cell405465344)
                    (ThetaLowerSegment.join cell405530880 cell405596416))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell405661952 cell405727488)
                    (ThetaLowerSegment.join cell405793024 cell405858560))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell405924096 cell405989632)
                    (ThetaLowerSegment.join cell406055168 cell406120704))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell406186240 cell406251776)
                    (ThetaLowerSegment.join cell406317312 cell406382848)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell406448384 cell406513920)
                    (ThetaLowerSegment.join cell406579456 cell406644992))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell406710528 cell406776064)
                    (ThetaLowerSegment.join cell406841600 cell406907136))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell406972672 cell407038208)
                    (ThetaLowerSegment.join cell407103744 cell407169280))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell407234816 cell407300352)
                    (ThetaLowerSegment.join cell407365888 cell407431424)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell407496960 cell407562496)
                    (ThetaLowerSegment.join cell407628032 cell407693568))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell407759104 cell407824640)
                    (ThetaLowerSegment.join cell407890176 cell407955712)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell408021248 cell408086784)
                    (ThetaLowerSegment.join cell408152320 cell408217856))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell408283392 cell408348928)
                    (ThetaLowerSegment.join cell408414464 cell408480000)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell408545536 cell408611072)
                    (ThetaLowerSegment.join cell408676608 cell408742144))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell408807680 cell408873216)
                    (ThetaLowerSegment.join cell408938752 cell409004288))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell409069824 cell409135360)
                    (ThetaLowerSegment.join cell409200896 cell409266432))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell409331968 cell409397504)
                    (ThetaLowerSegment.join cell409463040 cell409528576)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell409594112 cell409659648)
                    (ThetaLowerSegment.join cell409725184 cell409790720))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell409856256 cell409921792)
                    (ThetaLowerSegment.join cell409987328 cell410052864))))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell410118400 cell410183936)
                    (ThetaLowerSegment.join cell410249472 cell410315008))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell410380544 cell410446080)
                    (ThetaLowerSegment.join cell410511616 cell410577152)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell410642688 cell410708224)
                    (ThetaLowerSegment.join cell410773760 cell410839296))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell410904832 cell410970368)
                    (ThetaLowerSegment.join cell411035904 cell411101440))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell411166976 cell411232512)
                    (ThetaLowerSegment.join cell411298048 cell411363584))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell411429120 cell411494656)
                    (ThetaLowerSegment.join cell411560192 cell411625728)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell411691264 cell411756800)
                    (ThetaLowerSegment.join cell411822336 cell411887872))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell411953408 cell412018944)
                    (ThetaLowerSegment.join cell412084480 cell412150016)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell412215552 cell412281088)
                    (ThetaLowerSegment.join cell412346624 cell412412160))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell412477696 cell412543232)
                    (ThetaLowerSegment.join cell412608768 cell412674304)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell412739840 cell412805376)
                    (ThetaLowerSegment.join cell412870912 cell412936448))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell413001984 cell413067520)
                    (ThetaLowerSegment.join cell413133056 cell413198592))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell413264128 cell413329664)
                    (ThetaLowerSegment.join cell413395200 cell413460736))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell413526272 cell413591808)
                    (ThetaLowerSegment.join cell413657344 cell413722880)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell413788416 cell413853952)
                    (ThetaLowerSegment.join cell413919488 cell413985024))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell414050560 cell414116096)
                    (ThetaLowerSegment.join cell414181632 cell414247168))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell414312704 cell414378240)
                    (ThetaLowerSegment.join cell414443776 cell414509312))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell414574848 cell414640384)
                    (ThetaLowerSegment.join cell414705920 cell414771456)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell414836992 cell414902528)
                    (ThetaLowerSegment.join cell414968064 cell415033600))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell415099136 cell415164672)
                    (ThetaLowerSegment.join cell415230208 cell415295744))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell415361280 cell415426816)
                    (ThetaLowerSegment.join cell415492352 cell415557888))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell415623424 cell415688960)
                    (ThetaLowerSegment.join cell415754496 cell415820032)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell415885568 cell415951104)
                    (ThetaLowerSegment.join cell416016640 cell416082176))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell416147712 cell416213248)
                    (ThetaLowerSegment.join cell416278784 cell416344320)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell416409856 cell416475392)
                    (ThetaLowerSegment.join cell416540928 cell416606464))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell416672000 cell416737536)
                    (ThetaLowerSegment.join cell416803072 cell416868608)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell416934144 cell416999680)
                    (ThetaLowerSegment.join cell417065216 cell417130752))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell417196288 cell417261824)
                    (ThetaLowerSegment.join cell417327360 cell417392896))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell417458432 cell417523968)
                    (ThetaLowerSegment.join cell417589504 cell417655040))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell417720576 cell417786112)
                    (ThetaLowerSegment.join cell417851648 cell417917184)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell417982720 cell418048256)
                    (ThetaLowerSegment.join cell418113792 cell418179328))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell418244864 cell418310400)
                    (ThetaLowerSegment.join cell418375936 cell418441472)))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell418507008 cell418572544)
                    (ThetaLowerSegment.join cell418638080 cell418703616))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell418769152 cell418834688)
                    (ThetaLowerSegment.join cell418900224 cell418965760)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell419031296 cell419096832)
                    (ThetaLowerSegment.join cell419162368 cell419227904))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell419293440 cell419358976)
                    (ThetaLowerSegment.join cell419424512 cell419490048))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell419555584 cell419621120)
                    (ThetaLowerSegment.join cell419686656 cell419752192))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell419817728 cell419883264)
                    (ThetaLowerSegment.join cell419948800 cell420014336)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell420079872 cell420145408)
                    (ThetaLowerSegment.join cell420210944 cell420276480))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell420342016 cell420407552)
                    (ThetaLowerSegment.join cell420473088 cell420538624)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell420604160 cell420669696)
                    (ThetaLowerSegment.join cell420735232 cell420800768))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell420866304 cell420931840)
                    (ThetaLowerSegment.join cell420997376 cell421062912)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell421128448 cell421193984)
                    (ThetaLowerSegment.join cell421259520 cell421325056))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell421390592 cell421456128)
                    (ThetaLowerSegment.join cell421521664 cell421587200))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell421652736 cell421718272)
                    (ThetaLowerSegment.join cell421783808 cell421849344))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell421914880 cell421980416)
                    (ThetaLowerSegment.join cell422045952 cell422111488)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell422177024 cell422242560)
                    (ThetaLowerSegment.join cell422308096 cell422373632))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell422439168 cell422504704)
                    (ThetaLowerSegment.join cell422570240 cell422635776))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell422701312 cell422766848)
                    (ThetaLowerSegment.join cell422832384 cell422897920))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell422963456 cell423028992)
                    (ThetaLowerSegment.join cell423094528 cell423160064)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell423225600 cell423291136)
                    (ThetaLowerSegment.join cell423356672 cell423422208))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell423487744 cell423553280)
                    (ThetaLowerSegment.join cell423618816 cell423684352))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell423749888 cell423815424)
                    (ThetaLowerSegment.join cell423880960 cell423946496))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell424012032 cell424077568)
                    (ThetaLowerSegment.join cell424143104 cell424208640)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell424274176 cell424339712)
                    (ThetaLowerSegment.join cell424405248 cell424470784))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell424536320 cell424601856)
                    (ThetaLowerSegment.join cell424667392 cell424732928)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell424798464 cell424864000)
                  (ThetaLowerSegment.join cell424929536 cell424995072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell425060608 cell425126144)
                  (ThetaLowerSegment.join cell425191680 cell425257216)))
              (ThetaLowerSegment.join cell425322752 cell425339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
