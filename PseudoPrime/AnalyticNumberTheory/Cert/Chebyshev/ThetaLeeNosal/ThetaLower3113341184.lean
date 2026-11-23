/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis65536

/-! # Direct theta estimate up to 3113341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell3081341184 :
    ThetaLowerSegment 3081341184 3081472256 (308127750852491 / 100000)
      (308140816327251 / 100000) := by
  exact
    packedTile65536 3081341184 3081472256 14 5980 55509 32 _ _ (1092431 / 50000) (436973 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3081472256 :
    ThetaLowerSegment 3081472256 3081603328 (308140816327251 / 100000)
      (308153997623829 / 100000) := by
  exact
    packedTile65536 3081472256 3081603328 14 6033 55511 32 _ _ (1092433 / 50000) (2184869 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3081603328 :
    ThetaLowerSegment 3081603328 3081734400 (308153997623829 / 100000)
      (308167146171489 / 100000) := by
  exact
    packedTile65536 3081603328 3081734400 14 6018 55512 32 _ _ (218487 / 10000) (2184873 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3081734400 :
    ThetaLowerSegment 3081734400 3081865472 (308167146171489 / 100000)
      (308180255415489 / 100000) := by
  exact
    packedTile65536 3081734400 3081865472 14 6000 55513 32 _ _ (1092437 / 50000) (2184877 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3081865472 :
    ThetaLowerSegment 3081865472 3081996544 (308180255415489 / 100000)
      (38524168674417 / 12500) := by
  exact
    packedTile65536 3081865472 3081996544 14 5993 55514 32 _ _ (2184879 / 100000) (1092441 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3081996544 :
    ThetaLowerSegment 3081996544 3082127616 (38524168674417 / 12500) (38525772378539 / 12500) := by
  exact
    packedTile65536 3081996544 3082127616 14 5872 55515 32 _ _ (2184883 / 100000) (1092443 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3082127616 :
    ThetaLowerSegment 3082127616 3082258688 (38525772378539 / 12500) (154109676948461 / 50000) := by
  exact
    packedTile65536 3082127616 3082258688 14 6030 55516 32 _ _ (2184887 / 100000) (218489 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3082258688 :
    ThetaLowerSegment 3082258688 3082389760 (154109676948461 / 50000) (12329301413773 / 4000) := by
  exact
    packedTile65536 3082258688 3082389760 14 6033 55518 32 _ _ (2184891 / 100000) (1092447 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3082389760 :
    ThetaLowerSegment 3082389760 3082520832 (12329301413773 / 4000) (308245618501573 / 100000) := by
  exact
    packedTile65536 3082389760 3082520832 14 5988 55519 32 _ _ (68278 / 3125) (2184899 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3082520832 :
    ThetaLowerSegment 3082520832 3082651904 (308245618501573 / 100000)
      (308258708237473 / 100000) := by
  exact
    packedTile65536 3082520832 3082651904 14 5991 55520 32 _ _ (21849 / 1000) (2184903 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3082651904 :
    ThetaLowerSegment 3082651904 3082782976 (308258708237473 / 100000)
      (308271793627529 / 100000) := by
  exact
    packedTile65536 3082651904 3082782976 14 5989 55521 32 _ _ (273113 / 12500) (2184907 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3082782976 :
    ThetaLowerSegment 3082782976 3082914048 (308271793627529 / 100000)
      (61657012077781 / 20000) := by
  exact
    packedTile65536 3082782976 3082914048 14 6072 55522 32 _ _ (546227 / 25000) (2184911 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3082914048 :
    ThetaLowerSegment 3082914048 3083045120 (61657012077781 / 20000)
      (308298204825513 / 100000) := by
  exact
    packedTile65536 3082914048 3083045120 14 6016 55523 32 _ _ (2184913 / 100000) (546229 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3083045120 :
    ThetaLowerSegment 3083045120 3083176192 (308298204825513 / 100000)
      (38538897630947 / 12500) := by
  exact
    packedTile65536 3083045120 3083176192 14 5939 55525 32 _ _ (2184917 / 100000) (54623 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3083176192 :
    ThetaLowerSegment 3083176192 3083307264 (38538897630947 / 12500) (77081092307683 / 25000) := by
  exact
    packedTile65536 3083176192 3083307264 14 6036 55526 32 _ _ (2184921 / 100000) (546231 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3083307264 :
    ThetaLowerSegment 3083307264 3083438336 (77081092307683 / 25000) (154168728465741 / 50000) := by
  exact
    packedTile65536 3083307264 3083438336 14 5990 55527 32 _ _ (87397 / 4000) (68279 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3083438336 :
    ThetaLowerSegment 3083438336 3083569408 (154168728465741 / 50000) (38543809616169 / 12500) := by
  exact
    packedTile65536 3083438336 3083569408 14 5959 55528 32 _ _ (218493 / 10000) (2184933 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3083569408 :
    ThetaLowerSegment 3083569408 3083700480 (38543809616169 / 12500) (15418175175293 / 5000) := by
  exact
    packedTile65536 3083569408 3083700480 14 5962 55529 32 _ _ (1092467 / 50000) (2184937 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3083700480 :
    ThetaLowerSegment 3083700480 3083831552 (15418175175293 / 5000) (77094170762969 / 25000) := by
  exact
    packedTile65536 3083700480 3083831552 14 6032 55531 32 _ _ (1092469 / 50000) (2184941 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3083831552 :
    ThetaLowerSegment 3083831552 3083962624 (77094170762969 / 25000) (15419484391333 / 5000) := by
  exact
    packedTile65536 3083831552 3083962624 14 5952 55532 32 _ _ (1092471 / 50000) (436989 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3083962624 :
    ThetaLowerSegment 3083962624 3084093696 (15419484391333 / 5000) (15420144245327 / 5000) := by
  exact
    packedTile65536 3083962624 3084093696 14 6040 55533 32 _ _ (2184947 / 100000) (43699 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3084093696 :
    ThetaLowerSegment 3084093696 3084224768 (15420144245327 / 5000) (77104003023037 / 25000) := by
  exact
    packedTile65536 3084093696 3084224768 14 6008 55534 32 _ _ (2184951 / 100000) (1092477 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3084224768 :
    ThetaLowerSegment 3084224768 3084355840 (77104003023037 / 25000)
      (308429154596473 / 100000) := by
  exact
    packedTile65536 3084224768 3084355840 14 6015 55535 32 _ _ (436991 / 20000) (1092479 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3084355840 :
    ThetaLowerSegment 3084355840 3084486912 (308429154596473 / 100000)
      (308442408557767 / 100000) := by
  exact
    packedTile65536 3084355840 3084486912 14 6066 55536 32 _ _ (2184959 / 100000) (1092481 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3084486912 :
    ThetaLowerSegment 3084486912 3084617984 (308442408557767 / 100000)
      (308455437498099 / 100000) := by
  exact
    packedTile65536 3084486912 3084617984 14 5963 55538 32 _ _ (546241 / 25000) (2184967 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3084617984 :
    ThetaLowerSegment 3084617984 3084749056 (308455437498099 / 100000)
      (308468466462283 / 100000) := by
  exact
    packedTile65536 3084617984 3084749056 14 5963 55539 32 _ _ (273121 / 12500) (2184971 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3084749056 :
    ThetaLowerSegment 3084749056 3084880128 (308468466462283 / 100000)
      (308481606883891 / 100000) := by
  exact
    packedTile65536 3084749056 3084880128 14 6014 55540 32 _ _ (546243 / 25000) (87399 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3084880128 :
    ThetaLowerSegment 3084880128 3085011200 (308481606883891 / 100000)
      (308494751699507 / 100000) := by
  exact
    packedTile65536 3084880128 3085011200 14 6016 55541 32 _ _ (136561 / 6250) (2184979 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3085011200 :
    ThetaLowerSegment 3085011200 3085142272 (308494751699507 / 100000) (3856348078633 / 1250) := by
  exact
    packedTile65536 3085011200 3085142272 14 5993 55542 32 _ _ (2184981 / 100000) (273123 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3085142272 :
    ThetaLowerSegment 3085142272 3085273344 (3856348078633 / 1250) (61704210030999 / 20000) := by
  exact
    packedTile65536 3085142272 3085273344 14 6043 55544 32 _ _ (436997 / 20000) (546247 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3085273344 :
    ThetaLowerSegment 3085273344 3085404416 (61704210030999 / 20000)
      (308534068319457 / 100000) := by
  exact
    packedTile65536 3085273344 3085404416 14 5958 55545 32 _ _ (2184989 / 100000) (68281 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3085404416 :
    ThetaLowerSegment 3085404416 3085535488 (308534068319457 / 100000)
      (61709455757427 / 20000) := by
  exact
    packedTile65536 3085404416 3085535488 14 6046 55546 32 _ _ (2184993 / 100000) (546249 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3085535488 :
    ThetaLowerSegment 3085535488 3085666560 (61709455757427 / 20000)
      (308560386590137 / 100000) := by
  exact
    packedTile65536 3085535488 3085666560 14 5999 55547 32 _ _ (1092499 / 50000) (2185001 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3085666560 :
    ThetaLowerSegment 3085666560 3085797632 (308560386590137 / 100000)
      (308573627702257 / 100000) := by
  exact
    packedTile65536 3085666560 3085797632 14 6060 55548 32 _ _ (1092501 / 50000) (437001 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3085797632 :
    ThetaLowerSegment 3085797632 3085928704 (308573627702257 / 100000)
      (61717346673649 / 20000) := by
  exact
    packedTile65536 3085797632 3085928704 14 5998 55549 32 _ _ (1092503 / 50000) (2185009 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3085928704 :
    ThetaLowerSegment 3085928704 3086059776 (61717346673649 / 20000) (61719966063637 / 20000) := by
  exact
    packedTile65536 3085928704 3086059776 14 5994 55551 32 _ _ (218501 / 10000) (2185013 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3086059776 :
    ThetaLowerSegment 3086059776 3086190848 (61719966063637 / 20000) (61722562735463 / 20000) := by
  exact
    packedTile65536 3086059776 3086190848 14 5942 55552 32 _ _ (437003 / 20000) (1092509 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3086190848 :
    ThetaLowerSegment 3086190848 3086321920 (61722562735463 / 20000)
      (308625818910403 / 100000) := by
  exact
    packedTile65536 3086190848 3086321920 14 5952 55553 32 _ _ (2185019 / 100000) (1092511 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3086321920 :
    ThetaLowerSegment 3086321920 3086452992 (308625818910403 / 100000)
      (61727778817607 / 20000) := by
  exact
    packedTile65536 3086321920 3086452992 14 5984 55554 32 _ _ (2185023 / 100000) (1092513 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3086452992 :
    ThetaLowerSegment 3086452992 3086584064 (61727778817607 / 20000) (77162993961171 / 25000) := by
  exact
    packedTile65536 3086452992 3086584064 14 5987 55555 32 _ _ (2185027 / 100000) (218503 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3086584064 :
    ThetaLowerSegment 3086584064 3086715136 (77162993961171 / 25000) (77166257306463 / 25000) := by
  exact
    packedTile65536 3086584064 3086715136 14 5974 55557 32 _ _ (273129 / 12500) (437007 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3086715136 :
    ThetaLowerSegment 3086715136 3086846208 (77166257306463 / 25000) (3858477371221 / 1250) := by
  exact
    packedTile65536 3086715136 3086846208 14 6023 55558 32 _ _ (546259 / 25000) (2185039 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3086846208 :
    ThetaLowerSegment 3086846208 3086977280 (3858477371221 / 1250) (1929321184527 / 625) := by
  exact
    packedTile65536 3086846208 3086977280 14 6041 55559 32 _ _ (27313 / 1250) (2185043 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3086977280 :
    ThetaLowerSegment 3086977280 3087108352 (1929321184527 / 625) (38588084870241 / 12500) := by
  exact
    packedTile65536 3086977280 3087108352 14 6082 55560 32 _ _ (546261 / 25000) (2185047 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3087108352 :
    ThetaLowerSegment 3087108352 3087239424 (38588084870241 / 12500)
      (308717712779213 / 100000) := by
  exact
    packedTile65536 3087108352 3087239424 14 5965 55561 32 _ _ (2185049 / 100000) (546263 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3087239424 :
    ThetaLowerSegment 3087239424 3087370496 (308717712779213 / 100000) (15436543230661 / 5000) := by
  exact
    packedTile65536 3087239424 3087370496 14 6019 55562 32 _ _ (2185053 / 100000) (68283 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3087370496 :
    ThetaLowerSegment 3087370496 3087501568 (15436543230661 / 5000) (308743998990847 / 100000) := by
  exact
    packedTile65536 3087370496 3087501568 14 6011 55564 32 _ _ (2185057 / 100000) (109253 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3087501568 :
    ThetaLowerSegment 3087501568 3087632640 (308743998990847 / 100000)
      (308757021954407 / 100000) := by
  exact
    packedTile65536 3087501568 3087632640 14 5960 55565 32 _ _ (2185061 / 100000) (273133 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3087632640 :
    ThetaLowerSegment 3087632640 3087763712 (308757021954407 / 100000)
      (308769979395787 / 100000) := by
  exact
    packedTile65536 3087632640 3087763712 14 5930 55566 32 _ _ (1092533 / 50000) (2185069 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3087763712 :
    ThetaLowerSegment 3087763712 3087894784 (308769979395787 / 100000)
      (308783013338337 / 100000) := by
  exact
    packedTile65536 3087763712 3087894784 14 5965 55567 32 _ _ (218507 / 10000) (2185073 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3087894784 :
    ThetaLowerSegment 3087894784 3088025856 (308783013338337 / 100000)
      (308796112856967 / 100000) := by
  exact
    packedTile65536 3087894784 3088025856 14 5995 55568 32 _ _ (1092537 / 50000) (2185077 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3088025856 :
    ThetaLowerSegment 3088025856 3088156928 (308796112856967 / 100000)
      (308809459313391 / 100000) := by
  exact
    packedTile65536 3088025856 3088156928 14 6108 55570 32 _ _ (1092539 / 50000) (2185081 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3088156928 :
    ThetaLowerSegment 3088156928 3088288000 (308809459313391 / 100000)
      (308822451816909 / 100000) := by
  exact
    packedTile65536 3088156928 3088288000 14 5946 55571 32 _ _ (2185083 / 100000) (1092543 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3088288000 :
    ThetaLowerSegment 3088288000 3088419072 (308822451816909 / 100000)
      (308835256426729 / 100000) := by
  exact
    packedTile65536 3088288000 3088419072 14 5860 55572 32 _ _ (2185087 / 100000) (218509 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3088419072 :
    ThetaLowerSegment 3088419072 3088550144 (308835256426729 / 100000)
      (30884839100873 / 10000) := by
  exact
    packedTile65536 3088419072 3088550144 14 6011 55573 32 _ _ (2185091 / 100000) (1092547 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3088550144 :
    ThetaLowerSegment 3088550144 3088681216 (30884839100873 / 10000) (61772276279701 / 20000) := by
  exact
    packedTile65536 3088550144 3088681216 14 5945 55574 32 _ _ (437019 / 20000) (1092549 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3088681216 :
    ThetaLowerSegment 3088681216 3088812288 (61772276279701 / 20000) (61774884852081 / 20000) := by
  exact
    packedTile65536 3088681216 3088812288 14 5969 55575 32 _ _ (21851 / 1000) (2185103 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3088812288 :
    ThetaLowerSegment 3088812288 3088943360 (61774884852081 / 20000)
      (308887558920549 / 100000) := by
  exact
    packedTile65536 3088812288 3088943360 14 6011 55577 32 _ _ (136569 / 6250) (2185107 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3088943360 :
    ThetaLowerSegment 3088943360 3089074432 (308887558920549 / 100000)
      (308900802860137 / 100000) := by
  exact
    packedTile65536 3088943360 3089074432 14 6061 55578 32 _ _ (546277 / 25000) (2185111 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3089074432 :
    ThetaLowerSegment 3089074432 3089205504 (308900802860137 / 100000)
      (308913764944521 / 100000) := by
  exact
    packedTile65536 3089074432 3089205504 14 5932 55579 32 _ _ (273139 / 12500) (437023 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3089205504 :
    ThetaLowerSegment 3089205504 3089336576 (308913764944521 / 100000)
      (308926858159593 / 100000) := by
  exact
    packedTile65536 3089205504 3089336576 14 5992 55580 32 _ _ (546279 / 25000) (2185119 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3089336576 :
    ThetaLowerSegment 3089336576 3089467648 (308926858159593 / 100000)
      (154470042348503 / 50000) := by
  exact
    packedTile65536 3089336576 3089467648 14 6053 55581 32 _ _ (2185121 / 100000) (546281 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3089467648 :
    ThetaLowerSegment 3089467648 3089598720 (154470042348503 / 50000)
      (308953180151131 / 100000) := by
  exact
    packedTile65536 3089467648 3089598720 14 5993 55582 32 _ _ (17481 / 800) (273141 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3089598720 :
    ThetaLowerSegment 3089598720 3089729792 (308953180151131 / 100000)
      (308966286554873 / 100000) := by
  exact
    packedTile65536 3089598720 3089729792 14 5998 55584 32 _ _ (2185129 / 100000) (546283 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3089729792 :
    ThetaLowerSegment 3089729792 3089860864 (308966286554873 / 100000) (3862245171013 / 1250) := by
  exact
    packedTile65536 3089729792 3089860864 14 6099 55585 32 _ _ (2185133 / 100000) (136571 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3089860864 :
    ThetaLowerSegment 3089860864 3089991936 (3862245171013 / 1250) (6179854271667 / 2000) := by
  exact
    packedTile65536 3089860864 3089991936 14 5995 55586 32 _ _ (1092569 / 50000) (2185141 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3089991936 :
    ThetaLowerSegment 3089991936 3090123008 (6179854271667 / 2000) (154502888181113 / 50000) := by
  exact
    packedTile65536 3089991936 3090123008 14 5978 55587 32 _ _ (1092571 / 50000) (437029 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3090123008 :
    ThetaLowerSegment 3090123008 3090254080 (154502888181113 / 50000)
      (154509452359697 / 50000) := by
  exact
    packedTile65536 3090123008 3090254080 14 6008 55588 32 _ _ (1092573 / 50000) (2185149 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3090254080 :
    ThetaLowerSegment 3090254080 3090385152 (154509452359697 / 50000) (77258003358561 / 25000) := by
  exact
    packedTile65536 3090254080 3090385152 14 5999 55590 32 _ _ (43703 / 2000) (2185153 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3090385152 :
    ThetaLowerSegment 3090385152 3090516224 (77258003358561 / 25000) (154522507553247 / 50000) := by
  exact
    packedTile65536 3090385152 3090516224 14 5950 55591 32 _ _ (437031 / 20000) (1092579 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3090516224 :
    ThetaLowerSegment 3090516224 3090647296 (154522507553247 / 50000)
      (154529093622473 / 50000) := by
  exact
    packedTile65536 3090516224 3090647296 14 6028 55592 32 _ _ (2185159 / 100000) (1092581 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3090647296 :
    ThetaLowerSegment 3090647296 3090778368 (154529093622473 / 50000)
      (309071317889413 / 100000) := by
  exact
    packedTile65536 3090647296 3090778368 14 6009 55593 32 _ _ (2185163 / 100000) (1092583 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3090778368 :
    ThetaLowerSegment 3090778368 3090909440 (309071317889413 / 100000)
      (154542283278467 / 50000) := by
  exact
    packedTile65536 3090778368 3090909440 14 6063 55594 32 _ _ (2185167 / 100000) (218517 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3090909440 :
    ThetaLowerSegment 3090909440 3091040512 (154542283278467 / 50000)
      (154548720795179 / 50000) := by
  exact
    packedTile65536 3090909440 3091040512 14 5892 55595 32 _ _ (546293 / 25000) (87407 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3091040512 :
    ThetaLowerSegment 3091040512 3091171584 (154548720795179 / 50000)
      (154555275230591 / 50000) := by
  exact
    packedTile65536 3091040512 3091171584 14 5999 55597 32 _ _ (273147 / 12500) (2185179 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3091171584 :
    ThetaLowerSegment 3091171584 3091302656 (154555275230591 / 50000)
      (154561855900161 / 50000) := by
  exact
    packedTile65536 3091171584 3091302656 14 6023 55598 32 _ _ (109259 / 5000) (2185183 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3091302656 :
    ThetaLowerSegment 3091302656 3091433728 (154561855900161 / 50000)
      (154568418007713 / 50000) := by
  exact
    packedTile65536 3091302656 3091433728 14 6006 55599 32 _ _ (68287 / 3125) (2185187 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3091433728 :
    ThetaLowerSegment 3091433728 3091564800 (154568418007713 / 50000)
      (309149936223481 / 100000) := by
  exact
    packedTile65536 3091433728 3091564800 14 5995 55600 32 _ _ (2185189 / 100000) (273149 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3091564800 :
    ThetaLowerSegment 3091564800 3091695872 (309149936223481 / 100000)
      (154581463597933 / 50000) := by
  exact
    packedTile65536 3091564800 3091695872 14 5945 55601 32 _ _ (2185193 / 100000) (546299 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3091695872 :
    ThetaLowerSegment 3091695872 3091826944 (154581463597933 / 50000)
      (154587936151447 / 50000) := by
  exact
    packedTile65536 3091695872 3091826944 14 5924 55603 32 _ _ (2185197 / 100000) (5463 / 250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3091826944 :
    ThetaLowerSegment 3091826944 3091958016 (154587936151447 / 50000)
      (309189003175703 / 100000) := by
  exact
    packedTile65536 3091826944 3091958016 14 6009 55604 32 _ _ (2185201 / 100000) (546301 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3091958016 :
    ThetaLowerSegment 3091958016 3092089088 (309189003175703 / 100000)
      (309202197449531 / 100000) := by
  exact
    packedTile65536 3091958016 3092089088 14 6038 55605 32 _ _ (1092603 / 50000) (2185209 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3092089088 :
    ThetaLowerSegment 3092089088 3092220160 (309202197449531 / 100000)
      (309215345858101 / 100000) := by
  exact
    packedTile65536 3092089088 3092220160 14 6017 55606 32 _ _ (218521 / 10000) (2185213 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3092220160 :
    ThetaLowerSegment 3092220160 3092351232 (309215345858101 / 100000)
      (309228411252607 / 100000) := by
  exact
    packedTile65536 3092220160 3092351232 14 5979 55607 32 _ _ (1092607 / 50000) (2185217 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3092351232 :
    ThetaLowerSegment 3092351232 3092482304 (309228411252607 / 100000)
      (309241520375389 / 100000) := by
  exact
    packedTile65536 3092351232 3092482304 14 5999 55608 32 _ _ (1092609 / 50000) (2185221 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3092482304 :
    ThetaLowerSegment 3092482304 3092613376 (309241520375389 / 100000)
      (309254498408847 / 100000) := by
  exact
    packedTile65536 3092482304 3092613376 14 5939 55610 32 _ _ (1092611 / 50000) (87409 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3092613376 :
    ThetaLowerSegment 3092613376 3092744448 (309254498408847 / 100000) (9664610824977 / 3125) := by
  exact
    packedTile65536 3092613376 3092744448 14 5971 55611 32 _ _ (2185227 / 100000) (218523 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3092744448 :
    ThetaLowerSegment 3092744448 3092875520 (9664610824977 / 3125) (154640361671097 / 50000) := by
  exact
    packedTile65536 3092744448 3092875520 14 6030 55612 32 _ _ (2185231 / 100000) (1092617 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3092875520 :
    ThetaLowerSegment 3092875520 3093006592 (154640361671097 / 50000)
      (309293749528029 / 100000) := by
  exact
    packedTile65536 3092875520 3093006592 14 5961 55613 32 _ _ (437047 / 20000) (1092619 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3093006592 :
    ThetaLowerSegment 3093006592 3093137664 (309293749528029 / 100000)
      (61861360829163 / 20000) := by
  exact
    packedTile65536 3093006592 3093137664 14 5974 55614 32 _ _ (2185239 / 100000) (1092621 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3093137664 :
    ThetaLowerSegment 3093137664 3093268736 (61861360829163 / 20000)
      (309319812903347 / 100000) := by
  exact
    packedTile65536 3093137664 3093268736 14 5953 55615 32 _ _ (546311 / 25000) (2185247 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3093268736 :
    ThetaLowerSegment 3093268736 3093399808 (309319812903347 / 100000)
      (309332954984819 / 100000) := by
  exact
    packedTile65536 3093268736 3093399808 14 6014 55617 32 _ _ (68289 / 3125) (2185251 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3093399808 :
    ThetaLowerSegment 3093399808 3093530880 (309332954984819 / 100000)
      (309346046829551 / 100000) := by
  exact
    packedTile65536 3093399808 3093530880 14 5991 55618 32 _ _ (546313 / 25000) (437051 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3093530880 :
    ThetaLowerSegment 3093530880 3093661952 (309346046829551 / 100000)
      (309359228293743 / 100000) := by
  exact
    packedTile65536 3093530880 3093661952 14 6032 55619 32 _ _ (273157 / 12500) (2185259 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3093661952 :
    ThetaLowerSegment 3093661952 3093793024 (309359228293743 / 100000)
      (61874486328141 / 20000) := by
  exact
    packedTile65536 3093661952 3093793024 14 6042 55620 32 _ _ (2185261 / 100000) (136579 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3093793024 :
    ThetaLowerSegment 3093793024 3093924096 (61874486328141 / 20000) (30938560660339 / 10000) := by
  exact
    packedTile65536 3093793024 3093924096 14 6029 55621 32 _ _ (437053 / 20000) (546317 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3093924096 :
    ThetaLowerSegment 3093924096 3094055168 (30938560660339 / 10000) (61879719605519 / 20000) := by
  exact
    packedTile65536 3093924096 3094055168 14 5945 55623 32 _ _ (2185269 / 100000) (273159 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3094055168 :
    ThetaLowerSegment 3094055168 3094186240 (61879719605519 / 20000)
      (309411670330681 / 100000) := by
  exact
    packedTile65536 3094055168 3094186240 14 5982 55624 32 _ _ (2185273 / 100000) (546319 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3094186240 :
    ThetaLowerSegment 3094186240 3094317312 (309411670330681 / 100000)
      (309424762331179 / 100000) := by
  exact
    packedTile65536 3094186240 3094317312 14 5991 55625 32 _ _ (1092639 / 50000) (2185281 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3094317312 :
    ThetaLowerSegment 3094317312 3094448384 (309424762331179 / 100000)
      (309437712312311 / 100000) := by
  exact
    packedTile65536 3094317312 3094448384 14 5926 55626 32 _ _ (1092641 / 50000) (437057 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3094448384 :
    ThetaLowerSegment 3094448384 3094579456 (309437712312311 / 100000)
      (309450773766733 / 100000) := by
  exact
    packedTile65536 3094448384 3094579456 14 5977 55627 32 _ _ (1092643 / 50000) (2185289 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3094579456 :
    ThetaLowerSegment 3094579456 3094710528 (309450773766733 / 100000)
      (309463927027243 / 100000) := by
  exact
    packedTile65536 3094579456 3094710528 14 6019 55628 32 _ _ (218529 / 10000) (2185293 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3094710528 :
    ThetaLowerSegment 3094710528 3094841600 (309463927027243 / 100000)
      (77369228558857 / 25000) := by
  exact
    packedTile65536 3094710528 3094841600 14 5943 55630 32 _ _ (437059 / 20000) (1092649 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3094841600 :
    ThetaLowerSegment 3094841600 3094972672 (77369228558857 / 25000)
      (309490085032501 / 100000) := by
  exact
    packedTile65536 3094841600 3094972672 14 6027 55631 32 _ _ (2185299 / 100000) (1092651 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3094972672 :
    ThetaLowerSegment 3094972672 3095103744 (309490085032501 / 100000)
      (77375777905921 / 25000) := by
  exact
    packedTile65536 3094972672 3095103744 14 5961 55632 32 _ _ (2185303 / 100000) (1092653 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3095103744 :
    ThetaLowerSegment 3095103744 3095234816 (77375777905921 / 25000) (12380650074987 / 4000) := by
  exact
    packedTile65536 3095103744 3095234816 14 6013 55633 32 _ _ (2185307 / 100000) (218531 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3095234816 :
    ThetaLowerSegment 3095234816 3095365888 (12380650074987 / 4000) (309529372481919 / 100000) := by
  exact
    packedTile65536 3095234816 3095365888 14 6004 55634 32 _ _ (2185311 / 100000) (1092657 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3095365888 :
    ThetaLowerSegment 3095365888 3095496960 (309529372481919 / 100000)
      (309542427559703 / 100000) := by
  exact
    packedTile65536 3095365888 3095496960 14 5974 55636 32 _ _ (546329 / 25000) (2185319 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3095496960 :
    ThetaLowerSegment 3095496960 3095628032 (309542427559703 / 100000)
      (309555664042943 / 100000) := by
  exact
    packedTile65536 3095496960 3095628032 14 6057 55637 32 _ _ (54633 / 2500) (2185323 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3095628032 :
    ThetaLowerSegment 3095628032 3095759104 (309555664042943 / 100000)
      (309568668906067 / 100000) := by
  exact
    packedTile65536 3095628032 3095759104 14 5951 55638 32 _ _ (546331 / 25000) (2185327 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3095759104 :
    ThetaLowerSegment 3095759104 3095890176 (309568668906067 / 100000)
      (309581763391443 / 100000) := by
  exact
    packedTile65536 3095759104 3095890176 14 5992 55639 32 _ _ (136583 / 6250) (2185331 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3095890176 :
    ThetaLowerSegment 3095890176 3096021248 (309581763391443 / 100000)
      (309594897242773 / 100000) := by
  exact
    packedTile65536 3095890176 3096021248 14 6010 55640 32 _ _ (2185333 / 100000) (273167 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3096021248 :
    ThetaLowerSegment 3096021248 3096152320 (309594897242773 / 100000)
      (154804001354381 / 50000) := by
  exact
    packedTile65536 3096021248 3096152320 14 5997 55641 32 _ _ (2185337 / 100000) (109267 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3096152320 :
    ThetaLowerSegment 3096152320 3096283392 (154804001354381 / 50000) (30962117594431 / 10000) := by
  exact
    packedTile65536 3096152320 3096283392 14 6028 55643 32 _ _ (2185341 / 100000) (68292 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3096283392 :
    ThetaLowerSegment 3096283392 3096414464 (30962117594431 / 10000) (7740853813073 / 2500) := by
  exact
    packedTile65536 3096283392 3096414464 14 5938 55644 32 _ _ (437069 / 20000) (546337 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3096414464 :
    ThetaLowerSegment 3096414464 3096545536 (7740853813073 / 2500) (30964727554967 / 10000) := by
  exact
    packedTile65536 3096414464 3096545536 14 6005 55645 32 _ _ (43707 / 2000) (2185353 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3096545536 :
    ThetaLowerSegment 3096545536 3096676608 (30964727554967 / 10000) (154830239729269 / 50000) := by
  exact
    packedTile65536 3096545536 3096676608 14 6042 55646 32 _ _ (1092677 / 50000) (2185357 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3096676608 :
    ThetaLowerSegment 3096676608 3096807680 (154830239729269 / 50000) (1935459250958 / 625) := by
  exact
    packedTile65536 3096676608 3096807680 14 5949 55647 32 _ _ (1092679 / 50000) (2185361 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3096807680 :
    ThetaLowerSegment 3096807680 3096938752 (1935459250958 / 625) (77421666656897 / 25000) := by
  exact
    packedTile65536 3096807680 3096938752 14 6034 55648 32 _ _ (1092681 / 50000) (437073 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3096938752 :
    ThetaLowerSegment 3096938752 3097069824 (77421666656897 / 25000) (38712495845633 / 12500) := by
  exact
    packedTile65536 3096938752 3097069824 14 6086 55650 32 _ _ (1092683 / 50000) (2185369 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3097069824 :
    ThetaLowerSegment 3097069824 3097200896 (38712495845633 / 12500) (19357068529627 / 6250) := by
  exact
    packedTile65536 3097069824 3097200896 14 6008 55651 32 _ _ (2185371 / 100000) (1092687 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3097200896 :
    ThetaLowerSegment 3097200896 3097331968 (19357068529627 / 6250) (9678939651876 / 3125) := by
  exact
    packedTile65536 3097200896 3097331968 14 5936 55652 32 _ _ (17483 / 800) (1092689 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3097331968 :
    ThetaLowerSegment 3097331968 3097463040 (9678939651876 / 3125) (309739209543959 / 100000) := by
  exact
    packedTile65536 3097331968 3097463040 14 6013 55653 32 _ _ (2185379 / 100000) (1092691 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3097463040 :
    ThetaLowerSegment 3097463040 3097594112 (309739209543959 / 100000)
      (77438068987229 / 25000) := by
  exact
    packedTile65536 3097463040 3097594112 14 5979 55654 32 _ _ (2185383 / 100000) (1092693 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3097594112 :
    ThetaLowerSegment 3097594112 3097725184 (77438068987229 / 25000) (77441337234983 / 25000) := by
  exact
    packedTile65536 3097594112 3097725184 14 5982 55656 32 _ _ (546347 / 25000) (2185391 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3097725184 :
    ThetaLowerSegment 3097725184 3097856256 (77441337234983 / 25000) (77444565058967 / 25000) := by
  exact
    packedTile65536 3097725184 3097856256 14 5908 55657 32 _ _ (136587 / 6250) (437079 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3097856256 :
    ThetaLowerSegment 3097856256 3097987328 (77444565058967 / 25000) (9680985106381 / 3125) := by
  exact
    packedTile65536 3097856256 3097987328 14 6069 55658 32 _ _ (546349 / 25000) (2185399 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3097987328 :
    ThetaLowerSegment 3097987328 3098118400 (9680985106381 / 3125) (38725571553449 / 12500) := by
  exact
    packedTile65536 3097987328 3098118400 14 5971 55659 32 _ _ (10927 / 500) (2185403 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3098118400 :
    ThetaLowerSegment 3098118400 3098249472 (38725571553449 / 12500)
      (309817665188947 / 100000) := by
  exact
    packedTile65536 3098118400 3098249472 14 5991 55660 32 _ _ (437081 / 20000) (68294 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3098249472 :
    ThetaLowerSegment 3098249472 3098380544 (309817665188947 / 100000) (19364421007511 / 6250) := by
  exact
    packedTile65536 3098249472 3098380544 14 5981 55661 32 _ _ (2185409 / 100000) (546353 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3098380544 :
    ThetaLowerSegment 3098380544 3098511616 (19364421007511 / 6250) (30984366939431 / 10000) := by
  exact
    packedTile65536 3098380544 3098511616 14 5918 55663 32 _ _ (2185413 / 100000) (273177 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3098511616 :
    ThetaLowerSegment 3098511616 3098642688 (30984366939431 / 10000) (61971362935513 / 20000) := by
  exact
    packedTile65536 3098511616 3098642688 14 6015 55664 32 _ _ (2185417 / 100000) (109271 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3098642688 :
    ThetaLowerSegment 3098642688 3098773760 (61971362935513 / 20000)
      (309869903169923 / 100000) := by
  exact
    packedTile65536 3098642688 3098773760 14 5989 55665 32 _ _ (1092711 / 50000) (87417 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3098773760 :
    ThetaLowerSegment 3098773760 3098904832 (309869903169923 / 100000) (12395322989297 / 4000) := by
  exact
    packedTile65536 3098773760 3098904832 14 6027 55666 32 _ _ (1092713 / 50000) (2185429 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3098904832 :
    ThetaLowerSegment 3098904832 3099035904 (12395322989297 / 4000) (12395843558723 / 4000) := by
  exact
    packedTile65536 3098904832 3099035904 14 5955 55667 32 _ _ (218543 / 10000) (2185433 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3099035904 :
    ThetaLowerSegment 3099035904 3099166976 (12395843558723 / 4000) (309909251837057 / 100000) := by
  exact
    packedTile65536 3099035904 3099166976 14 6023 55668 32 _ _ (1092717 / 50000) (2185437 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3099166976 :
    ThetaLowerSegment 3099166976 3099298048 (309909251837057 / 100000)
      (309922423471883 / 100000) := by
  exact
    packedTile65536 3099166976 3099298048 14 6027 55670 32 _ _ (1092719 / 50000) (2185441 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3099298048 :
    ThetaLowerSegment 3099298048 3099429120 (309922423471883 / 100000)
      (309935737190639 / 100000) := by
  exact
    packedTile65536 3099298048 3099429120 14 6092 55671 32 _ _ (2185443 / 100000) (1092723 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3099429120 :
    ThetaLowerSegment 3099429120 3099560192 (309935737190639 / 100000)
      (154974369207421 / 50000) := by
  exact
    packedTile65536 3099429120 3099560192 14 5949 55672 32 _ _ (2185447 / 100000) (43709 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3099560192 :
    ThetaLowerSegment 3099560192 3099691264 (154974369207421 / 50000)
      (309961962578843 / 100000) := by
  exact
    packedTile65536 3099560192 3099691264 14 6051 55673 32 _ _ (2185451 / 100000) (1092727 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3099691264 :
    ThetaLowerSegment 3099691264 3099822336 (309961962578843 / 100000)
      (309975014116103 / 100000) := by
  exact
    packedTile65536 3099691264 3099822336 14 5972 55674 32 _ _ (437091 / 20000) (1092729 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3099822336 :
    ThetaLowerSegment 3099822336 3099953408 (309975014116103 / 100000)
      (309988107206963 / 100000) := by
  exact
    packedTile65536 3099822336 3099953408 14 5991 55676 32 _ _ (109273 / 5000) (2185463 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3099953408 :
    ThetaLowerSegment 3099953408 3100084480 (309988107206963 / 100000)
      (310001200321787 / 100000) := by
  exact
    packedTile65536 3099953408 3100084480 14 5991 55677 32 _ _ (273183 / 12500) (2185467 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3100084480 :
    ThetaLowerSegment 3100084480 3100215552 (310001200321787 / 100000)
      (62002810611819 / 20000) := by
  exact
    packedTile65536 3100084480 3100215552 14 5881 55678 32 _ _ (546367 / 25000) (2185471 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3100215552 :
    ThetaLowerSegment 3100215552 3100346624 (62002810611819 / 20000) (62005426621803 / 20000) := by
  exact
    packedTile65536 3100215552 3100346624 14 5985 55679 32 _ _ (68296 / 3125) (87419 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3100346624 :
    ThetaLowerSegment 3100346624 3100477696 (62005426621803 / 20000)
      (310040123578359 / 100000) := by
  exact
    packedTile65536 3100346624 3100477696 14 5944 55680 32 _ _ (546369 / 25000) (2185479 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3100477696 :
    ThetaLowerSegment 3100477696 3100608768 (310040123578359 / 100000)
      (38756648274787 / 12500) := by
  exact
    packedTile65536 3100477696 3100608768 14 5977 55681 32 _ _ (2185481 / 100000) (546371 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3100608768 :
    ThetaLowerSegment 3100608768 3100739840 (38756648274787 / 12500) (9689569115278 / 3125) := by
  exact
    packedTile65536 3100608768 3100739840 14 5960 55683 32 _ _ (437097 / 20000) (136593 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3100739840 :
    ThetaLowerSegment 3100739840 3100870912 (9689569115278 / 3125) (310079269985671 / 100000) := by
  exact
    packedTile65536 3100739840 3100870912 14 5975 55684 32 _ _ (2185489 / 100000) (546373 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3100870912 :
    ThetaLowerSegment 3100870912 3101001984 (310079269985671 / 100000)
      (62018462601579 / 20000) := by
  exact
    packedTile65536 3100870912 3101001984 14 5968 55685 32 _ _ (2185493 / 100000) (273187 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3101001984 :
    ThetaLowerSegment 3101001984 3101133056 (62018462601579 / 20000)
      (310105386656931 / 100000) := by
  exact
    packedTile65536 3101001984 3101133056 14 5982 55686 32 _ _ (1092749 / 50000) (2185501 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3101133056 :
    ThetaLowerSegment 3101133056 3101264128 (310105386656931 / 100000)
      (62023681138469 / 20000) := by
  exact
    packedTile65536 3101133056 3101264128 14 5957 55687 32 _ _ (1092751 / 50000) (437101 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3101264128 :
    ThetaLowerSegment 3101264128 3101395200 (62023681138469 / 20000)
      (310131684826801 / 100000) := by
  exact
    packedTile65536 3101264128 3101395200 14 6076 55688 32 _ _ (1092753 / 50000) (2185509 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3101395200 :
    ThetaLowerSegment 3101395200 3101526272 (310131684826801 / 100000)
      (310144668941711 / 100000) := by
  exact
    packedTile65536 3101395200 3101526272 14 5941 55690 32 _ _ (218551 / 10000) (2185513 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3101526272 :
    ThetaLowerSegment 3101526272 3101657344 (310144668941711 / 100000) (9692428707868 / 3125) := by
  exact
    packedTile65536 3101526272 3101657344 14 5971 55691 32 _ _ (437103 / 20000) (1092759 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3101657344 :
    ThetaLowerSegment 3101657344 3101788416 (9692428707868 / 3125) (155085369986989 / 50000) := by
  exact
    packedTile65536 3101657344 3101788416 14 5958 55692 32 _ _ (2185519 / 100000) (1092761 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3101788416 :
    ThetaLowerSegment 3101788416 3101919488 (155085369986989 / 50000)
      (155091944040173 / 50000) := by
  exact
    packedTile65536 3101788416 3101919488 14 6016 55693 32 _ _ (2185523 / 100000) (1092763 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3101919488 :
    ThetaLowerSegment 3101919488 3102050560 (155091944040173 / 50000) (77549244846769 / 25000) := by
  exact
    packedTile65536 3101919488 3102050560 14 5990 55694 32 _ _ (2185527 / 100000) (218553 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3102050560 :
    ThetaLowerSegment 3102050560 3102181632 (77549244846769 / 25000)
      (310210055419049 / 100000) := by
  exact
    packedTile65536 3102050560 3102181632 14 5983 55696 32 _ _ (2185531 / 100000) (1092767 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3102181632 :
    ThetaLowerSegment 3102181632 3102312704 (310210055419049 / 100000)
      (310222987235561 / 100000) := by
  exact
    packedTile65536 3102181632 3102312704 14 5917 55697 32 _ _ (68298 / 3125) (2185539 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3102312704 :
    ThetaLowerSegment 3102312704 3102443776 (310222987235561 / 100000)
      (310236111403261 / 100000) := by
  exact
    packedTile65536 3102312704 3102443776 14 6005 55698 32 _ _ (109277 / 5000) (2185543 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3102443776 :
    ThetaLowerSegment 3102443776 3102574848 (310236111403261 / 100000)
      (310249506602437 / 100000) := by
  exact
    packedTile65536 3102443776 3102574848 14 6129 55699 32 _ _ (273193 / 12500) (2185547 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3102574848 :
    ThetaLowerSegment 3102574848 3102705920 (310249506602437 / 100000)
      (310262613333793 / 100000) := by
  exact
    packedTile65536 3102574848 3102705920 14 5997 55700 32 _ _ (546387 / 25000) (2185551 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3102705920 :
    ThetaLowerSegment 3102705920 3102836992 (310262613333793 / 100000) (9696114204017 / 3125) := by
  exact
    packedTile65536 3102705920 3102836992 14 5967 55701 32 _ _ (2185553 / 100000) (546389 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3102836992 :
    ThetaLowerSegment 3102836992 3102968064 (9696114204017 / 3125) (310288778798329 / 100000) := by
  exact
    packedTile65536 3102836992 3102968064 14 6005 55703 32 _ _ (2185557 / 100000) (54639 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3102968064 :
    ThetaLowerSegment 3102968064 3103099136 (310288778798329 / 100000)
      (310301761030669 / 100000) := by
  exact
    packedTile65536 3102968064 3103099136 14 5940 55704 32 _ _ (2185561 / 100000) (546391 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3103099136 :
    ThetaLowerSegment 3103099136 3103230208 (310301761030669 / 100000)
      (310314983698919 / 100000) := by
  exact
    packedTile65536 3103099136 3103230208 14 6050 55705 32 _ _ (437113 / 20000) (68299 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3103230208 :
    ThetaLowerSegment 3103230208 3103361280 (310314983698919 / 100000)
      (155163955669777 / 50000) := by
  exact
    packedTile65536 3103230208 3103361280 14 5915 55706 32 _ _ (2185569 / 100000) (546393 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3103361280 :
    ThetaLowerSegment 3103361280 3103492352 (155163955669777 / 50000) (77585220680311 / 25000) := by
  exact
    packedTile65536 3103361280 3103492352 14 5935 55707 32 _ _ (1092787 / 50000) (2185577 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3103492352 :
    ThetaLowerSegment 3103492352 3103623424 (77585220680311 / 25000) (38794240234949 / 12500) := by
  exact
    packedTile65536 3103492352 3103623424 14 5966 55708 32 _ _ (1092789 / 50000) (2185581 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3103623424 :
    ThetaLowerSegment 3103623424 3103754496 (38794240234949 / 12500) (155183630243269 / 50000) := by
  exact
    packedTile65536 3103623424 3103754496 14 6103 55710 32 _ _ (1092791 / 50000) (437117 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3103754496 :
    ThetaLowerSegment 3103754496 3103885568 (155183630243269 / 50000) (77595089675859 / 25000) := by
  exact
    packedTile65536 3103754496 3103885568 14 5993 55711 32 _ _ (1092793 / 50000) (2185589 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3103885568 :
    ThetaLowerSegment 3103885568 3104016640 (77595089675859 / 25000) (155196803878039 / 50000) := by
  exact
    packedTile65536 3103885568 3104016640 14 6062 55712 32 _ _ (2185591 / 100000) (1092797 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3104016640 :
    ThetaLowerSegment 3104016640 3104147712 (155196803878039 / 50000) (77601624598847 / 25000) := by
  exact
    packedTile65536 3104016640 3104147712 14 5898 55713 32 _ _ (437119 / 20000) (1092799 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3104147712 :
    ThetaLowerSegment 3104147712 3104278784 (77601624598847 / 25000) (38802452591473 / 12500) := by
  exact
    packedTile65536 3104147712 3104278784 14 6004 55714 32 _ _ (2185599 / 100000) (1092801 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3104278784 :
    ThetaLowerSegment 3104278784 3104409856 (38802452591473 / 12500)
      (310432561687147 / 100000) := by
  exact
    packedTile65536 3104278784 3104409856 14 5921 55716 32 _ _ (2185603 / 100000) (1092803 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3104409856 :
    ThetaLowerSegment 3104409856 3104540928 (310432561687147 / 100000) (15522279285963 / 5000) := by
  exact
    packedTile65536 3104409856 3104540928 14 5959 55717 32 _ _ (2185607 / 100000) (218561 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3104540928 :
    ThetaLowerSegment 3104540928 3104672000 (15522279285963 / 5000) (9701833468072 / 3125) := by
  exact
    packedTile65536 3104540928 3104672000 14 5987 55718 32 _ _ (546403 / 25000) (437123 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3104672000 :
    ThetaLowerSegment 3104672000 3104803072 (9701833468072 / 3125) (1940449009377 / 625) := by
  exact
    packedTile65536 3104672000 3104803072 14 6026 55719 32 _ _ (136601 / 6250) (2185619 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3104803072 :
    ThetaLowerSegment 3104803072 3104934144 (1940449009377 / 625) (7762128361029 / 2500) := by
  exact
    packedTile65536 3104803072 3104934144 14 6082 55720 32 _ _ (109281 / 5000) (2185623 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3104934144 :
    ThetaLowerSegment 3104934144 3105065216 (7762128361029 / 2500) (1940613573052 / 625) := by
  exact
    packedTile65536 3104934144 3105065216 14 5965 55721 32 _ _ (273203 / 12500) (2185627 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3105065216 :
    ThetaLowerSegment 3105065216 3105196288 (1940613573052 / 625) (155255548749113 / 50000) := by
  exact
    packedTile65536 3105065216 3105196288 14 5914 55723 32 _ _ (2185629 / 100000) (68301 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3105196288 :
    ThetaLowerSegment 3105196288 3105327360 (155255548749113 / 50000) (19407765118443 / 6250) := by
  exact
    packedTile65536 3105196288 3105327360 14 6014 55724 32 _ _ (2185633 / 100000) (546409 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3105327360 :
    ThetaLowerSegment 3105327360 3105458432 (19407765118443 / 6250) (155268649445263 / 50000) := by
  exact
    packedTile65536 3105327360 3105458432 14 5974 55725 32 _ _ (2185637 / 100000) (54641 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3105458432 :
    ThetaLowerSegment 3105458432 3105589504 (155268649445263 / 50000) (62110060253767 / 20000) := by
  exact
    packedTile65536 3105458432 3105589504 14 5949 55726 32 _ _ (2185641 / 100000) (546411 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3105589504 :
    ThetaLowerSegment 3105589504 3105720576 (62110060253767 / 20000) (62112695267379 / 20000) := by
  exact
    packedTile65536 3105589504 3105720576 14 6028 55727 32 _ _ (437129 / 20000) (136603 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3105720576 :
    ThetaLowerSegment 3105720576 3105851648 (62112695267379 / 20000) (62115304933479 / 20000) := by
  exact
    packedTile65536 3105720576 3105851648 14 5970 55728 32 _ _ (43713 / 2000) (2185653 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3105851648 :
    ThetaLowerSegment 3105851648 3105982720 (62115304933479 / 20000)
      (310589662633589 / 100000) := by
  exact
    packedTile65536 3105851648 3105982720 14 6011 55730 32 _ _ (1092827 / 50000) (2185657 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3105982720 :
    ThetaLowerSegment 3105982720 3106113792 (310589662633589 / 100000)
      (62120571490187 / 20000) := by
  exact
    packedTile65536 3105982720 3106113792 14 6037 55731 32 _ _ (1092829 / 50000) (2185661 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3106113792 :
    ThetaLowerSegment 3106113792 3106244864 (62120571490187 / 20000) (62123205212897 / 20000) := by
  exact
    packedTile65536 3106113792 3106244864 14 6025 55732 32 _ _ (1092831 / 50000) (437133 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3106244864 :
    ThetaLowerSegment 3106244864 3106375936 (62123205212897 / 20000)
      (310629061382473 / 100000) := by
  exact
    packedTile65536 3106244864 3106375936 14 5964 55733 32 _ _ (2185667 / 100000) (218567 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3106375936 :
    ThetaLowerSegment 3106375936 3106507008 (310629061382473 / 100000) (19415147027989 / 6250) := by
  exact
    packedTile65536 3106375936 3106507008 14 6081 55734 32 _ _ (2185671 / 100000) (1092837 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3106507008 :
    ThetaLowerSegment 3106507008 3106638080 (19415147027989 / 6250) (310655459940799 / 100000) := by
  exact
    packedTile65536 3106507008 3106638080 14 5997 55736 32 _ _ (87427 / 4000) (1092839 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3106638080 :
    ThetaLowerSegment 3106638080 3106769152 (310655459940799 / 100000)
      (38833556178887 / 12500) := by
  exact
    packedTile65536 3106638080 3106769152 14 5943 55737 32 _ _ (2185679 / 100000) (1092841 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3106769152 :
    ThetaLowerSegment 3106769152 3106900224 (38833556178887 / 12500) (155340884491649 / 50000) := by
  exact
    packedTile65536 3106769152 3106900224 14 6094 55738 32 _ _ (2185683 / 100000) (1092843 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3106900224 :
    ThetaLowerSegment 3106900224 3107031296 (155340884491649 / 50000) (31069485906873 / 10000) := by
  exact
    packedTile65536 3106900224 3107031296 14 5989 55739 32 _ _ (273211 / 12500) (2185691 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3107031296 :
    ThetaLowerSegment 3107031296 3107162368 (31069485906873 / 10000) (155353916668221 / 50000) := by
  exact
    packedTile65536 3107031296 3107162368 14 5936 55740 32 _ _ (546423 / 25000) (437139 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3107162368 :
    ThetaLowerSegment 3107162368 3107293440 (155353916668221 / 50000)
      (155360452992109 / 50000) := by
  exact
    packedTile65536 3107162368 3107293440 14 5981 55741 32 _ _ (68303 / 3125) (2185699 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3107293440 :
    ThetaLowerSegment 3107293440 3107424512 (155360452992109 / 50000)
      (155367027577709 / 50000) := by
  exact
    packedTile65536 3107293440 3107424512 14 6016 55743 32 _ _ (21857 / 1000) (2185703 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3107424512 :
    ThetaLowerSegment 3107424512 3107555584 (155367027577709 / 50000)
      (310747438227133 / 100000) := by
  exact
    packedTile65536 3107424512 3107555584 14 6123 55744 32 _ _ (437141 / 20000) (546427 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3107555584 :
    ThetaLowerSegment 3107555584 3107686656 (310747438227133 / 100000) (3884506441551 / 1250) := by
  exact
    packedTile65536 3107555584 3107686656 14 5983 55745 32 _ _ (2185709 / 100000) (136607 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3107686656 :
    ThetaLowerSegment 3107686656 3107817728 (3884506441551 / 1250) (31077369517347 / 10000) := by
  exact
    packedTile65536 3107686656 3107817728 14 6030 55746 32 _ _ (2185713 / 100000) (546429 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3107817728 :
    ThetaLowerSegment 3107817728 3107948800 (31077369517347 / 10000) (62157320366471 / 20000) := by
  exact
    packedTile65536 3107817728 3107948800 14 5905 55747 32 _ _ (2185717 / 100000) (54643 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3107948800 :
    ThetaLowerSegment 3107948800 3108079872 (62157320366471 / 20000)
      (310799812330079 / 100000) := by
  exact
    packedTile65536 3107948800 3108079872 14 6044 55748 32 _ _ (2185721 / 100000) (546431 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3108079872 :
    ThetaLowerSegment 3108079872 3108210944 (310799812330079 / 100000)
      (62162581402909 / 20000) := by
  exact
    packedTile65536 3108079872 3108210944 14 5991 55750 32 _ _ (1092863 / 50000) (2185729 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3108210944 :
    ThetaLowerSegment 3108210944 3108342016 (62162581402909 / 20000) (62165219579019 / 20000) := by
  exact
    packedTile65536 3108210944 3108342016 14 6035 55751 32 _ _ (218573 / 10000) (2185733 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3108342016 :
    ThetaLowerSegment 3108342016 3108473088 (62165219579019 / 20000)
      (310838958753951 / 100000) := by
  exact
    packedTile65536 3108342016 3108473088 14 5884 55752 32 _ _ (1092867 / 50000) (2185737 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3108473088 :
    ThetaLowerSegment 3108473088 3108604160 (310838958753951 / 100000)
      (310851957337837 / 100000) := by
  exact
    packedTile65536 3108473088 3108604160 14 5947 55753 32 _ _ (1092869 / 50000) (2185741 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3108604160 :
    ThetaLowerSegment 3108604160 3108735232 (310851957337837 / 100000)
      (310865159219517 / 100000) := by
  exact
    packedTile65536 3108604160 3108735232 14 6040 55754 32 _ _ (1092871 / 50000) (437149 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3108735232 :
    ThetaLowerSegment 3108735232 3108866304 (310865159219517 / 100000)
      (77719593015033 / 25000) := by
  exact
    packedTile65536 3108735232 3108866304 14 6045 55756 32 _ _ (2185747 / 100000) (8743 / 400)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3108866304 :
    ThetaLowerSegment 3108866304 3108997376 (77719593015033 / 25000) (155445780440833 / 50000) := by
  exact
    packedTile65536 3108866304 3108997376 14 6034 55757 32 _ _ (2185751 / 100000) (1092877 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3108997376 :
    ThetaLowerSegment 3108997376 3109128448 (155445780440833 / 50000)
      (155452359563383 / 50000) := by
  exact
    packedTile65536 3108997376 3109128448 14 6020 55758 32 _ _ (437151 / 20000) (1092879 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3109128448 :
    ThetaLowerSegment 3109128448 3109259520 (155452359563383 / 50000)
      (310917700349467 / 100000) := by
  exact
    packedTile65536 3109128448 3109259520 14 5939 55759 32 _ _ (2185759 / 100000) (1092881 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3109259520 :
    ThetaLowerSegment 3109259520 3109390592 (310917700349467 / 100000)
      (62186155117943 / 20000) := by
  exact
    packedTile65536 3109259520 3109390592 14 5982 55760 32 _ _ (546441 / 25000) (2185767 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3109390592 :
    ThetaLowerSegment 3109390592 3109521664 (62186155117943 / 20000)
      (310943855225427 / 100000) := by
  exact
    packedTile65536 3109390592 3109521664 14 5984 55761 32 _ _ (273221 / 12500) (2185771 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3109521664 :
    ThetaLowerSegment 3109521664 3109652736 (310943855225427 / 100000)
      (310956982972059 / 100000) := by
  exact
    packedTile65536 3109521664 3109652736 14 6006 55763 32 _ _ (546443 / 25000) (87431 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3109652736 :
    ThetaLowerSegment 3109652736 3109783808 (310956982972059 / 100000)
      (310970075770299 / 100000) := by
  exact
    packedTile65536 3109652736 3109783808 14 5990 55764 32 _ _ (136611 / 6250) (2185779 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3109783808 :
    ThetaLowerSegment 3109783808 3109914880 (310970075770299 / 100000)
      (310983148920479 / 100000) := by
  exact
    packedTile65536 3109783808 3109914880 14 5981 55765 32 _ _ (109289 / 5000) (2185783 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3109914880 :
    ThetaLowerSegment 3109914880 3110045952 (310983148920479 / 100000)
      (38874520112323 / 12500) := by
  exact
    packedTile65536 3109914880 3110045952 14 5953 55766 32 _ _ (437157 / 20000) (546447 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3110045952 :
    ThetaLowerSegment 3110045952 3110177024 (38874520112323 / 12500) (77752347323403 / 25000) := by
  exact
    packedTile65536 3110045952 3110177024 14 6052 55767 32 _ _ (2185789 / 100000) (68306 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3110177024 :
    ThetaLowerSegment 3110177024 3110308096 (77752347323403 / 25000) (155511311042217 / 50000) := by
  exact
    packedTile65536 3110177024 3110308096 14 6054 55768 32 _ _ (2185793 / 100000) (546449 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3110308096 :
    ThetaLowerSegment 3110308096 3110439168 (155511311042217 / 50000)
      (311035730309043 / 100000) := by
  exact
    packedTile65536 3110308096 3110439168 14 5997 55770 32 _ _ (2185797 / 100000) (10929 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3110439168 :
    ThetaLowerSegment 3110439168 3110570240 (311035730309043 / 100000) (7776216592339 / 2500) := by
  exact
    packedTile65536 3110439168 3110570240 14 5917 55771 32 _ _ (2185801 / 100000) (546451 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3110570240 :
    ThetaLowerSegment 3110570240 3110701312 (7776216592339 / 2500) (155530920958967 / 50000) := by
  exact
    packedTile65536 3110570240 3110701312 14 6029 55772 32 _ _ (1092903 / 50000) (2185809 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3110701312 :
    ThetaLowerSegment 3110701312 3110832384 (155530920958967 / 50000) (9721092467617 / 3125) := by
  exact
    packedTile65536 3110701312 3110832384 14 6001 55773 32 _ _ (218581 / 10000) (2185813 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3110832384 :
    ThetaLowerSegment 3110832384 3110963456 (9721092467617 / 3125) (38886008138061 / 12500) := by
  exact
    packedTile65536 3110832384 3110963456 14 5996 55774 32 _ _ (1092907 / 50000) (2185817 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3110963456 :
    ThetaLowerSegment 3110963456 3111094528 (38886008138061 / 12500) (155550628258059 / 50000) := by
  exact
    packedTile65536 3110963456 3111094528 14 6035 55776 32 _ _ (1092909 / 50000) (2185821 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3111094528 :
    ThetaLowerSegment 3111094528 3111225600 (155550628258059 / 50000) (62222904455181 / 20000) := by
  exact
    packedTile65536 3111094528 3111225600 14 6069 55777 32 _ _ (2185823 / 100000) (1092913 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3111225600 :
    ThetaLowerSegment 3111225600 3111356672 (62222904455181 / 20000)
      (311127619751289 / 100000) := by
  exact
    packedTile65536 3111225600 3111356672 14 5992 55778 32 _ _ (2185827 / 100000) (218583 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3111356672 :
    ThetaLowerSegment 3111356672 3111487744 (311127619751289 / 100000)
      (311140516154189 / 100000) := by
  exact
    packedTile65536 3111356672 3111487744 14 5900 55779 32 _ _ (2185831 / 100000) (1092917 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3111487744 :
    ThetaLowerSegment 3111487744 3111618816 (311140516154189 / 100000)
      (311153609305839 / 100000) := by
  exact
    packedTile65536 3111487744 3111618816 14 5990 55780 32 _ _ (437167 / 20000) (1092919 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3111618816 :
    ThetaLowerSegment 3111618816 3111749888 (311153609305839 / 100000)
      (311166803030043 / 100000) := by
  exact
    packedTile65536 3111618816 3111749888 14 6036 55781 32 _ _ (2185839 / 100000) (1092921 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3111749888 :
    ThetaLowerSegment 3111749888 3111880960 (311166803030043 / 100000)
      (62235989302003 / 20000) := by
  exact
    packedTile65536 3111749888 3111880960 14 6013 55783 32 _ _ (546461 / 25000) (2185847 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3111880960 :
    ThetaLowerSegment 3111880960 3112012032 (62235989302003 / 20000)
      (311193109686671 / 100000) := by
  exact
    packedTile65536 3111880960 3112012032 14 6022 55784 32 _ _ (273231 / 12500) (2185851 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3112012032 :
    ThetaLowerSegment 3112012032 3112143104 (311193109686671 / 100000)
      (311205960310579 / 100000) := by
  exact
    packedTile65536 3112012032 3112143104 14 5879 55785 32 _ _ (546463 / 25000) (437171 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3112143104 :
    ThetaLowerSegment 3112143104 3112274176 (311205960310579 / 100000)
      (62243804597207 / 20000) := by
  exact
    packedTile65536 3112143104 3112274176 14 5976 55786 32 _ _ (68308 / 3125) (2185859 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3112274176 :
    ThetaLowerSegment 3112274176 3112405248 (62243804597207 / 20000) (62246415825563 / 20000) := by
  exact
    packedTile65536 3112274176 3112405248 14 5973 55787 32 _ _ (109293 / 5000) (2185863 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3112405248 :
    ThetaLowerSegment 3112405248 3112536320 (62246415825563 / 20000) (31124546317921 / 10000) := by
  exact
    packedTile65536 3112405248 3112536320 14 6123 55788 32 _ _ (437173 / 20000) (546467 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3112536320 :
    ThetaLowerSegment 3112536320 3112667392 (31124546317921 / 10000)
      (311258580579079 / 100000) := by
  exact
    packedTile65536 3112536320 3112667392 14 6001 55790 32 _ _ (2185869 / 100000) (136617 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3112667392 :
    ThetaLowerSegment 3112667392 3112798464 (311258580579079 / 100000)
      (62254370639987 / 20000) := by
  exact
    packedTile65536 3112667392 3112798464 14 6072 55791 32 _ _ (2185873 / 100000) (546469 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3112798464 :
    ThetaLowerSegment 3112798464 3112929536 (62254370639987 / 20000)
      (311284911629133 / 100000) := by
  exact
    packedTile65536 3112798464 3112929536 14 5974 55792 32 _ _ (2185877 / 100000) (54647 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3112929536 :
    ThetaLowerSegment 3112929536 3113060608 (311284911629133 / 100000)
      (311298033478779 / 100000) := by
  exact
    packedTile65536 3112929536 3113060608 14 6003 55793 32 _ _ (1092941 / 50000) (437177 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3113060608 :
    ThetaLowerSegment 3113060608 3113191680 (311298033478779 / 100000)
      (311311179397183 / 100000) := by
  exact
    packedTile65536 3113060608 3113191680 14 6014 55794 32 _ _ (1092943 / 50000) (2185889 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3113191680 :
    ThetaLowerSegment 3113191680 3113322752 (311311179397183 / 100000)
      (311324117680093 / 100000) := by
  exact
    packedTile65536 3113191680 3113322752 14 5919 55795 32 _ _ (218589 / 10000) (2185893 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3113322752 :
    ThetaLowerSegment 3113322752 3113339136 (311324117680093 / 100000)
      (311325748357017 / 100000) := by
  exact
    packedTile65536 3113322752 3113339136 11 746 55797 32 _ _ (1092947 / 50000) (2185897 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3113339136 :
    ThetaLowerSegment 3113339136 3113341184 (311325748357017 / 100000)
      (77831487911313 / 25000) := by
  exact
    packedTile65536 3113339136 3113341184 8 93 55797 32 _ _ (437179 / 20000) (1092949 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_3081341184_3113341184 :
    ThetaLowerSegment 3081341184 3113341184 (308127750852491 / 100000)
      (77831487911313 / 25000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3081341184 cell3081472256)
                  (ThetaLowerSegment.join cell3081603328 cell3081734400))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3081865472 cell3081996544)
                  (ThetaLowerSegment.join cell3082127616 cell3082258688)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3082389760 cell3082520832)
                  (ThetaLowerSegment.join cell3082651904 cell3082782976))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3082914048 cell3083045120)
                  (ThetaLowerSegment.join cell3083176192 cell3083307264))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3083438336 cell3083569408)
                  (ThetaLowerSegment.join cell3083700480 cell3083831552))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3083962624 cell3084093696)
                  (ThetaLowerSegment.join cell3084224768 cell3084355840)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3084486912 cell3084617984)
                  (ThetaLowerSegment.join cell3084749056 cell3084880128))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3085011200 cell3085142272)
                  (ThetaLowerSegment.join cell3085273344 cell3085404416)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3085535488 cell3085666560)
                  (ThetaLowerSegment.join cell3085797632 cell3085928704))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3086059776 cell3086190848)
                  (ThetaLowerSegment.join cell3086321920 cell3086452992)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3086584064 cell3086715136)
                  (ThetaLowerSegment.join cell3086846208 cell3086977280))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3087108352 cell3087239424)
                  (ThetaLowerSegment.join cell3087370496 cell3087501568))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3087632640 cell3087763712)
                  (ThetaLowerSegment.join cell3087894784 cell3088025856))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3088156928 cell3088288000)
                  (ThetaLowerSegment.join cell3088419072 cell3088550144)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3088681216 cell3088812288)
                  (ThetaLowerSegment.join cell3088943360 cell3089074432))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3089205504 cell3089336576)
                  (ThetaLowerSegment.join cell3089467648 cell3089598720))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3089729792 cell3089860864)
                  (ThetaLowerSegment.join cell3089991936 cell3090123008))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3090254080 cell3090385152)
                  (ThetaLowerSegment.join cell3090516224 cell3090647296)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3090778368 cell3090909440)
                  (ThetaLowerSegment.join cell3091040512 cell3091171584))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3091302656 cell3091433728)
                  (ThetaLowerSegment.join cell3091564800 cell3091695872))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3091826944 cell3091958016)
                  (ThetaLowerSegment.join cell3092089088 cell3092220160))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3092351232 cell3092482304)
                  (ThetaLowerSegment.join cell3092613376 cell3092744448)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3092875520 cell3093006592)
                  (ThetaLowerSegment.join cell3093137664 cell3093268736))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3093399808 cell3093530880)
                  (ThetaLowerSegment.join cell3093661952 cell3093793024)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3093924096 cell3094055168)
                  (ThetaLowerSegment.join cell3094186240 cell3094317312))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3094448384 cell3094579456)
                  (ThetaLowerSegment.join cell3094710528 cell3094841600)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3094972672 cell3095103744)
                  (ThetaLowerSegment.join cell3095234816 cell3095365888))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3095496960 cell3095628032)
                  (ThetaLowerSegment.join cell3095759104 cell3095890176))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3096021248 cell3096152320)
                  (ThetaLowerSegment.join cell3096283392 cell3096414464))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3096545536 cell3096676608)
                  (ThetaLowerSegment.join cell3096807680 cell3096938752)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3097069824 cell3097200896)
                  (ThetaLowerSegment.join cell3097331968 cell3097463040))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3097594112 cell3097725184)
                  (ThetaLowerSegment.join cell3097856256 cell3097987328)))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3098118400 cell3098249472)
                  (ThetaLowerSegment.join cell3098380544 cell3098511616))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3098642688 cell3098773760)
                  (ThetaLowerSegment.join cell3098904832 cell3099035904)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3099166976 cell3099298048)
                  (ThetaLowerSegment.join cell3099429120 cell3099560192))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3099691264 cell3099822336)
                  (ThetaLowerSegment.join cell3099953408 cell3100084480))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3100215552 cell3100346624)
                  (ThetaLowerSegment.join cell3100477696 cell3100608768))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3100739840 cell3100870912)
                  (ThetaLowerSegment.join cell3101001984 cell3101133056)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3101264128 cell3101395200)
                  (ThetaLowerSegment.join cell3101526272 cell3101657344))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3101788416 cell3101919488)
                  (ThetaLowerSegment.join cell3102050560 cell3102181632)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3102312704 cell3102443776)
                  (ThetaLowerSegment.join cell3102574848 cell3102705920))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3102836992 cell3102968064)
                  (ThetaLowerSegment.join cell3103099136 cell3103230208)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3103361280 cell3103492352)
                  (ThetaLowerSegment.join cell3103623424 cell3103754496))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3103885568 cell3104016640)
                  (ThetaLowerSegment.join cell3104147712 cell3104278784))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3104409856 cell3104540928)
                  (ThetaLowerSegment.join cell3104672000 cell3104803072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3104934144 cell3105065216)
                  (ThetaLowerSegment.join cell3105196288 cell3105327360)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3105458432 cell3105589504)
                  (ThetaLowerSegment.join cell3105720576 cell3105851648))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3105982720 cell3106113792)
                  (ThetaLowerSegment.join cell3106244864 cell3106375936))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3106507008 cell3106638080)
                  (ThetaLowerSegment.join cell3106769152 cell3106900224))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3107031296 cell3107162368)
                  (ThetaLowerSegment.join cell3107293440 cell3107424512)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3107555584 cell3107686656)
                  (ThetaLowerSegment.join cell3107817728 cell3107948800))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3108079872 cell3108210944)
                  (ThetaLowerSegment.join cell3108342016 cell3108473088))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3108604160 cell3108735232)
                  (ThetaLowerSegment.join cell3108866304 cell3108997376))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3109128448 cell3109259520)
                  (ThetaLowerSegment.join cell3109390592 cell3109521664)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3109652736 cell3109783808)
                  (ThetaLowerSegment.join cell3109914880 cell3110045952))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3110177024 cell3110308096)
                  (ThetaLowerSegment.join cell3110439168 cell3110570240)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3110701312 cell3110832384)
                  (ThetaLowerSegment.join cell3110963456 cell3111094528))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3111225600 cell3111356672)
                  (ThetaLowerSegment.join cell3111487744 cell3111618816)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3111749888 cell3111880960)
                  (ThetaLowerSegment.join cell3112012032 cell3112143104))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3112274176 cell3112405248)
                  (ThetaLowerSegment.join cell3112536320 cell3112667392))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell3112798464 cell3112929536)
                (ThetaLowerSegment.join cell3113060608 cell3113191680))
              (ThetaLowerSegment.join cell3113322752 cell3113339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
