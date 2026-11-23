/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis65536

/-! # Direct theta estimate up to 2537341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell2505341184 :
    ThetaLowerSegment 2505341184 2505472256 (250526307787397 / 100000)
      (250539660703957 / 100000) := by
  exact
    packedTile65536 2505341184 2505472256 14 6170 50053 31 _ _ (270521 / 12500) (2164171 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2505472256 :
    ThetaLowerSegment 2505472256 2505603328 (250539660703957 / 100000)
      (250552606786843 / 100000) := by
  exact
    packedTile65536 2505472256 2505603328 14 5982 50054 31 _ _ (2164173 / 100000) (135261 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2505603328 :
    ThetaLowerSegment 2505603328 2505734400 (250552606786843 / 100000)
      (250565873197983 / 100000) := by
  exact
    packedTile65536 2505603328 2505734400 14 6130 50056 31 _ _ (1082089 / 50000) (2164181 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2505734400 :
    ThetaLowerSegment 2505734400 2505865472 (250565873197983 / 100000)
      (50115821002569 / 20000) := by
  exact
    packedTile65536 2505734400 2505865472 14 6114 50057 31 _ _ (2164183 / 100000) (1082093 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2505865472 :
    ThetaLowerSegment 2505865472 2505996544 (50115821002569 / 20000)
      (250592207013051 / 100000) := by
  exact
    packedTile65536 2505865472 2505996544 14 6054 50058 31 _ _ (2164189 / 100000) (67631 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2505996544 :
    ThetaLowerSegment 2505996544 2506127616 (250592207013051 / 100000)
      (250605276580617 / 100000) := by
  exact
    packedTile65536 2505996544 2506127616 14 6039 50059 31 _ _ (1082097 / 50000) (2164197 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2506127616 :
    ThetaLowerSegment 2506127616 2506258688 (250605276580617 / 100000)
      (250618473866119 / 100000) := by
  exact
    packedTile65536 2506127616 2506258688 14 6098 50061 31 _ _ (2164199 / 100000) (1082101 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2506258688 :
    ThetaLowerSegment 2506258688 2506389760 (250618473866119 / 100000)
      (250631530508851 / 100000) := by
  exact
    packedTile65536 2506258688 2506389760 14 6033 50062 31 _ _ (541051 / 25000) (2164207 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2506389760 :
    ThetaLowerSegment 2506389760 2506520832 (250631530508851 / 100000)
      (250644606659629 / 100000) := by
  exact
    packedTile65536 2506389760 2506520832 14 6042 50063 31 _ _ (2164209 / 100000) (541053 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2506520832 :
    ThetaLowerSegment 2506520832 2506651904 (250644606659629 / 100000)
      (62664407185321 / 25000) := by
  exact
    packedTile65536 2506520832 2506651904 14 6017 50065 31 _ _ (432843 / 20000) (1082109 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2506651904 :
    ThetaLowerSegment 2506651904 2506782976 (62664407185321 / 25000) (62667684896511 / 25000) := by
  exact
    packedTile65536 2506651904 2506782976 14 6058 50066 31 _ _ (108211 / 5000) (2164223 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2506782976 :
    ThetaLowerSegment 2506782976 2506914048 (62667684896511 / 25000)
      (250683722771819 / 100000) := by
  exact
    packedTile65536 2506782976 2506914048 14 5999 50067 31 _ _ (86569 / 4000) (541057 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2506914048 :
    ThetaLowerSegment 2506914048 2507045120 (250683722771819 / 100000)
      (250696855319459 / 100000) := by
  exact
    packedTile65536 2506914048 2507045120 14 6068 50069 31 _ _ (216423 / 10000) (2164233 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2507045120 :
    ThetaLowerSegment 2507045120 2507176192 (250696855319459 / 100000)
      (250710039845171 / 100000) := by
  exact
    packedTile65536 2507045120 2507176192 14 6092 50070 31 _ _ (541059 / 25000) (2164239 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2507176192 :
    ThetaLowerSegment 2507176192 2507307264 (250710039845171 / 100000)
      (125361645746407 / 50000) := by
  exact
    packedTile65536 2507176192 2507307264 14 6123 50071 31 _ _ (2164241 / 100000) (541061 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2507307264 :
    ThetaLowerSegment 2507307264 2507438336 (125361645746407 / 50000) (62684082768741 / 25000) := by
  exact
    packedTile65536 2507307264 2507438336 14 6025 50073 31 _ _ (1082123 / 50000) (2164249 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2507438336 :
    ThetaLowerSegment 2507438336 2507569408 (62684082768741 / 25000) (125374824937809 / 50000) := by
  exact
    packedTile65536 2507438336 2507569408 14 6154 50074 31 _ _ (2164251 / 100000) (1082127 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2507569408 :
    ThetaLowerSegment 2507569408 2507700480 (125374824937809 / 50000)
      (125381439986273 / 50000) := by
  exact
    packedTile65536 2507569408 2507700480 14 6113 50075 31 _ _ (67633 / 3125) (2164259 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2507700480 :
    ThetaLowerSegment 2507700480 2507831552 (125381439986273 / 50000) (62694019951621 / 25000) := by
  exact
    packedTile65536 2507700480 2507831552 14 6099 50076 31 _ _ (1082131 / 50000) (432853 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2507831552 :
    ThetaLowerSegment 2507831552 2507962624 (62694019951621 / 25000) (125394521882907 / 50000) := by
  exact
    packedTile65536 2507831552 2507962624 14 5990 50078 31 _ _ (2164267 / 100000) (216427 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2507962624 :
    ThetaLowerSegment 2507962624 2508093696 (125394521882907 / 50000)
      (125401075298523 / 50000) := by
  exact
    packedTile65536 2507962624 2508093696 14 6056 50079 31 _ _ (135267 / 6250) (86571 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2508093696 :
    ThetaLowerSegment 2508093696 2508224768 (125401075298523 / 50000)
      (125407663357711 / 50000) := by
  exact
    packedTile65536 2508093696 2508224768 14 6088 50080 31 _ _ (2164277 / 100000) (54107 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2508224768 :
    ThetaLowerSegment 2508224768 2508355840 (125407663357711 / 50000)
      (250828440106119 / 100000) := by
  exact
    packedTile65536 2508224768 2508355840 14 6059 50082 31 _ _ (2164283 / 100000) (1082143 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2508355840 :
    ThetaLowerSegment 2508355840 2508486912 (250828440106119 / 100000)
      (250841618455751 / 100000) := by
  exact
    packedTile65536 2508355840 2508486912 14 6089 50083 31 _ _ (67634 / 3125) (2164291 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2508486912 :
    ThetaLowerSegment 2508486912 2508617984 (250841618455751 / 100000)
      (250854690785471 / 100000) := by
  exact
    packedTile65536 2508486912 2508617984 14 6040 50084 31 _ _ (2164293 / 100000) (270537 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2508617984 :
    ThetaLowerSegment 2508617984 2508749056 (250854690785471 / 100000)
      (50173562584849 / 20000) := by
  exact
    packedTile65536 2508617984 2508749056 14 6063 50086 31 _ _ (1082149 / 50000) (2164301 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2508749056 :
    ThetaLowerSegment 2508749056 2508880128 (50173562584849 / 20000)
      (250880833377109 / 100000) := by
  exact
    packedTile65536 2508749056 2508880128 14 6016 50087 31 _ _ (135269 / 6250) (2164307 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2508880128 :
    ThetaLowerSegment 2508880128 2509011200 (250880833377109 / 100000)
      (250893927446559 / 100000) := by
  exact
    packedTile65536 2508880128 2509011200 14 6050 50088 31 _ _ (2164309 / 100000) (270539 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2509011200 :
    ThetaLowerSegment 2509011200 2509142272 (250893927446559 / 100000)
      (250907064832539 / 100000) := by
  exact
    packedTile65536 2509011200 2509142272 14 6070 50090 31 _ _ (1082157 / 50000) (2164317 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2509142272 :
    ThetaLowerSegment 2509142272 2509273344 (250907064832539 / 100000) (15682519809861 / 6250) := by
  exact
    packedTile65536 2509142272 2509273344 14 6123 50091 31 _ _ (2164319 / 100000) (1082161 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2509273344 :
    ThetaLowerSegment 2509273344 2509404416 (15682519809861 / 6250) (62733323020039 / 25000) := by
  exact
    packedTile65536 2509273344 2509404416 14 5995 50092 31 _ _ (541081 / 25000) (2164327 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2509404416 :
    ThetaLowerSegment 2509404416 2509535488 (62733323020039 / 25000) (125473231014103 / 50000) := by
  exact
    packedTile65536 2509404416 2509535488 14 6085 50093 31 _ _ (216433 / 10000) (2164333 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2509535488 :
    ThetaLowerSegment 2509535488 2509666560 (125473231014103 / 50000) (62739871749059 / 25000) := by
  exact
    packedTile65536 2509535488 2509666560 14 6018 50095 31 _ _ (432867 / 20000) (1082169 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2509666560 :
    ThetaLowerSegment 2509666560 2509797632 (62739871749059 / 25000) (62743122587739 / 25000) := by
  exact
    packedTile65536 2509666560 2509797632 14 6008 50096 31 _ _ (108217 / 5000) (2164343 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2509797632 :
    ThetaLowerSegment 2509797632 2509928704 (62743122587739 / 25000)
      (250985720991941 / 100000) := by
  exact
    packedTile65536 2509797632 2509928704 14 6113 50097 31 _ _ (432869 / 20000) (541087 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2509928704 :
    ThetaLowerSegment 2509928704 2510059776 (250985720991941 / 100000)
      (125499404411219 / 50000) := by
  exact
    packedTile65536 2509928704 2510059776 14 6047 50099 31 _ _ (2164351 / 100000) (1082177 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2510059776 :
    ThetaLowerSegment 2510059776 2510190848 (125499404411219 / 50000) (5020237067921 / 2000) := by
  exact
    packedTile65536 2510059776 2510190848 14 6027 50100 31 _ _ (541089 / 25000) (2164359 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2510190848 :
    ThetaLowerSegment 2510190848 2510321920 (5020237067921 / 2000) (125512476054411 / 50000) := by
  exact
    packedTile65536 2510190848 2510321920 14 6052 50101 31 _ _ (2164361 / 100000) (541091 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2510321920 :
    ThetaLowerSegment 2510321920 2510452992 (125512476054411 / 50000) (31379761496851 / 12500) := by
  exact
    packedTile65536 2510321920 2510452992 14 6071 50103 31 _ _ (1082183 / 50000) (2164369 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2510452992 :
    ThetaLowerSegment 2510452992 2510584064 (31379761496851 / 12500) (62762784700799 / 25000) := by
  exact
    packedTile65536 2510452992 2510584064 14 6028 50104 31 _ _ (2164371 / 100000) (1082187 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2510584064 :
    ThetaLowerSegment 2510584064 2510715136 (62762784700799 / 25000) (125532138285793 / 50000) := by
  exact
    packedTile65536 2510584064 2510715136 14 6070 50105 31 _ _ (2164377 / 100000) (108219 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2510715136 :
    ThetaLowerSegment 2510715136 2510846208 (125532138285793 / 50000) (31384680854507 / 12500) := by
  exact
    packedTile65536 2510715136 2510846208 14 6085 50107 31 _ _ (1082191 / 50000) (432877 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2510846208 :
    ThetaLowerSegment 2510846208 2510977280 (31384680854507 / 12500)
      (251090487267731 / 100000) := by
  exact
    packedTile65536 2510846208 2510977280 14 6025 50108 31 _ _ (2164387 / 100000) (216439 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2510977280 :
    ThetaLowerSegment 2510977280 2511108352 (251090487267731 / 100000)
      (251103819922451 / 100000) := by
  exact
    packedTile65536 2510977280 2511108352 14 6160 50109 31 _ _ (270549 / 12500) (432879 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2511108352 :
    ThetaLowerSegment 2511108352 2511239424 (251103819922451 / 100000)
      (251116923187943 / 100000) := by
  exact
    packedTile65536 2511108352 2511239424 14 6054 50110 31 _ _ (1082199 / 50000) (2164401 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2511239424 :
    ThetaLowerSegment 2511239424 2511370496 (251116923187943 / 100000)
      (31391241676797 / 12500) := by
  exact
    packedTile65536 2511239424 2511370496 14 6011 50112 31 _ _ (2164403 / 100000) (1082203 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2511370496 :
    ThetaLowerSegment 2511370496 2511501568 (31391241676797 / 12500) (15696432356123 / 6250) := by
  exact
    packedTile65536 2511370496 2511501568 14 5999 50113 31 _ _ (270551 / 12500) (2164411 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2511501568 :
    ThetaLowerSegment 2511501568 2511632640 (15696432356123 / 6250) (50231215032919 / 20000) := by
  exact
    packedTile65536 2511501568 2511632640 14 6079 50114 31 _ _ (2164413 / 100000) (67638 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2511632640 :
    ThetaLowerSegment 2511632640 2511763712 (50231215032919 / 20000) (50233842636371 / 20000) := by
  exact
    packedTile65536 2511632640 2511763712 14 6070 50116 31 _ _ (1082209 / 50000) (2164421 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2511763712 :
    ThetaLowerSegment 2511763712 2511894784 (50233842636371 / 20000)
      (251182171588343 / 100000) := by
  exact
    packedTile65536 2511763712 2511894784 14 5987 50117 31 _ _ (270553 / 12500) (2164427 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2511894784 :
    ThetaLowerSegment 2511894784 2512025856 (251182171588343 / 100000)
      (62798811725983 / 25000) := by
  exact
    packedTile65536 2511894784 2512025856 14 6041 50118 31 _ _ (2164429 / 100000) (135277 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2512025856 :
    ThetaLowerSegment 2512025856 2512156928 (62798811725983 / 25000) (125604139480523 / 50000) := by
  exact
    packedTile65536 2512025856 2512156928 14 6021 50120 31 _ _ (1082217 / 50000) (2164437 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2512156928 :
    ThetaLowerSegment 2512156928 2512288000 (125604139480523 / 50000)
      (251221492861141 / 100000) := by
  exact
    packedTile65536 2512156928 2512288000 14 6105 50121 31 _ _ (2164439 / 100000) (1082221 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2512288000 :
    ThetaLowerSegment 2512288000 2512419072 (251221492861141 / 100000)
      (251234587747341 / 100000) := by
  exact
    packedTile65536 2512288000 2512419072 14 6050 50122 31 _ _ (541111 / 25000) (2164447 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2512419072 :
    ThetaLowerSegment 2512419072 2512550144 (251234587747341 / 100000)
      (251247799550141 / 100000) := by
  exact
    packedTile65536 2512419072 2512550144 14 6104 50124 31 _ _ (43289 / 2000) (2164453 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2512550144 :
    ThetaLowerSegment 2512550144 2512681216 (251247799550141 / 100000)
      (251260790609051 / 100000) := by
  exact
    packedTile65536 2512550144 2512681216 14 6002 50125 31 _ _ (432891 / 20000) (1082229 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2512681216 :
    ThetaLowerSegment 2512681216 2512812288 (251260790609051 / 100000)
      (251274028446411 / 100000) := by
  exact
    packedTile65536 2512681216 2512812288 14 6116 50126 31 _ _ (108223 / 5000) (2164463 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2512812288 :
    ThetaLowerSegment 2512812288 2512943360 (251274028446411 / 100000)
      (251287145104311 / 100000) := by
  exact
    packedTile65536 2512812288 2512943360 14 6060 50127 31 _ _ (432893 / 20000) (541117 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2512943360 :
    ThetaLowerSegment 2512943360 2513074432 (251287145104311 / 100000)
      (251300296430107 / 100000) := by
  exact
    packedTile65536 2512943360 2513074432 14 6076 50129 31 _ _ (2164471 / 100000) (1082237 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2513074432 :
    ThetaLowerSegment 2513074432 2513205504 (251300296430107 / 100000)
      (251313521378467 / 100000) := by
  exact
    packedTile65536 2513074432 2513205504 14 6110 50130 31 _ _ (541119 / 25000) (2164479 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2513205504 :
    ThetaLowerSegment 2513205504 2513336576 (251313521378467 / 100000)
      (251326768002187 / 100000) := by
  exact
    packedTile65536 2513205504 2513336576 14 6120 50131 31 _ _ (2164481 / 100000) (541121 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2513336576 :
    ThetaLowerSegment 2513336576 2513467648 (251326768002187 / 100000)
      (251339748424729 / 100000) := by
  exact
    packedTile65536 2513336576 2513467648 14 5997 50133 31 _ _ (1082243 / 50000) (2164489 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2513467648 :
    ThetaLowerSegment 2513467648 2513598720 (251339748424729 / 100000) (7854777647519 / 3125) := by
  exact
    packedTile65536 2513467648 2513598720 14 6069 50134 31 _ _ (2164491 / 100000) (1082247 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2513598720 :
    ThetaLowerSegment 2513598720 2513729792 (7854777647519 / 3125) (25136610113929 / 10000) := by
  exact
    packedTile65536 2513598720 2513729792 14 6106 50135 31 _ _ (2164497 / 100000) (4329 / 200)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2513729792 :
    ThetaLowerSegment 2513729792 2513860864 (25136610113929 / 10000) (62844816951239 / 25000) := by
  exact
    packedTile65536 2513729792 2513860864 14 6083 50137 31 _ _ (1082251 / 50000) (432901 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2513860864 :
    ThetaLowerSegment 2513860864 2513991936 (62844816951239 / 25000) (125696198852209 / 50000) := by
  exact
    packedTile65536 2513860864 2513991936 14 6066 50138 31 _ _ (2164507 / 100000) (216451 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2513991936 :
    ThetaLowerSegment 2513991936 2514123008 (125696198852209 / 50000)
      (125702743254241 / 50000) := by
  exact
    packedTile65536 2513991936 2514123008 14 6047 50139 31 _ _ (67641 / 3125) (432903 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2514123008 :
    ThetaLowerSegment 2514123008 2514254080 (125702743254241 / 50000)
      (125709280095581 / 50000) := by
  exact
    packedTile65536 2514123008 2514254080 14 6040 50141 31 _ _ (2164517 / 100000) (54113 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2514254080 :
    ThetaLowerSegment 2514254080 2514385152 (125709280095581 / 50000)
      (251431666377927 / 100000) := by
  exact
    packedTile65536 2514254080 2514385152 14 6055 50142 31 _ _ (2164523 / 100000) (1082263 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2514385152 :
    ThetaLowerSegment 2514385152 2514516224 (251431666377927 / 100000)
      (251444895973063 / 100000) := by
  exact
    packedTile65536 2514385152 2514516224 14 6112 50143 31 _ _ (135283 / 6250) (2164531 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2514516224 :
    ThetaLowerSegment 2514516224 2514647296 (251444895973063 / 100000) (502916151629 / 200) := by
  exact
    packedTile65536 2514516224 2514647296 14 6089 50144 31 _ _ (2164533 / 100000) (270567 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2514647296 :
    ThetaLowerSegment 2514647296 2514778368 (502916151629 / 200) (15716951992279 / 6250) := by
  exact
    packedTile65536 2514647296 2514778368 14 6078 50146 31 _ _ (1082269 / 50000) (2164541 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2514778368 :
    ThetaLowerSegment 2514778368 2514909440 (15716951992279 / 6250) (125742184247 / 50) := by
  exact
    packedTile65536 2514778368 2514909440 14 6069 50147 31 _ _ (67642 / 3125) (2164547 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2514909440 :
    ThetaLowerSegment 2514909440 2515040512 (125742184247 / 50) (62874341111549 / 25000) := by
  exact
    packedTile65536 2514909440 2515040512 14 6004 50148 31 _ _ (2164549 / 100000) (270569 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2515040512 :
    ThetaLowerSegment 2515040512 2515171584 (62874341111549 / 25000) (125755309005169 / 50000) := by
  exact
    packedTile65536 2515040512 2515171584 14 6123 50150 31 _ _ (1082277 / 50000) (2164557 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2515171584 :
    ThetaLowerSegment 2515171584 2515302656 (125755309005169 / 50000) (31440457705359 / 12500) := by
  exact
    packedTile65536 2515171584 2515302656 14 6026 50151 31 _ _ (2164559 / 100000) (1082281 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2515302656 :
    ThetaLowerSegment 2515302656 2515433728 (31440457705359 / 12500) (62884196348601 / 25000) := by
  exact
    packedTile65536 2515302656 2515433728 14 6063 50152 31 _ _ (541141 / 25000) (2164567 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2515433728 :
    ThetaLowerSegment 2515433728 2515564800 (62884196348601 / 25000) (125774902641477 / 50000) := by
  exact
    packedTile65536 2515433728 2515564800 14 6015 50154 31 _ _ (216457 / 10000) (2164573 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2515564800 :
    ThetaLowerSegment 2515564800 2515695872 (125774902641477 / 50000)
      (251562920442879 / 100000) := by
  exact
    packedTile65536 2515564800 2515695872 14 6059 50155 31 _ _ (86583 / 4000) (1082289 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2515695872 :
    ThetaLowerSegment 2515695872 2515826944 (251562920442879 / 100000)
      (251576031303939 / 100000) := by
  exact
    packedTile65536 2515695872 2515826944 14 6057 50156 31 _ _ (108229 / 5000) (2164583 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2515826944 :
    ThetaLowerSegment 2515826944 2515958016 (251576031303939 / 100000)
      (31448635198363 / 12500) := by
  exact
    packedTile65536 2515826944 2515958016 14 6029 50158 31 _ _ (432917 / 20000) (541147 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2515958016 :
    ThetaLowerSegment 2515958016 2516089088 (31448635198363 / 12500) (125801126558527 / 50000) := by
  exact
    packedTile65536 2515958016 2516089088 14 6085 50159 31 _ _ (216459 / 10000) (2164593 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2516089088 :
    ThetaLowerSegment 2516089088 2516220160 (125801126558527 / 50000)
      (125807727494029 / 50000) := by
  exact
    packedTile65536 2516089088 2516220160 14 6099 50160 31 _ _ (541149 / 25000) (2164599 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2516220160 :
    ThetaLowerSegment 2516220160 2516351232 (125807727494029 / 50000)
      (251628475063073 / 100000) := by
  exact
    packedTile65536 2516220160 2516351232 14 6015 50161 31 _ _ (2164601 / 100000) (541151 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2516351232 :
    ThetaLowerSegment 2516351232 2516482304 (251628475063073 / 100000)
      (50328319380929 / 20000) := by
  exact
    packedTile65536 2516351232 2516482304 14 6062 50163 31 _ _ (1082303 / 50000) (2164609 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2516482304 :
    ThetaLowerSegment 2516482304 2516613376 (50328319380929 / 20000) (10066181651137 / 4000) := by
  exact
    packedTile65536 2516482304 2516613376 14 5980 50164 31 _ _ (2164611 / 100000) (1082307 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2516613376 :
    ThetaLowerSegment 2516613376 2516744448 (10066181651137 / 4000) (50333503630269 / 20000) := by
  exact
    packedTile65536 2516613376 2516744448 14 5995 50165 31 _ _ (270577 / 12500) (2164619 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2516744448 :
    ThetaLowerSegment 2516744448 2516875520 (50333503630269 / 20000)
      (251680694205459 / 100000) := by
  exact
    packedTile65536 2516744448 2516875520 14 6087 50167 31 _ _ (1082311 / 50000) (17317 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2516875520 :
    ThetaLowerSegment 2516875520 2517006592 (251680694205459 / 100000)
      (62923461078621 / 25000) := by
  exact
    packedTile65536 2516875520 2517006592 14 6075 50168 31 _ _ (2164627 / 100000) (216463 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2517006592 :
    ThetaLowerSegment 2517006592 2517137664 (62923461078621 / 25000) (62926764848211 / 25000) := by
  exact
    packedTile65536 2517006592 2517137664 14 6105 50169 31 _ _ (270579 / 12500) (432927 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2517137664 :
    ThetaLowerSegment 2517137664 2517268736 (62926764848211 / 25000)
      (251720109989317 / 100000) := by
  exact
    packedTile65536 2517137664 2517268736 14 6029 50171 31 _ _ (2164637 / 100000) (13529 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2517268736 :
    ThetaLowerSegment 2517268736 2517399808 (251720109989317 / 100000)
      (251733145469463 / 100000) := by
  exact
    packedTile65536 2517268736 2517399808 14 6022 50172 31 _ _ (2164643 / 100000) (1082323 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2517399808 :
    ThetaLowerSegment 2517399808 2517530880 (251733145469463 / 100000)
      (251746256742399 / 100000) := by
  exact
    packedTile65536 2517399808 2517530880 14 6057 50173 31 _ _ (270581 / 12500) (2164651 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2517530880 :
    ThetaLowerSegment 2517530880 2517661952 (251746256742399 / 100000)
      (62939872316547 / 25000) := by
  exact
    packedTile65536 2517530880 2517661952 14 6113 50175 31 _ _ (2164653 / 100000) (135291 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2517661952 :
    ThetaLowerSegment 2517661952 2517793024 (62939872316547 / 25000) (25177262657559 / 10000) := by
  exact
    packedTile65536 2517661952 2517793024 14 6069 50176 31 _ _ (1082329 / 50000) (2164661 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2517793024 :
    ThetaLowerSegment 2517793024 2517924096 (25177262657559 / 10000) (125892928497923 / 50000) := by
  exact
    packedTile65536 2517793024 2517924096 14 6112 50177 31 _ _ (2164663 / 100000) (1082333 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2517924096 :
    ThetaLowerSegment 2517924096 2518055168 (125892928497923 / 50000)
      (251798929431937 / 100000) := by
  exact
    packedTile65536 2517924096 2518055168 14 6039 50178 31 _ _ (2164669 / 100000) (67646 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2518055168 :
    ThetaLowerSegment 2518055168 2518186240 (251798929431937 / 100000)
      (251812047356377 / 100000) := by
  exact
    packedTile65536 2518055168 2518186240 14 6060 50180 31 _ _ (1082337 / 50000) (2164677 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2518186240 :
    ThetaLowerSegment 2518186240 2518317312 (251812047356377 / 100000)
      (125912629196157 / 50000) := by
  exact
    packedTile65536 2518186240 2518317312 14 6103 50181 31 _ _ (2164679 / 100000) (1082341 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2518317312 :
    ThetaLowerSegment 2518317312 2518448384 (125912629196157 / 50000)
      (125919226070647 / 50000) := by
  exact
    packedTile65536 2518317312 2518448384 14 6095 50182 31 _ _ (541171 / 25000) (2164687 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2518448384 :
    ThetaLowerSegment 2518448384 2518579456 (125919226070647 / 50000) (12592573529047 / 5000) := by
  exact
    packedTile65536 2518448384 2518579456 14 6014 50184 31 _ _ (2164689 / 100000) (541173 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2518579456 :
    ThetaLowerSegment 2518579456 2518710528 (12592573529047 / 5000) (50372906903053 / 20000) := by
  exact
    packedTile65536 2518579456 2518710528 14 6035 50185 31 _ _ (432939 / 20000) (1082349 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2518710528 :
    ThetaLowerSegment 2518710528 2518841600 (50372906903053 / 20000) (50375511903033 / 20000) := by
  exact
    packedTile65536 2518710528 2518841600 14 6017 50186 31 _ _ (21647 / 1000) (2164703 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2518841600 :
    ThetaLowerSegment 2518841600 2518972672 (50375511903033 / 20000) (25189060186279 / 10000) := by
  exact
    packedTile65536 2518841600 2518972672 14 6025 50188 31 _ _ (432941 / 20000) (541177 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2518972672 :
    ThetaLowerSegment 2518972672 2519103744 (25189060186279 / 10000) (25190375031133 / 10000) := by
  exact
    packedTile65536 2518972672 2519103744 14 6074 50189 31 _ _ (216471 / 10000) (2164713 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2519103744 :
    ThetaLowerSegment 2519103744 2519234816 (25190375031133 / 10000) (6297921170927 / 2500) := by
  exact
    packedTile65536 2519103744 2519234816 14 6050 50190 31 _ _ (432943 / 20000) (1082359 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2519234816 :
    ThetaLowerSegment 2519234816 2519365888 (6297921170927 / 2500) (251930097094321 / 100000) := by
  exact
    packedTile65536 2519234816 2519365888 14 6121 50191 31 _ _ (2164721 / 100000) (541181 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2519365888 :
    ThetaLowerSegment 2519365888 2519496960 (251930097094321 / 100000)
      (50388633974927 / 20000) := by
  exact
    packedTile65536 2519365888 2519496960 14 6039 50193 31 _ _ (1082363 / 50000) (2164729 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2519496960 :
    ThetaLowerSegment 2519496960 2519628032 (50388633974927 / 20000)
      (251956249179337 / 100000) := by
  exact
    packedTile65536 2519496960 2519628032 14 6042 50194 31 _ _ (2164731 / 100000) (1082367 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2519628032 :
    ThetaLowerSegment 2519628032 2519759104 (251956249179337 / 100000)
      (251969313361097 / 100000) := by
  exact
    packedTile65536 2519628032 2519759104 14 6035 50195 31 _ _ (67648 / 3125) (2164739 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2519759104 :
    ThetaLowerSegment 2519759104 2519890176 (251969313361097 / 100000)
      (251982327783989 / 100000) := by
  exact
    packedTile65536 2519759104 2519890176 14 6012 50197 31 _ _ (2164741 / 100000) (270593 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2519890176 :
    ThetaLowerSegment 2519890176 2520021248 (251982327783989 / 100000)
      (50399105682239 / 20000) := by
  exact
    packedTile65536 2519890176 2520021248 14 6098 50198 31 _ _ (2164747 / 100000) (8659 / 400)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2520021248 :
    ThetaLowerSegment 2520021248 2520152320 (50399105682239 / 20000)
      (252008575371499 / 100000) := by
  exact
    packedTile65536 2520021248 2520152320 14 6027 50199 31 _ _ (135297 / 6250) (432951 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2520152320 :
    ThetaLowerSegment 2520152320 2520283392 (252008575371499 / 100000) (5040433139961 / 2000) := by
  exact
    packedTile65536 2520152320 2520283392 14 6043 50201 31 _ _ (2164757 / 100000) (54119 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2520283392 :
    ThetaLowerSegment 2520283392 2520414464 (5040433139961 / 2000) (2520349161653 / 1000) := by
  exact
    packedTile65536 2520283392 2520414464 14 6125 50202 31 _ _ (1082381 / 50000) (432953 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2520414464 :
    ThetaLowerSegment 2520414464 2520545536 (2520349161653 / 1000) (25204805630099 / 10000) := by
  exact
    packedTile65536 2520414464 2520545536 14 6070 50203 31 _ _ (2164767 / 100000) (216477 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2520545536 :
    ThetaLowerSegment 2520545536 2520676608 (25204805630099 / 10000)
      (252061094728769 / 100000) := by
  exact
    packedTile65536 2520545536 2520676608 14 6023 50205 31 _ _ (2164773 / 100000) (270597 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2520676608 :
    ThetaLowerSegment 2520676608 2520807680 (252061094728769 / 100000)
      (252074083396769 / 100000) := by
  exact
    packedTile65536 2520676608 2520807680 14 6000 50206 31 _ _ (1082389 / 50000) (2164781 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2520807680 :
    ThetaLowerSegment 2520807680 2520938752 (252074083396769 / 100000)
      (50417462910093 / 20000) := by
  exact
    packedTile65536 2520807680 2520938752 14 6112 50207 31 _ _ (2164783 / 100000) (1082393 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2520938752 :
    ThetaLowerSegment 2520938752 2521069824 (50417462910093 / 20000)
      (252100461307989 / 100000) := by
  exact
    packedTile65536 2520938752 2521069824 14 6073 50208 31 _ _ (541197 / 25000) (2164791 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2521069824 :
    ThetaLowerSegment 2521069824 2521200896 (252100461307989 / 100000)
      (126056730444977 / 50000) := by
  exact
    packedTile65536 2521069824 2521200896 14 6005 50210 31 _ _ (2164793 / 100000) (541199 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2521200896 :
    ThetaLowerSegment 2521200896 2521331968 (126056730444977 / 50000)
      (252126352267999 / 100000) := by
  exact
    packedTile65536 2521200896 2521331968 14 5955 50211 31 _ _ (2164799 / 100000) (1082401 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2521331968 :
    ThetaLowerSegment 2521331968 2521463040 (252126352267999 / 100000)
      (50427924070343 / 20000) := by
  exact
    packedTile65536 2521331968 2521463040 14 6129 50212 31 _ _ (541201 / 25000) (2164807 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2521463040 :
    ThetaLowerSegment 2521463040 2521594112 (50427924070343 / 20000) (7879773705548 / 3125) := by
  exact
    packedTile65536 2521463040 2521594112 14 6069 50214 31 _ _ (2164809 / 100000) (541203 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2521594112 :
    ThetaLowerSegment 2521594112 2521725184 (7879773705548 / 3125) (126082933263153 / 50000) := by
  exact
    packedTile65536 2521594112 2521725184 14 6055 50215 31 _ _ (1082407 / 50000) (2164817 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2521725184 :
    ThetaLowerSegment 2521725184 2521856256 (126082933263153 / 50000) (63044751744409 / 25000) := by
  exact
    packedTile65536 2521725184 2521856256 14 6070 50216 31 _ _ (2164819 / 100000) (1082411 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2521856256 :
    ThetaLowerSegment 2521856256 2521987328 (63044751744409 / 25000) (126096086721643 / 50000) := by
  exact
    packedTile65536 2521856256 2521987328 14 6082 50218 31 _ _ (86593 / 4000) (541207 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2521987328 :
    ThetaLowerSegment 2521987328 2522118400 (126096086721643 / 50000) (63051349597439 / 25000) := by
  exact
    packedTile65536 2521987328 2522118400 14 6109 50219 31 _ _ (216483 / 10000) (2164833 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2522118400 :
    ThetaLowerSegment 2522118400 2522249472 (63051349597439 / 25000)
      (252218541103041 / 100000) := by
  exact
    packedTile65536 2522118400 2522249472 14 6071 50220 31 _ _ (432967 / 20000) (1082419 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2522249472 :
    ThetaLowerSegment 2522249472 2522380544 (252218541103041 / 100000)
      (252231666527961 / 100000) := by
  exact
    packedTile65536 2522249472 2522380544 14 6063 50222 31 _ _ (54121 / 2500) (2164843 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2522380544 :
    ThetaLowerSegment 2522380544 2522511616 (252231666527961 / 100000)
      (252244724873001 / 100000) := by
  exact
    packedTile65536 2522380544 2522511616 14 6032 50223 31 _ _ (432969 / 20000) (135303 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2522511616 :
    ThetaLowerSegment 2522511616 2522642688 (252244724873001 / 100000)
      (126128821269459 / 50000) := by
  exact
    packedTile65536 2522511616 2522642688 14 5967 50224 31 _ _ (2164851 / 100000) (1082427 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2522642688 :
    ThetaLowerSegment 2522642688 2522773760 (126128821269459 / 50000)
      (126135429492399 / 50000) := by
  exact
    packedTile65536 2522642688 2522773760 14 6105 50225 31 _ _ (270607 / 12500) (2164859 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2522773760 :
    ThetaLowerSegment 2522773760 2522904832 (126135429492399 / 50000) (31535498878953 / 12500) := by
  exact
    packedTile65536 2522773760 2522904832 14 6066 50227 31 _ _ (2164861 / 100000) (67652 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2522904832 :
    ThetaLowerSegment 2522904832 2523035904 (31535498878953 / 12500) (15768561805443 / 6250) := by
  exact
    packedTile65536 2522904832 2523035904 14 6004 50228 31 _ _ (1082433 / 50000) (2164869 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2523035904 :
    ThetaLowerSegment 2523035904 2523166976 (15768561805443 / 6250) (252309962958991 / 100000) := by
  exact
    packedTile65536 2523035904 2523166976 14 5993 50229 31 _ _ (2164871 / 100000) (1082437 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2523166976 :
    ThetaLowerSegment 2523166976 2523298048 (252309962958991 / 100000)
      (126161535644613 / 50000) := by
  exact
    packedTile65536 2523166976 2523298048 14 6055 50231 31 _ _ (2164877 / 100000) (27061 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2523298048 :
    ThetaLowerSegment 2523298048 2523429120 (126161535644613 / 50000) (63084048159757 / 25000) := by
  exact
    packedTile65536 2523298048 2523429120 14 6061 50232 31 _ _ (1082441 / 50000) (432977 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2523429120 :
    ThetaLowerSegment 2523429120 2523560192 (63084048159757 / 25000) (50469867133601 / 20000) := by
  exact
    packedTile65536 2523429120 2523560192 14 6071 50233 31 _ _ (2164887 / 100000) (216489 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2523560192 :
    ThetaLowerSegment 2523560192 2523691264 (50469867133601 / 20000)
      (252362504706041 / 100000) := by
  exact
    packedTile65536 2523560192 2523691264 14 6083 50235 31 _ _ (541223 / 25000) (432979 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2523691264 :
    ThetaLowerSegment 2523691264 2523822336 (252362504706041 / 100000)
      (252375589343509 / 100000) := by
  exact
    packedTile65536 2523691264 2523822336 14 6044 50236 31 _ _ (2164897 / 100000) (21649 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2523822336 :
    ThetaLowerSegment 2523822336 2523953408 (252375589343509 / 100000)
      (252388708655689 / 100000) := by
  exact
    packedTile65536 2523822336 2523953408 14 6060 50237 31 _ _ (2164903 / 100000) (1082453 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2523953408 :
    ThetaLowerSegment 2523953408 2524084480 (252388708655689 / 100000)
      (50480398939217 / 20000) := by
  exact
    packedTile65536 2523953408 2524084480 14 6137 50238 31 _ _ (541227 / 25000) (2164911 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2524084480 :
    ThetaLowerSegment 2524084480 2524215552 (50480398939217 / 20000) (126207449871239 / 50000) := by
  exact
    packedTile65536 2524084480 2524215552 14 5961 50240 31 _ _ (2164913 / 100000) (541229 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2524215552 :
    ThetaLowerSegment 2524215552 2524346624 (126207449871239 / 50000)
      (126214000913107 / 50000) := by
  exact
    packedTile65536 2524215552 2524346624 14 6052 50241 31 _ _ (1082459 / 50000) (2164921 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2524346624 :
    ThetaLowerSegment 2524346624 2524477696 (126214000913107 / 50000)
      (126220538980567 / 50000) := by
  exact
    packedTile65536 2524346624 2524477696 14 6040 50242 31 _ _ (2164923 / 100000) (1082463 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2524477696 :
    ThetaLowerSegment 2524477696 2524608768 (126220538980567 / 50000)
      (252454208255519 / 100000) := by
  exact
    packedTile65536 2524477696 2524608768 14 6065 50244 31 _ _ (2164929 / 100000) (541233 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2524608768 :
    ThetaLowerSegment 2524608768 2524739840 (252454208255519 / 100000)
      (252467243323133 / 100000) := by
  exact
    packedTile65536 2524608768 2524739840 14 6021 50245 31 _ _ (1082467 / 50000) (2164937 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2524739840 :
    ThetaLowerSegment 2524739840 2524870912 (252467243323133 / 100000)
      (126240167354633 / 50000) := by
  exact
    packedTile65536 2524739840 2524870912 14 6047 50246 31 _ _ (2164939 / 100000) (1082471 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2524870912 :
    ThetaLowerSegment 2524870912 2525001984 (126240167354633 / 50000)
      (126246682753601 / 50000) := by
  exact
    packedTile65536 2524870912 2525001984 14 6019 50248 31 _ _ (135309 / 6250) (2164947 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2525001984 :
    ThetaLowerSegment 2525001984 2525133056 (126246682753601 / 50000) (63126585552877 / 25000) := by
  exact
    packedTile65536 2525001984 2525133056 14 5994 50249 31 _ _ (2164949 / 100000) (270619 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2525133056 :
    ThetaLowerSegment 2525133056 2525264128 (63126585552877 / 25000) (12625967462757 / 5000) := by
  exact
    packedTile65536 2525133056 2525264128 14 6008 50250 31 _ _ (1082477 / 50000) (2164957 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2525264128 :
    ThetaLowerSegment 2525264128 2525395200 (12625967462757 / 5000) (12626626584829 / 5000) := by
  exact
    packedTile65536 2525264128 2525395200 14 6089 50252 31 _ _ (13531 / 625) (2164963 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2525395200 :
    ThetaLowerSegment 2525395200 2525526272 (12626626584829 / 5000) (50509117720099 / 20000) := by
  exact
    packedTile65536 2525395200 2525526272 14 6031 50253 31 _ _ (432993 / 20000) (270621 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2525526272 :
    ThetaLowerSegment 2525526272 2525657344 (50509117720099 / 20000) (50511773272301 / 20000) := by
  exact
    packedTile65536 2525526272 2525657344 14 6133 50254 31 _ _ (216497 / 10000) (2164973 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2525657344 :
    ThetaLowerSegment 2525657344 2525788416 (50511773272301 / 20000) (12628602011719 / 5000) := by
  exact
    packedTile65536 2525657344 2525788416 14 6085 50255 31 _ _ (86599 / 4000) (1082489 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2525788416 :
    ThetaLowerSegment 2525788416 2525919488 (12628602011719 / 5000) (12629246309767 / 5000) := by
  exact
    packedTile65536 2525788416 2525919488 14 5952 50257 31 _ _ (108249 / 5000) (2164983 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2525919488 :
    ThetaLowerSegment 2525919488 2526050560 (12629246309767 / 5000) (7893690426256 / 3125) := by
  exact
    packedTile65536 2525919488 2526050560 14 6082 50258 31 _ _ (1082493 / 50000) (2164989 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2526050560 :
    ThetaLowerSegment 2526050560 2526181632 (7893690426256 / 3125) (252611072761237 / 100000) := by
  exact
    packedTile65536 2526050560 2526181632 14 5995 50259 31 _ _ (2164991 / 100000) (1082497 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2526181632 :
    ThetaLowerSegment 2526181632 2526312704 (252611072761237 / 100000)
      (252624270576853 / 100000) := by
  exact
    packedTile65536 2526181632 2526312704 14 6096 50261 31 _ _ (541249 / 25000) (2164999 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2526312704 :
    ThetaLowerSegment 2526312704 2526443776 (252624270576853 / 100000)
      (252637468422949 / 100000) := by
  exact
    packedTile65536 2526312704 2526443776 14 6096 50262 31 _ _ (2165001 / 100000) (541251 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2526443776 :
    ThetaLowerSegment 2526443776 2526574848 (252637468422949 / 100000)
      (252650549389201 / 100000) := by
  exact
    packedTile65536 2526443776 2526574848 14 6042 50263 31 _ _ (1082503 / 50000) (2165009 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2526574848 :
    ThetaLowerSegment 2526574848 2526705920 (252650549389201 / 100000)
      (252663675856957 / 100000) := by
  exact
    packedTile65536 2526574848 2526705920 14 6063 50265 31 _ _ (541253 / 25000) (433003 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2526705920 :
    ThetaLowerSegment 2526705920 2526836992 (252663675856957 / 100000)
      (252677055662017 / 100000) := by
  exact
    packedTile65536 2526705920 2526836992 14 6180 50266 31 _ _ (2165017 / 100000) (108251 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2526836992 :
    ThetaLowerSegment 2526836992 2526968064 (252677055662017 / 100000)
      (252690190850491 / 100000) := by
  exact
    packedTile65536 2526836992 2526968064 14 6067 50267 31 _ _ (1082511 / 50000) (86601 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2526968064 :
    ThetaLowerSegment 2526968064 2527099136 (252690190850491 / 100000)
      (63175801206947 / 25000) := by
  exact
    packedTile65536 2526968064 2527099136 14 6011 50268 31 _ _ (2165027 / 100000) (216503 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2527099136 :
    ThetaLowerSegment 2527099136 2527230208 (63175801206947 / 25000) (63179067698977 / 25000) := by
  exact
    packedTile65536 2527099136 2527230208 14 6035 50270 31 _ _ (270629 / 12500) (433007 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2527230208 :
    ThetaLowerSegment 2527230208 2527361280 (63179067698977 / 25000)
      (252729245862649 / 100000) := by
  exact
    packedTile65536 2527230208 2527361280 14 5993 50271 31 _ _ (2165037 / 100000) (27063 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2527361280 :
    ThetaLowerSegment 2527361280 2527492352 (252729245862649 / 100000)
      (63185594212111 / 25000) := by
  exact
    packedTile65536 2527361280 2527492352 14 6065 50272 31 _ _ (2165043 / 100000) (1082523 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2527492352 :
    ThetaLowerSegment 2527492352 2527623424 (63185594212111 / 25000) (63188900781669 / 25000) := by
  exact
    packedTile65536 2527492352 2527623424 14 6109 50274 31 _ _ (270631 / 12500) (2165051 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2527623424 :
    ThetaLowerSegment 2527623424 2527754496 (63188900781669 / 25000)
      (252768907377361 / 100000) := by
  exact
    packedTile65536 2527623424 2527754496 14 6145 50275 31 _ _ (2165053 / 100000) (67658 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2527754496 :
    ThetaLowerSegment 2527754496 2527885568 (252768907377361 / 100000)
      (252782005978261 / 100000) := by
  exact
    packedTile65536 2527754496 2527885568 14 6050 50276 31 _ _ (1082529 / 50000) (2165061 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2527885568 :
    ThetaLowerSegment 2527885568 2528016640 (252782005978261 / 100000)
      (252795221522813 / 100000) := by
  exact
    packedTile65536 2527885568 2528016640 14 6104 50278 31 _ _ (2165063 / 100000) (1082533 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2528016640 :
    ThetaLowerSegment 2528016640 2528147712 (252795221522813 / 100000) (7900256555367 / 3125) := by
  exact
    packedTile65536 2528016640 2528147712 14 5999 50279 31 _ _ (2165069 / 100000) (135317 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2528147712 :
    ThetaLowerSegment 2528147712 2528278784 (7900256555367 / 3125) (31602677090393 / 12500) := by
  exact
    packedTile65536 2528147712 2528278784 14 6100 50280 31 _ _ (1082537 / 50000) (2165077 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2528278784 :
    ThetaLowerSegment 2528278784 2528409856 (31602677090393 / 12500) (126417314017601 / 50000) := by
  exact
    packedTile65536 2528278784 2528409856 14 6102 50281 31 _ _ (2165079 / 100000) (1082541 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2528409856 :
    ThetaLowerSegment 2528409856 2528540928 (126417314017601 / 50000)
      (126423844993487 / 50000) := by
  exact
    packedTile65536 2528409856 2528540928 14 6033 50283 31 _ _ (541271 / 25000) (2165087 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2528540928 :
    ThetaLowerSegment 2528540928 2528672000 (126423844993487 / 50000)
      (252860717327487 / 100000) := by
  exact
    packedTile65536 2528540928 2528672000 14 6017 50284 31 _ _ (2165089 / 100000) (541273 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2528672000 :
    ThetaLowerSegment 2528672000 2528803072 (252860717327487 / 100000)
      (126436932974711 / 50000) := by
  exact
    packedTile65536 2528672000 2528803072 14 6073 50285 31 _ _ (433019 / 20000) (1082549 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2528803072 :
    ThetaLowerSegment 2528803072 2528934144 (126436932974711 / 50000)
      (126443456421011 / 50000) := by
  exact
    packedTile65536 2528803072 2528934144 14 6026 50287 31 _ _ (21651 / 1000) (2165103 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2528934144 :
    ThetaLowerSegment 2528934144 2529065216 (126443456421011 / 50000)
      (126450055661051 / 50000) := by
  exact
    packedTile65536 2528934144 2529065216 14 6096 50288 31 _ _ (433021 / 20000) (541277 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2529065216 :
    ThetaLowerSegment 2529065216 2529196288 (126450055661051 / 50000) (15807076316447 / 6250) := by
  exact
    packedTile65536 2529065216 2529196288 14 6055 50289 31 _ _ (216511 / 10000) (2165113 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2529196288 :
    ThetaLowerSegment 2529196288 2529327360 (15807076316447 / 6250) (126463125362611 / 50000) := by
  exact
    packedTile65536 2529196288 2529327360 14 6018 50291 31 _ _ (433023 / 20000) (1082559 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2529327360 :
    ThetaLowerSegment 2529327360 2529458432 (126463125362611 / 50000)
      (126469710575091 / 50000) := by
  exact
    packedTile65536 2529327360 2529458432 14 6083 50292 31 _ _ (13532 / 625) (2165123 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2529458432 :
    ThetaLowerSegment 2529458432 2529589504 (126469710575091 / 50000) (25295247252971 / 10000) := by
  exact
    packedTile65536 2529458432 2529589504 14 6028 50293 31 _ _ (1082563 / 50000) (2165129 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2529589504 :
    ThetaLowerSegment 2529589504 2529720576 (25295247252971 / 10000)
      (252965638691321 / 100000) := by
  exact
    packedTile65536 2529589504 2529720576 14 6081 50295 31 _ _ (2165131 / 100000) (1082567 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2529720576 :
    ThetaLowerSegment 2529720576 2529851648 (252965638691321 / 100000)
      (252978737764121 / 100000) := by
  exact
    packedTile65536 2529720576 2529851648 14 6050 50296 31 _ _ (135321 / 6250) (2165139 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2529851648 :
    ThetaLowerSegment 2529851648 2529982720 (252978737764121 / 100000) (2023935457067 / 800) := by
  exact
    packedTile65536 2529851648 2529982720 14 6094 50297 31 _ _ (2165141 / 100000) (270643 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2529982720 :
    ThetaLowerSegment 2529982720 2530113792 (2023935457067 / 800) (253005011780361 / 100000) := by
  exact
    packedTile65536 2529982720 2530113792 14 6041 50298 31 _ _ (1082573 / 50000) (2165149 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2530113792 :
    ThetaLowerSegment 2530113792 2530244864 (253005011780361 / 100000)
      (253018173739369 / 100000) := by
  exact
    packedTile65536 2530113792 2530244864 14 6079 50300 31 _ _ (67661 / 3125) (433031 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2530244864 :
    ThetaLowerSegment 2530244864 2530375936 (253018173739369 / 100000) (15814457941759 / 6250) := by
  exact
    packedTile65536 2530244864 2530375936 14 6075 50301 31 _ _ (2165157 / 100000) (54129 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2530375936 :
    ThetaLowerSegment 2530375936 2530507008 (15814457941759 / 6250) (63261058940997 / 25000) := by
  exact
    packedTile65536 2530375936 2530507008 14 5962 50302 31 _ _ (1082581 / 50000) (433033 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2530507008 :
    ThetaLowerSegment 2530507008 2530638080 (63261058940997 / 25000) (126528637199831 / 50000) := by
  exact
    packedTile65536 2530507008 2530638080 14 6022 50304 31 _ _ (2165167 / 100000) (216517 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2530638080 :
    ThetaLowerSegment 2530638080 2530769152 (126528637199831 / 50000)
      (126535125137729 / 50000) := by
  exact
    packedTile65536 2530638080 2530769152 14 5993 50305 31 _ _ (541293 / 25000) (86607 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2530769152 :
    ThetaLowerSegment 2530769152 2530900224 (126535125137729 / 50000) (50616653030881 / 20000) := by
  exact
    packedTile65536 2530769152 2530900224 14 6011 50306 31 _ _ (2165177 / 100000) (108259 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2530900224 :
    ThetaLowerSegment 2530900224 2531031296 (50616653030881 / 20000) (5061930104969 / 2000) := by
  exact
    packedTile65536 2530900224 2531031296 14 6115 50308 31 _ _ (2165183 / 100000) (1082593 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2531031296 :
    ThetaLowerSegment 2531031296 2531162368 (5061930104969 / 2000) (126554896503603 / 50000) := by
  exact
    packedTile65536 2531031296 2531162368 14 6137 50309 31 _ _ (541297 / 25000) (2165191 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2531162368 :
    ThetaLowerSegment 2531162368 2531293440 (126554896503603 / 50000)
      (126561513333411 / 50000) := by
  exact
    packedTile65536 2531162368 2531293440 14 6112 50310 31 _ _ (2165193 / 100000) (541299 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2531293440 :
    ThetaLowerSegment 2531293440 2531424512 (126561513333411 / 50000) (25313605249799 / 10000) := by
  exact
    packedTile65536 2531293440 2531424512 14 6016 50311 31 _ _ (1082599 / 50000) (2165201 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2531424512 :
    ThetaLowerSegment 2531424512 2531555584 (25313605249799 / 10000)
      (253149037220381 / 100000) := by
  exact
    packedTile65536 2531424512 2531555584 14 5997 50313 31 _ _ (2165203 / 100000) (1082603 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2531555584 :
    ThetaLowerSegment 2531555584 2531686656 (253149037220381 / 100000)
      (253162351084373 / 100000) := by
  exact
    packedTile65536 2531555584 2531686656 14 6149 50314 31 _ _ (270651 / 12500) (2165211 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2531686656 :
    ThetaLowerSegment 2531686656 2531817728 (253162351084373 / 100000)
      (253175444133431 / 100000) := by
  exact
    packedTile65536 2531686656 2531817728 14 6047 50315 31 _ _ (1082607 / 50000) (2165217 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2531817728 :
    ThetaLowerSegment 2531817728 2531948800 (253175444133431 / 100000)
      (63297121311867 / 25000) := by
  exact
    packedTile65536 2531817728 2531948800 14 6023 50317 31 _ _ (2165219 / 100000) (1082611 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2531948800 :
    ThetaLowerSegment 2531948800 2532079872 (63297121311867 / 25000) (63300444930707 / 25000) := by
  exact
    packedTile65536 2531948800 2532079872 14 6140 50318 31 _ _ (270653 / 12500) (2165227 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2532079872 :
    ThetaLowerSegment 2532079872 2532210944 (63300444930707 / 25000) (126607431018223 / 50000) := by
  exact
    packedTile65536 2532079872 2532210944 14 6042 50319 31 _ _ (2165229 / 100000) (135327 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2532210944 :
    ThetaLowerSegment 2532210944 2532342016 (126607431018223 / 50000) (25322784477951 / 10000) := by
  exact
    packedTile65536 2532210944 2532342016 14 5996 50321 31 _ _ (1082617 / 50000) (2165237 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2532342016 :
    ThetaLowerSegment 2532342016 2532473088 (25322784477951 / 10000) (25324087735907 / 10000) := by
  exact
    packedTile65536 2532342016 2532473088 14 6019 50322 31 _ _ (54131 / 2500) (2165243 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2532473088 :
    ThetaLowerSegment 2532473088 2532604160 (25324087735907 / 10000) (25325415464141 / 10000) := by
  exact
    packedTile65536 2532473088 2532604160 14 6132 50323 31 _ _ (433049 / 20000) (67664 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2532604160 :
    ThetaLowerSegment 2532604160 2532735232 (25325415464141 / 10000) (25326735833591 / 10000) := by
  exact
    packedTile65536 2532604160 2532735232 14 6098 50324 31 _ _ (8661 / 400) (2165253 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2532735232 :
    ThetaLowerSegment 2532735232 2532866304 (25326735833591 / 10000) (12664022040331 / 5000) := by
  exact
    packedTile65536 2532735232 2532866304 14 6042 50326 31 _ _ (433051 / 20000) (1082629 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2532866304 :
    ThetaLowerSegment 2532866304 2532997376 (12664022040331 / 5000) (6332340626869 / 2500) := by
  exact
    packedTile65536 2532866304 2532997376 14 6089 50327 31 _ _ (108263 / 5000) (2165263 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2532997376 :
    ThetaLowerSegment 2532997376 2533128448 (6332340626869 / 2500) (50661381795107 / 20000) := by
  exact
    packedTile65536 2532997376 2533128448 14 6135 50328 31 _ _ (433053 / 20000) (541317 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2533128448 :
    ThetaLowerSegment 2533128448 2533259520 (50661381795107 / 20000)
      (253320013195627 / 100000) := by
  exact
    packedTile65536 2533128448 2533259520 14 6052 50330 31 _ _ (2165271 / 100000) (1082637 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2533259520 :
    ThetaLowerSegment 2533259520 2533390592 (253320013195627 / 100000)
      (253333307990267 / 100000) := by
  exact
    packedTile65536 2533259520 2533390592 14 6140 50331 31 _ _ (541319 / 25000) (2165279 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2533390592 :
    ThetaLowerSegment 2533390592 2533521664 (253333307990267 / 100000)
      (253346429593127 / 100000) := by
  exact
    packedTile65536 2533390592 2533521664 14 6060 50332 31 _ _ (2165281 / 100000) (541321 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2533521664 :
    ThetaLowerSegment 2533521664 2533652736 (253346429593127 / 100000)
      (253359473275991 / 100000) := by
  exact
    packedTile65536 2533521664 2533652736 14 6024 50334 31 _ _ (1082643 / 50000) (2165289 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2533652736 :
    ThetaLowerSegment 2533652736 2533783808 (253359473275991 / 100000)
      (63343133036503 / 25000) := by
  exact
    packedTile65536 2533652736 2533783808 14 6031 50335 31 _ _ (2165291 / 100000) (1082647 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2533783808 :
    ThetaLowerSegment 2533783808 2533914880 (63343133036503 / 25000) (63346425369071 / 25000) := by
  exact
    packedTile65536 2533783808 2533914880 14 6082 50336 31 _ _ (135331 / 6250) (2165299 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2533914880 :
    ThetaLowerSegment 2533914880 2534045952 (63346425369071 / 25000) (126699323908471 / 50000) := by
  exact
    packedTile65536 2533914880 2534045952 14 5979 50338 31 _ _ (1082651 / 50000) (433061 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2534045952 :
    ThetaLowerSegment 2534045952 2534177024 (126699323908471 / 50000) (1583824561313 / 625) := by
  exact
    packedTile65536 2534045952 2534177024 14 6134 50339 31 _ _ (2165307 / 100000) (216531 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2534177024 :
    ThetaLowerSegment 2534177024 2534308096 (1583824561313 / 625) (7919532794859 / 3125) := by
  exact
    packedTile65536 2534177024 2534308096 14 6059 50340 31 _ _ (67666 / 3125) (433063 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2534308096 :
    ThetaLowerSegment 2534308096 2534439168 (7919532794859 / 3125) (126719066140401 / 50000) := by
  exact
    packedTile65536 2534308096 2534439168 14 6042 50341 31 _ _ (2165317 / 100000) (54133 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2534439168 :
    ThetaLowerSegment 2534439168 2534570240 (126719066140401 / 50000)
      (126725601082197 / 50000) := by
  exact
    packedTile65536 2534439168 2534570240 14 6036 50343 31 _ _ (1082661 / 50000) (86613 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2534570240 :
    ThetaLowerSegment 2534570240 2534701312 (126725601082197 / 50000) (25346421144901 / 10000) := by
  exact
    packedTile65536 2534570240 2534701312 14 6008 50344 31 _ _ (2165327 / 100000) (216533 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2534701312 :
    ThetaLowerSegment 2534701312 2534832384 (25346421144901 / 10000)
      (253477357185653 / 100000) := by
  exact
    packedTile65536 2534701312 2534832384 14 6071 50345 31 _ _ (2165333 / 100000) (270667 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2534832384 :
    ThetaLowerSegment 2534832384 2534963456 (253477357185653 / 100000)
      (253490535432721 / 100000) := by
  exact
    packedTile65536 2534832384 2534963456 14 6086 50347 31 _ _ (1082669 / 50000) (2165341 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2534963456 :
    ThetaLowerSegment 2534963456 2535094528 (253490535432721 / 100000)
      (253503735363649 / 100000) := by
  exact
    packedTile65536 2534963456 2535094528 14 6096 50348 31 _ _ (2165343 / 100000) (1082673 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2535094528 :
    ThetaLowerSegment 2535094528 2535225600 (253503735363649 / 100000)
      (253516822726961 / 100000) := by
  exact
    packedTile65536 2535094528 2535225600 14 6044 50349 31 _ _ (541337 / 25000) (2165351 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2535225600 :
    ThetaLowerSegment 2535225600 2535356672 (253516822726961 / 100000)
      (253529762876489 / 100000) := by
  exact
    packedTile65536 2535225600 2535356672 14 5976 50351 31 _ _ (2165353 / 100000) (541339 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2535356672 :
    ThetaLowerSegment 2535356672 2535487744 (253529762876489 / 100000)
      (253542819991259 / 100000) := by
  exact
    packedTile65536 2535356672 2535487744 14 6030 50352 31 _ _ (2165359 / 100000) (1082681 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2535487744 :
    ThetaLowerSegment 2535487744 2535618816 (253542819991259 / 100000)
      (253555881466907 / 100000) := by
  exact
    packedTile65536 2535487744 2535618816 14 6032 50353 31 _ _ (541341 / 25000) (2165367 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2535618816 :
    ThetaLowerSegment 2535618816 2535749888 (253555881466907 / 100000)
      (31696114894207 / 12500) := by
  exact
    packedTile65536 2535618816 2535749888 14 6021 50354 31 _ _ (2165369 / 100000) (541343 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2535749888 :
    ThetaLowerSegment 2535749888 2535880960 (31696114894207 / 12500) (126790991427499 / 50000) := by
  exact
    packedTile65536 2535749888 2535880960 14 6033 50356 31 _ _ (1082687 / 50000) (2165377 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2535880960 :
    ThetaLowerSegment 2535880960 2536012032 (126790991427499 / 50000)
      (126797513549047 / 50000) := by
  exact
    packedTile65536 2535880960 2536012032 14 6024 50357 31 _ _ (2165379 / 100000) (1082691 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2536012032 :
    ThetaLowerSegment 2536012032 2536143104 (126797513549047 / 50000)
      (126804137458703 / 50000) := by
  exact
    packedTile65536 2536012032 2536143104 14 6118 50358 31 _ _ (270673 / 12500) (2165387 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2536143104 :
    ThetaLowerSegment 2536143104 2536274176 (126804137458703 / 50000) (7925670488948 / 3125) := by
  exact
    packedTile65536 2536143104 2536274176 14 6087 50360 31 _ _ (216539 / 10000) (2165393 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2536274176 :
    ThetaLowerSegment 2536274176 2536405248 (7925670488948 / 3125) (253634640736491 / 100000) := by
  exact
    packedTile65536 2536274176 2536405248 14 6089 50361 31 _ _ (433079 / 20000) (1082699 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2536405248 :
    ThetaLowerSegment 2536405248 2536536320 (253634640736491 / 100000)
      (253647767391291 / 100000) := by
  exact
    packedTile65536 2536405248 2536536320 14 6062 50362 31 _ _ (10827 / 500) (2165403 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2536536320 :
    ThetaLowerSegment 2536536320 2536667392 (253647767391291 / 100000) (15853790045251 / 6250) := by
  exact
    packedTile65536 2536536320 2536667392 14 5945 50364 31 _ _ (433081 / 20000) (67669 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2536667392 :
    ThetaLowerSegment 2536667392 2536798464 (15853790045251 / 6250) (126836917283573 / 50000) := by
  exact
    packedTile65536 2536667392 2536798464 14 6093 50365 31 _ _ (216541 / 10000) (2165413 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2536798464 :
    ThetaLowerSegment 2536798464 2536929536 (126836917283573 / 50000)
      (126843452506043 / 50000) := by
  exact
    packedTile65536 2536798464 2536929536 14 6036 50366 31 _ _ (433083 / 20000) (1082709 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2536929536 :
    ThetaLowerSegment 2536929536 2537060608 (126843452506043 / 50000)
      (126850044047567 / 50000) := by
  exact
    packedTile65536 2536929536 2537060608 14 6088 50367 31 _ _ (2165421 / 100000) (135339 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2537060608 :
    ThetaLowerSegment 2537060608 2537191680 (126850044047567 / 50000) (63428315095373 / 25000) := by
  exact
    packedTile65536 2537060608 2537191680 14 6083 50369 31 _ _ (1082713 / 50000) (2165429 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2537191680 :
    ThetaLowerSegment 2537191680 2537322752 (63428315095373 / 25000)
      (253726506322919 / 100000) := by
  exact
    packedTile65536 2537191680 2537322752 14 6117 50370 31 _ _ (2165431 / 100000) (1082717 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2537322752 :
    ThetaLowerSegment 2537322752 2537339136 (253726506322919 / 100000)
      (253728234340847 / 100000) := by
  exact
    packedTile65536 2537322752 2537339136 11 798 50371 31 _ _ (541359 / 25000) (2165439 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2537339136 :
    ThetaLowerSegment 2537339136 2537341184 (253728234340847 / 100000)
      (253728455215421 / 100000) := by
  exact
    packedTile65536 2537339136 2537341184 8 102 50372 31 _ _ (2165437 / 100000) (13534 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_2505341184_2537341184 :
    ThetaLowerSegment 2505341184 2537341184 (250526307787397 / 100000)
      (253728455215421 / 100000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2505341184 cell2505472256)
                  (ThetaLowerSegment.join cell2505603328 cell2505734400))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2505865472 cell2505996544)
                  (ThetaLowerSegment.join cell2506127616 cell2506258688)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2506389760 cell2506520832)
                  (ThetaLowerSegment.join cell2506651904 cell2506782976))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2506914048 cell2507045120)
                  (ThetaLowerSegment.join cell2507176192 cell2507307264))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2507438336 cell2507569408)
                  (ThetaLowerSegment.join cell2507700480 cell2507831552))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2507962624 cell2508093696)
                  (ThetaLowerSegment.join cell2508224768 cell2508355840)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2508486912 cell2508617984)
                  (ThetaLowerSegment.join cell2508749056 cell2508880128))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2509011200 cell2509142272)
                  (ThetaLowerSegment.join cell2509273344 cell2509404416)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2509535488 cell2509666560)
                  (ThetaLowerSegment.join cell2509797632 cell2509928704))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2510059776 cell2510190848)
                  (ThetaLowerSegment.join cell2510321920 cell2510452992)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2510584064 cell2510715136)
                  (ThetaLowerSegment.join cell2510846208 cell2510977280))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2511108352 cell2511239424)
                  (ThetaLowerSegment.join cell2511370496 cell2511501568))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2511632640 cell2511763712)
                  (ThetaLowerSegment.join cell2511894784 cell2512025856))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2512156928 cell2512288000)
                  (ThetaLowerSegment.join cell2512419072 cell2512550144)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2512681216 cell2512812288)
                  (ThetaLowerSegment.join cell2512943360 cell2513074432))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2513205504 cell2513336576)
                  (ThetaLowerSegment.join cell2513467648 cell2513598720))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2513729792 cell2513860864)
                  (ThetaLowerSegment.join cell2513991936 cell2514123008))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2514254080 cell2514385152)
                  (ThetaLowerSegment.join cell2514516224 cell2514647296)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2514778368 cell2514909440)
                  (ThetaLowerSegment.join cell2515040512 cell2515171584))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2515302656 cell2515433728)
                  (ThetaLowerSegment.join cell2515564800 cell2515695872))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2515826944 cell2515958016)
                  (ThetaLowerSegment.join cell2516089088 cell2516220160))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2516351232 cell2516482304)
                  (ThetaLowerSegment.join cell2516613376 cell2516744448)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2516875520 cell2517006592)
                  (ThetaLowerSegment.join cell2517137664 cell2517268736))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2517399808 cell2517530880)
                  (ThetaLowerSegment.join cell2517661952 cell2517793024)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2517924096 cell2518055168)
                  (ThetaLowerSegment.join cell2518186240 cell2518317312))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2518448384 cell2518579456)
                  (ThetaLowerSegment.join cell2518710528 cell2518841600)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2518972672 cell2519103744)
                  (ThetaLowerSegment.join cell2519234816 cell2519365888))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2519496960 cell2519628032)
                  (ThetaLowerSegment.join cell2519759104 cell2519890176))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2520021248 cell2520152320)
                  (ThetaLowerSegment.join cell2520283392 cell2520414464))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2520545536 cell2520676608)
                  (ThetaLowerSegment.join cell2520807680 cell2520938752)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2521069824 cell2521200896)
                  (ThetaLowerSegment.join cell2521331968 cell2521463040))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2521594112 cell2521725184)
                  (ThetaLowerSegment.join cell2521856256 cell2521987328)))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2522118400 cell2522249472)
                  (ThetaLowerSegment.join cell2522380544 cell2522511616))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2522642688 cell2522773760)
                  (ThetaLowerSegment.join cell2522904832 cell2523035904)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2523166976 cell2523298048)
                  (ThetaLowerSegment.join cell2523429120 cell2523560192))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2523691264 cell2523822336)
                  (ThetaLowerSegment.join cell2523953408 cell2524084480))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2524215552 cell2524346624)
                  (ThetaLowerSegment.join cell2524477696 cell2524608768))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2524739840 cell2524870912)
                  (ThetaLowerSegment.join cell2525001984 cell2525133056)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2525264128 cell2525395200)
                  (ThetaLowerSegment.join cell2525526272 cell2525657344))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2525788416 cell2525919488)
                  (ThetaLowerSegment.join cell2526050560 cell2526181632)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2526312704 cell2526443776)
                  (ThetaLowerSegment.join cell2526574848 cell2526705920))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2526836992 cell2526968064)
                  (ThetaLowerSegment.join cell2527099136 cell2527230208)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2527361280 cell2527492352)
                  (ThetaLowerSegment.join cell2527623424 cell2527754496))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2527885568 cell2528016640)
                  (ThetaLowerSegment.join cell2528147712 cell2528278784))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2528409856 cell2528540928)
                  (ThetaLowerSegment.join cell2528672000 cell2528803072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2528934144 cell2529065216)
                  (ThetaLowerSegment.join cell2529196288 cell2529327360)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2529458432 cell2529589504)
                  (ThetaLowerSegment.join cell2529720576 cell2529851648))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2529982720 cell2530113792)
                  (ThetaLowerSegment.join cell2530244864 cell2530375936))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2530507008 cell2530638080)
                  (ThetaLowerSegment.join cell2530769152 cell2530900224))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2531031296 cell2531162368)
                  (ThetaLowerSegment.join cell2531293440 cell2531424512)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2531555584 cell2531686656)
                  (ThetaLowerSegment.join cell2531817728 cell2531948800))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2532079872 cell2532210944)
                  (ThetaLowerSegment.join cell2532342016 cell2532473088))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2532604160 cell2532735232)
                  (ThetaLowerSegment.join cell2532866304 cell2532997376))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2533128448 cell2533259520)
                  (ThetaLowerSegment.join cell2533390592 cell2533521664)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2533652736 cell2533783808)
                  (ThetaLowerSegment.join cell2533914880 cell2534045952))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2534177024 cell2534308096)
                  (ThetaLowerSegment.join cell2534439168 cell2534570240)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2534701312 cell2534832384)
                  (ThetaLowerSegment.join cell2534963456 cell2535094528))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2535225600 cell2535356672)
                  (ThetaLowerSegment.join cell2535487744 cell2535618816)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2535749888 cell2535880960)
                  (ThetaLowerSegment.join cell2536012032 cell2536143104))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2536274176 cell2536405248)
                  (ThetaLowerSegment.join cell2536536320 cell2536667392))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell2536798464 cell2536929536)
                (ThetaLowerSegment.join cell2537060608 cell2537191680))
              (ThetaLowerSegment.join cell2537322752 cell2537339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
