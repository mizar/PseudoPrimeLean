/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis65536

/-! # Direct theta estimate up to 1417341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell1385341184 :
    ThetaLowerSegment 1385341184 1385472256 (34632366098693 / 25000) (34635638723063 / 25000) := by
  exact
    packedTile65536 1385341184 1385472256 14 6219 37220 30 _ _ (52623 / 2500) (2104923 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1385472256 :
    ThetaLowerSegment 1385472256 1385603328 (34635638723063 / 25000) (17319434894539 / 12500) := by
  exact
    packedTile65536 1385472256 1385603328 14 6140 37221 30 _ _ (2104929 / 100000) (526233 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1385603328 :
    ThetaLowerSegment 1385603328 1385734400 (17319434894539 / 12500)
      (138568531883051 / 100000) := by
  exact
    packedTile65536 1385603328 1385734400 14 6201 37223 30 _ _ (2104939 / 100000) (1052471 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1385734400 :
    ThetaLowerSegment 1385734400 1385865472 (138568531883051 / 100000)
      (138581717277323 / 100000) := by
  exact
    packedTile65536 1385734400 1385865472 14 6264 37225 30 _ _ (526237 / 25000) (2104951 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1385865472 :
    ThetaLowerSegment 1385865472 1385996544 (138581717277323 / 100000)
      (138594875369781 / 100000) := by
  exact
    packedTile65536 1385865472 1385996544 14 6251 37227 30 _ _ (1052479 / 50000) (2104961 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1385996544 :
    ThetaLowerSegment 1385996544 1386127616 (138594875369781 / 100000)
      (138608001943993 / 100000) := by
  exact
    packedTile65536 1385996544 1386127616 14 6236 37228 30 _ _ (2104967 / 100000) (210497 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1386127616 :
    ThetaLowerSegment 1386127616 1386258688 (138608001943993 / 100000)
      (138621303287337 / 100000) := by
  exact
    packedTile65536 1386127616 1386258688 14 6319 37230 30 _ _ (131561 / 6250) (2104979 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1386258688 :
    ThetaLowerSegment 1386258688 1386389760 (138621303287337 / 100000)
      (138634417350117 / 100000) := by
  exact
    packedTile65536 1386258688 1386389760 14 6230 37232 30 _ _ (1052493 / 50000) (2104989 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1386389760 :
    ThetaLowerSegment 1386389760 1386520832 (138634417350117 / 100000) (8665462691517 / 6250) := by
  exact
    packedTile65536 1386389760 1386520832 14 6169 37234 30 _ _ (420999 / 20000) (1052499 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1386520832 :
    ThetaLowerSegment 1386520832 1386651904 (8665462691517 / 6250) (138660464620297 / 100000) := by
  exact
    packedTile65536 1386520832 1386651904 14 6205 37236 30 _ _ (421001 / 20000) (131563 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1386651904 :
    ThetaLowerSegment 1386651904 1386782976 (138660464620297 / 100000)
      (138673399931327 / 100000) := by
  exact
    packedTile65536 1386651904 1386782976 14 6145 37237 30 _ _ (1052507 / 50000) (2105017 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1386782976 :
    ThetaLowerSegment 1386782976 1386914048 (138673399931327 / 100000)
      (138686501600703 / 100000) := by
  exact
    packedTile65536 1386782976 1386914048 14 6224 37239 30 _ _ (65782 / 3125) (2105027 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1386914048 :
    ThetaLowerSegment 1386914048 1387045120 (138686501600703 / 100000)
      (138699535965039 / 100000) := by
  exact
    packedTile65536 1386914048 1387045120 14 6192 37241 30 _ _ (2105033 / 100000) (526259 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1387045120 :
    ThetaLowerSegment 1387045120 1387176192 (138699535965039 / 100000)
      (27742522498431 / 20000) := by
  exact
    packedTile65536 1387045120 1387176192 14 6212 37243 30 _ _ (2105043 / 100000) (1052523 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1387176192 :
    ThetaLowerSegment 1387176192 1387307264 (27742522498431 / 20000)
      (138725722756011 / 100000) := by
  exact
    packedTile65536 1387176192 1387307264 14 6228 37244 30 _ _ (526263 / 25000) (421011 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1387307264 :
    ThetaLowerSegment 1387307264 1387438336 (138725722756011 / 100000)
      (27747736724549 / 20000) := by
  exact
    packedTile65536 1387307264 1387438336 14 6157 37246 30 _ _ (1052531 / 50000) (421013 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1387438336 :
    ThetaLowerSegment 1387438336 1387569408 (27747736724549 / 20000) (69375866478937 / 50000) := by
  exact
    packedTile65536 1387438336 1387569408 14 6199 37248 30 _ _ (2105071 / 100000) (1052537 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1387569408 :
    ThetaLowerSegment 1387569408 1387700480 (69375866478937 / 50000) (69382383806617 / 50000) := by
  exact
    packedTile65536 1387569408 1387700480 14 6192 37250 30 _ _ (52627 / 2500) (2105083 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1387700480 :
    ThetaLowerSegment 1387700480 1387831552 (69382383806617 / 50000) (8673610408999 / 6250) := by
  exact
    packedTile65536 1387700480 1387831552 14 6175 37251 30 _ _ (210509 / 10000) (2105093 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1387831552 :
    ThetaLowerSegment 1387831552 1387962624 (8673610408999 / 6250) (138790988670803 / 100000) := by
  exact
    packedTile65536 1387831552 1387962624 14 6281 37253 30 _ _ (2105099 / 100000) (1052551 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1387962624 :
    ThetaLowerSegment 1387962624 1388093696 (138790988670803 / 100000) (5552166497717 / 4000) := by
  exact
    packedTile65536 1387962624 1388093696 14 6258 37255 30 _ _ (2105109 / 100000) (263139 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1388093696 :
    ThetaLowerSegment 1388093696 1388224768 (5552166497717 / 4000) (5552699092571 / 4000) := by
  exact
    packedTile65536 1388093696 1388224768 14 6325 37257 30 _ _ (1052559 / 50000) (2105121 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1388224768 :
    ThetaLowerSegment 1388224768 1388355840 (5552699092571 / 4000) (138830484900187 / 100000) := by
  exact
    packedTile65536 1388224768 1388355840 14 6179 37258 30 _ _ (263141 / 12500) (2105131 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1388355840 :
    ThetaLowerSegment 1388355840 1388486912 (138830484900187 / 100000) (6942173574517 / 5000) := by
  exact
    packedTile65536 1388355840 1388486912 14 6169 37260 30 _ _ (2105137 / 100000) (105257 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1388486912 :
    ThetaLowerSegment 1388486912 1388617984 (6942173574517 / 5000) (69428305908957 / 50000) := by
  exact
    packedTile65536 1388486912 1388617984 14 6242 37262 30 _ _ (2105147 / 100000) (42103 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1388617984 :
    ThetaLowerSegment 1388617984 1388749056 (69428305908957 / 50000) (69434742423427 / 50000) := by
  exact
    packedTile65536 1388617984 1388749056 14 6115 37264 30 _ _ (526289 / 25000) (2105159 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1388749056 :
    ThetaLowerSegment 1388749056 1388880128 (69434742423427 / 50000)
      (138882568447329 / 100000) := by
  exact
    packedTile65536 1388749056 1388880128 14 6215 37265 30 _ _ (421033 / 20000) (131573 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1388880128 :
    ThetaLowerSegment 1388880128 1389011200 (138882568447329 / 100000)
      (138895708949679 / 100000) := by
  exact
    packedTile65536 1388880128 1389011200 14 6242 37267 30 _ _ (84207 / 4000) (1052589 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1389011200 :
    ThetaLowerSegment 1389011200 1389142272 (138895708949679 / 100000)
      (138908681093487 / 100000) := by
  exact
    packedTile65536 1389011200 1389142272 14 6162 37269 30 _ _ (65787 / 3125) (2105187 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1389142272 :
    ThetaLowerSegment 1389142272 1389207808 (138908681093487 / 100000) (5556614771793 / 4000) := by
  exact
    packedTile65536 1389142272 1389207808 13 3177 37271 30 _ _ (1052597 / 50000) (2105197 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1389207808 :
    ThetaLowerSegment 1389207808 1389338880 (5556614771793 / 4000) (138928415206831 / 100000) := by
  exact
    packedTile65536 1389207808 1389338880 14 6197 37272 30 _ _ (1052599 / 50000) (2105201 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1389338880 :
    ThetaLowerSegment 1389338880 1389469952 (138928415206831 / 100000)
      (138941532757879 / 100000) := by
  exact
    packedTile65536 1389338880 1389469952 14 6231 37273 30 _ _ (263151 / 12500) (2105211 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1389469952 :
    ThetaLowerSegment 1389469952 1389601024 (138941532757879 / 100000)
      (138954736678903 / 100000) := by
  exact
    packedTile65536 1389469952 1389601024 14 6272 37275 30 _ _ (2105217 / 100000) (105261 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1389601024 :
    ThetaLowerSegment 1389601024 1389732096 (138954736678903 / 100000)
      (138967919610377 / 100000) := by
  exact
    packedTile65536 1389601024 1389732096 14 6262 37277 30 _ _ (2105227 / 100000) (210523 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1389732096 :
    ThetaLowerSegment 1389732096 1389863168 (138967919610377 / 100000)
      (138981117334861 / 100000) := by
  exact
    packedTile65536 1389732096 1389863168 14 6269 37279 30 _ _ (526309 / 25000) (2105239 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1389863168 :
    ThetaLowerSegment 1389863168 1389994240 (138981117334861 / 100000)
      (138994376174169 / 100000) := by
  exact
    packedTile65536 1389863168 1389994240 14 6298 37280 30 _ _ (1052623 / 50000) (2105249 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1389994240 :
    ThetaLowerSegment 1389994240 1390125312 (138994376174169 / 100000)
      (139007512965369 / 100000) := by
  exact
    packedTile65536 1389994240 1390125312 14 6240 37282 30 _ _ (421051 / 20000) (1052629 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1390125312 :
    ThetaLowerSegment 1390125312 1390256384 (139007512965369 / 100000)
      (139020654023257 / 100000) := by
  exact
    packedTile65536 1390125312 1390256384 14 6242 37284 30 _ _ (131579 / 6250) (2105267 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1390256384 :
    ThetaLowerSegment 1390256384 1390387456 (139020654023257 / 100000)
      (27806792713097 / 20000) := by
  exact
    packedTile65536 1390256384 1390387456 14 6322 37286 30 _ _ (1052637 / 50000) (2105277 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1390387456 :
    ThetaLowerSegment 1390387456 1390518528 (27806792713097 / 20000)
      (139047033162349 / 100000) := by
  exact
    packedTile65536 1390387456 1390518528 14 6208 37287 30 _ _ (2105283 / 100000) (1052643 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1390518528 :
    ThetaLowerSegment 1390518528 1390649600 (139047033162349 / 100000)
      (34765002020777 / 25000) := by
  exact
    packedTile65536 1390518528 1390649600 14 6163 37289 30 _ _ (2105293 / 100000) (131581 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1390649600 :
    ThetaLowerSegment 1390649600 1390780672 (34765002020777 / 25000) (13907318937893 / 10000) := by
  exact
    packedTile65536 1390649600 1390780672 14 6261 37291 30 _ _ (1052651 / 50000) (421061 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1390780672 :
    ThetaLowerSegment 1390780672 1390911744 (13907318937893 / 10000) (69543145367753 / 50000) := by
  exact
    packedTile65536 1390780672 1390911744 14 6223 37293 30 _ _ (65791 / 3125) (421063 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1390911744 :
    ThetaLowerSegment 1390911744 1391042816 (69543145367753 / 50000) (8693720298957 / 6250) := by
  exact
    packedTile65536 1390911744 1391042816 14 6286 37294 30 _ _ (2105321 / 100000) (526331 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1391042816 :
    ThetaLowerSegment 1391042816 1391173888 (8693720298957 / 6250) (69556323652601 / 50000) := by
  exact
    packedTile65536 1391042816 1391173888 14 6233 37296 30 _ _ (210533 / 10000) (2105333 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1391173888 :
    ThetaLowerSegment 1391173888 1391304960 (69556323652601 / 50000) (69562890208061 / 50000) := by
  exact
    packedTile65536 1391173888 1391304960 14 6238 37298 30 _ _ (105267 / 5000) (2105343 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1391304960 :
    ThetaLowerSegment 1391304960 1391436032 (69562890208061 / 50000) (27827794927661 / 20000) := by
  exact
    packedTile65536 1391304960 1391436032 14 6267 37300 30 _ _ (2105349 / 100000) (263169 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1391436032 :
    ThetaLowerSegment 1391436032 1391567104 (27827794927661 / 20000) (8697011347207 / 6250) := by
  exact
    packedTile65536 1391436032 1391567104 14 6273 37301 30 _ _ (2105359 / 100000) (1052681 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1391567104 :
    ThetaLowerSegment 1391567104 1391698176 (8697011347207 / 6250) (17395680408543 / 12500) := by
  exact
    packedTile65536 1391567104 1391698176 14 6299 37303 30 _ _ (263171 / 12500) (2105371 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1391698176 :
    ThetaLowerSegment 1391698176 1391829248 (17395680408543 / 12500) (347946515229 / 250) := by
  exact
    packedTile65536 1391698176 1391829248 14 6252 37305 30 _ _ (1052689 / 50000) (2105381 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1391829248 :
    ThetaLowerSegment 1391829248 1391960320 (347946515229 / 250) (69595831850887 / 50000) := by
  exact
    packedTile65536 1391829248 1391960320 14 6202 37307 30 _ _ (2105387 / 100000) (210539 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1391960320 :
    ThetaLowerSegment 1391960320 1392091392 (69595831850887 / 50000) (69602309101681 / 50000) := by
  exact
    packedTile65536 1391960320 1392091392 14 6153 37308 30 _ _ (526349 / 25000) (2105399 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1392091392 :
    ThetaLowerSegment 1392091392 1392222464 (69602309101681 / 50000) (34804415298383 / 25000) := by
  exact
    packedTile65536 1392091392 1392222464 14 6195 37310 30 _ _ (1052703 / 50000) (2105409 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1392222464 :
    ThetaLowerSegment 1392222464 1392353536 (34804415298383 / 25000)
      (139230851618507 / 100000) := by
  exact
    packedTile65536 1392222464 1392353536 14 6265 37312 30 _ _ (421083 / 20000) (1052709 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1392353536 :
    ThetaLowerSegment 1392353536 1392484608 (139230851618507 / 100000)
      (139244145271957 / 100000) := by
  exact
    packedTile65536 1392353536 1392484608 14 6314 37314 30 _ _ (84217 / 4000) (526357 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1392484608 :
    ThetaLowerSegment 1392484608 1392615680 (139244145271957 / 100000)
      (139257207384493 / 100000) := by
  exact
    packedTile65536 1392484608 1392615680 14 6204 37316 30 _ _ (1052717 / 50000) (2105437 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1392615680 :
    ThetaLowerSegment 1392615680 1392746752 (139257207384493 / 100000)
      (139270303239953 / 100000) := by
  exact
    packedTile65536 1392615680 1392746752 14 6220 37317 30 _ _ (2105443 / 100000) (1052723 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1392746752 :
    ThetaLowerSegment 1392746752 1392877824 (139270303239953 / 100000)
      (34820851368493 / 25000) := by
  exact
    packedTile65536 1392746752 1392877824 14 6223 37319 30 _ _ (2105453 / 100000) (131591 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1392877824 :
    ThetaLowerSegment 1392877824 1393008896 (34820851368493 / 25000) (69648180190829 / 50000) := by
  exact
    packedTile65536 1392877824 1393008896 14 6153 37321 30 _ _ (1052731 / 50000) (421093 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1393008896 :
    ThetaLowerSegment 1393008896 1393139968 (69648180190829 / 50000) (69654682941101 / 50000) := by
  exact
    packedTile65536 1393008896 1393139968 14 6177 37323 30 _ _ (65796 / 3125) (84219 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1393139968 :
    ThetaLowerSegment 1393139968 1393271040 (69654682941101 / 50000)
      (139322438813731 / 100000) := by
  exact
    packedTile65536 1393139968 1393271040 14 6209 37324 30 _ _ (2105481 / 100000) (526371 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1393271040 :
    ThetaLowerSegment 1393271040 1393402112 (139322438813731 / 100000)
      (34833900059493 / 25000) := by
  exact
    packedTile65536 1393271040 1393402112 14 6251 37326 30 _ _ (2105491 / 100000) (1052747 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1393402112 :
    ThetaLowerSegment 1393402112 1393533184 (34833900059493 / 25000) (34837176217493 / 25000) := by
  exact
    packedTile65536 1393402112 1393533184 14 6224 37328 30 _ _ (4211 / 200) (2105503 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1393533184 :
    ThetaLowerSegment 1393533184 1393664256 (34837176217493 / 25000) (13936180534697 / 10000) := by
  exact
    packedTile65536 1393533184 1393664256 14 6222 37330 30 _ _ (2105509 / 100000) (263189 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1393664256 :
    ThetaLowerSegment 1393664256 1393795328 (13936180534697 / 10000) (2787498033503 / 2000) := by
  exact
    packedTile65536 1393664256 1393795328 14 6220 37331 30 _ _ (2105519 / 100000) (1052761 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1393795328 :
    ThetaLowerSegment 1393795328 1393926400 (2787498033503 / 2000) (69693959024623 / 50000) := by
  exact
    packedTile65536 1393795328 1393926400 14 6182 37333 30 _ _ (263191 / 12500) (2105531 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1393926400 :
    ThetaLowerSegment 1393926400 1394057472 (69693959024623 / 50000) (1742510917807 / 1250) := by
  exact
    packedTile65536 1393926400 1394057472 14 6153 37335 30 _ _ (1052769 / 50000) (2105541 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1394057472 :
    ThetaLowerSegment 1394057472 1394188544 (1742510917807 / 1250) (69707088135253 / 50000) := by
  exact
    packedTile65536 1394057472 1394188544 14 6318 37337 30 _ _ (2105547 / 100000) (42111 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1394188544 :
    ThetaLowerSegment 1394188544 1394319616 (69707088135253 / 50000) (69713639572747 / 50000) := by
  exact
    packedTile65536 1394188544 1394319616 14 6223 37338 30 _ _ (526389 / 25000) (2105559 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1394319616 :
    ThetaLowerSegment 1394319616 1394450688 (69713639572747 / 50000) (69720156299517 / 50000) := by
  exact
    packedTile65536 1394319616 1394450688 14 6190 37340 30 _ _ (1052783 / 50000) (2105569 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1394450688 :
    ThetaLowerSegment 1394450688 1394581760 (69720156299517 / 50000)
      (139453339791559 / 100000) := by
  exact
    packedTile65536 1394450688 1394581760 14 6187 37342 30 _ _ (84223 / 4000) (1052789 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1394581760 :
    ThetaLowerSegment 1394581760 1394712832 (139453339791559 / 100000)
      (139466621821739 / 100000) := by
  exact
    packedTile65536 1394581760 1394712832 14 6308 37344 30 _ _ (421117 / 20000) (526397 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1394712832 :
    ThetaLowerSegment 1394712832 1394843904 (139466621821739 / 100000)
      (139479752305923 / 100000) := by
  exact
    packedTile65536 1394712832 1394843904 14 6236 37345 30 _ _ (1052797 / 50000) (2105597 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1394843904 :
    ThetaLowerSegment 1394843904 1394974976 (139479752305923 / 100000)
      (139493059716883 / 100000) := by
  exact
    packedTile65536 1394843904 1394974976 14 6320 37347 30 _ _ (2105603 / 100000) (1052803 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1394974976 :
    ThetaLowerSegment 1394974976 1395106048 (139493059716883 / 100000)
      (69753047783483 / 50000) := by
  exact
    packedTile65536 1394974976 1395106048 14 6191 37349 30 _ _ (2105613 / 100000) (131601 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1395106048 :
    ThetaLowerSegment 1395106048 1395237120 (69753047783483 / 50000) (69759600479147 / 50000) := by
  exact
    packedTile65536 1395106048 1395237120 14 6224 37351 30 _ _ (1052811 / 50000) (3369 / 160)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1395237120 :
    ThetaLowerSegment 1395237120 1395368192 (69759600479147 / 50000) (69766163734091 / 50000) := by
  exact
    packedTile65536 1395237120 1395368192 14 6234 37352 30 _ _ (65801 / 3125) (421127 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1395368192 :
    ThetaLowerSegment 1395368192 1395499264 (69766163734091 / 50000)
      (139545300322383 / 100000) := by
  exact
    packedTile65536 1395368192 1395499264 14 6161 37354 30 _ _ (2105641 / 100000) (526411 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1395499264 :
    ThetaLowerSegment 1395499264 1395630336 (139545300322383 / 100000)
      (139558517487433 / 100000) := by
  exact
    packedTile65536 1395499264 1395630336 14 6277 37356 30 _ _ (42113 / 2000) (2105653 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1395630336 :
    ThetaLowerSegment 1395630336 1395761408 (139558517487433 / 100000)
      (139571585213393 / 100000) := by
  exact
    packedTile65536 1395630336 1395761408 14 6206 37358 30 _ _ (105283 / 5000) (2105663 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1395761408 :
    ThetaLowerSegment 1395761408 1395892480 (139571585213393 / 100000)
      (139584686685911 / 100000) := by
  exact
    packedTile65536 1395761408 1395892480 14 6222 37359 30 _ _ (2105669 / 100000) (263209 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1395892480 :
    ThetaLowerSegment 1395892480 1396023552 (139584686685911 / 100000)
      (139597805059851 / 100000) := by
  exact
    packedTile65536 1395892480 1396023552 14 6230 37361 30 _ _ (1052839 / 50000) (2105681 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1396023552 :
    ThetaLowerSegment 1396023552 1396154624 (139597805059851 / 100000)
      (139610923496091 / 100000) := by
  exact
    packedTile65536 1396023552 1396154624 14 6230 37363 30 _ _ (263211 / 12500) (2105691 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1396154624 :
    ThetaLowerSegment 1396154624 1396285696 (139610923496091 / 100000)
      (139624016720037 / 100000) := by
  exact
    packedTile65536 1396154624 1396285696 14 6218 37365 30 _ _ (2105697 / 100000) (21057 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1396285696 :
    ThetaLowerSegment 1396285696 1396416768 (139624016720037 / 100000)
      (139637156331717 / 100000) := by
  exact
    packedTile65536 1396285696 1396416768 14 6240 37366 30 _ _ (2105707 / 100000) (210571 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1396416768 :
    ThetaLowerSegment 1396416768 1396547840 (139637156331717 / 100000)
      (27930060463341 / 20000) := by
  exact
    packedTile65536 1396416768 1396547840 14 6243 37368 30 _ _ (526429 / 25000) (2105719 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1396547840 :
    ThetaLowerSegment 1396547840 1396678912 (27930060463341 / 20000) (27932668193181 / 20000) := by
  exact
    packedTile65536 1396547840 1396678912 14 6192 37370 30 _ _ (84229 / 4000) (65804 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1396678912 :
    ThetaLowerSegment 1396678912 1396809984 (27932668193181 / 20000) (27935264143289 / 20000) := by
  exact
    packedTile65536 1396678912 1396809984 14 6164 37372 30 _ _ (421147 / 20000) (1052869 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1396809984 :
    ThetaLowerSegment 1396809984 1396941056 (27935264143289 / 20000)
      (139689393175197 / 100000) := by
  exact
    packedTile65536 1396809984 1396941056 14 6208 37373 30 _ _ (131609 / 6250) (2105747 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1396941056 :
    ThetaLowerSegment 1396941056 1397072128 (139689393175197 / 100000)
      (27940499035317 / 20000) := by
  exact
    packedTile65536 1396941056 1397072128 14 6222 37375 30 _ _ (1052877 / 50000) (2105757 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1397072128 :
    ThetaLowerSegment 1397072128 1397203200 (27940499035317 / 20000) (8732220483987 / 6250) := by
  exact
    packedTile65536 1397072128 1397203200 14 6189 37377 30 _ _ (2105763 / 100000) (1052883 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1397203200 :
    ThetaLowerSegment 1397203200 1397334272 (8732220483987 / 6250) (8733053316813 / 6250) := by
  exact
    packedTile65536 1397203200 1397334272 14 6328 37379 30 _ _ (526443 / 25000) (84231 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1397334272 :
    ThetaLowerSegment 1397334272 1397465344 (8733053316813 / 6250) (69870982886761 / 50000) := by
  exact
    packedTile65536 1397334272 1397465344 14 6227 37380 30 _ _ (1052891 / 50000) (421157 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1397465344 :
    ThetaLowerSegment 1397465344 1397596416 (69870982886761 / 50000) (69877565589427 / 50000) := by
  exact
    packedTile65536 1397465344 1397596416 14 6252 37382 30 _ _ (2105791 / 100000) (1052897 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1397596416 :
    ThetaLowerSegment 1397596416 1397727488 (69877565589427 / 50000) (69884040924427 / 50000) := by
  exact
    packedTile65536 1397596416 1397727488 14 6150 37384 30 _ _ (10529 / 500) (2105803 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1397727488 :
    ThetaLowerSegment 1397727488 1397858560 (69884040924427 / 50000) (17472650920323 / 12500) := by
  exact
    packedTile65536 1397727488 1397858560 14 6233 37386 30 _ _ (210581 / 10000) (2105813 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1397858560 :
    ThetaLowerSegment 1397858560 1397989632 (17472650920323 / 12500) (13979433503823 / 10000) := by
  exact
    packedTile65536 1397858560 1397989632 14 6234 37387 30 _ _ (2105819 / 100000) (1052911 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1397989632 :
    ThetaLowerSegment 1397989632 1398120704 (13979433503823 / 10000) (69903678742383 / 50000) := by
  exact
    packedTile65536 1397989632 1398120704 14 6184 37389 30 _ _ (2105829 / 100000) (263229 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1398120704 :
    ThetaLowerSegment 1398120704 1398251776 (69903678742383 / 50000) (13982051476059 / 10000) := by
  exact
    packedTile65536 1398120704 1398251776 14 6248 37391 30 _ _ (1052919 / 50000) (2105841 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1398251776 :
    ThetaLowerSegment 1398251776 1398382848 (13982051476059 / 10000) (69916823411241 / 50000) := by
  exact
    packedTile65536 1398251776 1398382848 14 6236 37393 30 _ _ (2105847 / 100000) (42117 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1398382848 :
    ThetaLowerSegment 1398382848 1398513920 (69916823411241 / 50000)
      (139846797899447 / 100000) := by
  exact
    packedTile65536 1398382848 1398513920 14 6245 37394 30 _ _ (2105857 / 100000) (105293 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1398513920 :
    ThetaLowerSegment 1398513920 1398644992 (139846797899447 / 100000)
      (139859791092667 / 100000) := by
  exact
    packedTile65536 1398513920 1398644992 14 6170 37396 30 _ _ (1052933 / 50000) (2105869 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1398644992 :
    ThetaLowerSegment 1398644992 1398776064 (139859791092667 / 100000)
      (139872855941167 / 100000) := by
  exact
    packedTile65536 1398644992 1398776064 14 6204 37398 30 _ _ (16847 / 800) (1052939 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1398776064 :
    ThetaLowerSegment 1398776064 1398907136 (139872855941167 / 100000)
      (139886051416577 / 100000) := by
  exact
    packedTile65536 1398776064 1398907136 14 6266 37400 30 _ _ (421177 / 20000) (65809 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1398907136 :
    ThetaLowerSegment 1398907136 1399038208 (139886051416577 / 100000)
      (27979822434233 / 20000) := by
  exact
    packedTile65536 1398907136 1399038208 14 6202 37401 30 _ _ (1052947 / 50000) (2105897 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1399038208 :
    ThetaLowerSegment 1399038208 1399169280 (27979822434233 / 20000) (27982454814233 / 20000) := by
  exact
    packedTile65536 1399038208 1399169280 14 6250 37403 30 _ _ (131619 / 6250) (2105907 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1399169280 :
    ThetaLowerSegment 1399169280 1399300352 (27982454814233 / 20000)
      (139925343367243 / 100000) := by
  exact
    packedTile65536 1399169280 1399300352 14 6206 37405 30 _ _ (2105913 / 100000) (526479 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1399300352 :
    ThetaLowerSegment 1399300352 1399431424 (139925343367243 / 100000)
      (139938322164529 / 100000) := by
  exact
    packedTile65536 1399300352 1399431424 14 6163 37407 30 _ _ (1052961 / 50000) (84237 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1399431424 :
    ThetaLowerSegment 1399431424 1399562496 (139938322164529 / 100000)
      (139951488451393 / 100000) := by
  exact
    packedTile65536 1399431424 1399562496 14 6252 37408 30 _ _ (526483 / 25000) (421187 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1399562496 :
    ThetaLowerSegment 1399562496 1399693568 (139951488451393 / 100000)
      (17495590009837 / 12500) := by
  exact
    packedTile65536 1399562496 1399693568 14 6283 37410 30 _ _ (2105941 / 100000) (263243 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1399693568 :
    ThetaLowerSegment 1399693568 1399824640 (17495590009837 / 12500) (69988874795673 / 50000) := by
  exact
    packedTile65536 1399693568 1399824640 14 6187 37412 30 _ _ (42119 / 2000) (2105953 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1399824640 :
    ThetaLowerSegment 1399824640 1399955712 (69988874795673 / 50000) (69995449602793 / 50000) := by
  exact
    packedTile65536 1399824640 1399955712 14 6244 37414 30 _ _ (52649 / 2500) (2105963 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1399955712 :
    ThetaLowerSegment 1399955712 1400086784 (69995449602793 / 50000)
      (140004055193929 / 100000) := by
  exact
    packedTile65536 1399955712 1400086784 14 6247 37415 30 _ _ (2105969 / 100000) (526493 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1400086784 :
    ThetaLowerSegment 1400086784 1400217856 (140004055193929 / 100000)
      (70008614046287 / 50000) := by
  exact
    packedTile65536 1400086784 1400217856 14 6255 37417 30 _ _ (2105979 / 100000) (1052991 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1400217856 :
    ThetaLowerSegment 1400217856 1400348928 (70008614046287 / 50000) (70015175251901 / 50000) := by
  exact
    packedTile65536 1400217856 1400348928 14 6231 37419 30 _ _ (526497 / 25000) (2105991 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1400348928 :
    ThetaLowerSegment 1400348928 1400480000 (70015175251901 / 50000)
      (140043451911139 / 100000) := by
  exact
    packedTile65536 1400348928 1400480000 14 6221 37421 30 _ _ (2105997 / 100000) (1053 / 50)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1400480000 :
    ThetaLowerSegment 1400480000 1400611072 (140043451911139 / 100000)
      (70028264054301 / 50000) := by
  exact
    packedTile65536 1400480000 1400611072 14 6209 37422 30 _ _ (2106007 / 100000) (210601 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1400611072 :
    ThetaLowerSegment 1400611072 1400742144 (70028264054301 / 50000) (70034707410253 / 50000) := by
  exact
    packedTile65536 1400611072 1400742144 14 6119 37424 30 _ _ (65813 / 3125) (2106019 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1400742144 :
    ThetaLowerSegment 1400742144 1400873216 (70034707410253 / 50000)
      (140082529038181 / 100000) := by
  exact
    packedTile65536 1400742144 1400873216 14 6227 37426 30 _ _ (84241 / 4000) (526507 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1400873216 :
    ThetaLowerSegment 1400873216 1401004288 (140082529038181 / 100000)
      (140095797058681 / 100000) := by
  exact
    packedTile65536 1400873216 1401004288 14 6300 37428 30 _ _ (421207 / 20000) (1053019 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1401004288 :
    ThetaLowerSegment 1401004288 1401135360 (140095797058681 / 100000)
      (140108810304557 / 100000) := by
  exact
    packedTile65536 1401004288 1401135360 14 6179 37429 30 _ _ (526511 / 25000) (2106047 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1401135360 :
    ThetaLowerSegment 1401135360 1401266432 (140108810304557 / 100000)
      (35030464325723 / 25000) := by
  exact
    packedTile65536 1401135360 1401266432 14 6195 37431 30 _ _ (2106053 / 100000) (263257 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1401266432 :
    ThetaLowerSegment 1401266432 1401397504 (35030464325723 / 25000)
      (140134921211681 / 100000) := by
  exact
    packedTile65536 1401266432 1401397504 14 6203 37433 30 _ _ (2106063 / 100000) (1053033 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1401397504 :
    ThetaLowerSegment 1401397504 1401528576 (140134921211681 / 100000)
      (140148037828097 / 100000) := by
  exact
    packedTile65536 1401397504 1401528576 14 6228 37435 30 _ _ (263259 / 12500) (84243 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1401528576 :
    ThetaLowerSegment 1401528576 1401659648 (140148037828097 / 100000)
      (140161141864079 / 100000) := by
  exact
    packedTile65536 1401528576 1401659648 14 6222 37436 30 _ _ (2106081 / 100000) (526521 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1401659648 :
    ThetaLowerSegment 1401659648 1401790720 (140161141864079 / 100000) (1401742649171 / 1000) := by
  exact
    packedTile65536 1401659648 1401790720 14 6231 37438 30 _ _ (2106091 / 100000) (1053047 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1401790720 :
    ThetaLowerSegment 1401790720 1401921792 (1401742649171 / 1000) (1401873269493 / 1000) := by
  exact
    packedTile65536 1401790720 1401921792 14 6202 37440 30 _ _ (21061 / 1000) (2106103 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1401921792 :
    ThetaLowerSegment 1401921792 1402052864 (1401873269493 / 1000) (5608017499113 / 4000) := by
  exact
    packedTile65536 1401921792 1402052864 14 6225 37442 30 _ _ (2106109 / 100000) (65816 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1402052864 :
    ThetaLowerSegment 1402052864 1402183936 (5608017499113 / 4000) (140213415383103 / 100000) := by
  exact
    packedTile65536 1402052864 1402183936 14 6162 37443 30 _ _ (2106119 / 100000) (1053061 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1402183936 :
    ThetaLowerSegment 1402183936 1402315008 (140213415383103 / 100000)
      (140226603956639 / 100000) := by
  exact
    packedTile65536 1402183936 1402315008 14 6262 37445 30 _ _ (131633 / 6250) (2106131 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1402315008 :
    ThetaLowerSegment 1402315008 1402446080 (140226603956639 / 100000) (5609582015477 / 4000) := by
  exact
    packedTile65536 1402315008 1402446080 14 6147 37447 30 _ _ (1053069 / 50000) (2106141 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1402446080 :
    ThetaLowerSegment 1402446080 1402577152 (5609582015477 / 4000) (140252768565497 / 100000) := by
  exact
    packedTile65536 1402446080 1402577152 14 6276 37449 30 _ _ (2106147 / 100000) (42123 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1402577152 :
    ThetaLowerSegment 1402577152 1402708224 (140252768565497 / 100000)
      (28053168716389 / 20000) := by
  exact
    packedTile65536 1402577152 1402708224 14 6208 37450 30 _ _ (526539 / 25000) (2106159 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1402708224 :
    ThetaLowerSegment 1402708224 1402839296 (28053168716389 / 20000)
      (140278948146797 / 100000) := by
  exact
    packedTile65536 1402708224 1402839296 14 6222 37452 30 _ _ (1053083 / 50000) (2106169 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1402839296 :
    ThetaLowerSegment 1402839296 1402970368 (140278948146797 / 100000)
      (70146010587511 / 50000) := by
  exact
    packedTile65536 1402839296 1402970368 14 6207 37454 30 _ _ (84247 / 4000) (1053089 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1402970368 :
    ThetaLowerSegment 1402970368 1403101440 (70146010587511 / 50000) (70152551341923 / 50000) := by
  exact
    packedTile65536 1402970368 1403101440 14 6211 37456 30 _ _ (263273 / 12500) (2106187 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1403101440 :
    ThetaLowerSegment 1403101440 1403232512 (70152551341923 / 50000) (35079552382277 / 25000) := by
  exact
    packedTile65536 1403101440 1403232512 14 6223 37457 30 _ _ (1053097 / 50000) (2106197 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1403232512 :
    ThetaLowerSegment 1403232512 1403363584 (35079552382277 / 25000)
      (140331383828873 / 100000) := by
  exact
    packedTile65536 1403232512 1403363584 14 6255 37459 30 _ _ (2106203 / 100000) (1053103 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1403363584 :
    ThetaLowerSegment 1403363584 1403494656 (140331383828873 / 100000)
      (140344473936453 / 100000) := by
  exact
    packedTile65536 1403363584 1403494656 14 6215 37461 30 _ _ (526553 / 25000) (421243 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1403494656 :
    ThetaLowerSegment 1403494656 1403625728 (140344473936453 / 100000)
      (140357521981743 / 100000) := by
  exact
    packedTile65536 1403494656 1403625728 14 6195 37463 30 _ _ (1053111 / 50000) (84249 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1403625728 :
    ThetaLowerSegment 1403625728 1403756800 (140357521981743 / 100000)
      (35092697282703 / 25000) := by
  exact
    packedTile65536 1403625728 1403756800 14 6299 37464 30 _ _ (2106231 / 100000) (1053117 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1403756800 :
    ThetaLowerSegment 1403756800 1403887872 (35092697282703 / 25000) (35095946684463 / 25000) := by
  exact
    packedTile65536 1403756800 1403887872 14 6171 37466 30 _ _ (13164 / 625) (2106243 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1403887872 :
    ThetaLowerSegment 1403887872 1404018944 (35095946684463 / 25000) (70198459603301 / 50000) := by
  exact
    packedTile65536 1403887872 1404018944 14 6235 37468 30 _ _ (337 / 16) (2106253 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1404018944 :
    ThetaLowerSegment 1404018944 1404150016 (70198459603301 / 50000)
      (140410085431611 / 100000) := by
  exact
    packedTile65536 1404018944 1404150016 14 6251 37470 30 _ _ (2106259 / 100000) (1053131 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1404150016 :
    ThetaLowerSegment 1404150016 1404281088 (140410085431611 / 100000)
      (140423102167851 / 100000) := by
  exact
    packedTile65536 1404150016 1404281088 14 6180 37471 30 _ _ (526567 / 25000) (2106271 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1404281088 :
    ThetaLowerSegment 1404281088 1404412160 (140423102167851 / 100000)
      (28087231375779 / 20000) := by
  exact
    packedTile65536 1404281088 1404412160 14 6198 37473 30 _ _ (1053139 / 50000) (2106281 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1404412160 :
    ThetaLowerSegment 1404412160 1404543232 (28087231375779 / 20000) (70224680596049 / 50000) := by
  exact
    packedTile65536 1404412160 1404543232 14 6269 37475 30 _ _ (2106287 / 100000) (210629 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1404543232 :
    ThetaLowerSegment 1404543232 1404674304 (70224680596049 / 50000) (70231141659029 / 50000) := by
  exact
    packedTile65536 1404543232 1404674304 14 6135 37477 30 _ _ (263287 / 12500) (2106299 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1404674304 :
    ThetaLowerSegment 1404674304 1404805376 (70231141659029 / 50000) (1755942491069 / 1250) := by
  exact
    packedTile65536 1404674304 1404805376 14 6227 37478 30 _ _ (1053153 / 50000) (2106309 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1404805376 :
    ThetaLowerSegment 1404805376 1404936448 (1755942491069 / 1250) (28097668518239 / 20000) := by
  exact
    packedTile65536 1404805376 1404936448 14 6145 37480 30 _ _ (421263 / 20000) (1053159 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1404936448 :
    ThetaLowerSegment 1404936448 1405067520 (28097668518239 / 20000)
      (140501355460867 / 100000) := by
  exact
    packedTile65536 1404936448 1405067520 14 6178 37482 30 _ _ (526581 / 25000) (2106327 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1405067520 :
    ThetaLowerSegment 1405067520 1405198592 (140501355460867 / 100000)
      (140514383136657 / 100000) := by
  exact
    packedTile65536 1405067520 1405198592 14 6185 37484 30 _ _ (1053167 / 50000) (2106337 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1405198592 :
    ThetaLowerSegment 1405198592 1405329664 (140514383136657 / 100000)
      (35131926439033 / 25000) := by
  exact
    packedTile65536 1405198592 1405329664 14 6325 37485 30 _ _ (2106343 / 100000) (1053173 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1405329664 :
    ThetaLowerSegment 1405329664 1405460736 (35131926439033 / 25000) (35135183912401 / 25000) := by
  exact
    packedTile65536 1405329664 1405460736 14 6186 37487 30 _ _ (131647 / 6250) (421271 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1405460736 :
    ThetaLowerSegment 1405460736 1405591808 (35135183912401 / 25000) (14055380141309 / 10000) := by
  exact
    packedTile65536 1405460736 1405591808 14 6203 37489 30 _ _ (1053181 / 50000) (421273 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1405591808 :
    ThetaLowerSegment 1405591808 1405722880 (14055380141309 / 10000) (70283438882129 / 50000) := by
  exact
    packedTile65536 1405591808 1405722880 14 6208 37491 30 _ _ (2106371 / 100000) (1053187 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1405722880 :
    ThetaLowerSegment 1405722880 1405853952 (70283438882129 / 50000) (70289919160199 / 50000) := by
  exact
    packedTile65536 1405722880 1405853952 14 6153 37492 30 _ _ (105319 / 5000) (2106383 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1405853952 :
    ThetaLowerSegment 1405853952 1405985024 (70289919160199 / 50000) (70296457394759 / 50000) := by
  exact
    packedTile65536 1405853952 1405985024 14 6208 37494 30 _ _ (210639 / 10000) (2106393 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1405985024 :
    ThetaLowerSegment 1405985024 1406116096 (70296457394759 / 50000) (70303008295649 / 50000) := by
  exact
    packedTile65536 1405985024 1406116096 14 6220 37496 30 _ _ (2106399 / 100000) (1053201 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1406116096 :
    ThetaLowerSegment 1406116096 1406247168 (70303008295649 / 50000) (70309635055217 / 50000) := by
  exact
    packedTile65536 1406116096 1406247168 14 6292 37498 30 _ _ (263301 / 12500) (2106411 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1406247168 :
    ThetaLowerSegment 1406247168 1406378240 (70309635055217 / 50000) (17579054666169 / 12500) := by
  exact
    packedTile65536 1406247168 1406378240 14 6251 37499 30 _ _ (1053209 / 50000) (2106421 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1406378240 :
    ThetaLowerSegment 1406378240 1406509312 (17579054666169 / 12500)
      (140645499283179 / 100000) := by
  exact
    packedTile65536 1406378240 1406509312 14 6201 37501 30 _ _ (2106427 / 100000) (210643 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1406509312 :
    ThetaLowerSegment 1406509312 1406640384 (140645499283179 / 100000)
      (28131731216487 / 20000) := by
  exact
    packedTile65536 1406509312 1406640384 14 6246 37503 30 _ _ (526609 / 25000) (2106439 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1406640384 :
    ThetaLowerSegment 1406640384 1406771456 (28131731216487 / 20000) (28134368485627 / 20000) := by
  exact
    packedTile65536 1406640384 1406771456 14 6260 37505 30 _ _ (421289 / 20000) (131653 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1406771456 :
    ThetaLowerSegment 1406771456 1406902528 (28134368485627 / 20000) (28137039470567 / 20000) := by
  exact
    packedTile65536 1406771456 1406902528 14 6340 37506 30 _ _ (421291 / 20000) (1053229 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1406902528 :
    ThetaLowerSegment 1406902528 1407033600 (28137039470567 / 20000)
      (140698318517091 / 100000) := by
  exact
    packedTile65536 1406902528 1407033600 14 6229 37508 30 _ _ (65827 / 3125) (2106467 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1407033600 :
    ThetaLowerSegment 1407033600 1407164672 (140698318517091 / 100000)
      (70355654568041 / 50000) := by
  exact
    packedTile65536 1407033600 1407164672 14 6167 37510 30 _ _ (2106473 / 100000) (526619 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1407164672 :
    ThetaLowerSegment 1407164672 1407295744 (70355654568041 / 50000) (35181108131293 / 25000) := by
  exact
    packedTile65536 1407164672 1407295744 14 6230 37512 30 _ _ (2106483 / 100000) (1053243 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1407295744 :
    ThetaLowerSegment 1407295744 1407426816 (35181108131293 / 25000) (17592187386881 / 12500) := by
  exact
    packedTile65536 1407295744 1407426816 14 6203 37513 30 _ _ (526623 / 25000) (421299 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1407426816 :
    ThetaLowerSegment 1407426816 1407557888 (17592187386881 / 12500)
      (140750409839677 / 100000) := by
  exact
    packedTile65536 1407426816 1407557888 14 6129 37515 30 _ _ (2106501 / 100000) (263313 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1407557888 :
    ThetaLowerSegment 1407557888 1407688960 (140750409839677 / 100000)
      (17595432986043 / 12500) := by
  exact
    packedTile65536 1407557888 1407688960 14 6197 37517 30 _ _ (2106511 / 100000) (1053257 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1407688960 :
    ThetaLowerSegment 1407688960 1407820032 (17595432986043 / 12500) (8798538694109 / 6250) := by
  exact
    packedTile65536 1407688960 1407820032 14 6245 37519 30 _ _ (52663 / 2500) (2106523 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1407820032 :
    ThetaLowerSegment 1407820032 1407951104 (8798538694109 / 6250) (28157939708861 / 20000) := by
  exact
    packedTile65536 1407820032 1407951104 14 6209 37520 30 _ _ (2106529 / 100000) (526633 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1407951104 :
    ThetaLowerSegment 1407951104 1408082176 (28157939708861 / 20000) (35200740855097 / 25000) := by
  exact
    packedTile65536 1407951104 1408082176 14 6297 37522 30 _ _ (2106539 / 100000) (1053271 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1408082176 :
    ThetaLowerSegment 1408082176 1408213248 (35200740855097 / 25000) (35204049188731 / 25000) := by
  exact
    packedTile65536 1408082176 1408213248 14 6282 37524 30 _ _ (526637 / 25000) (2106551 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1408213248 :
    ThetaLowerSegment 1408213248 1408344320 (35204049188731 / 25000)
      (140829192105057 / 100000) := by
  exact
    packedTile65536 1408213248 1408344320 14 6169 37526 30 _ _ (2106557 / 100000) (13166 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1408344320 :
    ThetaLowerSegment 1408344320 1408475392 (140829192105057 / 100000)
      (17605279759311 / 12500) := by
  exact
    packedTile65536 1408344320 1408475392 14 6193 37527 30 _ _ (2106567 / 100000) (210657 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1408475392 :
    ThetaLowerSegment 1408475392 1408606464 (17605279759311 / 12500) (17606923941879 / 12500) := by
  exact
    packedTile65536 1408475392 1408606464 14 6244 37529 30 _ _ (131661 / 6250) (2106579 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1408606464 :
    ThetaLowerSegment 1408606464 1408737536 (17606923941879 / 12500)
      (140868568224207 / 100000) := by
  exact
    packedTile65536 1408606464 1408737536 14 6255 37531 30 _ _ (421317 / 20000) (526647 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1408737536 :
    ThetaLowerSegment 1408737536 1408868608 (140868568224207 / 100000)
      (140881795527933 / 100000) := by
  exact
    packedTile65536 1408737536 1408868608 14 6279 37533 30 _ _ (1053297 / 50000) (2106597 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1408868608 :
    ThetaLowerSegment 1408868608 1408999680 (140881795527933 / 100000)
      (140894734289701 / 100000) := by
  exact
    packedTile65536 1408868608 1408999680 14 6142 37534 30 _ _ (526651 / 25000) (2106607 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1408999680 :
    ThetaLowerSegment 1408999680 1409130752 (140894734289701 / 100000)
      (70453945043943 / 50000) := by
  exact
    packedTile65536 1408999680 1409130752 14 6245 37536 30 _ _ (2106613 / 100000) (263327 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1409130752 :
    ThetaLowerSegment 1409130752 1409261824 (70453945043943 / 50000) (70460483998631 / 50000) := by
  exact
    packedTile65536 1409130752 1409261824 14 6208 37538 30 _ _ (1053311 / 50000) (16853 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1409261824 :
    ThetaLowerSegment 1409261824 1409392896 (70460483998631 / 50000) (70467037730783 / 50000) := by
  exact
    packedTile65536 1409261824 1409392896 14 6222 37540 30 _ _ (263329 / 12500) (421327 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1409392896 :
    ThetaLowerSegment 1409392896 1409523968 (70467037730783 / 50000)
      (140947273567431 / 100000) := by
  exact
    packedTile65536 1409392896 1409523968 14 6265 37541 30 _ _ (2106641 / 100000) (526661 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1409523968 :
    ThetaLowerSegment 1409523968 1409655040 (140947273567431 / 100000)
      (140960393783631 / 100000) := by
  exact
    packedTile65536 1409523968 1409655040 14 6228 37543 30 _ _ (42133 / 2000) (2106653 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1409655040 :
    ThetaLowerSegment 1409655040 1409786112 (140960393783631 / 100000)
      (140973581475231 / 100000) := by
  exact
    packedTile65536 1409655040 1409786112 14 6260 37545 30 _ _ (105333 / 5000) (2106663 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1409786112 :
    ThetaLowerSegment 1409786112 1409917184 (140973581475231 / 100000) (8811660568101 / 6250) := by
  exact
    packedTile65536 1409786112 1409917184 14 6165 37547 30 _ _ (2106669 / 100000) (131667 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1409917184 :
    ThetaLowerSegment 1409917184 1410048256 (8811660568101 / 6250) (4406232132879 / 3125) := by
  exact
    packedTile65536 1409917184 1410048256 14 6104 37548 30 _ _ (1053339 / 50000) (2106681 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1410048256 :
    ThetaLowerSegment 1410048256 1410179328 (4406232132879 / 3125) (141012584512443 / 100000) := by
  exact
    packedTile65536 1410048256 1410179328 14 6245 37550 30 _ _ (2106687 / 100000) (210669 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1410179328 :
    ThetaLowerSegment 1410179328 1410310400 (141012584512443 / 100000)
      (141025776649057 / 100000) := by
  exact
    packedTile65536 1410179328 1410310400 14 6262 37552 30 _ _ (2106697 / 100000) (21067 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1410310400 :
    ThetaLowerSegment 1410310400 1410441472 (141025776649057 / 100000)
      (141038895107319 / 100000) := by
  exact
    packedTile65536 1410310400 1410441472 14 6227 37554 30 _ _ (1053353 / 50000) (2106709 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1410441472 :
    ThetaLowerSegment 1410441472 1410572544 (141038895107319 / 100000)
      (141051935673169 / 100000) := by
  exact
    packedTile65536 1410441472 1410572544 14 6190 37555 30 _ _ (421343 / 20000) (1053359 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1410572544 :
    ThetaLowerSegment 1410572544 1410703616 (141051935673169 / 100000)
      (141065060569919 / 100000) := by
  exact
    packedTile65536 1410572544 1410703616 14 6230 37557 30 _ _ (84269 / 4000) (263341 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1410703616 :
    ThetaLowerSegment 1410703616 1410834688 (141065060569919 / 100000) (5643125651253 / 4000) := by
  exact
    packedTile65536 1410703616 1410834688 14 6209 37559 30 _ _ (1053367 / 50000) (2106737 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1410834688 :
    ThetaLowerSegment 1410834688 1410965760 (5643125651253 / 4000) (141091017694541 / 100000) := by
  exact
    packedTile65536 1410834688 1410965760 14 6112 37561 30 _ _ (2106743 / 100000) (1053373 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1410965760 :
    ThetaLowerSegment 1410965760 1411096832 (141091017694541 / 100000)
      (141104113271189 / 100000) := by
  exact
    packedTile65536 1410965760 1411096832 14 6216 37562 30 _ _ (2106753 / 100000) (526689 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1411096832 :
    ThetaLowerSegment 1411096832 1411227904 (141104113271189 / 100000)
      (141117248932259 / 100000) := by
  exact
    packedTile65536 1411096832 1411227904 14 6235 37564 30 _ _ (1053381 / 50000) (421353 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1411227904 :
    ThetaLowerSegment 1411227904 1411358976 (141117248932259 / 100000)
      (28226064710617 / 20000) := by
  exact
    packedTile65536 1411227904 1411358976 14 6206 37566 30 _ _ (2106771 / 100000) (1053387 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1411358976 :
    ThetaLowerSegment 1411358976 1411490048 (28226064710617 / 20000) (28228678803241 / 20000) := by
  exact
    packedTile65536 1411358976 1411490048 14 6204 37568 30 _ _ (105339 / 5000) (2106783 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1411490048 :
    ThetaLowerSegment 1411490048 1411621120 (28228678803241 / 20000) (5646266081827 / 4000) := by
  exact
    packedTile65536 1411490048 1411621120 14 6293 37569 30 _ _ (210679 / 10000) (2106793 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1411621120 :
    ThetaLowerSegment 1411621120 1411752192 (5646266081827 / 4000) (35292461731953 / 25000) := by
  exact
    packedTile65536 1411621120 1411752192 14 6263 37571 30 _ _ (2106799 / 100000) (1053401 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1411752192 :
    ThetaLowerSegment 1411752192 1411883264 (35292461731953 / 25000) (35295689888511 / 25000) := by
  exact
    packedTile65536 1411752192 1411883264 14 6129 37573 30 _ _ (263351 / 12500) (2106811 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1411883264 :
    ThetaLowerSegment 1411883264 1412014336 (35295689888511 / 25000) (3529896704391 / 2500) := by
  exact
    packedTile65536 1411883264 1412014336 14 6222 37575 30 _ _ (1053409 / 50000) (2106821 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1412014336 :
    ThetaLowerSegment 1412014336 1412145408 (3529896704391 / 2500) (17651109992399 / 12500) := by
  exact
    packedTile65536 1412014336 1412145408 14 6176 37576 30 _ _ (2106827 / 100000) (210683 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1412145408 :
    ThetaLowerSegment 1412145408 1412276480 (17651109992399 / 12500) (35305469252619 / 25000) := by
  exact
    packedTile65536 1412145408 1412276480 14 6169 37578 30 _ _ (526709 / 25000) (2106839 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1412276480 :
    ThetaLowerSegment 1412276480 1412342016 (35305469252619 / 25000)
      (141228452473721 / 100000) := by
  exact
    packedTile65536 1412276480 1412342016 13 3121 37580 30 _ _ (421369 / 20000) (65839 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1412342016 :
    ThetaLowerSegment 1412342016 1412407552 (141228452473721 / 100000)
      (141235032166271 / 100000) := by
  exact
    packedTile65536 1412342016 1412407552 13 3123 37581 30 _ _ (42137 / 2000) (2106853 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1412407552 :
    ThetaLowerSegment 1412407552 1412473088 (141235032166271 / 100000)
      (141241542348221 / 100000) := by
  exact
    packedTile65536 1412407552 1412473088 13 3090 37582 30 _ _ (421371 / 20000) (1053429 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1412473088 :
    ThetaLowerSegment 1412473088 1412538624 (141241542348221 / 100000)
      (70624103171619 / 50000) := by
  exact
    packedTile65536 1412473088 1412538624 13 3163 37582 30 _ _ (2106859 / 100000) (1053431 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1412538624 :
    ThetaLowerSegment 1412538624 1412669696 (70624103171619 / 50000) (14126130682359 / 10000) := by
  exact
    packedTile65536 1412538624 1412669696 14 6218 37583 30 _ _ (131679 / 6250) (2106867 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1412669696 :
    ThetaLowerSegment 1412669696 1412800768 (14126130682359 / 10000) (17659294599369 / 12500) := by
  exact
    packedTile65536 1412669696 1412800768 14 6194 37585 30 _ _ (2106873 / 100000) (526719 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1412800768 :
    ThetaLowerSegment 1412800768 1412866304 (17659294599369 / 12500) (17660135245287 / 12500) := by
  exact
    packedTile65536 1412800768 1412866304 13 3192 37587 30 _ _ (1053441 / 50000) (421377 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1412866304 :
    ThetaLowerSegment 1412866304 1412997376 (17660135245287 / 12500) (2825884663019 / 2000) := by
  exact
    packedTile65536 1412866304 1412997376 14 6242 37588 30 _ _ (2106887 / 100000) (210689 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1412997376 :
    ThetaLowerSegment 1412997376 1413128448 (2825884663019 / 2000) (70653634258251 / 50000) := by
  exact
    packedTile65536 1412997376 1413128448 14 6187 37589 30 _ _ (131681 / 6250) (2106899 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1413128448 :
    ThetaLowerSegment 1413128448 1413259520 (70653634258251 / 50000) (70660264691433 / 50000) := by
  exact
    packedTile65536 1413128448 1413259520 14 6294 37591 30 _ _ (1053453 / 50000) (2106909 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1413259520 :
    ThetaLowerSegment 1413259520 1413390592 (70660264691433 / 50000)
      (141333623859591 / 100000) := by
  exact
    packedTile65536 1413259520 1413390592 14 6215 37593 30 _ _ (421383 / 20000) (1053459 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1413390592 :
    ThetaLowerSegment 1413390592 1413521664 (141333623859591 / 100000)
      (141346884839247 / 100000) := by
  exact
    packedTile65536 1413390592 1413521664 14 6294 37595 30 _ _ (526731 / 25000) (2106927 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1413521664 :
    ThetaLowerSegment 1413521664 1413652736 (141346884839247 / 100000)
      (141359812986271 / 100000) := by
  exact
    packedTile65536 1413521664 1413652736 14 6136 37596 30 _ _ (1053467 / 50000) (2106937 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1413652736 :
    ThetaLowerSegment 1413652736 1413783808 (141359812986271 / 100000)
      (14137281914541 / 10000) := by
  exact
    packedTile65536 1413652736 1413783808 14 6173 37598 30 _ _ (2106943 / 100000) (1053473 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1413783808 :
    ThetaLowerSegment 1413783808 1413914880 (14137281914541 / 10000) (70693039097173 / 50000) := by
  exact
    packedTile65536 1413783808 1413914880 14 6293 37600 30 _ _ (263369 / 12500) (421391 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1413914880 :
    ThetaLowerSegment 1413914880 1414045952 (70693039097173 / 50000) (70699612815493 / 50000) := by
  exact
    packedTile65536 1413914880 1414045952 14 6240 37602 30 _ _ (2106961 / 100000) (526741 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1414045952 :
    ThetaLowerSegment 1414045952 1414177024 (70699612815493 / 50000) (70706135997709 / 50000) := by
  exact
    packedTile65536 1414045952 1414177024 14 6192 37603 30 _ _ (2106971 / 100000) (1053487 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1414177024 :
    ThetaLowerSegment 1414177024 1414308096 (70706135997709 / 50000) (70712734005579 / 50000) := by
  exact
    packedTile65536 1414177024 1414308096 14 6263 37605 30 _ _ (105349 / 5000) (2106983 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1414308096 :
    ThetaLowerSegment 1414308096 1414439168 (70712734005579 / 50000) (70719299383303 / 50000) := by
  exact
    packedTile65536 1414308096 1414439168 14 6232 37607 30 _ _ (2106989 / 100000) (131687 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1414439168 :
    ThetaLowerSegment 1414439168 1414570240 (70719299383303 / 50000) (70725887966049 / 50000) := by
  exact
    packedTile65536 1414439168 1414570240 14 6254 37609 30 _ _ (1053499 / 50000) (2107001 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1414570240 :
    ThetaLowerSegment 1414570240 1414701312 (70725887966049 / 50000) (70732474473057 / 50000) := by
  exact
    packedTile65536 1414570240 1414701312 14 6252 37610 30 _ _ (65844 / 3125) (2107011 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1414701312 :
    ThetaLowerSegment 1414701312 1414832384 (70732474473057 / 50000) (28295607968547 / 20000) := by
  exact
    packedTile65536 1414701312 1414832384 14 6213 37612 30 _ _ (2107017 / 100000) (105351 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1414832384 :
    ThetaLowerSegment 1414832384 1414963456 (28295607968547 / 20000) (28298243858073 / 20000) := by
  exact
    packedTile65536 1414832384 1414963456 14 6255 37614 30 _ _ (1053513 / 50000) (2107029 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1414963456 :
    ThetaLowerSegment 1414963456 1415094528 (28298243858073 / 20000) (14150435665359 / 10000) := by
  exact
    packedTile65536 1414963456 1415094528 14 6235 37616 30 _ _ (421407 / 20000) (1053519 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1415094528 :
    ThetaLowerSegment 1415094528 1415225600 (14150435665359 / 10000) (28303463417477 / 20000) := by
  exact
    packedTile65536 1415094528 1415225600 14 6151 37617 30 _ _ (421409 / 20000) (263381 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1415225600 :
    ThetaLowerSegment 1415225600 1415356672 (28303463417477 / 20000)
      (141530414535049 / 100000) := by
  exact
    packedTile65536 1415225600 1415356672 14 6216 37619 30 _ _ (1053527 / 50000) (2107057 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1415356672 :
    ThetaLowerSegment 1415356672 1415487744 (141530414535049 / 100000)
      (141543558394043 / 100000) := by
  exact
    packedTile65536 1415356672 1415487744 14 6238 37621 30 _ _ (2107063 / 100000) (1053533 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1415487744 :
    ThetaLowerSegment 1415487744 1415618816 (141543558394043 / 100000) (1769458541897 / 1250) := by
  exact
    packedTile65536 1415487744 1415618816 14 6229 37622 30 _ _ (2107073 / 100000) (526769 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1415618816 :
    ThetaLowerSegment 1415618816 1415749888 (1769458541897 / 1250) (70784872576539 / 50000) := by
  exact
    packedTile65536 1415618816 1415749888 14 6199 37624 30 _ _ (1053541 / 50000) (421417 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1415749888 :
    ThetaLowerSegment 1415749888 1415880960 (70784872576539 / 50000) (70791320274999 / 50000) := by
  exact
    packedTile65536 1415749888 1415880960 14 6120 37626 30 _ _ (2107091 / 100000) (1053547 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1415880960 :
    ThetaLowerSegment 1415880960 1416012032 (70791320274999 / 50000) (70797794339749 / 50000) := by
  exact
    packedTile65536 1415880960 1416012032 14 6145 37628 30 _ _ (21071 / 1000) (2107103 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1416012032 :
    ThetaLowerSegment 1416012032 1416143104 (70797794339749 / 50000) (70804429629139 / 50000) := by
  exact
    packedTile65536 1416012032 1416143104 14 6298 37629 30 _ _ (210711 / 10000) (2107113 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1416143104 :
    ThetaLowerSegment 1416143104 1416274176 (70804429629139 / 50000)
      (141621874932341 / 100000) := by
  exact
    packedTile65536 1416143104 1416274176 14 6177 37631 30 _ _ (2107119 / 100000) (1053561 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1416274176 :
    ThetaLowerSegment 1416274176 1416405248 (141621874932341 / 100000)
      (141635154052997 / 100000) := by
  exact
    packedTile65536 1416274176 1416405248 14 6302 37633 30 _ _ (263391 / 12500) (2107131 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1416405248 :
    ThetaLowerSegment 1416405248 1416536320 (141635154052997 / 100000)
      (17706025970839 / 12500) := by
  exact
    packedTile65536 1416405248 1416536320 14 6195 37635 30 _ _ (2107137 / 100000) (105357 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1416536320 :
    ThetaLowerSegment 1416536320 1416667392 (17706025970839 / 12500) (70830617074733 / 50000) := by
  exact
    packedTile65536 1416536320 1416667392 14 6182 37636 30 _ _ (2107147 / 100000) (42143 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1416667392 :
    ThetaLowerSegment 1416667392 1416798464 (70830617074733 / 50000) (566697522783 / 400) := by
  exact
    packedTile65536 1416667392 1416798464 14 6239 37638 30 _ _ (526789 / 25000) (2107159 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1416798464 :
    ThetaLowerSegment 1416798464 1416929536 (566697522783 / 400) (708436909519 / 500) := by
  exact
    packedTile65536 1416798464 1416929536 14 6170 37640 30 _ _ (421433 / 20000) (65849 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1416929536 :
    ThetaLowerSegment 1416929536 1417060608 (708436909519 / 500) (4428137105679 / 3125) := by
  exact
    packedTile65536 1416929536 1417060608 14 6172 37642 30 _ _ (1053587 / 50000) (2107177 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1417060608 :
    ThetaLowerSegment 1417060608 1417191680 (4428137105679 / 3125) (1771419545041 / 1250) := by
  exact
    packedTile65536 1417060608 1417191680 14 6253 37643 30 _ _ (131699 / 6250) (2107187 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1417191680 :
    ThetaLowerSegment 1417191680 1417322752 (1771419545041 / 1250) (70863269848887 / 50000) := by
  exact
    packedTile65536 1417191680 1417322752 14 6158 37645 30 _ _ (2107193 / 100000) (526799 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1417322752 :
    ThetaLowerSegment 1417322752 1417339136 (70863269848887 / 50000) (3543204214123 / 2500) := by
  exact
    packedTile65536 1417322752 1417339136 11 773 37647 30 _ _ (1053601 / 50000) (421441 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1417339136 :
    ThetaLowerSegment 1417339136 1417341184 (3543204214123 / 2500) (141728394035641 / 100000) := by
  exact
    packedTile65536 1417339136 1417341184 8 107 37647 30 _ _ (2107203 / 100000) (1053603 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_1385341184_1417341184 :
    ThetaLowerSegment 1385341184 1417341184 (34632366098693 / 25000)
      (141728394035641 / 100000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1385341184 cell1385472256)
                  (ThetaLowerSegment.join cell1385603328 cell1385734400))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1385865472 cell1385996544)
                  (ThetaLowerSegment.join cell1386127616 cell1386258688)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1386389760 cell1386520832)
                  (ThetaLowerSegment.join cell1386651904 cell1386782976))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1386914048 cell1387045120)
                  (ThetaLowerSegment.join cell1387176192 cell1387307264))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1387438336 cell1387569408)
                  (ThetaLowerSegment.join cell1387700480 cell1387831552))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1387962624 cell1388093696)
                  (ThetaLowerSegment.join cell1388224768 cell1388355840)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1388486912 cell1388617984)
                  (ThetaLowerSegment.join cell1388749056 cell1388880128))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1389011200 cell1389142272)
                  (ThetaLowerSegment.join cell1389207808 cell1389338880)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1389469952 cell1389601024)
                  (ThetaLowerSegment.join cell1389732096 cell1389863168))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1389994240 cell1390125312)
                  (ThetaLowerSegment.join cell1390256384 cell1390387456)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1390518528 cell1390649600)
                  (ThetaLowerSegment.join cell1390780672 cell1390911744))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1391042816 cell1391173888)
                  (ThetaLowerSegment.join cell1391304960 cell1391436032))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1391567104 cell1391698176)
                  (ThetaLowerSegment.join cell1391829248 cell1391960320))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1392091392 cell1392222464)
                  (ThetaLowerSegment.join cell1392353536 cell1392484608)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1392615680 cell1392746752)
                  (ThetaLowerSegment.join cell1392877824 cell1393008896))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1393139968 cell1393271040)
                  (ThetaLowerSegment.join cell1393402112 cell1393533184))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1393664256 cell1393795328)
                  (ThetaLowerSegment.join cell1393926400 cell1394057472))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1394188544 cell1394319616)
                  (ThetaLowerSegment.join cell1394450688 cell1394581760)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1394712832 cell1394843904)
                  (ThetaLowerSegment.join cell1394974976 cell1395106048))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1395237120 cell1395368192)
                  (ThetaLowerSegment.join cell1395499264 cell1395630336))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1395761408 cell1395892480)
                  (ThetaLowerSegment.join cell1396023552 cell1396154624))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1396285696 cell1396416768)
                  (ThetaLowerSegment.join cell1396547840 cell1396678912)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1396809984 cell1396941056)
                  (ThetaLowerSegment.join cell1397072128 cell1397203200))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1397334272 cell1397465344)
                  (ThetaLowerSegment.join cell1397596416 cell1397727488)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1397858560 cell1397989632)
                  (ThetaLowerSegment.join cell1398120704 cell1398251776))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1398382848 cell1398513920)
                  (ThetaLowerSegment.join cell1398644992 cell1398776064)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1398907136 cell1399038208)
                  (ThetaLowerSegment.join cell1399169280 cell1399300352))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1399431424 cell1399562496)
                  (ThetaLowerSegment.join cell1399693568 cell1399824640))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1399955712 cell1400086784)
                  (ThetaLowerSegment.join cell1400217856 cell1400348928))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1400480000 cell1400611072)
                  (ThetaLowerSegment.join cell1400742144 cell1400873216)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1401004288 cell1401135360)
                  (ThetaLowerSegment.join cell1401266432 cell1401397504))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1401528576 cell1401659648)
                  (ThetaLowerSegment.join cell1401790720 cell1401921792)))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1402052864 cell1402183936)
                  (ThetaLowerSegment.join cell1402315008 cell1402446080))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1402577152 cell1402708224)
                  (ThetaLowerSegment.join cell1402839296 cell1402970368)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1403101440 cell1403232512)
                  (ThetaLowerSegment.join cell1403363584 cell1403494656))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1403625728 cell1403756800)
                  (ThetaLowerSegment.join cell1403887872 cell1404018944))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1404150016 cell1404281088)
                  (ThetaLowerSegment.join cell1404412160 cell1404543232))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1404674304 cell1404805376)
                  (ThetaLowerSegment.join cell1404936448 cell1405067520)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1405198592 cell1405329664)
                  (ThetaLowerSegment.join cell1405460736 cell1405591808))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1405722880 cell1405853952)
                  (ThetaLowerSegment.join cell1405985024 cell1406116096)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1406247168 cell1406378240)
                  (ThetaLowerSegment.join cell1406509312 cell1406640384))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1406771456 cell1406902528)
                  (ThetaLowerSegment.join cell1407033600 cell1407164672)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1407295744 cell1407426816)
                  (ThetaLowerSegment.join cell1407557888 cell1407688960))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1407820032 cell1407951104)
                  (ThetaLowerSegment.join cell1408082176 cell1408213248))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1408344320 cell1408475392)
                  (ThetaLowerSegment.join cell1408606464 cell1408737536))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1408868608 cell1408999680)
                  (ThetaLowerSegment.join cell1409130752 cell1409261824)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1409392896 cell1409523968)
                  (ThetaLowerSegment.join cell1409655040 cell1409786112))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1409917184 cell1410048256)
                  (ThetaLowerSegment.join cell1410179328 cell1410310400))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1410441472 cell1410572544)
                  (ThetaLowerSegment.join cell1410703616 cell1410834688))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1410965760 cell1411096832)
                  (ThetaLowerSegment.join cell1411227904 cell1411358976)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1411490048 cell1411621120)
                  (ThetaLowerSegment.join cell1411752192 cell1411883264))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1412014336 cell1412145408)
                  (ThetaLowerSegment.join cell1412276480 cell1412342016))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1412407552 cell1412473088)
                  (ThetaLowerSegment.join cell1412538624 cell1412669696))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1412800768 cell1412866304)
                  (ThetaLowerSegment.join cell1412997376 cell1413128448)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1413259520 cell1413390592)
                  (ThetaLowerSegment.join cell1413521664 cell1413652736))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1413783808 cell1413914880)
                  (ThetaLowerSegment.join cell1414045952 cell1414177024)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1414308096 cell1414439168)
                  (ThetaLowerSegment.join cell1414570240 cell1414701312))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1414832384 cell1414963456)
                  (ThetaLowerSegment.join cell1415094528 cell1415225600)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1415356672 cell1415487744)
                  (ThetaLowerSegment.join cell1415618816 cell1415749888))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1415880960 cell1416012032)
                  (ThetaLowerSegment.join cell1416143104 cell1416274176))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1416405248 cell1416536320)
                  (ThetaLowerSegment.join cell1416667392 cell1416798464))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1416929536 cell1417060608)
                  (ThetaLowerSegment.join cell1417191680 cell1417322752)))
              cell1417339136)))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
