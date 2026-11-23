/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis65536

/-! # Direct theta estimate up to 1353341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell1321341184 :
    ThetaLowerSegment 1321341184 1321472256 (26425827251023 / 20000) (26428428126319 / 20000) := by
  exact
    packedTile65536 1321341184 1321472256 14 6192 36350 30 _ _ (210019 / 10000) (2100193 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1321472256 :
    ThetaLowerSegment 1321472256 1321537792 (26428428126319 / 20000) (26429771414239 / 20000) := by
  exact
    packedTile65536 1321472256 1321537792 13 3198 36352 30 _ _ (10501 / 500) (2100203 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1321537792 :
    ThetaLowerSegment 1321537792 1321668864 (26429771414239 / 20000) (6608107883473 / 5000) := by
  exact
    packedTile65536 1321537792 1321668864 14 6333 36352 30 _ _ (420041 / 20000) (131263 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1321668864 :
    ThetaLowerSegment 1321668864 1321799936 (6608107883473 / 5000) (26435053862341 / 20000) := by
  exact
    packedTile65536 1321668864 1321799936 14 6243 36354 30 _ _ (420043 / 20000) (1050109 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1321799936 :
    ThetaLowerSegment 1321799936 1321931008 (26435053862341 / 20000) (13218832641053 / 10000) := by
  exact
    packedTile65536 1321799936 1321931008 14 6217 36356 30 _ _ (84009 / 4000) (525057 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1321931008 :
    ThetaLowerSegment 1321931008 1322062080 (13218832641053 / 10000) (13220149487771 / 10000) := by
  exact
    packedTile65536 1321931008 1322062080 14 6270 36358 30 _ _ (1050117 / 50000) (2100237 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1322062080 :
    ThetaLowerSegment 1322062080 1322193152 (13220149487771 / 10000) (13221456889661 / 10000) := by
  exact
    packedTile65536 1322062080 1322193152 14 6225 36360 30 _ _ (525061 / 25000) (2100247 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1322193152 :
    ThetaLowerSegment 1322193152 1322324224 (13221456889661 / 10000) (66113772132911 / 50000) := by
  exact
    packedTile65536 1322193152 1322324224 14 6178 36361 30 _ _ (1050127 / 50000) (2100257 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1322324224 :
    ThetaLowerSegment 1322324224 1322455296 (66113772132911 / 50000) (66120294502763 / 50000) := by
  exact
    packedTile65536 1322324224 1322455296 14 6211 36363 30 _ _ (262533 / 12500) (2100267 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1322455296 :
    ThetaLowerSegment 1322455296 1322586368 (66120294502763 / 50000) (6612687991189 / 5000) := by
  exact
    packedTile65536 1322455296 1322586368 14 6271 36365 30 _ _ (1050137 / 50000) (2100277 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1322586368 :
    ThetaLowerSegment 1322586368 1322717440 (6612687991189 / 5000) (16533349535821 / 12500) := by
  exact
    packedTile65536 1322586368 1322717440 14 6207 36367 30 _ _ (525071 / 25000) (2100287 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1322717440 :
    ThetaLowerSegment 1322717440 1322848512 (16533349535821 / 12500) (16534983564553 / 12500) := by
  exact
    packedTile65536 1322717440 1322848512 14 6224 36369 30 _ _ (1050147 / 50000) (2100297 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1322848512 :
    ThetaLowerSegment 1322848512 1322979584 (16534983564553 / 12500) (16536627052433 / 12500) := by
  exact
    packedTile65536 1322848512 1322979584 14 6260 36370 30 _ _ (131269 / 6250) (2100307 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1322979584 :
    ThetaLowerSegment 1322979584 1323110656 (16536627052433 / 12500) (33076491738897 / 25000) := by
  exact
    packedTile65536 1322979584 1323110656 14 6166 36372 30 _ _ (1050157 / 50000) (2100317 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1323110656 :
    ThetaLowerSegment 1323110656 1323176192 (33076491738897 / 25000) (33078119489997 / 25000) := by
  exact
    packedTile65536 1323110656 1323176192 13 3100 36374 30 _ _ (525081 / 25000) (2100327 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1323176192 :
    ThetaLowerSegment 1323176192 1323241728 (33078119489997 / 25000)
      (132318919669031 / 100000) := by
  exact
    packedTile65536 1323176192 1323241728 13 3067 36375 30 _ _ (2100329 / 100000) (525083 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1323241728 :
    ThetaLowerSegment 1323241728 1323307264 (132318919669031 / 100000)
      (132325479012113 / 100000) := by
  exact
    packedTile65536 1323241728 1323307264 13 3123 36376 30 _ _ (1050167 / 50000) (2100337 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1323307264 :
    ThetaLowerSegment 1323307264 1323372800 (132325479012113 / 100000)
      (132331994260589 / 100000) := by
  exact
    packedTile65536 1323307264 1323372800 13 3102 36377 30 _ _ (1050169 / 50000) (2100341 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1323372800 :
    ThetaLowerSegment 1323372800 1323438336 (132331994260589 / 100000)
      (66169247411087 / 50000) := by
  exact
    packedTile65536 1323372800 1323438336 13 3095 36378 30 _ _ (2100343 / 100000) (1050173 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1323438336 :
    ThetaLowerSegment 1323438336 1323503872 (66169247411087 / 50000) (66172477746311 / 50000) := by
  exact
    packedTile65536 1323438336 1323503872 13 3076 36379 30 _ _ (525087 / 25000) (2100351 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1323503872 :
    ThetaLowerSegment 1323503872 1323569408 (66172477746311 / 50000)
      (132351598909161 / 100000) := by
  exact
    packedTile65536 1323503872 1323569408 13 3163 36379 30 _ _ (2100353 / 100000) (525089 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1323569408 :
    ThetaLowerSegment 1323569408 1323634944 (132351598909161 / 100000)
      (132358089015381 / 100000) := by
  exact
    packedTile65536 1323569408 1323634944 13 3090 36380 30 _ _ (1050179 / 50000) (2100361 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1323634944 :
    ThetaLowerSegment 1323634944 1323700480 (132358089015381 / 100000)
      (33091171563891 / 25000) := by
  exact
    packedTile65536 1323634944 1323700480 13 3141 36381 30 _ _ (2100363 / 100000) (1050183 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1323700480 :
    ThetaLowerSegment 1323700480 1323766016 (33091171563891 / 25000) (33092820877863 / 25000) := by
  exact
    packedTile65536 1323700480 1323766016 13 3141 36382 30 _ _ (131273 / 6250) (2100371 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1323766016 :
    ThetaLowerSegment 1323766016 1323831552 (33092820877863 / 25000) (4136805558274 / 3125) := by
  exact
    packedTile65536 1323766016 1323831552 13 3092 36383 30 _ _ (2100373 / 100000) (262547 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1323831552 :
    ThetaLowerSegment 1323831552 1323897088 (4136805558274 / 3125) (66192219081703 / 50000) := by
  exact
    packedTile65536 1323831552 1323897088 13 3171 36384 30 _ _ (1050189 / 50000) (2100381 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1323897088 :
    ThetaLowerSegment 1323897088 1323962624 (66192219081703 / 50000) (26478216334967 / 20000) := by
  exact
    packedTile65536 1323897088 1323962624 13 3163 36385 30 _ _ (2100383 / 100000) (1050193 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1323962624 :
    ThetaLowerSegment 1323962624 1324028160 (26478216334967 / 20000)
      (132397636985783 / 100000) := by
  exact
    packedTile65536 1323962624 1324028160 13 3121 36386 30 _ _ (525097 / 25000) (2100391 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1324028160 :
    ThetaLowerSegment 1324028160 1324093696 (132397636985783 / 100000)
      (33101054379263 / 25000) := by
  exact
    packedTile65536 1324028160 1324093696 13 3133 36387 30 _ _ (2100393 / 100000) (525099 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1324093696 :
    ThetaLowerSegment 1324093696 1324159232 (33101054379263 / 25000) (4137831203943 / 3125) := by
  exact
    packedTile65536 1324093696 1324159232 13 3038 36388 30 _ _ (1050199 / 50000) (2100401 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1324159232 :
    ThetaLowerSegment 1324159232 1324224768 (4137831203943 / 3125) (132417019458147 / 100000) := by
  exact
    packedTile65536 1324159232 1324224768 13 3057 36388 30 _ _ (2100403 / 100000) (1050203 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1324224768 :
    ThetaLowerSegment 1324224768 1324290304 (132417019458147 / 100000)
      (132423478212747 / 100000) := by
  exact
    packedTile65536 1324224768 1324290304 13 3075 36389 30 _ _ (262551 / 12500) (2100411 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1324290304 :
    ThetaLowerSegment 1324290304 1324355840 (132423478212747 / 100000)
      (16553762601867 / 12500) := by
  exact
    packedTile65536 1324290304 1324355840 13 3153 36390 30 _ _ (2100413 / 100000) (65638 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1324355840 :
    ThetaLowerSegment 1324355840 1324421376 (16553762601867 / 12500) (66218275599307 / 50000) := by
  exact
    packedTile65536 1324355840 1324421376 13 3071 36391 30 _ _ (1050209 / 50000) (2100421 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1324421376 :
    ThetaLowerSegment 1324421376 1324486912 (66218275599307 / 50000) (4138850560663 / 3125) := by
  exact
    packedTile65536 1324421376 1324486912 13 3174 36392 30 _ _ (2100423 / 100000) (1050213 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1324486912 :
    ThetaLowerSegment 1324486912 1324552448 (4138850560663 / 3125) (33112467499173 / 25000) := by
  exact
    packedTile65536 1324486912 1324552448 13 3167 36393 30 _ _ (525107 / 25000) (2100431 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1324552448 :
    ThetaLowerSegment 1324552448 1324617984 (33112467499173 / 25000)
      (132456438050683 / 100000) := by
  exact
    packedTile65536 1324552448 1324617984 13 3127 36394 30 _ _ (2100433 / 100000) (525109 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1324617984 :
    ThetaLowerSegment 1324617984 1324683520 (132456438050683 / 100000)
      (13246297251019 / 10000) := by
  exact
    packedTile65536 1324617984 1324683520 13 3111 36395 30 _ _ (2100437 / 100000) (52511 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1324683520 :
    ThetaLowerSegment 1324683520 1324749056 (13246297251019 / 10000) (66234702031797 / 50000) := by
  exact
    packedTile65536 1324683520 1324749056 13 3062 36396 30 _ _ (1050221 / 50000) (420089 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1324749056 :
    ThetaLowerSegment 1324749056 1324814592 (66234702031797 / 50000) (33118996716123 / 25000) := by
  exact
    packedTile65536 1324749056 1324814592 13 3134 36397 30 _ _ (2100447 / 100000) (42009 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1324814592 :
    ThetaLowerSegment 1324814592 1324880128 (33118996716123 / 25000) (8280160998901 / 6250) := by
  exact
    packedTile65536 1324814592 1324880128 13 3137 36398 30 _ _ (525113 / 25000) (420091 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1324880128 :
    ThetaLowerSegment 1324880128 1324945664 (8280160998901 / 6250) (66244583608241 / 50000) := by
  exact
    packedTile65536 1324880128 1324945664 13 3138 36398 30 _ _ (2100457 / 100000) (105023 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1324945664 :
    ThetaLowerSegment 1324945664 1325011200 (66244583608241 / 50000) (66247908639587 / 50000) := by
  exact
    packedTile65536 1324945664 1325011200 13 3166 36399 30 _ _ (1050231 / 50000) (420093 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1325011200 :
    ThetaLowerSegment 1325011200 1325076736 (66247908639587 / 50000)
      (132502255210529 / 100000) := by
  exact
    packedTile65536 1325011200 1325076736 13 3065 36400 30 _ _ (2100467 / 100000) (210047 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1325076736 :
    ThetaLowerSegment 1325076736 1325142272 (132502255210529 / 100000)
      (132508915807241 / 100000) := by
  exact
    packedTile65536 1325076736 1325142272 13 3171 36401 30 _ _ (262559 / 12500) (84019 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1325142272 :
    ThetaLowerSegment 1325142272 1325207808 (132508915807241 / 100000)
      (66257739898933 / 50000) := by
  exact
    packedTile65536 1325142272 1325207808 13 3125 36402 30 _ _ (2100477 / 100000) (13128 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1325207808 :
    ThetaLowerSegment 1325207808 1325273344 (66257739898933 / 50000) (1656525074943 / 1250) := by
  exact
    packedTile65536 1325207808 1325273344 13 3107 36403 30 _ _ (1050241 / 50000) (420097 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1325273344 :
    ThetaLowerSegment 1325273344 1325338880 (1656525074943 / 1250) (6626425875257 / 5000) := by
  exact
    packedTile65536 1325273344 1325338880 13 3100 36404 30 _ _ (2100487 / 100000) (210049 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1325338880 :
    ThetaLowerSegment 1325338880 1325404416 (6626425875257 / 5000) (33133774061521 / 25000) := by
  exact
    packedTile65536 1325338880 1325404416 13 3132 36405 30 _ _ (525123 / 25000) (420099 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1325404416 :
    ThetaLowerSegment 1325404416 1325469952 (33133774061521 / 25000) (3313540614769 / 2500) := by
  exact
    packedTile65536 1325404416 1325469952 13 3108 36406 30 _ _ (2100497 / 100000) (4201 / 200)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1325469952 :
    ThetaLowerSegment 1325469952 1325535488 (3313540614769 / 2500) (66274130038289 / 50000) := by
  exact
    packedTile65536 1325469952 1325535488 13 3159 36407 30 _ _ (1050251 / 50000) (420101 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1325535488 :
    ThetaLowerSegment 1325535488 1325601024 (66274130038289 / 50000) (66277377422111 / 50000) := by
  exact
    packedTile65536 1325535488 1325601024 13 3092 36407 30 _ _ (2100507 / 100000) (210051 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1325601024 :
    ThetaLowerSegment 1325601024 1325666560 (66277377422111 / 50000) (66280619562383 / 50000) := by
  exact
    packedTile65536 1325601024 1325666560 13 3087 36408 30 _ _ (65641 / 3125) (420103 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1325666560 :
    ThetaLowerSegment 1325666560 1325732096 (66280619562383 / 50000) (66283942580277 / 50000) := by
  exact
    packedTile65536 1325666560 1325732096 13 3164 36409 30 _ _ (2100517 / 100000) (52513 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1325732096 :
    ThetaLowerSegment 1325732096 1325797632 (66283942580277 / 50000) (3314361127269 / 2500) := by
  exact
    packedTile65536 1325732096 1325797632 13 3123 36410 30 _ _ (1050261 / 50000) (84021 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1325797632 :
    ThetaLowerSegment 1325797632 1325863168 (3314361127269 / 2500) (26516201847527 / 20000) := by
  exact
    packedTile65536 1325797632 1325863168 13 3125 36411 30 _ _ (2100527 / 100000) (210053 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1325863168 :
    ThetaLowerSegment 1325863168 1325928704 (26516201847527 / 20000) (66293782497443 / 50000) := by
  exact
    packedTile65536 1325863168 1325928704 13 3121 36412 30 _ _ (2100531 / 100000) (1050267 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1325928704 :
    ThetaLowerSegment 1325928704 1325994240 (66293782497443 / 50000) (66297034127171 / 50000) := by
  exact
    packedTile65536 1325928704 1325994240 13 3096 36413 30 _ _ (262567 / 12500) (2100539 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1325994240 :
    ThetaLowerSegment 1325994240 1326059776 (66297034127171 / 50000) (33150141832049 / 25000) := by
  exact
    packedTile65536 1325994240 1326059776 13 3094 36414 30 _ _ (2100541 / 100000) (65642 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1326059776 :
    ThetaLowerSegment 1326059776 1326125312 (33150141832049 / 25000) (13260713993663 / 10000) := by
  exact
    packedTile65536 1326059776 1326125312 13 3129 36415 30 _ _ (1050273 / 50000) (2100549 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1326125312 :
    ThetaLowerSegment 1326125312 1326190848 (13260713993663 / 10000)
      (132613716761811 / 100000) := by
  exact
    packedTile65536 1326125312 1326190848 13 3131 36416 30 _ _ (2100551 / 100000) (1050277 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1326190848 :
    ThetaLowerSegment 1326190848 1326256384 (132613716761811 / 100000)
      (132620280999311 / 100000) := by
  exact
    packedTile65536 1326190848 1326256384 13 3125 36416 30 _ _ (525139 / 25000) (2100559 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1326256384 :
    ThetaLowerSegment 1326256384 1326321920 (132620280999311 / 100000)
      (13262683264907 / 10000) := by
  exact
    packedTile65536 1326256384 1326321920 13 3119 36417 30 _ _ (2100561 / 100000) (525141 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1326321920 :
    ThetaLowerSegment 1326321920 1326387456 (13262683264907 / 10000) (66316731017683 / 50000) := by
  exact
    packedTile65536 1326321920 1326387456 13 3156 36418 30 _ _ (1050283 / 50000) (2100569 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1326387456 :
    ThetaLowerSegment 1326387456 1326452992 (66316731017683 / 50000) (33160005004507 / 25000) := by
  exact
    packedTile65536 1326387456 1326452992 13 3122 36419 30 _ _ (2100571 / 100000) (1050287 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1326452992 :
    ThetaLowerSegment 1326452992 1326518528 (33160005004507 / 25000) (33161650805803 / 25000) := by
  exact
    packedTile65536 1326452992 1326518528 13 3134 36420 30 _ _ (65643 / 3125) (2100579 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1326518528 :
    ThetaLowerSegment 1326518528 1326584064 (33161650805803 / 25000)
      (132653112923731 / 100000) := by
  exact
    packedTile65536 1326518528 1326584064 13 3099 36421 30 _ _ (2100581 / 100000) (262573 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1326584064 :
    ThetaLowerSegment 1326584064 1326649600 (132653112923731 / 100000)
      (132659658349707 / 100000) := by
  exact
    packedTile65536 1326584064 1326649600 13 3116 36422 30 _ _ (1050293 / 50000) (2100589 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1326649600 :
    ThetaLowerSegment 1326649600 1326715136 (132659658349707 / 100000)
      (132666149175897 / 100000) := by
  exact
    packedTile65536 1326649600 1326715136 13 3090 36423 30 _ _ (2100591 / 100000) (1050297 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1326715136 :
    ThetaLowerSegment 1326715136 1326780672 (132666149175897 / 100000)
      (132672679928861 / 100000) := by
  exact
    packedTile65536 1326715136 1326780672 13 3109 36424 30 _ _ (525149 / 25000) (2100599 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1326780672 :
    ThetaLowerSegment 1326780672 1326846208 (132672679928861 / 100000)
      (66339638958301 / 50000) := by
  exact
    packedTile65536 1326780672 1326846208 13 3141 36425 30 _ _ (2100601 / 100000) (525151 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1326846208 :
    ThetaLowerSegment 1326846208 1326911744 (66339638958301 / 50000) (8292856741973 / 6250) := by
  exact
    packedTile65536 1326846208 1326911744 13 3061 36425 30 _ _ (1050303 / 50000) (2100609 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1326911744 :
    ThetaLowerSegment 1326911744 1326977280 (8292856741973 / 6250) (26538467900099 / 20000) := by
  exact
    packedTile65536 1326911744 1326977280 13 3157 36426 30 _ _ (2100611 / 100000) (1050307 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1326977280 :
    ThetaLowerSegment 1326977280 1327042816 (26538467900099 / 20000) (2653976902103 / 2000) := by
  exact
    packedTile65536 1326977280 1327042816 13 3097 36427 30 _ _ (420123 / 20000) (1050309 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1327042816 :
    ThetaLowerSegment 1327042816 1327108352 (2653976902103 / 2000) (13270542424699 / 10000) := by
  exact
    packedTile65536 1327042816 1327108352 13 3132 36428 30 _ _ (105031 / 5000) (2100623 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1327108352 :
    ThetaLowerSegment 1327108352 1327173888 (13270542424699 / 10000) (13271212944199 / 10000) := by
  exact
    packedTile65536 1327108352 1327173888 13 3192 36429 30 _ _ (3361 / 160) (525157 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1327173888 :
    ThetaLowerSegment 1327173888 1327239424 (13271212944199 / 10000) (6635930914403 / 5000) := by
  exact
    packedTile65536 1327173888 1327239424 13 3089 36430 30 _ _ (210063 / 10000) (2100633 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1327239424 :
    ThetaLowerSegment 1327239424 1327304960 (6635930914403 / 5000) (5309004285983 / 4000) := by
  exact
    packedTile65536 1327239424 1327304960 13 3089 36431 30 _ _ (420127 / 20000) (1050319 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1327304960 :
    ThetaLowerSegment 1327304960 1327370496 (5309004285983 / 4000) (26546326347483 / 20000) := by
  exact
    packedTile65536 1327304960 1327370496 13 3106 36432 30 _ _ (13129 / 625) (2100643 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1327370496 :
    ThetaLowerSegment 1327370496 1327436032 (26546326347483 / 20000) (13273825927239 / 10000) := by
  exact
    packedTile65536 1327370496 1327436032 13 3155 36433 30 _ _ (420129 / 20000) (262581 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1327436032 :
    ThetaLowerSegment 1327436032 1327501568 (13273825927239 / 10000) (13274483010559 / 10000) := by
  exact
    packedTile65536 1327436032 1327501568 13 3128 36433 30 _ _ (42013 / 2000) (2100653 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1327501568 :
    ThetaLowerSegment 1327501568 1327567104 (13274483010559 / 10000) (265502776701 / 200) := by
  exact
    packedTile65536 1327501568 1327567104 13 3122 36434 30 _ _ (420131 / 20000) (1050329 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1327567104 :
    ThetaLowerSegment 1327567104 1327632640 (265502776701 / 200) (1659475304193 / 1250) := by
  exact
    packedTile65536 1327567104 1327632640 13 3159 36435 30 _ _ (105033 / 5000) (2100663 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1327632640 :
    ThetaLowerSegment 1327632640 1327698176 (1659475304193 / 1250) (829779035197 / 625) := by
  exact
    packedTile65536 1327632640 1327698176 13 3152 36436 30 _ _ (420133 / 20000) (525167 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1327698176 :
    ThetaLowerSegment 1327698176 1327763712 (829779035197 / 625) (13277124803733 / 10000) := by
  exact
    packedTile65536 1327698176 1327763712 13 3143 36437 30 _ _ (210067 / 10000) (2100673 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1327763712 :
    ThetaLowerSegment 1327763712 1327829248 (13277124803733 / 10000) (26555523876921 / 20000) := by
  exact
    packedTile65536 1327763712 1327829248 13 3033 36438 30 _ _ (84027 / 4000) (1050339 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1327829248 :
    ThetaLowerSegment 1327829248 1327894784 (26555523876921 / 20000) (26556845204641 / 20000) := by
  exact
    packedTile65536 1327829248 1327894784 13 3145 36439 30 _ _ (52517 / 2500) (2100683 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1327894784 :
    ThetaLowerSegment 1327894784 1327960320 (26556845204641 / 20000) (5311625492553 / 4000) := by
  exact
    packedTile65536 1327894784 1327960320 13 3052 36440 30 _ _ (420137 / 20000) (131293 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1327960320 :
    ThetaLowerSegment 1327960320 1328025856 (5311625492553 / 4000) (5311883877423 / 4000) := by
  exact
    packedTile65536 1327960320 1328025856 13 3075 36441 30 _ _ (210069 / 10000) (2100693 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1328025856 :
    ThetaLowerSegment 1328025856 1328091392 (5311883877423 / 4000) (132803531361297 / 100000) := by
  exact
    packedTile65536 1328025856 1328091392 13 3063 36442 30 _ _ (1050347 / 50000) (2100697 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1328091392 :
    ThetaLowerSegment 1328091392 1328156928 (132803531361297 / 100000)
      (132810148563147 / 100000) := by
  exact
    packedTile65536 1328091392 1328156928 13 3150 36442 30 _ _ (2100699 / 100000) (1050351 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1328156928 :
    ThetaLowerSegment 1328156928 1328222464 (132810148563147 / 100000)
      (26563322485871 / 20000) := by
  exact
    packedTile65536 1328156928 1328222464 13 3077 36443 30 _ _ (65647 / 3125) (2100707 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1328222464 :
    ThetaLowerSegment 1328222464 1328288000 (26563322485871 / 20000) (16602893992059 / 12500) := by
  exact
    packedTile65536 1328222464 1328288000 13 3113 36444 30 _ _ (2100709 / 100000) (262589 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1328288000 :
    ThetaLowerSegment 1328288000 1328353536 (16602893992059 / 12500) (13282980489771 / 10000) := by
  exact
    packedTile65536 1328288000 1328353536 13 3167 36445 30 _ _ (1050357 / 50000) (2100717 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1328353536 :
    ThetaLowerSegment 1328353536 1328419072 (13282980489771 / 10000) (33209082432731 / 25000) := by
  exact
    packedTile65536 1328353536 1328419072 13 3106 36446 30 _ _ (2100719 / 100000) (1050361 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1328419072 :
    ThetaLowerSegment 1328419072 1328484608 (33209082432731 / 25000) (16605361286497 / 12500) := by
  exact
    packedTile65536 1328419072 1328484608 13 3123 36447 30 _ _ (525181 / 25000) (2100727 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1328484608 :
    ThetaLowerSegment 1328484608 1328550144 (16605361286497 / 12500)
      (132849555905093 / 100000) := by
  exact
    packedTile65536 1328484608 1328550144 13 3173 36448 30 _ _ (2100729 / 100000) (525183 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1328550144 :
    ThetaLowerSegment 1328550144 1328615680 (132849555905093 / 100000)
      (132856164814257 / 100000) := by
  exact
    packedTile65536 1328550144 1328615680 13 3146 36449 30 _ _ (1050367 / 50000) (2100737 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1328615680 :
    ThetaLowerSegment 1328615680 1328681216 (132856164814257 / 100000)
      (66431379516989 / 50000) := by
  exact
    packedTile65536 1328615680 1328681216 13 3139 36450 30 _ _ (2100739 / 100000) (1050371 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1328681216 :
    ThetaLowerSegment 1328681216 1328746752 (66431379516989 / 50000) (66434647224281 / 50000) := by
  exact
    packedTile65536 1328681216 1328746752 13 3111 36451 30 _ _ (262593 / 12500) (2100747 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1328746752 :
    ThetaLowerSegment 1328746752 1328812288 (66434647224281 / 50000) (66437928594219 / 50000) := by
  exact
    packedTile65536 1328746752 1328812288 13 3124 36451 30 _ _ (2100749 / 100000) (131297 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1328812288 :
    ThetaLowerSegment 1328812288 1328877824 (66437928594219 / 50000) (66441199468197 / 50000) := by
  exact
    packedTile65536 1328812288 1328877824 13 3114 36452 30 _ _ (1050377 / 50000) (2100757 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1328877824 :
    ThetaLowerSegment 1328877824 1328943360 (66441199468197 / 50000) (26577777636189 / 20000) := by
  exact
    packedTile65536 1328877824 1328943360 13 3089 36453 30 _ _ (2100759 / 100000) (1050381 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1328943360 :
    ThetaLowerSegment 1328943360 1329008896 (26577777636189 / 20000) (6644774754029 / 5000) := by
  exact
    packedTile65536 1328943360 1329008896 13 3145 36454 30 _ _ (2100763 / 100000) (1050383 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1329008896 :
    ThetaLowerSegment 1329008896 1329074432 (6644774754029 / 5000) (33225490311121 / 25000) := by
  exact
    packedTile65536 1329008896 1329074432 13 3078 36455 30 _ _ (65649 / 3125) (2100771 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1329074432 :
    ThetaLowerSegment 1329074432 1329139968 (33225490311121 / 25000)
      (132908517757017 / 100000) := by
  exact
    packedTile65536 1329074432 1329139968 13 3121 36456 30 _ _ (2100773 / 100000) (262597 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1329139968 :
    ThetaLowerSegment 1329139968 1329205504 (132908517757017 / 100000)
      (132915131006161 / 100000) := by
  exact
    packedTile65536 1329139968 1329205504 13 3148 36457 30 _ _ (1050389 / 50000) (2100781 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1329205504 :
    ThetaLowerSegment 1329205504 1329271040 (132915131006161 / 100000)
      (66460896294527 / 50000) := by
  exact
    packedTile65536 1329205504 1329271040 13 3171 36458 30 _ _ (2100783 / 100000) (1050393 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1329271040 :
    ThetaLowerSegment 1329271040 1329336576 (66460896294527 / 50000) (66464152515927 / 50000) := by
  exact
    packedTile65536 1329271040 1329336576 13 3100 36459 30 _ _ (525197 / 25000) (2100791 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1329336576 :
    ThetaLowerSegment 1329336576 1329402112 (66464152515927 / 50000)
      (132934857405221 / 100000) := by
  exact
    packedTile65536 1329336576 1329402112 13 3119 36460 30 _ _ (2100793 / 100000) (525199 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1329402112 :
    ThetaLowerSegment 1329402112 1329467648 (132934857405221 / 100000)
      (132941371979819 / 100000) := by
  exact
    packedTile65536 1329402112 1329467648 13 3101 36460 30 _ _ (1050399 / 50000) (2100801 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1329467648 :
    ThetaLowerSegment 1329467648 1329533184 (132941371979819 / 100000) (6647394958737 / 5000) := by
  exact
    packedTile65536 1329467648 1329533184 13 3107 36461 30 _ _ (2100803 / 100000) (1050403 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1329533184 :
    ThetaLowerSegment 1329533184 1329598720 (6647394958737 / 5000) (33238601869481 / 25000) := by
  exact
    packedTile65536 1329533184 1329598720 13 3098 36462 30 _ _ (262601 / 12500) (2100811 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1329598720 :
    ThetaLowerSegment 1329598720 1329664256 (33238601869481 / 25000) (13296109226489 / 10000) := by
  exact
    packedTile65536 1329598720 1329664256 13 3182 36463 30 _ _ (2100813 / 100000) (131301 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1329664256 :
    ThetaLowerSegment 1329664256 1329729792 (13296109226489 / 10000) (2659350835523 / 2000) := by
  exact
    packedTile65536 1329664256 1329729792 13 3070 36464 30 _ _ (1050409 / 50000) (2100821 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1329729792 :
    ThetaLowerSegment 1329729792 1329795328 (2659350835523 / 2000) (66487014558787 / 50000) := by
  exact
    packedTile65536 1329729792 1329795328 13 3088 36465 30 _ _ (2100823 / 100000) (1050413 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1329795328 :
    ThetaLowerSegment 1329795328 1329860864 (66487014558787 / 50000) (66490290800053 / 50000) := by
  exact
    packedTile65536 1329795328 1329860864 13 3119 36466 30 _ _ (525207 / 25000) (2100831 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1329860864 :
    ThetaLowerSegment 1329860864 1329926400 (66490290800053 / 50000)
      (132987209728221 / 100000) := by
  exact
    packedTile65536 1329860864 1329926400 13 3155 36467 30 _ _ (2100833 / 100000) (525209 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1329926400 :
    ThetaLowerSegment 1329926400 1329991936 (132987209728221 / 100000)
      (66496824396813 / 50000) := by
  exact
    packedTile65536 1329926400 1329991936 13 3065 36468 30 _ _ (2100837 / 100000) (52521 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1329991936 :
    ThetaLowerSegment 1329991936 1330057472 (66496824396813 / 50000) (6650009855907 / 5000) := by
  exact
    packedTile65536 1329991936 1330057472 13 3117 36469 30 _ _ (1050421 / 50000) (420169 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1330057472 :
    ThetaLowerSegment 1330057472 1330123008 (6650009855907 / 5000) (133006674029441 / 100000) := by
  exact
    packedTile65536 1330057472 1330123008 13 3083 36469 30 _ _ (2100847 / 100000) (42017 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1330123008 :
    ThetaLowerSegment 1330123008 1330188544 (133006674029441 / 100000)
      (133013209780013 / 100000) := by
  exact
    packedTile65536 1330123008 1330188544 13 3111 36470 30 _ _ (525213 / 25000) (420171 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1330188544 :
    ThetaLowerSegment 1330188544 1330254080 (133013209780013 / 100000)
      (16627450335983 / 12500) := by
  exact
    packedTile65536 1330188544 1330254080 13 3043 36471 30 _ _ (2100857 / 100000) (105043 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1330254080 :
    ThetaLowerSegment 1330254080 1330319616 (16627450335983 / 12500) (66513079739083 / 50000) := by
  exact
    packedTile65536 1330254080 1330319616 13 3121 36472 30 _ _ (1050431 / 50000) (420173 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1330319616 :
    ThetaLowerSegment 1330319616 1330385152 (66513079739083 / 50000) (66516357091603 / 50000) := by
  exact
    packedTile65536 1330319616 1330385152 13 3120 36473 30 _ _ (2100867 / 100000) (210087 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1330385152 :
    ThetaLowerSegment 1330385152 1330450688 (66516357091603 / 50000) (66519593484919 / 50000) := by
  exact
    packedTile65536 1330385152 1330450688 13 3081 36474 30 _ _ (262609 / 12500) (16807 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1330450688 :
    ThetaLowerSegment 1330450688 1330516224 (66519593484919 / 50000) (33261446981343 / 25000) := by
  exact
    packedTile65536 1330450688 1330516224 13 3142 36475 30 _ _ (2100877 / 100000) (26261 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1330516224 :
    ThetaLowerSegment 1330516224 1330581760 (33261446981343 / 25000) (6652613352273 / 5000) := by
  exact
    packedTile65536 1330516224 1330581760 13 3084 36476 30 _ _ (1050441 / 50000) (420177 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1330581760 :
    ThetaLowerSegment 1330581760 1330647296 (6652613352273 / 5000) (133058777694273 / 100000) := by
  exact
    packedTile65536 1330581760 1330647296 13 3099 36477 30 _ _ (2100887 / 100000) (210089 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1330647296 :
    ThetaLowerSegment 1330647296 1330712832 (133058777694273 / 100000)
      (133065227432713 / 100000) := by
  exact
    packedTile65536 1330647296 1330712832 13 3070 36478 30 _ _ (525223 / 25000) (420179 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1330712832 :
    ThetaLowerSegment 1330712832 1330778368 (133065227432713 / 100000)
      (133071786433147 / 100000) := by
  exact
    packedTile65536 1330712832 1330778368 13 3122 36478 30 _ _ (2100897 / 100000) (21009 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1330778368 :
    ThetaLowerSegment 1330778368 1330843904 (133071786433147 / 100000) (4158703481789 / 3125) := by
  exact
    packedTile65536 1330778368 1330843904 13 3201 36479 30 _ _ (2100901 / 100000) (262613 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1330843904 :
    ThetaLowerSegment 1330843904 1330909440 (4158703481789 / 3125) (66542628713207 / 50000) := by
  exact
    packedTile65536 1330843904 1330909440 13 3211 36480 30 _ _ (1050453 / 50000) (2100909 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1330909440 :
    ThetaLowerSegment 1330909440 1330974976 (66542628713207 / 50000) (4159119002091 / 3125) := by
  exact
    packedTile65536 1330909440 1330974976 13 3118 36481 30 _ _ (2100911 / 100000) (1050457 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1330974976 :
    ThetaLowerSegment 1330974976 1331040512 (4159119002091 / 3125) (33274586004147 / 25000) := by
  exact
    packedTile65536 1330974976 1331040512 13 3111 36482 30 _ _ (525229 / 25000) (2100919 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1331040512 :
    ThetaLowerSegment 1331040512 1331106048 (33274586004147 / 25000) (5324194022757 / 4000) := by
  exact
    packedTile65536 1331040512 1331106048 13 3097 36483 30 _ _ (2100921 / 100000) (525231 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1331106048 :
    ThetaLowerSegment 1331106048 1331171584 (5324194022757 / 4000) (133111441173787 / 100000) := by
  exact
    packedTile65536 1331106048 1331171584 13 3137 36484 30 _ _ (1050463 / 50000) (2100929 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1331171584 :
    ThetaLowerSegment 1331171584 1331237120 (133111441173787 / 100000)
      (133117891031957 / 100000) := by
  exact
    packedTile65536 1331171584 1331237120 13 3070 36485 30 _ _ (2100931 / 100000) (1050467 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1331237120 :
    ThetaLowerSegment 1331237120 1331302656 (133117891031957 / 100000)
      (133124416539173 / 100000) := by
  exact
    packedTile65536 1331237120 1331302656 13 3106 36486 30 _ _ (262617 / 12500) (2100939 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1331302656 :
    ThetaLowerSegment 1331302656 1331368192 (133124416539173 / 100000) (3328272553601 / 2500) := by
  exact
    packedTile65536 1331302656 1331368192 13 3087 36487 30 _ _ (2100941 / 100000) (131309 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1331368192 :
    ThetaLowerSegment 1331368192 1331433728 (3328272553601 / 2500) (33284333810173 / 25000) := by
  exact
    packedTile65536 1331368192 1331433728 13 3062 36487 30 _ _ (1050473 / 50000) (2100949 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1331433728 :
    ThetaLowerSegment 1331433728 1331499264 (33284333810173 / 25000) (33285926331031 / 25000) := by
  exact
    packedTile65536 1331433728 1331499264 13 3032 36488 30 _ _ (2100951 / 100000) (1050477 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1331499264 :
    ThetaLowerSegment 1331499264 1331564800 (33285926331031 / 25000) (33287561925277 / 25000) := by
  exact
    packedTile65536 1331499264 1331564800 13 3114 36489 30 _ _ (525239 / 25000) (2100959 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1331564800 :
    ThetaLowerSegment 1331564800 1331630336 (33287561925277 / 25000) (33289204876779 / 25000) := by
  exact
    packedTile65536 1331564800 1331630336 13 3128 36490 30 _ _ (2100961 / 100000) (525241 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1331630336 :
    ThetaLowerSegment 1331630336 1331695872 (33289204876779 / 25000)
      (133163439647831 / 100000) := by
  exact
    packedTile65536 1331630336 1331695872 13 3151 36491 30 _ _ (420193 / 20000) (262621 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1331695872 :
    ThetaLowerSegment 1331695872 1331761408 (133163439647831 / 100000)
      (133170078713031 / 100000) := by
  exact
    packedTile65536 1331695872 1331761408 13 3160 36492 30 _ _ (210097 / 10000) (2100973 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1331761408 :
    ThetaLowerSegment 1331761408 1331826944 (133170078713031 / 100000)
      (133176667370631 / 100000) := by
  exact
    packedTile65536 1331761408 1331826944 13 3136 36493 30 _ _ (84039 / 4000) (1050489 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1331826944 :
    ThetaLowerSegment 1331826944 1331892480 (133176667370631 / 100000)
      (133183239236071 / 100000) := by
  exact
    packedTile65536 1331826944 1331892480 13 3128 36494 30 _ _ (105049 / 5000) (2100983 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1331892480 :
    ThetaLowerSegment 1331892480 1331958016 (133183239236071 / 100000)
      (133189781703361 / 100000) := by
  exact
    packedTile65536 1331892480 1331958016 13 3114 36495 30 _ _ (420197 / 20000) (525247 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1331958016 :
    ThetaLowerSegment 1331958016 1332023552 (133189781703361 / 100000)
      (133196311580281 / 100000) := by
  exact
    packedTile65536 1331958016 1332023552 13 3108 36496 30 _ _ (210099 / 10000) (2100993 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1332023552 :
    ThetaLowerSegment 1332023552 1332089088 (133196311580281 / 100000)
      (133202929714531 / 100000) := by
  exact
    packedTile65536 1332023552 1332089088 13 3150 36496 30 _ _ (420199 / 20000) (1050499 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1332089088 :
    ThetaLowerSegment 1332089088 1332154624 (133202929714531 / 100000)
      (133209442814531 / 100000) := by
  exact
    packedTile65536 1332089088 1332154624 13 3100 36497 30 _ _ (2101 / 100) (2101003 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1332154624 :
    ThetaLowerSegment 1332154624 1332220160 (133209442814531 / 100000)
      (66608035742653 / 50000) := by
  exact
    packedTile65536 1332154624 1332220160 13 3155 36498 30 _ _ (420201 / 20000) (131313 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1332220160 :
    ThetaLowerSegment 1332220160 1332285696 (66608035742653 / 50000) (66611315419263 / 50000) := by
  exact
    packedTile65536 1332220160 1332285696 13 3122 36499 30 _ _ (210101 / 10000) (2101013 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1332285696 :
    ThetaLowerSegment 1332285696 1332351232 (66611315419263 / 50000) (33307343774169 / 25000) := by
  exact
    packedTile65536 1332285696 1332351232 13 3210 36500 30 _ _ (420203 / 20000) (1050509 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1332351232 :
    ThetaLowerSegment 1332351232 1332416768 (33307343774169 / 25000) (33308975216199 / 25000) := by
  exact
    packedTile65536 1332351232 1332416768 13 3106 36501 30 _ _ (105051 / 5000) (2101023 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1332416768 :
    ThetaLowerSegment 1332416768 1332482304 (33308975216199 / 25000) (66621255344723 / 50000) := by
  exact
    packedTile65536 1332416768 1332482304 13 3146 36502 30 _ _ (84041 / 4000) (525257 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1332482304 :
    ThetaLowerSegment 1332482304 1332547840 (66621255344723 / 50000)
      (133249202466811 / 100000) := by
  exact
    packedTile65536 1332482304 1332547840 13 3185 36503 30 _ _ (2101029 / 100000) (262629 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1332547840 :
    ThetaLowerSegment 1332547840 1332613376 (133249202466811 / 100000)
      (133255860643557 / 100000) := by
  exact
    packedTile65536 1332547840 1332613376 13 3169 36504 30 _ _ (1050517 / 50000) (2101037 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1332613376 :
    ThetaLowerSegment 1332613376 1332678912 (133255860643557 / 100000)
      (26652484017463 / 20000) := by
  exact
    packedTile65536 1332613376 1332678912 13 3122 36504 30 _ _ (2101039 / 100000) (1050521 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1332678912 :
    ThetaLowerSegment 1332678912 1332744448 (26652484017463 / 20000)
      (133268987950859 / 100000) := by
  exact
    packedTile65536 1332678912 1332744448 13 3126 36505 30 _ _ (525261 / 25000) (2101047 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1332744448 :
    ThetaLowerSegment 1332744448 1332809984 (133268987950859 / 100000)
      (133275522213249 / 100000) := by
  exact
    packedTile65536 1332744448 1332809984 13 3110 36506 30 _ _ (2101049 / 100000) (525263 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1332809984 :
    ThetaLowerSegment 1332809984 1332875520 (133275522213249 / 100000)
      (133282209868131 / 100000) := by
  exact
    packedTile65536 1332809984 1332875520 13 3183 36507 30 _ _ (1050527 / 50000) (2101057 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1332875520 :
    ThetaLowerSegment 1332875520 1332941056 (133282209868131 / 100000)
      (133288874427279 / 100000) := by
  exact
    packedTile65536 1332875520 1332941056 13 3172 36508 30 _ _ (2101059 / 100000) (1050531 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1332941056 :
    ThetaLowerSegment 1332941056 1333006592 (133288874427279 / 100000)
      (133295442353343 / 100000) := by
  exact
    packedTile65536 1332941056 1333006592 13 3126 36509 30 _ _ (262633 / 12500) (2101067 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1333006592 :
    ThetaLowerSegment 1333006592 1333072128 (133295442353343 / 100000)
      (26660394495159 / 20000) := by
  exact
    packedTile65536 1333006592 1333072128 13 3108 36510 30 _ _ (2101069 / 100000) (131317 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1333072128 :
    ThetaLowerSegment 1333072128 1333137664 (26660394495159 / 20000) (26661720272853 / 20000) := by
  exact
    packedTile65536 1333072128 1333137664 13 3155 36511 30 _ _ (1050537 / 50000) (2101077 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1333137664 :
    ThetaLowerSegment 1333137664 1333203200 (26661720272853 / 20000) (66657577314833 / 50000) := by
  exact
    packedTile65536 1333137664 1333203200 13 3119 36512 30 _ _ (2101079 / 100000) (1050541 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1333203200 :
    ThetaLowerSegment 1333203200 1333268736 (66657577314833 / 50000) (66660902280263 / 50000) := by
  exact
    packedTile65536 1333203200 1333268736 13 3165 36513 30 _ _ (525271 / 25000) (2101087 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1333268736 :
    ThetaLowerSegment 1333268736 1333399808 (66660902280263 / 50000) (66667404097079 / 50000) := by
  exact
    packedTile65536 1333268736 1333399808 14 6189 36513 30 _ _ (65659 / 3125) (2101091 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1333399808 :
    ThetaLowerSegment 1333399808 1333465344 (66667404097079 / 50000) (33335315166529 / 25000) := by
  exact
    packedTile65536 1333399808 1333465344 13 3071 36515 30 _ _ (1050549 / 50000) (2101101 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1333465344 :
    ThetaLowerSegment 1333465344 1333530880 (33335315166529 / 25000)
      (133347830815197 / 100000) := by
  exact
    packedTile65536 1333465344 1333530880 13 3127 36516 30 _ _ (2101103 / 100000) (1050553 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1333530880 :
    ThetaLowerSegment 1333530880 1333596416 (133347830815197 / 100000)
      (133354279115649 / 100000) := by
  exact
    packedTile65536 1333530880 1333596416 13 3069 36517 30 _ _ (525277 / 25000) (2101111 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1333596416 :
    ThetaLowerSegment 1333596416 1333661952 (133354279115649 / 100000)
      (66680384726853 / 50000) := by
  exact
    packedTile65536 1333596416 1333661952 13 3089 36518 30 _ _ (2101113 / 100000) (525279 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1333661952 :
    ThetaLowerSegment 1333661952 1333727488 (66680384726853 / 50000) (8335453212671 / 6250) := by
  exact
    packedTile65536 1333661952 1333727488 13 3085 36519 30 _ _ (1050559 / 50000) (2101121 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1333727488 :
    ThetaLowerSegment 1333727488 1333793024 (8335453212671 / 6250) (133373888850293 / 100000) := by
  exact
    packedTile65536 1333727488 1333793024 13 3159 36520 30 _ _ (2101123 / 100000) (1050563 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1333793024 :
    ThetaLowerSegment 1333793024 1333858560 (133373888850293 / 100000)
      (133380459077549 / 100000) := by
  exact
    packedTile65536 1333793024 1333858560 13 3127 36521 30 _ _ (262641 / 12500) (2101131 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1333858560 :
    ThetaLowerSegment 1333858560 1333924096 (133380459077549 / 100000)
      (133387035623839 / 100000) := by
  exact
    packedTile65536 1333858560 1333924096 13 3130 36522 30 _ _ (2101133 / 100000) (131321 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1333924096 :
    ThetaLowerSegment 1333924096 1333989632 (133387035623839 / 100000)
      (133393586972123 / 100000) := by
  exact
    packedTile65536 1333924096 1333989632 13 3118 36522 30 _ _ (1050569 / 50000) (2101141 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1333989632 :
    ThetaLowerSegment 1333989632 1334055168 (133393586972123 / 100000) (3335006662643 / 2500) := by
  exact
    packedTile65536 1333989632 1334055168 13 3179 36523 30 _ _ (2101143 / 100000) (1050573 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1334055168 :
    ThetaLowerSegment 1334055168 1334120704 (3335006662643 / 2500) (133406849399271 / 100000) := by
  exact
    packedTile65536 1334055168 1334120704 13 3133 36524 30 _ _ (2101147 / 100000) (42023 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1334120704 :
    ThetaLowerSegment 1334120704 1334186240 (133406849399271 / 100000)
      (133413505848807 / 100000) := by
  exact
    packedTile65536 1334120704 1334186240 13 3168 36525 30 _ _ (65661 / 3125) (420231 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1334186240 :
    ThetaLowerSegment 1334186240 1334317312 (133413505848807 / 100000)
      (133426701114767 / 100000) := by
  exact
    packedTile65536 1334186240 1334317312 14 6280 36526 30 _ _ (2101157 / 100000) (52529 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1334317312 :
    ThetaLowerSegment 1334317312 1334448384 (133426701114767 / 100000)
      (66719970284017 / 50000) := by
  exact
    packedTile65536 1334317312 1334448384 14 6301 36528 30 _ _ (2101167 / 100000) (210117 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1334448384 :
    ThetaLowerSegment 1334448384 1334579456 (66719970284017 / 50000)
      (133452898526593 / 100000) := by
  exact
    packedTile65536 1334448384 1334579456 14 6167 36530 30 _ _ (2101177 / 100000) (105059 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1334579456 :
    ThetaLowerSegment 1334579456 1334710528 (133452898526593 / 100000)
      (66732936678159 / 50000) := by
  exact
    packedTile65536 1334579456 1334710528 14 6175 36531 30 _ _ (2101187 / 100000) (210119 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1334710528 :
    ThetaLowerSegment 1334710528 1334776064 (66732936678159 / 50000)
      (133472565668763 / 100000) := by
  exact
    packedTile65536 1334710528 1334776064 13 3185 36533 30 _ _ (2101197 / 100000) (5253 / 250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1334776064 :
    ThetaLowerSegment 1334776064 1334907136 (133472565668763 / 100000) (8342855479313 / 6250) := by
  exact
    packedTile65536 1334776064 1334907136 14 6245 36534 30 _ _ (2101201 / 100000) (525301 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1334907136 :
    ThetaLowerSegment 1334907136 1335038208 (8342855479313 / 6250) (6674945424431 / 5000) := by
  exact
    packedTile65536 1334907136 1335038208 14 6292 36536 30 _ _ (2101211 / 100000) (1050607 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1335038208 :
    ThetaLowerSegment 1335038208 1335169280 (6674945424431 / 5000) (26702385110543 / 20000) := by
  exact
    packedTile65536 1335038208 1335169280 14 6195 36538 30 _ _ (2101221 / 100000) (262653 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1335169280 :
    ThetaLowerSegment 1335169280 1335300352 (26702385110543 / 20000) (66762477643073 / 50000) := by
  exact
    packedTile65536 1335169280 1335300352 14 6201 36539 30 _ _ (2101231 / 100000) (1050617 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1335300352 :
    ThetaLowerSegment 1335300352 1335431424 (66762477643073 / 50000) (66769054527403 / 50000) := by
  exact
    packedTile65536 1335300352 1335431424 14 6260 36541 30 _ _ (2101241 / 100000) (525311 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1335431424 :
    ThetaLowerSegment 1335431424 1335562496 (66769054527403 / 50000)
      (133551298607333 / 100000) := by
  exact
    packedTile65536 1335431424 1335562496 14 6277 36543 30 _ _ (2101251 / 100000) (1050627 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1335562496 :
    ThetaLowerSegment 1335562496 1335693568 (133551298607333 / 100000)
      (133564351634453 / 100000) := by
  exact
    packedTile65536 1335562496 1335693568 14 6212 36545 30 _ _ (105063 / 5000) (2101263 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1335693568 :
    ThetaLowerSegment 1335693568 1335824640 (133564351634453 / 100000)
      (133577394217343 / 100000) := by
  exact
    packedTile65536 1335693568 1335824640 14 6207 36547 30 _ _ (210127 / 10000) (2101273 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1335824640 :
    ThetaLowerSegment 1335824640 1335955712 (133577394217343 / 100000)
      (133590447368703 / 100000) := by
  exact
    packedTile65536 1335824640 1335955712 14 6212 36548 30 _ _ (13133 / 625) (2101283 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1335955712 :
    ThetaLowerSegment 1335955712 1336086784 (133590447368703 / 100000)
      (133603572026043 / 100000) := by
  exact
    packedTile65536 1335955712 1336086784 14 6246 36550 30 _ _ (210129 / 10000) (2101293 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1336086784 :
    ThetaLowerSegment 1336086784 1336217856 (133603572026043 / 100000)
      (133616755582243 / 100000) := by
  exact
    packedTile65536 1336086784 1336217856 14 6274 36552 30 _ _ (21013 / 1000) (2101303 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1336217856 :
    ThetaLowerSegment 1336217856 1336348928 (133616755582243 / 100000)
      (133629934992291 / 100000) := by
  exact
    packedTile65536 1336217856 1336348928 14 6272 36554 30 _ _ (2101309 / 100000) (65666 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1336348928 :
    ThetaLowerSegment 1336348928 1336480000 (133629934992291 / 100000)
      (33410744469831 / 25000) := by
  exact
    packedTile65536 1336348928 1336480000 14 6207 36556 30 _ _ (2101319 / 100000) (1050661 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1336480000 :
    ThetaLowerSegment 1336480000 1336611072 (33410744469831 / 25000)
      (133656226758669 / 100000) := by
  exact
    packedTile65536 1336480000 1336611072 14 6305 36557 30 _ _ (2101329 / 100000) (525333 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1336611072 :
    ThetaLowerSegment 1336611072 1336742144 (133656226758669 / 100000)
      (133669439978301 / 100000) := by
  exact
    packedTile65536 1336611072 1336742144 14 6288 36559 30 _ _ (2101339 / 100000) (1050671 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1336742144 :
    ThetaLowerSegment 1336742144 1336873216 (133669439978301 / 100000)
      (66841218410933 / 50000) := by
  exact
    packedTile65536 1336742144 1336873216 14 6185 36561 30 _ _ (2101349 / 100000) (262669 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1336873216 :
    ThetaLowerSegment 1336873216 1337004288 (66841218410933 / 50000) (66847791458757 / 50000) := by
  exact
    packedTile65536 1336873216 1337004288 14 6256 36563 30 _ _ (1050679 / 50000) (2101361 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1337004288 :
    ThetaLowerSegment 1337004288 1337135360 (66847791458757 / 50000) (66854437035057 / 50000) := by
  exact
    packedTile65536 1337004288 1337135360 14 6325 36565 30 _ _ (262671 / 12500) (2101371 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1337135360 :
    ThetaLowerSegment 1337135360 1337266432 (66854437035057 / 50000) (66860980726149 / 50000) := by
  exact
    packedTile65536 1337135360 1337266432 14 6228 36566 30 _ _ (1050689 / 50000) (2101381 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1337266432 :
    ThetaLowerSegment 1337266432 1337397504 (66860980726149 / 50000) (66867524448381 / 50000) := by
  exact
    packedTile65536 1337266432 1337397504 14 6228 36568 30 _ _ (525347 / 25000) (2101391 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1337397504 :
    ThetaLowerSegment 1337397504 1337528576 (66867524448381 / 50000) (6687409236783 / 5000) := by
  exact
    packedTile65536 1337397504 1337528576 14 6251 36570 30 _ _ (1050699 / 50000) (2101401 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1337528576 :
    ThetaLowerSegment 1337528576 1337659648 (6687409236783 / 5000) (66880663467519 / 50000) := by
  exact
    packedTile65536 1337528576 1337659648 14 6254 36572 30 _ _ (2101407 / 100000) (210141 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1337659648 :
    ThetaLowerSegment 1337659648 1337790720 (66880663467519 / 50000) (66887350176413 / 50000) := by
  exact
    packedTile65536 1337659648 1337790720 14 6364 36574 30 _ _ (2101417 / 100000) (105071 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1337790720 :
    ThetaLowerSegment 1337790720 1337921792 (66887350176413 / 50000)
      (133787840575857 / 100000) := by
  exact
    packedTile65536 1337790720 1337921792 14 6253 36575 30 _ _ (2101427 / 100000) (210143 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1337921792 :
    ThetaLowerSegment 1337921792 1338052864 (133787840575857 / 100000)
      (13380093042693 / 10000) := by
  exact
    packedTile65536 1337921792 1338052864 14 6229 36577 30 _ _ (2101437 / 100000) (13134 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1338052864 :
    ThetaLowerSegment 1338052864 1338183936 (13380093042693 / 10000) (26762793981113 / 20000) := by
  exact
    packedTile65536 1338052864 1338183936 14 6205 36579 30 _ _ (2101447 / 100000) (42029 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1338183936 :
    ThetaLowerSegment 1338183936 1338315008 (26762793981113 / 20000)
      (133826870743949 / 100000) := by
  exact
    packedTile65536 1338183936 1338315008 14 6139 36581 30 _ _ (131341 / 6250) (2101459 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1338315008 :
    ThetaLowerSegment 1338315008 1338446080 (133826870743949 / 100000)
      (133840076356293 / 100000) := by
  exact
    packedTile65536 1338315008 1338446080 14 6284 36582 30 _ _ (1050733 / 50000) (2101469 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1338446080 :
    ThetaLowerSegment 1338446080 1338577152 (133840076356293 / 100000)
      (133853261016717 / 100000) := by
  exact
    packedTile65536 1338446080 1338577152 14 6274 36584 30 _ _ (525369 / 25000) (2101479 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1338577152 :
    ThetaLowerSegment 1338577152 1338708224 (133853261016717 / 100000)
      (133866456247311 / 100000) := by
  exact
    packedTile65536 1338577152 1338708224 14 6279 36586 30 _ _ (1050743 / 50000) (2101489 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1338708224 :
    ThetaLowerSegment 1338708224 1338839296 (133866456247311 / 100000)
      (133879586394319 / 100000) := by
  exact
    packedTile65536 1338708224 1338839296 14 6248 36588 30 _ _ (262687 / 12500) (2101499 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1338839296 :
    ThetaLowerSegment 1338839296 1338970368 (133879586394319 / 100000)
      (33473181776271 / 25000) := by
  exact
    packedTile65536 1338839296 1338970368 14 6253 36590 30 _ _ (420301 / 20000) (525377 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1338970368 :
    ThetaLowerSegment 1338970368 1339101440 (33473181776271 / 25000)
      (133905758599599 / 100000) := by
  exact
    packedTile65536 1338970368 1339101440 14 6201 36591 30 _ _ (420303 / 20000) (1050759 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1339101440 :
    ThetaLowerSegment 1339101440 1339232512 (133905758599599 / 100000)
      (133918737617999 / 100000) := by
  exact
    packedTile65536 1339101440 1339232512 14 6176 36593 30 _ _ (84061 / 4000) (262691 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1339232512 :
    ThetaLowerSegment 1339232512 1339363584 (133918737617999 / 100000)
      (33482913938411 / 25000) := by
  exact
    packedTile65536 1339232512 1339363584 14 6147 36595 30 _ _ (420307 / 20000) (1050769 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1339363584 :
    ThetaLowerSegment 1339363584 1339494656 (33482913938411 / 25000)
      (133944737871269 / 100000) := by
  exact
    packedTile65536 1339363584 1339494656 14 6225 36597 30 _ _ (420309 / 20000) (525387 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1339494656 :
    ThetaLowerSegment 1339494656 1339625728 (133944737871269 / 100000)
      (133957710764111 / 100000) := by
  exact
    packedTile65536 1339494656 1339625728 14 6173 36599 30 _ _ (1050777 / 50000) (2101557 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1339625728 :
    ThetaLowerSegment 1339625728 1339756800 (133957710764111 / 100000)
      (133970685820247 / 100000) := by
  exact
    packedTile65536 1339625728 1339756800 14 6174 36600 30 _ _ (525391 / 25000) (2101567 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1339756800 :
    ThetaLowerSegment 1339756800 1339887872 (133970685820247 / 100000)
      (133983879501819 / 100000) := by
  exact
    packedTile65536 1339756800 1339887872 14 6278 36602 30 _ _ (1050787 / 50000) (2101577 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1339887872 :
    ThetaLowerSegment 1339887872 1340018944 (133983879501819 / 100000)
      (133996818954507 / 100000) := by
  exact
    packedTile65536 1339887872 1340018944 14 6157 36604 30 _ _ (131349 / 6250) (2101587 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1340018944 :
    ThetaLowerSegment 1340018944 1340150016 (133996818954507 / 100000)
      (33502466936361 / 25000) := by
  exact
    packedTile65536 1340018944 1340150016 14 6209 36606 30 _ _ (2101593 / 100000) (525399 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1340150016 :
    ThetaLowerSegment 1340150016 1340281088 (33502466936361 / 25000)
      (134022887176029 / 100000) := by
  exact
    packedTile65536 1340150016 1340281088 14 6195 36608 30 _ _ (2101603 / 100000) (1050803 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1340281088 :
    ThetaLowerSegment 1340281088 1340346624 (134022887176029 / 100000)
      (33507387847713 / 25000) := by
  exact
    packedTile65536 1340281088 1340346624 13 3171 36609 30 _ _ (2101613 / 100000) (131351 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1340346624 :
    ThetaLowerSegment 1340346624 1340477696 (33507387847713 / 25000) (33510651660467 / 25000) := by
  exact
    packedTile65536 1340346624 1340477696 14 6212 36610 30 _ _ (1050809 / 50000) (2101621 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1340477696 :
    ThetaLowerSegment 1340477696 1340608768 (33510651660467 / 25000) (33513944911543 / 25000) := by
  exact
    packedTile65536 1340477696 1340608768 14 6268 36612 30 _ _ (525407 / 25000) (2101631 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1340608768 :
    ThetaLowerSegment 1340608768 1340739840 (33513944911543 / 25000)
      (134068866539771 / 100000) := by
  exact
    packedTile65536 1340608768 1340739840 14 6227 36614 30 _ _ (2101637 / 100000) (52541 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1340739840 :
    ThetaLowerSegment 1340739840 1340870912 (134068866539771 / 100000)
      (67041062915347 / 50000) := by
  exact
    packedTile65536 1340739840 1340870912 14 6309 36616 30 _ _ (2101647 / 100000) (42033 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1340870912 :
    ThetaLowerSegment 1340870912 1341001984 (67041062915347 / 50000) (2681903458347 / 2000) := by
  exact
    packedTile65536 1340870912 1341001984 14 6208 36617 30 _ _ (2101657 / 100000) (105083 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1341001984 :
    ThetaLowerSegment 1341001984 1341133056 (2681903458347 / 2000) (33527093897361 / 25000) := by
  exact
    packedTile65536 1341001984 1341133056 14 6282 36619 30 _ _ (2101667 / 100000) (210167 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1341133056 :
    ThetaLowerSegment 1341133056 1341264128 (33527093897361 / 25000)
      (134121450122061 / 100000) := by
  exact
    packedTile65536 1341133056 1341264128 14 6221 36621 30 _ _ (2101677 / 100000) (26271 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1341264128 :
    ThetaLowerSegment 1341264128 1341395200 (134121450122061 / 100000)
      (134134797929847 / 100000) := by
  exact
    packedTile65536 1341264128 1341395200 14 6351 36623 30 _ _ (1050843 / 50000) (2101689 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1341395200 :
    ThetaLowerSegment 1341395200 1341526272 (134134797929847 / 100000)
      (134148040716343 / 100000) := by
  exact
    packedTile65536 1341395200 1341526272 14 6301 36625 30 _ _ (65678 / 3125) (2101699 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1341526272 :
    ThetaLowerSegment 1341526272 1341657344 (134148040716343 / 100000)
      (134161340311911 / 100000) := by
  exact
    packedTile65536 1341526272 1341657344 14 6328 36626 30 _ _ (1050853 / 50000) (2101709 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1341657344 :
    ThetaLowerSegment 1341657344 1341788416 (134161340311911 / 100000)
      (134174328916791 / 100000) := by
  exact
    packedTile65536 1341657344 1341788416 14 6180 36628 30 _ _ (525429 / 25000) (2101719 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1341788416 :
    ThetaLowerSegment 1341788416 1341919488 (134174328916791 / 100000)
      (16773427570227 / 12500) := by
  exact
    packedTile65536 1341788416 1341919488 14 6229 36630 30 _ _ (84069 / 4000) (65679 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1341919488 :
    ThetaLowerSegment 1341919488 1342050560 (16773427570227 / 12500)
      (134200512269131 / 100000) := by
  exact
    packedTile65536 1341919488 1342050560 14 6229 36632 30 _ _ (420347 / 20000) (1050869 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1342050560 :
    ThetaLowerSegment 1342050560 1342181632 (134200512269131 / 100000)
      (134213690210281 / 100000) := by
  exact
    packedTile65536 1342050560 1342181632 14 6270 36634 30 _ _ (420349 / 20000) (525437 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1342181632 :
    ThetaLowerSegment 1342181632 1342312704 (134213690210281 / 100000)
      (67113363698273 / 50000) := by
  exact
    packedTile65536 1342181632 1342312704 14 6203 36635 30 _ _ (420351 / 20000) (1050879 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1342312704 :
    ThetaLowerSegment 1342312704 1342443776 (67113363698273 / 50000) (13423985501449 / 10000) := by
  exact
    packedTile65536 1342312704 1342443776 14 6246 36637 30 _ _ (525441 / 25000) (2101767 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1342443776 :
    ThetaLowerSegment 1342443776 1342574848 (13423985501449 / 10000) (33563246199167 / 25000) := by
  exact
    packedTile65536 1342443776 1342574848 14 6247 36639 30 _ _ (1050887 / 50000) (2101777 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1342574848 :
    ThetaLowerSegment 1342574848 1342705920 (33563246199167 / 25000) (33566528134883 / 25000) := by
  exact
    packedTile65536 1342574848 1342705920 14 6246 36641 30 _ _ (262723 / 12500) (2101787 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1342705920 :
    ThetaLowerSegment 1342705920 1342836992 (33566528134883 / 25000) (33569775406613 / 25000) := by
  exact
    packedTile65536 1342705920 1342836992 14 6180 36642 30 _ _ (1050897 / 50000) (2101797 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1342836992 :
    ThetaLowerSegment 1342836992 1342968064 (33569775406613 / 25000) (33573074187991 / 25000) := by
  exact
    packedTile65536 1342836992 1342968064 14 6278 36644 30 _ _ (525451 / 25000) (2101807 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1342968064 :
    ThetaLowerSegment 1342968064 1343099136 (33573074187991 / 25000) (67152682912599 / 50000) := by
  exact
    packedTile65536 1342968064 1343099136 14 6218 36646 30 _ _ (2101813 / 100000) (262727 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1343099136 :
    ThetaLowerSegment 1343099136 1343230208 (67152682912599 / 50000)
      (134318743928593 / 100000) := by
  exact
    packedTile65536 1343099136 1343230208 14 6365 36648 30 _ _ (2101823 / 100000) (1050913 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1343230208 :
    ThetaLowerSegment 1343230208 1343361280 (134318743928593 / 100000)
      (134331901403173 / 100000) := by
  exact
    packedTile65536 1343230208 1343361280 14 6260 36650 30 _ _ (2101833 / 100000) (525459 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1343361280 :
    ThetaLowerSegment 1343361280 1343492352 (134331901403173 / 100000)
      (67172469567651 / 50000) := by
  exact
    packedTile65536 1343361280 1343492352 14 6203 36651 30 _ _ (2101843 / 100000) (1050923 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1343492352 :
    ThetaLowerSegment 1343492352 1343623424 (67172469567651 / 50000) (67178932762551 / 50000) := by
  exact
    packedTile65536 1343492352 1343623424 14 6150 36653 30 _ _ (525463 / 25000) (420371 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1343623424 :
    ThetaLowerSegment 1343623424 1343754496 (67178932762551 / 50000) (33592714283531 / 25000) := by
  exact
    packedTile65536 1343623424 1343754496 14 6181 36655 30 _ _ (1050931 / 50000) (420373 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1343754496 :
    ThetaLowerSegment 1343754496 1343885568 (33592714283531 / 25000) (33596016849911 / 25000) := by
  exact
    packedTile65536 1343754496 1343885568 14 6285 36657 30 _ _ (131367 / 6250) (3363 / 160)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1343885568 :
    ThetaLowerSegment 1343885568 1344016640 (33596016849911 / 25000) (67198575807547 / 50000) := by
  exact
    packedTile65536 1343885568 1344016640 14 6225 36659 30 _ _ (1050941 / 50000) (420377 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1344016640 :
    ThetaLowerSegment 1344016640 1344147712 (67198575807547 / 50000) (67205264024709 / 50000) := by
  exact
    packedTile65536 1344016640 1344147712 14 6364 36660 30 _ _ (2101891 / 100000) (1050947 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1344147712 :
    ThetaLowerSegment 1344147712 1344278784 (67205264024709 / 50000)
      (134423599771737 / 100000) := by
  exact
    packedTile65536 1344147712 1344278784 14 6219 36662 30 _ _ (2101901 / 100000) (131369 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1344278784 :
    ThetaLowerSegment 1344278784 1344409856 (134423599771737 / 100000)
      (134436694677267 / 100000) := by
  exact
    packedTile65536 1344278784 1344409856 14 6230 36664 30 _ _ (2101911 / 100000) (1050957 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1344409856 :
    ThetaLowerSegment 1344409856 1344540928 (134436694677267 / 100000)
      (134449726587467 / 100000) := by
  exact
    packedTile65536 1344409856 1344540928 14 6200 36666 30 _ _ (2101921 / 100000) (525481 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1344540928 :
    ThetaLowerSegment 1344540928 1344672000 (134449726587467 / 100000)
      (134462848936457 / 100000) := by
  exact
    packedTile65536 1344540928 1344672000 14 6243 36667 30 _ _ (210193 / 10000) (2101933 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1344672000 :
    ThetaLowerSegment 1344672000 1344803072 (134462848936457 / 100000)
      (134475843129537 / 100000) := by
  exact
    packedTile65536 1344672000 1344803072 14 6182 36669 30 _ _ (105097 / 5000) (2101943 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1344803072 :
    ThetaLowerSegment 1344803072 1344934144 (134475843129537 / 100000)
      (134488822670787 / 100000) := by
  exact
    packedTile65536 1344803072 1344934144 14 6175 36671 30 _ _ (42039 / 2000) (2101953 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1344934144 :
    ThetaLowerSegment 1344934144 1345065216 (134488822670787 / 100000)
      (134501989348227 / 100000) := by
  exact
    packedTile65536 1344934144 1345065216 14 6264 36673 30 _ _ (52549 / 2500) (2101963 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1345065216 :
    ThetaLowerSegment 1345065216 1345196288 (134501989348227 / 100000) (5380600189611 / 4000) := by
  exact
    packedTile65536 1345065216 1345196288 14 6192 36675 30 _ _ (2101969 / 100000) (525493 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1345196288 :
    ThetaLowerSegment 1345196288 1345327360 (5380600189611 / 4000) (16816014873407 / 12500) := by
  exact
    packedTile65536 1345196288 1345327360 14 6239 36676 30 _ _ (2101979 / 100000) (1050991 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1345327360 :
    ThetaLowerSegment 1345327360 1345458432 (16816014873407 / 12500) (33635298339709 / 25000) := by
  exact
    packedTile65536 1345327360 1345458432 14 6220 36678 30 _ _ (2101989 / 100000) (262749 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1345458432 :
    ThetaLowerSegment 1345458432 1345589504 (33635298339709 / 25000) (67277157018297 / 50000) := by
  exact
    packedTile65536 1345458432 1345589504 14 6242 36680 30 _ _ (2101999 / 100000) (1051001 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1345589504 :
    ThetaLowerSegment 1345589504 1345720576 (67277157018297 / 50000) (67283704773217 / 50000) := by
  exact
    packedTile65536 1345589504 1345720576 14 6230 36682 30 _ _ (262751 / 12500) (2102011 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1345720576 :
    ThetaLowerSegment 1345720576 1345851648 (67283704773217 / 50000) (33645092121851 / 25000) := by
  exact
    packedTile65536 1345720576 1345851648 14 6165 36684 30 _ _ (1051009 / 50000) (2102021 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1345851648 :
    ThetaLowerSegment 1345851648 1345982720 (33645092121851 / 25000) (8412093215513 / 6250) := by
  exact
    packedTile65536 1345851648 1345982720 14 6243 36685 30 _ _ (525507 / 25000) (2102031 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1345982720 :
    ThetaLowerSegment 1345982720 1346113792 (8412093215513 / 6250) (67303284113303 / 50000) := by
  exact
    packedTile65536 1345982720 1346113792 14 6221 36687 30 _ _ (1051019 / 50000) (2102041 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1346113792 :
    ThetaLowerSegment 1346113792 1346244864 (67303284113303 / 50000) (16827462201521 / 12500) := by
  exact
    packedTile65536 1346113792 1346244864 14 6246 36689 30 _ _ (2102047 / 100000) (42041 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1346244864 :
    ThetaLowerSegment 1346244864 1346375936 (16827462201521 / 12500) (67316304223131 / 50000) := by
  exact
    packedTile65536 1346244864 1346375936 14 6142 36691 30 _ _ (2102057 / 100000) (105103 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1346375936 :
    ThetaLowerSegment 1346375936 1346507008 (67316304223131 / 50000) (6732289840731 / 5000) := by
  exact
    packedTile65536 1346375936 1346507008 14 6274 36692 30 _ _ (2102067 / 100000) (210207 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1346507008 :
    ThetaLowerSegment 1346507008 1346638080 (6732289840731 / 5000) (16832377096323 / 12500) := by
  exact
    packedTile65536 1346507008 1346638080 14 6289 36694 30 _ _ (525519 / 25000) (2102079 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1346638080 :
    ThetaLowerSegment 1346638080 1346769152 (16832377096323 / 12500) (67336114190547 / 50000) := by
  exact
    packedTile65536 1346638080 1346769152 14 6285 36696 30 _ _ (1051043 / 50000) (2102089 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1346769152 :
    ThetaLowerSegment 1346769152 1346900224 (67336114190547 / 50000) (67342672730067 / 50000) := by
  exact
    packedTile65536 1346769152 1346900224 14 6240 36698 30 _ _ (131381 / 6250) (2102099 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1346900224 :
    ThetaLowerSegment 1346900224 1347031296 (67342672730067 / 50000) (67349304874497 / 50000) := by
  exact
    packedTile65536 1346900224 1347031296 14 6310 36700 30 _ _ (1051053 / 50000) (2102109 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1347031296 :
    ThetaLowerSegment 1347031296 1347162368 (67349304874497 / 50000)
      (134711905626369 / 100000) := by
  exact
    packedTile65536 1347031296 1347162368 14 6325 36701 30 _ _ (420423 / 20000) (1051059 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1347162368 :
    ThetaLowerSegment 1347162368 1347293440 (134711905626369 / 100000)
      (134724972435369 / 100000) := by
  exact
    packedTile65536 1347162368 1347293440 14 6216 36703 30 _ _ (16817 / 800) (131383 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1347293440 :
    ThetaLowerSegment 1347293440 1347424512 (134724972435369 / 100000)
      (134738199068789 / 100000) := by
  exact
    packedTile65536 1347293440 1347424512 14 6292 36705 30 _ _ (420427 / 20000) (1051069 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1347424512 :
    ThetaLowerSegment 1347424512 1347555584 (134738199068789 / 100000)
      (134751375313649 / 100000) := by
  exact
    packedTile65536 1347424512 1347555584 14 6268 36707 30 _ _ (420429 / 20000) (525537 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1347555584 :
    ThetaLowerSegment 1347555584 1347686656 (134751375313649 / 100000)
      (26952860291719 / 20000) := by
  exact
    packedTile65536 1347555584 1347686656 14 6149 36709 30 _ _ (1051077 / 50000) (2102157 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1347686656 :
    ThetaLowerSegment 1347686656 1347817728 (26952860291719 / 20000)
      (134777181417423 / 100000) := by
  exact
    packedTile65536 1347686656 1347817728 14 6127 36710 30 _ _ (525541 / 25000) (2102167 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1347817728 :
    ThetaLowerSegment 1347817728 1347948800 (134777181417423 / 100000)
      (134790267450573 / 100000) := by
  exact
    packedTile65536 1347817728 1347948800 14 6225 36712 30 _ _ (1051087 / 50000) (2102177 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1347948800 :
    ThetaLowerSegment 1347948800 1348079872 (134790267450573 / 100000)
      (33700867815499 / 25000) := by
  exact
    packedTile65536 1347948800 1348079872 14 6281 36714 30 _ _ (2102183 / 100000) (1051093 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1348079872 :
    ThetaLowerSegment 1348079872 1348210944 (33700867815499 / 25000)
      (134816523778333 / 100000) := by
  exact
    packedTile65536 1348079872 1348210944 14 6209 36716 30 _ _ (2102193 / 100000) (525549 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1348210944 :
    ThetaLowerSegment 1348210944 1348342016 (134816523778333 / 100000)
      (134829708795549 / 100000) := by
  exact
    packedTile65536 1348210944 1348342016 14 6272 36717 30 _ _ (2102203 / 100000) (1051103 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1348342016 :
    ThetaLowerSegment 1348342016 1348473088 (134829708795549 / 100000)
      (134842919102041 / 100000) := by
  exact
    packedTile65536 1348342016 1348473088 14 6284 36719 30 _ _ (2102213 / 100000) (262777 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1348473088 :
    ThetaLowerSegment 1348473088 1348604160 (134842919102041 / 100000)
      (134856049580653 / 100000) := by
  exact
    packedTile65536 1348473088 1348604160 14 6246 36721 30 _ _ (1051111 / 50000) (84089 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1348604160 :
    ThetaLowerSegment 1348604160 1348735232 (134856049580653 / 100000)
      (134869178019493 / 100000) := by
  exact
    packedTile65536 1348604160 1348735232 14 6245 36723 30 _ _ (262779 / 12500) (420447 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1348735232 :
    ThetaLowerSegment 1348735232 1348866304 (134869178019493 / 100000)
      (134882321236477 / 100000) := by
  exact
    packedTile65536 1348735232 1348866304 14 6252 36725 30 _ _ (1051121 / 50000) (420449 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1348866304 :
    ThetaLowerSegment 1348866304 1348997376 (134882321236477 / 100000)
      (26979085335089 / 20000) := by
  exact
    packedTile65536 1348866304 1348997376 14 6234 36726 30 _ _ (525563 / 25000) (420451 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1348997376 :
    ThetaLowerSegment 1348997376 1349128448 (26979085335089 / 20000) (33727125159151 / 25000) := by
  exact
    packedTile65536 1348997376 1349128448 14 6219 36728 30 _ _ (2102261 / 100000) (262783 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1349128448 :
    ThetaLowerSegment 1349128448 1349259520 (33727125159151 / 25000)
      (134921465341861 / 100000) := by
  exact
    packedTile65536 1349128448 1349259520 14 6167 36730 30 _ _ (2102271 / 100000) (1051137 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1349259520 :
    ThetaLowerSegment 1349259520 1349390592 (134921465341861 / 100000)
      (67467313861601 / 50000) := by
  exact
    packedTile65536 1349259520 1349390592 14 6261 36732 30 _ _ (2102281 / 100000) (525571 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1349390592 :
    ThetaLowerSegment 1349390592 1349521664 (67467313861601 / 50000) (33736958051673 / 25000) := by
  exact
    packedTile65536 1349390592 1349521664 14 6281 36734 30 _ _ (210229 / 10000) (2102293 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1349521664 :
    ThetaLowerSegment 1349521664 1349652736 (33736958051673 / 25000) (33740226077023 / 25000) := by
  exact
    packedTile65536 1349521664 1349652736 14 6218 36735 30 _ _ (21023 / 1000) (2102303 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1349652736 :
    ThetaLowerSegment 1349652736 1349783808 (33740226077023 / 25000) (67486978775441 / 50000) := by
  exact
    packedTile65536 1349652736 1349783808 14 6209 36737 30 _ _ (210231 / 10000) (2102313 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1349783808 :
    ThetaLowerSegment 1349783808 1349914880 (67486978775441 / 50000) (67493448665241 / 50000) := by
  exact
    packedTile65536 1349783808 1349914880 14 6155 36739 30 _ _ (26279 / 1250) (2102323 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1349914880 :
    ThetaLowerSegment 1349914880 1350045952 (67493448665241 / 50000)
      (135000017965771 / 100000) := by
  exact
    packedTile65536 1349914880 1350045952 14 6241 36741 30 _ _ (2102329 / 100000) (525583 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1350045952 :
    ThetaLowerSegment 1350045952 1350177024 (135000017965771 / 100000)
      (67506468419463 / 50000) := by
  exact
    packedTile65536 1350045952 1350177024 14 6145 36742 30 _ _ (2102339 / 100000) (1051171 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1350177024 :
    ThetaLowerSegment 1350177024 1350308096 (67506468419463 / 50000) (27005203110411 / 20000) := by
  exact
    packedTile65536 1350177024 1350308096 14 6221 36744 30 _ _ (2102349 / 100000) (131397 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1350308096 :
    ThetaLowerSegment 1350308096 1350439168 (27005203110411 / 20000)
      (135039296147541 / 100000) := by
  exact
    packedTile65536 1350308096 1350439168 14 6317 36746 30 _ _ (1051179 / 50000) (2102361 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1350439168 :
    ThetaLowerSegment 1350439168 1350570240 (135039296147541 / 100000)
      (135052393900181 / 100000) := by
  exact
    packedTile65536 1350439168 1350570240 14 6230 36748 30 _ _ (65699 / 3125) (2102371 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1350570240 :
    ThetaLowerSegment 1350570240 1350701312 (135052393900181 / 100000)
      (135065640983959 / 100000) := by
  exact
    packedTile65536 1350570240 1350701312 14 6301 36750 30 _ _ (1051189 / 50000) (2102381 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1350701312 :
    ThetaLowerSegment 1350701312 1350832384 (135065640983959 / 100000)
      (67539322123777 / 50000) := by
  exact
    packedTile65536 1350701312 1350832384 14 6185 36751 30 _ _ (2102387 / 100000) (210239 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1350832384 :
    ThetaLowerSegment 1350832384 1350963456 (67539322123777 / 50000)
      (135091878836669 / 100000) := by
  exact
    packedTile65536 1350832384 1350963456 14 6295 36753 30 _ _ (2102397 / 100000) (2628 / 125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1350963456 :
    ThetaLowerSegment 1350963456 1351094528 (135091878836669 / 100000)
      (135105018880419 / 100000) := by
  exact
    packedTile65536 1350963456 1351094528 14 6250 36755 30 _ _ (2102407 / 100000) (210241 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1351094528 :
    ThetaLowerSegment 1351094528 1351225600 (135105018880419 / 100000)
      (33779513992059 / 25000) := by
  exact
    packedTile65536 1351094528 1351225600 14 6201 36757 30 _ _ (2102417 / 100000) (105121 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1351225600 :
    ThetaLowerSegment 1351225600 1351356672 (33779513992059 / 25000) (33782758035377 / 25000) := by
  exact
    packedTile65536 1351225600 1351356672 14 6172 36759 30 _ _ (1051213 / 50000) (2102429 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1351356672 :
    ThetaLowerSegment 1351356672 1351487744 (33782758035377 / 25000) (16893014975701 / 12500) := by
  exact
    packedTile65536 1351356672 1351487744 14 6225 36760 30 _ _ (525609 / 25000) (2102439 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1351487744 :
    ThetaLowerSegment 1351487744 1351618816 (16893014975701 / 12500) (2703142132291 / 2000) := by
  exact
    packedTile65536 1351487744 1351618816 14 6177 36762 30 _ _ (1051223 / 50000) (2102449 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1351618816 :
    ThetaLowerSegment 1351618816 1351749888 (2703142132291 / 2000) (27034017013853 / 20000) := by
  exact
    packedTile65536 1351618816 1351749888 14 6173 36764 30 _ _ (420491 / 20000) (1051229 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1351749888 :
    ThetaLowerSegment 1351749888 1351880960 (27034017013853 / 20000) (27036650141019 / 20000) := by
  exact
    packedTile65536 1351749888 1351880960 14 6262 36766 30 _ _ (420493 / 20000) (525617 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1351880960 :
    ThetaLowerSegment 1351880960 1352012032 (27036650141019 / 20000) (27039242913189 / 20000) := by
  exact
    packedTile65536 1351880960 1352012032 14 6166 36767 30 _ _ (84099 / 4000) (1051239 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1352012032 :
    ThetaLowerSegment 1352012032 1352143104 (27039242913189 / 20000) (27041864710737 / 20000) := by
  exact
    packedTile65536 1352012032 1352143104 14 6235 36769 30 _ _ (525621 / 25000) (2102487 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1352143104 :
    ThetaLowerSegment 1352143104 1352274176 (27041864710737 / 20000)
      (135222312761617 / 100000) := by
  exact
    packedTile65536 1352143104 1352274176 14 6178 36771 30 _ _ (1051247 / 50000) (2102497 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1352274176 :
    ThetaLowerSegment 1352274176 1352405248 (135222312761617 / 100000)
      (135235474436657 / 100000) := by
  exact
    packedTile65536 1352274176 1352405248 14 6260 36773 30 _ _ (262813 / 12500) (2102507 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1352405248 :
    ThetaLowerSegment 1352405248 1352536320 (135235474436657 / 100000)
      (135248613046643 / 100000) := by
  exact
    packedTile65536 1352405248 1352536320 14 6249 36775 30 _ _ (1051257 / 50000) (2102517 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1352536320 :
    ThetaLowerSegment 1352536320 1352667392 (135248613046643 / 100000)
      (135261879966773 / 100000) := by
  exact
    packedTile65536 1352536320 1352667392 14 6310 36776 30 _ _ (2102523 / 100000) (1051263 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1352667392 :
    ThetaLowerSegment 1352667392 1352798464 (135261879966773 / 100000) (5411004532379 / 4000) := by
  exact
    packedTile65536 1352667392 1352798464 14 6294 36778 30 _ _ (2102533 / 100000) (262817 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1352798464 :
    ThetaLowerSegment 1352798464 1352929536 (5411004532379 / 4000) (67644134460513 / 50000) := by
  exact
    packedTile65536 1352798464 1352929536 14 6257 36780 30 _ _ (2102543 / 100000) (1051273 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1352929536 :
    ThetaLowerSegment 1352929536 1353060608 (67644134460513 / 50000) (67650690217649 / 50000) := by
  exact
    packedTile65536 1352929536 1353060608 14 6236 36782 30 _ _ (262819 / 12500) (420511 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1353060608 :
    ThetaLowerSegment 1353060608 1353191680 (67650690217649 / 50000) (16914311238671 / 12500) := by
  exact
    packedTile65536 1353060608 1353191680 14 6235 36783 30 _ _ (1051281 / 50000) (420513 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1353191680 :
    ThetaLowerSegment 1353191680 1353322752 (16914311238671 / 12500) (16915941783257 / 12500) := by
  exact
    packedTile65536 1353191680 1353322752 14 6204 36785 30 _ _ (525643 / 25000) (84103 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1353322752 :
    ThetaLowerSegment 1353322752 1353339136 (16915941783257 / 12500) (67664593447361 / 50000) := by
  exact
    packedTile65536 1353322752 1353339136 11 786 36787 30 _ _ (2102581 / 100000) (262823 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1353339136 :
    ThetaLowerSegment 1353339136 1353341184 (67664593447361 / 50000)
      (135329374024609 / 100000) := by
  exact
    packedTile65536 1353339136 1353341184 8 89 36787 30 _ _ (2102583 / 100000) (1051293 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_1321341184_1353341184 :
    ThetaLowerSegment 1321341184 1353341184 (26425827251023 / 20000)
      (135329374024609 / 100000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1321341184 cell1321472256)
                    (ThetaLowerSegment.join cell1321537792 cell1321668864))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1321799936 cell1321931008)
                    (ThetaLowerSegment.join cell1322062080 cell1322193152)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1322324224 cell1322455296)
                    (ThetaLowerSegment.join cell1322586368 cell1322717440))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1322848512 cell1322979584)
                    (ThetaLowerSegment.join cell1323110656 cell1323176192))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1323241728 cell1323307264)
                    (ThetaLowerSegment.join cell1323372800 cell1323438336))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1323503872 cell1323569408)
                    (ThetaLowerSegment.join cell1323634944 cell1323700480)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1323766016 cell1323831552)
                    (ThetaLowerSegment.join cell1323897088 cell1323962624))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1324028160 cell1324093696)
                    (ThetaLowerSegment.join cell1324159232 cell1324224768)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1324290304 cell1324355840)
                    (ThetaLowerSegment.join cell1324421376 cell1324486912))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1324552448 cell1324617984)
                    (ThetaLowerSegment.join cell1324683520 cell1324749056)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1324814592 cell1324880128)
                    (ThetaLowerSegment.join cell1324945664 cell1325011200))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1325076736 cell1325142272)
                    (ThetaLowerSegment.join cell1325207808 cell1325273344))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1325338880 cell1325404416)
                    (ThetaLowerSegment.join cell1325469952 cell1325535488))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1325601024 cell1325666560)
                    (ThetaLowerSegment.join cell1325732096 cell1325797632)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1325863168 cell1325928704)
                    (ThetaLowerSegment.join cell1325994240 cell1326059776))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1326125312 cell1326190848)
                    (ThetaLowerSegment.join cell1326256384 cell1326321920))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1326387456 cell1326452992)
                    (ThetaLowerSegment.join cell1326518528 cell1326584064))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1326649600 cell1326715136)
                    (ThetaLowerSegment.join cell1326780672 cell1326846208)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1326911744 cell1326977280)
                    (ThetaLowerSegment.join cell1327042816 cell1327108352))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1327173888 cell1327239424)
                    (ThetaLowerSegment.join cell1327304960 cell1327370496))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1327436032 cell1327501568)
                    (ThetaLowerSegment.join cell1327567104 cell1327632640))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1327698176 cell1327763712)
                    (ThetaLowerSegment.join cell1327829248 cell1327894784)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1327960320 cell1328025856)
                    (ThetaLowerSegment.join cell1328091392 cell1328156928))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1328222464 cell1328288000)
                    (ThetaLowerSegment.join cell1328353536 cell1328419072)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1328484608 cell1328550144)
                    (ThetaLowerSegment.join cell1328615680 cell1328681216))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1328746752 cell1328812288)
                    (ThetaLowerSegment.join cell1328877824 cell1328943360)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1329008896 cell1329074432)
                    (ThetaLowerSegment.join cell1329139968 cell1329205504))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1329271040 cell1329336576)
                    (ThetaLowerSegment.join cell1329402112 cell1329467648))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1329533184 cell1329598720)
                    (ThetaLowerSegment.join cell1329664256 cell1329729792))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1329795328 cell1329860864)
                    (ThetaLowerSegment.join cell1329926400 cell1329991936)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1330057472 cell1330123008)
                    (ThetaLowerSegment.join cell1330188544 cell1330254080))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1330319616 cell1330385152)
                    (ThetaLowerSegment.join cell1330450688 cell1330516224)))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1330581760 cell1330647296)
                    (ThetaLowerSegment.join cell1330712832 cell1330778368))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1330843904 cell1330909440)
                    (ThetaLowerSegment.join cell1330974976 cell1331040512)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1331106048 cell1331171584)
                    (ThetaLowerSegment.join cell1331237120 cell1331302656))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1331368192 cell1331433728)
                    (ThetaLowerSegment.join cell1331499264 cell1331564800))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1331630336 cell1331695872)
                    (ThetaLowerSegment.join cell1331761408 cell1331826944))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1331892480 cell1331958016)
                    (ThetaLowerSegment.join cell1332023552 cell1332089088)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1332154624 cell1332220160)
                    (ThetaLowerSegment.join cell1332285696 cell1332351232))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1332416768 cell1332482304)
                    (ThetaLowerSegment.join cell1332547840 cell1332613376)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1332678912 cell1332744448)
                    (ThetaLowerSegment.join cell1332809984 cell1332875520))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1332941056 cell1333006592)
                    (ThetaLowerSegment.join cell1333072128 cell1333137664)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1333203200 cell1333268736)
                    (ThetaLowerSegment.join cell1333399808 cell1333465344))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1333530880 cell1333596416)
                    (ThetaLowerSegment.join cell1333661952 cell1333727488))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1333793024 cell1333858560)
                    (ThetaLowerSegment.join cell1333924096 cell1333989632))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1334055168 cell1334120704)
                    (ThetaLowerSegment.join cell1334186240 cell1334317312)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1334448384 cell1334579456)
                    (ThetaLowerSegment.join cell1334710528 cell1334776064))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1334907136 cell1335038208)
                    (ThetaLowerSegment.join cell1335169280 cell1335300352))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1335431424 cell1335562496)
                    (ThetaLowerSegment.join cell1335693568 cell1335824640))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1335955712 cell1336086784)
                    (ThetaLowerSegment.join cell1336217856 cell1336348928)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1336480000 cell1336611072)
                    (ThetaLowerSegment.join cell1336742144 cell1336873216))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1337004288 cell1337135360)
                    (ThetaLowerSegment.join cell1337266432 cell1337397504))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1337528576 cell1337659648)
                    (ThetaLowerSegment.join cell1337790720 cell1337921792))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1338052864 cell1338183936)
                    (ThetaLowerSegment.join cell1338315008 cell1338446080)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1338577152 cell1338708224)
                    (ThetaLowerSegment.join cell1338839296 cell1338970368))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1339101440 cell1339232512)
                    (ThetaLowerSegment.join cell1339363584 cell1339494656)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1339625728 cell1339756800)
                    (ThetaLowerSegment.join cell1339887872 cell1340018944))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1340150016 cell1340281088)
                    (ThetaLowerSegment.join cell1340346624 cell1340477696)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1340608768 cell1340739840)
                    (ThetaLowerSegment.join cell1340870912 cell1341001984))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1341133056 cell1341264128)
                    (ThetaLowerSegment.join cell1341395200 cell1341526272))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1341657344 cell1341788416)
                    (ThetaLowerSegment.join cell1341919488 cell1342050560))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1342181632 cell1342312704)
                    (ThetaLowerSegment.join cell1342443776 cell1342574848)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1342705920 cell1342836992)
                    (ThetaLowerSegment.join cell1342968064 cell1343099136))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1343230208 cell1343361280)
                    (ThetaLowerSegment.join cell1343492352 cell1343623424))))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1343754496 cell1343885568)
                  (ThetaLowerSegment.join cell1344016640 cell1344147712))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1344278784 cell1344409856)
                  (ThetaLowerSegment.join cell1344540928 cell1344672000)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1344803072 cell1344934144)
                  (ThetaLowerSegment.join cell1345065216 cell1345196288))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1345327360 cell1345458432)
                  (ThetaLowerSegment.join cell1345589504 cell1345720576))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1345851648 cell1345982720)
                  (ThetaLowerSegment.join cell1346113792 cell1346244864))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1346375936 cell1346507008)
                  (ThetaLowerSegment.join cell1346638080 cell1346769152)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1346900224 cell1347031296)
                  (ThetaLowerSegment.join cell1347162368 cell1347293440))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1347424512 cell1347555584)
                  (ThetaLowerSegment.join cell1347686656 cell1347817728)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1347948800 cell1348079872)
                  (ThetaLowerSegment.join cell1348210944 cell1348342016))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1348473088 cell1348604160)
                  (ThetaLowerSegment.join cell1348735232 cell1348866304)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1348997376 cell1349128448)
                  (ThetaLowerSegment.join cell1349259520 cell1349390592))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1349521664 cell1349652736)
                  (ThetaLowerSegment.join cell1349783808 cell1349914880))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1350045952 cell1350177024)
                  (ThetaLowerSegment.join cell1350308096 cell1350439168))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1350570240 cell1350701312)
                  (ThetaLowerSegment.join cell1350832384 cell1350963456)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1351094528 cell1351225600)
                  (ThetaLowerSegment.join cell1351356672 cell1351487744))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1351618816 cell1351749888)
                  (ThetaLowerSegment.join cell1351880960 cell1352012032))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join (ThetaLowerSegment.join cell1352143104 cell1352274176)
              (ThetaLowerSegment.join cell1352405248 cell1352536320))
            (ThetaLowerSegment.join (ThetaLowerSegment.join cell1352667392 cell1352798464)
              (ThetaLowerSegment.join cell1352929536 cell1353060608)))
          (ThetaLowerSegment.join (ThetaLowerSegment.join cell1353191680 cell1353322752)
            cell1353339136))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
