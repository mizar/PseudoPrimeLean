/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaDivisorBase4096

/-! # Direct theta estimate up to 8096000 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell4000000 :
    ThetaLowerSegment 4000000 4004096 (39965831043 / 10000) (100018709869 / 25000) := by
  exact
    thetaTile4096 4000000 4004096 7 5 274 2000 22 _ _ (1520179 / 100000) (760091 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4004096 :
    ThetaLowerSegment 4004096 4008192 (100018709869 / 25000) (40049139647 / 10000) := by
  exact
    thetaTile4096 4004096 4008192 7 5 274 2001 22 _ _ (1520281 / 100000) (380071 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4008192 :
    ThetaLowerSegment 4008192 4012288 (40049139647 / 10000) (200453990843 / 50000) := by
  exact
    thetaTile4096 4008192 4012288 7 5 274 2002 22 _ _ (47512 / 3125) (1520387 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4012288 :
    ThetaLowerSegment 4012288 4016384 (200453990843 / 50000) (25082502087 / 6250) := by
  exact
    thetaTile4096 4012288 4016384 7 5 271 2003 22 _ _ (760243 / 50000) (1520489 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4016384 :
    ThetaLowerSegment 4016384 4020480 (25082502087 / 6250) (100426945833 / 25000) := by
  exact
    thetaTile4096 4016384 4020480 7 5 255 2004 22 _ _ (380147 / 25000) (1520591 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4020480 :
    ThetaLowerSegment 4020480 4024576 (100426945833 / 25000) (201066027921 / 50000) := by
  exact
    thetaTile4096 4020480 4024576 7 5 279 2005 22 _ _ (152069 / 10000) (1520693 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4024576 :
    ThetaLowerSegment 4024576 4028672 (201066027921 / 50000) (40254114889 / 10000) := by
  exact
    thetaTile4096 4024576 4028672 7 5 269 2006 22 _ _ (190099 / 12500) (304159 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4028672 :
    ThetaLowerSegment 4028672 4032768 (40254114889 / 10000) (40295179 / 10) := by
  exact
    thetaTile4096 4028672 4032768 7 5 270 2007 22 _ _ (1520893 / 100000) (47528 / 3125) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4032768 :
    ThetaLowerSegment 4032768 4036864 (40295179 / 10) (40338679457 / 10000) := by
  exact
    thetaTile4096 4032768 4036864 7 5 286 2008 22 _ _ (304199 / 20000) (760499 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4036864 :
    ThetaLowerSegment 4036864 4040960 (40338679457 / 10000) (201905590177 / 50000) := by
  exact
    thetaTile4096 4036864 4040960 7 5 279 2009 22 _ _ (190137 / 12500) (1521099 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4040960 :
    ThetaLowerSegment 4040960 4045056 (201905590177 / 50000) (12632457406 / 3125) := by
  exact
    thetaTile4096 4040960 4045056 7 5 281 2010 22 _ _ (760599 / 50000) (1521201 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4045056 :
    ThetaLowerSegment 4045056 4049152 (12632457406 / 3125) (50583075089 / 12500) := by
  exact
    thetaTile4096 4045056 4049152 7 5 280 2011 22 _ _ (1521299 / 100000) (760651 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4049152 :
    ThetaLowerSegment 4049152 4053248 (50583075089 / 12500) (12658177691 / 3125) := by
  exact
    thetaTile4096 4049152 4053248 7 5 261 2012 22 _ _ (7607 / 500) (1521403 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4053248 :
    ThetaLowerSegment 4053248 4057344 (12658177691 / 3125) (101361276091 / 25000) := by
  exact
    thetaTile4096 4053248 4057344 7 5 252 2013 22 _ _ (1521501 / 100000) (47547 / 3125) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4057344 :
    ThetaLowerSegment 4057344 4061440 (101361276091 / 25000) (202933294059 / 50000) := by
  exact
    thetaTile4096 4057344 4061440 7 5 277 2014 22 _ _ (760801 / 50000) (304321 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4061440 :
    ThetaLowerSegment 4061440 4065536 (202933294059 / 50000) (40626831771 / 10000) := by
  exact
    thetaTile4096 4061440 4065536 7 5 264 2015 22 _ _ (1521703 / 100000) (760853 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4065536 :
    ThetaLowerSegment 4065536 4069632 (40626831771 / 10000) (203340363297 / 50000) := by
  exact
    thetaTile4096 4065536 4069632 7 5 271 2016 22 _ _ (380451 / 25000) (1521807 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4069632 :
    ThetaLowerSegment 4069632 4073728 (203340363297 / 50000) (407093162849 / 100000) := by
  exact
    thetaTile4096 4069632 4073728 7 5 271 2017 22 _ _ (304381 / 20000) (380477 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4073728 :
    ThetaLowerSegment 4073728 4077824 (407093162849 / 100000) (203757379117 / 50000) := by
  exact
    thetaTile4096 4073728 4077824 7 5 277 2018 22 _ _ (304401 / 20000) (190251 / 12500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4077824 :
    ThetaLowerSegment 4077824 4081920 (203757379117 / 50000) (2549545306 / 625) := by
  exact
    thetaTile4096 4077824 4081920 7 5 271 2019 22 _ _ (761053 / 50000) (1522109 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4081920 :
    ThetaLowerSegment 4081920 4086016 (2549545306 / 625) (102081516733 / 25000) := by
  exact
    thetaTile4096 4081920 4086016 7 5 262 2020 22 _ _ (761103 / 50000) (1522209 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4086016 :
    ThetaLowerSegment 4086016 4090112 (102081516733 / 25000) (408741656743 / 100000) := by
  exact
    thetaTile4096 4086016 4090112 7 5 273 2021 22 _ _ (1522307 / 100000) (152231 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4090112 :
    ThetaLowerSegment 4090112 4094208 (408741656743 / 100000) (102290079667 / 25000) := by
  exact
    thetaTile4096 4090112 4094208 7 5 275 2022 22 _ _ (1522407 / 100000) (152241 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4094208 :
    ThetaLowerSegment 4094208 4098304 (102290079667 / 25000) (409566828037 / 100000) := by
  exact
    thetaTile4096 4094208 4098304 7 5 267 2023 22 _ _ (1522507 / 100000) (152251 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4098304 :
    ThetaLowerSegment 4098304 4102400 (409566828037 / 100000) (204983636839 / 50000) := by
  exact
    thetaTile4096 4098304 4102400 7 5 263 2024 22 _ _ (1522607 / 100000) (152261 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4102400 :
    ThetaLowerSegment 4102400 4106496 (204983636839 / 50000) (41038754081 / 10000) := by
  exact
    thetaTile4096 4102400 4106496 7 5 276 2025 22 _ _ (1522707 / 100000) (152271 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4106496 :
    ThetaLowerSegment 4106496 4110592 (41038754081 / 10000) (410815449577 / 100000) := by
  exact
    thetaTile4096 4106496 4110592 7 5 281 2026 22 _ _ (1522807 / 100000) (152281 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4110592 :
    ThetaLowerSegment 4110592 4114688 (410815449577 / 100000) (411196176077 / 100000) := by
  exact
    thetaTile4096 4110592 4114688 7 5 250 2027 22 _ _ (761453 / 50000) (1522909 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4114688 :
    ThetaLowerSegment 4114688 4118784 (411196176077 / 100000) (411590634631 / 100000) := by
  exact
    thetaTile4096 4114688 4118784 7 5 259 2028 22 _ _ (761503 / 50000) (1523009 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4118784 :
    ThetaLowerSegment 4118784 4122880 (411590634631 / 100000) (205992559413 / 50000) := by
  exact
    thetaTile4096 4118784 4122880 7 5 259 2029 22 _ _ (304621 / 20000) (380777 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4122880 :
    ThetaLowerSegment 4122880 4126976 (205992559413 / 50000) (412397907381 / 100000) := by
  exact
    thetaTile4096 4122880 4126976 7 5 271 2030 22 _ _ (304641 / 20000) (190401 / 12500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4126976 :
    ThetaLowerSegment 4126976 4131072 (412397907381 / 100000) (412801582941 / 100000) := by
  exact
    thetaTile4096 4126976 4131072 7 5 265 2031 22 _ _ (190413 / 12500) (1523307 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4131072 :
    ThetaLowerSegment 4131072 4135168 (412801582941 / 100000) (413185480497 / 100000) := by
  exact
    thetaTile4096 4131072 4135168 7 5 252 2032 22 _ _ (1523403 / 100000) (761703 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4135168 :
    ThetaLowerSegment 4135168 4139264 (413185480497 / 100000) (413584638021 / 100000) := by
  exact
    thetaTile4096 4135168 4139264 7 5 262 2033 22 _ _ (761751 / 50000) (304701 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4139264 :
    ThetaLowerSegment 4139264 4143360 (413584638021 / 100000) (413999057493 / 100000) := by
  exact
    thetaTile4096 4139264 4143360 7 5 272 2034 22 _ _ (1523601 / 100000) (380901 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4143360 :
    ThetaLowerSegment 4143360 4147456 (413999057493 / 100000) (414396743193 / 100000) := by
  exact
    thetaTile4096 4143360 4147456 7 5 261 2035 22 _ _ (15237 / 1000) (1523703 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4147456 :
    ThetaLowerSegment 4147456 4151552 (414396743193 / 100000) (82967119461 / 20000) := by
  exact
    thetaTile4096 4147456 4151552 7 5 288 2036 22 _ _ (1523799 / 100000) (761901 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4151552 :
    ThetaLowerSegment 4151552 4155648 (82967119461 / 20000) (415240954173 / 100000) := by
  exact
    thetaTile4096 4151552 4155648 7 5 266 2037 22 _ _ (761949 / 50000) (1523901 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4155648 :
    ThetaLowerSegment 4155648 4159744 (415240954173 / 100000) (415661577069 / 100000) := by
  exact
    thetaTile4096 4155648 4159744 7 5 276 2038 22 _ _ (380999 / 25000) (1523999 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4159744 :
    ThetaLowerSegment 4159744 4163840 (415661577069 / 100000) (208049496167 / 50000) := by
  exact
    thetaTile4096 4159744 4163840 7 5 287 2039 22 _ _ (304819 / 20000) (762049 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4163840 :
    ThetaLowerSegment 4163840 4167936 (208049496167 / 50000) (104127631111 / 25000) := by
  exact
    thetaTile4096 4163840 4167936 7 5 270 2040 22 _ _ (1524193 / 100000) (381049 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4167936 :
    ThetaLowerSegment 4167936 4172032 (104127631111 / 25000) (52112402363 / 12500) := by
  exact
    thetaTile4096 4167936 4172032 7 5 255 2041 22 _ _ (381073 / 25000) (304859 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4172032 :
    ThetaLowerSegment 4172032 4176128 (52112402363 / 12500) (104326176661 / 25000) := by
  exact
    thetaTile4096 4172032 4176128 7 5 266 2042 22 _ _ (152439 / 10000) (1524393 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4176128 :
    ThetaLowerSegment 4176128 4180224 (104326176661 / 25000) (20885587247 / 5000) := by
  exact
    thetaTile4096 4176128 4180224 7 5 267 2043 22 _ _ (190561 / 12500) (1524491 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4180224 :
    ThetaLowerSegment 4180224 4184320 (20885587247 / 5000) (209067027631 / 50000) := by
  exact
    thetaTile4096 4180224 4184320 7 5 277 2044 22 _ _ (762293 / 50000) (1524589 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4184320 :
    ThetaLowerSegment 4184320 4188416 (209067027631 / 50000) (209276671681 / 50000) := by
  exact
    thetaTile4096 4184320 4188416 7 5 275 2045 22 _ _ (381171 / 25000) (1524687 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4188416 :
    ThetaLowerSegment 4188416 4192512 (209276671681 / 50000) (104746214167 / 25000) := by
  exact
    thetaTile4096 4188416 4192512 7 5 283 2046 22 _ _ (762391 / 50000) (304957 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4192512 :
    ThetaLowerSegment 4192512 4196608 (104746214167 / 25000) (104844950147 / 25000) := by
  exact
    thetaTile4096 4192512 4196608 7 5 259 2047 22 _ _ (19061 / 1250) (1524883 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4196608 :
    ThetaLowerSegment 4196608 4200704 (104844950147 / 25000) (41978544447 / 10000) := by
  exact
    thetaTile4096 4196608 4200704 7 5 266 2048 22 _ _ (1524977 / 100000) (76249 / 5000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4200704 :
    ThetaLowerSegment 4200704 4204800 (41978544447 / 10000) (84039137929 / 20000) := by
  exact
    thetaTile4096 4200704 4204800 7 5 269 2049 22 _ _ (61003 / 4000) (762539 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4204800 :
    ThetaLowerSegment 4204800 4208896 (84039137929 / 20000) (420619687461 / 100000) := by
  exact
    thetaTile4096 4204800 4208896 7 5 278 2050 22 _ _ (381293 / 25000) (61007 / 4000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4208896 :
    ThetaLowerSegment 4208896 4212992 (420619687461 / 100000) (421037611441 / 100000) := by
  exact
    thetaTile4096 4208896 4212992 7 5 274 2051 22 _ _ (152527 / 10000) (1525273 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4212992 :
    ThetaLowerSegment 4212992 4217088 (421037611441 / 100000) (210713290013 / 50000) := by
  exact
    thetaTile4096 4212992 4217088 7 5 255 2052 22 _ _ (1525367 / 100000) (152537 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4217088 :
    ThetaLowerSegment 4217088 4221184 (210713290013 / 50000) (8436647069 / 2000) := by
  exact
    thetaTile4096 4217088 4221184 7 5 266 2053 22 _ _ (190683 / 12500) (1525467 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4221184 :
    ThetaLowerSegment 4221184 4225280 (8436647069 / 2000) (42225951053 / 10000) := by
  exact
    thetaTile4096 4221184 4225280 7 5 280 2054 22 _ _ (1525561 / 100000) (381391 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4225280 :
    ThetaLowerSegment 4225280 4229376 (42225951053 / 10000) (26415915997 / 6250) := by
  exact
    thetaTile4096 4225280 4229376 7 5 259 2055 22 _ _ (762829 / 50000) (1525661 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4229376 :
    ThetaLowerSegment 4229376 4233472 (26415915997 / 6250) (423052878007 / 100000) := by
  exact
    thetaTile4096 4229376 4233472 7 5 261 2056 22 _ _ (305151 / 20000) (762879 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4233472 :
    ThetaLowerSegment 4233472 4237568 (423052878007 / 100000) (423445021971 / 100000) := by
  exact
    thetaTile4096 4233472 4237568 7 5 257 2057 22 _ _ (381463 / 25000) (305171 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4237568 :
    ThetaLowerSegment 4237568 4241664 (423445021971 / 100000) (84773236779 / 20000) := by
  exact
    thetaTile4096 4237568 4241664 7 5 276 2058 22 _ _ (1525949 / 100000) (47686 / 3125) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4241664 :
    ThetaLowerSegment 4241664 4245760 (84773236779 / 20000) (16970762391 / 4000) := by
  exact
    thetaTile4096 4241664 4245760 7 5 264 2059 22 _ _ (305209 / 20000) (47689 / 3125) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4245760 :
    ThetaLowerSegment 4245760 4249856 (16970762391 / 4000) (424678065831 / 100000) := by
  exact
    thetaTile4096 4245760 4249856 7 5 268 2060 22 _ _ (763071 / 50000) (305229 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4249856 :
    ThetaLowerSegment 4249856 4253952 (424678065831 / 100000) (425114569899 / 100000) := by
  exact
    thetaTile4096 4249856 4253952 7 5 286 2061 22 _ _ (763119 / 50000) (1526241 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4253952 :
    ThetaLowerSegment 4253952 4258048 (425114569899 / 100000) (425508364071 / 100000) := by
  exact
    thetaTile4096 4253952 4258048 7 5 258 2062 22 _ _ (763167 / 50000) (1526337 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4258048 :
    ThetaLowerSegment 4258048 4262144 (425508364071 / 100000) (425914394717 / 100000) := by
  exact
    thetaTile4096 4258048 4262144 7 5 266 2063 22 _ _ (1526431 / 100000) (763217 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4262144 :
    ThetaLowerSegment 4262144 4266240 (425914394717 / 100000) (426326557007 / 100000) := by
  exact
    thetaTile4096 4262144 4266240 7 5 270 2064 22 _ _ (1526527 / 100000) (152653 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4266240 :
    ThetaLowerSegment 4266240 4270336 (426326557007 / 100000) (426720425741 / 100000) := by
  exact
    thetaTile4096 4266240 4270336 7 5 258 2065 22 _ _ (1526623 / 100000) (763313 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4270336 :
    ThetaLowerSegment 4270336 4274432 (426720425741 / 100000) (85428360037 / 20000) := by
  exact
    thetaTile4096 4270336 4274432 7 5 276 2066 22 _ _ (1526719 / 100000) (763361 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4274432 :
    ThetaLowerSegment 4274432 4278528 (85428360037 / 20000) (10688354791 / 2500) := by
  exact
    thetaTile4096 4274432 4278528 7 5 257 2067 22 _ _ (305363 / 20000) (763409 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4278528 :
    ThetaLowerSegment 4278528 4282624 (10688354791 / 2500) (1711791937 / 400) := by
  exact
    thetaTile4096 4278528 4282624 7 5 271 2068 22 _ _ (152691 / 10000) (1526913 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4282624 :
    ThetaLowerSegment 4282624 4286720 (1711791937 / 400) (21416868539 / 5000) := by
  exact
    thetaTile4096 4282624 4286720 7 5 255 2069 22 _ _ (763503 / 50000) (1527009 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4286720 :
    ThetaLowerSegment 4286720 4290816 (21416868539 / 5000) (42872678179 / 10000) := by
  exact
    thetaTile4096 4286720 4290816 7 5 255 2070 22 _ _ (763551 / 50000) (305421 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4290816 :
    ThetaLowerSegment 4290816 4294912 (42872678179 / 10000) (429137597783 / 100000) := by
  exact
    thetaTile4096 4290816 4294912 7 5 269 2071 22 _ _ (1527197 / 100000) (1909 / 125) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4294912 :
    ThetaLowerSegment 4294912 4299008 (429137597783 / 100000) (1073871099 / 250) := by
  exact
    thetaTile4096 4294912 4299008 7 5 269 2072 22 _ _ (1527293 / 100000) (47728 / 3125) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4299008 :
    ThetaLowerSegment 4299008 4303104 (1073871099 / 250) (107490590437 / 25000) := by
  exact
    thetaTile4096 4299008 4303104 7 5 271 2073 22 _ _ (381847 / 25000) (1527391 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4303104 :
    ThetaLowerSegment 4303104 4307200 (107490590437 / 25000) (215184336113 / 50000) := by
  exact
    thetaTile4096 4303104 4307200 7 5 266 2074 22 _ _ (1527483 / 100000) (763743 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4307200 :
    ThetaLowerSegment 4307200 4311296 (215184336113 / 50000) (10769260631 / 2500) := by
  exact
    thetaTile4096 4307200 4311296 7 5 263 2075 22 _ _ (763789 / 50000) (1527581 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4311296 :
    ThetaLowerSegment 4311296 4315392 (10769260631 / 2500) (431184424623 / 100000) := by
  exact
    thetaTile4096 4311296 4315392 7 5 271 2076 22 _ _ (1527673 / 100000) (381919 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4315392 :
    ThetaLowerSegment 4315392 4319488 (431184424623 / 100000) (431613727431 / 100000) := by
  exact
    thetaTile4096 4315392 4319488 7 5 281 2077 22 _ _ (190971 / 12500) (1527771 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4319488 :
    ThetaLowerSegment 4319488 4323584 (431613727431 / 100000) (431989581729 / 100000) := by
  exact
    thetaTile4096 4319488 4323584 7 5 246 2078 22 _ _ (1527863 / 100000) (763933 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4323584 :
    ThetaLowerSegment 4323584 4327680 (431989581729 / 100000) (86484093177 / 20000) := by
  exact
    thetaTile4096 4323584 4327680 7 5 282 2079 22 _ _ (763979 / 50000) (1527961 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4327680 :
    ThetaLowerSegment 4327680 4331776 (86484093177 / 20000) (432814703559 / 100000) := by
  exact
    thetaTile4096 4327680 4331776 7 5 258 2080 22 _ _ (1528053 / 100000) (191007 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4331776 :
    ThetaLowerSegment 4331776 4335872 (432814703559 / 100000) (21660830311 / 5000) := by
  exact
    thetaTile4096 4331776 4335872 7 5 263 2081 22 _ _ (1528147 / 100000) (30563 / 2000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4335872 :
    ThetaLowerSegment 4335872 4339968 (21660830311 / 5000) (54206710429 / 12500) := by
  exact
    thetaTile4096 4335872 4339968 7 5 286 2082 22 _ _ (764121 / 50000) (305649 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4339968 :
    ThetaLowerSegment 4339968 4344064 (54206710429 / 12500) (10851199853 / 2500) := by
  exact
    thetaTile4096 4339968 4344064 7 5 258 2083 22 _ _ (95521 / 6250) (1528339 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4344064 :
    ThetaLowerSegment 4344064 4348160 (10851199853 / 2500) (434440800887 / 100000) := by
  exact
    thetaTile4096 4344064 4348160 7 5 257 2084 22 _ _ (1528431 / 100000) (764217 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4348160 :
    ThetaLowerSegment 4348160 4352256 (434440800887 / 100000) (434847388537 / 100000) := by
  exact
    thetaTile4096 4348160 4352256 7 5 266 2085 22 _ _ (61141 / 4000) (95533 / 6250) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4352256 :
    ThetaLowerSegment 4352256 4356352 (434847388537 / 100000) (435254001191 / 100000) := by
  exact
    thetaTile4096 4352256 4356352 7 5 266 2086 22 _ _ (1528619 / 100000) (764311 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4356352 :
    ThetaLowerSegment 4356352 4360448 (435254001191 / 100000) (435651466571 / 100000) := by
  exact
    thetaTile4096 4356352 4360448 7 5 260 2087 22 _ _ (1528713 / 100000) (382179 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4360448 :
    ThetaLowerSegment 4360448 4364544 (435651466571 / 100000) (436058129233 / 100000) := by
  exact
    thetaTile4096 4360448 4364544 7 5 266 2088 22 _ _ (1528807 / 100000) (152881 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4364544 :
    ThetaLowerSegment 4364544 4368640 (436058129233 / 100000) (218234701801 / 50000) := by
  exact
    thetaTile4096 4364544 4368640 7 5 269 2089 22 _ _ (1528901 / 100000) (191113 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4368640 :
    ThetaLowerSegment 4368640 4372736 (218234701801 / 50000) (54611043529 / 12500) := by
  exact
    thetaTile4096 4368640 4372736 7 5 274 2090 22 _ _ (305799 / 20000) (764499 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4372736 :
    ThetaLowerSegment 4372736 4376832 (54611043529 / 12500) (54662267977 / 12500) := by
  exact
    thetaTile4096 4372736 4376832 7 5 268 2091 22 _ _ (47784 / 3125) (1529091 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4376832 :
    ThetaLowerSegment 4376832 4380928 (54662267977 / 12500) (218854746887 / 50000) := by
  exact
    thetaTile4096 4376832 4380928 7 5 269 2092 22 _ _ (764591 / 50000) (305837 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4380928 :
    ThetaLowerSegment 4380928 4385024 (218854746887 / 50000) (219068845527 / 50000) := by
  exact
    thetaTile4096 4380928 4385024 7 5 280 2093 22 _ _ (382319 / 25000) (1529279 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4385024 :
    ThetaLowerSegment 4385024 4389120 (219068845527 / 50000) (54815004163 / 12500) := by
  exact
    thetaTile4096 4385024 4389120 7 5 250 2094 22 _ _ (1529369 / 100000) (382343 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4389120 :
    ThetaLowerSegment 4389120 4393216 (54815004163 / 12500) (219470317677 / 50000) := by
  exact
    thetaTile4096 4389120 4393216 7 5 275 2095 22 _ _ (764731 / 50000) (305893 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4393216 :
    ThetaLowerSegment 4393216 4397312 (219470317677 / 50000) (219670689513 / 50000) := by
  exact
    thetaTile4096 4393216 4397312 7 5 262 2096 22 _ _ (382389 / 25000) (1529559 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4397312 :
    ThetaLowerSegment 4397312 4401408 (219670689513 / 50000) (439728380223 / 100000) := by
  exact
    thetaTile4096 4397312 4401408 7 5 253 2096 22 _ _ (1529649 / 100000) (382413 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4401408 :
    ThetaLowerSegment 4401408 4405504 (439728380223 / 100000) (440152118757 / 100000) := by
  exact
    thetaTile4096 4401408 4405504 7 5 277 2097 22 _ _ (764871 / 50000) (305949 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4405504 :
    ThetaLowerSegment 4405504 4409600 (440152118757 / 100000) (220268053671 / 50000) := by
  exact
    thetaTile4096 4405504 4409600 7 5 251 2098 22 _ _ (305967 / 20000) (764919 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4409600 :
    ThetaLowerSegment 4409600 4413696 (220268053671 / 50000) (220484538483 / 50000) := by
  exact
    thetaTile4096 4409600 4413696 7 5 283 2099 22 _ _ (191241 / 12500) (1529931 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4413696 :
    ThetaLowerSegment 4413696 4417792 (220484538483 / 50000) (110345545659 / 25000) := by
  exact
    thetaTile4096 4413696 4417792 7 5 270 2100 22 _ _ (1530021 / 100000) (191253 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4417792 :
    ThetaLowerSegment 4417792 4421888 (110345545659 / 25000) (220904542221 / 50000) := by
  exact
    thetaTile4096 4417792 4421888 7 5 279 2101 22 _ _ (765057 / 50000) (1530117 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4421888 :
    ThetaLowerSegment 4421888 4425984 (220904542221 / 50000) (110559002979 / 25000) := by
  exact
    thetaTile4096 4421888 4425984 7 5 279 2102 22 _ _ (765103 / 50000) (1530209 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4425984 :
    ThetaLowerSegment 4425984 4430080 (110559002979 / 25000) (88533205187 / 20000) := by
  exact
    thetaTile4096 4425984 4430080 7 5 281 2103 22 _ _ (1530299 / 100000) (765151 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4430080 :
    ThetaLowerSegment 4430080 4434176 (88533205187 / 20000) (88612785519 / 20000) := by
  exact
    thetaTile4096 4430080 4434176 7 5 260 2104 22 _ _ (1530391 / 100000) (765197 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4434176 :
    ThetaLowerSegment 4434176 4438272 (88612785519 / 20000) (443489402147 / 100000) := by
  exact
    thetaTile4096 4434176 4438272 7 5 278 2105 22 _ _ (382621 / 25000) (1530487 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4438272 :
    ThetaLowerSegment 4438272 4442368 (443489402147 / 100000) (88784511031 / 20000) := by
  exact
    thetaTile4096 4438272 4442368 7 5 283 2106 22 _ _ (95661 / 6250) (1530579 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4442368 :
    ThetaLowerSegment 4442368 4446464 (88784511031 / 20000) (444338896851 / 100000) := by
  exact
    thetaTile4096 4442368 4446464 7 5 272 2107 22 _ _ (382667 / 25000) (1530671 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4446464 :
    ThetaLowerSegment 4446464 4450560 (444338896851 / 100000) (444746079011 / 100000) := by
  exact
    thetaTile4096 4446464 4450560 7 5 266 2108 22 _ _ (38269 / 2500) (1530763 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4450560 :
    ThetaLowerSegment 4450560 4454656 (444746079011 / 100000) (445162471027 / 100000) := by
  exact
    thetaTile4096 4450560 4454656 7 5 272 2109 22 _ _ (1530853 / 100000) (191357 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4454656 :
    ThetaLowerSegment 4454656 4458752 (445162471027 / 100000) (445569702397 / 100000) := by
  exact
    thetaTile4096 4454656 4458752 7 5 266 2110 22 _ _ (306189 / 20000) (382737 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4458752 :
    ThetaLowerSegment 4458752 4462848 (445569702397 / 100000) (445989206261 / 100000) := by
  exact
    thetaTile4096 4458752 4462848 7 5 274 2111 22 _ _ (382759 / 25000) (1531039 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4462848 :
    ThetaLowerSegment 4462848 4466944 (445989206261 / 100000) (446388830669 / 100000) := by
  exact
    thetaTile4096 4462848 4466944 7 5 261 2112 22 _ _ (191391 / 12500) (1531131 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4466944 :
    ThetaLowerSegment 4466944 4471040 (446388830669 / 100000) (446811447389 / 100000) := by
  exact
    thetaTile4096 4466944 4471040 7 5 276 2113 22 _ _ (76561 / 5000) (1531223 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4471040 :
    ThetaLowerSegment 4471040 4475136 (446811447389 / 100000) (447208057197 / 100000) := by
  exact
    thetaTile4096 4471040 4475136 7 5 259 2114 22 _ _ (95707 / 6250) (306263 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4475136 :
    ThetaLowerSegment 4475136 4479232 (447208057197 / 100000) (111908063957 / 25000) := by
  exact
    thetaTile4096 4475136 4479232 7 5 277 2115 22 _ _ (1531403 / 100000) (765703 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4479232 :
    ThetaLowerSegment 4479232 4483328 (111908063957 / 25000) (224016753759 / 50000) := by
  exact
    thetaTile4096 4479232 4483328 7 5 262 2116 22 _ _ (306299 / 20000) (765749 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4483328 :
    ThetaLowerSegment 4483328 4487424 (224016753759 / 50000) (56060282777 / 12500) := by
  exact
    thetaTile4096 4483328 4487424 7 5 293 2117 22 _ _ (765793 / 50000) (1531589 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4487424 :
    ThetaLowerSegment 4487424 4491520 (56060282777 / 12500) (448882029913 / 100000) := by
  exact
    thetaTile4096 4487424 4491520 7 5 261 2118 22 _ _ (1531677 / 100000) (9573 / 625) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4491520 :
    ThetaLowerSegment 4491520 4495616 (448882029913 / 100000) (449286416929 / 100000) := by
  exact
    thetaTile4096 4491520 4495616 7 5 264 2119 22 _ _ (1531769 / 100000) (382943 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4495616 :
    ThetaLowerSegment 4495616 4499712 (449286416929 / 100000) (449687764249 / 100000) := by
  exact
    thetaTile4096 4495616 4499712 7 5 262 2120 22 _ _ (76593 / 5000) (1531863 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4499712 :
    ThetaLowerSegment 4499712 4503808 (449687764249 / 100000) (450107518823 / 100000) := by
  exact
    thetaTile4096 4499712 4503808 7 5 274 2121 22 _ _ (1531951 / 100000) (765977 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4503808 :
    ThetaLowerSegment 4503808 4507904 (450107518823 / 100000) (450521170163 / 100000) := by
  exact
    thetaTile4096 4503808 4507904 7 5 270 2122 22 _ _ (766021 / 50000) (306409 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4507904 :
    ThetaLowerSegment 4507904 4512000 (450521170163 / 100000) (112727199953 / 25000) := by
  exact
    thetaTile4096 4507904 4512000 7 5 253 2123 22 _ _ (1532133 / 100000) (191517 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4512000 :
    ThetaLowerSegment 4512000 4516096 (112727199953 / 25000) (112826028401 / 25000) := by
  exact
    thetaTile4096 4512000 4516096 7 5 258 2124 22 _ _ (47882 / 3125) (1532227 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4516096 :
    ThetaLowerSegment 4516096 4520192 (112826028401 / 25000) (112930225753 / 25000) := by
  exact
    thetaTile4096 4516096 4520192 7 5 272 2125 22 _ _ (766157 / 50000) (1532317 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4520192 :
    ThetaLowerSegment 4520192 4524288 (112930225753 / 25000) (452108601477 / 100000) := by
  exact
    thetaTile4096 4520192 4524288 7 5 253 2126 22 _ _ (306481 / 20000) (191551 / 12500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4524288 :
    ThetaLowerSegment 4524288 4528384 (452108601477 / 100000) (452520842901 / 100000) := by
  exact
    thetaTile4096 4524288 4528384 7 5 269 2127 22 _ _ (95781 / 6250) (1532499 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4528384 :
    ThetaLowerSegment 4528384 4532480 (452520842901 / 100000) (452923913019 / 100000) := by
  exact
    thetaTile4096 4528384 4532480 7 5 263 2128 22 _ _ (766293 / 50000) (1532589 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4532480 :
    ThetaLowerSegment 4532480 4536576 (452923913019 / 100000) (453320876103 / 100000) := by
  exact
    thetaTile4096 4532480 4536576 7 5 259 2128 22 _ _ (383169 / 25000) (1532679 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4536576 :
    ThetaLowerSegment 4536576 4540672 (453320876103 / 100000) (226863529679 / 50000) := by
  exact
    thetaTile4096 4536576 4540672 7 5 265 2129 22 _ _ (1532767 / 100000) (153277 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4540672 :
    ThetaLowerSegment 4540672 4544768 (226863529679 / 50000) (11353369983 / 2500) := by
  exact
    thetaTile4096 4540672 4544768 7 5 266 2130 22 _ _ (1532857 / 100000) (76643 / 5000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4544768 :
    ThetaLowerSegment 4544768 4548864 (11353369983 / 2500) (454544096169 / 100000) := by
  exact
    thetaTile4096 4544768 4548864 7 5 267 2131 22 _ _ (1532947 / 100000) (30659 / 2000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4548864 :
    ThetaLowerSegment 4548864 4552960 (454544096169 / 100000) (454951884011 / 100000) := by
  exact
    thetaTile4096 4548864 4552960 7 5 266 2132 22 _ _ (1533037 / 100000) (19163 / 1250) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4552960 :
    ThetaLowerSegment 4552960 4557056 (454951884011 / 100000) (455387292079 / 100000) := by
  exact
    thetaTile4096 4552960 4557056 7 5 284 2133 22 _ _ (1533127 / 100000) (153313 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4557056 :
    ThetaLowerSegment 4557056 4561152 (455387292079 / 100000) (455761397027 / 100000) := by
  exact
    thetaTile4096 4557056 4561152 7 5 244 2134 22 _ _ (1533217 / 100000) (76661 / 5000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4561152 :
    ThetaLowerSegment 4561152 4565248 (455761397027 / 100000) (456206056057 / 100000) := by
  exact
    thetaTile4096 4561152 4565248 7 5 290 2135 22 _ _ (1533307 / 100000) (153331 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4565248 :
    ThetaLowerSegment 4565248 4569344 (456206056057 / 100000) (57078467529 / 12500) := by
  exact
    thetaTile4096 4565248 4569344 7 5 275 2136 22 _ _ (1533397 / 100000) (7667 / 500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4569344 :
    ThetaLowerSegment 4569344 4573440 (57078467529 / 12500) (457000377573 / 100000) := by
  exact
    thetaTile4096 4569344 4573440 7 5 243 2137 22 _ _ (1533487 / 100000) (153349 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4573440 :
    ThetaLowerSegment 4573440 4577536 (457000377573 / 100000) (146376057 / 32) := by
  exact
    thetaTile4096 4573440 4577536 7 5 277 2138 22 _ _ (191697 / 12500) (1533579 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4577536 :
    ThetaLowerSegment 4577536 4581632 (146376057 / 32) (457842335277 / 100000) := by
  exact
    thetaTile4096 4577536 4581632 7 5 272 2139 22 _ _ (766833 / 50000) (1533669 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4581632 :
    ThetaLowerSegment 4581632 4585728 (457842335277 / 100000) (458253381617 / 100000) := by
  exact
    thetaTile4096 4581632 4585728 7 5 268 2140 22 _ _ (306751 / 20000) (766879 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4585728 :
    ThetaLowerSegment 4585728 4589824 (458253381617 / 100000) (458652181057 / 100000) := by
  exact
    thetaTile4096 4585728 4589824 7 5 260 2141 22 _ _ (383461 / 25000) (1533847 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4589824 :
    ThetaLowerSegment 4589824 4593920 (458652181057 / 100000) (459074012907 / 100000) := by
  exact
    thetaTile4096 4589824 4593920 7 5 275 2142 22 _ _ (766967 / 50000) (1533937 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4593920 :
    ThetaLowerSegment 4593920 4598016 (459074012907 / 100000) (459488199117 / 100000) := by
  exact
    thetaTile4096 4593920 4598016 7 5 270 2143 22 _ _ (1534023 / 100000) (767013 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4598016 :
    ThetaLowerSegment 4598016 4602112 (459488199117 / 100000) (459876329453 / 100000) := by
  exact
    thetaTile4096 4598016 4602112 7 5 253 2144 22 _ _ (47941 / 3125) (306823 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4602112 :
    ThetaLowerSegment 4602112 4606208 (459876329453 / 100000) (460287495321 / 100000) := by
  exact
    thetaTile4096 4602112 4606208 7 5 268 2145 22 _ _ (1534201 / 100000) (383551 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4606208 :
    ThetaLowerSegment 4606208 4610304 (460287495321 / 100000) (460714027941 / 100000) := by
  exact
    thetaTile4096 4606208 4610304 7 5 278 2146 22 _ _ (153429 / 10000) (1534293 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4610304 :
    ThetaLowerSegment 4610304 4614400 (460714027941 / 100000) (461131379029 / 100000) := by
  exact
    thetaTile4096 4610304 4614400 7 5 272 2147 22 _ _ (1534379 / 100000) (767191 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4614400 :
    ThetaLowerSegment 4614400 4618496 (461131379029 / 100000) (461534944113 / 100000) := by
  exact
    thetaTile4096 4614400 4618496 7 5 263 2148 22 _ _ (383617 / 25000) (1534471 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4618496 :
    ThetaLowerSegment 4618496 4622592 (461534944113 / 100000) (461933928673 / 100000) := by
  exact
    thetaTile4096 4618496 4622592 7 5 260 2149 22 _ _ (383639 / 25000) (1534559 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4622592 :
    ThetaLowerSegment 4622592 4626688 (461933928673 / 100000) (462366698563 / 100000) := by
  exact
    thetaTile4096 4622592 4626688 7 5 282 2150 22 _ _ (306929 / 20000) (191831 / 12500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4626688 :
    ThetaLowerSegment 4626688 4630784 (462366698563 / 100000) (462767264137 / 100000) := by
  exact
    thetaTile4096 4626688 4630784 7 5 261 2150 22 _ _ (767367 / 50000) (1534737 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4630784 :
    ThetaLowerSegment 4630784 4634880 (462767264137 / 100000) (463161713391 / 100000) := by
  exact
    thetaTile4096 4630784 4634880 7 5 257 2151 22 _ _ (767411 / 50000) (61393 / 4000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4634880 :
    ThetaLowerSegment 4634880 4638976 (463161713391 / 100000) (9271492089 / 2000) := by
  exact
    thetaTile4096 4634880 4638976 7 5 269 2152 22 _ _ (1534911 / 100000) (767457 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4638976 :
    ThetaLowerSegment 4638976 4643072 (9271492089 / 2000) (463978309187 / 100000) := by
  exact
    thetaTile4096 4638976 4643072 7 5 263 2153 22 _ _ (1534999 / 100000) (767501 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4643072 :
    ThetaLowerSegment 4643072 4647168 (463978309187 / 100000) (58048522177 / 12500) := by
  exact
    thetaTile4096 4643072 4647168 7 5 267 2154 22 _ _ (1535087 / 100000) (153509 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4647168 :
    ThetaLowerSegment 4647168 4651264 (58048522177 / 12500) (464801139491 / 100000) := by
  exact
    thetaTile4096 4647168 4651264 7 5 269 2155 22 _ _ (61407 / 4000) (767589 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4651264 :
    ThetaLowerSegment 4651264 4655360 (464801139491 / 100000) (232591709989 / 50000) := by
  exact
    thetaTile4096 4651264 4655360 7 5 249 2156 22 _ _ (1535263 / 100000) (767633 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4655360 :
    ThetaLowerSegment 4655360 4659456 (232591709989 / 50000) (465574934483 / 100000) := by
  exact
    thetaTile4096 4655360 4659456 7 5 255 2157 22 _ _ (1535351 / 100000) (767677 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4659456 :
    ThetaLowerSegment 4659456 4663552 (465574934483 / 100000) (116497759613 / 25000) := by
  exact
    thetaTile4096 4659456 4663552 7 5 271 2158 22 _ _ (1535439 / 100000) (767721 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4663552 :
    ThetaLowerSegment 4663552 4667648 (116497759613 / 25000) (233199744317 / 50000) := by
  exact
    thetaTile4096 4663552 4667648 7 5 266 2159 22 _ _ (1535527 / 100000) (153553 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4667648 :
    ThetaLowerSegment 4667648 4671744 (233199744317 / 50000) (58352530893 / 12500) := by
  exact
    thetaTile4096 4667648 4671744 7 5 274 2160 22 _ _ (307123 / 20000) (767809 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4671744 :
    ThetaLowerSegment 4671744 4675840 (58352530893 / 12500) (747593019 / 160) := by
  exact
    thetaTile4096 4671744 4675840 7 5 277 2161 22 _ _ (1535703 / 100000) (767853 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4675840 :
    ThetaLowerSegment 4675840 4679936 (747593019 / 160) (3741343833 / 800) := by
  exact
    thetaTile4096 4675840 4679936 7 5 275 2162 22 _ _ (153579 / 10000) (1535793 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4679936 :
    ThetaLowerSegment 4679936 4684032 (3741343833 / 800) (18723613823 / 4000) := by
  exact
    thetaTile4096 4679936 4684032 7 5 275 2163 22 _ _ (767939 / 50000) (1535881 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4684032 :
    ThetaLowerSegment 4684032 4688128 (18723613823 / 4000) (93703468769 / 20000) := by
  exact
    thetaTile4096 4684032 4688128 7 5 278 2164 22 _ _ (307193 / 20000) (47999 / 3125) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4688128 :
    ThetaLowerSegment 4688128 4692224 (93703468769 / 20000) (234449910521 / 50000) := by
  exact
    thetaTile4096 4688128 4692224 7 5 249 2165 22 _ _ (1536053 / 100000) (192007 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4692224 :
    ThetaLowerSegment 4692224 4696320 (234449910521 / 50000) (234663433981 / 50000) := by
  exact
    thetaTile4096 4692224 4696320 7 5 278 2166 22 _ _ (76807 / 5000) (1536143 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4696320 :
    ThetaLowerSegment 4696320 4700416 (234663433981 / 50000) (469737040571 / 100000) := by
  exact
    thetaTile4096 4696320 4700416 7 5 267 2167 22 _ _ (1536227 / 100000) (153623 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4700416 :
    ThetaLowerSegment 4700416 4704512 (469737040571 / 100000) (235078227283 / 50000) := by
  exact
    thetaTile4096 4700416 4704512 7 5 273 2168 22 _ _ (307263 / 20000) (768159 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4704512 :
    ThetaLowerSegment 4704512 4708608 (235078227283 / 50000) (235273350337 / 50000) := by
  exact
    thetaTile4096 4704512 4708608 7 5 254 2168 22 _ _ (768201 / 50000) (307281 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4708608 :
    ThetaLowerSegment 4708608 4712704 (235273350337 / 50000) (470950797281 / 100000) := by
  exact
    thetaTile4096 4708608 4712704 7 5 263 2169 22 _ _ (1536489 / 100000) (384123 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4712704 :
    ThetaLowerSegment 4712704 4716800 (470950797281 / 100000) (94271290669 / 20000) := by
  exact
    thetaTile4096 4712704 4716800 7 5 264 2170 22 _ _ (48018 / 3125) (1536579 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4716800 :
    ThetaLowerSegment 4716800 4720896 (94271290669 / 20000) (235892591161 / 50000) := by
  exact
    thetaTile4096 4716800 4720896 7 5 279 2171 22 _ _ (1536663 / 100000) (768333 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4720896 :
    ThetaLowerSegment 4720896 4724992 (235892591161 / 50000) (236089295033 / 50000) := by
  exact
    thetaTile4096 4720896 4724992 7 5 256 2172 22 _ _ (1536749 / 100000) (96047 / 6250) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4724992 :
    ThetaLowerSegment 4724992 4729088 (236089295033 / 50000) (236292925803 / 50000) := by
  exact
    thetaTile4096 4724992 4729088 7 5 265 2173 22 _ _ (384209 / 25000) (1536839 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4729088 :
    ThetaLowerSegment 4729088 4733184 (236292925803 / 50000) (473008505431 / 100000) := by
  exact
    thetaTile4096 4729088 4733184 7 5 275 2174 22 _ _ (1536923 / 100000) (768463 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4733184 :
    ThetaLowerSegment 4733184 4737280 (473008505431 / 100000) (2959002531 / 625) := by
  exact
    thetaTile4096 4733184 4737280 7 5 281 2175 22 _ _ (1537009 / 100000) (384253 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4737280 :
    ThetaLowerSegment 4737280 4741376 (2959002531 / 625) (59229429829 / 12500) := by
  exact
    thetaTile4096 4737280 4741376 7 5 257 2176 22 _ _ (192137 / 12500) (1537099 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4741376 :
    ThetaLowerSegment 4741376 4745472 (59229429829 / 12500) (11856031367 / 2500) := by
  exact
    thetaTile4096 4741376 4745472 7 5 264 2177 22 _ _ (768591 / 50000) (307437 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4745472 :
    ThetaLowerSegment 4745472 4749568 (11856031367 / 2500) (474645556427 / 100000) := by
  exact
    thetaTile4096 4745472 4749568 7 5 263 2178 22 _ _ (1537269 / 100000) (192159 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4749568 :
    ThetaLowerSegment 4749568 4753664 (474645556427 / 100000) (237514178911 / 50000) := by
  exact
    thetaTile4096 4749568 4753664 7 5 249 2179 22 _ _ (307471 / 20000) (768679 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4753664 :
    ThetaLowerSegment 4753664 4757760 (237514178911 / 50000) (29715601041 / 6250) := by
  exact
    thetaTile4096 4753664 4757760 7 5 274 2180 22 _ _ (1537441 / 100000) (384361 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4757760 :
    ThetaLowerSegment 4757760 4761856 (29715601041 / 6250) (237935449527 / 50000) := by
  exact
    thetaTile4096 4757760 4761856 7 5 274 2181 22 _ _ (1537527 / 100000) (153753 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4761856 :
    ThetaLowerSegment 4761856 4765952 (237935449527 / 50000) (238141489669 / 50000) := by
  exact
    thetaTile4096 4761856 4765952 7 5 268 2182 22 _ _ (1537613 / 100000) (96101 / 6250) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4765952 :
    ThetaLowerSegment 4765952 4770048 (238141489669 / 50000) (476690469573 / 100000) := by
  exact
    thetaTile4096 4765952 4770048 7 5 265 2183 22 _ _ (1537699 / 100000) (768851 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4770048 :
    ThetaLowerSegment 4770048 4774144 (476690469573 / 100000) (477059537973 / 100000) := by
  exact
    thetaTile4096 4770048 4774144 7 5 240 2184 22 _ _ (307557 / 20000) (384447 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4774144 :
    ThetaLowerSegment 4774144 4778240 (477059537973 / 100000) (5968569103 / 1250) := by
  exact
    thetaTile4096 4774144 4778240 7 5 277 2184 22 _ _ (1537871 / 100000) (768937 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4778240 :
    ThetaLowerSegment 4778240 4782336 (5968569103 / 1250) (119474425179 / 25000) := by
  exact
    thetaTile4096 4778240 4782336 7 5 268 2185 22 _ _ (1537957 / 100000) (38449 / 2500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4782336 :
    ThetaLowerSegment 4782336 4786432 (119474425179 / 25000) (239148026797 / 50000) := by
  exact
    thetaTile4096 4782336 4786432 7 5 259 2186 22 _ _ (769021 / 50000) (307609 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4786432 :
    ThetaLowerSegment 4786432 4790528 (239148026797 / 50000) (239352597821 / 50000) := by
  exact
    thetaTile4096 4786432 4790528 7 5 266 2187 22 _ _ (96133 / 6250) (1538131 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4790528 :
    ThetaLowerSegment 4790528 4794624 (239352597821 / 50000) (47909282557 / 10000) := by
  exact
    thetaTile4096 4790528 4794624 7 5 252 2188 22 _ _ (769107 / 50000) (1538217 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4794624 :
    ThetaLowerSegment 4794624 4798720 (47909282557 / 10000) (479506628001 / 100000) := by
  exact
    thetaTile4096 4794624 4798720 7 5 269 2189 22 _ _ (1538299 / 100000) (769151 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4798720 :
    ThetaLowerSegment 4798720 4802816 (479506628001 / 100000) (479928145217 / 100000) := by
  exact
    thetaTile4096 4798720 4802816 7 5 274 2190 22 _ _ (96149 / 6250) (1538387 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4802816 :
    ThetaLowerSegment 4802816 4806912 (479928145217 / 100000) (480360455287 / 100000) := by
  exact
    thetaTile4096 4802816 4806912 7 5 281 2191 22 _ _ (153847 / 10000) (1538473 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4806912 :
    ThetaLowerSegment 4806912 4811008 (480360455287 / 100000) (240374854851 / 50000) := by
  exact
    thetaTile4096 4806912 4811008 7 5 253 2192 22 _ _ (307711 / 20000) (769279 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4811008 :
    ThetaLowerSegment 4811008 4815104 (240374854851 / 50000) (240577186011 / 50000) := by
  exact
    thetaTile4096 4811008 4815104 7 5 263 2193 22 _ _ (19233 / 1250) (1538643 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4815104 :
    ThetaLowerSegment 4815104 4819200 (240577186011 / 50000) (481577521397 / 100000) := by
  exact
    thetaTile4096 4815104 4819200 7 5 275 2194 22 _ _ (61549 / 4000) (192341 / 12500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4819200 :
    ThetaLowerSegment 4819200 4823296 (481577521397 / 100000) (481991461287 / 100000) := by
  exact
    thetaTile4096 4819200 4823296 7 5 269 2195 22 _ _ (153881 / 10000) (1538813 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4823296 :
    ThetaLowerSegment 4823296 4827392 (481991461287 / 100000) (482363873877 / 100000) := by
  exact
    thetaTile4096 4823296 4827392 7 5 242 2196 22 _ _ (307779 / 20000) (769449 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4827392 :
    ThetaLowerSegment 4827392 4831488 (482363873877 / 100000) (482762469697 / 100000) := by
  exact
    thetaTile4096 4827392 4831488 7 5 259 2197 22 _ _ (76949 / 5000) (1538983 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4831488 :
    ThetaLowerSegment 4831488 4835584 (482762469697 / 100000) (120799506273 / 25000) := by
  exact
    thetaTile4096 4831488 4835584 7 5 283 2198 22 _ _ (307813 / 20000) (384767 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4835584 :
    ThetaLowerSegment 4835584 4839680 (120799506273 / 25000) (60454777749 / 12500) := by
  exact
    thetaTile4096 4835584 4839680 7 5 286 2198 22 _ _ (30783 / 2000) (1539153 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4839680 :
    ThetaLowerSegment 4839680 4843776 (60454777749 / 12500) (60504033237 / 12500) := by
  exact
    thetaTile4096 4839680 4843776 7 5 256 2199 22 _ _ (769617 / 50000) (1539237 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4843776 :
    ThetaLowerSegment 4843776 4847872 (60504033237 / 12500) (96886805631 / 20000) := by
  exact
    thetaTile4096 4843776 4847872 7 5 261 2200 22 _ _ (1539319 / 100000) (769661 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4847872 :
    ThetaLowerSegment 4847872 4851968 (96886805631 / 20000) (96971472851 / 20000) := by
  exact
    thetaTile4096 4847872 4851968 7 5 275 2201 22 _ _ (384851 / 25000) (1539407 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4851968 :
    ThetaLowerSegment 4851968 4856064 (96971472851 / 20000) (97051526227 / 20000) := by
  exact
    thetaTile4096 4851968 4856064 7 5 260 2202 22 _ _ (48109 / 3125) (1539491 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4856064 :
    ThetaLowerSegment 4856064 4860160 (97051526227 / 20000) (485664078143 / 100000) := by
  exact
    thetaTile4096 4856064 4860160 7 5 264 2203 22 _ _ (384893 / 25000) (61583 / 4000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4860160 :
    ThetaLowerSegment 4860160 4864256 (485664078143 / 100000) (60760550563 / 12500) := by
  exact
    thetaTile4096 4860160 4864256 7 5 273 2204 22 _ _ (1539657 / 100000) (76983 / 5000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4864256 :
    ThetaLowerSegment 4864256 4868352 (60760550563 / 12500) (486504753797 / 100000) := by
  exact
    thetaTile4096 4864256 4868352 7 5 273 2205 22 _ _ (1539741 / 100000) (48117 / 3125) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4868352 :
    ThetaLowerSegment 4868352 4872448 (486504753797 / 100000) (486920506547 / 100000) := by
  exact
    thetaTile4096 4868352 4872448 7 5 270 2206 22 _ _ (61593 / 4000) (384957 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4872448 :
    ThetaLowerSegment 4872448 4876544 (486920506547 / 100000) (30456496493 / 6250) := by
  exact
    thetaTile4096 4872448 4876544 7 5 249 2207 22 _ _ (1539909 / 100000) (192489 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4876544 :
    ThetaLowerSegment 4876544 4880640 (30456496493 / 6250) (487721281991 / 100000) := by
  exact
    thetaTile4096 4876544 4880640 7 5 271 2208 22 _ _ (1539993 / 100000) (384999 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4880640 :
    ThetaLowerSegment 4880640 4884736 (487721281991 / 100000) (244069321429 / 50000) := by
  exact
    thetaTile4096 4880640 4884736 7 5 271 2209 22 _ _ (1540077 / 100000) (19251 / 1250) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4884736 :
    ThetaLowerSegment 4884736 4888832 (244069321429 / 50000) (488559106811 / 100000) := by
  exact
    thetaTile4096 4884736 4888832 7 5 273 2210 22 _ _ (1540161 / 100000) (385041 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4888832 :
    ThetaLowerSegment 4888832 4892928 (488559106811 / 100000) (122246438669 / 25000) := by
  exact
    thetaTile4096 4888832 4892928 7 5 277 2211 22 _ _ (308049 / 20000) (192531 / 12500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4892928 :
    ThetaLowerSegment 4892928 4897024 (122246438669 / 25000) (30588950507 / 6250) := by
  exact
    thetaTile4096 4892928 4897024 7 5 284 2211 22 _ _ (1540329 / 100000) (385083 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4897024 :
    ThetaLowerSegment 4897024 4905216 (30588950507 / 6250) (122561061927 / 25000) := by
  exact
    thetaTile4096 4897024 4905216 7 6 533 2212 22 _ _ (385103 / 25000) (308083 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4905216 :
    ThetaLowerSegment 4905216 4913408 (122561061927 / 25000) (491059213999 / 100000) := by
  exact
    thetaTile4096 4905216 4913408 7 6 529 2214 22 _ _ (1540579 / 100000) (770291 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4913408 :
    ThetaLowerSegment 4913408 4921600 (491059213999 / 100000) (491881972363 / 100000) := by
  exact
    thetaTile4096 4913408 4921600 7 6 534 2216 22 _ _ (770373 / 50000) (1540749 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4921600 :
    ThetaLowerSegment 4921600 4929792 (491881972363 / 100000) (246347016757 / 50000) := by
  exact
    thetaTile4096 4921600 4929792 7 6 527 2218 22 _ _ (1540913 / 100000) (385229 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4929792 :
    ThetaLowerSegment 4929792 4937984 (246347016757 / 50000) (98701852861 / 20000) := by
  exact
    thetaTile4096 4929792 4937984 7 6 529 2220 22 _ _ (1541079 / 100000) (770541 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4937984 :
    ThetaLowerSegment 4937984 4946176 (98701852861 / 20000) (98870773313 / 20000) := by
  exact
    thetaTile4096 4937984 4946176 7 6 548 2222 22 _ _ (308249 / 20000) (48164 / 3125) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4946176 :
    ThetaLowerSegment 4946176 4954368 (98870773313 / 20000) (247586177903 / 50000) := by
  exact
    thetaTile4096 4946176 4954368 7 6 531 2224 22 _ _ (1541411 / 100000) (770707 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4954368 :
    ThetaLowerSegment 4954368 4962560 (247586177903 / 50000) (49599247477 / 10000) := by
  exact
    thetaTile4096 4954368 4962560 7 6 532 2225 22 _ _ (1541577 / 100000) (77079 / 5000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4962560 :
    ThetaLowerSegment 4962560 4970752 (49599247477 / 10000) (62103319649 / 12500) := by
  exact
    thetaTile4096 4962560 4970752 7 6 541 2227 22 _ _ (770871 / 50000) (308349 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4970752 :
    ThetaLowerSegment 4970752 4978944 (62103319649 / 12500) (2488326773 / 500) := by
  exact
    thetaTile4096 4970752 4978944 7 6 544 2229 22 _ _ (1541907 / 100000) (154191 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4978944 :
    ThetaLowerSegment 4978944 4987136 (2488326773 / 500) (24924903647 / 5000) := by
  exact
    thetaTile4096 4978944 4987136 7 6 540 2231 22 _ _ (1542071 / 100000) (771037 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4987136 :
    ThetaLowerSegment 4987136 4995328 (24924903647 / 5000) (124830406741 / 25000) := by
  exact
    thetaTile4096 4987136 4995328 7 6 534 2233 22 _ _ (385559 / 25000) (1542239 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell4995328 :
    ThetaLowerSegment 4995328 5003520 (124830406741 / 25000) (125029376341 / 25000) := by
  exact
    thetaTile4096 4995328 5003520 7 6 516 2235 22 _ _ (1928 / 125) (1542403 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5003520 :
    ThetaLowerSegment 5003520 5011712 (125029376341 / 25000) (62615918933 / 12500) := by
  exact
    thetaTile4096 5003520 5011712 7 6 525 2236 22 _ _ (385641 / 25000) (1542567 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5011712 :
    ThetaLowerSegment 5011712 5019904 (62615918933 / 12500) (250869412933 / 50000) := by
  exact
    thetaTile4096 5011712 5019904 7 6 526 2238 22 _ _ (1542727 / 100000) (154273 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5019904 :
    ThetaLowerSegment 5019904 5028096 (250869412933 / 50000) (502576615679 / 100000) := by
  exact
    thetaTile4096 5019904 5028096 7 6 543 2240 22 _ _ (1542891 / 100000) (771447 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5028096 :
    ThetaLowerSegment 5028096 5036288 (502576615679 / 100000) (503383632921 / 100000) := by
  exact
    thetaTile4096 5028096 5036288 7 6 523 2242 22 _ _ (771527 / 50000) (1543057 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5036288 :
    ThetaLowerSegment 5036288 5044480 (503383632921 / 100000) (504195364537 / 100000) := by
  exact
    thetaTile4096 5036288 5044480 7 6 526 2244 22 _ _ (96451 / 6250) (1543219 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5044480 :
    ThetaLowerSegment 5044480 5052672 (504195364537 / 100000) (252498189119 / 50000) := by
  exact
    thetaTile4096 5044480 5052672 7 6 519 2245 22 _ _ (1543379 / 100000) (771691 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5052672 :
    ThetaLowerSegment 5052672 5060864 (252498189119 / 50000) (505843782247 / 100000) := by
  exact
    thetaTile4096 5052672 5060864 7 6 549 2247 22 _ _ (1543541 / 100000) (192943 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5060864 :
    ThetaLowerSegment 5060864 5069056 (505843782247 / 100000) (101328066599 / 20000) := by
  exact
    thetaTile4096 5060864 5069056 7 6 516 2249 22 _ _ (1543703 / 100000) (771853 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5069056 :
    ThetaLowerSegment 5069056 5077248 (101328066599 / 20000) (6343290163 / 1250) := by
  exact
    thetaTile4096 5069056 5077248 7 6 533 2251 22 _ _ (308773 / 20000) (385967 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5077248 :
    ThetaLowerSegment 5077248 5085440 (6343290163 / 1250) (127073474757 / 25000) := by
  exact
    thetaTile4096 5077248 5085440 7 6 538 2253 22 _ _ (772013 / 50000) (1544029 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5085440 :
    ThetaLowerSegment 5085440 5093632 (127073474757 / 25000) (15909904726 / 3125) := by
  exact
    thetaTile4096 5085440 5093632 7 6 533 2255 22 _ _ (386047 / 25000) (1544191 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5093632 :
    ThetaLowerSegment 5093632 5101824 (15909904726 / 3125) (509943177947 / 100000) := by
  exact
    thetaTile4096 5093632 5101824 7 6 535 2256 22 _ _ (1544349 / 100000) (48261 / 3125) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5101824 :
    ThetaLowerSegment 5101824 5110016 (509943177947 / 100000) (31920197187 / 6250) := by
  exact
    thetaTile4096 5101824 5110016 7 6 505 2258 22 _ _ (1544509 / 100000) (48266 / 3125) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5110016 :
    ThetaLowerSegment 5110016 5118208 (31920197187 / 6250) (255770142711 / 50000) := by
  exact
    thetaTile4096 5110016 5118208 7 6 529 2260 22 _ _ (154467 / 10000) (1544673 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5118208 :
    ThetaLowerSegment 5118208 5126400 (255770142711 / 50000) (128095554443 / 25000) := by
  exact
    thetaTile4096 5118208 5126400 7 6 545 2262 22 _ _ (154483 / 10000) (1544833 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5126400 :
    ThetaLowerSegment 5126400 5134592 (128095554443 / 25000) (64150132809 / 12500) := by
  exact
    thetaTile4096 5126400 5134592 7 6 530 2264 22 _ _ (154499 / 10000) (1544993 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5134592 :
    ThetaLowerSegment 5134592 5142784 (64150132809 / 12500) (257010768561 / 50000) := by
  exact
    thetaTile4096 5134592 5142784 7 6 531 2265 22 _ _ (30903 / 2000) (1545153 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5142784 :
    ThetaLowerSegment 5142784 5150976 (257010768561 / 50000) (514823552493 / 100000) := by
  exact
    thetaTile4096 5142784 5150976 7 6 519 2267 22 _ _ (1545309 / 100000) (48291 / 3125) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5150976 :
    ThetaLowerSegment 5150976 5159168 (514823552493 / 100000) (515644196001 / 100000) := by
  exact
    thetaTile4096 5150976 5159168 7 6 531 2269 22 _ _ (386367 / 25000) (1545471 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5159168 :
    ThetaLowerSegment 5159168 5167360 (515644196001 / 100000) (258226279461 / 50000) := by
  exact
    thetaTile4096 5159168 5167360 7 6 523 2271 22 _ _ (1545627 / 100000) (154563 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5167360 :
    ThetaLowerSegment 5167360 5175552 (258226279461 / 50000) (51728419179 / 10000) := by
  exact
    thetaTile4096 5167360 5175552 7 6 538 2273 22 _ _ (772893 / 50000) (1545789 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5175552 :
    ThetaLowerSegment 5175552 5183744 (51728419179 / 10000) (259033992699 / 50000) := by
  exact
    thetaTile4096 5175552 5183744 7 6 507 2274 22 _ _ (193243 / 12500) (1545947 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5183744 :
    ThetaLowerSegment 5183744 5191936 (259033992699 / 50000) (259443709729 / 50000) := by
  exact
    thetaTile4096 5183744 5191936 7 6 530 2276 22 _ _ (773051 / 50000) (309221 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5191936 :
    ThetaLowerSegment 5191936 5200128 (259443709729 / 50000) (259853468629 / 50000) := by
  exact
    thetaTile4096 5191936 5200128 7 6 530 2278 22 _ _ (77313 / 5000) (1546263 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5200128 :
    ThetaLowerSegment 5200128 5208320 (259853468629 / 50000) (26027796037 / 5000) := by
  exact
    thetaTile4096 5200128 5208320 7 6 549 2280 22 _ _ (773209 / 50000) (1546421 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5208320 :
    ThetaLowerSegment 5208320 5216512 (26027796037 / 5000) (52137560549 / 10000) := by
  exact
    thetaTile4096 5208320 5216512 7 6 530 2282 22 _ _ (61863 / 4000) (773289 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5216512 :
    ThetaLowerSegment 5216512 5224704 (52137560549 / 10000) (52218763979 / 10000) := by
  exact
    thetaTile4096 5216512 5224704 7 6 525 2283 22 _ _ (386683 / 25000) (309347 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5224704 :
    ThetaLowerSegment 5224704 5232896 (52218763979 / 10000) (6537593637 / 1250) := by
  exact
    thetaTile4096 5224704 5232896 7 6 530 2285 22 _ _ (1546889 / 100000) (386723 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5232896 :
    ThetaLowerSegment 5232896 5241088 (6537593637 / 1250) (16369897113 / 3125) := by
  exact
    thetaTile4096 5232896 5241088 7 6 536 2287 22 _ _ (773523 / 50000) (1547049 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5241088 :
    ThetaLowerSegment 5241088 5249280 (16369897113 / 3125) (262336871949 / 50000) := by
  exact
    thetaTile4096 5241088 5249280 7 6 541 2289 22 _ _ (773601 / 50000) (309441 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5249280 :
    ThetaLowerSegment 5249280 5257472 (262336871949 / 50000) (65686730521 / 12500) := by
  exact
    thetaTile4096 5249280 5257472 7 6 530 2291 22 _ _ (1547359 / 100000) (773681 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5257472 :
    ThetaLowerSegment 5257472 5265664 (65686730521 / 12500) (263160108589 / 50000) := by
  exact
    thetaTile4096 5257472 5265664 7 6 534 2292 22 _ _ (309503 / 20000) (773759 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5265664 :
    ThetaLowerSegment 5265664 5273856 (263160108589 / 50000) (263576431819 / 50000) := by
  exact
    thetaTile4096 5265664 5273856 7 6 538 2294 22 _ _ (154767 / 10000) (1547673 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5273856 :
    ThetaLowerSegment 5273856 5282048 (263576431819 / 50000) (263974223101 / 50000) := by
  exact
    thetaTile4096 5273856 5282048 7 6 514 2296 22 _ _ (773913 / 50000) (1547829 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5282048 :
    ThetaLowerSegment 5282048 5290240 (263974223101 / 50000) (528761136227 / 100000) := by
  exact
    thetaTile4096 5282048 5290240 7 6 525 2298 22 _ _ (1547981 / 100000) (96749 / 6250) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5290240 :
    ThetaLowerSegment 5290240 5298432 (528761136227 / 100000) (529590937123 / 100000) := by
  exact
    thetaTile4096 5290240 5298432 7 6 536 2300 22 _ _ (193517 / 12500) (1548139 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5298432 :
    ThetaLowerSegment 5298432 5306624 (529590937123 / 100000) (132606366493 / 25000) := by
  exact
    thetaTile4096 5298432 5306624 7 6 539 2301 22 _ _ (1548291 / 100000) (774147 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5306624 :
    ThetaLowerSegment 5306624 5314816 (132606366493 / 25000) (531222915147 / 100000) := by
  exact
    thetaTile4096 5306624 5314816 7 6 515 2303 22 _ _ (309689 / 20000) (48389 / 3125) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5314816 :
    ThetaLowerSegment 5314816 5323008 (531222915147 / 100000) (266014867613 / 50000) := by
  exact
    thetaTile4096 5314816 5323008 7 6 521 2305 22 _ _ (1548599 / 100000) (774301 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5323008 :
    ThetaLowerSegment 5323008 5331200 (266014867613 / 50000) (532858318081 / 100000) := by
  exact
    thetaTile4096 5323008 5331200 7 6 535 2307 22 _ _ (1548753 / 100000) (387189 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5331200 :
    ThetaLowerSegment 5331200 5339392 (532858318081 / 100000) (266840393849 / 50000) := by
  exact
    thetaTile4096 5331200 5339392 7 6 531 2308 22 _ _ (1548907 / 100000) (154891 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5339392 :
    ThetaLowerSegment 5339392 5347584 (266840393849 / 50000) (534518829699 / 100000) := by
  exact
    thetaTile4096 5339392 5347584 7 6 541 2310 22 _ _ (1549061 / 100000) (193633 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5347584 :
    ThetaLowerSegment 5347584 5355776 (534518829699 / 100000) (107063025139 / 20000) := by
  exact
    thetaTile4096 5347584 5355776 7 6 514 2312 22 _ _ (774607 / 50000) (1549217 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5355776 :
    ThetaLowerSegment 5355776 5363968 (107063025139 / 20000) (268067370419 / 50000) := by
  exact
    thetaTile4096 5355776 5363968 7 6 529 2314 22 _ _ (1549367 / 100000) (154937 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5363968 :
    ThetaLowerSegment 5363968 5372160 (268067370419 / 50000) (268462498019 / 50000) := by
  exact
    thetaTile4096 5363968 5372160 7 6 510 2316 22 _ _ (19369 / 1250) (1549523 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5372160 :
    ThetaLowerSegment 5372160 5380352 (268462498019 / 50000) (268890207767 / 50000) := by
  exact
    thetaTile4096 5372160 5380352 7 6 552 2317 22 _ _ (1549673 / 100000) (387419 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5380352 :
    ThetaLowerSegment 5380352 5388544 (268890207767 / 50000) (538618870859 / 100000) := by
  exact
    thetaTile4096 5380352 5388544 7 6 541 2319 22 _ _ (61993 / 4000) (387457 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5388544 :
    ThetaLowerSegment 5388544 5396736 (538618870859 / 100000) (269711654461 / 50000) := by
  exact
    thetaTile4096 5388544 5396736 7 6 519 2321 22 _ _ (1549977 / 100000) (77499 / 5000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5396736 :
    ThetaLowerSegment 5396736 5404928 (269711654461 / 50000) (540221625357 / 100000) := by
  exact
    thetaTile4096 5396736 5404928 7 6 515 2323 22 _ _ (1550129 / 100000) (387533 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5404928 :
    ThetaLowerSegment 5404928 5413120 (540221625357 / 100000) (21641606949 / 4000) := by
  exact
    thetaTile4096 5404928 5413120 7 6 528 2324 22 _ _ (1550281 / 100000) (387571 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5413120 :
    ThetaLowerSegment 5413120 5421312 (21641606949 / 4000) (541852600093 / 100000) := by
  exact
    thetaTile4096 5413120 5421312 7 6 524 2326 22 _ _ (48451 / 3125) (310087 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5421312 :
    ThetaLowerSegment 5421312 5429504 (541852600093 / 100000) (542686813747 / 100000) := by
  exact
    thetaTile4096 5421312 5429504 7 6 538 2328 22 _ _ (1550583 / 100000) (775293 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5429504 :
    ThetaLowerSegment 5429504 5437696 (542686813747 / 100000) (543505601299 / 100000) := by
  exact
    thetaTile4096 5429504 5437696 7 6 528 2330 22 _ _ (775367 / 50000) (1550737 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5437696 :
    ThetaLowerSegment 5437696 5445888 (543505601299 / 100000) (136079953981 / 25000) := by
  exact
    thetaTile4096 5437696 5445888 7 6 525 2331 22 _ _ (310177 / 20000) (193861 / 12500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5445888 :
    ThetaLowerSegment 5445888 5454080 (136079953981 / 25000) (136289343841 / 25000) := by
  exact
    thetaTile4096 5445888 5454080 7 6 540 2333 22 _ _ (387759 / 25000) (1551039 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5454080 :
    ThetaLowerSegment 5454080 5462272 (136289343841 / 25000) (27299440553 / 5000) := by
  exact
    thetaTile4096 5454080 5462272 7 6 536 2335 22 _ _ (775593 / 50000) (1551189 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5462272 :
    ThetaLowerSegment 5462272 5470464 (27299440553 / 5000) (136697325109 / 25000) := by
  exact
    thetaTile4096 5462272 5470464 7 6 516 2337 22 _ _ (193917 / 12500) (1551339 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5470464 :
    ThetaLowerSegment 5470464 5478656 (136697325109 / 25000) (54759452167 / 10000) := by
  exact
    thetaTile4096 5470464 5478656 7 6 519 2338 22 _ _ (775743 / 50000) (1551489 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5478656 :
    ThetaLowerSegment 5478656 5486848 (54759452167 / 10000) (438733511 / 80) := by
  exact
    thetaTile4096 5478656 5486848 7 6 530 2340 22 _ _ (387909 / 25000) (1551639 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5486848 :
    ThetaLowerSegment 5486848 5495040 (438733511 / 80) (13730673013 / 2500) := by
  exact
    thetaTile4096 5486848 5495040 7 6 522 2342 22 _ _ (310357 / 20000) (387947 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5495040 :
    ThetaLowerSegment 5495040 5503232 (13730673013 / 2500) (275027050671 / 50000) := by
  exact
    thetaTile4096 5495040 5503232 7 6 533 2344 22 _ _ (775967 / 50000) (1551937 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5503232 :
    ThetaLowerSegment 5503232 5511424 (275027050671 / 50000) (550865840751 / 100000) := by
  exact
    thetaTile4096 5503232 5511424 7 6 523 2345 22 _ _ (1552083 / 100000) (776043 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5511424 :
    ThetaLowerSegment 5511424 5519616 (550865840751 / 100000) (551657479071 / 100000) := by
  exact
    thetaTile4096 5511424 5519616 7 6 510 2347 22 _ _ (194029 / 12500) (310447 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5519616 :
    ThetaLowerSegment 5519616 5527808 (551657479071 / 100000) (552460059531 / 100000) := by
  exact
    thetaTile4096 5519616 5527808 7 6 517 2349 22 _ _ (77619 / 5000) (1552383 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5527808 :
    ThetaLowerSegment 5527808 5536000 (552460059531 / 100000) (276654646447 / 50000) := by
  exact
    thetaTile4096 5527808 5536000 7 6 547 2351 22 _ _ (1552529 / 100000) (388133 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5536000 :
    ThetaLowerSegment 5536000 5544192 (276654646447 / 50000) (138525289541 / 25000) := by
  exact
    thetaTile4096 5536000 5544192 7 6 510 2352 22 _ _ (1552677 / 100000) (38817 / 2500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5544192 :
    ThetaLowerSegment 5544192 5552384 (138525289541 / 25000) (138727156791 / 25000) := by
  exact
    thetaTile4096 5544192 5552384 7 6 520 2354 22 _ _ (62113 / 4000) (388207 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5552384 :
    ThetaLowerSegment 5552384 5560576 (138727156791 / 25000) (138930596123 / 25000) := by
  exact
    thetaTile4096 5552384 5560576 7 6 524 2356 22 _ _ (388243 / 25000) (62119 / 4000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5560576 :
    ThetaLowerSegment 5560576 5568768 (138930596123 / 25000) (139136384523 / 25000) := by
  exact
    thetaTile4096 5560576 5568768 7 6 530 2358 22 _ _ (9707 / 625) (1553123 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5568768 :
    ThetaLowerSegment 5568768 5576960 (139136384523 / 25000) (557376535937 / 100000) := by
  exact
    thetaTile4096 5568768 5576960 7 6 535 2359 22 _ _ (1553267 / 100000) (155327 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5576960 :
    ThetaLowerSegment 5576960 5585152 (557376535937 / 100000) (558196738529 / 100000) := by
  exact
    thetaTile4096 5576960 5585152 7 6 528 2361 22 _ _ (776707 / 50000) (1553417 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5585152 :
    ThetaLowerSegment 5585152 5593344 (558196738529 / 100000) (139749205611 / 25000) := by
  exact
    thetaTile4096 5585152 5593344 7 6 515 2363 22 _ _ (1553561 / 100000) (388391 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5593344 :
    ThetaLowerSegment 5593344 5601536 (139749205611 / 25000) (22392997931 / 4000) := by
  exact
    thetaTile4096 5593344 5601536 7 6 533 2365 22 _ _ (1553707 / 100000) (155371 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5601536 :
    ThetaLowerSegment 5601536 5609728 (22392997931 / 4000) (560631398501 / 100000) := by
  exact
    thetaTile4096 5601536 5609728 7 6 519 2366 22 _ _ (776927 / 50000) (1553857 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5609728 :
    ThetaLowerSegment 5609728 5617920 (560631398501 / 100000) (561448802501 / 100000) := by
  exact
    thetaTile4096 5609728 5617920 7 6 526 2368 22 _ _ (777 / 50) (1554003 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5617920 :
    ThetaLowerSegment 5617920 5626112 (561448802501 / 100000) (562238308669 / 100000) := by
  exact
    thetaTile4096 5617920 5626112 7 6 508 2370 22 _ _ (777073 / 50000) (1554149 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5626112 :
    ThetaLowerSegment 5626112 5630208 (562238308669 / 100000) (562661075821 / 100000) := by
  exact
    thetaTile4096 5626112 5630208 7 5 272 2371 22 _ _ (1554291 / 100000) (777147 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5630208 :
    ThetaLowerSegment 5630208 5638400 (562661075821 / 100000) (112700397349 / 20000) := by
  exact
    thetaTile4096 5630208 5638400 7 6 541 2372 22 _ _ (388591 / 25000) (1554367 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5638400 :
    ThetaLowerSegment 5638400 5646592 (112700397349 / 20000) (112853982937 / 20000) := by
  exact
    thetaTile4096 5638400 5646592 7 6 494 2374 22 _ _ (155451 / 10000) (1554513 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5646592 :
    ThetaLowerSegment 5646592 5650688 (112853982937 / 20000) (22587462489 / 4000) := by
  exact
    thetaTile4096 5646592 5650688 7 5 268 2376 22 _ _ (310931 / 20000) (777329 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5650688 :
    ThetaLowerSegment 5650688 5654784 (22587462489 / 4000) (282547727713 / 50000) := by
  exact
    thetaTile4096 5650688 5654784 7 5 263 2377 22 _ _ (1554727 / 100000) (155473 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5654784 :
    ThetaLowerSegment 5654784 5658880 (282547727713 / 50000) (282745964713 / 50000) := by
  exact
    thetaTile4096 5654784 5658880 7 5 255 2377 22 _ _ (3887 / 250) (1554803 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5658880 :
    ThetaLowerSegment 5658880 5662976 (282745964713 / 50000) (56591485461 / 10000) := by
  exact
    thetaTile4096 5658880 5662976 7 5 272 2378 22 _ _ (194359 / 12500) (12439 / 800) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5662976 :
    ThetaLowerSegment 5662976 5667072 (56591485461 / 10000) (113262273117 / 20000) := by
  exact
    thetaTile4096 5662976 5667072 7 5 255 2379 22 _ _ (310989 / 20000) (388737 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5667072 :
    ThetaLowerSegment 5667072 5671168 (113262273117 / 20000) (283355502477 / 50000) := by
  exact
    thetaTile4096 5667072 5671168 7 5 257 2380 22 _ _ (1555017 / 100000) (77751 / 5000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5671168 :
    ThetaLowerSegment 5671168 5675264 (283355502477 / 50000) (17722451196 / 3125) := by
  exact
    thetaTile4096 5671168 5675264 7 5 262 2381 22 _ _ (1555089 / 100000) (388773 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5675264 :
    ThetaLowerSegment 5675264 5679360 (17722451196 / 3125) (113505489123 / 20000) := by
  exact
    thetaTile4096 5675264 5679360 7 5 263 2382 22 _ _ (1555161 / 100000) (388791 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5679360 :
    ThetaLowerSegment 5679360 5683456 (113505489123 / 20000) (567922474797 / 100000) := by
  exact
    thetaTile4096 5679360 5683456 7 5 254 2383 22 _ _ (1555233 / 100000) (388809 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5683456 :
    ThetaLowerSegment 5683456 5687552 (567922474797 / 100000) (568345518029 / 100000) := by
  exact
    thetaTile4096 5683456 5687552 7 5 272 2384 22 _ _ (777653 / 50000) (1555309 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5687552 :
    ThetaLowerSegment 5687552 5691648 (568345518029 / 100000) (113755271547 / 20000) := by
  exact
    thetaTile4096 5687552 5691648 7 5 277 2384 22 _ _ (777689 / 50000) (1555381 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5691648 :
    ThetaLowerSegment 5691648 5695744 (113755271547 / 20000) (113834288407 / 20000) := by
  exact
    thetaTile4096 5691648 5695744 7 5 254 2385 22 _ _ (31109 / 2000) (1555453 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5695744 :
    ThetaLowerSegment 5695744 5699840 (113834288407 / 20000) (569613209999 / 100000) := by
  exact
    thetaTile4096 5695744 5699840 7 5 284 2386 22 _ _ (1555521 / 100000) (388881 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5699840 :
    ThetaLowerSegment 5699840 5708032 (569613209999 / 100000) (570431451917 / 100000) := by
  exact
    thetaTile4096 5699840 5708032 7 6 526 2387 22 _ _ (1555593 / 100000) (388899 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5708032 :
    ThetaLowerSegment 5708032 5716224 (570431451917 / 100000) (22850488619 / 4000) := by
  exact
    thetaTile4096 5708032 5716224 7 6 534 2389 22 _ _ (1555737 / 100000) (77787 / 5000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5716224 :
    ThetaLowerSegment 5716224 5724416 (22850488619 / 4000) (22883784451 / 4000) := by
  exact
    thetaTile4096 5716224 5724416 7 6 535 2390 22 _ _ (38897 / 2500) (1555883 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5724416 :
    ThetaLowerSegment 5724416 5732608 (22883784451 / 4000) (572925528091 / 100000) := by
  exact
    thetaTile4096 5724416 5732608 7 6 534 2392 22 _ _ (194503 / 12500) (1556027 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5732608 :
    ThetaLowerSegment 5732608 5740800 (572925528091 / 100000) (14342862619 / 2500) := by
  exact
    thetaTile4096 5732608 5740800 7 6 507 2394 22 _ _ (1556167 / 100000) (155617 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5740800 :
    ThetaLowerSegment 5740800 5748992 (14342862619 / 2500) (71817029489 / 12500) := by
  exact
    thetaTile4096 5740800 5748992 7 6 528 2395 22 _ _ (1556309 / 100000) (194539 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5748992 :
    ThetaLowerSegment 5748992 5757184 (71817029489 / 12500) (71919755321 / 12500) := by
  exact
    thetaTile4096 5748992 5757184 7 6 528 2397 22 _ _ (389113 / 25000) (311291 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5757184 :
    ThetaLowerSegment 5757184 5765376 (71919755321 / 12500) (144039532971 / 25000) := by
  exact
    thetaTile4096 5757184 5765376 7 6 514 2399 22 _ _ (778297 / 50000) (1556597 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5765376 :
    ThetaLowerSegment 5765376 5773568 (144039532971 / 25000) (72121732759 / 12500) := by
  exact
    thetaTile4096 5765376 5773568 7 6 524 2401 22 _ _ (1556737 / 100000) (77837 / 5000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5773568 :
    ThetaLowerSegment 5773568 5777664 (72121732759 / 12500) (18042499002 / 3125) := by
  exact
    thetaTile4096 5773568 5777664 7 5 248 2402 22 _ _ (1556879 / 100000) (778441 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5777664 :
    ThetaLowerSegment 5777664 5781760 (18042499002 / 3125) (144440415291 / 25000) := by
  exact
    thetaTile4096 5777664 5781760 7 5 258 2403 22 _ _ (31139 / 2000) (1556953 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5781760 :
    ThetaLowerSegment 5781760 5785856 (144440415291 / 25000) (144541621591 / 25000) := by
  exact
    thetaTile4096 5781760 5785856 7 5 260 2404 22 _ _ (77851 / 5000) (1557023 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5785856 :
    ThetaLowerSegment 5785856 5789952 (144541621591 / 25000) (72321416253 / 12500) := by
  exact
    thetaTile4096 5785856 5789952 7 5 260 2405 22 _ _ (1557091 / 100000) (778547 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5789952 :
    ThetaLowerSegment 5789952 5794048 (72321416253 / 12500) (144746383779 / 25000) := by
  exact
    thetaTile4096 5789952 5794048 7 5 266 2406 22 _ _ (778581 / 50000) (311433 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5794048 :
    ThetaLowerSegment 5794048 5798144 (144746383779 / 25000) (579385743997 / 100000) := by
  exact
    thetaTile4096 5794048 5798144 7 5 257 2407 22 _ _ (1557233 / 100000) (389309 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5798144 :
    ThetaLowerSegment 5798144 5802240 (579385743997 / 100000) (144949607323 / 25000) := by
  exact
    thetaTile4096 5798144 5802240 7 5 265 2407 22 _ _ (1557303 / 100000) (778653 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5802240 :
    ThetaLowerSegment 5802240 5806336 (144949607323 / 25000) (36263682517 / 6250) := by
  exact
    thetaTile4096 5802240 5806336 7 5 270 2408 22 _ _ (778687 / 50000) (1557377 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5806336 :
    ThetaLowerSegment 5806336 5810432 (36263682517 / 6250) (580644102757 / 100000) := by
  exact
    thetaTile4096 5806336 5810432 7 5 273 2409 22 _ _ (311489 / 20000) (194681 / 12500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5810432 :
    ThetaLowerSegment 5810432 5814528 (580644102757 / 100000) (290517519511 / 50000) := by
  exact
    thetaTile4096 5810432 5814528 7 5 251 2410 22 _ _ (311503 / 20000) (778759 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5814528 :
    ThetaLowerSegment 5814528 5818624 (290517519511 / 50000) (290720005691 / 50000) := by
  exact
    thetaTile4096 5814528 5818624 7 5 260 2411 22 _ _ (778793 / 50000) (1557589 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5818624 :
    ThetaLowerSegment 5818624 5822720 (290720005691 / 50000) (290926395111 / 50000) := by
  exact
    thetaTile4096 5818624 5822720 7 5 265 2412 22 _ _ (194707 / 12500) (1557659 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5822720 :
    ThetaLowerSegment 5822720 5826816 (290926395111 / 50000) (291117995409 / 50000) := by
  exact
    thetaTile4096 5822720 5826816 7 5 246 2413 22 _ _ (778863 / 50000) (1557729 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5826816 :
    ThetaLowerSegment 5826816 5830912 (291117995409 / 50000) (72832074501 / 12500) := by
  exact
    thetaTile4096 5826816 5830912 7 5 270 2413 22 _ _ (1557797 / 100000) (7789 / 500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5830912 :
    ThetaLowerSegment 5830912 5835008 (72832074501 / 12500) (291532378581 / 50000) := by
  exact
    thetaTile4096 5830912 5835008 7 5 262 2414 22 _ _ (1557867 / 100000) (155787 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5835008 :
    ThetaLowerSegment 5835008 5839104 (291532378581 / 50000) (583458915223 / 100000) := by
  exact
    thetaTile4096 5835008 5839104 7 5 253 2415 22 _ _ (1557937 / 100000) (77897 / 5000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5839104 :
    ThetaLowerSegment 5839104 5843200 (583458915223 / 100000) (291939009553 / 50000) := by
  exact
    thetaTile4096 5839104 5843200 7 5 269 2416 22 _ _ (1558007 / 100000) (155801 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5843200 :
    ThetaLowerSegment 5843200 5847296 (291939009553 / 50000) (73037337487 / 12500) := by
  exact
    thetaTile4096 5843200 5847296 7 5 270 2417 22 _ _ (1558077 / 100000) (9738 / 625) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5847296 :
    ThetaLowerSegment 5847296 5851392 (73037337487 / 12500) (584705376263 / 100000) := by
  exact
    thetaTile4096 5847296 5851392 7 5 261 2418 22 _ _ (1558147 / 100000) (31163 / 2000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5851392 :
    ThetaLowerSegment 5851392 5855488 (584705376263 / 100000) (117024907381 / 20000) := by
  exact
    thetaTile4096 5851392 5855488 7 5 269 2418 22 _ _ (779109 / 50000) (1558221 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5855488 :
    ThetaLowerSegment 5855488 5859584 (117024907381 / 20000) (117102821731 / 20000) := by
  exact
    thetaTile4096 5855488 5859584 7 5 250 2419 22 _ _ (1558287 / 100000) (155829 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5859584 :
    ThetaLowerSegment 5859584 5863680 (117102821731 / 20000) (585909931333 / 100000) := by
  exact
    thetaTile4096 5859584 5863680 7 5 254 2420 22 _ _ (1558357 / 100000) (38959 / 2500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5863680 :
    ThetaLowerSegment 5863680 5867776 (585909931333 / 100000) (586330706623 / 100000) := by
  exact
    thetaTile4096 5863680 5867776 7 5 270 2421 22 _ _ (1558427 / 100000) (155843 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5867776 :
    ThetaLowerSegment 5867776 5871872 (586330706623 / 100000) (29336873717 / 5000) := by
  exact
    thetaTile4096 5867776 5871872 7 5 261 2422 22 _ _ (1558497 / 100000) (3117 / 200) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5871872 :
    ThetaLowerSegment 5871872 5875968 (29336873717 / 5000) (587144260327 / 100000) := by
  exact
    thetaTile4096 5871872 5875968 7 5 261 2423 22 _ _ (1558567 / 100000) (155857 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5875968 :
    ThetaLowerSegment 5875968 5880064 (587144260327 / 100000) (587552623221 / 100000) := by
  exact
    thetaTile4096 5875968 5880064 7 5 262 2424 22 _ _ (1558637 / 100000) (19483 / 1250) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5880064 :
    ThetaLowerSegment 5880064 5884160 (587552623221 / 100000) (587999971843 / 100000) := by
  exact
    thetaTile4096 5880064 5884160 7 5 287 2424 22 _ _ (779353 / 50000) (1558709 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5884160 :
    ThetaLowerSegment 5884160 5888256 (587999971843 / 100000) (588430194019 / 100000) := by
  exact
    thetaTile4096 5884160 5888256 7 5 276 2425 22 _ _ (194847 / 12500) (1558779 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5888256 :
    ThetaLowerSegment 5888256 5892352 (588430194019 / 100000) (117764292873 / 20000) := by
  exact
    thetaTile4096 5888256 5892352 7 5 251 2426 22 _ _ (779423 / 50000) (1558849 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5892352 :
    ThetaLowerSegment 5892352 5896448 (117764292873 / 20000) (11785128033 / 2000) := by
  exact
    thetaTile4096 5892352 5896448 7 5 279 2427 22 _ _ (311783 / 20000) (779459 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5896448 :
    ThetaLowerSegment 5896448 5904640 (11785128033 / 2000) (118014350161 / 20000) := by
  exact
    thetaTile4096 5896448 5904640 7 6 523 2428 22 _ _ (311797 / 20000) (389747 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5904640 :
    ThetaLowerSegment 5904640 5912832 (118014350161 / 20000) (590907440733 / 100000) := by
  exact
    thetaTile4096 5904640 5912832 7 6 536 2429 22 _ _ (1559123 / 100000) (779563 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5912832 :
    ThetaLowerSegment 5912832 5921024 (590907440733 / 100000) (591763475571 / 100000) := by
  exact
    thetaTile4096 5912832 5921024 7 6 549 2431 22 _ _ (779631 / 50000) (311853 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5921024 :
    ThetaLowerSegment 5921024 5929216 (591763475571 / 100000) (592583719971 / 100000) := by
  exact
    thetaTile4096 5921024 5929216 7 6 526 2433 22 _ _ (7797 / 500) (1559403 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5929216 :
    ThetaLowerSegment 5929216 5937408 (592583719971 / 100000) (18543924907 / 3125) := by
  exact
    thetaTile4096 5929216 5937408 7 6 527 2434 22 _ _ (1559539 / 100000) (779771 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5937408 :
    ThetaLowerSegment 5937408 5945600 (18543924907 / 3125) (297116112917 / 50000) := by
  exact
    thetaTile4096 5937408 5945600 7 6 530 2436 23 _ _ (1559677 / 100000) (9748 / 625) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5945600 :
    ThetaLowerSegment 5945600 5953792 (297116112917 / 50000) (297518545187 / 50000) := by
  exact
    thetaTile4096 5945600 5953792 7 6 516 2438 23 _ _ (311963 / 20000) (779909 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5953792 :
    ThetaLowerSegment 5953792 5961984 (297518545187 / 50000) (297931152491 / 50000) := by
  exact
    thetaTile4096 5953792 5961984 7 6 529 2440 23 _ _ (97497 / 6250) (311991 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5961984 :
    ThetaLowerSegment 5961984 5970176 (297931152491 / 50000) (149166437833 / 25000) := by
  exact
    thetaTile4096 5961984 5970176 7 6 515 2441 23 _ _ (156009 / 10000) (1560093 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5970176 :
    ThetaLowerSegment 5970176 5978368 (149166437833 / 25000) (37341926779 / 6250) := by
  exact
    thetaTile4096 5970176 5978368 7 6 516 2443 23 _ _ (1560227 / 100000) (156023 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5978368 :
    ThetaLowerSegment 5978368 5986560 (37341926779 / 6250) (37392638609 / 6250) := by
  exact
    thetaTile4096 5978368 5986560 7 6 520 2445 23 _ _ (390091 / 25000) (1560367 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5986560 :
    ThetaLowerSegment 5986560 5994752 (37392638609 / 6250) (599104601771 / 100000) := by
  exact
    thetaTile4096 5986560 5994752 7 6 527 2446 23 _ _ (1560501 / 100000) (195063 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell5994752 :
    ThetaLowerSegment 5994752 6002944 (599104601771 / 100000) (599906769703 / 100000) := by
  exact
    thetaTile4096 5994752 6002944 7 6 514 2448 23 _ _ (780319 / 50000) (1560641 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6002944 :
    ThetaLowerSegment 6002944 6011136 (599906769703 / 100000) (300381817589 / 50000) := by
  exact
    thetaTile4096 6002944 6011136 7 6 549 2450 23 _ _ (62431 / 4000) (780389 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6011136 :
    ThetaLowerSegment 6011136 6019328 (300381817589 / 50000) (150393046769 / 25000) := by
  exact
    thetaTile4096 6011136 6019328 7 6 518 2451 23 _ _ (1560911 / 100000) (780457 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6019328 :
    ThetaLowerSegment 6019328 6027520 (150393046769 / 25000) (602422957691 / 100000) := by
  exact
    thetaTile4096 6019328 6027520 7 6 545 2453 23 _ _ (1561047 / 100000) (31221 / 2000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6027520 :
    ThetaLowerSegment 6027520 6035712 (602422957691 / 100000) (150798935819 / 25000) := by
  exact
    thetaTile4096 6027520 6035712 7 6 495 2455 23 _ _ (1561183 / 100000) (780593 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6035712 :
    ThetaLowerSegment 6035712 6043904 (150798935819 / 25000) (151005029927 / 25000) := by
  exact
    thetaTile4096 6035712 6043904 7 6 528 2456 23 _ _ (1561319 / 100000) (780661 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6043904 :
    ThetaLowerSegment 6043904 6052096 (151005029927 / 25000) (302414476699 / 50000) := by
  exact
    thetaTile4096 6043904 6052096 7 6 518 2458 23 _ _ (312291 / 20000) (780729 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6052096 :
    ThetaLowerSegment 6052096 6060288 (302414476699 / 50000) (151415320217 / 25000) := by
  exact
    thetaTile4096 6052096 6060288 7 6 533 2460 23 _ _ (156159 / 10000) (1561593 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6060288 :
    ThetaLowerSegment 6060288 6068480 (151415320217 / 25000) (75805267921 / 12500) := by
  exact
    thetaTile4096 6060288 6068480 7 6 500 2461 23 _ _ (62469 / 4000) (48804 / 3125) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6068480 :
    ThetaLowerSegment 6068480 6076672 (75805267921 / 12500) (75911474401 / 12500) := by
  exact
    thetaTile4096 6068480 6076672 7 6 544 2463 23 _ _ (78093 / 5000) (1561863 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6076672 :
    ThetaLowerSegment 6076672 6084864 (75911474401 / 12500) (38004940043 / 6250) := by
  exact
    thetaTile4096 6076672 6084864 7 6 504 2465 23 _ _ (312399 / 20000) (780999 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6084864 :
    ThetaLowerSegment 6084864 6093056 (38004940043 / 6250) (76113761731 / 12500) := by
  exact
    thetaTile4096 6084864 6093056 7 6 532 2466 23 _ _ (156213 / 10000) (1562133 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6093056 :
    ThetaLowerSegment 6093056 6101248 (76113761731 / 12500) (152435304707 / 25000) := by
  exact
    thetaTile4096 6093056 6101248 7 6 532 2468 23 _ _ (312453 / 20000) (390567 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6101248 :
    ThetaLowerSegment 6101248 6109440 (152435304707 / 25000) (1221132331 / 200) := by
  exact
    thetaTile4096 6101248 6109440 7 6 528 2470 23 _ _ (1562399 / 100000) (781201 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6109440 :
    ThetaLowerSegment 6109440 6117632 (1221132331 / 200) (24455459813 / 4000) := by
  exact
    thetaTile4096 6109440 6117632 7 6 525 2471 23 _ _ (1562533 / 100000) (195317 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6117632 :
    ThetaLowerSegment 6117632 6125824 (24455459813 / 4000) (612192831497 / 100000) := by
  exact
    thetaTile4096 6117632 6125824 7 6 516 2473 23 _ _ (1562667 / 100000) (156267 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6125824 :
    ThetaLowerSegment 6125824 6134016 (612192831497 / 100000) (306503525409 / 50000) := by
  exact
    thetaTile4096 6125824 6134016 7 6 521 2475 23 _ _ (1562801 / 100000) (390701 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6134016 :
    ThetaLowerSegment 6134016 6142208 (306503525409 / 50000) (153457288657 / 25000) := by
  exact
    thetaTile4096 6134016 6142208 7 6 526 2476 23 _ _ (312587 / 20000) (781469 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6142208 :
    ThetaLowerSegment 6142208 6150400 (153457288657 / 25000) (76832392967 / 12500) := by
  exact
    thetaTile4096 6142208 6150400 7 6 531 2478 23 _ _ (390767 / 25000) (1563071 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6150400 :
    ThetaLowerSegment 6150400 6158592 (76832392967 / 12500) (307740693731 / 50000) := by
  exact
    thetaTile4096 6150400 6158592 7 6 526 2480 23 _ _ (1563201 / 100000) (390801 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6158592 :
    ThetaLowerSegment 6158592 6166784 (307740693731 / 50000) (154073971119 / 25000) := by
  exact
    thetaTile4096 6158592 6166784 7 6 521 2481 23 _ _ (781667 / 50000) (1563337 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6166784 :
    ThetaLowerSegment 6166784 6174976 (154073971119 / 25000) (617122958519 / 100000) := by
  exact
    thetaTile4096 6166784 6174976 7 6 529 2483 23 _ _ (1563467 / 100000) (156347 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6174976 :
    ThetaLowerSegment 6174976 6183168 (617122958519 / 100000) (617929776119 / 100000) := by
  exact
    thetaTile4096 6174976 6183168 7 6 516 2484 23 _ _ (3909 / 250) (1563603 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6183168 :
    ThetaLowerSegment 6183168 6191360 (617929776119 / 100000) (154679865321 / 25000) := by
  exact
    thetaTile4096 6183168 6191360 7 6 505 2486 23 _ _ (1563733 / 100000) (195467 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6191360 :
    ThetaLowerSegment 6191360 6199552 (154679865321 / 25000) (19361373387 / 3125) := by
  exact
    thetaTile4096 6191360 6199552 7 6 540 2488 23 _ _ (312773 / 20000) (390967 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6199552 :
    ThetaLowerSegment 6199552 6207744 (19361373387 / 3125) (620385046809 / 100000) := by
  exact
    thetaTile4096 6199552 6207744 7 6 525 2489 23 _ _ (1563997 / 100000) (391 / 25) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6207744 :
    ThetaLowerSegment 6207744 6215936 (620385046809 / 100000) (124237801823 / 20000) := by
  exact
    thetaTile4096 6207744 6215936 7 6 514 2491 23 _ _ (1564129 / 100000) (391033 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6215936 :
    ThetaLowerSegment 6215936 6224128 (124237801823 / 20000) (310994173243 / 50000) := by
  exact
    thetaTile4096 6215936 6224128 7 6 511 2493 23 _ _ (1564261 / 100000) (195533 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6224128 :
    ThetaLowerSegment 6224128 6232320 (310994173243 / 50000) (124558176019 / 20000) := by
  exact
    thetaTile4096 6224128 6232320 7 6 513 2494 23 _ _ (1564393 / 100000) (391099 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6232320 :
    ThetaLowerSegment 6232320 6236416 (124558176019 / 20000) (124645789363 / 20000) := by
  exact
    thetaTile4096 6232320 6236416 7 5 280 2496 23 _ _ (391131 / 25000) (1564527 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6236416 :
    ThetaLowerSegment 6236416 6244608 (124645789363 / 20000) (124806942133 / 20000) := by
  exact
    thetaTile4096 6236416 6244608 7 6 515 2497 23 _ _ (156459 / 10000) (1564593 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6244608 :
    ThetaLowerSegment 6244608 6252800 (124806942133 / 20000) (19526462527 / 3125) := by
  exact
    thetaTile4096 6244608 6252800 7 6 519 2498 23 _ _ (1564721 / 100000) (391181 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6252800 :
    ThetaLowerSegment 6252800 6256896 (19526462527 / 3125) (1563165453 / 250) := by
  exact
    thetaTile4096 6252800 6256896 7 5 268 2500 23 _ _ (391213 / 25000) (312971 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6256896 :
    ThetaLowerSegment 6256896 6265088 (1563165453 / 250) (313054836001 / 50000) := by
  exact
    thetaTile4096 6256896 6265088 7 6 539 2501 23 _ _ (782459 / 50000) (1564921 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6265088 :
    ThetaLowerSegment 6265088 6273280 (313054836001 / 50000) (626946973217 / 100000) := by
  exact
    thetaTile4096 6265088 6273280 7 6 535 2503 23 _ _ (1565049 / 100000) (391263 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6273280 :
    ThetaLowerSegment 6273280 6281472 (626946973217 / 100000) (313879650559 / 50000) := by
  exact
    thetaTile4096 6273280 6281472 7 6 519 2504 23 _ _ (1565179 / 100000) (782591 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6281472 :
    ThetaLowerSegment 6281472 6289664 (313879650559 / 50000) (314297588329 / 50000) := by
  exact
    thetaTile4096 6281472 6289664 7 6 534 2506 23 _ _ (156531 / 10000) (1565313 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6289664 :
    ThetaLowerSegment 6289664 6297856 (314297588329 / 50000) (314719474409 / 50000) := by
  exact
    thetaTile4096 6289664 6297856 7 6 539 2507 23 _ _ (9784 / 625) (1565443 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6297856 :
    ThetaLowerSegment 6297856 6306048 (314719474409 / 50000) (78786914451 / 12500) := by
  exact
    thetaTile4096 6297856 6306048 7 6 547 2509 23 _ _ (156557 / 10000) (1565573 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6306048 :
    ThetaLowerSegment 6306048 6314240 (78786914451 / 12500) (157770715677 / 25000) := by
  exact
    thetaTile4096 6306048 6314240 7 6 503 2511 23 _ _ (15657 / 1000) (1565703 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6314240 :
    ThetaLowerSegment 6314240 6322432 (157770715677 / 25000) (315955593389 / 50000) := by
  exact
    thetaTile4096 6314240 6322432 7 6 529 2512 23 _ _ (156583 / 10000) (1565833 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6322432 :
    ThetaLowerSegment 6322432 6330624 (315955593389 / 50000) (316382317489 / 50000) := by
  exact
    thetaTile4096 6322432 6330624 7 6 545 2514 23 _ _ (39149 / 2500) (1565963 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6330624 :
    ThetaLowerSegment 6330624 6338816 (316382317489 / 50000) (316786368451 / 50000) := by
  exact
    thetaTile4096 6330624 6338816 7 6 516 2516 23 _ _ (1566089 / 100000) (391523 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6338816 :
    ThetaLowerSegment 6338816 6347008 (316786368451 / 50000) (39648219287 / 6250) := by
  exact
    thetaTile4096 6338816 6347008 7 6 510 2517 23 _ _ (1566219 / 100000) (783111 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6347008 :
    ThetaLowerSegment 6347008 6355200 (39648219287 / 6250) (39699125597 / 6250) := by
  exact
    thetaTile4096 6347008 6355200 7 6 520 2519 23 _ _ (391587 / 25000) (1566351 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6355200 :
    ThetaLowerSegment 6355200 6363392 (39699125597 / 6250) (127196669269 / 20000) := by
  exact
    thetaTile4096 6355200 6363392 7 6 509 2520 23 _ _ (1566477 / 100000) (19581 / 1250) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6363392 :
    ThetaLowerSegment 6363392 6371584 (127196669269 / 20000) (127356463081 / 20000) := by
  exact
    thetaTile4096 6363392 6371584 7 6 510 2522 23 _ _ (783303 / 50000) (1566609 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6371584 :
    ThetaLowerSegment 6371584 6379776 (127356463081 / 20000) (637568815873 / 100000) := by
  exact
    thetaTile4096 6371584 6379776 7 6 502 2524 23 _ _ (783367 / 50000) (1566737 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6379776 :
    ThetaLowerSegment 6379776 6387968 (637568815873 / 100000) (319187875159 / 50000) := by
  exact
    thetaTile4096 6379776 6387968 7 6 515 2525 23 _ _ (1566863 / 100000) (783433 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6387968 :
    ThetaLowerSegment 6387968 6396160 (319187875159 / 50000) (319595292819 / 50000) := by
  exact
    thetaTile4096 6387968 6396160 7 6 520 2527 23 _ _ (1566991 / 100000) (783497 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6396160 :
    ThetaLowerSegment 6396160 6404352 (319595292819 / 50000) (640016457351 / 100000) := by
  exact
    thetaTile4096 6396160 6404352 7 6 527 2529 23 _ _ (1567119 / 100000) (783561 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6404352 :
    ThetaLowerSegment 6404352 6412544 (640016457351 / 100000) (640837694779 / 100000) := by
  exact
    thetaTile4096 6404352 6412544 7 6 524 2530 23 _ _ (1567247 / 100000) (6269 / 400) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6412544 :
    ThetaLowerSegment 6412544 6420736 (640837694779 / 100000) (641643325529 / 100000) := by
  exact
    thetaTile4096 6412544 6420736 7 6 514 2532 23 _ _ (12539 / 800) (783689 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6420736 :
    ThetaLowerSegment 6420736 6428928 (641643325529 / 100000) (80309066827 / 12500) := by
  exact
    thetaTile4096 6420736 6428928 7 6 529 2533 23 _ _ (1567503 / 100000) (783753 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6428928 :
    ThetaLowerSegment 6428928 6437120 (80309066827 / 12500) (321630526253 / 50000) := by
  exact
    thetaTile4096 6428928 6437120 7 6 503 2535 23 _ _ (156763 / 10000) (1567633 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6437120 :
    ThetaLowerSegment 6437120 6441216 (321630526253 / 50000) (160916775457 / 25000) := by
  exact
    thetaTile4096 6437120 6441216 7 5 259 2537 23 _ _ (783879 / 50000) (1567761 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6441216 :
    ThetaLowerSegment 6441216 6445312 (160916775457 / 25000) (161020251643 / 25000) := by
  exact
    thetaTile4096 6441216 6445312 7 5 264 2537 23 _ _ (1567821 / 100000) (97989 / 6250) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6445312 :
    ThetaLowerSegment 6445312 6449408 (161020251643 / 25000) (644477681477 / 100000) := by
  exact
    thetaTile4096 6445312 6449408 7 5 253 2538 23 _ _ (313577 / 20000) (97993 / 6250) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6449408 :
    ThetaLowerSegment 6449408 6453504 (644477681477 / 100000) (644915138969 / 100000) := by
  exact
    thetaTile4096 6449408 6453504 7 5 279 2539 23 _ _ (391987 / 25000) (1567951 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6453504 :
    ThetaLowerSegment 6453504 6461696 (644915138969 / 100000) (129147041849 / 20000) := by
  exact
    thetaTile4096 6453504 6461696 7 6 523 2540 23 _ _ (392003 / 25000) (313603 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6461696 :
    ThetaLowerSegment 6461696 6469888 (129147041849 / 20000) (64654280083 / 10000) := by
  exact
    thetaTile4096 6461696 6469888 7 6 515 2541 23 _ _ (1568139 / 100000) (784071 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6469888 :
    ThetaLowerSegment 6469888 6478080 (64654280083 / 10000) (25894520137 / 4000) := by
  exact
    thetaTile4096 6469888 6478080 7 6 523 2543 23 _ _ (313653 / 20000) (392067 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6478080 :
    ThetaLowerSegment 6478080 6486272 (25894520137 / 4000) (648175430481 / 100000) := by
  exact
    thetaTile4096 6478080 6486272 7 6 518 2545 23 _ _ (196049 / 12500) (313679 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6486272 :
    ThetaLowerSegment 6486272 6494464 (648175430481 / 100000) (648981648733 / 100000) := by
  exact
    thetaTile4096 6486272 6494464 7 6 514 2546 23 _ _ (784259 / 50000) (1568521 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6494464 :
    ThetaLowerSegment 6494464 6498560 (648981648733 / 100000) (324698669829 / 50000) := by
  exact
    thetaTile4096 6494464 6498560 7 5 265 2548 23 _ _ (313729 / 20000) (196081 / 12500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6498560 :
    ThetaLowerSegment 6498560 6502656 (324698669829 / 50000) (324916720241 / 50000) := by
  exact
    thetaTile4096 6498560 6502656 7 5 278 2549 23 _ _ (392177 / 25000) (1568711 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6502656 :
    ThetaLowerSegment 6502656 6510848 (324916720241 / 50000) (325321463159 / 50000) := by
  exact
    thetaTile4096 6502656 6510848 7 6 516 2550 23 _ _ (1568771 / 100000) (784387 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6510848 :
    ThetaLowerSegment 6510848 6519040 (325321463159 / 50000) (651466597243 / 100000) := by
  exact
    thetaTile4096 6510848 6519040 7 6 525 2551 23 _ _ (1568897 / 100000) (15689 / 1000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6519040 :
    ThetaLowerSegment 6519040 6527232 (651466597243 / 100000) (130455242519 / 20000) := by
  exact
    thetaTile4096 6519040 6527232 7 6 516 2553 23 _ _ (784511 / 50000) (62761 / 4000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6527232 :
    ThetaLowerSegment 6527232 6535424 (130455242519 / 20000) (653087462111 / 100000) := by
  exact
    thetaTile4096 6527232 6535424 7 6 517 2554 23 _ _ (392287 / 25000) (1569151 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6535424 :
    ThetaLowerSegment 6535424 6543616 (653087462111 / 100000) (653925453893 / 100000) := by
  exact
    thetaTile4096 6535424 6543616 7 6 534 2556 23 _ _ (1569273 / 100000) (392319 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6543616 :
    ThetaLowerSegment 6543616 6551808 (653925453893 / 100000) (327360569593 / 50000) := by
  exact
    thetaTile4096 6543616 6551808 7 6 507 2558 23 _ _ (1569399 / 100000) (784701 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6551808 :
    ThetaLowerSegment 6551808 6560000 (327360569593 / 50000) (327782771549 / 50000) := by
  exact
    thetaTile4096 6551808 6560000 7 6 538 2559 23 _ _ (392381 / 25000) (1569527 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6560000 :
    ThetaLowerSegment 6560000 6568192 (327782771549 / 50000) (328190880289 / 50000) := by
  exact
    thetaTile4096 6560000 6568192 7 6 520 2561 23 _ _ (1569649 / 100000) (392413 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6568192 :
    ThetaLowerSegment 6568192 6576384 (328190880289 / 50000) (131442434099 / 20000) := by
  exact
    thetaTile4096 6568192 6576384 7 6 529 2562 23 _ _ (1569773 / 100000) (98111 / 6250) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6576384 :
    ThetaLowerSegment 6576384 6584576 (131442434099 / 20000) (658058345517 / 100000) := by
  exact
    thetaTile4096 6576384 6584576 7 6 539 2564 23 _ _ (784949 / 50000) (1569901 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6584576 :
    ThetaLowerSegment 6584576 6592768 (658058345517 / 100000) (658865337339 / 100000) := by
  exact
    thetaTile4096 6584576 6592768 7 6 514 2566 23 _ _ (1570023 / 100000) (785013 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6592768 :
    ThetaLowerSegment 6592768 6600960 (658865337339 / 100000) (329841691963 / 50000) := by
  exact
    thetaTile4096 6592768 6600960 7 6 521 2567 23 _ _ (1570147 / 100000) (31403 / 2000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6600960 :
    ThetaLowerSegment 6600960 6609152 (329841691963 / 50000) (165128906889 / 25000) := by
  exact
    thetaTile4096 6600960 6609152 7 6 530 2569 23 _ _ (1570271 / 100000) (785137 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6609152 :
    ThetaLowerSegment 6609152 6617344 (165128906889 / 25000) (330680250033 / 50000) := by
  exact
    thetaTile4096 6609152 6617344 7 6 538 2570 23 _ _ (314079 / 20000) (785199 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6617344 :
    ThetaLowerSegment 6617344 6625536 (330680250033 / 50000) (165540366189 / 25000) := by
  exact
    thetaTile4096 6617344 6625536 7 6 510 2572 23 _ _ (1570519 / 100000) (785261 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6625536 :
    ThetaLowerSegment 6625536 6633728 (165540366189 / 25000) (20717872392 / 3125) := by
  exact
    thetaTile4096 6625536 6633728 7 6 516 2574 23 _ _ (1570643 / 100000) (785323 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6633728 :
    ThetaLowerSegment 6633728 6641920 (20717872392 / 3125) (165947964099 / 25000) := by
  exact
    thetaTile4096 6633728 6641920 7 6 522 2575 23 _ _ (785383 / 50000) (1570769 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6641920 :
    ThetaLowerSegment 6641920 6650112 (165947964099 / 25000) (83074126287 / 12500) := by
  exact
    thetaTile4096 6641920 6650112 7 6 510 2577 23 _ _ (157089 / 10000) (1570893 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6650112 :
    ThetaLowerSegment 6650112 6658304 (83074126287 / 12500) (665395797939 / 100000) := by
  exact
    thetaTile4096 6650112 6658304 7 6 511 2578 23 _ _ (1571013 / 100000) (196377 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6658304 :
    ThetaLowerSegment 6658304 6666496 (665395797939 / 100000) (666204932979 / 100000) := by
  exact
    thetaTile4096 6658304 6666496 7 6 515 2580 23 _ _ (49098 / 3125) (1571139 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6666496 :
    ThetaLowerSegment 6666496 6674688 (666204932979 / 100000) (667034557731 / 100000) := by
  exact
    thetaTile4096 6666496 6674688 7 6 528 2581 23 _ _ (1571259 / 100000) (785631 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6674688 :
    ThetaLowerSegment 6674688 6682880 (667034557731 / 100000) (667834391169 / 100000) := by
  exact
    thetaTile4096 6674688 6682880 7 6 509 2583 23 _ _ (785691 / 50000) (314277 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6682880 :
    ThetaLowerSegment 6682880 6691072 (667834391169 / 100000) (668635858209 / 100000) := by
  exact
    thetaTile4096 6682880 6691072 7 6 510 2585 23 _ _ (98219 / 6250) (1571507 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6691072 :
    ThetaLowerSegment 6691072 6699264 (668635858209 / 100000) (669471963773 / 100000) := by
  exact
    thetaTile4096 6691072 6699264 7 6 532 2586 23 _ _ (1571627 / 100000) (157163 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6699264 :
    ThetaLowerSegment 6699264 6707456 (669471963773 / 100000) (670308134241 / 100000) := by
  exact
    thetaTile4096 6699264 6707456 7 6 532 2588 23 _ _ (1571749 / 100000) (196469 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6707456 :
    ThetaLowerSegment 6707456 6715648 (670308134241 / 100000) (671150657633 / 100000) := by
  exact
    thetaTile4096 6707456 6715648 7 6 536 2589 23 _ _ (49121 / 3125) (503 / 32) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6715648 :
    ThetaLowerSegment 6715648 6723840 (671150657633 / 100000) (671982242459 / 100000) := by
  exact
    thetaTile4096 6715648 6723840 7 6 529 2591 23 _ _ (785997 / 50000) (1571997 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6723840 :
    ThetaLowerSegment 6723840 6732032 (671982242459 / 100000) (168197970421 / 25000) := by
  exact
    thetaTile4096 6723840 6732032 7 6 515 2593 23 _ _ (314423 / 20000) (786059 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6732032 :
    ThetaLowerSegment 6732032 6740224 (168197970421 / 25000) (673611017161 / 100000) := by
  exact
    thetaTile4096 6732032 6740224 7 6 521 2594 23 _ _ (1572237 / 100000) (19653 / 1250) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6740224 :
    ThetaLowerSegment 6740224 6748416 (673611017161 / 100000) (674444367431 / 100000) := by
  exact
    thetaTile4096 6740224 6748416 7 6 530 2596 23 _ _ (1572359 / 100000) (786181 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6748416 :
    ThetaLowerSegment 6748416 6756608 (674444367431 / 100000) (675274636871 / 100000) := by
  exact
    thetaTile4096 6748416 6756608 7 6 528 2597 23 _ _ (9828 / 625) (1572483 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6756608 :
    ThetaLowerSegment 6756608 6764800 (675274636871 / 100000) (676100252921 / 100000) := by
  exact
    thetaTile4096 6756608 6764800 7 6 525 2599 23 _ _ (786301 / 50000) (314521 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6764800 :
    ThetaLowerSegment 6764800 6772992 (676100252921 / 100000) (21153149029 / 3125) := by
  exact
    thetaTile4096 6764800 6772992 7 6 509 2600 23 _ _ (1572723 / 100000) (786363 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6772992 :
    ThetaLowerSegment 6772992 6781184 (21153149029 / 3125) (169432414429 / 25000) := by
  exact
    thetaTile4096 6772992 6781184 7 6 527 2602 23 _ _ (393211 / 25000) (1572847 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6781184 :
    ThetaLowerSegment 6781184 6789376 (169432414429 / 25000) (678527150971 / 100000) := by
  exact
    thetaTile4096 6781184 6789376 7 6 507 2604 23 _ _ (314593 / 20000) (196621 / 12500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6789376 :
    ThetaLowerSegment 6789376 6797568 (678527150971 / 100000) (679316839641 / 100000) := by
  exact
    thetaTile4096 6789376 6797568 7 6 502 2605 23 _ _ (314617 / 20000) (49159 / 3125) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6797568 :
    ThetaLowerSegment 6797568 6805760 (679316839641 / 100000) (680160078057 / 100000) := by
  exact
    thetaTile4096 6797568 6805760 7 6 536 2607 23 _ _ (786603 / 50000) (1573209 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6805760 :
    ThetaLowerSegment 6805760 6813952 (680160078057 / 100000) (680978207577 / 100000) := by
  exact
    thetaTile4096 6805760 6813952 7 6 520 2608 23 _ _ (786663 / 50000) (1573329 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6813952 :
    ThetaLowerSegment 6813952 6822144 (680978207577 / 100000) (681824722063 / 100000) := by
  exact
    thetaTile4096 6813952 6822144 7 6 538 2610 23 _ _ (1573447 / 100000) (31469 / 2000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6822144 :
    ThetaLowerSegment 6822144 6830336 (681824722063 / 100000) (170655630133 / 25000) := by
  exact
    thetaTile4096 6822144 6830336 7 6 507 2611 23 _ _ (1573567 / 100000) (157357 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6830336 :
    ThetaLowerSegment 6830336 6838528 (170655630133 / 25000) (683442411459 / 100000) := by
  exact
    thetaTile4096 6830336 6838528 7 6 521 2613 23 _ _ (1573687 / 100000) (157369 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6838528 :
    ThetaLowerSegment 6838528 6846720 (683442411459 / 100000) (21383690718 / 3125) := by
  exact
    thetaTile4096 6838528 6846720 7 6 531 2615 23 _ _ (1573807 / 100000) (157381 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6846720 :
    ThetaLowerSegment 6846720 6854912 (21383690718 / 3125) (137018364647 / 20000) := by
  exact
    thetaTile4096 6846720 6854912 7 6 517 2616 23 _ _ (1573927 / 100000) (157393 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6854912 :
    ThetaLowerSegment 6854912 6863104 (137018364647 / 20000) (137189935661 / 20000) := by
  exact
    thetaTile4096 6854912 6863104 7 6 545 2618 23 _ _ (787023 / 50000) (1574049 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6863104 :
    ThetaLowerSegment 6863104 6871296 (137189935661 / 20000) (686782412119 / 100000) := by
  exact
    thetaTile4096 6863104 6871296 7 6 529 2619 23 _ _ (787083 / 50000) (1574169 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6871296 :
    ThetaLowerSegment 6871296 6879488 (686782412119 / 100000) (171900653651 / 25000) := by
  exact
    thetaTile4096 6871296 6879488 7 6 521 2621 23 _ _ (314857 / 20000) (98393 / 6250) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6879488 :
    ThetaLowerSegment 6879488 6887680 (171900653651 / 25000) (21513411772 / 3125) := by
  exact
    thetaTile4096 6879488 6887680 7 6 525 2622 23 _ _ (393601 / 25000) (1574407 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6887680 :
    ThetaLowerSegment 6887680 6895872 (21513411772 / 3125) (689265248417 / 100000) := by
  exact
    thetaTile4096 6887680 6895872 7 6 531 2624 23 _ _ (1574523 / 100000) (787263 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6895872 :
    ThetaLowerSegment 6895872 6904064 (689265248417 / 100000) (690047845491 / 100000) := by
  exact
    thetaTile4096 6895872 6904064 7 6 497 2625 23 _ _ (787321 / 50000) (314929 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6904064 :
    ThetaLowerSegment 6904064 6912256 (690047845491 / 100000) (690885618343 / 100000) := by
  exact
    thetaTile4096 6904064 6912256 7 6 532 2627 23 _ _ (1574761 / 100000) (393691 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6912256 :
    ThetaLowerSegment 6912256 6920448 (690885618343 / 100000) (138343430891 / 20000) := by
  exact
    thetaTile4096 6912256 6920448 7 6 528 2629 23 _ _ (1574879 / 100000) (787441 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6920448 :
    ThetaLowerSegment 6920448 6928640 (138343430891 / 20000) (692499928461 / 100000) := by
  exact
    thetaTile4096 6920448 6928640 7 6 497 2630 23 _ _ (787499 / 50000) (1575001 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6928640 :
    ThetaLowerSegment 6928640 6936832 (692499928461 / 100000) (693345765753 / 100000) := by
  exact
    thetaTile4096 6928640 6936832 7 6 537 2632 23 _ _ (393779 / 25000) (1575119 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6936832 :
    ThetaLowerSegment 6936832 6945024 (693345765753 / 100000) (138832347393 / 20000) := by
  exact
    thetaTile4096 6936832 6945024 7 6 518 2633 23 _ _ (787617 / 50000) (1575237 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6945024 :
    ThetaLowerSegment 6945024 6953216 (138832347393 / 20000) (695032906621 / 100000) := by
  exact
    thetaTile4096 6945024 6953216 7 6 553 2635 23 _ _ (196919 / 12500) (315071 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6953216 :
    ThetaLowerSegment 6953216 6961408 (695032906621 / 100000) (695828518971 / 100000) := by
  exact
    thetaTile4096 6953216 6961408 7 6 505 2636 23 _ _ (157547 / 10000) (1575473 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6961408 :
    ThetaLowerSegment 6961408 6969600 (695828518971 / 100000) (139330510299 / 20000) := by
  exact
    thetaTile4096 6961408 6969600 7 6 523 2638 23 _ _ (393897 / 25000) (1575591 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6969600 :
    ThetaLowerSegment 6969600 6977792 (139330510299 / 20000) (34873989831 / 5000) := by
  exact
    thetaTile4096 6969600 6977792 7 6 525 2640 23 _ _ (315141 / 20000) (393927 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6977792 :
    ThetaLowerSegment 6977792 6985984 (34873989831 / 5000) (698272435589 / 100000) := by
  exact
    thetaTile4096 6977792 6985984 7 6 503 2641 23 _ _ (1575823 / 100000) (787913 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6985984 :
    ThetaLowerSegment 6985984 6994176 (698272435589 / 100000) (699085620629 / 100000) := by
  exact
    thetaTile4096 6985984 6994176 7 6 516 2643 23 _ _ (78797 / 5000) (1575943 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell6994176 :
    ThetaLowerSegment 6994176 7002368 (699085620629 / 100000) (699914626611 / 100000) := by
  exact
    thetaTile4096 6994176 7002368 7 6 526 2644 23 _ _ (1576057 / 100000) (78803 / 5000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7002368 :
    ThetaLowerSegment 7002368 7010560 (699914626611 / 100000) (140147162653 / 20000) := by
  exact
    thetaTile4096 7002368 7010560 7 6 521 2646 23 _ _ (788087 / 50000) (1576177 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7010560 :
    ThetaLowerSegment 7010560 7018752 (140147162653 / 20000) (701552332003 / 100000) := by
  exact
    thetaTile4096 7010560 7018752 7 6 518 2647 23 _ _ (1576291 / 100000) (788147 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7018752 :
    ThetaLowerSegment 7018752 7026944 (701552332003 / 100000) (140475673959 / 20000) := by
  exact
    thetaTile4096 7018752 7026944 7 6 524 2649 23 _ _ (197051 / 12500) (1576411 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7026944 :
    ThetaLowerSegment 7026944 7035136 (140475673959 / 20000) (17580624093 / 2500) := by
  exact
    thetaTile4096 7026944 7035136 7 6 537 2650 23 _ _ (63061 / 4000) (98533 / 6250) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7035136 :
    ThetaLowerSegment 7035136 7043328 (17580624093 / 2500) (704071619937 / 100000) := by
  exact
    thetaTile4096 7035136 7043328 7 6 537 2652 23 _ _ (1576641 / 100000) (394161 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7043328 :
    ThetaLowerSegment 7043328 7051520 (704071619937 / 100000) (704915185467 / 100000) := by
  exact
    thetaTile4096 7043328 7051520 7 6 535 2653 23 _ _ (788379 / 50000) (1576761 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7051520 :
    ThetaLowerSegment 7051520 7059712 (704915185467 / 100000) (705725698703 / 100000) := by
  exact
    thetaTile4096 7051520 7059712 7 6 514 2655 23 _ _ (788437 / 50000) (1576877 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7059712 :
    ThetaLowerSegment 7059712 7067904 (705725698703 / 100000) (706495269823 / 100000) := by
  exact
    thetaTile4096 7059712 7067904 7 6 488 2657 23 _ _ (157699 / 10000) (1576993 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7067904 :
    ThetaLowerSegment 7067904 7076096 (706495269823 / 100000) (707332713109 / 100000) := by
  exact
    thetaTile4096 7067904 7076096 7 6 531 2658 23 _ _ (788553 / 50000) (1577109 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7076096 :
    ThetaLowerSegment 7076096 7084288 (707332713109 / 100000) (708148136883 / 100000) := by
  exact
    thetaTile4096 7076096 7084288 7 6 517 2660 23 _ _ (788611 / 50000) (63089 / 4000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7084288 :
    ThetaLowerSegment 7084288 7092480 (708148136883 / 100000) (708987280167 / 100000) := by
  exact
    thetaTile4096 7084288 7092480 7 6 532 2661 23 _ _ (1577337 / 100000) (78867 / 5000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7092480 :
    ThetaLowerSegment 7092480 7100672 (708987280167 / 100000) (35490456659 / 5000) := by
  exact
    thetaTile4096 7092480 7100672 7 6 521 2663 23 _ _ (1577453 / 100000) (98591 / 6250) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7100672 :
    ThetaLowerSegment 7100672 7108864 (35490456659 / 5000) (35532656603 / 5000) := by
  exact
    thetaTile4096 7100672 7108864 7 6 535 2664 23 _ _ (49299 / 3125) (1577571 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7108864 :
    ThetaLowerSegment 7108864 7117056 (35532656603 / 5000) (88933993757 / 12500) := by
  exact
    thetaTile4096 7108864 7117056 7 6 519 2666 23 _ _ (394421 / 25000) (1577687 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7117056 :
    ThetaLowerSegment 7117056 7125248 (88933993757 / 12500) (178068367987 / 25000) := by
  exact
    thetaTile4096 7117056 7125248 7 6 508 2667 23 _ _ (1577799 / 100000) (788901 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7125248 :
    ThetaLowerSegment 7125248 7133440 (178068367987 / 25000) (22282313328 / 3125) := by
  exact
    thetaTile4096 7125248 7133440 7 6 482 2669 23 _ _ (788957 / 50000) (1577917 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7133440 :
    ThetaLowerSegment 7133440 7141632 (22282313328 / 3125) (356925722759 / 50000) := by
  exact
    thetaTile4096 7133440 7141632 7 6 518 2670 23 _ _ (1578029 / 100000) (98627 / 6250) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7141632 :
    ThetaLowerSegment 7141632 7149824 (356925722759 / 50000) (14293694111 / 2000) := by
  exact
    thetaTile4096 7141632 7149824 7 6 528 2672 23 _ _ (49317 / 3125) (1578147 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7149824 :
    ThetaLowerSegment 7149824 7158016 (14293694111 / 2000) (357751121597 / 50000) := by
  exact
    thetaTile4096 7149824 7158016 7 6 518 2673 23 _ _ (789129 / 50000) (1578261 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7158016 :
    ThetaLowerSegment 7158016 7166208 (357751121597 / 50000) (179078381729 / 25000) := by
  exact
    thetaTile4096 7158016 7166208 7 6 514 2675 23 _ _ (1578373 / 100000) (197297 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7166208 :
    ThetaLowerSegment 7166208 7174400 (179078381729 / 25000) (143429077913 / 20000) := by
  exact
    thetaTile4096 7166208 7174400 7 6 527 2676 23 _ _ (1578487 / 100000) (157849 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7174400 :
    ThetaLowerSegment 7174400 7182592 (143429077913 / 20000) (89741638933 / 12500) := by
  exact
    thetaTile4096 7174400 7182592 7 6 499 2678 23 _ _ (1578601 / 100000) (394651 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7182592 :
    ThetaLowerSegment 7182592 7190784 (89741638933 / 12500) (179687326909 / 25000) := by
  exact
    thetaTile4096 7182592 7190784 7 6 517 2680 23 _ _ (394679 / 25000) (1578719 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7190784 :
    ThetaLowerSegment 7190784 7198976 (179687326909 / 25000) (179890995979 / 25000) := by
  exact
    thetaTile4096 7190784 7198976 7 6 516 2681 23 _ _ (157883 / 10000) (1578833 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7198976 :
    ThetaLowerSegment 7198976 7207168 (179890995979 / 25000) (360200411853 / 50000) := by
  exact
    thetaTile4096 7198976 7207168 7 6 530 2683 23 _ _ (1578943 / 100000) (789473 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7207168 :
    ThetaLowerSegment 7207168 7215360 (360200411853 / 50000) (721210879947 / 100000) := by
  exact
    thetaTile4096 7207168 7215360 7 6 513 2684 23 _ _ (1579057 / 100000) (78953 / 5000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7215360 :
    ThetaLowerSegment 7215360 7223552 (721210879947 / 100000) (722032048867 / 100000) := by
  exact
    thetaTile4096 7215360 7223552 7 6 520 2686 23 _ _ (1579171 / 100000) (789587 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7223552 :
    ThetaLowerSegment 7223552 7231744 (722032048867 / 100000) (144564969887 / 20000) := by
  exact
    thetaTile4096 7223552 7231744 7 6 502 2687 23 _ _ (394821 / 25000) (1579287 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7231744 :
    ThetaLowerSegment 7231744 7239936 (144564969887 / 20000) (723657192181 / 100000) := by
  exact
    thetaTile4096 7231744 7239936 7 6 527 2689 23 _ _ (789699 / 50000) (1579401 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7239936 :
    ThetaLowerSegment 7239936 7248128 (723657192181 / 100000) (90562383943 / 12500) := by
  exact
    thetaTile4096 7239936 7248128 7 6 533 2690 23 _ _ (1579511 / 100000) (789757 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7248128 :
    ThetaLowerSegment 7248128 7256320 (90562383943 / 12500) (90664664597 / 12500) := by
  exact
    thetaTile4096 7248128 7256320 7 6 518 2692 23 _ _ (197453 / 12500) (1579627 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7256320 :
    ThetaLowerSegment 7256320 7264512 (90664664597 / 12500) (45383673751 / 6250) := by
  exact
    thetaTile4096 7256320 7264512 7 6 520 2693 23 _ _ (1579737 / 100000) (78987 / 5000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7264512 :
    ThetaLowerSegment 7264512 7272704 (45383673751 / 6250) (363482520783 / 50000) := by
  exact
    thetaTile4096 7264512 7272704 7 6 523 2695 23 _ _ (31597 / 2000) (1579853 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7272704 :
    ThetaLowerSegment 7272704 7280896 (363482520783 / 50000) (363893310903 / 50000) := by
  exact
    thetaTile4096 7272704 7280896 7 6 520 2696 23 _ _ (789981 / 50000) (315993 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7280896 :
    ThetaLowerSegment 7280896 7289088 (363893310903 / 50000) (91077217657 / 12500) := by
  exact
    thetaTile4096 7280896 7289088 7 6 526 2698 23 _ _ (63203 / 4000) (790039 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7289088 :
    ThetaLowerSegment 7289088 7297280 (91077217657 / 12500) (145890099961 / 20000) := by
  exact
    thetaTile4096 7289088 7297280 7 6 527 2699 23 _ _ (1580187 / 100000) (158019 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7297280 :
    ThetaLowerSegment 7297280 7305472 (145890099961 / 20000) (146048129961 / 20000) := by
  exact
    thetaTile4096 7297280 7305472 7 6 500 2701 23 _ _ (15803 / 1000) (1580303 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7305472 :
    ThetaLowerSegment 7305472 7313664 (146048129961 / 20000) (731035597041 / 100000) := by
  exact
    thetaTile4096 7305472 7313664 7 6 503 2702 23 _ _ (395103 / 25000) (316083 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7313664 :
    ThetaLowerSegment 7313664 7321856 (731035597041 / 100000) (731887499477 / 100000) := by
  exact
    thetaTile4096 7313664 7321856 7 6 539 2704 23 _ _ (395131 / 25000) (1580527 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7321856 :
    ThetaLowerSegment 7321856 7330048 (731887499477 / 100000) (732703107653 / 100000) := by
  exact
    thetaTile4096 7321856 7330048 7 6 516 2705 23 _ _ (395159 / 25000) (1580639 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7330048 :
    ThetaLowerSegment 7330048 7338240 (732703107653 / 100000) (733504546889 / 100000) := by
  exact
    thetaTile4096 7330048 7338240 7 6 507 2707 23 _ _ (395187 / 25000) (1580751 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7338240 :
    ThetaLowerSegment 7338240 7346432 (733504546889 / 100000) (734294976389 / 100000) := by
  exact
    thetaTile4096 7338240 7346432 7 6 500 2708 23 _ _ (1580859 / 100000) (790431 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7346432 :
    ThetaLowerSegment 7346432 7354624 (734294976389 / 100000) (18377966557 / 2500) := by
  exact
    thetaTile4096 7346432 7354624 7 6 521 2710 23 _ _ (1580971 / 100000) (790487 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7354624 :
    ThetaLowerSegment 7354624 7362816 (18377966557 / 2500) (36797831787 / 5000) := by
  exact
    thetaTile4096 7354624 7362816 7 6 530 2711 23 _ _ (790541 / 50000) (316217 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7362816 :
    ThetaLowerSegment 7362816 7371008 (36797831787 / 5000) (14735419013 / 2000) := by
  exact
    thetaTile4096 7362816 7371008 7 6 515 2713 23 _ _ (790597 / 50000) (1581197 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7371008 :
    ThetaLowerSegment 7371008 7379200 (14735419013 / 2000) (73761853013 / 10000) := by
  exact
    thetaTile4096 7371008 7379200 7 6 536 2714 23 _ _ (316261 / 20000) (395327 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7379200 :
    ThetaLowerSegment 7379200 7387392 (73761853013 / 10000) (369210944729 / 50000) := by
  exact
    thetaTile4096 7379200 7387392 7 6 508 2716 23 _ _ (197677 / 12500) (1581419 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7387392 :
    ThetaLowerSegment 7387392 7395584 (369210944729 / 50000) (184803954003 / 25000) := by
  exact
    thetaTile4096 7387392 7395584 7 6 502 2717 23 _ _ (1581527 / 100000) (158153 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7395584 :
    ThetaLowerSegment 7395584 7403776 (184803954003 / 25000) (370016761429 / 50000) := by
  exact
    thetaTile4096 7395584 7403776 7 6 517 2719 23 _ _ (790819 / 50000) (1581641 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7403776 :
    ThetaLowerSegment 7403776 7411968 (370016761429 / 50000) (92603445107 / 12500) := by
  exact
    thetaTile4096 7403776 7411968 7 6 502 2720 23 _ _ (1581749 / 100000) (197719 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7411968 :
    ThetaLowerSegment 7411968 7420160 (92603445107 / 12500) (370836136781 / 50000) := by
  exact
    thetaTile4096 7411968 7420160 7 6 534 2722 23 _ _ (1581859 / 100000) (790931 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7420160 :
    ThetaLowerSegment 7420160 7428352 (370836136781 / 50000) (185622538013 / 25000) := by
  exact
    thetaTile4096 7420160 7428352 7 6 517 2723 23 _ _ (158197 / 10000) (1581973 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7428352 :
    ThetaLowerSegment 7428352 7436544 (185622538013 / 25000) (185831768093 / 25000) := by
  exact
    thetaTile4096 7428352 7436544 7 6 529 2725 23 _ _ (9888 / 625) (1582083 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7436544 :
    ThetaLowerSegment 7436544 7444736 (185831768093 / 25000) (23254780486 / 3125) := by
  exact
    thetaTile4096 7436544 7444736 7 6 522 2727 23 _ _ (158219 / 10000) (1582193 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7444736 :
    ThetaLowerSegment 7444736 7452928 (23254780486 / 3125) (186247503063 / 25000) := by
  exact
    thetaTile4096 7444736 7452928 7 6 529 2728 23 _ _ (15823 / 1000) (1582303 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7452928 :
    ThetaLowerSegment 7452928 7461120 (186247503063 / 25000) (372892982241 / 50000) := by
  exact
    thetaTile4096 7452928 7461120 7 6 503 2730 23 _ _ (158241 / 10000) (1582413 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7461120 :
    ThetaLowerSegment 7461120 7469312 (372892982241 / 50000) (373283073421 / 50000) := by
  exact
    thetaTile4096 7461120 7469312 7 6 493 2731 23 _ _ (39563 / 2500) (1582523 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7469312 :
    ThetaLowerSegment 7469312 7477504 (373283073421 / 50000) (373704053001 / 50000) := by
  exact
    thetaTile4096 7469312 7477504 7 6 532 2733 23 _ _ (158263 / 10000) (1582633 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7477504 :
    ThetaLowerSegment 7477504 7485696 (373704053001 / 50000) (748223216587 / 100000) := by
  exact
    thetaTile4096 7477504 7485696 7 6 515 2734 23 _ _ (1582739 / 100000) (791371 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7485696 :
    ThetaLowerSegment 7485696 7493888 (748223216587 / 100000) (374516026213 / 50000) := by
  exact
    thetaTile4096 7485696 7493888 7 6 511 2736 23 _ _ (1582849 / 100000) (395713 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7493888 :
    ThetaLowerSegment 7493888 7502080 (374516026213 / 50000) (187455487117 / 25000) := by
  exact
    thetaTile4096 7493888 7502080 7 6 499 2737 23 _ _ (791479 / 50000) (1582961 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7502080 :
    ThetaLowerSegment 7502080 7510272 (187455487117 / 25000) (187660494423 / 25000) := by
  exact
    thetaTile4096 7502080 7510272 7 6 518 2738 23 _ _ (395767 / 25000) (1583071 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7510272 :
    ThetaLowerSegment 7510272 7518464 (187660494423 / 25000) (751469979263 / 100000) := by
  exact
    thetaTile4096 7510272 7518464 7 6 523 2740 23 _ _ (1583177 / 100000) (79159 / 5000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7518464 :
    ThetaLowerSegment 7518464 7526656 (751469979263 / 100000) (752250539261 / 100000) := by
  exact
    thetaTile4096 7518464 7526656 7 6 493 2741 23 _ _ (791643 / 50000) (1583289 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7526656 :
    ThetaLowerSegment 7526656 7534848 (752250539261 / 100000) (753077071451 / 100000) := by
  exact
    thetaTile4096 7526656 7534848 7 6 522 2743 23 _ _ (316679 / 20000) (791699 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7534848 :
    ThetaLowerSegment 7534848 7543040 (753077071451 / 100000) (376957372269 / 50000) := by
  exact
    thetaTile4096 7534848 7543040 7 6 529 2744 23 _ _ (1583503 / 100000) (791753 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7543040 :
    ThetaLowerSegment 7543040 7551232 (376957372269 / 50000) (377375445837 / 50000) := by
  exact
    thetaTile4096 7543040 7551232 7 6 528 2746 23 _ _ (395903 / 25000) (316723 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7551232 :
    ThetaLowerSegment 7551232 7559424 (377375445837 / 50000) (188894398509 / 25000) := by
  exact
    thetaTile4096 7551232 7559424 7 6 522 2747 23 _ _ (1583721 / 100000) (395931 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7559424 :
    ThetaLowerSegment 7559424 7567616 (188894398509 / 25000) (756364757049 / 100000) := by
  exact
    thetaTile4096 7559424 7567616 7 6 497 2749 23 _ _ (1583829 / 100000) (197979 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7567616 :
    ThetaLowerSegment 7567616 7575808 (756364757049 / 100000) (151433879409 / 20000) := by
  exact
    thetaTile4096 7567616 7575808 7 6 508 2750 23 _ _ (1583937 / 100000) (79197 / 5000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7575808 :
    ThetaLowerSegment 7575808 7584000 (151433879409 / 20000) (151595452101 / 20000) := by
  exact
    thetaTile4096 7575808 7584000 7 6 510 2752 23 _ _ (792023 / 50000) (1584049 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7584000 :
    ThetaLowerSegment 7584000 7592192 (151595452101 / 20000) (758799436431 / 100000) := by
  exact
    thetaTile4096 7584000 7592192 7 6 519 2753 23 _ _ (792077 / 50000) (1584157 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7592192 :
    ThetaLowerSegment 7592192 7600384 (758799436431 / 100000) (6077201481 / 800) := by
  exact
    thetaTile4096 7592192 7600384 7 6 537 2755 23 _ _ (792131 / 50000) (316853 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7600384 :
    ThetaLowerSegment 7600384 7608576 (6077201481 / 800) (380250495639 / 50000) := by
  exact
    thetaTile4096 7600384 7608576 7 6 537 2756 23 _ _ (1584369 / 100000) (396093 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7608576 :
    ThetaLowerSegment 7608576 7616768 (380250495639 / 50000) (190324099683 / 25000) := by
  exact
    thetaTile4096 7608576 7616768 7 6 502 2758 23 _ _ (1584477 / 100000) (9903 / 625) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7616768 :
    ThetaLowerSegment 7616768 7624960 (190324099683 / 25000) (762121967517 / 100000) := by
  exact
    thetaTile4096 7616768 7624960 7 6 521 2759 23 _ _ (316917 / 20000) (396147 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7624960 :
    ThetaLowerSegment 7624960 7633152 (762121967517 / 100000) (152588884533 / 20000) := by
  exact
    thetaTile4096 7624960 7633152 7 6 519 2761 23 _ _ (396173 / 25000) (316939 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7633152 :
    ThetaLowerSegment 7633152 7641344 (152588884533 / 20000) (152750851093 / 20000) := by
  exact
    thetaTile4096 7633152 7641344 7 6 511 2762 23 _ _ (1981 / 125) (1584803 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7641344 :
    ThetaLowerSegment 7641344 7649536 (152750851093 / 20000) (764591086361 / 100000) := by
  exact
    thetaTile4096 7641344 7649536 7 6 528 2764 23 _ _ (1584907 / 100000) (158491 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7649536 :
    ThetaLowerSegment 7649536 7657728 (764591086361 / 100000) (153080205703 / 20000) := by
  exact
    thetaTile4096 7649536 7657728 7 6 511 2765 23 _ _ (792507 / 50000) (1585017 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7657728 :
    ThetaLowerSegment 7657728 7665920 (153080205703 / 20000) (191556719139 / 25000) := by
  exact
    thetaTile4096 7657728 7665920 7 6 521 2767 23 _ _ (1585121 / 100000) (396281 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7665920 :
    ThetaLowerSegment 7665920 7674112 (191556719139 / 25000) (23970696616 / 3125) := by
  exact
    thetaTile4096 7665920 7674112 7 6 527 2768 23 _ _ (396307 / 25000) (1585231 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7674112 :
    ThetaLowerSegment 7674112 7682304 (23970696616 / 3125) (767859715217 / 100000) := by
  exact
    thetaTile4096 7674112 7682304 7 6 503 2770 23 _ _ (317067 / 20000) (792669 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7682304 :
    ThetaLowerSegment 7682304 7690496 (767859715217 / 100000) (768692072267 / 100000) := by
  exact
    thetaTile4096 7682304 7690496 7 6 525 2771 23 _ _ (792721 / 50000) (317089 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7690496 :
    ThetaLowerSegment 7690496 7698688 (768692072267 / 100000) (769527656063 / 100000) := by
  exact
    thetaTile4096 7690496 7698688 7 6 527 2773 23 _ _ (396387 / 25000) (1585551 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7698688 :
    ThetaLowerSegment 7698688 7706880 (769527656063 / 100000) (192582895787 / 25000) := by
  exact
    thetaTile4096 7698688 7706880 7 6 507 2774 23 _ _ (317131 / 20000) (792829 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7706880 :
    ThetaLowerSegment 7706880 7715072 (192582895787 / 25000) (192789044717 / 25000) := by
  exact
    thetaTile4096 7706880 7715072 7 6 520 2776 23 _ _ (1585761 / 100000) (396441 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7715072 :
    ThetaLowerSegment 7715072 7723264 (192789044717 / 25000) (96498396647 / 12500) := by
  exact
    thetaTile4096 7715072 7723264 7 6 524 2777 23 _ _ (1585867 / 100000) (158587 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7723264 :
    ThetaLowerSegment 7723264 7731456 (96498396647 / 12500) (38639642373 / 5000) := by
  exact
    thetaTile4096 7723264 7731456 7 6 508 2779 23 _ _ (1585973 / 100000) (198247 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7731456 :
    ThetaLowerSegment 7731456 7739648 (38639642373 / 5000) (773587473039 / 100000) := by
  exact
    thetaTile4096 7731456 7739648 7 6 501 2780 23 _ _ (1586079 / 100000) (793041 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7739648 :
    ThetaLowerSegment 7739648 7747840 (773587473039 / 100000) (774374220799 / 100000) := by
  exact
    thetaTile4096 7739648 7747840 7 6 496 2782 23 _ _ (317237 / 20000) (396547 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7747840 :
    ThetaLowerSegment 7747840 7756032 (774374220799 / 100000) (387609856951 / 50000) := by
  exact
    thetaTile4096 7747840 7756032 7 6 533 2783 23 _ _ (1586291 / 100000) (793147 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7756032 :
    ThetaLowerSegment 7756032 7764224 (387609856951 / 50000) (776033535563 / 100000) := by
  exact
    thetaTile4096 7756032 7764224 7 6 513 2784 23 _ _ (1586397 / 100000) (1983 / 125) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7764224 :
    ThetaLowerSegment 7764224 7772416 (776033535563 / 100000) (776833132571 / 100000) := by
  exact
    thetaTile4096 7764224 7772416 7 6 504 2786 23 _ _ (793251 / 50000) (317301 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7772416 :
    ThetaLowerSegment 7772416 7780608 (776833132571 / 100000) (155534172319 / 20000) := by
  exact
    thetaTile4096 7772416 7780608 7 6 528 2787 23 _ _ (99163 / 6250) (1586611 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7780608 :
    ThetaLowerSegment 7780608 7788800 (155534172319 / 20000) (194611691063 / 25000) := by
  exact
    thetaTile4096 7780608 7788800 7 6 489 2789 23 _ _ (1586713 / 100000) (396679 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7788800 :
    ThetaLowerSegment 7788800 7796992 (194611691063 / 25000) (389633574579 / 50000) := by
  exact
    thetaTile4096 7788800 7796992 7 6 517 2790 23 _ _ (793409 / 50000) (1586821 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7796992 :
    ThetaLowerSegment 7796992 7805184 (389633574579 / 50000) (780093936041 / 100000) := by
  exact
    thetaTile4096 7796992 7805184 7 6 521 2792 23 _ _ (1586923 / 100000) (793463 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7805184 :
    ThetaLowerSegment 7805184 7813376 (780093936041 / 100000) (780944583049 / 100000) := by
  exact
    thetaTile4096 7805184 7813376 7 6 536 2793 23 _ _ (396757 / 25000) (1587031 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7813376 :
    ThetaLowerSegment 7813376 7821568 (780944583049 / 100000) (390869868341 / 50000) := by
  exact
    thetaTile4096 7813376 7821568 7 6 501 2795 23 _ _ (1587133 / 100000) (49598 / 3125) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7821568 :
    ThetaLowerSegment 7821568 7829760 (390869868341 / 50000) (391277788507 / 50000) := by
  exact
    thetaTile4096 7821568 7829760 7 6 514 2796 23 _ _ (793619 / 50000) (1587241 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7829760 :
    ThetaLowerSegment 7829760 7837952 (391277788507 / 50000) (783366709287 / 100000) := by
  exact
    thetaTile4096 7829760 7837952 7 6 511 2798 23 _ _ (1587343 / 100000) (793673 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7837952 :
    ThetaLowerSegment 7837952 7846144 (783366709287 / 100000) (156846056091 / 20000) := by
  exact
    thetaTile4096 7837952 7846144 7 6 544 2799 23 _ _ (1587447 / 100000) (31749 / 2000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7846144 :
    ThetaLowerSegment 7846144 7854336 (156846056091 / 20000) (785052632391 / 100000) := by
  exact
    thetaTile4096 7846144 7854336 7 6 518 2801 23 _ _ (49611 / 3125) (317511 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7854336 :
    ThetaLowerSegment 7854336 7862528 (785052632391 / 100000) (785881388823 / 100000) := by
  exact
    thetaTile4096 7854336 7862528 7 6 522 2802 23 _ _ (198457 / 12500) (1587659 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7862528 :
    ThetaLowerSegment 7862528 7870720 (785881388823 / 100000) (786695909703 / 100000) := by
  exact
    thetaTile4096 7862528 7870720 7 6 513 2804 23 _ _ (19847 / 1250) (1587763 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7870720 :
    ThetaLowerSegment 7870720 7878912 (786695909703 / 100000) (787527950963 / 100000) := by
  exact
    thetaTile4096 7870720 7878912 7 6 524 2805 23 _ _ (317573 / 20000) (396967 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7878912 :
    ThetaLowerSegment 7878912 7887104 (787527950963 / 100000) (788353694843 / 100000) := by
  exact
    thetaTile4096 7878912 7887104 7 6 520 2806 23 _ _ (1587969 / 100000) (396993 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7887104 :
    ThetaLowerSegment 7887104 7895296 (788353694843 / 100000) (789187432643 / 100000) := by
  exact
    thetaTile4096 7887104 7895296 7 6 525 2808 23 _ _ (198509 / 12500) (63523 / 4000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7895296 :
    ThetaLowerSegment 7895296 7903488 (789187432643 / 100000) (789967227059 / 100000) := by
  exact
    thetaTile4096 7895296 7903488 7 6 491 2809 23 _ _ (99261 / 6250) (1588179 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7903488 :
    ThetaLowerSegment 7903488 7911680 (789967227059 / 100000) (790810603739 / 100000) := by
  exact
    thetaTile4096 7903488 7911680 7 6 531 2811 23 _ _ (39707 / 2500) (1588283 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7911680 :
    ThetaLowerSegment 7911680 7919872 (790810603739 / 100000) (791623856347 / 100000) := by
  exact
    thetaTile4096 7911680 7919872 7 6 512 2812 23 _ _ (49637 / 3125) (1588387 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7919872 :
    ThetaLowerSegment 7919872 7928064 (791623856347 / 100000) (158488067733 / 20000) := by
  exact
    thetaTile4096 7919872 7928064 7 6 514 2814 23 _ _ (1588487 / 100000) (158849 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7928064 :
    ThetaLowerSegment 7928064 7936256 (158488067733 / 20000) (158652645657 / 20000) := by
  exact
    thetaTile4096 7928064 7936256 7 6 518 2815 23 _ _ (158859 / 10000) (1588593 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7936256 :
    ThetaLowerSegment 7936256 7944448 (158652645657 / 20000) (794086171777 / 100000) := by
  exact
    thetaTile4096 7936256 7944448 7 6 518 2817 23 _ _ (794347 / 50000) (1588697 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7944448 :
    ThetaLowerSegment 7944448 7952640 (794086171777 / 100000) (397456967507 / 50000) := by
  exact
    thetaTile4096 7944448 7952640 7 6 521 2818 23 _ _ (1588797 / 100000) (1986 / 125) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7952640 :
    ThetaLowerSegment 7952640 7960832 (397456967507 / 50000) (397857370307 / 50000) := by
  exact
    thetaTile4096 7952640 7960832 7 6 504 2820 23 _ _ (15889 / 1000) (1588903 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7960832 :
    ThetaLowerSegment 7960832 7969024 (397857370307 / 50000) (19912810503 / 2500) := by
  exact
    thetaTile4096 7960832 7969024 7 6 502 2821 23 _ _ (1589003 / 100000) (794503 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7969024 :
    ThetaLowerSegment 7969024 7977216 (19912810503 / 2500) (24917432016 / 3125) := by
  exact
    thetaTile4096 7969024 7977216 7 6 532 2822 23 _ _ (794553 / 50000) (1589109 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7977216 :
    ThetaLowerSegment 7977216 7985408 (24917432016 / 3125) (798182623983 / 100000) := by
  exact
    thetaTile4096 7977216 7985408 7 6 519 2824 23 _ _ (1589209 / 100000) (397303 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7985408 :
    ThetaLowerSegment 7985408 7993600 (798182623983 / 100000) (798986815349 / 100000) := by
  exact
    thetaTile4096 7985408 7993600 7 6 506 2825 23 _ _ (1589311 / 100000) (794657 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell7993600 :
    ThetaLowerSegment 7993600 8001792 (798986815349 / 100000) (799799005903 / 100000) := by
  exact
    thetaTile4096 7993600 8001792 7 6 511 2827 23 _ _ (794707 / 50000) (1589417 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8001792 :
    ThetaLowerSegment 8001792 8009984 (799799005903 / 100000) (800625554223 / 100000) := by
  exact
    thetaTile4096 8001792 8009984 7 6 520 2828 23 _ _ (397379 / 25000) (1589519 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8009984 :
    ThetaLowerSegment 8009984 8018176 (800625554223 / 100000) (801420363223 / 100000) := by
  exact
    thetaTile4096 8009984 8018176 7 6 500 2830 23 _ _ (794809 / 50000) (1589621 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8018176 :
    ThetaLowerSegment 8018176 8026368 (801420363223 / 100000) (160450039517 / 20000) := by
  exact
    thetaTile4096 8018176 8026368 7 6 522 2831 23 _ _ (1589721 / 100000) (397431 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8026368 :
    ThetaLowerSegment 8026368 8034560 (160450039517 / 20000) (803032390501 / 100000) := by
  exact
    thetaTile4096 8026368 8034560 7 6 492 2833 23 _ _ (1589823 / 100000) (794913 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8034560 :
    ThetaLowerSegment 8034560 8042752 (803032390501 / 100000) (401930370713 / 50000) := by
  exact
    thetaTile4096 8034560 8042752 7 6 521 2834 23 _ _ (63597 / 4000) (198741 / 12500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8042752 :
    ThetaLowerSegment 8042752 8050944 (401930370713 / 50000) (402331057517 / 50000) := by
  exact
    thetaTile4096 8042752 8050944 7 6 504 2835 23 _ _ (1590027 / 100000) (159003 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8050944 :
    ThetaLowerSegment 8050944 8059136 (402331057517 / 50000) (402762777269 / 50000) := by
  exact
    thetaTile4096 8050944 8059136 7 6 543 2837 23 _ _ (99383 / 6250) (1590131 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8059136 :
    ThetaLowerSegment 8059136 8067328 (402762777269 / 50000) (201587720977 / 25000) := by
  exact
    thetaTile4096 8059136 8067328 7 6 519 2838 23 _ _ (159023 / 10000) (1590233 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8067328 :
    ThetaLowerSegment 8067328 8075520 (201587720977 / 25000) (201789693141 / 25000) := by
  exact
    thetaTile4096 8067328 8075520 7 6 508 2840 23 _ _ (397583 / 25000) (318067 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8075520 :
    ThetaLowerSegment 8075520 8083712 (201789693141 / 25000) (403975404099 / 50000) := by
  exact
    thetaTile4096 8075520 8083712 7 6 498 2841 23 _ _ (1590433 / 100000) (397609 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8083712 :
    ThetaLowerSegment 8083712 8091904 (403975404099 / 50000) (404379399989 / 50000) := by
  exact
    thetaTile4096 8083712 8091904 7 6 508 2843 23 _ _ (318107 / 20000) (795269 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8091904 :
    ThetaLowerSegment 8091904 8096000 (404379399989 / 50000) (404582206079 / 50000) := by
  exact
    thetaTile4096 8091904 8096000 7 5 255 2844 23 _ _ (397659 / 25000) (1590639 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_4000000_8096000 :
    ThetaLowerSegment 4000000 8096000 (39965831043 / 10000) (404582206079 / 50000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell4000000 cell4004096)
                      (ThetaLowerSegment.join cell4008192 cell4012288))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell4016384 cell4020480)
                      (ThetaLowerSegment.join cell4024576 cell4028672)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell4032768 cell4036864)
                      (ThetaLowerSegment.join cell4040960 cell4045056))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell4049152 cell4053248)
                      (ThetaLowerSegment.join cell4057344 cell4061440))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell4065536 cell4069632)
                      (ThetaLowerSegment.join cell4073728 cell4077824))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell4081920 cell4086016)
                      (ThetaLowerSegment.join cell4090112 cell4094208)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell4098304 cell4102400)
                      (ThetaLowerSegment.join cell4106496 cell4110592))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell4114688 cell4118784)
                      (ThetaLowerSegment.join cell4122880 cell4126976)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell4131072 cell4135168)
                      (ThetaLowerSegment.join cell4139264 cell4143360))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell4147456 cell4151552)
                      (ThetaLowerSegment.join cell4155648 cell4159744)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell4163840 cell4167936)
                      (ThetaLowerSegment.join cell4172032 cell4176128))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell4180224 cell4184320)
                      (ThetaLowerSegment.join cell4188416 cell4192512))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell4196608 cell4200704)
                      (ThetaLowerSegment.join cell4204800 cell4208896))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell4212992 cell4217088)
                      (ThetaLowerSegment.join cell4221184 cell4225280)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell4229376 cell4233472)
                      (ThetaLowerSegment.join cell4237568 cell4241664))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell4245760 cell4249856)
                      (ThetaLowerSegment.join cell4253952 cell4258048))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell4262144 cell4266240)
                      (ThetaLowerSegment.join cell4270336 cell4274432))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell4278528 cell4282624)
                      (ThetaLowerSegment.join cell4286720 cell4290816)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell4294912 cell4299008)
                      (ThetaLowerSegment.join cell4303104 cell4307200))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell4311296 cell4315392)
                      (ThetaLowerSegment.join cell4319488 cell4323584))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell4327680 cell4331776)
                      (ThetaLowerSegment.join cell4335872 cell4339968))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell4344064 cell4348160)
                      (ThetaLowerSegment.join cell4352256 cell4356352)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell4360448 cell4364544)
                      (ThetaLowerSegment.join cell4368640 cell4372736))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell4376832 cell4380928)
                      (ThetaLowerSegment.join cell4385024 cell4389120)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell4393216 cell4397312)
                      (ThetaLowerSegment.join cell4401408 cell4405504))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell4409600 cell4413696)
                      (ThetaLowerSegment.join cell4417792 cell4421888)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell4425984 cell4430080)
                      (ThetaLowerSegment.join cell4434176 cell4438272))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell4442368 cell4446464)
                      (ThetaLowerSegment.join cell4450560 cell4454656))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell4458752 cell4462848)
                      (ThetaLowerSegment.join cell4466944 cell4471040))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell4475136 cell4479232)
                      (ThetaLowerSegment.join cell4483328 cell4487424)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell4491520 cell4495616)
                      (ThetaLowerSegment.join cell4499712 cell4503808))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell4507904 cell4512000)
                      (ThetaLowerSegment.join cell4516096 cell4520192)))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell4524288 cell4528384)
                      (ThetaLowerSegment.join cell4532480 cell4536576))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell4540672 cell4544768)
                      (ThetaLowerSegment.join cell4548864 cell4552960)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell4557056 cell4561152)
                      (ThetaLowerSegment.join cell4565248 cell4569344))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell4573440 cell4577536)
                      (ThetaLowerSegment.join cell4581632 cell4585728))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell4589824 cell4593920)
                      (ThetaLowerSegment.join cell4598016 cell4602112))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell4606208 cell4610304)
                      (ThetaLowerSegment.join cell4614400 cell4618496)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell4622592 cell4626688)
                      (ThetaLowerSegment.join cell4630784 cell4634880))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell4638976 cell4643072)
                      (ThetaLowerSegment.join cell4647168 cell4651264)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell4655360 cell4659456)
                      (ThetaLowerSegment.join cell4663552 cell4667648))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell4671744 cell4675840)
                      (ThetaLowerSegment.join cell4679936 cell4684032)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell4688128 cell4692224)
                      (ThetaLowerSegment.join cell4696320 cell4700416))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell4704512 cell4708608)
                      (ThetaLowerSegment.join cell4712704 cell4716800))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell4720896 cell4724992)
                      (ThetaLowerSegment.join cell4729088 cell4733184))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell4737280 cell4741376)
                      (ThetaLowerSegment.join cell4745472 cell4749568)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell4753664 cell4757760)
                      (ThetaLowerSegment.join cell4761856 cell4765952))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell4770048 cell4774144)
                      (ThetaLowerSegment.join cell4778240 cell4782336))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell4786432 cell4790528)
                      (ThetaLowerSegment.join cell4794624 cell4798720))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell4802816 cell4806912)
                      (ThetaLowerSegment.join cell4811008 cell4815104)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell4819200 cell4823296)
                      (ThetaLowerSegment.join cell4827392 cell4831488))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell4835584 cell4839680)
                      (ThetaLowerSegment.join cell4843776 cell4847872))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell4851968 cell4856064)
                      (ThetaLowerSegment.join cell4860160 cell4864256))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell4868352 cell4872448)
                      (ThetaLowerSegment.join cell4876544 cell4880640)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell4884736 cell4888832)
                      (ThetaLowerSegment.join cell4892928 cell4897024))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell4905216 cell4913408)
                      (ThetaLowerSegment.join cell4921600 cell4929792)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell4937984 cell4946176)
                      (ThetaLowerSegment.join cell4954368 cell4962560))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell4970752 cell4978944)
                      (ThetaLowerSegment.join cell4987136 cell4995328)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell5003520 cell5011712)
                      (ThetaLowerSegment.join cell5019904 cell5028096))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell5036288 cell5044480)
                      (ThetaLowerSegment.join cell5052672 cell5060864))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell5069056 cell5077248)
                      (ThetaLowerSegment.join cell5085440 cell5093632))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell5101824 cell5110016)
                      (ThetaLowerSegment.join cell5118208 cell5126400)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell5134592 cell5142784)
                      (ThetaLowerSegment.join cell5150976 cell5159168))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell5167360 cell5175552)
                      (ThetaLowerSegment.join cell5183744 cell5191936))))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell5200128 cell5208320)
                      (ThetaLowerSegment.join cell5216512 cell5224704))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell5232896 cell5241088)
                      (ThetaLowerSegment.join cell5249280 cell5257472)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell5265664 cell5273856)
                      (ThetaLowerSegment.join cell5282048 cell5290240))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell5298432 cell5306624)
                      (ThetaLowerSegment.join cell5314816 cell5323008))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell5331200 cell5339392)
                      (ThetaLowerSegment.join cell5347584 cell5355776))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell5363968 cell5372160)
                      (ThetaLowerSegment.join cell5380352 cell5388544)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell5396736 cell5404928)
                      (ThetaLowerSegment.join cell5413120 cell5421312))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell5429504 cell5437696)
                      (ThetaLowerSegment.join cell5445888 cell5454080)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell5462272 cell5470464)
                      (ThetaLowerSegment.join cell5478656 cell5486848))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell5495040 cell5503232)
                      (ThetaLowerSegment.join cell5511424 cell5519616)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell5527808 cell5536000)
                      (ThetaLowerSegment.join cell5544192 cell5552384))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell5560576 cell5568768)
                      (ThetaLowerSegment.join cell5576960 cell5585152))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell5593344 cell5601536)
                      (ThetaLowerSegment.join cell5609728 cell5617920))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell5626112 cell5630208)
                      (ThetaLowerSegment.join cell5638400 cell5646592)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell5650688 cell5654784)
                      (ThetaLowerSegment.join cell5658880 cell5662976))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell5667072 cell5671168)
                      (ThetaLowerSegment.join cell5675264 cell5679360))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell5683456 cell5687552)
                      (ThetaLowerSegment.join cell5691648 cell5695744))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell5699840 cell5708032)
                      (ThetaLowerSegment.join cell5716224 cell5724416)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell5732608 cell5740800)
                      (ThetaLowerSegment.join cell5748992 cell5757184))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell5765376 cell5773568)
                      (ThetaLowerSegment.join cell5777664 cell5781760))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell5785856 cell5789952)
                      (ThetaLowerSegment.join cell5794048 cell5798144))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell5802240 cell5806336)
                      (ThetaLowerSegment.join cell5810432 cell5814528)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell5818624 cell5822720)
                      (ThetaLowerSegment.join cell5826816 cell5830912))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell5835008 cell5839104)
                      (ThetaLowerSegment.join cell5843200 cell5847296)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell5851392 cell5855488)
                      (ThetaLowerSegment.join cell5859584 cell5863680))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell5867776 cell5871872)
                      (ThetaLowerSegment.join cell5875968 cell5880064)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell5884160 cell5888256)
                      (ThetaLowerSegment.join cell5892352 cell5896448))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell5904640 cell5912832)
                      (ThetaLowerSegment.join cell5921024 cell5929216))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell5937408 cell5945600)
                      (ThetaLowerSegment.join cell5953792 cell5961984))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell5970176 cell5978368)
                      (ThetaLowerSegment.join cell5986560 cell5994752)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell6002944 cell6011136)
                      (ThetaLowerSegment.join cell6019328 cell6027520))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell6035712 cell6043904)
                      (ThetaLowerSegment.join cell6052096 cell6060288)))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell6068480 cell6076672)
                      (ThetaLowerSegment.join cell6084864 cell6093056))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell6101248 cell6109440)
                      (ThetaLowerSegment.join cell6117632 cell6125824)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell6134016 cell6142208)
                      (ThetaLowerSegment.join cell6150400 cell6158592))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell6166784 cell6174976)
                      (ThetaLowerSegment.join cell6183168 cell6191360))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell6199552 cell6207744)
                      (ThetaLowerSegment.join cell6215936 cell6224128))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell6232320 cell6236416)
                      (ThetaLowerSegment.join cell6244608 cell6252800)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell6256896 cell6265088)
                      (ThetaLowerSegment.join cell6273280 cell6281472))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell6289664 cell6297856)
                      (ThetaLowerSegment.join cell6306048 cell6314240)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell6322432 cell6330624)
                      (ThetaLowerSegment.join cell6338816 cell6347008))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell6355200 cell6363392)
                      (ThetaLowerSegment.join cell6371584 cell6379776)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell6387968 cell6396160)
                      (ThetaLowerSegment.join cell6404352 cell6412544))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell6420736 cell6428928)
                      (ThetaLowerSegment.join cell6437120 cell6441216))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell6445312 cell6449408)
                      (ThetaLowerSegment.join cell6453504 cell6461696))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell6469888 cell6478080)
                      (ThetaLowerSegment.join cell6486272 cell6494464)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell6498560 cell6502656)
                      (ThetaLowerSegment.join cell6510848 cell6519040))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell6527232 cell6535424)
                      (ThetaLowerSegment.join cell6543616 cell6551808))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell6560000 cell6568192)
                      (ThetaLowerSegment.join cell6576384 cell6584576))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell6592768 cell6600960)
                      (ThetaLowerSegment.join cell6609152 cell6617344)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell6625536 cell6633728)
                      (ThetaLowerSegment.join cell6641920 cell6650112))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell6658304 cell6666496)
                      (ThetaLowerSegment.join cell6674688 cell6682880))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell6691072 cell6699264)
                      (ThetaLowerSegment.join cell6707456 cell6715648))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell6723840 cell6732032)
                      (ThetaLowerSegment.join cell6740224 cell6748416)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell6756608 cell6764800)
                      (ThetaLowerSegment.join cell6772992 cell6781184))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell6789376 cell6797568)
                      (ThetaLowerSegment.join cell6805760 cell6813952)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell6822144 cell6830336)
                      (ThetaLowerSegment.join cell6838528 cell6846720))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell6854912 cell6863104)
                      (ThetaLowerSegment.join cell6871296 cell6879488)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell6887680 cell6895872)
                      (ThetaLowerSegment.join cell6904064 cell6912256))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell6920448 cell6928640)
                      (ThetaLowerSegment.join cell6936832 cell6945024))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell6953216 cell6961408)
                      (ThetaLowerSegment.join cell6969600 cell6977792))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell6985984 cell6994176)
                      (ThetaLowerSegment.join cell7002368 cell7010560)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell7018752 cell7026944)
                      (ThetaLowerSegment.join cell7035136 cell7043328))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell7051520 cell7059712)
                      (ThetaLowerSegment.join cell7067904 cell7076096)))))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell7084288 cell7092480)
                  (ThetaLowerSegment.join cell7100672 cell7108864))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell7117056 cell7125248)
                  (ThetaLowerSegment.join cell7133440 cell7141632)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell7149824 cell7158016)
                  (ThetaLowerSegment.join cell7166208 cell7174400))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell7182592 cell7190784)
                  (ThetaLowerSegment.join cell7198976 cell7207168))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell7215360 cell7223552)
                  (ThetaLowerSegment.join cell7231744 cell7239936))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell7248128 cell7256320)
                  (ThetaLowerSegment.join cell7264512 cell7272704)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell7280896 cell7289088)
                  (ThetaLowerSegment.join cell7297280 cell7305472))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell7313664 cell7321856)
                  (ThetaLowerSegment.join cell7330048 cell7338240)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell7346432 cell7354624)
                  (ThetaLowerSegment.join cell7362816 cell7371008))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell7379200 cell7387392)
                  (ThetaLowerSegment.join cell7395584 cell7403776)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell7411968 cell7420160)
                  (ThetaLowerSegment.join cell7428352 cell7436544))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell7444736 cell7452928)
                  (ThetaLowerSegment.join cell7461120 cell7469312))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell7477504 cell7485696)
                  (ThetaLowerSegment.join cell7493888 cell7502080))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell7510272 cell7518464)
                  (ThetaLowerSegment.join cell7526656 cell7534848)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell7543040 cell7551232)
                  (ThetaLowerSegment.join cell7559424 cell7567616))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell7575808 cell7584000)
                  (ThetaLowerSegment.join cell7592192 cell7600384))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell7608576 cell7616768)
                  (ThetaLowerSegment.join cell7624960 cell7633152))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell7641344 cell7649536)
                  (ThetaLowerSegment.join cell7657728 cell7665920)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell7674112 cell7682304)
                  (ThetaLowerSegment.join cell7690496 cell7698688))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell7706880 cell7715072)
                  (ThetaLowerSegment.join cell7723264 cell7731456))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell7739648 cell7747840)
                  (ThetaLowerSegment.join cell7756032 cell7764224))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell7772416 cell7780608)
                  (ThetaLowerSegment.join cell7788800 cell7796992)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell7805184 cell7813376)
                  (ThetaLowerSegment.join cell7821568 cell7829760))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell7837952 cell7846144)
                  (ThetaLowerSegment.join cell7854336 cell7862528)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell7870720 cell7878912)
                  (ThetaLowerSegment.join cell7887104 cell7895296))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell7903488 cell7911680)
                  (ThetaLowerSegment.join cell7919872 cell7928064)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell7936256 cell7944448)
                  (ThetaLowerSegment.join cell7952640 cell7960832))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell7969024 cell7977216)
                  (ThetaLowerSegment.join cell7985408 cell7993600))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell8001792 cell8009984)
                  (ThetaLowerSegment.join cell8018176 cell8026368))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell8034560 cell8042752)
                  (ThetaLowerSegment.join cell8050944 cell8059136)))
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell8067328 cell8075520)
                (ThetaLowerSegment.join cell8083712 cell8091904)))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
