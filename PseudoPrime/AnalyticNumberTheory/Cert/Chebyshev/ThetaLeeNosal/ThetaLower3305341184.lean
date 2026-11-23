/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis65536

/-! # Direct theta estimate up to 3305341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell3273341184 :
    ThetaLowerSegment 3273341184 3273472256 (65465009055529 / 20000) (65467635951823 / 20000) := by
  exact
    packedTile65536 3273341184 3273472256 14 5995 57213 32 _ _ (1095453 / 50000) (2190909 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3273472256 :
    ThetaLowerSegment 3273472256 3273603328 (65467635951823 / 20000) (65470267234733 / 20000) := by
  exact
    packedTile65536 3273472256 3273603328 14 6005 57214 32 _ _ (219091 / 10000) (2190913 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3273603328 :
    ThetaLowerSegment 3273603328 3273734400 (65470267234733 / 20000) (65472909477017 / 20000) := by
  exact
    packedTile65536 3273603328 3273734400 14 6030 57215 32 _ _ (1095457 / 50000) (2190917 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3273734400 :
    ThetaLowerSegment 3273734400 3273865472 (65472909477017 / 20000)
      (327377664411151 / 100000) := by
  exact
    packedTile65536 3273734400 3273865472 14 5987 57216 32 _ _ (1095459 / 50000) (2190921 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3273865472 :
    ThetaLowerSegment 3273865472 3273996544 (327377664411151 / 100000)
      (327390687251519 / 100000) := by
  exact
    packedTile65536 3273865472 3273996544 14 5944 57217 32 _ _ (1095461 / 50000) (87637 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3273996544 :
    ThetaLowerSegment 3273996544 3274127616 (327390687251519 / 100000)
      (327403699161033 / 100000) := by
  exact
    packedTile65536 3273996544 3274127616 14 5939 57218 32 _ _ (1095463 / 50000) (2190929 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3274127616 :
    ThetaLowerSegment 3274127616 3274258688 (327403699161033 / 100000)
      (327416862268473 / 100000) := by
  exact
    packedTile65536 3274127616 3274258688 14 6008 57219 32 _ _ (219093 / 10000) (2190933 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3274258688 :
    ThetaLowerSegment 3274258688 3274389760 (327416862268473 / 100000) (13097196195943 / 4000) := by
  exact
    packedTile65536 3274258688 3274389760 14 5953 57221 32 _ _ (1095467 / 50000) (2190937 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3274389760 :
    ThetaLowerSegment 3274389760 3274520832 (13097196195943 / 4000) (327442719694937 / 100000) := by
  exact
    packedTile65536 3274389760 3274520832 14 5849 57222 32 _ _ (1095469 / 50000) (2190941 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3274520832 :
    ThetaLowerSegment 3274520832 3274651904 (327442719694937 / 100000)
      (65491172631199 / 20000) := by
  exact
    packedTile65536 3274520832 3274651904 14 5999 57223 32 _ _ (1095471 / 50000) (438189 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3274651904 :
    ThetaLowerSegment 3274651904 3274782976 (65491172631199 / 20000)
      (327469039505239 / 100000) := by
  exact
    packedTile65536 3274651904 3274782976 14 6014 57224 32 _ _ (1095473 / 50000) (2190949 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3274782976 :
    ThetaLowerSegment 3274782976 3274914048 (327469039505239 / 100000)
      (327482272843239 / 100000) := by
  exact
    packedTile65536 3274782976 3274914048 14 6040 57225 32 _ _ (43819 / 2000) (2190953 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3274914048 :
    ThetaLowerSegment 3274914048 3275045120 (327482272843239 / 100000)
      (327495212617563 / 100000) := by
  exact
    packedTile65536 3274914048 3275045120 14 5906 57226 32 _ _ (1095477 / 50000) (2190957 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3275045120 :
    ThetaLowerSegment 3275045120 3275176192 (327495212617563 / 100000)
      (327508325501193 / 100000) := by
  exact
    packedTile65536 3275045120 3275176192 14 5985 57228 32 _ _ (1095479 / 50000) (2190961 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3275176192 :
    ThetaLowerSegment 3275176192 3275307264 (327508325501193 / 100000) (13100851051103 / 4000) := by
  exact
    packedTile65536 3275176192 3275307264 14 5911 57229 32 _ _ (1095481 / 50000) (438193 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3275307264 :
    ThetaLowerSegment 3275307264 3275438336 (13100851051103 / 4000) (327534419882609 / 100000) := by
  exact
    packedTile65536 3275307264 3275438336 14 5999 57230 32 _ _ (1095483 / 50000) (2190969 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3275438336 :
    ThetaLowerSegment 3275438336 3275569408 (327534419882609 / 100000)
      (327547670869169 / 100000) := by
  exact
    packedTile65536 3275438336 3275569408 14 6048 57231 32 _ _ (219097 / 10000) (2190973 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3275569408 :
    ThetaLowerSegment 3275569408 3275700480 (327547670869169 / 100000)
      (327560796994403 / 100000) := by
  exact
    packedTile65536 3275569408 3275700480 14 5991 57232 32 _ _ (1095487 / 50000) (2190977 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3275700480 :
    ThetaLowerSegment 3275700480 3275831552 (327560796994403 / 100000)
      (327573909997733 / 100000) := by
  exact
    packedTile65536 3275700480 3275831552 14 5985 57233 32 _ _ (1095489 / 50000) (2190981 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3275831552 :
    ThetaLowerSegment 3275831552 3275962624 (327573909997733 / 100000)
      (327587158865887 / 100000) := by
  exact
    packedTile65536 3275831552 3275962624 14 6047 57234 32 _ _ (1095491 / 50000) (438197 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3275962624 :
    ThetaLowerSegment 3275962624 3276093696 (327587158865887 / 100000)
      (65520071034913 / 20000) := by
  exact
    packedTile65536 3275962624 3276093696 14 6023 57236 32 _ _ (1095493 / 50000) (2190989 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3276093696 :
    ThetaLowerSegment 3276093696 3276224768 (65520071034913 / 20000) (65522679627607 / 20000) := by
  exact
    packedTile65536 3276093696 3276224768 14 5953 57237 32 _ _ (219099 / 10000) (2190993 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3276224768 :
    ThetaLowerSegment 3276224768 3276355840 (65522679627607 / 20000)
      (327626493709173 / 100000) := by
  exact
    packedTile65536 3276224768 3276355840 14 5977 57238 32 _ _ (1095497 / 50000) (2190997 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3276355840 :
    ThetaLowerSegment 3276355840 3276486912 (327626493709173 / 100000)
      (327639644079169 / 100000) := by
  exact
    packedTile65536 3276355840 3276486912 14 6002 57239 32 _ _ (1095499 / 50000) (2191001 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3276486912 :
    ThetaLowerSegment 3276486912 3276617984 (327639644079169 / 100000)
      (327652925933293 / 100000) := by
  exact
    packedTile65536 3276486912 3276617984 14 6062 57240 32 _ _ (1095501 / 50000) (438201 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3276617984 :
    ThetaLowerSegment 3276617984 3276749056 (327652925933293 / 100000)
      (327665931744909 / 100000) := by
  exact
    packedTile65536 3276617984 3276749056 14 5936 57241 32 _ _ (1095503 / 50000) (2191009 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3276749056 :
    ThetaLowerSegment 3276749056 3276880128 (327665931744909 / 100000)
      (327679040557739 / 100000) := by
  exact
    packedTile65536 3276749056 3276880128 14 5983 57242 32 _ _ (219101 / 10000) (2191013 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3276880128 :
    ThetaLowerSegment 3276880128 3277011200 (327679040557739 / 100000)
      (327692105574221 / 100000) := by
  exact
    packedTile65536 3276880128 3277011200 14 5963 57244 32 _ _ (1095507 / 50000) (2191017 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3277011200 :
    ThetaLowerSegment 3277011200 3277142272 (327692105574221 / 100000)
      (327705168423537 / 100000) := by
  exact
    packedTile65536 3277011200 3277142272 14 5962 57245 32 _ _ (1095509 / 50000) (2191021 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3277142272 :
    ThetaLowerSegment 3277142272 3277273344 (327705168423537 / 100000)
      (327718397814373 / 100000) := by
  exact
    packedTile65536 3277142272 3277273344 14 6038 57246 32 _ _ (1095511 / 50000) (87641 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3277273344 :
    ThetaLowerSegment 3277273344 3277404416 (327718397814373 / 100000)
      (327731574644737 / 100000) := by
  exact
    packedTile65536 3277273344 3277404416 14 6014 57247 32 _ _ (1095513 / 50000) (2191029 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3277404416 :
    ThetaLowerSegment 3277404416 3277535488 (327731574644737 / 100000)
      (327744655093837 / 100000) := by
  exact
    packedTile65536 3277404416 3277535488 14 5970 57248 32 _ _ (219103 / 10000) (2191033 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3277535488 :
    ThetaLowerSegment 3277535488 3277666560 (327744655093837 / 100000)
      (327757672026831 / 100000) := by
  exact
    packedTile65536 3277535488 3277666560 14 5941 57249 32 _ _ (1095517 / 50000) (2191037 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3277666560 :
    ThetaLowerSegment 3277666560 3277797632 (327757672026831 / 100000)
      (327770789771337 / 100000) := by
  exact
    packedTile65536 3277666560 3277797632 14 5987 57250 32 _ _ (1095519 / 50000) (2191041 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3277797632 :
    ThetaLowerSegment 3277797632 3277928704 (327770789771337 / 100000)
      (327784124452949 / 100000) := by
  exact
    packedTile65536 3277797632 3277928704 14 6086 57252 32 _ _ (1095521 / 50000) (438209 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3277928704 :
    ThetaLowerSegment 3277928704 3278059776 (327784124452949 / 100000) (524475303633 / 160) := by
  exact
    packedTile65536 3277928704 3278059776 14 5906 57253 32 _ _ (1095523 / 50000) (2191049 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3278059776 :
    ThetaLowerSegment 3278059776 3278190848 (524475303633 / 160) (13112410809159 / 4000) := by
  exact
    packedTile65536 3278059776 3278190848 14 6027 57254 32 _ _ (43821 / 2000) (2191053 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3278190848 :
    ThetaLowerSegment 3278190848 3278321920 (13112410809159 / 4000) (327823335483977 / 100000) := by
  exact
    packedTile65536 3278190848 3278321920 14 5963 57255 32 _ _ (1095527 / 50000) (2191057 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3278321920 :
    ThetaLowerSegment 3278321920 3278452992 (327823335483977 / 100000)
      (327836591384877 / 100000) := by
  exact
    packedTile65536 3278321920 3278452992 14 6050 57256 32 _ _ (1095529 / 50000) (2191061 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3278452992 :
    ThetaLowerSegment 3278452992 3278584064 (327836591384877 / 100000)
      (327849654496521 / 100000) := by
  exact
    packedTile65536 3278452992 3278584064 14 5962 57257 32 _ _ (1095531 / 50000) (438213 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3278584064 :
    ThetaLowerSegment 3278584064 3278715136 (327849654496521 / 100000)
      (327862735160541 / 100000) := by
  exact
    packedTile65536 3278584064 3278715136 14 5970 57258 32 _ _ (1095533 / 50000) (2191069 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3278715136 :
    ThetaLowerSegment 3278715136 3278846208 (327862735160541 / 100000)
      (327875782982391 / 100000) := by
  exact
    packedTile65536 3278715136 3278846208 14 5955 57260 32 _ _ (219107 / 10000) (2191073 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3278846208 :
    ThetaLowerSegment 3278846208 3278977280 (327875782982391 / 100000)
      (327888846165579 / 100000) := by
  exact
    packedTile65536 3278846208 3278977280 14 5962 57261 32 _ _ (1095537 / 50000) (2191077 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3278977280 :
    ThetaLowerSegment 3278977280 3279108352 (327888846165579 / 100000)
      (327901867742133 / 100000) := by
  exact
    packedTile65536 3278977280 3279108352 14 5943 57262 32 _ _ (1095539 / 50000) (2191081 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3279108352 :
    ThetaLowerSegment 3279108352 3279239424 (327901867742133 / 100000)
      (327915007660887 / 100000) := by
  exact
    packedTile65536 3279108352 3279239424 14 5997 57263 32 _ _ (1095541 / 50000) (438217 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3279239424 :
    ThetaLowerSegment 3279239424 3279370496 (327915007660887 / 100000)
      (327927994227609 / 100000) := by
  exact
    packedTile65536 3279239424 3279370496 14 5927 57264 32 _ _ (1095543 / 50000) (2191089 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3279370496 :
    ThetaLowerSegment 3279370496 3279501568 (327927994227609 / 100000)
      (327941375214239 / 100000) := by
  exact
    packedTile65536 3279370496 3279501568 14 6107 57265 32 _ _ (219109 / 10000) (2191093 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3279501568 :
    ThetaLowerSegment 3279501568 3279632640 (327941375214239 / 100000)
      (327954615995281 / 100000) := by
  exact
    packedTile65536 3279501568 3279632640 14 6043 57266 32 _ _ (1095547 / 50000) (2191097 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3279632640 :
    ThetaLowerSegment 3279632640 3279763712 (327954615995281 / 100000)
      (327967624544107 / 100000) := by
  exact
    packedTile65536 3279632640 3279763712 14 5937 57268 32 _ _ (1095549 / 50000) (2191101 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3279763712 :
    ThetaLowerSegment 3279763712 3279894784 (327967624544107 / 100000)
      (327980749245087 / 100000) := by
  exact
    packedTile65536 3279763712 3279894784 14 5990 57269 32 _ _ (1095551 / 50000) (438221 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3279894784 :
    ThetaLowerSegment 3279894784 3280025856 (327980749245087 / 100000)
      (65598752006503 / 20000) := by
  exact
    packedTile65536 3279894784 3280025856 14 5938 57270 32 _ _ (1095553 / 50000) (2191109 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3280025856 :
    ThetaLowerSegment 3280025856 3280156928 (65598752006503 / 20000) (65601387035389 / 20000) := by
  exact
    packedTile65536 3280025856 3280156928 14 6013 57271 32 _ _ (219111 / 10000) (2191113 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3280156928 :
    ThetaLowerSegment 3280156928 3280288000 (65601387035389 / 20000) (65603972549909 / 20000) := by
  exact
    packedTile65536 3280156928 3280288000 14 5900 57272 32 _ _ (1095557 / 50000) (2191117 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3280288000 :
    ThetaLowerSegment 3280288000 3280419072 (65603972549909 / 20000)
      (328032849505931 / 100000) := by
  exact
    packedTile65536 3280288000 3280419072 14 5927 57273 32 _ _ (1095559 / 50000) (2191121 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3280419072 :
    ThetaLowerSegment 3280419072 3280550144 (328032849505931 / 100000)
      (328046002811297 / 100000) := by
  exact
    packedTile65536 3280419072 3280550144 14 6003 57274 32 _ _ (1095561 / 50000) (17529 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3280550144 :
    ThetaLowerSegment 3280550144 3280681216 (328046002811297 / 100000)
      (328059256932471 / 100000) := by
  exact
    packedTile65536 3280550144 3280681216 14 6049 57276 32 _ _ (1095563 / 50000) (2191129 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3280681216 :
    ThetaLowerSegment 3280681216 3280812288 (328059256932471 / 100000)
      (328072331405181 / 100000) := by
  exact
    packedTile65536 3280681216 3280812288 14 5967 57277 32 _ _ (219113 / 10000) (2191133 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3280812288 :
    ThetaLowerSegment 3280812288 3280943360 (328072331405181 / 100000)
      (328085506693923 / 100000) := by
  exact
    packedTile65536 3280812288 3280943360 14 6013 57278 32 _ _ (1095567 / 50000) (2191137 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3280943360 :
    ThetaLowerSegment 3280943360 3281074432 (328085506693923 / 100000)
      (328098631610543 / 100000) := by
  exact
    packedTile65536 3280943360 3281074432 14 5990 57279 32 _ _ (1095569 / 50000) (2191141 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3281074432 :
    ThetaLowerSegment 3281074432 3281205504 (328098631610543 / 100000)
      (328111622891461 / 100000) := by
  exact
    packedTile65536 3281074432 3281205504 14 5929 57280 32 _ _ (1095571 / 50000) (438229 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3281205504 :
    ThetaLowerSegment 3281205504 3281336576 (328111622891461 / 100000)
      (328124519976817 / 100000) := by
  exact
    packedTile65536 3281205504 3281336576 14 5886 57281 32 _ _ (1095573 / 50000) (2191149 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3281336576 :
    ThetaLowerSegment 3281336576 3281467648 (328124519976817 / 100000)
      (328137883800667 / 100000) := by
  exact
    packedTile65536 3281336576 3281467648 14 6099 57282 32 _ _ (43823 / 2000) (2191153 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3281467648 :
    ThetaLowerSegment 3281467648 3281598720 (328137883800667 / 100000)
      (65630171962931 / 20000) := by
  exact
    packedTile65536 3281467648 3281598720 14 5922 57284 32 _ _ (1095577 / 50000) (2191157 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3281598720 :
    ThetaLowerSegment 3281598720 3281729792 (65630171962931 / 20000)
      (328164098791291 / 100000) := by
  exact
    packedTile65536 3281598720 3281729792 14 6042 57285 32 _ _ (1095579 / 50000) (2191161 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3281729792 :
    ThetaLowerSegment 3281729792 3281860864 (328164098791291 / 100000)
      (328177153734487 / 100000) := by
  exact
    packedTile65536 3281729792 3281860864 14 5958 57286 32 _ _ (1095581 / 50000) (438233 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3281860864 :
    ThetaLowerSegment 3281860864 3281991936 (328177153734487 / 100000)
      (328190451920941 / 100000) := by
  exact
    packedTile65536 3281860864 3281991936 14 6069 57287 32 _ _ (1095583 / 50000) (2191169 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3281991936 :
    ThetaLowerSegment 3281991936 3282123008 (328190451920941 / 100000)
      (328203544161691 / 100000) := by
  exact
    packedTile65536 3281991936 3282123008 14 5975 57288 32 _ _ (219117 / 10000) (2191173 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3282123008 :
    ThetaLowerSegment 3282123008 3282254080 (328203544161691 / 100000)
      (65643288282371 / 20000) := by
  exact
    packedTile65536 3282123008 3282254080 14 5886 57289 32 _ _ (1095587 / 50000) (2191177 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3282254080 :
    ThetaLowerSegment 3282254080 3282385152 (65643288282371 / 20000)
      (328229308009071 / 100000) := by
  exact
    packedTile65536 3282254080 3282385152 14 5872 57290 32 _ _ (1095589 / 50000) (2191181 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3282385152 :
    ThetaLowerSegment 3282385152 3282516224 (328229308009071 / 100000)
      (328242487968801 / 100000) := by
  exact
    packedTile65536 3282385152 3282516224 14 6015 57292 32 _ _ (1095591 / 50000) (438237 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3282516224 :
    ThetaLowerSegment 3282516224 3282647296 (328242487968801 / 100000)
      (328255551819733 / 100000) := by
  exact
    packedTile65536 3282516224 3282647296 14 5962 57293 32 _ _ (1095593 / 50000) (2191189 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3282647296 :
    ThetaLowerSegment 3282647296 3282778368 (328255551819733 / 100000)
      (328268738401153 / 100000) := by
  exact
    packedTile65536 3282647296 3282778368 14 6018 57294 32 _ _ (219119 / 10000) (2191193 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3282778368 :
    ThetaLowerSegment 3282778368 3282909440 (328268738401153 / 100000)
      (328281850506049 / 100000) := by
  exact
    packedTile65536 3282778368 3282909440 14 5984 57295 32 _ _ (1095597 / 50000) (2191197 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3282909440 :
    ThetaLowerSegment 3282909440 3283040512 (328281850506049 / 100000)
      (328295126974731 / 100000) := by
  exact
    packedTile65536 3282909440 3283040512 14 6059 57296 32 _ _ (1095599 / 50000) (2191201 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3283040512 :
    ThetaLowerSegment 3283040512 3283171584 (328295126974731 / 100000)
      (328308261039519 / 100000) := by
  exact
    packedTile65536 3283040512 3283171584 14 5994 57297 32 _ _ (1095601 / 50000) (438241 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3283171584 :
    ThetaLowerSegment 3283171584 3283302656 (328308261039519 / 100000)
      (328321327200897 / 100000) := by
  exact
    packedTile65536 3283171584 3283302656 14 5963 57298 32 _ _ (1095603 / 50000) (2191209 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3283302656 :
    ThetaLowerSegment 3283302656 3283433728 (328321327200897 / 100000)
      (328334371474027 / 100000) := by
  exact
    packedTile65536 3283302656 3283433728 14 5953 57300 32 _ _ (219121 / 10000) (2191213 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3283433728 :
    ThetaLowerSegment 3283433728 3283564800 (328334371474027 / 100000)
      (328347448639179 / 100000) := by
  exact
    packedTile65536 3283433728 3283564800 14 5968 57301 32 _ _ (1095607 / 50000) (2191217 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3283564800 :
    ThetaLowerSegment 3283564800 3283695872 (328347448639179 / 100000)
      (328360541166729 / 100000) := by
  exact
    packedTile65536 3283564800 3283695872 14 5975 57302 32 _ _ (1095609 / 50000) (2191221 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3283695872 :
    ThetaLowerSegment 3283695872 3283826944 (328360541166729 / 100000)
      (328373743279279 / 100000) := by
  exact
    packedTile65536 3283695872 3283826944 14 6025 57303 32 _ _ (1095611 / 50000) (87649 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3283826944 :
    ThetaLowerSegment 3283826944 3283958016 (328373743279279 / 100000)
      (328386833663403 / 100000) := by
  exact
    packedTile65536 3283826944 3283958016 14 5974 57304 32 _ _ (1095613 / 50000) (2191229 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3283958016 :
    ThetaLowerSegment 3283958016 3284089088 (328386833663403 / 100000)
      (328399764111633 / 100000) := by
  exact
    packedTile65536 3283958016 3284089088 14 5901 57305 32 _ _ (219123 / 10000) (2191233 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3284089088 :
    ThetaLowerSegment 3284089088 3284220160 (328399764111633 / 100000)
      (65682590191569 / 20000) := by
  exact
    packedTile65536 3284089088 3284220160 14 6018 57306 32 _ _ (1095617 / 50000) (2191237 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3284220160 :
    ThetaLowerSegment 3284220160 3284351232 (65682590191569 / 20000)
      (328426118106987 / 100000) := by
  exact
    packedTile65536 3284220160 3284351232 14 6009 57308 32 _ _ (1095619 / 50000) (2191241 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3284351232 :
    ThetaLowerSegment 3284351232 3284482304 (328426118106987 / 100000)
      (328439149423161 / 100000) := by
  exact
    packedTile65536 3284351232 3284482304 14 5947 57309 32 _ _ (1095621 / 50000) (438249 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3284482304 :
    ThetaLowerSegment 3284482304 3284613376 (328439149423161 / 100000)
      (328452399887723 / 100000) := by
  exact
    packedTile65536 3284482304 3284613376 14 6047 57310 32 _ _ (1095623 / 50000) (2191249 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3284613376 :
    ThetaLowerSegment 3284613376 3284744448 (328452399887723 / 100000)
      (328465591212723 / 100000) := by
  exact
    packedTile65536 3284613376 3284744448 14 6020 57311 32 _ _ (1753 / 80) (2191253 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3284744448 :
    ThetaLowerSegment 3284744448 3284875520 (328465591212723 / 100000)
      (65695770974637 / 20000) := by
  exact
    packedTile65536 3284744448 3284875520 14 6053 57312 32 _ _ (1095627 / 50000) (2191257 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3284875520 :
    ThetaLowerSegment 3284875520 3285006592 (65695770974637 / 20000)
      (328491930109671 / 100000) := by
  exact
    packedTile65536 3284875520 3285006592 14 5967 57313 32 _ _ (1095629 / 50000) (2191261 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3285006592 :
    ThetaLowerSegment 3285006592 3285137664 (328491930109671 / 100000)
      (328505025091383 / 100000) := by
  exact
    packedTile65536 3285006592 3285137664 14 5976 57314 32 _ _ (1095631 / 50000) (438253 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3285137664 :
    ThetaLowerSegment 3285137664 3285268736 (328505025091383 / 100000)
      (65703648561579 / 20000) := by
  exact
    packedTile65536 3285137664 3285268736 14 6032 57316 32 _ _ (1095633 / 50000) (2191269 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3285268736 :
    ThetaLowerSegment 3285268736 3285399808 (65703648561579 / 20000) (13141250270417 / 4000) := by
  exact
    packedTile65536 3285268736 3285399808 14 5939 57317 32 _ _ (219127 / 10000) (2191273 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3285399808 :
    ThetaLowerSegment 3285399808 3285530880 (13141250270417 / 4000) (328544367152767 / 100000) := by
  exact
    packedTile65536 3285399808 3285530880 14 5983 57318 32 _ _ (1095637 / 50000) (2191277 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3285530880 :
    ThetaLowerSegment 3285530880 3285661952 (328544367152767 / 100000) (13142303748271 / 4000) := by
  exact
    packedTile65536 3285530880 3285661952 14 6036 57319 32 _ _ (1095639 / 50000) (2191281 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3285661952 :
    ThetaLowerSegment 3285661952 3285793024 (13142303748271 / 4000) (328570546374677 / 100000) := by
  exact
    packedTile65536 3285661952 3285793024 14 5911 57320 32 _ _ (1095641 / 50000) (438257 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3285793024 :
    ThetaLowerSegment 3285793024 3285924096 (328570546374677 / 100000)
      (328583768594401 / 100000) := by
  exact
    packedTile65536 3285793024 3285924096 14 6034 57321 32 _ _ (1095643 / 50000) (2191289 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3285924096 :
    ThetaLowerSegment 3285924096 3286055168 (328583768594401 / 100000)
      (328596907569241 / 100000) := by
  exact
    packedTile65536 3285924096 3286055168 14 5996 57322 32 _ _ (219129 / 10000) (2191293 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3286055168 :
    ThetaLowerSegment 3286055168 3286186240 (328596907569241 / 100000)
      (65722022461377 / 20000) := by
  exact
    packedTile65536 3286055168 3286186240 14 6026 57324 32 _ _ (1095647 / 50000) (2191297 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3286186240 :
    ThetaLowerSegment 3286186240 3286317312 (65722022461377 / 20000)
      (328623089173641 / 100000) := by
  exact
    packedTile65536 3286186240 3286317312 14 5922 57325 32 _ _ (1095649 / 50000) (2191301 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3286317312 :
    ThetaLowerSegment 3286317312 3286448384 (328623089173641 / 100000)
      (328636085785803 / 100000) := by
  exact
    packedTile65536 3286317312 3286448384 14 5931 57326 32 _ _ (1095651 / 50000) (438261 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3286448384 :
    ThetaLowerSegment 3286448384 3286579456 (328636085785803 / 100000)
      (328649014491203 / 100000) := by
  exact
    packedTile65536 3286448384 3286579456 14 5900 57327 32 _ _ (1095653 / 50000) (2191309 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3286579456 :
    ThetaLowerSegment 3286579456 3286710528 (328649014491203 / 100000)
      (328662122907623 / 100000) := by
  exact
    packedTile65536 3286579456 3286710528 14 5982 57328 32 _ _ (219131 / 10000) (2191313 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3286710528 :
    ThetaLowerSegment 3286710528 3286841600 (328662122907623 / 100000)
      (328675161225923 / 100000) := by
  exact
    packedTile65536 3286710528 3286841600 14 5950 57329 32 _ _ (1095657 / 50000) (2191317 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3286841600 :
    ThetaLowerSegment 3286841600 3286972672 (328675161225923 / 100000)
      (328688335429739 / 100000) := by
  exact
    packedTile65536 3286841600 3286972672 14 6012 57330 32 _ _ (1095659 / 50000) (2191321 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3286972672 :
    ThetaLowerSegment 3286972672 3287103744 (328688335429739 / 100000)
      (328701630180313 / 100000) := by
  exact
    packedTile65536 3286972672 3287103744 14 6067 57332 32 _ _ (1095661 / 50000) (87653 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3287103744 :
    ThetaLowerSegment 3287103744 3287234816 (328701630180313 / 100000)
      (328714743075097 / 100000) := by
  exact
    packedTile65536 3287103744 3287234816 14 5984 57333 32 _ _ (1095663 / 50000) (2191329 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3287234816 :
    ThetaLowerSegment 3287234816 3287365888 (328714743075097 / 100000)
      (328727834080517 / 100000) := by
  exact
    packedTile65536 3287234816 3287365888 14 5974 57334 32 _ _ (219133 / 10000) (2191333 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3287365888 :
    ThetaLowerSegment 3287365888 3287496960 (328727834080517 / 100000)
      (65748197293437 / 20000) := by
  exact
    packedTile65536 3287365888 3287496960 14 6002 57335 32 _ _ (1095667 / 50000) (2191337 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3287496960 :
    ThetaLowerSegment 3287496960 3287628032 (65748197293437 / 20000)
      (328754252827437 / 100000) := by
  exact
    packedTile65536 3287496960 3287628032 14 6054 57336 32 _ _ (1095669 / 50000) (2191341 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3287628032 :
    ThetaLowerSegment 3287628032 3287759104 (328754252827437 / 100000)
      (328767262824891 / 100000) := by
  exact
    packedTile65536 3287628032 3287759104 14 5937 57337 32 _ _ (1095671 / 50000) (438269 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3287759104 :
    ThetaLowerSegment 3287759104 3287890176 (328767262824891 / 100000)
      (328780237784557 / 100000) := by
  exact
    packedTile65536 3287759104 3287890176 14 5921 57338 32 _ _ (1095673 / 50000) (2191349 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3287890176 :
    ThetaLowerSegment 3287890176 3288021248 (328780237784557 / 100000)
      (328793311378657 / 100000) := by
  exact
    packedTile65536 3287890176 3288021248 14 5966 57340 32 _ _ (43827 / 2000) (2191353 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3288021248 :
    ThetaLowerSegment 3288021248 3288152320 (328793311378657 / 100000)
      (328806382805267 / 100000) := by
  exact
    packedTile65536 3288021248 3288152320 14 5965 57341 32 _ _ (1095677 / 50000) (2191357 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3288152320 :
    ThetaLowerSegment 3288152320 3288283392 (328806382805267 / 100000)
      (328819506848329 / 100000) := by
  exact
    packedTile65536 3288152320 3288283392 14 5989 57342 32 _ _ (1095679 / 50000) (2191361 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3288283392 :
    ThetaLowerSegment 3288283392 3288414464 (328819506848329 / 100000)
      (328832755822981 / 100000) := by
  exact
    packedTile65536 3288283392 3288414464 14 6046 57343 32 _ _ (1095681 / 50000) (438273 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3288414464 :
    ThetaLowerSegment 3288414464 3288545536 (328832755822981 / 100000)
      (328845925932641 / 100000) := by
  exact
    packedTile65536 3288414464 3288545536 14 6010 57344 32 _ _ (1095683 / 50000) (2191369 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3288545536 :
    ThetaLowerSegment 3288545536 3288676608 (328845925932641 / 100000)
      (328858984306471 / 100000) := by
  exact
    packedTile65536 3288545536 3288676608 14 5959 57345 32 _ _ (219137 / 10000) (2191373 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3288676608 :
    ThetaLowerSegment 3288676608 3288807680 (328858984306471 / 100000)
      (328872209248561 / 100000) := by
  exact
    packedTile65536 3288676608 3288807680 14 6035 57346 32 _ _ (1095687 / 50000) (2191377 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3288807680 :
    ThetaLowerSegment 3288807680 3288938752 (328872209248561 / 100000)
      (328885302732111 / 100000) := by
  exact
    packedTile65536 3288807680 3288938752 14 5975 57348 32 _ _ (1095689 / 50000) (2191381 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3288938752 :
    ThetaLowerSegment 3288938752 3289069824 (328885302732111 / 100000)
      (328898216546237 / 100000) := by
  exact
    packedTile65536 3288938752 3289069824 14 5893 57349 32 _ _ (1095691 / 50000) (438277 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3289069824 :
    ThetaLowerSegment 3289069824 3289200896 (328898216546237 / 100000)
      (328911413072729 / 100000) := by
  exact
    packedTile65536 3289069824 3289200896 14 6022 57350 32 _ _ (1095693 / 50000) (2191389 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3289200896 :
    ThetaLowerSegment 3289200896 3289331968 (328911413072729 / 100000)
      (328924491288249 / 100000) := by
  exact
    packedTile65536 3289200896 3289331968 14 5968 57351 32 _ _ (219139 / 10000) (2191393 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3289331968 :
    ThetaLowerSegment 3289331968 3289463040 (328924491288249 / 100000)
      (328937654992007 / 100000) := by
  exact
    packedTile65536 3289331968 3289463040 14 6007 57352 32 _ _ (1095697 / 50000) (2191397 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3289463040 :
    ThetaLowerSegment 3289463040 3289594112 (328937654992007 / 100000)
      (328950825293987 / 100000) := by
  exact
    packedTile65536 3289463040 3289594112 14 6010 57353 32 _ _ (1095699 / 50000) (2191401 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3289594112 :
    ThetaLowerSegment 3289594112 3289725184 (328950825293987 / 100000)
      (328963925495143 / 100000) := by
  exact
    packedTile65536 3289594112 3289725184 14 5978 57354 32 _ _ (1095701 / 50000) (438281 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3289725184 :
    ThetaLowerSegment 3289725184 3289856256 (328963925495143 / 100000)
      (328976968737703 / 100000) := by
  exact
    packedTile65536 3289725184 3289856256 14 5952 57356 32 _ _ (438281 / 20000) (136963 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3289856256 :
    ThetaLowerSegment 3289856256 3289987328 (328976968737703 / 100000)
      (82247505740279 / 25000) := by
  exact
    packedTile65536 3289856256 3289987328 14 5957 57357 32 _ _ (2191409 / 100000) (547853 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3289987328 :
    ThetaLowerSegment 3289987328 3290118400 (82247505740279 / 25000) (164501557231189 / 50000) := by
  exact
    packedTile65536 3289987328 3290118400 14 5974 57358 32 _ _ (2191413 / 100000) (273927 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3290118400 :
    ThetaLowerSegment 3290118400 3290249472 (164501557231189 / 50000) (65803239882657 / 20000) := by
  exact
    packedTile65536 3290118400 3290249472 14 5971 57359 32 _ _ (2191417 / 100000) (109571 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3290249472 :
    ThetaLowerSegment 3290249472 3290380544 (65803239882657 / 20000) (164514604939881 / 50000) := by
  exact
    packedTile65536 3290249472 3290380544 14 5937 57360 32 _ _ (2191421 / 100000) (68482 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3290380544 :
    ThetaLowerSegment 3290380544 3290511616 (164514604939881 / 50000)
      (329042382535437 / 100000) := by
  exact
    packedTile65536 3290380544 3290511616 14 6011 57361 32 _ _ (87657 / 4000) (547857 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3290511616 :
    ThetaLowerSegment 3290511616 3290642688 (329042382535437 / 100000)
      (329055241840809 / 100000) := by
  exact
    packedTile65536 3290511616 3290642688 14 5868 57362 32 _ _ (2191429 / 100000) (273929 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3290642688 :
    ThetaLowerSegment 3290642688 3290773760 (329055241840809 / 100000)
      (164534121806399 / 50000) := by
  exact
    packedTile65536 3290642688 3290773760 14 5933 57364 32 _ _ (2191433 / 100000) (547859 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3290773760 :
    ThetaLowerSegment 3290773760 3290904832 (164534121806399 / 50000)
      (164540661054407 / 50000) := by
  exact
    packedTile65536 3290773760 3290904832 14 5968 57365 32 _ _ (2191437 / 100000) (27393 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3290904832 :
    ThetaLowerSegment 3290904832 3291035904 (164540661054407 / 50000)
      (164547182782823 / 50000) := by
  exact
    packedTile65536 3290904832 3291035904 14 5952 57366 32 _ _ (2191441 / 100000) (547861 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3291035904 :
    ThetaLowerSegment 3291035904 3291166976 (164547182782823 / 50000)
      (329107569021771 / 100000) := by
  exact
    packedTile65536 3291035904 3291166976 14 6025 57367 32 _ _ (438289 / 20000) (273931 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3291166976 :
    ThetaLowerSegment 3291166976 3291298048 (329107569021771 / 100000)
      (329120761544751 / 100000) := by
  exact
    packedTile65536 3291166976 3291298048 14 6020 57368 32 _ _ (2191449 / 100000) (547863 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3291298048 :
    ThetaLowerSegment 3291298048 3291429120 (329120761544751 / 100000)
      (329133791924289 / 100000) := by
  exact
    packedTile65536 3291298048 3291429120 14 5946 57369 32 _ _ (2191453 / 100000) (68483 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3291429120 :
    ThetaLowerSegment 3291429120 3291560192 (329133791924289 / 100000)
      (82286745575993 / 25000) := by
  exact
    packedTile65536 3291429120 3291560192 14 6019 57370 32 _ _ (2191457 / 100000) (109573 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3291560192 :
    ThetaLowerSegment 3291560192 3291691264 (82286745575993 / 25000) (82290050299181 / 25000) := by
  exact
    packedTile65536 3291560192 3291691264 14 6032 57372 32 _ _ (2191461 / 100000) (273933 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3291691264 :
    ThetaLowerSegment 3291691264 3291822336 (82290050299181 / 25000) (164586664036037 / 50000) := by
  exact
    packedTile65536 3291691264 3291822336 14 5990 57373 32 _ _ (438293 / 20000) (547867 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3291822336 :
    ThetaLowerSegment 3291822336 3291953408 (164586664036037 / 50000)
      (164593216528347 / 50000) := by
  exact
    packedTile65536 3291822336 3291953408 14 5980 57374 32 _ _ (2191469 / 100000) (136967 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3291953408 :
    ThetaLowerSegment 3291953408 3292084480 (164593216528347 / 50000) (16459972739463 / 5000) := by
  exact
    packedTile65536 3291953408 3292084480 14 5942 57375 32 _ _ (2191473 / 100000) (547869 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3292084480 :
    ThetaLowerSegment 3292084480 3292215552 (16459972739463 / 5000) (164606264570521 / 50000) := by
  exact
    packedTile65536 3292084480 3292215552 14 5966 57376 32 _ _ (2191477 / 100000) (54787 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3292215552 :
    ThetaLowerSegment 3292215552 3292346624 (164606264570521 / 50000) (65845128154373 / 20000) := by
  exact
    packedTile65536 3292215552 3292346624 14 5983 57377 32 _ _ (2191481 / 100000) (547871 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3292346624 :
    ThetaLowerSegment 3292346624 3292477696 (65845128154373 / 20000) (13169545977073 / 4000) := by
  exact
    packedTile65536 3292346624 3292477696 14 5936 57378 32 _ _ (438297 / 20000) (68484 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3292477696 :
    ThetaLowerSegment 3292477696 3292608768 (13169545977073 / 4000) (164625979169761 / 50000) := by
  exact
    packedTile65536 3292477696 3292608768 14 6073 57380 32 _ _ (2191489 / 100000) (547873 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3292608768 :
    ThetaLowerSegment 3292608768 3292739840 (164625979169761 / 50000)
      (164632518584873 / 50000) := by
  exact
    packedTile65536 3292608768 3292739840 14 5968 57381 32 _ _ (2191493 / 100000) (273937 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3292739840 :
    ThetaLowerSegment 3292739840 3292870912 (164632518584873 / 50000) (20579886360547 / 6250) := by
  exact
    packedTile65536 3292739840 3292870912 14 5998 57382 32 _ _ (2191497 / 100000) (4383 / 200)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3292870912 :
    ThetaLowerSegment 3292870912 3293001984 (20579886360547 / 6250) (41161414155343 / 12500) := by
  exact
    packedTile65536 3292870912 3293001984 14 5992 57383 32 _ _ (2191501 / 100000) (136969 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3293001984 :
    ThetaLowerSegment 3293001984 3293133056 (41161414155343 / 12500) (10290770472662 / 3125) := by
  exact
    packedTile65536 3293001984 3293133056 14 6088 57384 32 _ _ (438301 / 20000) (547877 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3293133056 :
    ThetaLowerSegment 3293133056 3293264128 (10290770472662 / 3125) (65863551631499 / 20000) := by
  exact
    packedTile65536 3293133056 3293264128 14 5979 57385 32 _ _ (2191509 / 100000) (273939 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3293264128 :
    ThetaLowerSegment 3293264128 3293395200 (65863551631499 / 20000) (164665443755939 / 50000) := by
  exact
    packedTile65536 3293264128 3293395200 14 5991 57386 32 _ _ (2191513 / 100000) (547879 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3293395200 :
    ThetaLowerSegment 3293395200 3293526272 (164665443755939 / 50000)
      (164671921880191 / 50000) := by
  exact
    packedTile65536 3293395200 3293526272 14 5912 57388 32 _ _ (2191517 / 100000) (13697 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3293526272 :
    ThetaLowerSegment 3293526272 3293657344 (164671921880191 / 50000)
      (329357008227029 / 100000) := by
  exact
    packedTile65536 3293526272 3293657344 14 6007 57389 32 _ _ (2191521 / 100000) (547881 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3293657344 :
    ThetaLowerSegment 3293657344 3293788416 (329357008227029 / 100000)
      (329370012736379 / 100000) := by
  exact
    packedTile65536 3293657344 3293788416 14 5934 57390 32 _ _ (87661 / 4000) (273941 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3293788416 :
    ThetaLowerSegment 3293788416 3293919488 (329370012736379 / 100000)
      (32938320354943 / 10000) := by
  exact
    packedTile65536 3293788416 3293919488 14 6019 57391 32 _ _ (2191529 / 100000) (547883 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3293919488 :
    ThetaLowerSegment 3293919488 3294050560 (32938320354943 / 10000)
      (329396306725237 / 100000) := by
  exact
    packedTile65536 3293919488 3294050560 14 5979 57392 32 _ _ (2191533 / 100000) (136971 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3294050560 :
    ThetaLowerSegment 3294050560 3294181632 (329396306725237 / 100000)
      (82352359055851 / 25000) := by
  exact
    packedTile65536 3294050560 3294181632 14 5991 57393 32 _ _ (2191537 / 100000) (109577 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3294181632 :
    ThetaLowerSegment 3294181632 3294312704 (82352359055851 / 25000)
      (329422583277863 / 100000) := by
  exact
    packedTile65536 3294181632 3294312704 14 5999 57394 32 _ _ (2191541 / 100000) (273943 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3294312704 :
    ThetaLowerSegment 3294312704 3294443776 (329422583277863 / 100000)
      (329435622970613 / 100000) := by
  exact
    packedTile65536 3294312704 3294443776 14 5950 57396 32 _ _ (438309 / 20000) (547887 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3294443776 :
    ThetaLowerSegment 3294443776 3294574848 (329435622970613 / 100000) (10295271325347 / 3125) := by
  exact
    packedTile65536 3294443776 3294574848 14 5959 57397 32 _ _ (2191549 / 100000) (68486 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3294574848 :
    ThetaLowerSegment 3294574848 3294705920 (10295271325347 / 3125) (82365403143451 / 25000) := by
  exact
    packedTile65536 3294574848 3294705920 14 5900 57398 32 _ _ (2191553 / 100000) (547889 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3294705920 :
    ThetaLowerSegment 3294705920 3294836992 (82365403143451 / 25000) (82368659797153 / 25000) := by
  exact
    packedTile65536 3294705920 3294836992 14 5944 57399 32 _ _ (2191557 / 100000) (54789 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3294836992 :
    ThetaLowerSegment 3294836992 3294968064 (82368659797153 / 25000) (3294878060871 / 1000) := by
  exact
    packedTile65536 3294836992 3294968064 14 6008 57400 32 _ _ (2191561 / 100000) (547891 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3294968064 :
    ThetaLowerSegment 3294968064 3295099136 (3294878060871 / 1000) (65900173124587 / 20000) := by
  exact
    packedTile65536 3294968064 3295099136 14 5959 57401 32 _ _ (438313 / 20000) (136973 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3295099136 :
    ThetaLowerSegment 3295099136 3295230208 (65900173124587 / 20000)
      (329513852860829 / 100000) := by
  exact
    packedTile65536 3295099136 3295230208 14 5926 57402 32 _ _ (2191569 / 100000) (547893 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3295230208 :
    ThetaLowerSegment 3295230208 3295361280 (329513852860829 / 100000)
      (164763537310369 / 50000) := by
  exact
    packedTile65536 3295230208 3295361280 14 6033 57404 32 _ _ (2191573 / 100000) (273947 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3295361280 :
    ThetaLowerSegment 3295361280 3295492352 (164763537310369 / 50000)
      (329539888771457 / 100000) := by
  exact
    packedTile65536 3295361280 3295492352 14 5847 57405 32 _ _ (2191577 / 100000) (109579 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3295492352 :
    ThetaLowerSegment 3295492352 3295623424 (329539888771457 / 100000)
      (329553007575323 / 100000) := by
  exact
    packedTile65536 3295492352 3295623424 14 5986 57406 32 _ _ (2191581 / 100000) (68487 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3295623424 :
    ThetaLowerSegment 3295623424 3295754496 (329553007575323 / 100000)
      (164783121278569 / 50000) := by
  exact
    packedTile65536 3295623424 3295754496 14 6039 57407 32 _ _ (438317 / 20000) (547897 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3295754496 :
    ThetaLowerSegment 3295754496 3295885568 (164783121278569 / 50000) (65915884116359 / 20000) := by
  exact
    packedTile65536 3295754496 3295885568 14 6013 57408 32 _ _ (2191589 / 100000) (273949 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3295885568 :
    ThetaLowerSegment 3295885568 3296016640 (65915884116359 / 20000) (32959255918183 / 10000) := by
  exact
    packedTile65536 3295885568 3296016640 14 5995 57409 32 _ _ (2191593 / 100000) (547899 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3296016640 :
    ThetaLowerSegment 3296016640 3296147712 (32959255918183 / 10000)
      (329605649590711 / 100000) := by
  exact
    packedTile65536 3296016640 3296147712 14 5973 57410 32 _ _ (2191597 / 100000) (5479 / 250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3296147712 :
    ThetaLowerSegment 3296147712 3296278784 (329605649590711 / 100000)
      (329618750981489 / 100000) := by
  exact
    packedTile65536 3296147712 3296278784 14 5978 57412 32 _ _ (2191601 / 100000) (547901 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3296278784 :
    ThetaLowerSegment 3296278784 3296409856 (329618750981489 / 100000)
      (329631913761119 / 100000) := by
  exact
    packedTile65536 3296278784 3296409856 14 6006 57413 32 _ _ (438321 / 20000) (273951 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3296409856 :
    ThetaLowerSegment 3296409856 3296540928 (329631913761119 / 100000)
      (329644986702839 / 100000) := by
  exact
    packedTile65536 3296409856 3296540928 14 5965 57414 32 _ _ (273951 / 12500) (2191611 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3296540928 :
    ThetaLowerSegment 3296540928 3296672000 (329644986702839 / 100000)
      (329658171440631 / 100000) := by
  exact
    packedTile65536 3296540928 3296672000 14 6016 57415 32 _ _ (547903 / 25000) (438323 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3296672000 :
    ThetaLowerSegment 3296672000 3296803072 (329658171440631 / 100000)
      (329671367160567 / 100000) := by
  exact
    packedTile65536 3296672000 3296803072 14 6021 57416 32 _ _ (68488 / 3125) (2191619 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3296803072 :
    ThetaLowerSegment 3296803072 3296934144 (329671367160567 / 100000)
      (329684381000127 / 100000) := by
  exact
    packedTile65536 3296803072 3296934144 14 5938 57417 32 _ _ (109581 / 5000) (2191623 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3296934144 :
    ThetaLowerSegment 3296934144 3297065216 (329684381000127 / 100000)
      (65939493875731 / 20000) := by
  exact
    packedTile65536 3296934144 3297065216 14 5972 57418 32 _ _ (273953 / 12500) (2191627 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3297065216 :
    ThetaLowerSegment 3297065216 3297196288 (65939493875731 / 20000)
      (329710577505723 / 100000) := by
  exact
    packedTile65536 3297065216 3297196288 14 5981 57420 32 _ _ (547907 / 25000) (2191631 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3297196288 :
    ThetaLowerSegment 3297196288 3297327360 (329710577505723 / 100000)
      (329723665932027 / 100000) := by
  exact
    packedTile65536 3297196288 3297327360 14 5972 57421 32 _ _ (136977 / 6250) (438327 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3297327360 :
    ThetaLowerSegment 3297327360 3297458432 (329723665932027 / 100000)
      (329736988887271 / 100000) := by
  exact
    packedTile65536 3297327360 3297458432 14 6079 57422 32 _ _ (547909 / 25000) (2191639 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3297458432 :
    ThetaLowerSegment 3297458432 3297589504 (329736988887271 / 100000)
      (329749871347191 / 100000) := by
  exact
    packedTile65536 3297458432 3297589504 14 5878 57423 32 _ _ (54791 / 2500) (2191643 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3297589504 :
    ThetaLowerSegment 3297589504 3297720576 (329749871347191 / 100000)
      (329763205309287 / 100000) := by
  exact
    packedTile65536 3297589504 3297720576 14 6084 57424 32 _ _ (547911 / 25000) (2191647 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3297720576 :
    ThetaLowerSegment 3297720576 3297851648 (329763205309287 / 100000)
      (65955260519547 / 20000) := by
  exact
    packedTile65536 3297720576 3297851648 14 5976 57425 32 _ _ (68489 / 3125) (2191651 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3297851648 :
    ThetaLowerSegment 3297851648 3297982720 (65955260519547 / 20000)
      (329789373610263 / 100000) := by
  exact
    packedTile65536 3297851648 3297982720 14 5964 57426 32 _ _ (547913 / 25000) (438331 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3297982720 :
    ThetaLowerSegment 3297982720 3298113792 (329789373610263 / 100000)
      (329802519162951 / 100000) := by
  exact
    packedTile65536 3297982720 3298113792 14 5998 57428 32 _ _ (273957 / 12500) (2191659 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3298113792 :
    ThetaLowerSegment 3298113792 3298244864 (329802519162951 / 100000)
      (329815502556791 / 100000) := by
  exact
    packedTile65536 3298113792 3298244864 14 5924 57429 32 _ _ (109583 / 5000) (2191663 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3298244864 :
    ThetaLowerSegment 3298244864 3298375936 (329815502556791 / 100000)
      (329828624049159 / 100000) := by
  exact
    packedTile65536 3298244864 3298375936 14 5987 57430 32 _ _ (136979 / 6250) (2191667 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3298375936 :
    ThetaLowerSegment 3298375936 3298507008 (329828624049159 / 100000) (13193676397623 / 4000) := by
  exact
    packedTile65536 3298375936 3298507008 14 6062 57431 32 _ _ (547917 / 25000) (2191671 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3298507008 :
    ThetaLowerSegment 3298507008 3298638080 (13193676397623 / 4000) (329855000797431 / 100000) := by
  exact
    packedTile65536 3298507008 3298638080 14 5973 57432 32 _ _ (273959 / 12500) (87667 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3298638080 :
    ThetaLowerSegment 3298638080 3298769152 (329855000797431 / 100000)
      (329867933877507 / 100000) := by
  exact
    packedTile65536 3298638080 3298769152 14 5901 57433 32 _ _ (547919 / 25000) (2191679 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3298769152 :
    ThetaLowerSegment 3298769152 3298900224 (329867933877507 / 100000)
      (329881024782147 / 100000) := by
  exact
    packedTile65536 3298769152 3298900224 14 5973 57434 32 _ _ (13698 / 625) (2191683 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3298900224 :
    ThetaLowerSegment 3298900224 3299031296 (329881024782147 / 100000)
      (329894078452051 / 100000) := by
  exact
    packedTile65536 3298900224 3299031296 14 5956 57436 32 _ _ (547921 / 25000) (2191687 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3299031296 :
    ThetaLowerSegment 3299031296 3299162368 (329894078452051 / 100000)
      (329907165021099 / 100000) := by
  exact
    packedTile65536 3299031296 3299162368 14 5971 57437 32 _ _ (273961 / 12500) (2191691 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3299162368 :
    ThetaLowerSegment 3299162368 3299293440 (329907165021099 / 100000)
      (65984002982259 / 20000) := by
  exact
    packedTile65536 3299162368 3299293440 14 5863 57438 32 _ _ (547923 / 25000) (438339 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3299293440 :
    ThetaLowerSegment 3299293440 3299424512 (65984002982259 / 20000)
      (329933151937119 / 100000) := by
  exact
    packedTile65536 3299293440 3299424512 14 5994 57439 32 _ _ (136981 / 6250) (2191699 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3299424512 :
    ThetaLowerSegment 3299424512 3299555584 (329933151937119 / 100000)
      (329945997490819 / 100000) := by
  exact
    packedTile65536 3299424512 3299555584 14 5861 57440 32 _ _ (21917 / 1000) (2191703 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3299555584 :
    ThetaLowerSegment 3299555584 3299686656 (329945997490819 / 100000)
      (329959246341499 / 100000) := by
  exact
    packedTile65536 3299555584 3299686656 14 6045 57441 32 _ _ (273963 / 12500) (2191707 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3299686656 :
    ThetaLowerSegment 3299686656 3299817728 (329959246341499 / 100000)
      (329972212486027 / 100000) := by
  exact
    packedTile65536 3299686656 3299817728 14 5916 57442 32 _ _ (547927 / 25000) (2191711 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3299817728 :
    ThetaLowerSegment 3299817728 3299948800 (329972212486027 / 100000)
      (329985465768491 / 100000) := by
  exact
    packedTile65536 3299817728 3299948800 14 6047 57444 32 _ _ (68491 / 3125) (438343 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3299948800 :
    ThetaLowerSegment 3299948800 3300079872 (329985465768491 / 100000)
      (329998550313011 / 100000) := by
  exact
    packedTile65536 3299948800 3300079872 14 5970 57445 32 _ _ (547929 / 25000) (2191719 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3300079872 :
    ThetaLowerSegment 3300079872 3300210944 (329998550313011 / 100000)
      (330011619539371 / 100000) := by
  exact
    packedTile65536 3300079872 3300210944 14 5963 57446 32 _ _ (54793 / 2500) (2191723 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3300210944 :
    ThetaLowerSegment 3300210944 3300342016 (330011619539371 / 100000)
      (330024829059919 / 100000) := by
  exact
    packedTile65536 3300210944 3300342016 14 6027 57447 32 _ _ (547931 / 25000) (2191727 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3300342016 :
    ThetaLowerSegment 3300342016 3300473088 (330024829059919 / 100000) (13201510585543 / 4000) := by
  exact
    packedTile65536 3300342016 3300473088 14 5902 57448 32 _ _ (136983 / 6250) (2191731 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3300473088 :
    ThetaLowerSegment 3300473088 3300604160 (13201510585543 / 4000) (330050972015607 / 100000) := by
  exact
    packedTile65536 3300473088 3300604160 14 6026 57449 32 _ _ (547933 / 25000) (438347 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3300604160 :
    ThetaLowerSegment 3300604160 3300735232 (330050972015607 / 100000)
      (330064089555567 / 100000) := by
  exact
    packedTile65536 3300604160 3300735232 14 5985 57450 32 _ _ (273967 / 12500) (2191739 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3300735232 :
    ThetaLowerSegment 3300735232 3300866304 (330064089555567 / 100000)
      (330077121641607 / 100000) := by
  exact
    packedTile65536 3300735232 3300866304 14 5946 57452 32 _ _ (109587 / 5000) (2191743 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3300866304 :
    ThetaLowerSegment 3300866304 3300997376 (330077121641607 / 100000)
      (330090313748743 / 100000) := by
  exact
    packedTile65536 3300866304 3300997376 14 6019 57453 32 _ _ (68492 / 3125) (2191747 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3300997376 :
    ThetaLowerSegment 3300997376 3301128448 (330090313748743 / 100000)
      (330103271362919 / 100000) := by
  exact
    packedTile65536 3300997376 3301128448 14 5912 57454 32 _ _ (547937 / 25000) (2191751 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3301128448 :
    ThetaLowerSegment 3301128448 3301259520 (330103271362919 / 100000)
      (330116665159391 / 100000) := by
  exact
    packedTile65536 3301128448 3301259520 14 6111 57455 32 _ _ (273969 / 12500) (438351 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3301259520 :
    ThetaLowerSegment 3301259520 3301390592 (330116665159391 / 100000)
      (82532440223879 / 25000) := by
  exact
    packedTile65536 3301259520 3301390592 14 5975 57456 32 _ _ (438351 / 20000) (1095879 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3301390592 :
    ThetaLowerSegment 3301390592 3301521664 (82532440223879 / 25000)
      (330142887340167 / 100000) := by
  exact
    packedTile65536 3301390592 3301521664 14 5989 57457 32 _ _ (2191759 / 100000) (1095881 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3301521664 :
    ThetaLowerSegment 3301521664 3301652736 (330142887340167 / 100000)
      (165077914850341 / 50000) := by
  exact
    packedTile65536 3301521664 3301652736 14 5905 57458 32 _ _ (2191763 / 100000) (1095883 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3301652736 :
    ThetaLowerSegment 3301652736 3301783808 (165077914850341 / 50000)
      (330168899207303 / 100000) := by
  exact
    packedTile65536 3301652736 3301783808 14 5963 57460 32 _ _ (2191767 / 100000) (219177 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3301783808 :
    ThetaLowerSegment 3301783808 3301914880 (330168899207303 / 100000)
      (330182115586433 / 100000) := by
  exact
    packedTile65536 3301783808 3301914880 14 6030 57461 32 _ _ (2191771 / 100000) (1095887 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3301914880 :
    ThetaLowerSegment 3301914880 3302045952 (330182115586433 / 100000)
      (165097535584229 / 50000) := by
  exact
    packedTile65536 3301914880 3302045952 14 5911 57462 32 _ _ (87671 / 4000) (1095889 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3302045952 :
    ThetaLowerSegment 3302045952 3302177024 (165097535584229 / 50000) (66041636916443 / 20000) := by
  exact
    packedTile65536 3302045952 3302177024 14 5983 57463 32 _ _ (2191779 / 100000) (1095891 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3302177024 :
    ThetaLowerSegment 3302177024 3302308096 (66041636916443 / 20000) (165110677503131 / 50000) := by
  exact
    packedTile65536 3302177024 3302308096 14 6009 57464 32 _ _ (2191783 / 100000) (1095893 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3302308096 :
    ThetaLowerSegment 3302308096 3302439168 (165110677503131 / 50000)
      (330234499152901 / 100000) := by
  exact
    packedTile65536 3302308096 3302439168 14 5997 57465 32 _ _ (2191787 / 100000) (219179 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3302439168 :
    ThetaLowerSegment 3302439168 3302570240 (330234499152901 / 100000)
      (82561886721181 / 25000) := by
  exact
    packedTile65536 3302439168 3302570240 14 5953 57466 32 _ _ (2191791 / 100000) (1095897 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3302570240 :
    ThetaLowerSegment 3302570240 3302701312 (82561886721181 / 25000) (165130403622237 / 50000) := by
  exact
    packedTile65536 3302570240 3302701312 14 6050 57467 32 _ _ (438359 / 20000) (1095899 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3302701312 :
    ThetaLowerSegment 3302701312 3302832384 (165130403622237 / 50000) (20642123747279 / 6250) := by
  exact
    packedTile65536 3302701312 3302832384 14 6010 57469 32 _ _ (2191799 / 100000) (1095901 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3302832384 :
    ThetaLowerSegment 3302832384 3302963456 (20642123747279 / 6250) (330286909402361 / 100000) := by
  exact
    packedTile65536 3302832384 3302963456 14 5899 57470 32 _ _ (2191803 / 100000) (1095903 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3302963456 :
    ThetaLowerSegment 3302963456 3303094528 (330286909402361 / 100000)
      (165149954504839 / 50000) := by
  exact
    packedTile65536 3302963456 3303094528 14 5931 57471 32 _ _ (2191807 / 100000) (219181 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3303094528 :
    ThetaLowerSegment 3303094528 3303225600 (165149954504839 / 50000)
      (330313092752843 / 100000) := by
  exact
    packedTile65536 3303094528 3303225600 14 6015 57472 32 _ _ (2191811 / 100000) (1095907 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3303225600 :
    ThetaLowerSegment 3303225600 3303356672 (330313092752843 / 100000)
      (330326322548183 / 100000) := by
  exact
    packedTile65536 3303225600 3303356672 14 6036 57473 32 _ _ (438363 / 20000) (1095909 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3303356672 :
    ThetaLowerSegment 3303356672 3303487744 (330326322548183 / 100000)
      (33033950195583 / 10000) := by
  exact
    packedTile65536 3303356672 3303487744 14 6013 57474 32 _ _ (2191819 / 100000) (1095911 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3303487744 :
    ThetaLowerSegment 3303487744 3303618816 (33033950195583 / 10000) (165176234390349 / 50000) := by
  exact
    packedTile65536 3303487744 3303618816 14 5916 57475 32 _ _ (2191823 / 100000) (1095913 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3303618816 :
    ThetaLowerSegment 3303618816 3303749888 (165176234390349 / 50000)
      (330365718374913 / 100000) := by
  exact
    packedTile65536 3303618816 3303749888 14 6045 57477 32 _ _ (2191827 / 100000) (219183 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3303749888 :
    ThetaLowerSegment 3303749888 3303880960 (330365718374913 / 100000)
      (41297367711417 / 12500) := by
  exact
    packedTile65536 3303749888 3303880960 14 6033 57478 32 _ _ (2191831 / 100000) (1095917 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3303880960 :
    ThetaLowerSegment 3303880960 3304012032 (41297367711417 / 12500)
      (330392099276841 / 100000) := by
  exact
    packedTile65536 3303880960 3304012032 14 6003 57479 32 _ _ (438367 / 20000) (1095919 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3304012032 :
    ThetaLowerSegment 3304012032 3304143104 (330392099276841 / 100000)
      (330405311682333 / 100000) := by
  exact
    packedTile65536 3304012032 3304143104 14 6028 57480 32 _ _ (2191839 / 100000) (1095921 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3304143104 :
    ThetaLowerSegment 3304143104 3304274176 (330405311682333 / 100000) (6608370087707 / 2000) := by
  exact
    packedTile65536 3304143104 3304274176 14 6019 57481 32 _ _ (2191843 / 100000) (1095923 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3304274176 :
    ThetaLowerSegment 3304274176 3304405248 (6608370087707 / 2000) (41303952001763 / 12500) := by
  exact
    packedTile65536 3304274176 3304405248 14 5982 57482 32 _ _ (2191847 / 100000) (43837 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3304405248 :
    ThetaLowerSegment 3304405248 3304536320 (41303952001763 / 12500)
      (330444773695657 / 100000) := by
  exact
    packedTile65536 3304405248 3304536320 14 6003 57483 32 _ _ (2191851 / 100000) (1095927 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3304536320 :
    ThetaLowerSegment 3304536320 3304667392 (330444773695657 / 100000)
      (165228987619161 / 50000) := by
  exact
    packedTile65536 3304536320 3304667392 14 6023 57485 32 _ _ (438371 / 20000) (1095929 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3304667392 :
    ThetaLowerSegment 3304667392 3304798464 (165228987619161 / 50000) (10327219000998 / 3125) := by
  exact
    packedTile65536 3304667392 3304798464 14 5946 57486 32 _ _ (2191859 / 100000) (1095931 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3304798464 :
    ThetaLowerSegment 3304798464 3304929536 (10327219000998 / 3125) (41310517709379 / 12500) := by
  exact
    packedTile65536 3304798464 3304929536 14 5992 57487 32 _ _ (2191863 / 100000) (1095933 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3304929536 :
    ThetaLowerSegment 3304929536 3305060608 (41310517709379 / 12500) (165248543420767 / 50000) := by
  exact
    packedTile65536 3304929536 3305060608 14 5906 57488 32 _ _ (2191867 / 100000) (219187 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3305060608 :
    ThetaLowerSegment 3305060608 3305191680 (165248543420767 / 50000)
      (165255040126411 / 50000) := by
  exact
    packedTile65536 3305060608 3305191680 14 5928 57489 32 _ _ (2191871 / 100000) (1095937 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3305191680 :
    ThetaLowerSegment 3305191680 3305322752 (165255040126411 / 50000)
      (165261589448911 / 50000) := by
  exact
    packedTile65536 3305191680 3305322752 14 5976 57490 32 _ _ (3507 / 160) (1095939 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3305322752 :
    ThetaLowerSegment 3305322752 3305339136 (165261589448911 / 50000) (82631198577977 / 25000) := by
  exact
    packedTile65536 3305322752 3305339136 11 737 57491 32 _ _ (1095939 / 50000) (2191881 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3305339136 :
    ThetaLowerSegment 3305339136 3305341184 (82631198577977 / 25000)
      (330525015691687 / 100000) := by
  exact
    packedTile65536 3305339136 3305341184 8 101 57492 32 _ _ (2191879 / 100000) (1095941 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_3273341184_3305341184 :
    ThetaLowerSegment 3273341184 3305341184 (65465009055529 / 20000)
      (330525015691687 / 100000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3273341184 cell3273472256)
                  (ThetaLowerSegment.join cell3273603328 cell3273734400))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3273865472 cell3273996544)
                  (ThetaLowerSegment.join cell3274127616 cell3274258688)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3274389760 cell3274520832)
                  (ThetaLowerSegment.join cell3274651904 cell3274782976))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3274914048 cell3275045120)
                  (ThetaLowerSegment.join cell3275176192 cell3275307264))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3275438336 cell3275569408)
                  (ThetaLowerSegment.join cell3275700480 cell3275831552))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3275962624 cell3276093696)
                  (ThetaLowerSegment.join cell3276224768 cell3276355840)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3276486912 cell3276617984)
                  (ThetaLowerSegment.join cell3276749056 cell3276880128))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3277011200 cell3277142272)
                  (ThetaLowerSegment.join cell3277273344 cell3277404416)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3277535488 cell3277666560)
                  (ThetaLowerSegment.join cell3277797632 cell3277928704))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3278059776 cell3278190848)
                  (ThetaLowerSegment.join cell3278321920 cell3278452992)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3278584064 cell3278715136)
                  (ThetaLowerSegment.join cell3278846208 cell3278977280))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3279108352 cell3279239424)
                  (ThetaLowerSegment.join cell3279370496 cell3279501568))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3279632640 cell3279763712)
                  (ThetaLowerSegment.join cell3279894784 cell3280025856))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3280156928 cell3280288000)
                  (ThetaLowerSegment.join cell3280419072 cell3280550144)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3280681216 cell3280812288)
                  (ThetaLowerSegment.join cell3280943360 cell3281074432))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3281205504 cell3281336576)
                  (ThetaLowerSegment.join cell3281467648 cell3281598720))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3281729792 cell3281860864)
                  (ThetaLowerSegment.join cell3281991936 cell3282123008))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3282254080 cell3282385152)
                  (ThetaLowerSegment.join cell3282516224 cell3282647296)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3282778368 cell3282909440)
                  (ThetaLowerSegment.join cell3283040512 cell3283171584))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3283302656 cell3283433728)
                  (ThetaLowerSegment.join cell3283564800 cell3283695872))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3283826944 cell3283958016)
                  (ThetaLowerSegment.join cell3284089088 cell3284220160))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3284351232 cell3284482304)
                  (ThetaLowerSegment.join cell3284613376 cell3284744448)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3284875520 cell3285006592)
                  (ThetaLowerSegment.join cell3285137664 cell3285268736))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3285399808 cell3285530880)
                  (ThetaLowerSegment.join cell3285661952 cell3285793024)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3285924096 cell3286055168)
                  (ThetaLowerSegment.join cell3286186240 cell3286317312))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3286448384 cell3286579456)
                  (ThetaLowerSegment.join cell3286710528 cell3286841600)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3286972672 cell3287103744)
                  (ThetaLowerSegment.join cell3287234816 cell3287365888))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3287496960 cell3287628032)
                  (ThetaLowerSegment.join cell3287759104 cell3287890176))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3288021248 cell3288152320)
                  (ThetaLowerSegment.join cell3288283392 cell3288414464))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3288545536 cell3288676608)
                  (ThetaLowerSegment.join cell3288807680 cell3288938752)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3289069824 cell3289200896)
                  (ThetaLowerSegment.join cell3289331968 cell3289463040))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3289594112 cell3289725184)
                  (ThetaLowerSegment.join cell3289856256 cell3289987328)))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3290118400 cell3290249472)
                  (ThetaLowerSegment.join cell3290380544 cell3290511616))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3290642688 cell3290773760)
                  (ThetaLowerSegment.join cell3290904832 cell3291035904)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3291166976 cell3291298048)
                  (ThetaLowerSegment.join cell3291429120 cell3291560192))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3291691264 cell3291822336)
                  (ThetaLowerSegment.join cell3291953408 cell3292084480))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3292215552 cell3292346624)
                  (ThetaLowerSegment.join cell3292477696 cell3292608768))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3292739840 cell3292870912)
                  (ThetaLowerSegment.join cell3293001984 cell3293133056)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3293264128 cell3293395200)
                  (ThetaLowerSegment.join cell3293526272 cell3293657344))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3293788416 cell3293919488)
                  (ThetaLowerSegment.join cell3294050560 cell3294181632)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3294312704 cell3294443776)
                  (ThetaLowerSegment.join cell3294574848 cell3294705920))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3294836992 cell3294968064)
                  (ThetaLowerSegment.join cell3295099136 cell3295230208)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3295361280 cell3295492352)
                  (ThetaLowerSegment.join cell3295623424 cell3295754496))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3295885568 cell3296016640)
                  (ThetaLowerSegment.join cell3296147712 cell3296278784))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3296409856 cell3296540928)
                  (ThetaLowerSegment.join cell3296672000 cell3296803072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3296934144 cell3297065216)
                  (ThetaLowerSegment.join cell3297196288 cell3297327360)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3297458432 cell3297589504)
                  (ThetaLowerSegment.join cell3297720576 cell3297851648))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3297982720 cell3298113792)
                  (ThetaLowerSegment.join cell3298244864 cell3298375936))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3298507008 cell3298638080)
                  (ThetaLowerSegment.join cell3298769152 cell3298900224))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3299031296 cell3299162368)
                  (ThetaLowerSegment.join cell3299293440 cell3299424512)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3299555584 cell3299686656)
                  (ThetaLowerSegment.join cell3299817728 cell3299948800))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3300079872 cell3300210944)
                  (ThetaLowerSegment.join cell3300342016 cell3300473088))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3300604160 cell3300735232)
                  (ThetaLowerSegment.join cell3300866304 cell3300997376))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3301128448 cell3301259520)
                  (ThetaLowerSegment.join cell3301390592 cell3301521664)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3301652736 cell3301783808)
                  (ThetaLowerSegment.join cell3301914880 cell3302045952))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3302177024 cell3302308096)
                  (ThetaLowerSegment.join cell3302439168 cell3302570240)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3302701312 cell3302832384)
                  (ThetaLowerSegment.join cell3302963456 cell3303094528))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3303225600 cell3303356672)
                  (ThetaLowerSegment.join cell3303487744 cell3303618816)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3303749888 cell3303880960)
                  (ThetaLowerSegment.join cell3304012032 cell3304143104))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3304274176 cell3304405248)
                  (ThetaLowerSegment.join cell3304536320 cell3304667392))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell3304798464 cell3304929536)
                (ThetaLowerSegment.join cell3305060608 cell3305191680))
              (ThetaLowerSegment.join cell3305322752 cell3305339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
